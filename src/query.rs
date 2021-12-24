use std::fmt::{self, Debug, Display};

pub use parse::{parse, Options as ParseOptions};

#[derive(PartialEq, Eq, Clone)]
#[must_use]
pub enum Part {
    And(Box<BinaryPart>),
    Or(Box<BinaryPart>),
    Not(Box<Part>),

    String(String),
}
impl Part {
    pub fn string(s: impl AsRef<str>) -> Self {
        Self::String(s.as_ref().into())
    }
    pub fn and(left: impl Into<Self>, right: impl Into<Self>) -> Self {
        Self::And(BinaryPart::new(left.into(), right.into()).into_box())
    }
    pub fn or(left: impl Into<Self>, right: impl Into<Self>) -> Self {
        Self::Or(BinaryPart::new(left.into(), right.into()).into_box())
    }
    pub fn not(not: impl Into<Self>) -> Self {
        Self::Not(Box::new(not.into()))
    }

    /// Tests the equality of the parts AND order.
    ///
    /// See [`BinaryPart`] for more details.
    ///
    /// This makes no difference to the [`Eq`] implementation if `self` is [`Self::Not`] or
    /// [`Self::String`].
    #[must_use]
    pub fn eq_order(&self, other: &Self) -> bool {
        if !self.eq(other) {
            return false;
        }
        match self {
            Self::String(_) | Self::Not(_) => true,
            Self::Or(p1) | Self::And(p1) => {
                if let Self::Or(p2) | Self::And(p2) = other {
                    p1.eq_order(p2)
                } else {
                    false
                }
            }
        }
    }
}
impl<T: Into<String>> From<T> for Part {
    fn from(s: T) -> Self {
        Self::String(s.into())
    }
}
impl Debug for Part {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(self, f)
    }
}
impl Display for Part {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn fmt_pair(f: &mut fmt::Formatter<'_>, pair: &BinaryPart, op: &str) -> fmt::Result {
            write!(f, "({} {} {})", pair.left, op, pair.right)
        }
        match self {
            Self::String(s) => f.write_str(s),
            Self::And(pair) => fmt_pair(f, pair, "AND"),
            Self::Or(pair) => fmt_pair(f, pair, "OR"),
            Self::Not(not) => write!(f, "(NOT {})", not),
        }
    }
}

#[derive(Debug, Clone)]
#[must_use]
/// Eq implementation doesn't care of which is left and right.
pub struct BinaryPart {
    pub left: Part,
    pub right: Part,
}
impl BinaryPart {
    pub fn new(left: Part, right: Part) -> Self {
        Self { left, right }
    }
    #[must_use]
    pub fn into_box(self) -> Box<Self> {
        Box::new(self)
    }
    /// Swaps [`Self::left`] and [`Self::right`].
    ///
    /// This does not affect [`Eq`].
    pub fn swap(&mut self) {
        std::mem::swap(&mut self.left, &mut self.right);
    }
    /// Tests the equality of the parts AND order of [`Self::left`] & [`Self::right`].
    #[must_use]
    pub fn eq_order(&self, other: &Self) -> bool {
        self.left.eq_order(&other.left) && self.right.eq_order(&other.right)
    }
}
impl PartialEq for BinaryPart {
    fn eq(&self, other: &Self) -> bool {
        (self.left == other.left && self.right == other.right)
            || (self.left == other.right && self.right == other.left)
    }
}
impl Eq for BinaryPart {}
#[derive(Debug, PartialEq, Eq, Clone)]
#[must_use]
pub struct Query {
    root: Part,
}

pub mod parse {
    use std::fmt::Debug;

    use crate::query::BinaryPart;

    use super::Part;

    #[allow(clippy::missing_panics_doc)]
    #[allow(clippy::missing_errors_doc)]
    pub fn parse(s: &str, opts: Options) -> Result<Part, Error> {
        let mut parser = Parser::new();
        let mut opts = opts;
        let opts = &mut opts;
        let mut rest = s;

        if s.is_empty() {
            return Err(Error::InputEmpty);
        }

        loop {
            let advance = parser.next(opts, rest)?;
            rest = rest
                .get(advance..)
                .expect("handle utf codepoint error, also this might bee too long.");
            if rest.is_empty() {
                return parser.finish();
            }
        }
    }

    #[derive(Debug)]
    pub struct Parser {
        sub: Option<Box<Parser>>,
        sub_layer: usize,
        pub left: Option<Part>,
        left_group_explicit: bool,
        pub string: String,
        old_op: Option<Op>,
        pub op: Option<Op>,
    }
    impl Parser {
        fn take_string(&mut self) -> String {
            std::mem::replace(&mut self.string, String::with_capacity(8))
        }
        // start by appending to a Part::String
        // if any things (struct) are recogniced
        // add their corresponding part (method of struct, manip the tree)
        //
        // Make sure the order is right on those rules - order of importance: NOT, AND, OR
        /// # Panics
        ///
        /// Panics if `rest.is_empty()`.
        fn next(&mut self, opts: &mut Options, rest: &str) -> Result<usize, Error> {
            if let Some(sub) = &mut self.sub {
                if rest.starts_with('(') {
                    self.sub_layer += 1;
                }
                if rest.starts_with(')') {
                    self.sub_layer -= 1;
                    if self.sub_layer == 0 {
                        let parenthesis = sub.finish()?;
                        self.finish_part(self.old_op, parenthesis);
                        self.sub = None;
                        self.left_group_explicit = true;
                        return Ok(1);
                    }
                }
                return sub.next(opts, rest);
            } else if rest.starts_with('(') {
                self.sub = Some(Box::new(Self::new()));
                self.sub_layer += 1;
                return Ok(1);
            }

            let mut advance = None;
            for rule in &mut opts.rules {
                if let Some(result) = rule.next(self, rest) {
                    assert!(result > 0, "Cannot stay on the same byte.");

                    if advance.is_none() {
                        advance = Some(result);
                    }
                }
            }
            if let Some(advance) = advance {
                if !self.string.is_empty() {
                    match (self.op, self.old_op) {
                        (Some(_), None) => {
                            self.left = Some(Part::String(self.take_string()));
                        }
                        (_, Some(old_op)) => {
                            // set left and string to old op.
                            //
                            // replace old with new
                            let right = Part::String(self.take_string());
                            self.finish_op(old_op, right);
                        }
                        _ => {}
                    }
                    self.left_group_explicit = false;
                }

                if let Some(op) = self.op {
                    self.old_op = Some(op);
                    self.op = None;
                }

                return Ok(advance);
            }
            let c = rest.chars().next().unwrap();
            if c.is_alphanumeric() {
                self.string.push(c);
            }
            Ok(1)
        }
        fn finish_part(&mut self, op: Option<Op>, right: Part) {
            if let Some(op) = op {
                self.finish_op(op, right);
            } else {
                self.left = Some(right);
            }
        }
        fn finish_op(&mut self, op: Op, mut right: Part) {
            if let Op::And | Op::Or = op {
                if self.left.is_none() {
                    self.left = Some(right);
                    return;
                }
            }
            match op {
                Op::And => {
                    // UNWRAP: See if statement in top of fn
                    let left = self.left.take().unwrap();
                    let part = if let Part::Or(mut pair) = left {
                        if self.left_group_explicit {
                            Part::And(BinaryPart::new(Part::Or(pair), right).into_box())
                        } else {
                            std::mem::swap(&mut right, &mut pair.left);
                            pair.swap();
                            let and = Part::And(pair);
                            // We swapped the left part of the pair to `right`.
                            let or = right;
                            Part::or(or, and)
                        }
                    } else {
                        Part::And(BinaryPart::new(left, right).into_box())
                    };
                    self.left = Some(part);
                }
                Op::Or => {
                    // UNWRAP: See if statement in top of fn
                    let left = self.left.take().unwrap();
                    self.left = Some(Part::Or(BinaryPart::new(left, right).into_box()));
                }
                Op::Not => self.left = Some(Part::Not(Box::new(right))),
            }
        }
        fn finish(&mut self) -> Result<Part, Error> {
            if !self.string.is_empty() {
                let right = Part::String(self.take_string());
                self.finish_part(self.old_op, right);
            }
            self.left.take().ok_or(Error::NotEnoughArguments)
        }
        fn new() -> Self {
            Self {
                sub: None,
                sub_layer: 0,
                left: None,
                left_group_explicit: false,
                string: String::with_capacity(8),
                old_op: None,
                op: None,
            }
        }
    }

    #[derive(Debug, Clone, Copy)]
    pub enum Op {
        And,
        Or,
        Not,
    }
    impl Op {
        pub fn binary(&self) -> bool {
            matches!(self, Self::And | Self::Or)
        }
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum Error {
        InputEmpty,
        /// Operation took more arguments than what was supplied.
        NotEnoughArguments,
        UnexpectedParentheses,
    }
    #[derive(Debug)]
    #[must_use]
    pub struct Options {
        rules: Vec<Box<dyn Rule>>,
    }
    impl Options {
        pub fn new() -> Self {
            Self { rules: Vec::new() }
        }
        pub fn insert<R: 'static + Rule>(mut self, rule: R) -> Self {
            self.rules.push(Box::new(rule));
            self
        }
    }
    impl Default for Options {
        fn default() -> Self {
            Self::new()
                .insert(NotLiteral)
                .insert(AndLiteral)
                .insert(OrLiteral)
                .insert(AndSpace::default())
        }
    }
    pub trait Rule: Debug {
        #[must_use]
        fn next(&mut self, parser: &mut Parser, rest: &str) -> Option<usize>;
    }

    #[derive(Debug, Default)]
    pub struct AndSpace {
        last_was_other_op: bool,
    }
    impl Rule for AndSpace {
        fn next(&mut self, parser: &mut Parser, rest: &str) -> Option<usize> {
            // if parser.string.is_empty() {
            // return None;
            // }
            if !self.last_was_other_op {
                self.last_was_other_op = parser.op.is_some();
                if self.last_was_other_op {
                    return None;
                }
            }
            let c = rest.chars().next().unwrap();
            if self.last_was_other_op {
                if c == ' ' {
                    None
                } else {
                    self.last_was_other_op = false;
                    None
                }
            } else if c == ' ' {
                parser.op = Some(Op::And);
                Some(1)
            } else {
                None
            }
        }
    }

    #[derive(Debug)]
    #[must_use]
    pub struct LiteralRule {
        literal: &'static str,
        op: Op,
    }
    impl LiteralRule {
        /// Matches the `literal` with [`Op`].
        ///
        /// Will exit if nothing was detected before and this is a binary operation.
        pub fn new(literal: &'static str, op: Op) -> Self {
            Self { literal, op }
        }
    }
    impl Rule for LiteralRule {
        fn next(&mut self, parser: &mut Parser, rest: &str) -> Option<usize> {
            if self.op.binary() && parser.string.is_empty() && parser.left.is_none() {
                return None;
            }
            if rest
                .get(0..self.literal.len())
                .map_or(false, |rest| rest.eq_ignore_ascii_case(self.literal))
                && rest
                    .chars()
                    .nth(self.literal.len())
                    .map_or(false, |c| c == ' ')
            {
                parser.op = Some(self.op);
                Some(self.literal.len())
            } else {
                None
            }
        }
    }

    #[derive(Debug)]
    pub struct AndLiteral;
    impl Rule for AndLiteral {
        fn next(&mut self, parser: &mut Parser, rest: &str) -> Option<usize> {
            LiteralRule::new("and", Op::And).next(parser, rest)
        }
    }
    #[derive(Debug)]
    pub struct OrLiteral;
    impl Rule for OrLiteral {
        fn next(&mut self, parser: &mut Parser, rest: &str) -> Option<usize> {
            LiteralRule::new("or", Op::Or).next(parser, rest)
        }
    }

    #[derive(Debug)]
    pub struct NotLiteral;
    impl Rule for NotLiteral {
        fn next(&mut self, parser: &mut Parser, rest: &str) -> Option<usize> {
            LiteralRule::new("not", Op::Not).next(parser, rest)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Parses `s` with [`ParseOptions::default`].
    fn s(s: &str) -> Part {
        parse(s, ParseOptions::default()).unwrap()
    }

    #[test]
    fn binary_swap_eq() {
        let part = s("icelk kvarn");
        let mut swapped = part.clone();
        if let Part::And(pair) = &mut swapped {
            pair.swap();
        } else {
            panic!("Isn't Add.");
        }
        assert_eq!(part, swapped);
    }

    #[test]
    fn parse_and() {
        let input = "icelk kvarn";
        let part = s(input);
        assert_eq!(part, Part::and("icelk", "kvarn"));
    }
    #[test]
    fn parse_and_chain() {
        let input = "icelk kvarn web server";
        let part = s(input);
        assert_eq!(
            part,
            Part::and(Part::and(Part::and("icelk", "kvarn"), "web"), "server")
        );
    }
    #[test]
    fn parse_plain_not() {
        let part = s("not icelk");
        assert_eq!(part, Part::not("icelk"));
    }
    #[test]
    fn parse_empty() {
        assert_eq!(
            parse("", ParseOptions::default()).unwrap_err(),
            parse::Error::InputEmpty
        );
    }
    #[test]
    fn parse_without_ops() {
        assert_eq!(s("icelk"), Part::string("icelk"),);
    }
    #[test]
    fn parse_and_before_or() {
        let i1 = "icelk and kvarn or agde";
        let i2 = "agde or icelk and kvarn";
        let p1 = s(i1);
        let p2 = s(i2);

        let correct = Part::or(Part::and("icelk", "kvarn"), "agde");
        assert_eq!(p1, correct);
        assert!(p1.eq_order(&correct));
        assert_eq!(p2, correct);
        assert!(!p2.eq_order(&correct));
        assert_eq!(p1, p2);

        let implicit = "icelk kvarn or agde";
        let p_impl = s(implicit);

        assert_eq!(p_impl, p1);
    }
    #[test]
    fn parse_parentheses_or() {
        let p1 = s("(icelk or kvarn) and code");
        let p2 = s("code (kvarn or icelk) ");

        let correct = Part::and(Part::or("icelk", "kvarn"), "code");

        assert_eq!(p1, correct);
        assert!(p1.eq_order(&correct));
        assert_eq!(p2, correct);
        assert!(!p2.eq_order(&correct));
        assert_eq!(p1, p2);
    }
    #[test]
    fn parse_parentheses_and() {
        let p = s(" (icelk or iselk)  (kvarn or agde)))");
        assert_eq!(
            p,
            Part::and(Part::or("icelk", "iselk"), Part::or("kvarn", "agde"))
        );
    }
    #[test]
    fn parse_not() {
        let p = s("not");
        assert_eq!(p, Part::string("not"));
        assert_eq!(
            parse("not ", ParseOptions::default()).unwrap_err(),
            parse::Error::NotEnoughArguments
        );
    }
    #[test]
    fn parse_space() {
        assert_eq!(
            parse(" ", ParseOptions::default()).unwrap_err(),
            parse::Error::NotEnoughArguments
        );
    }
    #[test]
    fn parse_parentheses_space() {
        assert_eq!(
            parse(" (  ) ", ParseOptions::default()).unwrap_err(),
            parse::Error::NotEnoughArguments
        );
    }
    #[test]
    fn parse_binary_one_arg() {
        let p = s("or icelk");
        assert_eq!(p, Part::and("or", "icelk"));
    }
    // ↑ in parentheses
    // `not` order with or and and
}
