pub use parse::{parse, Options as ParseOptions};

#[derive(Debug, PartialEq, Eq, Clone)]
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
}
impl<T: Into<String>> From<T> for Part {
    fn from(s: T) -> Self {
        Self::String(s.into())
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
            let advance = parser.next(opts, rest);
            rest = rest
                .get(advance..)
                .expect("handle utf codepoint error, also this might bee too long.");
            if rest.is_empty() {
                let right = Part::String(parser.take_string());
                parser.finish_op(parser.old_op.unwrap(), right);
                return parser.left.ok_or(Error::InputEmpty);
            }
        }
    }

    #[derive(Debug)]
    pub struct Parser {
        pub sub: Option<Box<Parser>>,
        pub left: Option<Part>,
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
        fn next(&mut self, opts: &mut Options, rest: &str) -> usize {
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
                match (self.op, self.old_op) {
                    (Some(_), None) => {
                        self.left = Some(Part::String(self.take_string()));
                    }
                    (_, Some(old_op)) if !self.string.is_empty() => {
                        // set left and string to old op.
                        //
                        // replace old with new
                        let right = Part::String(self.take_string());
                        self.finish_op(old_op, right);
                    }
                    _ => {}
                }

                if let Some(op) = self.op {
                    self.old_op = Some(op);
                    self.op = None;
                }

                return advance;
            }
            let c = rest.chars().next().unwrap();
            if c.is_alphanumeric() {
                self.string.push(c);
            }
            1
        }
        fn finish_op(&mut self, op: Op, right: Part) {
            match op {
                Op::And => {
                    let left = self.left.take().unwrap();
                    self.left = Some(Part::And(BinaryPart::new(left, right).into_box()));
                }
                Op::Or => {
                    let left = self.left.take().unwrap();
                    self.left = Some(Part::Or(BinaryPart::new(left, right).into_box()));
                }
                Op::Not => self.left = Some(Part::Not(Box::new(right))),
            }
        }
        fn new() -> Self {
            Self {
                sub: None,
                left: None,
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

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum Error {
        InputEmpty,
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
            Self::new().insert(NotLiteral).insert(AndSpace::default())
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
    pub struct NotLiteral;
    impl Rule for NotLiteral {
        fn next(&mut self, parser: &mut Parser, rest: &str) -> Option<usize> {
            if rest
                .get(0..4)
                .map_or(false, |rest| rest.eq_ignore_ascii_case("not "))
            {
                parser.op = Some(Op::Not);
                Some(3)
            } else {
                None
            }
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

        assert_eq!(p1, Part::or(Part::and("icelk", "kvarn"), "agde"));
        assert_eq!(p2, Part::or(Part::and("icelk", "kvarn"), "agde"));
        assert_eq!(p1, p2);

        let implicit = "icelk kvarn or agde";
        let p_impl = s(implicit);

        assert_eq!(p_impl, p1);
    }
}
