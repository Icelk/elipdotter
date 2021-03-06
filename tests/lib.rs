use elipdotter::proximity::ProximateMap;
use elipdotter::*;
use index::{DocumentMap, Simple, SimpleOccurences};
use query::Query;

/// Parses `s` with [`ParseOptions::default`].
fn pq(s: &str) -> Query {
    match s.parse() {
        Ok(p) => p,
        Err(err) => {
            panic!("Failed to parse '{}', {:?}", s, err);
        }
    }
}

fn doc1() -> &'static str {
    "\
Lorem ipsum dolor sit amet, consectetur adipiscing elit. Mauris interdum, metus ut consectetur ullamcorper, velit mi placerat diam, vitae rutrum quam magna sit amet lacus. Curabitur ut rutrum ante. Pellentesque vel neque ante. Nullam vel velit ut ipsum luctus varius id porta nisi. Morbi hendrerit, nunc non consequat consequat, dolor mi consectetur eros, vitae varius diam leo in sem. Aliquam erat volutpat. Proin id mollis quam. Morbi venenatis tincidunt nunc eget ullamcorper. Cras hendrerit libero enim, et aliquet diam rutrum ut. Duis auctor ligula libero, cursus ullamcorper libero porttitor eget. Aliquam scelerisque ac elit at condimentum. Fusce sit amet purus posuere, suscipit libero id, tincidunt nulla. Aliquam molestie orci vitae tellus commodo, nec mattis purus efficitur. Quisque quam nisl, fermentum sit amet ante vitae, finibus aliquet nunc. Ut ut hendrerit lorem.

Nam porttitor urna leo, sit amet imperdiet libero vulputate sed. Morbi elementum ligula turpis, at mattis risus finibus vitae. Vestibulum id egestas tortor. Curabitur suscipit nulla dolor. Duis rhoncus et felis dignissim bibendum. Sed congue arcu quis lacinia iaculis. Nam sit amet lacus sit amet lacus efficitur bibendum."
}
fn doc2() -> &'static str {
    "\
Lorem ipsum dolor sit amet, consectetur adipiscing elit. Nulla lectus orci, aliquam ut justo varius, consequat semper enim. Vestibulum porttitor justo sed tincidunt fringilla. Donec sit amet sollicitudin mi, eu bibendum orci. Maecenas at feugiat ipsum. Vestibulum libero dolor, egestas et sollicitudin eu, ornare sit amet mauris. Maecenas in dolor volutpat, rhoncus urna id, luctus sem. Nulla pulvinar non ex eu venenatis.

Aliquam euismod, justo eu viverra ornare, ex nisi interdum neque, in rutrum nunc mi sit amet libero. Aenean nec arcu pulvinar, venenatis erat ac, sodales massa. Morbi quam leo, cursus at est a, placerat aliquam mauris. Pellentesque habitant morbi tristique senectus et netus et malesuada fames ac turpis egestas. In hac habitasse platea dictumst. In consectetur aliquet aliquam. In vel tempor elit, eget auctor dolor. Phasellus molestie est eget posuere imperdiet. Donec sagittis tincidunt facilisis. Sed eu pulvinar lectus, euismod dictum tellus. Nulla lacinia diam quis odio ultrices, viverra dictum arcu mollis. Donec tempor diam eget tristique maximus. Etiam a dui eu augue euismod dignissim."
}
fn docs() -> (DocumentMap, Simple) {
    let mut map = DocumentMap::new();
    let mut index = Simple::default();
    map.insert("doc 1", doc1(), &mut index);
    map.insert("doc_2", doc2(), &mut index);
    (map, index)
}
fn augment_simple<'a>(
    index: &'a Simple,
    map: &DocumentMap,
    proximate_map: &'a ProximateMap,
) -> SimpleOccurences<'a> {
    let mut occurences = SimpleOccurences::new(index, proximate_map);
    occurences.add_document(map.get_id("doc 1").unwrap(), doc1().to_owned().into());
    occurences.add_document(map.get_id("doc_2").unwrap(), doc2().to_owned().into());
    occurences
}

#[test]
fn query_and() {
    let q = pq("feugiat luctus sem");
    let (map, index) = docs();

    let mut docs = q.documents(&index);
    let mut docs_iter = docs.iter().unwrap();
    assert_eq!(docs_iter.next(), Some(map.get_id("doc_2").unwrap()));
    assert_eq!(docs_iter.next(), None);
    drop(docs_iter);
    let proximate_map = docs.take_proximate_map();

    let occ_provider = augment_simple(&index, &map, &proximate_map);
    let occurrences = q.occurrences(&occ_provider, 100).unwrap();

    let mut occs: Vec<_> = occurrences.collect();
    occs.sort_unstable_by(|a, b| a.rating().partial_cmp(&b.rating()).unwrap());

    let mut occurences = occs.iter();
    let next = occurences.next().unwrap();
    assert_eq!(next.id(), map.get_id("doc_2").unwrap());
    // if the start is at any of the words' starts.
    assert!(
        next.start() == 238 || next.start() == 63 || next.start() == 382,
        "start {}",
        next.start()
    );
    assert!(occs.len() > 1);
}
#[test]
fn query_and_not_1() {
    let q = pq("feugiat test -sem");
    let (_, index) = docs();

    let docs = q.documents(&index);
    let mut docs = docs.iter().unwrap();
    assert_eq!(docs.next(), None);
}
#[test]
fn query_and_not_2() {
    // volutpat exists in both.
    // hac exists only in the second
    let q = pq("volutpat -hac");
    let (map, mut index) = docs();

    let mut docs = q.documents(&index);
    let mut docs_iter = docs.iter().unwrap();

    assert_eq!(docs_iter.next(), Some(map.get_id("doc 1").unwrap()));
    // It does contain `hac`, but maybe they're far apart?
    assert_eq!(docs_iter.next(), Some(map.get_id("doc_2").unwrap()));
    drop(docs_iter);
    let proximate_map = docs.take_proximate_map();

    let occ_provider = augment_simple(&index, &map, &proximate_map);
    let mut occurences = q.occurrences(&occ_provider, 100).unwrap();
    let next = occurences.next().unwrap();
    assert_eq!(next.id(), map.get_id("doc 1").unwrap());
    assert_eq!(next.start(), 399);
    // since this wasn't caught by the NOT (it wasn't present in the entire document),
    // elipdotter adds 2.5 to the rating.
    assert_eq!(next.rating(), 2.5);
    let next = occurences.next().unwrap();
    assert_eq!(next.id(), map.get_id("doc_2").unwrap());
    assert_eq!(next.start(), 348);
    assert!(next.rating() < -0.0);
    assert_eq!(occurences.next(), None);

    drop(occurences);
    occ_provider.missing().apply(&mut index);
}
#[test]
// Same as `query_and_not_2` but q reversed.
fn query_and_not_3() {
    let q = pq("-hac volutpat");
    let (map, mut index) = docs();

    let mut docs = q.documents(&index);
    let mut docs_iter = docs.iter().unwrap();

    assert_eq!(docs_iter.next(), Some(map.get_id("doc 1").unwrap()));
    // It does contain `hac`, but maybe they're far apart?
    assert_eq!(docs_iter.next(), Some(map.get_id("doc_2").unwrap()));
    drop(docs_iter);
    let proximate_map = docs.take_proximate_map();

    let occ_provider = augment_simple(&index, &map, &proximate_map);
    let mut occurences = q.occurrences(&occ_provider, 100).unwrap();
    let next = occurences.next().unwrap();
    assert_eq!(next.id(), map.get_id("doc 1").unwrap());
    assert_eq!(next.start(), 399);
    // since this wasn't caught by the NOT (it wasn't present in the entire document),
    // elipdotter adds 2.5 to the rating.
    assert_eq!(next.rating(), 2.5, "rating is {}", next.rating());
    let next = occurences.next().unwrap();
    assert_eq!(next.id(), map.get_id("doc_2").unwrap());
    assert_eq!(next.start(), 348);
    assert!(next.rating() < -0.0);
    assert_eq!(occurences.next(), None);

    drop(occurences);
    occ_provider.missing().apply(&mut index);
}
