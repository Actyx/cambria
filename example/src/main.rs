use cambria::Cambria;
use rkyv::archived_root;
use rkyv::ser::serializers::AllocSerializer;
use rkyv::ser::Serializer;

mod schema;

use schema::Doc;

fn main() {
    let mut doc = Doc::default();
    doc.done = true.into();
    doc.xanswer = 42.into();
    doc.shopping.push("cheese".into());
    doc.shopping.push("eggs".into());
    doc.shopping.push("milk".into());

    let mut ser = AllocSerializer::<256>::default();
    ser.serialize_value(&doc).unwrap();
    let bytes = ser.into_serializer().into_inner().to_vec();
    let ptr = unsafe { archived_root::<Doc>(&bytes[..]) }.ptr();

    assert_eq!(
        ptr.keys().unwrap().collect::<Vec<_>>(),
        vec!["done", "shopping", "xanswer"]
    );
    let done = ptr.get("done").unwrap().boolean().unwrap();
    assert_eq!(done, true);

    let answer = ptr.get("xanswer").unwrap().number().unwrap();
    assert_eq!(answer, 42);

    let shopping = ptr.get("shopping").unwrap();
    assert_eq!(shopping.len().unwrap(), 3);
    let cheese = shopping.idx(0).unwrap();
    assert_eq!(cheese.string().unwrap(), "cheese");
    let eggs = shopping.idx(1).unwrap();
    assert_eq!(eggs.string().unwrap(), "eggs");

    println!("{:?}", doc);
}
