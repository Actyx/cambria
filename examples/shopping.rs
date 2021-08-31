use cambria::layout::{Bool, Number, Ptr};
use cambria::lens::{Kind, Lens, Lenses, PrimitiveKind, Schema};
use rkyv::ser::serializers::AllocSerializer;
use rkyv::ser::Serializer;
use rkyv::{archived_root, Archive, Deserialize, Serialize};
use std::convert::TryFrom;

/*gen_structs!(Doc, vec![
    Make(Kind::Object),
    AddProperty("shopping"),
    LensIn("shopping", Make(Kind::Array)),
    LensIn("shopping", LensMap(Make(Kind::String))),
])*/

pub trait Root {
    // TODO: &'static ArchivedLenses
    fn lenses(&self) -> Vec<u8>;
    // TODO: &'static ArchivedSchema
    fn schema(&self) -> Vec<u8>;
    fn ptr<'a>(&'a self, schema: &'a [u8]) -> Ptr<'a>;
}

#[derive(Default, Archive, Deserialize, Serialize)]
#[archive_attr(repr(C))]
struct Doc {
    done: Bool,
    shopping: Vec<String>,
    xanswer: Number,
}

impl Root for ArchivedDoc {
    fn lenses(&self) -> Vec<u8> {
        let ls = vec![
            Lens::Make(Kind::Object),
            Lens::AddProperty("shopping".into()),
            Lens::LensIn("shopping".into(), Box::new(Lens::Make(Kind::Array))),
            Lens::LensIn(
                "shopping".into(),
                Box::new(Lens::LensMap(Box::new(Lens::Make(Kind::Primitive(
                    PrimitiveKind::Text,
                ))))),
            ),
            Lens::AddProperty("done".into()),
            Lens::LensIn(
                "done".into(),
                Box::new(Lens::Make(Kind::Primitive(PrimitiveKind::Boolean))),
            ),
            Lens::AddProperty("xanswer".into()),
            Lens::LensIn(
                "xanswer".into(),
                Box::new(Lens::Make(Kind::Primitive(PrimitiveKind::Number))),
            ),
        ];
        let mut ser = AllocSerializer::<256>::default();
        ser.serialize_value(&Lenses::new(ls)).unwrap();
        ser.into_serializer().into_inner().to_vec()
    }

    fn schema(&self) -> Vec<u8> {
        let lenses = self.lenses();
        let lenses = unsafe { archived_root::<Lenses>(&lenses[..]) };
        let schema = Schema::try_from(lenses).unwrap();
        let mut ser = AllocSerializer::<256>::default();
        ser.serialize_value(&schema).unwrap();
        ser.into_serializer().into_inner().to_vec()
    }

    fn ptr<'a>(&'a self, schema: &'a [u8]) -> Ptr<'a> {
        let schema = unsafe { archived_root::<Schema>(&schema[..]) };
        Ptr::new(self as *const _ as *const u8, schema)
    }
}

fn main() {
    let mut doc = Doc::default();
    doc.done = true.into();
    doc.xanswer = 42.into();
    doc.shopping.push("cheese".into());
    doc.shopping.push("eggs".into());
    doc.shopping.push("milk".into());

    let mut ser = AllocSerializer::<256>::default();
    ser.serialize_value(&doc).unwrap();
    let doc = ser.into_serializer().into_inner().to_vec();
    let doc = unsafe { archived_root::<Doc>(&doc[..]) };

    let schema = doc.schema();
    let ptr = doc.ptr(&schema);

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
}
