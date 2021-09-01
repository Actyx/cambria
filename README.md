# Cambria

Use lenses to maintain forwards and backwards compatibility with your software. Cambria minimizes
allocations using `rkyv` for zero copy deserialization and is formally verified with idris.

## Getting started

Add your lenses to your `build.rs` file.

```rust
use cambria::{Kind, Lens, Lenses, PrimitiveKind};
use std::process::Command;

fn main() {
    let tokens = cambria::precompile("Doc", Lenses::new(vec![
        Lens::Make(Kind::Object),
        Lens::AddProperty("shopping".into()),
        Lens::LensIn(
            "shopping".into(),
            Box::new(Lens::LensMap(Box::new(Lens::Make(Kind::Primitive(
                PrimitiveKind::Text,
            ))))),
        ),
    ]));
    std::fs::write("src/schema.rs", tokens.to_string()).unwrap();
    Command::new("rustfmt")
        .arg("src/schema.rs")
        .arg("--emit")
        .arg("files")
        .status()
        .unwrap();
}
```

Do some stuff with your schema.

```rust
use cambria::{Cambria, Ptr};
use rkyv::ser::serializers::AllocSerializer;
use rkyv::ser::Serializer;

mod schema;
mod schema2;

use schema::Doc;
use schema2::Doc2;

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
    let ptr = Ptr::new(&bytes, Doc::schema());

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

    let doc2 = Doc2::transform(Doc::lenses(), &bytes).unwrap();
    println!("{:?}", doc);
    println!("{:?}", doc2);
}
```

# License
Apache-2.0 or MIT
