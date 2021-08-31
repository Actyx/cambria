use cambria::{Kind, Lens, Lenses, PrimitiveKind};
use std::process::Command;

fn write_rust(path: &str, rust: String) {
    std::fs::write(path, rust).unwrap();
    Command::new("rustfmt")
        .arg(path)
        .arg("--emit")
        .arg("files")
        .status()
        .unwrap();
}

fn main() {
    let mut lenses = vec![
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
    let doc = cambria::precompile("Doc", Lenses::new(lenses.clone()));
    lenses.push(Lens::RenameProperty(
        "shopping".into(),
        "shopping_list".into(),
    ));
    let doc2 = cambria::precompile("Doc2", Lenses::new(lenses));
    write_rust("src/schema.rs", doc.to_string());
    write_rust("src/schema2.rs", doc2.to_string());
}
