use cambria::{Kind, Lens, Lenses, PrimitiveKind};
use std::process::Command;

fn main() {
    let tokens = cambria::precompile(
        "Doc",
        Lenses::new(vec![
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
        ]),
    );
    std::fs::write("src/schema.rs", tokens.to_string()).unwrap();
    Command::new("rustfmt")
        .arg("src/schema.rs")
        .arg("--emit")
        .arg("files")
        .status()
        .unwrap();
}
