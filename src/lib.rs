mod layout;
mod lens;
mod precompile;

pub use layout::{Bool, Number, Ptr};
pub use lens::{ArchivedSchema, Kind, Lens, Lenses, PrimitiveKind, PrimitiveValue, Schema};
pub use precompile::precompile;
pub use {aligned, rkyv};

pub trait Cambria {
    fn lenses(&self) -> &'static [u8];
    fn schema(&self) -> &'static ArchivedSchema;
    fn ptr<'a>(&'a self) -> Ptr<'a>;
    fn transform(lenses: &[u8], bytes: &[u8]) -> Self;
}
