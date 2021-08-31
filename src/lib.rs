mod layout;
mod lens;
mod precompile;

pub use layout::{Bool, Number, Ptr};
pub use lens::{ArchivedSchema, Kind, Lens, Lenses, PrimitiveKind, PrimitiveValue, Schema};
pub use precompile::precompile;
pub use {aligned, rkyv};

use anyhow::Result;
use rkyv::archived_root;

pub trait Cambria {
    fn lenses() -> &'static [u8];

    fn schema() -> &'static ArchivedSchema;

    fn ptr<'a>(&'a self) -> Ptr<'a> {
        Ptr::new(self as *const _ as *const u8, unsafe {
            &*(Self::schema() as *const _)
        })
    }

    fn transform(lenses: &[u8], bytes: &[u8]) -> Result<Self>
    where
        Self: Sized,
    {
        let a = unsafe { archived_root::<Lenses>(lenses) };
        let b = unsafe { archived_root::<Lenses>(Self::lenses()) };
        let sa = a.to_schema()?;
        let sa = unsafe { archived_root::<Schema>(&sa[..]) };
        let pa = Ptr::new(bytes as *const _ as *const u8, sa);
        //let mut me = Self::default();
        for lens in a.transform(b) {
            //lens.transform_value(pa.ptr()
        }
        todo!()
    }
}
