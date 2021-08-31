#[derive(
    Clone,
    Debug,
    Default,
    Eq,
    Hash,
    PartialEq,
    rkyv :: Archive,
    rkyv :: Deserialize,
    rkyv :: Serialize,
)]
#[archive_attr(derive(Debug, Eq, Hash, PartialEq), repr(C))]
pub struct Doc {
    #[with(cambria::Bool)]
    pub done: bool,
    pub shopping: Vec<String>,
    #[with(cambria::Number)]
    pub xanswer: i64,
}
impl cambria::Cambria for ArchivedDoc {
    fn lenses() -> &'static [u8] {
        use cambria::aligned::{Aligned, A8};
        static LENSES: Aligned<A8, [u8; 292usize]> = Aligned([
            115u8, 104u8, 111u8, 112u8, 112u8, 105u8, 110u8, 103u8, 115u8, 104u8, 111u8, 112u8,
            112u8, 105u8, 110u8, 103u8, 0u8, 0u8, 0u8, 0u8, 2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 115u8, 104u8, 111u8, 112u8, 112u8, 105u8,
            110u8, 103u8, 0u8, 0u8, 0u8, 0u8, 1u8, 0u8, 0u8, 0u8, 2u8, 0u8, 0u8, 0u8, 0u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 10u8, 0u8, 0u8, 0u8, 232u8, 255u8, 255u8, 255u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 1u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
            0u8, 1u8, 0u8, 0u8, 0u8, 1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 3u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
            0u8, 0u8, 0u8, 2u8, 0u8, 0u8, 0u8, 8u8, 0u8, 0u8, 0u8, 108u8, 255u8, 255u8, 255u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 9u8, 0u8, 0u8, 0u8, 8u8, 0u8, 0u8, 0u8, 96u8, 255u8,
            255u8, 255u8, 96u8, 255u8, 255u8, 255u8, 0u8, 0u8, 0u8, 0u8, 9u8, 0u8, 0u8, 0u8, 8u8,
            0u8, 0u8, 0u8, 104u8, 255u8, 255u8, 255u8, 124u8, 255u8, 255u8, 255u8, 0u8, 0u8, 0u8,
            0u8, 2u8, 0u8, 0u8, 0u8, 100u8, 111u8, 110u8, 101u8, 0u8, 0u8, 0u8, 4u8, 0u8, 0u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 0u8, 9u8, 0u8, 0u8, 0u8, 100u8, 111u8, 110u8, 101u8, 0u8, 0u8, 0u8,
            4u8, 104u8, 255u8, 255u8, 255u8, 0u8, 0u8, 0u8, 0u8, 2u8, 0u8, 0u8, 0u8, 120u8, 97u8,
            110u8, 115u8, 119u8, 101u8, 114u8, 7u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 9u8,
            0u8, 0u8, 0u8, 120u8, 97u8, 110u8, 115u8, 119u8, 101u8, 114u8, 7u8, 84u8, 255u8, 255u8,
            255u8, 0u8, 0u8, 0u8, 0u8, 96u8, 255u8, 255u8, 255u8, 8u8, 0u8, 0u8, 0u8,
        ]);
        &LENSES[..]
    }
    fn schema() -> &'static cambria::ArchivedSchema {
        use cambria::aligned::{Aligned, A8};
        static SCHEMA: Aligned<A8, [u8; 104usize]> = Aligned([
            115u8, 104u8, 111u8, 112u8, 112u8, 105u8, 110u8, 103u8, 3u8, 0u8, 0u8, 0u8, 0u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 20u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 3u8, 0u8, 0u8,
            0u8, 100u8, 111u8, 110u8, 101u8, 0u8, 0u8, 0u8, 4u8, 1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 0u8, 8u8, 0u8, 0u8, 0u8, 204u8, 255u8, 255u8, 255u8, 4u8, 1u8, 0u8,
            0u8, 200u8, 255u8, 255u8, 255u8, 0u8, 0u8, 0u8, 0u8, 120u8, 97u8, 110u8, 115u8, 119u8,
            101u8, 114u8, 7u8, 2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 5u8,
            0u8, 0u8, 0u8, 3u8, 0u8, 0u8, 0u8, 176u8, 255u8, 255u8, 255u8,
        ]);
        unsafe { rkyv::archived_root::<cambria::Schema>(&SCHEMA[..]) }
    }
}
