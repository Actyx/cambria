use crate::lens::ArchivedSchema;
use rkyv::string::ArchivedString;
use rkyv::{Archive, Deserialize, RawRelPtr, Serialize};

#[derive(
    Clone,
    Copy,
    Debug,
    Default,
    Eq,
    Hash,
    Ord,
    PartialEq,
    PartialOrd,
    Archive,
    Deserialize,
    Serialize,
)]
#[repr(C)]
pub struct Number([u8; 8]);

impl From<Number> for i64 {
    fn from(n: Number) -> i64 {
        i64::from_le_bytes(n.0)
    }
}

impl From<i64> for Number {
    fn from(n: i64) -> Number {
        Self(n.to_le_bytes())
    }
}

#[derive(
    Clone,
    Copy,
    Debug,
    Default,
    Eq,
    Hash,
    Ord,
    PartialEq,
    PartialOrd,
    Archive,
    Deserialize,
    Serialize,
)]
#[repr(C)]
pub struct Bool([u8; 8]);

impl From<Bool> for bool {
    fn from(b: Bool) -> bool {
        u64::from_le_bytes(b.0) > 0
    }
}

impl From<bool> for Bool {
    fn from(b: bool) -> Bool {
        let n: u64 = if b { 1 } else { 0 };
        Self(n.to_le_bytes())
    }
}

pub struct Ptr<'a> {
    ptr: *const u8,
    schema: &'a ArchivedSchema,
}

impl<'a> Ptr<'a> {
    pub fn new(ptr: *const u8, schema: &'a ArchivedSchema) -> Self {
        Self { ptr, schema }
    }

    pub fn string(&self) -> Option<&str> {
        if let ArchivedSchema::Text = self.schema {
            let s = unsafe { &*(self.ptr as *const ArchivedString) };
            return Some(s.as_str());
        }
        None
    }

    pub fn boolean(&self) -> Option<bool> {
        if let ArchivedSchema::Boolean = self.schema {
            return Some(unsafe { *(self.ptr as *const Bool) }.into());
        }
        None
    }

    pub fn number(&self) -> Option<i64> {
        if let ArchivedSchema::Number = self.schema {
            return Some(unsafe { *(self.ptr as *const Number) }.into());
        }
        None
    }

    pub fn idx(&self, idx: usize) -> Option<Ptr<'a>> {
        if let ArchivedSchema::Array(_, schema) = self.schema {
            let rel_ptr = unsafe { &*(self.ptr as *const RawRelPtr) };
            // TODO bounds checking
            let ptr = unsafe { (rel_ptr.as_ptr() as *const u8).add(idx * 8) };
            return Some(Ptr { ptr, schema });
        }
        None
    }

    pub fn get(&self, key: &str) -> Option<Ptr<'a>> {
        if let ArchivedSchema::Object(m) = self.schema {
            if !m.contains_key(key) {
                return None;
            }
            let mut i = 0;
            let mut schema = None;
            for (k, s) in m.iter() {
                if k.as_str() == key {
                    schema = Some(s);
                    break;
                } else {
                    i += 8;
                }
            }
            let ptr = unsafe { self.ptr.add(i) };
            return Some(Ptr {
                ptr,
                schema: schema.unwrap(),
            });
        }
        None
    }

    pub fn len(&self) -> Option<usize> {
        if let ArchivedSchema::Array(_, _) = self.schema {
            let rel_ptr = unsafe { *(self.ptr as *const u64) };
            return Some((rel_ptr >> 32) as usize);
        }
        None
    }

    pub fn keys(&self) -> Option<impl Iterator<Item = &str>> {
        if let ArchivedSchema::Object(m) = self.schema {
            return Some(m.keys().map(|k| k.as_str()));
        }
        None
    }
}
