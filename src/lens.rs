use anyhow::{anyhow, Result};
use fnv::FnvHashMap;
use rkyv::{Archive, Deserialize, Serialize};
use std::convert::TryFrom;

pub type Prop = String;

#[derive(Clone, Debug, Eq, PartialEq, Archive, Deserialize, Serialize)]
pub enum PrimitiveKind {
    Boolean,
    Number,
    Text,
}

#[derive(Clone, Debug, Eq, PartialEq, Archive, Deserialize, Serialize)]
pub enum PrimitiveValue {
    Boolean(bool),
    Number(i64),
    Text(String),
}

impl PrimitiveValue {
    pub fn kind_of(&self) -> PrimitiveKind {
        match self {
            Self::Boolean(_) => PrimitiveKind::Boolean,
            Self::Number(_) => PrimitiveKind::Number,
            Self::Text(_) => PrimitiveKind::Text,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Value {
    Null,
    Primitive(PrimitiveValue),
    Array(Vec<Value>),
    Object(FnvHashMap<Prop, Value>),
}

#[derive(Clone, Debug, Eq, PartialEq, Archive, Deserialize, Serialize)]
pub enum Kind {
    Null,
    Primitive(PrimitiveKind),
    Array,
    Object,
}

#[derive(Clone, Debug, Eq, PartialEq)]
//#[derive(Archive, Deserialize, Serialize)]
pub enum Schema {
    Null,
    Boolean,
    Number,
    Text,
    Array(bool, Box<Schema>),
    Object(FnvHashMap<Prop, Schema>),
}

impl Schema {
    pub fn validate(&self, v: &Value) -> bool {
        match (self, v) {
            (Self::Null, Value::Null) => true,
            (Self::Boolean, Value::Primitive(PrimitiveValue::Boolean(_))) => true,
            (Self::Number, Value::Primitive(PrimitiveValue::Number(_))) => true,
            (Self::Text, Value::Primitive(PrimitiveValue::Text(_))) => true,
            (Self::Array(e, s), Value::Array(vs)) => {
                if vs.is_empty() {
                    *e
                } else {
                    for v in vs {
                        if !s.validate(v) {
                            return false;
                        }
                    }
                    true
                }
            }
            (Self::Object(sm), Value::Object(vm)) => {
                for k in sm.keys() {
                    if !vm.contains_key(k) {
                        return false;
                    }
                }
                for (k, v) in vm {
                    if let Some(s) = sm.get(k) {
                        if !s.validate(v) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }
}

impl TryFrom<Vec<Lens>> for Schema {
    type Error = anyhow::Error;

    fn try_from(lenses: Vec<Lens>) -> Result<Self> {
        let mut schema = Schema::Null;
        for lens in lenses {
            lens.transform_schema(&mut schema)?;
        }
        Ok(schema)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
//#[derive(Archive, Deserialize, Serialize)]
pub enum Lens {
    Make(Kind),
    Destroy(Kind),
    AddProperty(Prop),
    RemoveProperty(Prop),
    RenameProperty(Prop, Prop),
    HoistProperty(Prop, Prop),
    PlungeProperty(Prop, Prop),
    Wrap,
    Head,
    LensIn(Prop, Box<Lens>),
    LensMap(Box<Lens>),
    Convert(
        PrimitiveKind,
        PrimitiveKind,
        Vec<(PrimitiveValue, PrimitiveValue)>,
    ),
}

impl Lens {
    pub fn reverse(self) -> Self {
        match self {
            Self::Make(kind) => Self::Destroy(kind),
            Self::Destroy(kind) => Self::Make(kind),
            Self::AddProperty(key) => Self::RemoveProperty(key),
            Self::RemoveProperty(key) => Self::AddProperty(key),
            Self::RenameProperty(from, to) => Self::RenameProperty(to, from),
            Self::HoistProperty(host, name) => Self::PlungeProperty(host, name),
            Self::PlungeProperty(host, name) => Self::HoistProperty(host, name),
            Self::Wrap => Self::Head,
            Self::Head => Self::Wrap,
            Self::LensIn(key, lens) => Self::LensIn(key, Box::new(lens.reverse())),
            Self::LensMap(lens) => Self::LensMap(Box::new(lens.reverse())),
            Self::Convert(from, to, map) => {
                Self::Convert(to, from, map.into_iter().map(|(k, v)| (v, k)).collect())
            }
        }
    }

    pub fn transform_schema(&self, s: &mut Schema) -> Result<()> {
        match (self, s) {
            (Self::Make(k), s) => {
                if *s != Schema::Null {
                    return Err(anyhow!("cannot make schema"));
                }
                *s = match k {
                    Kind::Null => return Err(anyhow!("cannot make a null schema")),
                    Kind::Primitive(PrimitiveKind::Boolean) => Schema::Boolean,
                    Kind::Primitive(PrimitiveKind::Number) => Schema::Number,
                    Kind::Primitive(PrimitiveKind::Text) => Schema::Text,
                    Kind::Array => Schema::Array(true, Box::new(Schema::Null)),
                    Kind::Object => Schema::Object(Default::default()),
                }
            }
            (Self::Destroy(k), s) => {
                match (k, &s) {
                    (Kind::Primitive(PrimitiveKind::Boolean), Schema::Boolean) => {}
                    (Kind::Primitive(PrimitiveKind::Number), Schema::Number) => {}
                    (Kind::Primitive(PrimitiveKind::Text), Schema::Text) => {}
                    (Kind::Array, Schema::Array(true, s)) => {
                        if **s != Schema::Null {
                            return Err(anyhow!("can't destroy non empty array"));
                        }
                    }
                    (Kind::Object, Schema::Object(m)) => {
                        if !m.is_empty() {
                            return Err(anyhow!("can't destroy non empty object"));
                        }
                    }
                    _ => return Err(anyhow!("can't apply destroy")),
                }
                *s = Schema::Null;
            }
            (Self::AddProperty(key), Schema::Object(m)) => {
                if m.contains_key(key) {
                    return Err(anyhow!("property {} already exists in schema", key));
                }
                m.insert(key.clone(), Schema::Null);
            }
            (Self::RemoveProperty(key), Schema::Object(m)) => {
                match m.get(key) {
                    Some(Schema::Null) => {}
                    Some(_) => return Err(anyhow!("property {} cannot be removed", key)),
                    None => return Err(anyhow!("property {} doesn't exist in schema", key)),
                }
                m.remove(key);
            }
            (Self::RenameProperty(from, to), Schema::Object(m)) => {
                if m.contains_key(to) {
                    return Err(anyhow!("trying to rename to existing property: {}", to));
                }
                if let Some(s) = m.remove(from) {
                    m.insert(to.clone(), s);
                } else {
                    return Err(anyhow!(
                        "cannot rename property that doesn't exist: {}",
                        from
                    ));
                }
            }
            (Self::HoistProperty(host, target), Schema::Object(m)) => {
                if m.contains_key(target) {
                    return Err(anyhow!("target property {} already exists", target));
                }
                if let Some(Schema::Object(host)) = m.get_mut(host) {
                    if let Some(s) = host.remove(target) {
                        m.insert(target.clone(), s);
                    } else {
                        return Err(anyhow!("target property {} doesn't exist", target));
                    }
                } else {
                    return Err(anyhow!("host property {} doesn't exist", host));
                }
            }
            (Self::PlungeProperty(host, target), Schema::Object(m)) => {
                if host == target {
                    return Err(anyhow!("host and target property are the same"));
                }
                let s = if let Some(s) = m.remove(target) {
                    s
                } else {
                    return Err(anyhow!("target property {} doesn't exist", target));
                };
                if let Some(Schema::Object(host)) = m.get_mut(host) {
                    if host.contains_key(target) {
                        return Err(anyhow!("host already contains target property {}", target));
                    }
                    host.insert(target.clone(), s);
                } else {
                    return Err(anyhow!("host property doesn't exist"));
                }
            }
            (Self::Wrap, s) => *s = Schema::Array(false, Box::new(s.clone())),
            (Self::Head, s) => {
                if let Schema::Array(false, s2) = s {
                    *s = (**s2).clone();
                } else {
                    return Err(anyhow!("cannot apply head to {:?}", s));
                }
            }
            (Self::LensIn(key, lens), Schema::Object(m)) if m.contains_key(key) => {
                lens.transform_schema(m.get_mut(key).unwrap())?;
            }
            (Self::LensMap(lens), Schema::Array(_, s)) => lens.transform_schema(s)?,
            (Self::Convert(a, b, m), s) => {
                for (va, vb) in m {
                    if va.kind_of() != *a || vb.kind_of() != *b {
                        return Err(anyhow::anyhow!("invalid map"));
                    }
                }
                match (a, &s) {
                    (PrimitiveKind::Boolean, Schema::Boolean) => {}
                    (PrimitiveKind::Number, Schema::Number) => {}
                    (PrimitiveKind::Text, Schema::Text) => {}
                    _ => return Err(anyhow!("kind doesn't match schema")),
                }
                *s = match b {
                    PrimitiveKind::Boolean => Schema::Boolean,
                    PrimitiveKind::Number => Schema::Number,
                    PrimitiveKind::Text => Schema::Text,
                }
            }
            (_, s) => return Err(anyhow!("invalid lens for schema: {:?} {:?}", self, s)),
        }
        Ok(())
    }

    pub fn transform_value(&self, v: &mut Value) {
        match (self, v) {
            (Lens::Make(k), v) => {
                *v = match k {
                    Kind::Null => Value::Null,
                    Kind::Primitive(PrimitiveKind::Boolean) => {
                        Value::Primitive(PrimitiveValue::Boolean(false))
                    }
                    Kind::Primitive(PrimitiveKind::Number) => {
                        Value::Primitive(PrimitiveValue::Number(0))
                    }
                    Kind::Primitive(PrimitiveKind::Text) => {
                        Value::Primitive(PrimitiveValue::Text("".into()))
                    }
                    Kind::Array => Value::Array(vec![]),
                    Kind::Object => Value::Object(Default::default()),
                };
            }
            (Lens::Destroy(_), v) => {
                *v = Value::Null;
            }
            (Lens::AddProperty(key), Value::Object(m)) => {
                m.insert(key.clone(), Value::Null);
            }
            (Lens::RemoveProperty(key), Value::Object(m)) => {
                m.remove(key);
            }
            (Lens::RenameProperty(from, to), Value::Object(m)) => {
                if let Some(v) = m.remove(from) {
                    m.insert(to.clone(), v);
                }
            }
            (Lens::HoistProperty(host, target), Value::Object(m)) => {
                if let Some(Value::Object(host)) = m.get_mut(host) {
                    if let Some(v) = host.remove(target) {
                        m.insert(target.clone(), v);
                    }
                }
            }
            (Lens::PlungeProperty(host, target), Value::Object(m)) => {
                if let Some(v) = m.remove(target) {
                    if let Some(Value::Object(host)) = m.get_mut(host) {
                        host.insert(target.clone(), v);
                    } else {
                        m.insert(target.clone(), v);
                    }
                }
            }
            (Lens::Wrap, v) => {
                *v = Value::Array(vec![v.clone()]);
            }
            (Lens::Head, v) => {
                if let Value::Array(vs) = &v {
                    if let Some(head) = vs.get(0) {
                        *v = head.clone();
                    }
                }
            }
            (Lens::LensIn(key, lens), Value::Object(m)) => {
                if let Some(v) = m.get_mut(key) {
                    lens.transform_value(v);
                }
            }
            (Lens::LensMap(lens), Value::Array(vs)) => {
                for v in vs.iter_mut() {
                    lens.transform_value(v);
                }
            }
            (Lens::Convert(_, k, m), Value::Primitive(p)) => {
                for (k, v) in m {
                    if k == p {
                        *p = v.clone();
                        break;
                    }
                }
                *p = match k {
                    PrimitiveKind::Boolean => PrimitiveValue::Boolean(false),
                    PrimitiveKind::Number => PrimitiveValue::Number(0),
                    PrimitiveKind::Text => PrimitiveValue::Text("".into()),
                };
            }
            _ => {}
        }
    }
}

pub fn transform(a: &[Lens], b: &[Lens]) -> Vec<Lens> {
    let mut prefix = 0;
    for (a, b) in a.iter().zip(b) {
        if a == b {
            prefix += 1;
        } else {
            break;
        }
    }
    let mut c = Vec::with_capacity(a.len() + b.len() - 2 * prefix);
    for a in a[prefix..].iter().rev() {
        c.push(a.clone().reverse());
    }
    for b in b[prefix..].iter() {
        c.push(b.clone());
    }
    c
}
