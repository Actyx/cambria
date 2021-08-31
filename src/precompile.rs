use crate::lens::{ArchivedSchema, Lenses, Schema};
use heck::CamelCase;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use rkyv::archived_root;
use rkyv::ser::serializers::AllocSerializer;
use rkyv::ser::Serializer;

pub fn precompile(ident: &str, lenses: Lenses) -> TokenStream {
    let mut ser = AllocSerializer::<256>::default();
    ser.serialize_value(&lenses).unwrap();
    let lenses = ser.into_serializer().into_inner().to_vec();
    let lenses_ref = unsafe { archived_root::<Lenses>(&lenses) };

    let schema = lenses_ref.to_schema().unwrap();
    let schema_ref = unsafe { archived_root::<Schema>(&schema) };

    let ident = ident.to_camel_case();
    let structs = precompile_schema(&ident, schema_ref).def;
    let ident = format_ident!("Archived{}", ident);
    let lenses_len = lenses.len();
    let schema_len = schema.len();

    quote! {
        #structs

        impl cambria::Cambria for #ident {
            fn lenses() -> &'static [u8] {
                use cambria::aligned::{Aligned, A8};
                static LENSES: Aligned<A8, [u8; #lenses_len]> = Aligned([#(#lenses),*]);
                &LENSES[..]
            }

            fn schema() -> &'static cambria::ArchivedSchema {
                use cambria::aligned::{Aligned, A8};
                static SCHEMA: Aligned<A8, [u8; #schema_len]> = Aligned([#(#schema),*]);
                unsafe { rkyv::archived_root::<cambria::Schema>(&SCHEMA[..]) }
            }
        }
    }
}

struct PrecompiledSchema {
    ty: TokenStream,
    imp: TokenStream,
    def: TokenStream,
}

fn precompile_schema(key: &str, schema: &ArchivedSchema) -> PrecompiledSchema {
    let ty = format_ident!("{}", key.to_camel_case());
    let key = format_ident!("{}", key);
    match schema {
        ArchivedSchema::Null => PrecompiledSchema {
            ty: quote!(()),
            imp: quote! {
                pub #key: (),
            },
            def: quote!(),
        },
        ArchivedSchema::Boolean => PrecompiledSchema {
            ty: quote!(bool),
            imp: quote! {
                #[with(cambria::Bool)]
                pub #key: bool,
            },
            def: quote!(),
        },
        ArchivedSchema::Number => PrecompiledSchema {
            ty: quote!(i64),
            imp: quote! {
                #[with(cambria::Number)]
                pub #key: i64,
            },
            def: quote!(),
        },
        ArchivedSchema::Text => PrecompiledSchema {
            ty: quote!(String),
            imp: quote! {
                pub #key: String,
            },
            def: quote!(),
        },
        ArchivedSchema::Array(_, s) => {
            let s = precompile_schema("p", s);
            let ty = s.ty;
            let def = s.def;
            PrecompiledSchema {
                ty: quote!(Vec<#ty>),
                imp: quote! {
                    pub #key: Vec<#ty>,
                },
                def,
            }
        }
        ArchivedSchema::Object(m) => {
            let mut imp = vec![];
            let mut def = vec![];
            for (k, v) in m {
                let s = precompile_schema(k.as_str(), v);
                imp.push(s.imp);
                def.push(s.def);
            }
            PrecompiledSchema {
                ty: quote!(#ty),
                imp: quote! {
                    #key: #ty,
                },
                def: quote! {
                    #[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
                    #[derive(rkyv::Archive, rkyv::Deserialize, rkyv::Serialize)]
                    #[archive_attr(derive(Debug, Eq, Hash, PartialEq), repr(C))]
                    pub struct #ty {
                        #(#imp)*
                    }

                    #(#def)*
                },
            }
        }
    }
}
