use std::{str::FromStr, collections::{HashSet, BTreeSet}};

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::ToTokens;
use semver::Version;
use syn::{spanned::Spanned, punctuated::Punctuated};

/// """unwraps""" a syn result by returning it's equivalent token stream
macro_rules! unwrap_res {
    ($e:expr) => {{
        let __res = $e;
        match __res {
            Ok(__success) => __success,
            Err(__error) => return __error.into_compile_error().into()
        }
    }}
}

/// Formats the new struct name given the original and a version
fn format_versioned_ident(ident: &syn::Ident, version: Version) -> syn::Ident {
    quote::format_ident!(
        "{}_v{}{}{}",
        ident,
        version.major,
        version.minor,
        version.patch
    )
}

/// Gets a [`semver::Version`] from a [`syn::LitStr`]
fn get_version_from_litstr(str: &syn::LitStr) -> syn::Result<Version> {
    Version::from_str(str.value().as_str())
        .map_err(|e| syn::Error::new(
            str.span(),
            format!("Version must be a valid semantic versioning number: {}", e).as_str()
        ))
}

/// Pulls a [`syn::LitStr`] from an attribute, assuming it is of the format `brw_version = "litstr"`
fn get_litstr_from_attr(attr: &syn::Attribute) -> syn::Result<syn::LitStr> {
    match attr.parse_meta()? {
        syn::Meta::NameValue(value) => match value.lit {
            syn::Lit::Str(litstr) => Ok(litstr),
            other => Err(syn::Error::new(
                other.span(),
                "Version argument must be a string literal"
            ))
        },
        other => Err(syn::Error::new(
            other.span(),
            "brw_version attributes use the form #[brw_version = <version>]"
        ))
    }
}

/// Gets the first version found in all of a field's attribute
fn get_version_from_field_attrs(field: &syn::Field) -> syn::Result<Option<Version>> {
    for attribute in field.attrs.iter() {
        if !attribute.path.is_ident("brw_version") { continue; }

        let version_string = get_litstr_from_attr(&attribute)?;
        let version = get_version_from_litstr(&version_string)?;
        return Ok(Some(version))
    }

    Ok(None)
}

/// Generates a [`syn::Expr`] that represents the provided version
fn version_expr(version: &Version) -> syn::Expr {
    let major = syn::LitInt::new(format!("{}", version.major).as_str(), Span::call_site());
    let minor = syn::LitInt::new(format!("{}", version.minor).as_str(), Span::call_site());
    let patch = syn::LitInt::new(format!("{}", version.patch).as_str(), Span::call_site());

    syn::parse_quote! { ::semver::Version::new(#major, #minor, #patch) }
}

/// Generates a [`From`] impl between the two versions
fn generate_from_impl(
    previous: &Version,
    current: &Version,
    reference: &syn::ItemStruct,
    output: &mut proc_macro2::TokenStream,
    is_main: bool,
) -> syn::Result<()> {
    // We accumulate our internal patterns as token streams to make it easier
    let mut from_tokens = vec![];
    
    // Count the number of tuple items that we have gone through so far
    let mut unnamed_counter = 0;
    for field in reference.fields.iter() {
        // If there is an ident (the field is named) we want that, but if not then we need to keep track of
        // our tuple field index
        let id = if let Some(id) = field.ident.as_ref() {
            id.to_token_stream()
        } else {
            unnamed_counter += 1;
            syn::Member::Unnamed(syn::Index {
                index: unnamed_counter - 1,
                span: field.span()
            }).to_token_stream()
        };

        // If there is a version on the field then we need to do some version checks, otherwise we can just add it
        if let Some(field_version) = get_version_from_field_attrs(&field)? {
            if field_version > *current { continue; }

            if field_version > *previous {
                from_tokens.push(quote::quote!(#id: Default::default(),).to_token_stream());
            } else {
                from_tokens.push(quote::quote!(#id: other.#id,));
            }
        } else {
            from_tokens.push(quote::quote!(#id: other.#id,));
        }
    }

    // If this is the *main* struct that we are generating a `From` impl for, we need to use the reference struct's
    // ident instead of generating a new one
    let current_id = if is_main {
        reference.ident.clone()
    } else {
        format_versioned_ident(&reference.ident, current.clone())
    };
    let prev_id = format_versioned_ident(&reference.ident, previous.clone());

    // We generate a second from impl if the versions are identical
    let stmts = from_tokens.iter();
    let stmts2 = from_tokens.iter();

    quote::quote! {
        impl From<#prev_id> for #current_id {
            fn from(other: #prev_id) -> Self {
                Self {
                    #(#stmts)*
                }
            }
        }
    }.to_tokens(output);

    if *current == *previous {
        quote::quote! {
            impl From<#current_id> for #prev_id {
                fn from(other: #current_id) -> Self {
                    Self {
                        #(#stmts2)*
                    }
                }
            }
        }.to_tokens(output);
    }

    Ok(())
}

#[proc_macro_attribute]
pub fn binrw_versioned(attributes: TokenStream, item: TokenStream) -> TokenStream {
    // The current version is a string that we are going to parse into semver
    let current_version = syn::parse_macro_input!(attributes as syn::LitStr);
    let mut item_struct = syn::parse_macro_input!(item as syn::ItemStruct);

    // Get the current version as semver, otherwise make an error out of it
    let Ok(current_version) = Version::from_str(current_version.value().as_str()) else {
        return syn::Error::new(current_version.span(), "Current version must be a valid semantic versioning number").into_compile_error().into();
    };

    // Go through all of the fields and figure out which ones have associated versions
    let mut unique_versions = BTreeSet::new();
    unique_versions.insert(current_version.clone());
    for field in item_struct.fields.iter() {
        if let Some(version) = unwrap_res!(get_version_from_field_attrs(field)) {
            let _ = unique_versions.insert(version);
        }
    }

    // Each of these checks goes into our BinRead implementation for the structure
    // so that they can, well, be properly read from
    //
    // Since our macro generates `From` impls on all previous versions, we can safely call `Self::from`
    //
    // Note that we *don't* have to do this for writing, since when we write we are just going to call the write impl for the current
    // version prefixed by our actual version
    let checks: Vec<syn::ExprIf> = unique_versions.iter().map(|version| {
        // Get the expression for the generated code
        let expr = version_expr(version);

        // Get the ident for the versioned struct
        let versioned_struct = format_versioned_ident(&item_struct.ident, version.clone());

        // Write the check expression, this will output to something like
        // ```
        // if __version == ::semver::Version::new(1, 0, 0) {
        //  return Ok(Self::from(TestStruct_v100::read_options(reader, options, ())?));   
        // }
        // ```
        syn::parse_quote! { 
            if __version == #expr {
                return Ok(Self::from(#versioned_struct::read_options(reader, options, ())?));
            }
        }
    })
    .collect();
    
    // Get an iter of our checks for the quote
    let checks = checks.into_iter();
    
    // Get our main struct ID ahead of time
    let item_id = &item_struct.ident;

    // This is what we are returning
    let mut output = proc_macro2::TokenStream::new();
    
    quote::quote! {
        impl ::binrw::BinRead for #item_id {
            type Args = ();
            fn read_options<R: ::std::io::Read + ::std::io::Seek>(
                reader: &mut R,
                options: &::binrw::ReadOptions,
                _: ()
            ) -> binrw::BinResult<Self>
            {
                use ::binrw::BinRead;
                let __version_patch = u8::read(reader)?;
                let __version_minor = u8::read(reader)?;
                let __version_major = u16::read_options(reader, options, ())?;
                let __version = ::semver::Version::new(__version_major as u64, __version_minor as u64, __version_patch as u64);
                #(#checks)*
                return Err(::binrw::Error::Custom {
                    pos: reader.stream_position()?,
                    err: Box::new(format!("Version {} is not supported", __version))
                });
            }
        }
    }.to_tokens(&mut output);

    let current_version_expr = version_expr(&current_version);
    let current_version_ident = format_versioned_ident(&item_struct.ident, current_version.clone());

    quote::quote! {
        impl ::binrw::BinWrite for #item_id {
            type Args = ();
            fn write_options<W: ::std::io::Write + ::std::io::Seek>(
                &self,
                writer: &mut W,
                options: &::binrw::WriteOptions,
                _: ()
            ) -> binrw::BinResult<()>
            {
                use ::binrw::BinWrite;
                let __version = #current_version_expr;
                (__version.patch as u8).write(writer)?;
                (__version.minor as u8).write(writer)?;
                (__version.major as u16).write_options(writer, options, ())?;
                #current_version_ident::write_options(unsafe { std::mem::transmute(self) }, writer, options, ())
            }
        }
    }.to_tokens(&mut output);

    // Accumulate a list of the previous versions as we go
    let mut prev_versions = vec![];

    // We are going to create a struct for each and every unique version, starting at the lowest
    for version in unique_versions {
        // Create a new structure, we will filter out what we don't need soon
        let mut new_struct = item_struct.clone();
        
        // Our filtering is the same regardless of the field
        let old_fields = match &mut new_struct.fields {
            syn::Fields::Unit => continue,
            syn::Fields::Named(named) => &mut named.named,
            syn::Fields::Unnamed(unnamed) => &mut unnamed.unnamed
        };

        // Create a temporary vector of fields to consume
        let mut fields = Punctuated::new();
        std::mem::swap(&mut fields, old_fields);

        for mut field in fields.into_iter() {
            // For each field, if it is versioned and it's version is greater than our version we ignore it
            // otherwise we put it back into our fields
            match unwrap_res!(get_version_from_field_attrs(&field)) {
                Some(field_version) if field_version > version => {},
                _ => {
                    // Let's try and remove our field attribute since it's not going to play nice in the output
                    let mut attrs = vec![];
                    std::mem::swap(&mut attrs, &mut field.attrs);
                    field.attrs = attrs.into_iter().filter(|attr| !attr.path.is_ident("brw_version")).collect();

                    // Add our field back to our struct
                    old_fields.push(field)
                }
            }
        }

        // We create a new struct, even if it is the current version because our binrw impl on the current version is a little different
        new_struct.ident = format_versioned_ident(&new_struct.ident, version.clone());

        // Generate a BinRead/BinWrite impl on the version
        quote::quote! {
            #[::binrw::binrw]
            #[allow(non_camel_case_types)]
            #new_struct
        }.to_tokens(&mut output);

        // Generate a from impl for all previous versions
        for prev_version in prev_versions.iter() {
            unwrap_res!(generate_from_impl(prev_version, &version, &item_struct, &mut output, false));
        }

        unwrap_res!(generate_from_impl(&version, &current_version, &item_struct, &mut output, true));

        prev_versions.push(version);
    }
    
    'remove_attrs: {
        // Our filtering is the same regardless of the field
        let old_fields = match &mut item_struct.fields {
            syn::Fields::Unit => break 'remove_attrs,
            syn::Fields::Named(named) => &mut named.named,
            syn::Fields::Unnamed(unnamed) => &mut unnamed.unnamed
        };
    
        // Create a temporary vector of fields to consume
        let mut fields = Punctuated::new();
        std::mem::swap(&mut fields, old_fields);
    
        for mut field in fields.into_iter() {
            // Let's try and remove our field attribute since it's not going to play nice in the output
            let mut attrs = vec![];
            std::mem::swap(&mut attrs, &mut field.attrs);
            field.attrs = attrs.into_iter().filter(|attr| !attr.path.is_ident("brw_version")).collect();
            // Add our field back to our struct
            old_fields.push(field)
        }
    }

    quote::quote! {
        #item_struct
    }.to_tokens(&mut output);

    output.into()
}
