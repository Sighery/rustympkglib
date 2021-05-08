//! A _rusty_ (and very much incomplete) crate library for dealing with Arch Linux's `PKGBUILD`
//! files and implement some of `makepkg`'s (or related tools) functionality.
//!
//! This crate so far can only parse certain key variables and arrays in a PKGBUILD file. In the
//! near future it will also be able to edit those key variables and write it back into the
//! PKGBUILD.
use std::fmt;

mod helpers;
pub mod pkgbuild;
pub mod pkgdata;

/// A list of possible PKGBUILD/makepkg error kinds used in `rustympkglib`.
#[derive(Debug, PartialEq, Eq)]
#[non_exhaustive]
#[allow(clippy::upper_case_acronyms)]
pub enum ErrorKind {
    /// Error trying to validate some field or value. For example: `pkgname`s that contain illegal
    /// characters.
    ValidationError,
    /// Error trying to parse the given PKGBUILD file. This error happens at the parsing level, so
    /// chances are it'll be something illegal with the file or the Bash code within.
    ParseError,
    /// Error used when the PKGBUILD file could be parsed, but it doesn't follow the documentation
    /// on things such as containing all the required fields.
    InvalidPKGBUILDError,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// Error interface used across `rustympkglib`.
#[derive(Debug, PartialEq, Eq)]
pub struct Error {
    pub kind: ErrorKind,
    pub msg: String,
}

impl Error {
    pub fn new(kind: ErrorKind, msg: &str) -> Error {
        Error {
            kind,
            msg: msg.to_string(),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.kind, self.msg)
    }
}
