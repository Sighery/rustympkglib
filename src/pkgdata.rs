use crate::helpers;
use crate::pkgbuild;
use crate::pkgbuild::Pkgbuild;
use crate::{Error, ErrorKind};

extern crate serde;

use serde::Serialize;

/// Representation of the key `pkgver` in a PKGBUILD
#[derive(Debug, Serialize, Eq)]
pub struct Pkgver(String);

impl Pkgver {
    /// Validate and create a new `Pkgname` instance
    ///
    /// The `pkgver` key in a PKGBUILD file must follow the following rules:
    /// * Can only contain letters, numbers, periods, and underscores
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rustympkglib::pkgdata::Pkgver;
    /// assert!(Pkgver::new("0.1.0-alpha").is_err());
    /// assert!(Pkgver::new("0.1.0_alpha").is_ok());
    /// ```
    pub fn new(version: &str) -> Result<Pkgver, Error> {
        let check = |x: char| x.is_alphanumeric() || x == '.' || x == '_';

        if !version.chars().all(check) {
            return Err(Error::new(
                ErrorKind::ValidationError,
                "pkgver can only contain letters, numbers, periods and underscores",
            ));
        }

        Ok(Pkgver(version.to_string()))
    }
}

impl PartialEq for Pkgver {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl PartialEq<str> for Pkgver {
    fn eq(&self, other: &str) -> bool {
        self.0[..] == other[..]
    }
}

impl PartialEq<&str> for Pkgver {
    fn eq(&self, other: &&str) -> bool {
        self.0[..] == other[..]
    }
}

/// Representation of the key `pkgname` in a PKGBUILD
#[derive(Debug, Serialize, Eq, PartialEq)]
pub enum Pkgname {
    Single(String),
    Multiple(Vec<String>),
}

impl Pkgname {
    /// Validate and create a new `Pkgname` instance
    ///
    /// The `pkgname` key in a PKGBUILD file must follow the following rules:
    /// * Can't start with hyphens
    /// * Can't start with dots
    /// * Can only contain lowercase alphanumerics or `@._+-`
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rustympkglib::pkgdata::Pkgname;
    /// assert!(Pkgname::new("-test-package@._+-").is_err());
    /// assert!(Pkgname::new(".test-package@._+-").is_err());
    /// assert!(Pkgname::new("test-package@._+-").is_ok());
    /// ```
    pub fn new(pkgname: &str) -> Result<Pkgname, Error> {
        let names = match (
            pkgname.as_bytes()[0] as char,
            pkgname.as_bytes()[pkgname.len() - 1] as char,
        ) {
            ('(', ')') => pkgname[1..pkgname.len()-1]
                .split(',')
                .map(|s| s.trim().to_string())
                .collect(),
            _ => vec![pkgname.to_string()],
        };
        for name in &names {
            let check = |x: char| {
                match x {
                    'a'..='z' | '0'..='9'|'@'|'.'|'_'|'+'|'-'  => false,
                    _ => true,
                }
                    };
            if let Some(_) = name.rfind(check) {
                return Err(Error::new(
                    ErrorKind::ValidationError,
                    "pkgname can only contain lowercase alphanumerics or @._+-",
                ));
            }

            for (index, character) in name.chars().enumerate() {
                if index == 0 && character == '-' {
                    return Err(Error::new(
                        ErrorKind::ValidationError,
                        "pkgname can't start with hyphens",
                    ));
                } else if index == 0 && character == '.' {
                    return Err(Error::new(
                        ErrorKind::ValidationError,
                        "pkgname can't start with dots",
                    ));
                }
            }
        }
        if names.len() == 1 {
            Ok(Pkgname::Single(names[0].clone()))
        } else {
            Ok(Pkgname::Multiple(names))
        }
    }
}

impl PartialEq<str> for Pkgname {
    fn eq(&self, other: &str) -> bool {
        match self {
            Pkgname::Single(str) => str[..] == other[..],
            _ => false,
        }
    }
}

impl PartialEq<&str> for Pkgname {
    fn eq(&self, other: &&str) -> bool {
        match self {
            Pkgname::Single(str) => str[..] == other[..],
            _ => false,
        }
    }
}

/// Used to keep track of the progress when walking the nodes tree
#[derive(Debug)]
enum State<'a> {
    VariableAssignment(&'a str),
    NodeArray(&'a str),
    Other,
}

/// Representation of a PKGBUILD file
///
/// Currently it only handles a small subset of all the available keys in a PKGBUILD. Check the
/// fields themselves, they match the PKGBUILD's keys. More information on the available keys in
/// the [Arch Linux wiki page for PKGBUILD][PKGBUILD wiki].
///
/// It also only handles the base keys, and not complex ones such as architecture-specific source
/// or integrity keys (`source_x86_64` or `sha256sums_x86_64`).
///
/// Most fields are optional (values are `Option`), while a few are always required. In
/// particular, `pkgname` and `pkgver`, as well as required, must follow certain rules as well.
/// Check [Pkgname][] and [Pkgver][] for more information.
///
/// [PKGBUILD wiki]: https://wiki.archlinux.org/index.php/PKGBUILD
/// [Pkgname]: struct.Pkgname.html
/// [Pkgver]: struct.Pkgver.html
#[derive(Debug, Serialize)]
pub struct PkgData {
    pub pkgname: Pkgname,
    pub pkgver: Pkgver,
    pub pkgrel: usize,
    pub epoch: Option<usize>,
    pub pkgdesc: Option<String>,
    pub arch: Vec<String>,
    pub url: Option<String>,
    pub license: Option<Vec<String>>,
    pub depends: Option<Vec<String>>,
    pub optdepends: Option<Vec<String>>,
    pub makedepends: Option<Vec<String>>,
    pub checkdepends: Option<Vec<String>>,
    pub provides: Option<Vec<String>>,
    pub conflicts: Option<Vec<String>>,
    pub replaces: Option<Vec<String>>,
    pub source: Option<Vec<String>>,
    pub validpgpkeys: Option<Vec<String>>,
    pub md5sums: Option<Vec<String>>,
    pub sha1sums: Option<Vec<String>>,
    pub sha256sums: Option<Vec<String>>,
    pub sha224sums: Option<Vec<String>>,
    pub sha384sums: Option<Vec<String>>,
    pub sha512sums: Option<Vec<String>>,
    pub b2sums: Option<Vec<String>>,
}

impl PkgData {
    /// Parse a PKGBUILD source into a PkgData representation.
    ///
    /// Check the [PKGBUILD wiki entry][PKGBUILD wiki] and [PKGBUILD.proto] for documentation on
    /// the PKGBUILD file.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rustympkglib::pkgdata::PkgData;
    /// let source_code = r#"
    /// pkgname=testing-package
    /// pkgver=0.1.0
    /// pkgrel=1
    /// arch=('any')
    /// license=('MIT')
    /// "#;
    ///
    /// let pkgdata = PkgData::from_source(source_code).unwrap();
    /// println!("{:#?}", pkgdata);
    ///
    /// assert_eq!(pkgdata.pkgname, "testing-package");
    /// assert_eq!(pkgdata.pkgver, "0.1.0");
    /// assert_eq!(pkgdata.pkgrel, 1);
    /// assert_eq!(pkgdata.arch, vec!["any".to_string()]);
    /// assert_eq!(pkgdata.license, Some(vec!["MIT".to_string()]));
    /// ```
    ///
    /// [PKGBUILD wiki]: https://wiki.archlinux.org/index.php/PKGBUILD
    /// [PKGBUILD.proto]: https://git.archlinux.org/pacman.git/tree/proto/PKGBUILD.proto
    #[allow(clippy::cognitive_complexity)]
    pub fn from_source(source_code: &str) -> Result<PkgData, Error> {
        let mut pkgname: Option<Pkgname> = None;
        let mut pkgver: Option<Pkgver> = None;
        let mut pkgrel: Option<usize> = None;
        let mut arch: Option<Vec<String>> = None;

        let mut epoch: Option<usize> = None;
        let mut pkgdesc: Option<String> = None;
        let mut url: Option<String> = None;
        let mut license: Option<Vec<String>> = None;
        let mut depends: Option<Vec<String>> = None;
        let mut optdepends: Option<Vec<String>> = None;
        let mut makedepends: Option<Vec<String>> = None;
        let mut checkdepends: Option<Vec<String>> = None;
        let mut provides: Option<Vec<String>> = None;
        let mut conflicts: Option<Vec<String>> = None;
        let mut replaces: Option<Vec<String>> = None;
        let mut source: Option<Vec<String>> = None;
        let mut validpgpkeys: Option<Vec<String>> = None;
        let mut md5sums: Option<Vec<String>> = None;
        let mut sha1sums: Option<Vec<String>> = None;
        let mut sha256sums: Option<Vec<String>> = None;
        let mut sha224sums: Option<Vec<String>> = None;
        let mut sha384sums: Option<Vec<String>> = None;
        let mut sha512sums: Option<Vec<String>> = None;
        let mut b2sums: Option<Vec<String>> = None;

        let mut state = State::Other;
        let pkgbuild = Pkgbuild::new(source_code)?;
        let walker = pkgbuild::TreeWalker::new(pkgbuild.tree.root_node());

        for node in walker {
            let node_kind = node.kind();
            let mut text = node.utf8_text(&pkgbuild.source).unwrap();

            match node_kind {
                "variable_assignment" => {
                    // Only assign if this variable is under the root node `program`
                    if node.parent().unwrap().kind() == "program" {
                        state = State::VariableAssignment("");
                    }
                }
                "variable_name" => match state {
                    State::VariableAssignment(_) => {
                        state = State::VariableAssignment(text);
                    }
                    _ => continue,
                },
                "=" | "(" => match state {
                    State::VariableAssignment(_) | State::NodeArray(_) => continue,
                    _ => state = State::Other,
                },
                "array" => match state {
                    State::VariableAssignment(variable) => {
                        state = State::NodeArray(variable);
                    }
                    _ => continue,
                },
                "word" | "string" | "raw_string" => {
                    if node_kind == "raw_string" || node_kind == "string" {
                        text = helpers::cleanup_rawstring(text);
                    }

                    match state {
                        State::VariableAssignment(variable) => match variable {
                            "pkgname" => pkgname = Some(Pkgname::new(text)?),
                            "pkgver" => pkgver = Some(Pkgver::new(text)?),
                            "pkgrel" => {
                                pkgrel = Some(text.parse::<usize>().map_err(|_| {
                                    Error::new(
                                        ErrorKind::ValidationError,
                                        "pkgrel must be an integer",
                                    )
                                })?);
                            }
                            "epoch" => {
                                epoch = Some(text.parse::<usize>().map_err(|_| {
                                    Error::new(
                                        ErrorKind::ValidationError,
                                        "epoch must be an integer",
                                    )
                                })?);
                            }
                            "pkgdesc" => pkgdesc = Some(text.to_string()),
                            "url" => url = Some(text.to_string()),
                            _ => eprintln!("Unknown variable `{}`", variable),
                        },
                        State::NodeArray(variable) => match variable {
                            "arch" => match &mut arch {
                                Some(array) => array.push(text.to_string()),
                                None => arch = Some(vec![text.to_string()]),
                            },
                            "license" => match &mut license {
                                Some(array) => array.push(text.to_string()),
                                None => license = Some(vec![text.to_string()]),
                            },
                            "depends" => match &mut depends {
                                Some(array) => array.push(text.to_string()),
                                None => depends = Some(vec![text.to_string()]),
                            },
                            "optdepends" => match &mut optdepends {
                                Some(array) => array.push(text.to_string()),
                                None => optdepends = Some(vec![text.to_string()]),
                            },
                            "makedepends" => match &mut makedepends {
                                Some(array) => array.push(text.to_string()),
                                None => makedepends = Some(vec![text.to_string()]),
                            },
                            "checkdepends" => match &mut checkdepends {
                                Some(array) => array.push(text.to_string()),
                                None => checkdepends = Some(vec![text.to_string()]),
                            },
                            "provides" => match &mut provides {
                                Some(array) => array.push(text.to_string()),
                                None => provides = Some(vec![text.to_string()]),
                            },
                            "conflicts" => match &mut conflicts {
                                Some(array) => array.push(text.to_string()),
                                None => conflicts = Some(vec![text.to_string()]),
                            },
                            "replaces" => match &mut replaces {
                                Some(array) => array.push(text.to_string()),
                                None => replaces = Some(vec![text.to_string()]),
                            },
                            "source" => match &mut source {
                                Some(array) => array.push(text.to_string()),
                                None => source = Some(vec![text.to_string()]),
                            },
                            "validpgpkeys" => match &mut validpgpkeys {
                                Some(array) => array.push(text.to_string()),
                                None => validpgpkeys = Some(vec![text.to_string()]),
                            },
                            "md5sums" => match &mut md5sums {
                                Some(array) => array.push(text.to_string()),
                                None => md5sums = Some(vec![text.to_string()]),
                            },
                            "sha1sums" => match &mut sha1sums {
                                Some(array) => array.push(text.to_string()),
                                None => sha1sums = Some(vec![text.to_string()]),
                            },
                            "sha256sums" => match &mut sha256sums {
                                Some(array) => array.push(text.to_string()),
                                None => sha256sums = Some(vec![text.to_string()]),
                            },
                            "sha224sums" => match &mut sha224sums {
                                Some(array) => array.push(text.to_string()),
                                None => sha224sums = Some(vec![text.to_string()]),
                            },
                            "sha384sums" => match &mut sha384sums {
                                Some(array) => array.push(text.to_string()),
                                None => sha384sums = Some(vec![text.to_string()]),
                            },
                            "sha512sums" => match &mut sha512sums {
                                Some(array) => array.push(text.to_string()),
                                None => sha512sums = Some(vec![text.to_string()]),
                            },
                            "b2sums" => match &mut b2sums {
                                Some(array) => array.push(text.to_string()),
                                None => b2sums = Some(vec![text.to_string()]),
                            },
                            _ => eprintln!("Unknown variable `{}`", variable),
                        },
                        _ => continue,
                    }
                }
                _ => state = State::Other,
            }
        }

        // These variables MUST exist in the PKGBUILD file
        let pkgname = match pkgname {
            Some(pkgname) => pkgname,
            None => {
                return Err(Error::new(
                    ErrorKind::InvalidPKGBUILDError,
                    "pkgname key must exist",
                ))
            }
        };
        let pkgver = match pkgver {
            Some(pkgver) => pkgver,
            None => {
                return Err(Error::new(
                    ErrorKind::InvalidPKGBUILDError,
                    "pkgver key must exist",
                ))
            }
        };
        let pkgrel = match pkgrel {
            Some(pkgrel) => pkgrel,
            None => {
                return Err(Error::new(
                    ErrorKind::InvalidPKGBUILDError,
                    "pkgrel key must exist",
                ))
            }
        };
        let arch = match arch {
            Some(arch) => arch,
            None => {
                return Err(Error::new(
                    ErrorKind::InvalidPKGBUILDError,
                    "arch key must exist",
                ))
            }
        };

        Ok(PkgData {
            pkgname,
            pkgver,
            pkgrel,
            arch,
            epoch,
            pkgdesc,
            url,
            license,
            depends,
            optdepends,
            makedepends,
            checkdepends,
            provides,
            conflicts,
            replaces,
            source,
            validpgpkeys,
            md5sums,
            sha1sums,
            sha256sums,
            sha224sums,
            sha384sums,
            sha512sums,
            b2sums,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pkgver_with_hyphen_should_fail() {
        assert!(Pkgver::new("0.1.0-alpha").is_err());
    }

    #[test]
    fn pkgver_expected_should_work() {
        assert!(Pkgver::new("0.1.0").is_ok());
    }

    #[test]
    fn pkgname_starts_with_hyphen_should_fail() {
        assert!(Pkgname::new("-package12@._+-").is_err());
    }

    #[test]
    fn pkgname_starts_with_dot_should_fail() {
        assert!(Pkgname::new(".package12@._+-").is_err());
    }

    #[test]
    fn pkgname_with_uppercase_should_fail() {
        assert!(Pkgname::new("Package12@._+-").is_err());
    }

    #[test]
    fn pkgname_expected_should_work() {
        assert!(Pkgname::new("package12@._+-").is_ok());
    }

    #[test]
    fn pkgname_multiple_should_work() {
        assert!(Pkgname::new("(package12@._+-, p@ck@ge42)").unwrap() == Pkgname::Multiple(vec!["package12@._+-".to_string(), "p@ck@ge42".to_string()]));
    }

    #[test]
    fn pkgdata_source_with_pkgname_missing_should_fail() {
        let source_code = r#"
pkgver=0.1.0
pkgrel=1
arch=('any')
license=('MIT')
"#;
        let pkgdata = PkgData::from_source(&source_code);
        assert!(pkgdata.is_err());

        let error = pkgdata.unwrap_err();
        let expected_error = Error::new(ErrorKind::InvalidPKGBUILDError, "pkgname key must exist");
        assert_eq!(error, expected_error);
    }

    #[test]
    fn pkgdata_source_with_pkgver_missing_should_fail() {
        let source_code = r#"
pkgname=testing-package
pkgrel=1
arch=('any')
license=('MIT')
"#;
        let pkgdata = PkgData::from_source(&source_code);
        assert!(pkgdata.is_err());

        let error = pkgdata.unwrap_err();
        let expected_error = Error::new(ErrorKind::InvalidPKGBUILDError, "pkgver key must exist");
        assert_eq!(error, expected_error);
    }

    #[test]
    fn pkgdata_source_with_pkgrel_missing_should_fail() {
        let source_code = r#"
pkgname=testing-package
pkgver=0.1.0
arch=('any')
license=('MIT')
"#;
        let pkgdata = PkgData::from_source(&source_code);
        assert!(pkgdata.is_err());

        let error = pkgdata.unwrap_err();
        let expected_error = Error::new(ErrorKind::InvalidPKGBUILDError, "pkgrel key must exist");
        assert_eq!(error, expected_error);
    }

    #[test]
    fn pkgdata_source_with_arch_missing_should_fail() {
        let source_code = r#"
pkgname=testing-package
pkgver=0.1.0
pkgrel=1
license=('MIT')
"#;
        let pkgdata = PkgData::from_source(&source_code);
        assert!(pkgdata.is_err());

        let error = pkgdata.unwrap_err();
        let expected_error = Error::new(ErrorKind::InvalidPKGBUILDError, "arch key must exist");
        assert_eq!(error, expected_error);
    }

    #[test]
    fn pkgdata_source_with_invalid_pkgname() {
        // Most of the validation is done by Pkgname so don't bother exhausting it here
        let source_code = r#"
pkgname=INVALID-PACKAGE
pkgver=0.1.0
pkgrel=1
arch=('any')
license=('MIT')
"#;

        let expected_error = Pkgname::new("INVALID-PACKAGE").unwrap_err();
        let error = PkgData::from_source(&source_code).unwrap_err();

        assert_eq!(error, expected_error);
    }

    #[test]
    fn pkgdata_source_with_invalid_pkgrel() {
        let source_code = r#"
pkgname=testing-package
pkgver=0.1.0
pkgrel=invalid
arch=('any')
license=('MIT')
"#;

        let error = PkgData::from_source(&source_code).unwrap_err();
        let expected_error = Error::new(ErrorKind::ValidationError, "pkgrel must be an integer");

        assert_eq!(error, expected_error);
    }

    #[test]
    fn pkgdata_source_with_invalid_epoch() {
        let source_code = r#"
pkgname=testing-package
pkgver=0.1.0
pkgrel=1
epoch=invalid
arch=('any')
license=('MIT')
"#;

        let error = PkgData::from_source(&source_code).unwrap_err();
        let expected_error = Error::new(ErrorKind::ValidationError, "epoch must be an integer");

        assert_eq!(error, expected_error);
    }

    #[test]
    fn pkgdata_source_with_invalid_pkgver() {
        // Most of the validation is done by Pkgver so don't bother exhausting it here
        let source_code = r#"
pkgname=testing-package
pkgver=0.1.0-alpha
pkgrel=1
arch=('any')
license=('MIT')
"#;

        let error = PkgData::from_source(&source_code).unwrap_err();
        let expected_error = Pkgver::new("0.1.0-alpha").unwrap_err();

        assert_eq!(error, expected_error);
    }

    #[test]
    fn pkgdata_source_key_gets_ignored_if_not_at_root_level() {
        let source_code = r#"
pkgname=testing-package
pkgver=0.1.0
pkgrel=1
arch=('any')
license=('MIT')

prepare() {
	pkgname=overwritten-package
}
"#;

        let pkgdata = PkgData::from_source(&source_code).unwrap();

        assert_eq!(pkgdata.pkgname, "testing-package");
        assert_eq!(pkgdata.pkgver, "0.1.0");
        assert_eq!(pkgdata.pkgrel, 1);
        assert_eq!(pkgdata.arch, vec!["any"]);
        assert_eq!(pkgdata.license, Some(vec!["MIT".to_string()]));
    }

    #[test]
    fn pkgdata_expected_should_work() {
        // Taken from https://github.com/Sighery/terraform-provider-njalla-pkgbuild
        let source_code = r##"
# Maintainer: Sighery
pkgname=terraform-provider-njalla
pkgver=0.7.0
pkgrel=1
pkgdesc="Unofficial Terraform Njalla provider plugin"
url='https://github.com/Sighery/terraform-provider-njalla'
arch=('x86_64')
license=('MIT')
makedepends=('go')
source=(
	"$pkgname-$pkgver.tar.gz::$url/archive/v$pkgver.tar.gz"
)
sha256sums=('29d5b4c94dcfe2260e0d217392e2aa935a6b81e7388f72305fde87f0b680189a')

build() {
	export CGO_LDFLAGS="${LDFLAGS}"
	export GOFLAGS="-trimpath"

	cd $pkgname-$pkgver
	go build -o "${pkgname}_v${pkgver}"
}

package() {
	cd $pkgname-$pkgver

	install -Dm755 "${pkgname}_v${pkgver}" "$pkgdir/usr/bin/${pkgname}_v${pkgver}"

	# MIT license needs to be installed separately
	install -Dm644 LICENSE $pkgdir/usr/share/licenses/$pkgname/LICENSE
}
"##;

        let pkgdata = PkgData::from_source(&source_code).expect("this should have passed");

        assert_eq!(pkgdata.pkgname, "terraform-provider-njalla");
        assert_eq!(pkgdata.pkgver, "0.7.0");
        assert_eq!(pkgdata.pkgrel, 1);
        assert_eq!(
            pkgdata.pkgdesc,
            Some("Unofficial Terraform Njalla provider plugin".to_string())
        );
        assert_eq!(
            pkgdata.url,
            Some("https://github.com/Sighery/terraform-provider-njalla".to_string())
        );
        assert_eq!(pkgdata.arch, vec!["x86_64"]);
        assert_eq!(pkgdata.license, Some(vec!["MIT".to_string()]));
        assert_eq!(pkgdata.makedepends, Some(vec!["go".to_string()]));
        assert_eq!(
            pkgdata.source,
            Some(vec![
                "$pkgname-$pkgver.tar.gz::$url/archive/v$pkgver.tar.gz".to_string()
            ])
        );
        assert_eq!(
            pkgdata.sha256sums,
            Some(vec![
                "29d5b4c94dcfe2260e0d217392e2aa935a6b81e7388f72305fde87f0b680189a".to_string()
            ])
        );

        assert_eq!(pkgdata.epoch, None);
        assert_eq!(pkgdata.depends, None);
        assert_eq!(pkgdata.optdepends, None);
        assert_eq!(pkgdata.checkdepends, None);
        assert_eq!(pkgdata.provides, None);
        assert_eq!(pkgdata.conflicts, None);
        assert_eq!(pkgdata.replaces, None);
        assert_eq!(pkgdata.validpgpkeys, None);
        assert_eq!(pkgdata.md5sums, None);
        assert_eq!(pkgdata.sha224sums, None);
        assert_eq!(pkgdata.sha384sums, None);
        assert_eq!(pkgdata.sha512sums, None);
        assert_eq!(pkgdata.b2sums, None);
    }
}
