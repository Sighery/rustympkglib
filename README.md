A _rusty_ (and very much incomplete) crate library for dealing with Arch
Linux's `PKGBUILD` files and implement some of `makepkg`'s (or related tools)
functionality.

### Limitations

So far this crate can only parse certain key variables and arrays in a
PKGBUILD file. It can't actually do anything with the data other than display
it as of now. In the near future variables should be editable, and any edit
should be written back into the PKGBUILD file.

### Usage

This is a library crate, a CLI tool resembling `makepkg` called [rustympkg][]
that makes use of this library's code for its functionality (found it easier
to separate concerns and dependencies this way) is also available. Check the
CLI tool's README for more information on its status and what it can do so
far.

This being the case, and with the current limitations, the usage is mostly up
to you. There's the [docs.rs documentation][documentation], and some examples
of usage can be seen in the unit tests in the code.


[Documentation]: https://docs.rs/rustympkglib
[rustympkg]: https://github.com/Sighery/rustympkg
