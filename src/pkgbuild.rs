use tree_sitter::{Language, Node, Parser, Tree};

extern "C" {
    fn tree_sitter_bash() -> Language;
}

use crate::{Error, ErrorKind};

/// Struct used to walk a tree of nodes.
///
/// After creation, it can be walked since it implements `Iterator`.
pub struct TreeWalker<'a> {
    nodes: Vec<Node<'a>>,
    index: usize,
}

impl TreeWalker<'_> {
    /// Create a new `TreeWalker`.
    ///
    /// ```rust
    /// use rustympkglib::pkgbuild::{Pkgbuild, TreeWalker};
    ///
    /// let source_code = r#"
    /// pkgname=testing-package
    /// pkgver=0.1.0
    /// pkgrel=1
    /// arch=('any')
    /// license=('MIT')
    /// "#;
    ///
    /// let pkgbuild = Pkgbuild::new(&source_code).unwrap();
    /// let root_node = pkgbuild.tree.root_node();
    /// let walker = TreeWalker::new(root_node);
    ///
    /// for node in walker {
    ///     let node_kind = node.kind();
    ///     let text = node.utf8_text(&pkgbuild.source).unwrap();
    ///     println!("Node kind: {:#?}\nNode text: {:#?}", node_kind, text);
    /// }
    /// ```
    pub fn new(node: Node<'_>) -> TreeWalker<'_> {
        let mut nodes: Vec<Node> = Vec::new();
        TreeWalker::traverse(node, &mut nodes);

        TreeWalker { nodes, index: 0 }
    }

    /// Recursive function that will fetch all nodes and store them in a given Vector.
    ///
    /// Not meant to be called. `TreeWalker` implements `Iterator` so initialise `TreeWalker` and
    /// then loop over it.
    fn traverse<'a>(node: Node<'a>, collection: &mut Vec<Node<'a>>) {
        collection.push(node);
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            TreeWalker::traverse(child, collection);
        }
    }
}

impl<'a> Iterator for TreeWalker<'a> {
    type Item = Node<'a>;

    fn next(&mut self) -> Option<Node<'a>> {
        if self.index >= self.nodes.len() {
            None
        } else {
            let node = self.nodes[self.index];
            self.index += 1;

            Some(node)
        }
    }
}

/// Struct used to parse a PKGBUILD file. This contains fairly low-level fields such as the
/// `parser` and the source code.
///
/// This won't fetch any of the data inside the PKGBUILD file. To parse the data and make it
/// available inside Rust, you'll want to use [PkgData][].
///
/// [PkgData]: ../pkgdata/struct.PkgData.html
pub struct Pkgbuild {
    pub source: Vec<u8>,
    pub parser: Parser,
    pub tree: Tree,
}

impl Pkgbuild {
    /// Create a new Pkgbuild from a given PKGBUILD source code
    ///
    /// ```rust
    /// # use rustympkglib::pkgbuild::Pkgbuild;
    /// let source_code = r#"
    /// pkgname=testing-package
    /// pkgver=0.1.0
    /// pkgrel=1
    /// arch=('any')
    /// license=('MIT')
    /// "#;
    ///
    /// let pkgbuild = Pkgbuild::new(&source_code).unwrap();
    ///
    /// assert_eq!(pkgbuild.source, source_code.as_bytes().iter().copied().collect::<Vec<u8>>());
    /// ```
    pub fn new(source: &str) -> Result<Pkgbuild, Error> {
        let mut parser = Parser::new();

        let language = unsafe { tree_sitter_bash() };
        parser.set_language(language).unwrap();

        let tree = match parser.parse(source, None) {
            Some(tree) => tree,
            None => {
                return Err(Error::new(
                    ErrorKind::ParseError,
                    "failed to parse source code",
                ));
            }
        };

        Ok(Pkgbuild {
            source: source.as_bytes().iter().copied().collect(),
            parser,
            tree,
        })
    }
}
