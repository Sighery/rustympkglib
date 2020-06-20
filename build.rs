use std::path::PathBuf;

fn compile_tree_sitter_cpp_lib(name: &str) {
    let scanner_lib = format!("{}-scanner", name);
    let parser_lib = format!("{}-parser", name);
    println!("cargo:rustc-link-lib=static={}", scanner_lib);
    println!("cargo:rustc-link-lib=static={}", parser_lib);

    let dir: PathBuf = [name, "src"].iter().collect();
    cc::Build::new()
        .cpp(true)
        .flag("-w")
        .include(&dir)
        .file(dir.join("scanner.cc"))
        .compile(&scanner_lib);
    cc::Build::new()
        .flag("-w")
        .include(&dir)
        .file(dir.join("parser.c"))
        .compile(&parser_lib);
}

fn main() {
    compile_tree_sitter_cpp_lib("tree-sitter-bash")
}
