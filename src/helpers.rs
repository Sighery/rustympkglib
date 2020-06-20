/// Clean a given tree-sitter-bash `raw_string` or `string`.
///
/// These nodes are wrapped in single or double quotes respectively. To interact with the data,
/// we need to clean up these wrapping quotes, which this function can be used for.
///
/// Empty `raw_string`s or `string`s just return an empty `&str`. Other strings get their first
/// and last character "removed". Take a look at the unit tests for examples.
pub fn cleanup_rawstring(raw_string: &str) -> &str {
    let len = raw_string.len();
    if len <= 2 {
        ""
    } else {
        &raw_string[1..len - 1]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_string_returns_empty_string() {
        assert_eq!("", cleanup_rawstring(r#""#));
        assert_eq!("", cleanup_rawstring(r#""""#));
        assert_eq!("", cleanup_rawstring(r#"''"#));
    }

    #[test]
    fn string_is_cleaned_as_expected() {
        assert_eq!(
            "https://github.com/Sighery/rustympkg",
            cleanup_rawstring(r#"'https://github.com/Sighery/rustympkg'"#)
        );
        assert_eq!(
            "https://github.com/Sighery/rustympkg",
            cleanup_rawstring(r#""https://github.com/Sighery/rustympkg""#)
        );
    }
}
