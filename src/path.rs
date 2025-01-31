//! Contains assertions for [Path]s. See [PathAssertions] for more details.

use crate::{AssertThat, AssertThatData, Failure};

use std::ffi::OsStr;
use std::fmt::Display;
use std::fs::{self, Metadata, ReadDir};
use std::io;
use std::io::ErrorKind;
use std::path::Path;

/// An extension trait to be used on the output of [assert_that](crate::assert_that) with a [Path]
/// argument.
///
/// Examples:
///
/// ```
/// use kernal::prelude::*;
/// use std::path::Path;
///
/// assert_that!(Path::new("i/surely/hope/this/file/does/not.exist"))
///     .is_relative()
///     .has_extension("exist")
///     .does_not_exist();
/// ```
pub trait PathAssertions {

    /// Asserts that the tested path points at an existing entity and the metadata is accessible.
    ///
    /// In the case that the metadata is not accessible (e.g. because of a permission error or
    /// broken symbolic link), both [PathAssertions::does_not_exist] and this method will fail.
    fn exists(self) -> Self;

    /// Asserts that the tested path does not point at an existing entity, but the metadata is
    /// accessible.
    ///
    /// In the case that the metadata is not accessible (e.g. because of a permission error or
    /// broken symbolic link), both [PathAssertions::exist] and this method will fail.
    fn does_not_exist(self) -> Self;

    /// Asserts that the tested path is absolute, i.e. it is independent of the current directory.
    /// See [Path::is_absolute] for more details.
    fn is_absolute(self) -> Self;

    /// Asserts that the tested path is relative, i.e. not absolute. See [Path::is_absolute] for
    /// more details.
    fn is_relative(self) -> Self;

    /// Asserts that the tested path exists on the disk, the metadata is accessible, and it is
    /// pointing at a regular file or a symlink to such a file.
    ///
    /// In the case that the metadata is not accessible (e.g. because of a permission error or
    /// broken symbolic link), [PathAssertions::is_dir] and this method will fail.
    fn is_file(self) -> Self;

    /// Asserts that the tested path exists on the disk, the metadata is accessible, and it is
    /// pointing directly at a regular file without any symlinks.
    ///
    /// In the case that the metadata is not accessible (e.g. because of a permission error or
    /// broken symbolic link), [PathAssertions::is_non_symlink_dir], [PathAssertions::is_symlink],
    /// and this method will fail.
    fn is_non_symlink_file(self) -> Self;

    /// Asserts that the tested path exists on the disk, the metadata is accessible, and it is
    /// pointing at a directory or a symlink to such a directory.
    ///
    /// In the case that the metadata is not accessible (e.g. because of a permission error),
    /// [PathAssertions::is_file], [PathAssertions::is_symlink] and this method will fail.
    fn is_dir(self) -> Self;

    /// Asserts that the tested path exists on the disk, the metadata is accessible, and it is
    /// pointing directly at a directory without any symlinks.
    ///
    /// In the case that the metadata is not accessible (e.g. because of a permission error),
    /// [PathAssertions::is_non_symlink_file], [PathAssertions::is_symlink], and this method will
    /// fail.
    fn is_non_symlink_dir(self) -> Self;

    /// Asserts that the tested path exists on the disk, the metadata is accessible, and it is
    /// pointing at a symbolic link.
    ///
    /// In the case that the metadata is not accessible (e.g. because of a permission error or
    /// broken symbolic link), [PathAssertions::is_file], [PathAssertions::is_dir] and this method
    /// will fail.
    fn is_symlink(self) -> Self;

    /// Asserts that the tested path exists on the disk, the metadata is accessible, and it is not
    /// pointing at a symbolic link.
    fn is_non_symlink(self) -> Self;

    /// Asserts that the tested path has a final component equaling the given file name.
    fn has_file_name(self, file_name: impl AsRef<OsStr>) -> Self;

    /// Asserts that the tested path does not have a final component equaling the given file name.
    fn does_not_have_file_name(self, file_name: impl AsRef<OsStr>) -> Self;

    /// Asserts that the tested path has a final component whose stem (file name without extension)
    /// equals the given file stem.
    fn has_file_stem(self, file_stem: impl AsRef<OsStr>) -> Self;

    /// Asserts that the tested path does not have a final component whose stem (file name without
    /// extension) equals the given file stem.
    fn does_not_have_file_stem(self, file_stem: impl AsRef<OsStr>) -> Self;

    /// Asserts that the tested path has a final component whose extension equals the given
    /// extension.
    fn has_extension(self, extension: impl AsRef<OsStr>) -> Self;

    /// Asserts that the tested path does not have a final component whose extension equals the
    /// given extension.
    fn does_not_have_extension(self, extension: impl AsRef<OsStr>) -> Self;

    /// Asserts that `prefix` is a prefix of the tested path, while only considering full path
    /// components as a match.
    fn starts_with_path(self, prefix: impl AsRef<Path>) -> Self;

    /// Asserts that `prefix` is not a prefix of the tested path, while only considering full path
    /// components as a match.
    fn does_not_start_with_path(self, prefix: impl AsRef<Path>) -> Self;

    /// Asserts that `suffix` is a suffix of the tested path, while only considering full path
    /// components as a match.
    fn ends_with_path(self, suffix: impl AsRef<Path>) -> Self;

    /// Asserts that `suffix` is not a suffix of the tested path, while only considering full path
    /// components as a match.
    fn does_not_end_with_path(self, suffix: impl AsRef<Path>) -> Self;

    /// Asserts that the tested path exists on disk, its metadata is accessible, and it is pointing
    /// at a regular file that has the given content.
    fn is_file_with_content(self, expected_content: impl AsRef<[u8]>) -> Self;

    /// Asserts that the tested path exists on disk, its metadata is accessible, and it is pointing
    /// at a regular file that is empty.
    fn is_empty_file(self) -> Self;

    /// Asserts that the tested path exists on disk, its metadata is accessible, and it is pointing
    /// at a regular file that is not empty.
    fn is_non_empty_file(self) -> Self;

    /// Asserts that the tested path exists on disk, its metadata is accessible, and it is pointing
    /// at an empty directory.
    fn is_empty_dir(self) -> Self;

    /// Asserts that the tested path exists on disk, its metadata is accessible, and it is pointing
    /// at a non-empty directory.
    fn is_non_empty_dir(self) -> Self;

    /// Converts the tested path to a [String], failing if that is not possible, and allows
    /// assertions on it.
    fn to_string(self) -> AssertThat<String>;

    /// Converts the tested path to the data contained in the file it points to and allows
    /// assertions to it. If no such file exists, or it cannot be opened, this method causes a test
    /// failure.
    fn to_content(self) -> AssertThat<Vec<u8>>;

    /// Converts the tested path to the data contained in the file it points to as a string and
    /// allows assertions to it. If no such file exists, it cannot be opened, or its content cannot
    /// be converted to a string (i.e. it is not UTF-8), this method causes a test failure.
    fn to_content_string(self) -> AssertThat<String>;
}

impl Failure {

    fn but_it_was_path<T: AsRef<Path>>(
        self,
        assert_that: &AssertThat<T>,
        and: impl Display
    ) -> Failure {
        self.but_it(format!("was <{}>, {}", assert_that.data().as_ref().display(), and))
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum ExpectedFileType {
    File,
    Dir,
    Symlink
}

fn assert_file_kind<T: AsRef<Path>>(
    assert_that: AssertThat<T>,
    get_metadata: impl FnOnce(&Path) -> io::Result<Metadata>,
    expected_file_types: &[ExpectedFileType],
    expected_it: &str
) -> AssertThat<T> {
    let path = assert_that.data().as_ref();
    let metadata = get_metadata(path);
    let fail = |reason| Failure::new(&assert_that)
        .expected_it(expected_it)
        .but_it_was_path(&assert_that, reason)
        .fail();

    let file_type = match metadata.as_ref().map(Metadata::file_type) {
        Ok(file_type) => file_type,
        Err(error) if error.kind() == ErrorKind::NotFound => fail("which does not exist"),
        Err(_) => fail("whose metadata cannot be accessed")
    };

    if file_type.is_file() && !expected_file_types.contains(&ExpectedFileType::File) {
        fail("which points to a regular file");
    }

    if file_type.is_dir() && !expected_file_types.contains(&ExpectedFileType::Dir) {
        fail("which points to a directory");
    }

    if file_type.is_symlink() && !expected_file_types.contains(&ExpectedFileType::Symlink) {
        fail("which points to a symbolic link");
    }

    assert_that
}

// TODO use OsStr::display once stable: https://github.com/rust-lang/rust/issues/120048

fn assert_has_segment<T: AsRef<Path>>(
    assert_that: AssertThat<T>,
    get_actual_segment: impl Fn(&Path) -> Option<&OsStr>,
    expected_segment: impl AsRef<OsStr>,
    segment_name: &str
) -> AssertThat<T> {
    let expected_segment = expected_segment.as_ref();
    let fail = |reason| Failure::new(&assert_that)
        .expected_it(format!("to have {} <{}>", segment_name, expected_segment.to_string_lossy()))
        .but_it_was_path(&assert_that, reason)
        .fail();

    match get_actual_segment(assert_that.data().as_ref()) {
        Some(actual_segment) =>
            if actual_segment == expected_segment {
                assert_that
            }
            else {
                fail(format!("which has {} <{}>", segment_name, actual_segment.to_string_lossy()))
            },
        None => fail(format!("which has no {}", segment_name))
    }
}

fn assert_does_not_have_segment<T: AsRef<Path>>(
    assert_that: AssertThat<T>,
    get_actual_segment: impl Fn(&Path) -> Option<&OsStr>,
    expected_segment: impl AsRef<OsStr>,
    segment_name: &str
) -> AssertThat<T> {
    let expected_segment = expected_segment.as_ref();

    match get_actual_segment(assert_that.data().as_ref()) {
        Some(actual_segment) =>
            if actual_segment == expected_segment {
                Failure::new(&assert_that)
                    .expected_it(format!(
                        "not to have {} <{}>", segment_name, expected_segment.to_string_lossy()))
                    .but_it_was_path(&assert_that, "which does")
                    .fail()
            }
            else {
                assert_that
            },
        None => assert_that
    }
}

fn assert_is_dir_satisfying<T: AsRef<Path>>(
    assert_that: AssertThat<T>,
    validate_dir: impl Fn(ReadDir) -> bool,
    expected_it: &str,
    reason_on_invalid: &str
) -> AssertThat<T> {
    let fail = |reason| Failure::new(&assert_that)
        .expected_it(expected_it)
        .but_it_was_path(&assert_that, reason)
        .fail();

    let read_dir = assert_that.data().as_ref().read_dir().unwrap_or_else(|error|
        match error.kind() {
            ErrorKind::NotFound => fail("which does not exist"),
            ErrorKind::NotADirectory => fail("which is not a directory"),
            _ => fail("which cannot be opened")
        }
    );

    if !validate_dir(read_dir) {
        fail(reason_on_invalid);
    }

    assert_that
}

fn read_content_or_fail<T: AsRef<Path>>(assert_that: &AssertThat<T>, expected_it: &str) -> Vec<u8> {
    fs::read(assert_that.data())
        .unwrap_or_else(|err| {
            let reason = if err.kind() == ErrorKind::NotFound {
                "which does not exist"
            }
            else {
                "which cannot be opened"
            };

            Failure::new(assert_that)
                .expected_it(expected_it)
                .but_it_was_path(assert_that, reason)
                .fail()
        })
}

impl<T: AsRef<Path>> PathAssertions for AssertThat<T> {

    fn exists(self) -> Self {
        let path = self.data().as_ref();
        let fail = |reason| Failure::new(&self)
            .expected_it("to exist")
            .but_it_was_path(&self, reason)
            .fail();

        match path.try_exists() {
            Ok(true) => self,
            Ok(false) => fail("which does not exist"),
            Err(_) => fail("whose metadata cannot be accessed")
        }
    }

    fn does_not_exist(self) -> Self {
        let path = self.data().as_ref();
        let fail = |reason| Failure::new(&self)
            .expected_it("not to exist")
            .but_it_was_path(&self, reason)
            .fail();

        match path.try_exists() {
            Ok(false) => self,
            Ok(true) => fail("which does exist"),
            Err(_) => fail("whose metadata cannot be accessed")
        }
    }

    fn is_absolute(self) -> Self {
        let path = self.data().as_ref();

        if !path.is_absolute() {
            Failure::new(&self)
                .expected_it("to be absolute")
                .but_it_was_path(&self, "which is relative")
                .fail();
        }

        self
    }

    fn is_relative(self) -> Self {
        let path = self.data().as_ref();

        if !path.is_relative() {
            Failure::new(&self)
                .expected_it("to be relative")
                .but_it_was_path(&self, "which is absolute")
                .fail();
        }

        self
    }

    fn is_file(self) -> Self {
        assert_file_kind(self,
            Path::metadata,
            &[ExpectedFileType::File],
            "to point to a regular file")
    }

    fn is_non_symlink_file(self) -> Self {
        assert_file_kind(self,
            Path::symlink_metadata,
            &[ExpectedFileType::File],
            "to point to a regular file without symbolic link")
    }

    fn is_dir(self) -> Self {
        assert_file_kind(self,
            Path::metadata,
            &[ExpectedFileType::Dir],
            "to point to a directory")
    }

    fn is_non_symlink_dir(self) -> Self {
        assert_file_kind(self,
            Path::symlink_metadata,
            &[ExpectedFileType::Dir],
            "to point to a directory without symbolic link")
    }

    fn is_symlink(self) -> Self {
        assert_file_kind(self,
            Path::symlink_metadata,
            &[ExpectedFileType::Symlink],
            "to point to a symbolic link")
    }

    fn is_non_symlink(self) -> Self {
        assert_file_kind(self,
            Path::symlink_metadata,
            &[ExpectedFileType::File, ExpectedFileType::Dir],
            "not to point to a symbolic link")
    }

    fn has_file_name(self, file_name: impl AsRef<OsStr>) -> Self {
        assert_has_segment(self, Path::file_name, file_name, "file name")
    }

    fn does_not_have_file_name(self, file_name: impl AsRef<OsStr>) -> Self {
        assert_does_not_have_segment(self, Path::file_name, file_name, "file name")
    }

    fn has_file_stem(self, file_stem: impl AsRef<OsStr>) -> Self {
        assert_has_segment(self, Path::file_stem, file_stem, "file stem")
    }

    fn does_not_have_file_stem(self, file_stem: impl AsRef<OsStr>) -> Self {
        assert_does_not_have_segment(self, Path::file_stem, file_stem, "file stem")
    }

    fn has_extension(self, extension: impl AsRef<OsStr>) -> Self {
        assert_has_segment(self, Path::extension, extension, "extension")
    }

    fn does_not_have_extension(self, extension: impl AsRef<OsStr>) -> Self {
        assert_does_not_have_segment(self, Path::extension, extension, "extension")
    }

    fn starts_with_path(self, prefix: impl AsRef<Path>) -> Self {
        let path = self.data().as_ref();
        let prefix = prefix.as_ref();

        if !path.starts_with(prefix) {
            Failure::new(&self)
                .expected_it(format!("to start with <{}>", prefix.display()))
                .but_it(format!("was <{}>", path.display()))
                .fail();
        }

        self
    }

    fn does_not_start_with_path(self, prefix: impl AsRef<Path>) -> Self {
        let path = self.data().as_ref();
        let prefix = prefix.as_ref();

        if path.starts_with(prefix) {
            let prefix_formatted = format!("{}", prefix.display());
            let path_formatted = format!("{}", path.display());
            let suffix = path_formatted.strip_prefix(&prefix_formatted).unwrap();
            let highlighted = format!("[{}]{}", &prefix_formatted, suffix);

            Failure::new(&self)
                .expected_it(format!("not to start with <{}>", prefix.display()))
                .but_it(format!("was <{}>", highlighted))
                .fail();
        }

        self
    }

    fn ends_with_path(self, suffix: impl AsRef<Path>) -> Self {
        let path = self.data().as_ref();
        let suffix = suffix.as_ref();

        if !path.ends_with(suffix) {
            Failure::new(&self)
                .expected_it(format!("to end with <{}>", suffix.display()))
                .but_it(format!("was <{}>", path.display()))
                .fail();
        }

        self
    }

    fn does_not_end_with_path(self, suffix: impl AsRef<Path>) -> Self {
        let path = self.data().as_ref();
        let suffix = suffix.as_ref();

        if path.ends_with(suffix) {
            let suffix_formatted = format!("{}", suffix.display());
            let path_formatted = format!("{}", path.display());
            let prefix = path_formatted.strip_suffix(&suffix_formatted).unwrap();
            let highlighted = format!("{}[{}]", prefix, &suffix_formatted);

            Failure::new(&self)
                .expected_it(format!("not to end with <{}>", suffix.display()))
                .but_it(format!("was <{}>", highlighted))
                .fail();
        }

        self
    }

    fn is_file_with_content(self, expected_content: impl AsRef<[u8]>) -> Self {
        let content = read_content_or_fail(&self, "to point to a file with given content");
        let expected_content = expected_content.as_ref();

        if content != expected_content {
            match (std::str::from_utf8(&content), std::str::from_utf8(expected_content)) {
                (Ok(content), Ok(expected_content)) => {
                    Failure::new(&self)
                        .expected_it(format!("to point to a file with content <{}>",
                            expected_content.escape_debug()))
                        .but_it_was_path(&self,
                            format!("which has content <{}>", content.escape_debug()))
                        .fail()
                },
                _ => {
                    Failure::new(&self)
                        .expected_it(format!("to point to a file with content <{:?}>", expected_content))
                        .but_it_was_path(&self, format!("which has content <{:?}>", content))
                        .fail()
                }
            }
        }

        self
    }

    fn is_empty_file(self) -> Self {
        let expected_it = "to point to an empty file";
        let content = read_content_or_fail(&self, expected_it);
        let fail = |reason| Failure::new(&self)
            .expected_it(expected_it)
            .but_it_was_path(&self, reason)
            .fail();

        if !content.is_empty() {
            if let Ok(content) = std::str::from_utf8(&content) {
                fail(format!("which has content <{}>", content.escape_debug()));
            }
            else {
                fail(format!("which has content <{:?}>", content));
            }
        }

        self
    }

    fn is_non_empty_file(self) -> Self {
        let expected_it = "to point to a non-empty file";
        let content = read_content_or_fail(&self, expected_it);

        if content.is_empty() {
            Failure::new(&self)
                .expected_it(expected_it)
                .but_it_was_path(&self, "which points to an empty file")
                .fail();
        }

        self
    }

    fn is_empty_dir(self) -> Self {
        assert_is_dir_satisfying(self,
            |mut read_dir| read_dir.next().is_none(),
            "to point to an empty directory",
            "which is not empty")
    }

    fn is_non_empty_dir(self) -> Self {
        assert_is_dir_satisfying(self,
            |mut read_dir| read_dir.next().is_some(),
            "to point to a non-empty directory",
            "which is empty")
    }

    fn to_string(self) -> AssertThat<String> {
        let data = self.data.as_ref().to_str()
            .map(str::to_owned)
            .unwrap_or_else(|| Failure::new(&self)
                .expected_it("to be convertible to a string")
                .but_it_was_path(&self, "which is not")
                .fail());
        let expression = format!("<{}> as string", self.expression);

        AssertThat::new(data, expression)
    }

    fn to_content(self) -> AssertThat<Vec<u8>> {
        let content = read_content_or_fail(&self, "to be readable");
        let expression = format!("content of <{}>", self.expression);

        AssertThat::new(content, expression)
    }

    fn to_content_string(self) -> AssertThat<String> {
        let content = read_content_or_fail(&self, "to be readable");
        let content = String::from_utf8(content)
            .unwrap_or_else(|_| Failure::new(&self)
                .expected_it("to contain valid UTF-8")
                .but_it_was_path(&self, "which contains non-UTF-8 data")
                .fail());
        let expression = format!("content of <{}> as string", self.expression);

        AssertThat::new(content, expression)
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::assert_fails;
    use crate::prelude::*;

    use std::{io, path};
    use std::fs::File;
    use std::io::Write;
    use std::panic::{RefUnwindSafe, UnwindSafe};
    use std::path::PathBuf;
    use rstest::rstest;

    use rstest_reuse::{apply, template};

    use tempfile::{NamedTempFile, TempDir};

    const NON_EXISTING_PATH: &str = "/some/path/that/hopefully/does/not/exist";

    struct TempSymlink<DestT> {
        _symlink_dest: DestT,
        _target_dir: TempDir,
        symlink_path: PathBuf
    }

    impl<DestT: AsRef<Path>> TempSymlink<DestT> {

        fn new(
            create_dest: impl FnOnce() -> io::Result<DestT>,
            create_symlink: impl FnOnce(&DestT, &Path) -> io::Result<()>
        ) -> io::Result<TempSymlink<DestT>> {
            let symlink_dest = create_dest()?;
            let target_dir = TempDir::new()?;
            let symlink_path = target_dir.path().join("symlink");
            create_symlink(&symlink_dest, &symlink_path)?;

            Ok(TempSymlink {
                _symlink_dest: symlink_dest,
                _target_dir: target_dir,
                symlink_path
            })
        }
    }

    impl TempSymlink<NamedTempFile> {

        fn new_file() -> io::Result<TempSymlink<NamedTempFile>> {
            TempSymlink::new(
                || NamedTempFile::new(),
                |file, symlink| symlink::symlink_file(file, symlink))
        }
    }

    impl TempSymlink<TempDir> {

        fn new_dir() -> io::Result<TempSymlink<TempDir>> {
            TempSymlink::new(
                || TempDir::new(),
                |file, symlink| symlink::symlink_dir(file, symlink))
        }
    }

    impl TempSymlink<PathBuf> {

        fn new_broken() -> io::Result<TempSymlink<PathBuf>> {
            TempSymlink::new(
                || Ok(PathBuf::from(NON_EXISTING_PATH)),
                |file, symlink| symlink::symlink_file(file, symlink))
        }
    }

    impl<DestT: AsRef<Path>> AsRef<Path> for TempSymlink<DestT> {

        fn as_ref(&self) -> &Path {
            &self.symlink_path
        }
    }

    fn assert_fails_and_was_path<T>(
        assertion: impl Fn() -> T + UnwindSafe,
        expression: &str,
        expected_it: &str,
        but_it_path: impl AsRef<Path>,
        but_it_continuation: &str
    ) {
        assert_that!(assertion)
            .panics_with_message(Failure::from_expression(expression)
                .expected_it(expected_it)
                .but_it(
                    format!("was <{}>, {}", but_it_path.as_ref().display(), but_it_continuation))
                .message());
    }

    fn assert_fails_non_existing<T>(
        assertion: impl FnOnce(AssertThat<&'static str>) -> T + UnwindSafe,
        expected_it: &str
    ) {
        assert_that!(|| assertion(assert_that!(NON_EXISTING_PATH)))
            .panics_with_message(Failure::from_expression("NON_EXISTING_PATH")
                .expected_it(expected_it)
                .but_it(format!("was <{}>, which does not exist", NON_EXISTING_PATH))
                .message());
    }

    // TODO typedef `impl AsRef<Path> + RefUnwindSafe` once stable
    //  https://github.com/rust-lang/rust/issues/63063

    #[template]
    #[rstest]
    #[case::file(NamedTempFile::new().unwrap())]
    #[case::symlink_to_file(TempSymlink::new_file().unwrap())]
    fn file_and_symlink_file(#[case] entity: impl AsRef<Path> + RefUnwindSafe) {}

    #[template]
    #[rstest]
    #[case::dir(TempDir::new().unwrap())]
    #[case::symlink_to_dir(TempSymlink::new_dir().unwrap())]
    fn dir_and_symlink_dir(#[case] entity: impl AsRef<Path> + RefUnwindSafe) {}

    #[template]
    #[rstest]
    #[case::symlink_to_file(TempSymlink::new_file().unwrap())]
    #[case::symlink_to_dir(TempSymlink::new_dir().unwrap())]
    fn symlink(#[case] entity: impl AsRef<Path> + RefUnwindSafe) {}

    #[template]
    #[rstest]
    #[case::file(NamedTempFile::new().unwrap())]
    #[case::dir(TempDir::new().unwrap())]
    #[case::symlink_to_file(TempSymlink::new_file().unwrap())]
    #[case::symlink_to_dir(TempSymlink::new_dir().unwrap())]
    fn existing_entities(#[case] entity: impl AsRef<Path> + RefUnwindSafe) {}

    #[template]
    #[rstest]
    #[case::empty("")]
    #[case::only_root("/")]
    #[case::ancestors("../..")]
    fn paths_with_empty_file_name(#[case] path: &str) {}

    #[template]
    #[rstest]
    #[case::both_empty("", "", "")]
    #[case::both_single_segment("hello", "hello", "")]
    #[case::trivial_empty_prefix("some/path", "", "some/path")]
    #[case::same_path("some/path", "some/path", "")]
    #[case::strict_prefix("some/path", "some", "/path")]
    #[case::strict_prefix_with_root("/some/path", "/some", "/path")]
    #[case::strict_prefix_with_parent("../path", "..", "/path")]
    fn true_prefixes_with_unmatched_path(
        #[case] path: &str,
        #[case] prefix: &str,
        #[case] unmatched_path: &str) {}

    #[template]
    #[rstest]
    #[case::empty_path("", "segment")]
    #[case::different_single_segment("segment1", "segment2")]
    #[case::incomplete_single_segment("segment", "seg")]
    #[case::different_last_segment("some/path", "some/bath")]
    #[case::incomplete_last_segment("some/path", "some/pa")]
    #[case::different_last_segment_with_root("/some/path/plus", "/some/bath")]
    #[case::longer_prefix("some/path", "some/path/but/longer")]
    #[case::more_parents("../path", "../../path")]
    #[case::rooted_prefix_on_unrooted_path("some/path", "/some")]
    fn false_prefixes(#[case] path: &str, #[case] prefix: &str) {}

    #[template]
    #[rstest]
    #[case::both_empty("", "", "")]
    #[case::both_single_segment("hello", "hello", "")]
    #[case::trivial_empty_suffix("some/path", "", "some/path")]
    #[case::same_path("some/path", "some/path", "")]
    #[case::strict_suffix("some/path", "path", "some/")]
    #[case::strict_suffix_with_root("/some/path", "path", "/some/")]
    #[case::strict_suffix_with_parent("../path/..", "..", "../path/")]
    fn true_suffixes_with_unmatched_path(
        #[case] path: &str,
        #[case] suffix: &str,
        #[case] unmatched_path: &str) {}

    #[template]
    #[rstest]
    #[case::empty_path("", "segment")]
    #[case::incomplete_single_segment("segment", "ment")]
    #[case::different_single_segment("segment1", "segment2")]
    #[case::different_first_segment("some/path", "one/path")]
    #[case::incomplete_first_segment("some/path", "me/path")]
    #[case::different_last_segment_with_root("/some/path/plus", "/path/minus")]
    #[case::longer_suffix("some/path", "some/path/but/longer")]
    #[case::more_parents("../path", "../../path")]
    #[case::differently_rooted_suffix("/some/path", "/path")]
    #[case::rooted_suffix_on_unrooted_path("some/path", "/path")]
    fn false_suffixes(#[case] path: &str, #[case] suffix: &str) {}

    #[apply(existing_entities)]
    fn exists_passes_for_existing_symlink_to_directory(
        #[case] entity: impl AsRef<Path> + RefUnwindSafe
    ) {
        assert_that!(entity).exists();
    }

    #[test]
    fn exists_fails_for_non_existing_file() {
        assert_fails_non_existing(|it| it.exists(), "to exist");
    }

    #[test]
    fn does_not_exist_passes_for_non_existing_file() {
        assert_that!("/some/path/that/hopefully/does/not/exist").does_not_exist();
    }

    #[apply(existing_entities)]
    fn does_not_exist_fails_for_existing_file(#[case] entity: impl AsRef<Path> + RefUnwindSafe) {
        assert_fails_and_was_path(|| assert_that!(&entity).does_not_exist(),
            "&entity", "not to exist", &entity, "which does exist");
    }

    #[test]
    fn is_absolute_passes_for_absolute_path() {
        let path = path::absolute("relative/path").unwrap();

        assert_that!(path).is_absolute();
    }

    #[test]
    fn is_absolute_fails_for_relative_path() {
        assert_fails!(("relative/path").is_absolute(),
            expected it "to be absolute"
            but it "was <relative/path>, which is relative");
    }

    #[test]
    fn is_relative_passes_for_relative_path() {
        assert_that!("relative/path").is_relative();
    }

    #[test]
    fn is_relative_fails_for_absolute_path() {
        let path = path::absolute("relative/path").unwrap();

        assert_fails_and_was_path(|| assert_that!(&path).is_relative(),
            "&path", "to be relative", &path, "which is absolute");
    }

    #[apply(file_and_symlink_file)]
    fn is_file_passes_for_file(entity: impl AsRef<Path> + RefUnwindSafe) {
        assert_that!(entity).is_file();
    }

    #[apply(dir_and_symlink_dir)]
    fn is_file_fails_for_dir(entity: impl AsRef<Path> + RefUnwindSafe) {
        assert_fails_and_was_path(|| assert_that!(&entity).is_file(),
            "&entity", "to point to a regular file", &entity, "which points to a directory");
    }

    #[test]
    fn is_file_fails_for_non_existing_path() {
        assert_fails_non_existing(|it| it.is_file(), "to point to a regular file");
    }


    #[test]
    fn is_non_symlink_file_passes_for_file() {
        let file = NamedTempFile::new().unwrap();

        assert_that!(file).is_non_symlink_file();
    }

    #[test]
    fn is_non_symlink_file_fails_for_dir() {
        let dir = TempDir::new().unwrap();

        assert_fails_and_was_path(|| assert_that!(&dir).is_non_symlink_file(),
            "&dir",
            "to point to a regular file without symbolic link",
            &dir,
            "which points to a directory");
    }

    #[apply(symlink)]
    fn is_non_symlink_file_fails_for_symlink(entity: impl AsRef<Path> + RefUnwindSafe) {
        assert_fails_and_was_path(|| assert_that!(&entity).is_non_symlink_file(),
            "&entity",
            "to point to a regular file without symbolic link",
            &entity,
            "which points to a symbolic link");
    }

    #[test]
    fn is_non_symlink_file_fails_for_non_existing_path() {
        assert_fails_non_existing(
            |it| it.is_non_symlink_file(),
            "to point to a regular file without symbolic link");
    }

    #[apply(dir_and_symlink_dir)]
    fn is_dir_passes_for_dir(entity: impl AsRef<Path> + RefUnwindSafe) {
        assert_that!(entity).is_dir();
    }

    #[apply(file_and_symlink_file)]
    fn is_dir_fails_for_file(entity: impl AsRef<Path> + RefUnwindSafe) {
        assert_fails_and_was_path(|| assert_that!(&entity).is_dir(),
            "&entity", "to point to a directory", &entity, "which points to a regular file");
    }

    #[test]
    fn is_dir_fails_for_non_existing_path() {
        assert_fails_non_existing(|it| it.is_dir(), "to point to a directory");
    }

    #[test]
    fn is_non_symlink_dir_passes_for_dir() {
        let dir = TempDir::new().unwrap();

        assert_that!(dir).is_non_symlink_dir();
    }

    #[test]
    fn is_non_symlink_dir_fails_for_file() {
        let file = NamedTempFile::new().unwrap();

        assert_fails_and_was_path(|| assert_that!(&file).is_non_symlink_dir(),
            "&file",
            "to point to a directory without symbolic link",
            &file,
            "which points to a regular file")
    }

    #[apply(symlink)]
    fn is_non_symlink_dir_fails_for_symlink(entity: impl AsRef<Path> + RefUnwindSafe) {
        assert_fails_and_was_path(|| assert_that!(&entity).is_non_symlink_dir(),
            "&entity",
            "to point to a directory without symbolic link",
            &entity,
            "which points to a symbolic link");
    }

    #[test]
    fn is_non_symlink_dir_fails_for_non_existing_path() {
        assert_fails_non_existing(
            |it| it.is_non_symlink_dir(),
            "to point to a directory without symbolic link");
    }

    #[rstest]
    #[case::symlink_to_file(TempSymlink::new_file().unwrap())]
    #[case::symlink_to_dir(TempSymlink::new_dir().unwrap())]
    fn is_symlink_passes_for_symlink(#[case] symlink: impl AsRef<Path> + RefUnwindSafe) {
        assert_that!(symlink).is_symlink();
    }

    #[test]
    fn is_symlink_fails_for_non_symlink_file() {
        let file = NamedTempFile::new().unwrap();

        assert_fails_and_was_path(|| assert_that!(&file).is_symlink(),
            "&file", "to point to a symbolic link", &file, "which points to a regular file");
    }

    #[test]
    fn is_symlink_fails_for_non_symlink_dir() {
        let dir = TempDir::new().unwrap();

        assert_fails_and_was_path(|| assert_that!(&dir).is_symlink(),
            "&dir", "to point to a symbolic link", &dir, "which points to a directory");
    }

    #[test]
    fn is_symlink_fails_for_non_existing_path() {
        assert_fails_non_existing(|it| it.is_symlink(), "to point to a symbolic link");
    }

    #[rstest]
    #[case::file(NamedTempFile::new().unwrap())]
    #[case::dir(TempDir::new().unwrap())]
    fn is_non_symlink_passes_for_file_or_dir(#[case] entity: impl AsRef<Path> + RefUnwindSafe) {
        assert_that!(entity).is_non_symlink();
    }

    #[apply(symlink)]
    fn is_non_symlink_fails_for_symlink(#[case] entity: impl AsRef<Path> + RefUnwindSafe) {
        assert_fails_and_was_path(|| assert_that!(&entity).is_non_symlink(),
            "&entity",
            "not to point to a symbolic link",
            &entity,
            "which points to a symbolic link");
    }

    #[test]
    fn is_non_symlink_fails_for_non_existing_path() {
        assert_fails_non_existing(|it| it.is_non_symlink(), "not to point to a symbolic link");
    }

    #[rstest]
    #[case::only_segment("file_name.ext", "file_name.ext")]
    #[case::only_segment_after_root("/file_name", "file_name")]
    #[case::last_segment("some/longer/path", "path")]
    fn has_file_name_passes(#[case] path: &str, #[case] expected_file_name: &str) {
        assert_that!(path).has_file_name(expected_file_name);
    }

    #[apply(paths_with_empty_file_name)]
    fn has_file_name_fails_for_empty_file_name(#[case] path: &str) {
        assert_fails!((path).has_file_name("anything"),
            expected it "to have file name <anything>"
            but it (format!("was <{}>, which has no file name", path)));
    }

    #[test]
    fn has_file_name_fails_for_different_file_stem() {
        assert_fails!(("some/path.exe").has_file_name("bath.exe"),
            expected it "to have file name <bath.exe>"
            but it "was <some/path.exe>, which has file name <path.exe>");
    }

    #[test]
    fn has_file_name_fails_for_different_extension() {
        assert_fails!(("some/path.pdf").has_file_name("path.docx"),
            expected it "to have file name <path.docx>"
            but it "was <some/path.pdf>, which has file name <path.pdf>");
    }

    #[apply(paths_with_empty_file_name)]
    fn does_not_have_file_name_passes_for_empty_file_name(#[case] path: &str) {
        assert_that!(path).does_not_have_file_name("anything");
    }

    #[test]
    fn does_not_have_file_name_passes_for_different_file_stem() {
        assert_that!("some/path.exe").does_not_have_file_name("bath.exe");
    }

    #[test]
    fn does_not_have_file_name_passes_for_different_extension() {
        assert_that!("some/path.pdf").does_not_have_file_name("path.docx");
    }

    #[rstest]
    #[case::only_segment("file_name.ext", "file_name.ext")]
    #[case::only_segment_after_root("/file_name", "file_name")]
    #[case::last_segment("some/longer/path", "path")]
    fn does_not_have_file_name_fails(#[case] path: &str, #[case] expected_file_name: &str) {
        assert_fails!((path).does_not_have_file_name(expected_file_name),
            expected it (format!("not to have file name <{}>", expected_file_name))
            but it (format!("was <{}>, which does", path)));
    }

    #[rstest]
    #[case::only_segment_without_extension("file_name", "file_name")]
    #[case::only_segment_with_extension("file_name.ext", "file_name")]
    #[case::only_segment_after_root_without_extension("/file_name", "file_name")]
    #[case::only_segment_after_root_with_extension("/file_name.json", "file_name")]
    #[case::last_segment_without_extension("some/longer/path", "path")]
    #[case::last_segment_with_extension("some/longer/path.pdf", "path")]
    fn has_file_stem_passes(#[case] path: &str, #[case] expected_file_stem: &str) {
        assert_that!(path).has_file_stem(expected_file_stem);
    }

    #[apply(paths_with_empty_file_name)]
    fn has_file_stem_fails_for_empty_file_name(#[case] path: &str) {
        assert_fails!((path).has_file_stem("anything"),
            expected it "to have file stem <anything>"
            but it (format!("was <{}>, which has no file stem", path)));
    }

    #[test]
    fn has_file_stem_fails_for_different_file_stem() {
        assert_fails!(("some/path.exe").has_file_stem("bath"),
            expected it "to have file stem <bath>"
            but it "was <some/path.exe>, which has file stem <path>");
    }

    #[rstest]
    #[case::only_segment_without_extension("file_name", "file_name")]
    #[case::only_segment_with_extension("file_name.ext", "file_name")]
    #[case::only_segment_after_root_without_extension("/file_name", "file_name")]
    #[case::only_segment_after_root_with_extension("/file_name.json", "file_name")]
    #[case::last_segment_without_extension("some/longer/path", "path")]
    #[case::last_segment_with_extension("some/longer/path.pdf", "path")]
    fn does_not_have_file_stem_fails(#[case] path: &str, #[case] expected_file_stem: &str) {
        assert_fails!((path).does_not_have_file_stem(expected_file_stem),
            expected it (format!("not to have file stem <{}>", expected_file_stem))
            but it (format!("was <{}>, which does", path)));
    }

    #[apply(paths_with_empty_file_name)]
    fn does_not_have_file_stem_passes_for_empty_file_name(#[case] path: &str) {
        assert_that!(path).does_not_have_file_stem("anything");
    }

    #[test]
    fn does_not_have_file_stem_fails_for_different_file_stem() {
        assert_that!("some/path.exe").does_not_have_file_stem("bath");
    }

    #[rstest]
    #[case::only_segment("file_name.ext", "ext")]
    #[case::only_segment_after_root("/file_name.json", "json")]
    #[case::last_segment("some/longer/path.hello.pdf", "pdf")]
    fn has_extension_passes(#[case] path: &str, #[case] expected_extension: &str) {
        assert_that!(path).has_extension(expected_extension);
    }

    #[apply(paths_with_empty_file_name)]
    #[case::only_segment_without_extension("file_name")]
    #[case::only_segment_after_root_without_extension("/file_name")]
    #[case::last_segment_without_extension("some/longer/path")]
    #[case::without_extension_but_with_period(".path")]
    fn has_extension_fails_for_file_without_extension(#[case] path: &str) {
        assert_fails!((path).has_extension("any"),
            expected it "to have extension <any>"
            but it (format!("was <{}>, which has no extension", path)));
    }

    #[test]
    fn has_extension_fails_for_different_extension() {
        assert_fails!(("some/path.exe").has_extension("pdf"),
            expected it "to have extension <pdf>"
            but it "was <some/path.exe>, which has extension <exe>");
    }

    #[test]
    fn does_not_have_extension_passes_for_different_extension() {
        assert_that!("some/path.exe").does_not_have_extension("pdf");
    }

    #[apply(paths_with_empty_file_name)]
    #[case::only_segment_without_extension("file_name")]
    #[case::only_segment_after_root_without_extension("/file_name")]
    #[case::last_segment_without_extension("some/longer/path")]
    #[case::without_extension_but_with_period(".path")]
    fn does_not_have_extension_passes_for_file_without_extension(#[case] path: &str) {
        assert_that!(path).does_not_have_extension("any");
    }

    #[rstest]
    #[case::only_segment("file_name.ext", "ext")]
    #[case::only_segment_after_root("/file_name.json", "json")]
    #[case::last_segment("some/longer/path.hello.pdf", "pdf")]
    fn does_not_have_extension_fails(#[case] path: &str, #[case] expected_extension: &str) {
        assert_fails!((path).does_not_have_extension(expected_extension),
            expected it (format!("not to have extension <{}>", expected_extension))
            but it (format!("was <{}>, which does", path)));
    }

    #[apply(true_prefixes_with_unmatched_path)]
    fn starts_with_path_passes(#[case] path: &str, #[case] prefix: &str, #[case] _unmatched_path: &str) {
        assert_that!(path).starts_with_path(prefix);
    }

    #[apply(false_prefixes)]
    fn starts_with_path_fails(#[case] path: &str, #[case] prefix: &str) {
        assert_fails!((path).starts_with_path(prefix),
            expected it (format!("to start with <{}>", prefix))
            but it (format!("was <{}>", path)));
    }

    #[apply(false_prefixes)]
    fn does_not_start_with_path_passes(#[case] path: &str, #[case] prefix: &str) {
        assert_that!(path).does_not_start_with_path(prefix);
    }

    #[apply(true_prefixes_with_unmatched_path)]
    fn does_not_start_with_path_fails(
        #[case] path: &str,
        #[case] prefix: &str,
        #[case] unmatched_path: &str
    ) {
        assert_fails!((path).does_not_start_with_path(prefix),
            expected it (format!("not to start with <{}>", prefix))
            but it (format!("was <[{}]{}>", prefix, unmatched_path)));
    }

    #[apply(true_suffixes_with_unmatched_path)]
    fn ends_with_path_passes(#[case] path: &str, #[case] suffix: &str, #[case] _unmatched_path: &str) {
        assert_that!(path).ends_with_path(suffix);
    }

    #[apply(false_suffixes)]
    fn ends_with_path_fails(#[case] path: &str, #[case] suffix: &str) {
        assert_fails!((path).ends_with_path(suffix),
            expected it (format!("to end with <{}>", suffix))
            but it (format!("was <{}>", path)));
    }

    #[apply(false_suffixes)]
    fn does_not_end_with_path_passes(#[case] path: &str, #[case] suffix: &str) {
        assert_that!(path).does_not_end_with_path(suffix);
    }

    #[apply(true_suffixes_with_unmatched_path)]
    fn does_not_end_with_path_fails(
        #[case] path: &str,
        #[case] suffix: &str,
        #[case] unmatched_path: &str
    ) {
        assert_fails!((path).does_not_end_with_path(suffix),
            expected it (format!("not to end with <{}>", suffix))
            but it (format!("was <{}[{}]>", unmatched_path, suffix)));
    }

    #[rstest]
    #[case::empty(&[])]
    #[case::non_empty(b"some content\nsome more content")]
    fn is_file_with_content_passes(#[case] content: &[u8]) {
        let mut file = NamedTempFile::new().unwrap();
        file.write_all(content).unwrap();

        assert_that!(file).is_file_with_content(content);
    }

    #[rstest]
    #[case::empty_file_non_empty_expected("", "expected")]
    #[case::non_empty_file_empty_expected("expected", "")]
    #[case::different_non_empty("file\ncontent", "expected\ncontent")]
    fn is_file_with_content_fails_for_different_utf8_content(
        #[case] file_content: &str,
        #[case] expected_content: &str
    ) {
        let mut file = NamedTempFile::new().unwrap();
        file.write_all(file_content.as_bytes()).unwrap();

        assert_fails_and_was_path(|| assert_that!(&file).is_file_with_content(expected_content),
            "&file",
            &format!("to point to a file with content <{}>", expected_content.escape_debug()),
            &file,
            &format!("which has content <{}>", file_content.escape_debug()));
    }

    #[test]
    fn is_file_with_content_fails_for_different_non_utf8_content() {
        let mut file = NamedTempFile::new().unwrap();
        file.write_all(&[ 255, 254 ]).unwrap();

        assert_fails_and_was_path(|| assert_that!(&file).is_file_with_content(&[ 255, 253 ]),
            "&file",
            "to point to a file with content <[255, 253]>",
            &file,
            "which has content <[255, 254]>");
    }

    #[apply(dir_and_symlink_dir)]
    fn is_file_with_content_fails_for_directory(#[case] dir: impl AsRef<Path> + RefUnwindSafe) {
        assert_fails_and_was_path(|| assert_that!(&dir).is_file_with_content("anything"),
            "&dir", "to point to a file with given content", &dir, "which cannot be opened");
    }

    #[test]
    fn is_file_with_content_fails_for_non_existing_path() {
        assert_fails_non_existing(
            |it| it.is_file_with_content("anything"),
            "to point to a file with given content");
    }

    #[apply(file_and_symlink_file)]
    fn is_empty_file_passes(#[case] file: impl AsRef<Path> + RefUnwindSafe) {
        assert_that!(file).is_empty_file();
    }

    #[test]
    fn is_empty_file_fails_for_file_with_utf8_content() {
        let mut file = NamedTempFile::new().unwrap();
        file.write_all(b"not empty\n").unwrap();

        assert_fails_and_was_path(|| assert_that!(&file).is_empty_file(),
            "&file", "to point to an empty file", &file, "which has content <not empty\\n>");
    }

    #[test]
    fn is_empty_file_fails_for_file_with_non_utf8_content() {
        let mut file = NamedTempFile::new().unwrap();
        file.write_all(&[ 255, 254 ]).unwrap();

        assert_fails_and_was_path(|| assert_that!(&file).is_empty_file(),
            "&file", "to point to an empty file", &file, "which has content <[255, 254]>");
    }

    #[apply(dir_and_symlink_dir)]
    fn is_empty_file_fails_for_directory(#[case] dir: impl AsRef<Path> + RefUnwindSafe) {
        assert_fails_and_was_path(|| assert_that!(&dir).is_empty_file(),
            "&dir", "to point to an empty file", &dir, "which cannot be opened");
    }

    #[test]
    fn is_empty_file_fails_for_non_existing_path() {
        assert_fails_non_existing(|it| it.is_empty_file(), "to point to an empty file");
    }

    #[test]
    fn is_non_empty_file_passes_for_file_with_content() {
        let mut file = NamedTempFile::new().unwrap();
        file.write_all(b"not empty\n").unwrap();

        assert_that!(&file).is_non_empty_file();
    }

    #[apply(file_and_symlink_file)]
    fn is_non_empty_file_fails_for_empty_file(#[case] file: impl AsRef<Path> + RefUnwindSafe) {
        assert_fails_and_was_path(|| assert_that!(&file).is_non_empty_file(),
            "&file", "to point to a non-empty file", &file, "which points to an empty file");
    }

    #[apply(dir_and_symlink_dir)]
    fn is_non_empty_file_fails_for_directory(#[case] dir: impl AsRef<Path> + RefUnwindSafe) {
        assert_fails_and_was_path(|| assert_that!(&dir).is_non_empty_file(),
            "&dir", "to point to a non-empty file", &dir, "which cannot be opened");
    }

    #[test]
    fn is_non_empty_file_fails_for_non_existing_path() {
        assert_fails_non_existing(|it| it.is_non_empty_file(), "to point to a non-empty file");
    }

    #[apply(dir_and_symlink_dir)]
    fn is_empty_dir_passes_for_empty_directory(#[case] dir: impl AsRef<Path> + RefUnwindSafe) {
        assert_that!(dir).is_empty_dir();
    }

    #[test]
    fn is_empty_dir_fails_for_directory_with_file() {
        let dir = TempDir::new().unwrap();
        File::create(dir.path().join("file")).unwrap();

        assert_fails_and_was_path(|| assert_that!(&dir).is_empty_dir(),
            "&dir", "to point to an empty directory", &dir, "which is not empty");
    }

    #[test]
    fn is_empty_dir_fails_for_directory_with_subdirectory() {
        let dir = TempDir::new().unwrap();
        fs::create_dir(dir.path().join("subdir")).unwrap();

        assert_fails_and_was_path(|| assert_that!(&dir).is_empty_dir(),
            "&dir", "to point to an empty directory", &dir, "which is not empty");
    }

    #[apply(file_and_symlink_file)]
    fn is_empty_dir_fails_for_file(#[case] file: impl AsRef<Path> + RefUnwindSafe) {
        assert_fails_and_was_path(|| assert_that!(&file).is_empty_dir(),
            "&file", "to point to an empty directory", &file, "which is not a directory")
    }

    #[test]
    fn is_empty_dir_fails_for_non_existing_path() {
        assert_fails_non_existing(|it| it.is_empty_dir(), "to point to an empty directory");
    }

    #[apply(dir_and_symlink_dir)]
    fn is_non_empty_dir_fails_for_empty_directory(#[case] dir: impl AsRef<Path> + RefUnwindSafe) {
        assert_fails_and_was_path(|| assert_that!(&dir).is_non_empty_dir(),
            "&dir", "to point to a non-empty directory", &dir, "which is empty")
    }

    #[test]
    fn is_non_empty_dir_passes_for_directory_with_file() {
        let dir = TempDir::new().unwrap();
        File::create(dir.path().join("file")).unwrap();

        assert_that!(&dir).is_non_empty_dir();
    }

    #[test]
    fn is_non_empty_dir_passes_for_directory_with_subdirectory() {
        let dir = TempDir::new().unwrap();
        fs::create_dir(dir.path().join("subdir")).unwrap();

        assert_that!(&dir).is_non_empty_dir();
    }

    #[apply(file_and_symlink_file)]
    fn is_non_empty_dir_fails_for_file(#[case] file: impl AsRef<Path> + RefUnwindSafe) {
        assert_fails_and_was_path(|| assert_that!(&file).is_non_empty_dir(),
            "&file", "to point to a non-empty directory", &file, "which is not a directory")
    }

    #[test]
    fn is_non_empty_dir_fails_for_non_existing_path() {
        assert_fails_non_existing(|it| it.is_non_empty_dir(), "to point to a non-empty directory");
    }

    #[rstest]
    #[case::empty("")]
    #[case::self_dir(".")]
    #[case::parent_dir("..")]
    #[case::single_segment("segment")]
    #[case::path_without_root("some/path")]
    #[case::path_with_root("/some/path")]
    #[case::path_with_parent("../some/path")]
    fn to_string_works(#[case] path: &str) {
        let result = assert_that!(Path::new(path)).to_string();

        assert_eq!(path, &result.data);
        assert_eq!("<Path::new(path)> as string", &result.expression);
    }

    #[rstest]
    #[case::empty(&[])]
    #[case::utf8(b"some data")]
    #[case::non_utf8(&[ 255, 254, 253 ])]
    fn to_content_works_for_file(#[case] content: &[u8]) {
        let mut file = NamedTempFile::new().unwrap();
        file.write_all(content).unwrap();

        let result = assert_that!(&file).to_content();

        assert_eq!(content, &result.data);
        assert_eq!("content of <&file>", &result.expression);
    }

    #[apply(dir_and_symlink_dir)]
    fn to_content_fails_for_directory(#[case] dir: impl AsRef<Path> + RefUnwindSafe) {
        assert_fails_and_was_path(|| assert_that!(&dir).to_content(),
            "&dir", "to be readable", &dir, "which cannot be opened")
    }

    #[test]
    fn to_content_fails_for_non_existing_path() {
        assert_fails_non_existing(|it| it.to_content(), "to be readable");
    }

    #[rstest]
    #[case::empty("")]
    #[case::utf8("some data")]
    fn to_content_string_works_for_utf8_file(#[case] content: &str) {
        let mut file = NamedTempFile::new().unwrap();
        file.write_all(content.as_bytes()).unwrap();

        let result = assert_that!(&file).to_content_string();

        assert_eq!(content, &result.data);
        assert_eq!("content of <&file> as string", &result.expression);
    }

    #[test]
    fn to_content_string_does_not_work_for_non_utf8_file() {
        let mut file = NamedTempFile::new().unwrap();
        file.write_all(&[ 255, 254, 253 ]).unwrap();

        assert_fails_and_was_path(|| assert_that!(&file).to_content_string(),
            "&file", "to contain valid UTF-8", &file, "which contains non-UTF-8 data");
    }

    #[apply(dir_and_symlink_dir)]
    fn to_content_string_fails_for_directory(#[case] dir: impl AsRef<Path> + RefUnwindSafe) {
        assert_fails_and_was_path(|| assert_that!(&dir).to_content_string(),
            "&dir", "to be readable", &dir, "which cannot be opened")
    }

    #[test]
    fn to_content_string_fails_for_non_existing_path() {
        assert_fails_non_existing(|it| it.to_content_string(), "to be readable");
    }

    #[rstest]
    #[case::exists(AssertThat::exists)]
    #[case::is_file(AssertThat::is_file)]
    #[case::is_non_symlink_file(AssertThat::is_non_symlink_file)]
    #[case::is_dir(AssertThat::is_dir)]
    #[case::is_non_symlink_dir(AssertThat::is_non_symlink_dir)]
    #[case::is_non_symlink(AssertThat::is_non_symlink)]
    #[case::is_file_with_content(|it: AssertThat<TempSymlink<PathBuf>>| it.is_file_with_content("anything"))]
    #[case::is_empty_file(AssertThat::is_empty_file)]
    #[case::is_non_empty_file(AssertThat::is_non_empty_file)]
    #[case::is_empty_dir(AssertThat::is_empty_dir)]
    #[case::is_non_empty_dir(AssertThat::is_non_empty_dir)]
    #[case::to_content(AssertThat::to_content)]
    #[case::to_content_string(AssertThat::to_content_string)]
    fn accessing_assertions_fail_for_broken_symlink<AssertT, ResultT>(#[case] assertion: AssertT)
    where
        AssertT: FnOnce(AssertThat<TempSymlink<PathBuf>>) -> ResultT
        + UnwindSafe
    {
        // Unfortunately, handling of broken symlinks seems to be platform-dependent, so we just
        // assert that they fail.

        assert_that!(|| assertion(assert_that!(TempSymlink::new_broken().unwrap()))).panics();
    }

}
