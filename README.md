# Kernal

Kernal (Kernal Extensive Rust Natural Assertion Language) allows you to use fluent assertions in
Rust tests. That is, instead of writing `assert_eq!(my_vec.len(), 10)`, you can write
`assert_that!(my_vec).has_length(10)`, making your tests more readable and enabling the framework to
provide more expressive error messages. Kernal aims to provide specialized assertions for as many
commonly tested properties as possible.

## Writing an assertion

To write an assertion over a value, start with `assert_that!(<your value>)`, which gives you an
instance on which you can call associated functions to make your assertions. Import the specialized
extension traits, such as `StringAssertions` for special assertions for `String`s, from the
`prelude` module. This gives you all imports you need to write every assertion supported by Kernal.

```rust
use kernal::prelude::*;

assert_that!("hello world").contains("world");
```

## Chaining

Every assertion returns the same asserter instance to continue writing assertions on the same value.
In addition, some extension traits define mapping methods that manipulate the data in some way and
return asserter instances on the new data.

```rust
assert_that!("almost")
    .has_char_length(6)
    .ends_with("most")
    .to_chars()
    .is_sorted_in_strictly_ascending_order();
```

## Creating custom assertions

Kernal allows the creation of custom assertions to test instances of your types in a more natural
way. This is achieved by grouping assertions you want to offer for specific types into traits, which
are then implemented on the output type of the `assert_that` macro. For more details, view the
crate-level [documentation][Doc]. The example below demonstrates this process.

```rust
// Our type for which we want to write assertions.
struct Vector2f32 { x: f32, y: f32 }

// The custom assertion trait we will later implement on `AssertThat`.
trait Vector2f32Assertions {
    // The custom assertion we want to supply. It is recommended to take an owned `self` and
    // return the same instance to support chaining.
    fn has_euclidean_norm(self, expected_norm: f32, epsilon: f32) -> AssertThat<Vector2f32>;
}

impl Vector2f32Assertions for AssertThat<Vector2f32> {
    fn has_euclidean_norm(self, expected_norm: f32, epsilon: f32) -> AssertThat<Vector2f32> {
        // We get our data with `self.data()`, supplied by `AssertThatData`
        let vector = self.data();
        let actual_norm = (vector.x * vector.x + vector.y * vector.y).sqrt();

        if (actual_norm - expected_norm).abs() > epsilon {
            // Here we must fail - using the `Failure` struct
            Failure::new(&self)
                .expected_it(format!("to have a euclidean norm within <{}> of <{}>",
                    epsilon, expected_norm))
                .but_it(format!("was <({}, {})>, with a euclidean norm of <{}>",
                    vector.x, vector.y, actual_norm))
                .fail()
        }

        // Here the test passes, so we return `self` for chaining
        self
    }
}
```

## Crate features

* `json`: Enables assertions on types that can be parsed as JSONs as well as JSON values from
  the [serde_json](https://docs.rs/serde_json/latest/serde_json/) crate.

## Links

* [Crate](https://crates.io/crates/kernal)
* [Documentation][Doc]
* [Repository](https://github.com/florian1345/kernal)

[Doc]: https://docs.rs/kernal/latest/kernal/
