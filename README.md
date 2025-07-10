# Non-empty collections

**Warning: this is a preview version that is not tested yet!** It mainly intends to showcase
the desired API. If you want to contribute tests please feel free to do so on GitHub!

It's quite common for algorithms to require that a certain collection is not empty.
For example, computing average of numbers requires that there is at least one number.
Rather than checking the inputs in function that computes it one might want to pass this
responsibility to the caller and push validation to the edge of the application.
This makes error reporting simpler or, in case the number of elements is statically known,
avoids errors completely.

This crate provides the [`NonEmpty`] type which proves that the collection it stores is not
empty (assuming the collection is implemented correctly).
It also provides various methods and trait impls that take advantage of the invariant.
For instance it has the [`first`](NonEmpty::first) method that replaces those on `std`'s
collections such that it returns the element without being wrapped in `Option`.

In addition, the crate provides some specialized types which use
[`NonZeroUsize`] internally to explain the invariant to the compiler. These can be used in data
structures to reduce the size of enums. As an example, one can re-implement `Cow` from the
[`beef`](https://docs.rs/beef) crate using only safe code thanks to this invariant.

The API strives to be similar to that of `std` types, however there are some differences
between them that this crate erases to a degree.

# Examples

Compute average

```rust
use non_empty::NonEmpty;

pub fn compute_average(numbers: &NonEmpty<[usize]>) -> usize {
    // This can still overflow but the type at least catches obvious mistake
    numbers.iter().sum::<usize>() / numbers.len()
}

assert_eq!(compute_average([42, 24].as_ref()), 33);
```

However, this would fail to compile:

```rust
assert_eq!(compute_average([].as_ref()), 42);
```

Of course, the number of items is not always known. But that's also easy to deal with:

```rust
let user_input = get_user_input()?;
let user_input = NonEmpty::new(user_input).ok_or(Error::EmptyInput)?;
let average = compute_average(&user_input);
println!("{}", average);
```

Note that you don't always have to do manual validation like this. For instance, if you're
using [`serde`], you can just wrap your type in [`NonEmpty`] and it'll validate the length for
you! Similarly, you can use `string.parse()` if the collection implements
[`FromStr`](core::str::FromStr) or use [`configure_me`](https://docs.rs/confiure_me) out of the
box if the collection implements `ParseArg` (this works well for strings).

# Features

* `std` - enables support for [`std`] types. On by default, implies `alloc`.
* `alloc` - enables support for [`alloc`] types. On by defult, implied by `std`.
* `parse_arg` - implements the [`parse_arg::ParseArg`] trait.
* `serde` - implements [`serde::Serialize`] and [`serde::Deserialize`].
* `newer-rust` - enables rust version detection and thus features requiring higher MSRV. This
  may or may not add a dependency (currently it does) and may become deprecated once version
  checking is supported by Rust itself.

# Why this crate contains (so much) `unsafe`?

If you look at the code there appear to be many lines of `unsafe`. However, almost all boil down
to "this collection is not empty" which is a trivial condition/assumption. We're trusting
[`std`] to implement its types properly (no logic bugs in collections) and this is indicated by
the `WellBehavedCollection` trait. However, non-`std` types are not trusted and the optimization
is not applied.

It could be argued that the crate could've went with just panics instead. Perhaps. But it feels
like it'd really suck not getting use of this invariant. It'd be possible to add later but it
might lead the API design to not account for it which would make it difficult to add later.
Note though that the `unsafe` optimizations are currently turned off by default since there
wasn't much testing. They can be turned on with *unstable* `non_empty_no_paranoid_checks` cfg
flag for the time being. This will become the default (or maybe the only) option once the crate
is tested more.

# Comparison with other crates

There are other crates around that provide a similar functionality. The main advantages of this
one are:

* Generic type supports arbitrary collections including the entire `std`
* Rich safe API
* Explicitly conservative MSRV
* Focus on getting stable and production-ready ~soon
* Both thin wrapper and customized types with different trade-offs
* Non-empty iterator API with combinators supports infallibly transforming the collections
* Not abandoned (yet :D)

# MSRV

The miminal supported Rust version is 1.63. The intention is to support the latest Debian stable
and, if feasible, support compilers up to two years old. The crate still supports newer rust
features using the `newer-rust` Cargo feature flag.

Note that dependencies may have a more lax MSRV. This is not a bug.

# License

MITNFA
