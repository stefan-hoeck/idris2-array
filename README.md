# idris2-array: Immutable and mutable (linear) size-indexed arrays

This library provides utilities for working with immutable and mutable
arrays. They are indexed by their size, which allows us to safely access
the values they hold if we can proof that an index is strictly smaller
than an array's size.

Mutable arrays make use of linear types to make sure they are not
being freely shared in an application.

Here is a quick overview of the modules provided (look there for more
details and documentation):

* `Data.Array.Index`: Different data types, conversions, and proofs for
  safely accessing the values in an indexed array. The default type to
  use for indexing is `Fin n`, but other types might be better suited
  for iterating over the values in an array from the left or right.

* `Data.Array.Core`: This module holds the core data types and functions
  for working with mutable and immutable arrays. Mutable arrays can be used
  in pure code as long as they are kept in a linear context, which
  prevents them from being freely shared.

* `Data.Array.Mutable`: Utilities for working with mutable linear arrays.
  Currently, this mainly contains different functions for filling a mutable
  array with values from different sources, but also for setting and reading
  values using different types of indices.

* `Data.Array.Indexed`: Functions for creating, inspecting, and modifying
  size-indexed immutable arrays.

In addition, there is a [tutorial](docs/src/Linear/Tutorial.md), describing
in detail some aspects of linear types in Idris and how `Data.Array.Core`
was implemented.

## Additional Resources

There are not many resources available about linear types in Idris, but there
are several blog posts, articles, and libraries explaining and using these
concepts in Haskell. Here is a non-comprehensive selection:

* [Idris2 introduction to linear types](https://idris2.readthedocs.io/en/latest/tutorial/multiplicities.html#linearity):
  This gives a nice introduction to using linear types for safe resource
  management in Idris2, a topic which is not being discussed in the
  tutorial of this library.
* [linear-base](https://github.com/tweag/linear-base): Some parts of the
  tutorial were inspired by the examples in this library. A treasure trove
  of utilities that has been very well documented.
* [TWEAK blog posts on linear types](https://www.tweag.io/blog/tags/linear-types):
  Lots of interesting stuff on using linear types in high-performance algorithms
  and for writing safe resource protocols.
