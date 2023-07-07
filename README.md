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
  for iterating over the values in an array for the left or the right.

* `Data.Array.Core`: This module holds the core data types and functions
  for working with mutable and immutable arrays. Mutable arrays can be used
  in pure code as long as they are kept in a linear context, which
  prevents them from being freely shared.

* `Data.Array.Mutable`: Utilities for working with mutable linear arrays.
  Currently, this mainly contains different functions for filling a mutable
  array with values from different sources, but also for setting and reading
  values using different types of indices.
