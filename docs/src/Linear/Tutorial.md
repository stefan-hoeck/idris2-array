# Implementing Mutable Linear Arrays

In this tutorial I am going to explain the basics of linear
types and how they can be used to implement a library of
mutable arrays that can be safely used in pure code.

```idris
module Linear.Tutorial

import Data.Array.Index
import Data.Fin

%default total
```

## An Introduction to Linear Types

A linear function argument (annotated with a `1` quantity) must be consumed
exactly once. We will explore two things in this introduction: What it means to
"consume an argument exactly once", and why we should care about this.

Below is an example of a linear function type:

```idris
boolToNat1 : (1 b : Bool) -> Nat
```

The `1` quantity in `boolToNat1`'s type signature means, that the `Bool`
argument `b` must be consumed exactly once if the resulting natural number
is consumed exactly once. We can *consume* an argument by

* pattern matching on it
* passing it as a quantity `1` argument to another function
* wrapping it in a data constructor as a quantity `1` argument or
  record field

Let's look at each of them before showing some counterexamples. First,
a pattern match:

```idris
boolToNat1 False = 0
boolToNat1 True  = 1
```

Second, passing it to another linear function:

```idris
boolToNat1' : (1 b : Bool) -> Nat
boolToNat1' b = boolToNat1 b
```

Third, wrapping it in a data constructor:

```idris
record LinBool where
  constructor LB
  1 bool : Bool

wrapBool : (1 b : Bool) -> LinBool
wrapBool b = LB b
```

Here are a couple of examples that don't work:

```idris
failing "Trying to use linear name b in non-linear context"
  twice : (1 b : Bool) -> (Bool,Bool)
  twice b = (b,b)
```

The above does not work for two reasons: The arguments of `MkPair` are
non-linear, and even if they were, we are not allowed to use a linear
argument twice:


```idris
failing "Trying to use linear name b in non-linear context"
  addTwice : (1 b : Bool) -> Nat
  addTwice b = boolToNat1 b + boolToNat1 b
```

We also must not pass the argument as a non-linear argument to
another function:

```idris
failing "Trying to use linear name b in non-linear context"
  not1 : (1 b : Bool) -> Bool
  not1 b = not b
```

However, at least in the example above, we can rewrite `not` in such a way,
that it accepts its with quantity `1`:

```idris
not1 : (1 b : Bool) -> Bool
not1 False = True
not1 True  = False
```

### Using Linear Functions

Linear functions can be used both in linear and non-linear contexts.
The linearity restrictions apply only if they are used in a linear
context. For instance, we can always convert a linear function
to a non-linear one:

```idris
unlinear: ((1 _ : a) -> b) -> a -> b
unlinear f v = f v
```

This is not possible the other way around: A non-linear function cannot be
converted to a linear one:

```idris
failing "Trying to use linear name v in non-linear context"
  tolin : (a -> b) -> (1 _ : a) -> b
  tolin f v = f v
```

Before we continue, we introduce a simple operator for describing linear
function types a bit more concisely:

```idris
export infixr 0 -@

(-@) : Type -> Type -> Type
a -@ b = (1 _ : a) -> b
```

While it is not possible to compose linear functions with the dot operator
from the Prelude, we can define a linear version of the dot operator. Due
to the ambiguity resolver available in Idris, the compiler will use the
correct version depending to the expected quantities:

```idris
(.) : (b -@ c) -@ (a -@ b) -@ a -@ c
(.) g f x = g (f x)
```

Here's a non-linear composition example of two `not` functions:

```idris
boolId : Bool -> Bool
boolId = not . not
```

And here's the linear pendant:

```idris
boolId1 : Bool -@ Bool
boolId1 = not1 . not1
```

### Wrapping and Unwrapping Linear Arguments

We already saw that a linear function argument can be wrapped in a data
constructor, if and only if the corresponding constructor argument
is also annotated with quantity `1`. This means, that a linear argument can never
leave the linear context. This allows for safe resource handling, as we will
see below: A linear argument must always be handled properly in its
linear context, and Idris will not allow us to forget to do that, nor
will it allow us to distribute the linear argument to several parts of
our program.

But eventually, we usually want to break out of linearity. For instance,
when we write an algorithm using a linear mutable array, we want to get
rid or the array and use the result of the algorithm freely in other parts of
our code. To do this - and to make sure our linear resource does *not*
escape from our algorithms - we need a data type of forced unrestrictedness,
abbreviated `Ur`:

```idris
record Ur a where
  constructor U
  unrestricted : a
```

This data type has a couple of important implications. First, even if
an `Ur a` appears in a linear context, the wrapped value can be
used unrestrictedly, because we need to consume the `Ur a` exactly once
(by pattern matching on it), but not the enclosed value because it
is not annotated with quantity `1`:

```idris
breakout : Ur a -@ (a,a)
breakout (U v) = (v,v)
```

Second, it is not possible to wrap a linear argument in a `Ur`, even
if the `Ur` itself is later on used in a linear context:

```idris
failing "Trying to use linear name b in non-linear context"
  unrestrictedBool : Bool -@ Ur Bool
  unrestrictedBool b = U b
```

However, it is perfectly fine to wrap an unrestricted constructor field
of a linear argument in a `Ur`:

```idris
eitherToUr : Either a a -@ Ur a
eitherToUr (Left x)  = U x
eitherToUr (Right x) = U x
```

In the example above, the `Either a a` argument is consumed exactly once
by pattern matching on it. The values it holds have unrestricted
quantity, so we are allowed to wrap them in a `Ur`.

Finally, we can always convert a linear function taking an `Ur` argument
to a non-linear and vice versa (the second conversion would not be
possible otherwise):

```idris
demote : (Ur a -@ b) -> a -> b
demote f v = f (U v)

promote : (a -> b) -> Ur a -@ b
promote f (U x) = f x
```

## An Implementation of Mutable Arrays

While all of the above is necessary to understand what's going on in
the code that follows, it might not yet be clear why all of this is
needed.. It is therefore time to start with actual implementation of
mutable and immutable arrays. First, the primitive stuff:

```idris
data ArrayData : Type -> Type where [external]

%extern prim__newArray : forall a . Bits32 -> a -> %World -> (ArrayData a)
%extern prim__arrayGet : forall a . ArrayData a -> Bits32 -> %World -> a
%extern prim__arraySet : forall a . ArrayData a -> Bits32 -> a -> PrimIO ()
```

Support for working with arrays is built into the compiler directly. To
be more precise: Into the main code generators like the Chez Scheme, Racket and
node backends. Therefore, functions `prim__newArray` and friends get
some special treatment by the compiler. If you'd like to learn more,
have a look at one of the code generators and how it implements
primitive functions calls. For instance, here is a link the the
corresponding code in the
[JavaScript codegenerator](https://github.com/idris-lang/Idris2/blob/main/src/Compiler/ES/Codegen.idr#L560-L562).

We need some black magic to invoke `prim__arraySet` outside of `IO`:

```idris
destroy : (1 _ : %World) -> a -> a
destroy %MkWorld x = x

set' : (m : Nat) -> a -> ArrayData a -> ArrayData a
set' m y z =
  let MkIORes () w2 := prim__arraySet z (cast m) y %MkWorld
   in destroy w2 z
```

Now, about `ArrayData a`: This is the type used to represent a mutable
array internally in our module. We can access its values by means of
`prim__arrayGet` and update (mutate) them by means of `set'`, which
will give the array data back to us. We must be careful not to return
`Unit` here, because Idris might decide to optimize the function call
away completely because it does not produce an interesting result
(`PrimIO` gets some special treatment in this regard, so we are safe
in this case).

The important thing about `ArrayData`: We do not want a value of this type
to ever leak into the outside world, as this would mean that we'd have
shared mutable state in a pure programming language (outside of `IO`).
This must not happen, so we encapsulate `ArrayData` objects in two
possible wrapper types: One for immutable arrays and one for mutable
arrays:

```idris
||| An immutable array of size `n` holding values of type `a`.
export
record IArray (n : Nat) (a : Type) where
  constructor IA
  arr : ArrayData a

||| A mutable array.
export
record MArray (n : Nat) (a : Type) where
  constructor MA
  arr : ArrayData a
```

Note, that both data types are not publicly exported, so we cannot
decompose them outside of the module they have been defined in.

For `IArray`, there is only one core function:

```idris
||| Safely access a value in an array at the given position.
export
at : IArray n a -> Fin n -> a
at (IA arr) m = prim__arrayGet arr (cast $ finToNat m) %MkWorld
```

Note, how we use `Fin n` to safely (that is, without having to check
the bounds) access an element in the array.

Of course we will be able to write and implement many derived functions
for immutable arrays, but they will all have to be implemented by
going via mutable arrays, which we will fill with the correct values.

For mutable arrays, we define five core functions, from which all others
can be derived. All of them accept the mutable array as a linear
argument to make sure it is not freely shared in client code. First,
here's the function for setting a position in an array to a new value:

```idris
export
set : Fin n -> a -> (1 _ : MArray n a) -> MArray n a
set m x (MA arr) = MA $ set' (finToNat m) x arr
```

It is important to see that this will return a new `MArray` (holding the
same `ArrayData` internally) to make sure we can continue using the array
in a linear context (the original `MArray` argument has been spent
and can no longer be used because of it being annotated with quantity `1`).

Second, function `get` for accessing a position in a mutable array.
This is more involved as it will not only have to return to
value at the position we look at (with unrestricted quantity) but
also a new `MArray` with quantity `1`. There is data type `Builtin.Res`
in the Prelude for this use case. Since `Res` is a dependent pair,
it is convenient to in our case define an alias for its type-constant
version:

```idris
public export
0 CRes : Type -> Type -> Type
CRes a b = Res a (const b)

export
get : Fin n -> MArray n a -@ CRes a (MArray n a)
get m (MA arr) = prim__arrayGet arr (cast $ finToNat m) %MkWorld # MA arr
```

When we are done with filling a mutable array with data, we often want
to convert it to an immutable array in order to be still able to
read the data but to no longer write to it:

```idris
freeze : MArray n a -@ Ur (IArray n a)
freeze (MA arr) = U (IA arr)
```

This is very important: Since the result type is an `Ur (IArray n a)`, we will
be able to freely share the resulting immutable array, while we will never
be able to use the mutable array argument again, because it was of quantity `1`.
This is the function that allows us to safely break out of the linear
context, by turning a mutable array into an immutable one. It is important to
understand that the underlying array data `arr` is still the same, and is
still - in theory - a mutable array. But the functions we defined here will not
allow client code to extract and mutate this array anymore. All we can do
now is reading the values it holds by means of function `at`.


As an additional pair of utilities, if we don't want to further use the `MArray`,
we can also safely discard it (we are going to use `discarding` in an example
below):

```idris
export %inline
discard : MArray n a -@ ()
discard (MA _) = ()

export %inline
discarding : (1 _ : MArray n a) -> x -> x
discarding (MA _) x = x
```

The last part, and the most complicated to understand, is the function
to create (allocate) a new mutable array. Let's write a wrong implementation
first:

```idris
createMutable : (n : Nat) -> a -> MArray n a
createMutable n v = MA $ prim__newArray (cast n) v %MkWorld
```

But this is definitely not what we want! The resulting array will be
freely shareable and referential transparency will be no more:

```idris
main : IO ()
main =
  let ma := createMutable 10 "foo"
   in do
     let x # _ := get 3 ma
         ma3   := set 3 "bar" ma
         y # _ := get 3 ma3
         z # _ := get 3 ma
     putStrLn x
     putStrLn y
     putStrLn z
```

By running the program above, we can see that `x` and `z` are not identical,
although they are the results of invoking the same pure function (`get`)
with the same arguments! We have overwritten a shared mutable array, exactly
the thing we wanted to make sure to prevent from happening.

The solution is to enforce that the freshly created `MArray` *must*
be used in a linear context, that is, in a linear function. And we
*must* make sure that the `MArray` does not leak out of this linear
function, even when being wrapped in a deeply nested data type. Here's how
to do this:

```idris
export
alloc : (n : Nat) -> a -> (1 fun : MArray n a -@ Ur b) -> Ur b
alloc n v f = f (MA $ prim__newArray (cast n) v %MkWorld)
```

Function `alloc` is the *only* function we export that allocates a new
array of size `n` filling all positions with the same value of type `a`.
The resulting `MArray` will be passed to function argument `fun`, which
can freely inspect and mutate it, but only in a linear context. Once
`fun` is done, the result it produces is wrapped in a `Ur`, which prevents
the `MArray` from being part of the result `b`, because the `b` wrapped
in the `Ur` - and therefore, all other values it potentially holds -
must be of unrestricted quantity.

## A Usage Example

Let us implement a very simple algorithm for counting the number
of occurrences of values of type `Fin n` in a list:

```idris
countFins : {n : _} -> List (Fin n) -> List (Fin n, Nat)
```

We could do this in `O(n*log(n))` time by first sorting the list and
then counting the occurrences with a simple fold from the left.
That would be nice and functional and declarative and all the good things.
Still, it would be slower than necessary, and sometimes, writing programs
is all about performance. So, instead of sorting the list and folding,
we iterate over the list once, keeping track of the counts in a mutable
array (this is an example of a [radix sort](https://en.wikipedia.org/wiki/Radix_sort)
that runs in O(n) complexity).

Here's the counting part:

```idris
toPairs : {n : _} -> MArray n a -@ Ur (List (Fin n, a))

count' : {n : _} -> List (Fin n) -> MArray n Nat -@ Ur (List (Fin n, Nat))
count' []        arr = toPairs arr
count' (x :: xs) arr =
  let c # arr2 := get x arr
      arr3     := set x (S c) arr2
   in count' xs arr3
```

We look at the implementation of `toPairs` in a moment. First, note how in
the implementation of `count'` we are forced to use every `MArray`
exactly once. After calling `get x arr`, `arr` has been spent, and we must
no longer use it. Luckily, `get` returns a new `MArray` (internally, this is
exactly the same `ArrayData`, so we don't pay anything in terms
of performance), which we are then forced to use again exactly once,
and so on.

This way, the mutable array is threaded linearly through our algorithm, without
the slightest chance of it escaping into the outer world.

We can finalize our implementation by invoking `alloc`:

```idris
countFins xs = unrestricted $ alloc n 0 (count' xs)
```

Now, extracting the values in an array requires iterating over the array's
indices. `Fin n` is not very well suited to do this, because when we
pattern match on a `Fin (S n)`, in case of an `FS x`, the wrapped `x` is of
type `Fin n`. We could call `weaken` on it, but this would confuse the totality
checker. That's why we typically need natural numbers for iterating over
the indices in an array, together with an auto implicit proof that the natural
number in question is within the valid bounds. The machinery and different
proof types for this come from module `Data.Array.Index`, which should be
reasonably well documented.

Here's how to collect the elements of an array in a list. Since the
list is built from last to first element, we can conveniently use
a natural number for counting down:

```idris
ontoPairs :
     List (Fin n, a)
  -> (m : Nat)
  -> {auto 0 p : LTE m n}
  -> (1 arr : MArray n a)
  -> Ur (List (Fin n, a))
ontoPairs xs 0     arr = discarding arr (U xs)
ontoPairs xs (S k) arr =
  let x        := natToFinLT k
      v # arr2 := get x arr
   in ontoPairs ((x,v) :: xs) k arr2

toPairs = ontoPairs [] n
```

You can try this at the REPL. Just keep in mind that the primitive operations
will not be reduced there, so we have to print the result via an
`IO` action using `:exec`:

```repl
...> :exec printLn (countFins {n=10} [2,7,6,6,4,2,2,4,3,3,3,1,0,8,9])
[(0, 1), (1, 1), (2, 3), (3, 3), (4, 2), (5, 0), (6, 2), (7, 1), (8, 1), (9, 1)]
...>
```

## Conclusion

This concludes our tutorial about how linear arrays are implemented. You
should now be able to look at the source code of the library and understand
how and why things are defined and implemented the way they are.

What we did not touch upon in this introduction is the use of linear
types for safe resource handling. That will be for another library and
another day.

<!-- vi: filetype=idris2:syntax=markdown
-->
