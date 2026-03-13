module Main

import Data.Array.All
import Data.Buffer
import Data.Buffer.Builder as BB
import Data.String.Builder as SB
import Data.Linear.Ref1
import Data.Linear.Token
import Data.List
import Profile

%default total

-- plain recursive single-argument loop
loop1 : Nat -> Nat -> Nat
loop1 n 0     = n
loop1 n (S k) = loop1 (n+2) k

-- plain recursive ten-argument loop
loop10 : Nat -> (b1,b2,b3,b4,b5 : Bool) -> (s1,s2,s3,s4 : String) -> Nat -> Nat
loop10 n b1 b2 b3 b4 b5 s1 s2 s3 s4 0     = n
loop10 n b1 b2 b3 b4 b5 s1 s2 s3 s4 (S k) = loop10 (n+2) b1 b2 b3 b4 b5 s1 s2 s3 s4 k

-- recursive loop with mutable reference
loopRef1 : Ref s Nat -> Nat -> F1 s Nat
loopRef1 ref 0     t = read1 ref t
loopRef1 ref (S k) t =
 let n # t := read1 ref t
     _ # t := write1 ref (n+2) t
  in loopRef1 ref k t

loopRef : Nat -> Nat
loopRef n = run1 $ \t => let ref # t := ref1 Z t in loopRef1 ref n t

-- recursive loop with record of 10 mutable references
record Refs s where
  constructor R
  b1, b2, b3, b4, b5 : Ref s Bool
  s1, s2, s3, s4     : Ref s String
  n1                 : Ref s Nat

mkRefs : F1 s (Refs s)
mkRefs t =
 let b1 # t := ref1 True t
     b2 # t := ref1 True t
     b3 # t := ref1 True t
     b4 # t := ref1 True t
     b5 # t := ref1 True t
     s1 # t := ref1 {a = String} "foo" t
     s2 # t := ref1 {a = String} "foo" t
     s3 # t := ref1 {a = String} "foo" t
     s4 # t := ref1 {a = String} "foo" t
     n1 # t := ref1 Z t
  in R b1 b2 b3 b4 b5 s1 s2 s3 s4 n1 # t

loopRef10 : Refs s -> Nat -> F1 s Nat
loopRef10 refs 0     t = read1 refs.n1 t
loopRef10 refs (S k) t =
 let n # t := read1 refs.n1 t
     _ # t := write1 refs.n1 (n+2) t
  in loopRef10 refs k t

loopRefrec : Nat -> Nat
loopRefrec n = run1 $ \t => let refs # t := mkRefs t in loopRef10 refs n t

-- recursive loop over a pair
loopPair : (Nat,Bool) -> Nat -> Nat
loopPair (x, y) 0     = x
loopPair (x, y) (S k) = loopPair (x+2,y) k

-- recursive loop with record of 10 mutable references
record Rec where
  constructor RC
  b1, b2, b3, b4, b5 : Bool
  s1, s2, s3, s4     : String
  n1                 : Nat

mkRec : Rec
mkRec = RC True True True True True "foo" "foo" "foo" "foo" 0

loopRec : Rec -> Nat -> Nat
loopRec rec 0     = rec.n1
loopRec rec (S k) = loopRec ({n1 $= (+2)} rec) k

-- recursive loop with mutable reference
0 Types : List Type
Types = [Nat,Bool,Bool,Bool,Bool,String,String,String,String,Nat]

loopAll1 : MHArr s Types -> Nat -> F1 s Nat
loopAll1 arr 0     t = All.get arr 0 t
loopAll1 arr (S k) t =
 let n # t := All.get arr 0 t
     _ # t := All.set arr 0 (n+2) t
  in loopAll1 arr k t

loopAllFst : Nat -> Nat
loopAllFst n =
  run1 $ \t =>
   let arr # t := mall1 [Z,True,True,True,True,"foo","foo","foo","foo",Z] t
    in loopAll1 arr n t

loopAll10 : MHArr s Types -> Nat -> F1 s Nat
loopAll10 arr 0     t = All.get arr 9 t
loopAll10 arr (S k) t =
 let n # t := All.get arr 9 t
     _ # t := All.set arr 9 (n+2) t
  in loopAll10 arr k t

loopAllLst : Nat -> Nat
loopAllLst n =
  run1 $ \t =>
   let arr # t := mall1 [Z,True,True,True,True,"foo","foo","foo","foo",Z] t
    in loopAll10 arr n t

hello : IBuffer ?
hello = "hello"

buildHello : Nat -> String
buildHello n = BB.withBuilder (loop n)
  where
    loop : {0 q : _} -> BB.Builder q => Nat -> F1 q String
    loop 0     t = getString t
    loop (S k) t = let _ # t := BB.put hello t in loop k t

sbuildHello : Nat -> String
sbuildHello n = SB.withBuilder (loop n)
  where
    loop : {0 q : _} -> SB.Builder q => Nat -> F1' q
    loop 0     t = () # t
    loop (S k) t = let _ # t := SB.putText "hello" t in loop k t

concatHello : Nat -> String
concatHello n = fastConcat $ replicate n "hello"

-- This profiles our JSON lexer against the one from parser-json
-- to know what we are up against.
bench : Benchmark Void
bench =
  Group "Loops" [
    Group "bytes build hello" [
      Single "10^4" (basic buildHello 10_000)
    , Single "10^5" (basic buildHello 100_000)
    , Single "10^6" (basic buildHello 1_000_000)
    , Single "10^7" (basic buildHello 10_000_000)
    ]
  , Group "string build hello" [
      Single "10^4" (basic sbuildHello 10_000)
    , Single "10^5" (basic sbuildHello 100_000)
    , Single "10^6" (basic sbuildHello 1_000_000)
    , Single "10^7" (basic sbuildHello 10_000_000)
    ]
  , Group "concat hello" [
      Single "10^4" (basic concatHello 10_000)
    , Single "10^5" (basic concatHello 100_000)
    , Single "10^6" (basic concatHello 1_000_000)
    , Single "10^7" (basic concatHello 10_000_000)
    ]
  , Group "loopRef1" [
      Single "10^5" (basic loopRef 100_000)
    , Single "10^6" (basic loopRef 1_000_000)
    , Single "10^7" (basic loopRef 10_000_000)
    , Single "10^8" (basic loopRef 100_000_000)
    ]
  , Group "loopRefrec" [
      Single "10^5" (basic loopRefrec 100_000)
    , Single "10^6" (basic loopRefrec 1_000_000)
    , Single "10^7" (basic loopRefrec 10_000_000)
    , Single "10^8" (basic loopRefrec 100_000_000)
    ]
  , Group "loopAllFst" [
      Single "10^5" (basic loopAllFst 100_000)
    , Single "10^6" (basic loopAllFst 1_000_000)
    , Single "10^7" (basic loopAllFst 10_000_000)
    , Single "10^8" (basic loopAllFst 100_000_000)
    ]
  , Group "loopAllLst" [
      Single "10^5" (basic loopAllLst 100_000)
    , Single "10^6" (basic loopAllLst 1_000_000)
    , Single "10^7" (basic loopAllLst 10_000_000)
    , Single "10^8" (basic loopAllLst 100_000_000)
    ]
  , Group "loop10" [
      Single "10^5" (basic (loop10 0 True True True False True "" "foo" "bar" "baz") 100_000)
    , Single "10^6" (basic (loop10 0 True True True False True "" "foo" "bar" "baz") 1_000_000)
    , Single "10^7" (basic (loop10 0 True True True False True "" "foo" "bar" "baz") 10_000_000)
    , Single "10^8" (basic (loop10 0 True True True False True "" "foo" "bar" "baz") 100_000_000)
    ]
  , Group "loopPair" [
      Single "10^5" (basic (loopPair (0, False)) 100_000)
    , Single "10^6" (basic (loopPair (0, False)) 1_000_000)
    , Single "10^7" (basic (loopPair (0, False)) 10_000_000)
    , Single "10^8" (basic (loopPair (0, False)) 100_000_000)
    ]
  , Group "loopRec" [
      Single "10^5" (basic (loopRec mkRec) 100_000)
    , Single "10^6" (basic (loopRec mkRec) 1_000_000)
    , Single "10^7" (basic (loopRec mkRec) 10_000_000)
    , Single "10^8" (basic (loopRec mkRec) 100_000_000)
    ]
  , Group "loop1" [
      Single "10^5" (basic (loop1 0) 100_000)
    , Single "10^6" (basic (loop1 0) 1_000_000)
    , Single "10^7" (basic (loop1 0) 10_000_000)
    , Single "10^8" (basic (loop1 0) 100_000_000)
    ]
  ]

main : IO ()
main = runDefault (Prelude.const True) Table show bench
