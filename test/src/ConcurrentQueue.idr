module ConcurrentQueue

import Data.Queue
import Data.Vect as V
import Data.Array
import Data.Array.Mutable
import System.Concurrency
import System

%default total

record State where
  constructor ST
  cur   : Nat
  queue : Queue Nat

next : State -> State
next (ST n q) = ST (S n) (enqueue q n)

ITER : Nat
ITER = 10_000

DELAY : Nat
DELAY = 100_000

data Prog = Unsafe | CAS | Mut

inc : (r : IOArray 1 State) -> Nat -> F1' [World]
inc r 0     = modify r 0 next
inc r (S k) = inc r k

casinc : (r : IOArray 1 State) -> Nat -> F1' [World]
casinc r 0     = casmodify r 0 next
casinc r (S k) = casinc r k

mutinc : Mutex -> IOArray 1 State -> Nat -> Nat -> IO ()
mutinc m r n     (S k) = mutinc m r n k
mutinc m r 0     0     = pure ()
mutinc m r (S k) 0     = do
  mutexAcquire m
  runIO (inc r 0)
  mutexRelease m
  mutinc m r k DELAY

prog : Prog -> Mutex -> IOArray 1 State -> IO ()
prog Unsafe m ref = runIO (forN ITER $ inc ref DELAY)
prog CAS    m ref = runIO (forN ITER $ casinc ref DELAY)
prog Mut    m ref = mutinc m ref ITER DELAY

runProg : Prog -> Nat -> IO (List Nat)
runProg prg n = do
  mut <- makeMutex
  ref <- newIOArray 1 (ST 0 empty)
  ts  <- sequence $ V.replicate n (fork $ prog prg mut ref)
  traverse_ (\t => threadWait t) ts
  toList . queue <$> runIO (get ref 0)

main : IO ()
main = do
  us <- runProg Unsafe 4
  cs <- runProg CAS 4
  when (length us >= length cs) (die "no race condition")
  when (cs /= [0 .. pred (4 * ITER)]) (die "CAS synchronization failed")
  putStrLn "Concurrent queue succeeded!"
