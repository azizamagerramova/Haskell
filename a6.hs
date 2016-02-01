import Data.Array
import Data.IORef (newIORef, readIORef, writeIORef)

{- ASSIGNMENT 6

Due: 2015-10-21 23:55

You will need to consult the documentation on the imported modules.
(https://downloads.haskell.org/~ghc/latest/docs/html/libraries/)

Please note: ghci will evaluate expressions, of course, but if the
expression is of type (IO a), its value will be *executed* and the
resulting value in type a showed.

The first two questions are 50 points each and count for 100% of the
mark.  The last one is worth 25 points and is for extra credit; scores
over 100% will be factored in total assignment marks for the term.

-}


----------------------------------------------------------------

{- QUESTION 1

Use imperative-style programming to implement the factorial function
in the IO monad.  In other words, create and initialize variables
(references) using newIORef, modify their values using a while loop
with ,readIORef and writeIORef, then have the IO action return a pair
consisting of the input (n) and the final result.  The expression
named mod3 below gives a small example of this kind of programming.

Reading:
- LYAH Chapter 9 "Input and Output" up to the first occurrence of
"Control.Monad".
- Module documentation for the functions imported from Data.IORef (see
the top of this file).

-}

while :: IO Bool -> IO () -> IO ()
while test body =
  do b <- test
     if b
       then do {body ; while test body}  -- same-line syntax for do
       else return ()

-- remainder when integer-dividing n by 3
mod3 :: Integer -> IO Integer
mod3 n = do r <- newIORef n
            while
              (do {v <- readIORef r; return (v >= 3)})
              (do {v <- readIORef r; writeIORef r (v-3)})
            readIORef r          

-- ghci> fact 4
-- 24

fact :: Integer -> IO (Integer, Integer) 
fact n = do r <- newIORef n
            a <- newIORef 1 
            while
              (do {v <- readIORef r;  return (v >= 1) })
              (do {v <- readIORef r;f <- readIORef a; writeIORef a ( v* f); writeIORef r (v-1)})
            r<-readIORef a
            return (n, r)      




----------------------------------------------------------------


{- CODE FOR QUESTIONS 2 AND 3

Below we give a roll-your-own alternative to Data.IORef.  We model
memory as an array and memory locations (references) as indices into
the array.  Using this model it is straightforward to implement
creation, reading and writing of references.

However, as with the IO monad, we use a layer of abstraction to hide
all the details of memory management.  Instead of (IO a), we will
have (MM a) -- "MM" for "memory modifiers".

The implementation of actions in (IO a) is completely hidden from us
in Haskell.  The actions in (MM a) will all be constructed from
scratch using the usual kinds of Haskell data.  The basic decision in
designing MM is how represent actions.

Since we're focusing on references, it's natural to consider an action
as something, that in addition to producing a value, modifies memory.
Modifying something in a functional setting is done by applying a
function which produces the new "modified" copy.  Thus an action can
be thought of as a function that takes a memory (array), and from it
produces both a value and a new memory (an array with possibly some
values updated).

More formally, actions in (MM a) are elements of the type

  Mem -> (Mem,a)

so we define

data MM a = MM (Mem -> (Mem, a))

We want to use the same "do" syntax to hide memory management details
that IO does.  Fortunately, it turns out that MM is a monad.  The
definition of (>>=) for MM is not immediately transparent, but it need
not be to do Question 2.  For question 2, MM can be thought of as
replacement for IO and programs using "do" can be constructed
analogously.  Question 3 requires understanding details of the
construction of MM and its operations.

-}

-- for convenience
type Z = Integer

-- raise an error if an attempt to index the array is out of bounds
checkBounds :: String -> Z -> Array Z a -> ()
checkBounds msg i a =
  let (lower, upper) = bounds a
  in if i >= lower && i < upper
     then ()
     else error msg
  

-- Memory is modeled by (Mem n i a) where:
--   - n is the size of the memory (number of locations)
--   - a is an array, with indexes 0<=i<n, representing the
--     values stored in memory and
--   - i is the next position to allocate at
data Mem = Mem Z Z (Array Z Z)
         deriving Show

-- A reference is an index into the memory array.
type Ref = Z

-- Memory-modifying computations with result type a.
data MM a = MM (Mem -> (Mem, a))

-- ignore, not needed for either question!
instance Functor MM where
  fmap f (MM g) = MM (\m -> let (m',v) = g m in (m', f v))

-- ignore, not needed for either question!
instance Applicative MM where
  pure x = MM (\m -> (m,x))
  MM f <*> MM g =
    MM (\m-> let (m', f') = f m
                 (m'', x) = g m'
             in (m'', f' x))


instance Monad MM where

  -- action that produces x without modifying memory
  return x = MM (\m -> (m,x))

  -- like composing f and g, except memory modifications are chained
  (MM a) >>= f =
    MM (\m-> let (m', v) = a m
                 MM b = f v
             in b m')

-- create an initial memory of size n
initMem :: Z -> Mem
initMem n = Mem n 0 (array (0,n) [])

-- return a new reference, initialized to v
newRef :: Z -> MM Ref
newRef v =
  MM f where
    f (Mem n i a) = (m', i )
      where m' = Mem n (i+1) a'
            a' = a // [(i,v)]

writeRef :: Ref -> Z -> MM ()
writeRef j v =
  MM f where f (Mem n i a) = (Mem n i a', ())
               where a' = a // [(j,v)]

readRef :: Ref -> MM Z
readRef j =
  MM f where f m@(Mem _ _ a) = (m, a!j)

run :: Z -> MM a -> a
run n (MM mm) =
  snd $ mm (initMem n)

-- run the action and return a list of memory contents
runDump :: Z -> MM a -> [Z]
runDump n (MM mm) =
  elems a where
    Mem _ _ a = fst $ mm (initMem n)

-- The test needs to be in MM Bool instead of just Bool because it
-- will generally need to refer to values stored in memory.
while' :: MM Bool -> MM () -> MM ()
while' test body =
  do b <- test
     if b
       then do {body ; while' test body}
       else return ()


----------------------------------------------------------------


{- QUESTION 2

Repeat Question 1, but using MM and its reference operations in place
of IO, and while' in place of while.  You can execute elements of (MM
a) using the run function above (which also takes an argument for the
size of memory to use).

ghci> run 10 (fact' 4)
24

-}

fact' :: Integer -> MM (Integer, Integer)
fact' n = do  r <- newRef n
              a <- newRef 1
              while' 
                (do {v <- readRef r; return (v>=1 )})
                (do {v <- readRef r; f <- readRef a; writeRef a (v*f); writeRef r (v-1)})
              r<- readRef a   
              return (n, r)
            


----------------------------------------------------------------


{- QUESTION 3  --  EXTRA CREDIT

Implement versions of newRef, writeRef and readRef that, instead of
returning a single reference, allocate a pair of consecutive storage
locations and return the first address (index).  Effectively, the
operations deal with 2-cell objects.  The advantage of this is that
linked structures, like linked lists, can be implemented.

Below is given the types for the new operations, and a program
appendTest that creates two linked lists then appends them by changing
the pointer at the end of the first list.  The example uses some
auxiliary functions.  You just need to implement the three reference
operations.

-}

newRef2 :: Z -> Z -> MM Ref
newRef2 u v =
  undefined

writeRef2 :: Ref -> Z -> Z -> MM ()
writeRef2 j u v =
  undefined

readRef2 :: Ref -> MM (Z,Z)
readRef2 j =
  undefined




mkList :: [Z] -> MM Ref
-- Use -1 for "nil", i.e. null pointer
mkList [] = return (-1)
mkList (x:xs) =
  do tail <- mkList xs
     head <- newRef2 x tail
     return head

append :: Ref -> Ref -> MM (Ref)
-- x and y must be pointers to lists
append (-1) y = return y
append x y =
  do append' x
     return x
  where append' x =
          do (v,i) <- readRef2 x
             if i == -1
               then writeRef2 x v y
               else append' i

collectList :: Ref -> MM [Z]
collectList (-1) = return []
collectList i =
  do (x,j) <- readRef2 i
     xs <- collectList j
     return (x:xs)

-- ghci> run 37 appendTest
-- [1,2,3,4,5,6]
appendTest :: MM [Z]
appendTest =
  do l <- mkList [1,2,3]
     newRef 17 >> newRef 17 >> newRef 17  -- some irrelevant creations
     l' <- mkList [4,5,6]
     newRef 17 >> newRef 17 >> newRef 17  -- ditto
     x <- append l l'
     result <- collectList x
     return result