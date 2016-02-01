import Text.ParserCombinators.ReadP
import Control.Monad
import Data.Maybe (isJust, fromMaybe)
import Data.List (intercalate)
import Debug.Trace
                  
{-

# Assignment 4 COMP 3007 Fall 2015

Due: 23:55 Wed Sep 30 2015

**What to submit.** Submit this Haskell file with the questions
completed.

**Collaboration policy.** Collaborating on assignments is STRICTLY
DISALLOWED. You must complete the work by yourself. If you need
help, please see a TA or your instructor. Posting assignment
solutions on discussion boards before the due date and time is also
prohibited.

**What you can use.** In this assignment, you can use anything from
the lectures, the given Haskell file (including what's imported) and
anything in the Prelude.  Nothing more though.  The first two import
lines at the beginning of the file can be ignored.  They're just for
the parser.  The next two are useful but you don't need to use them.

**Debugging.** You might find the debugger useful.  It's imported
above. It's quite easy to use the basic tracing facility. See the
Haskell Hierarchical Libraries documentation for info on how to use
it:

https://downloads.haskell.org/~ghc/latest/docs/html/libraries/

The assignment is to implement the evaluator for the language L
discussed in class.  You should review the notes from that class.
There is also a complete description of the language in this file.

## Description of L

Here is the description of L that was discussed in the Wed Sept 23
lecture.

Expressions (abstract and concrete syntax):

%x.e  -- lambda abstraction, like \x->e in Haskell
e e'  -- application
x,y,z -- variables
succ, pred, ifzero, 0, 1, 2....

Values:

0, 1, 2, 3,...
%x.e
succ, pred, ifzero
ifzero e
ifzero e e


Evaluation: e ==> v means e evaluates to value v.  The rules below
specify how to evaluate.

For an algorithmic view, you can read the rules bottom-up.  E.g. the
second rule can be read as saying that to evaluate an application
expression e e', first evaluate e, and if you get a value of the form
%x.b, continue by evaluating b[e'/x], and if that results in a value
v, return that as the result of evaluating e e'.

There's a more algorithmic presentation of evaluation in the lectures
notes.  There are a few small differences, so please use the
definition below as the specification for your evaluator.


-------
e ==> v

e ==> %x.b  b[e'/x] ==> v   (b[e'/x] is substitution of e' for x in b)
-------------------------
e e' ==> v

e ==> succ e' ==> n  m=n+1
--------------------------
e e' ==> m

e ==> pred e' ==> n  m=max(n-1,0)
---------------------------------
e e' ==> m

e ==> ifzero
------------------
e e' ==> ifzero e'

e ==> ifzero eb
---------------------
e e' ==> ifzero eb e'

e ==> ifzero eb et  eb ==> 0  et ==> v
--------------------------------------
e e' ==> v

e ==> ifzero eb et  eb ==> u  u \= 0  e' ==> v
-----------------------------------------------
e e' ==> v

Here is an example of how to derive an evaluation fact.

## Example evaluation

Write s for succ

%x.s x ==> %x.s x
(%f.%x.f x) ==> (%f.%x.f x)    s ==> s  3 ==> 3  4=3+1
---------------------------   ------------------------
(%f.%x.f x) s ==> %x.s x          s 3 ==> 4
-------------------------------------------
(%f.%x.f x) s 3 ==> 4


## The Y combinator

The language L may not seem so far to have a way of defining functions
recursively.  However, it does.  The key is the following expression,
which we'll call Y:

   %f. (%x. f (x x)) (%x. f (x x))

Don't try to figure out what it means.  All that matters it how it
behaves when you compute with it.  

Suppose F is some other expression.  By considering evaluation steps,
we can see that the following equalities hold, if by "equal" we mean
that the equal things always compute to the same values no matter how
they're used.  The first step below is applying the function Y to its
one argument, and this means plugging F in for f in the body of the %
expression (%f.  ...).  The second step is one more application step,
and the last step is just using the reverse of the first step
(replacing a bigger term by YF).

Y F = (%x. F (x x)) (%x. F (x x))
    = F ((%x. F (x x)) (%x. F (x x)))
    = F (Y F)

The equality we get, Y F = F (Y F), is the key thing.  You don't
really need to understanding anything at all about Y other than this
fact.  

Let's see how this fact can be used to do recursion, by using a simple
example.

Suppose we actually were able to do recursive definitions in L.  The
definition of factorial could look something like this.

   fact = %n. ifzero n 1 (times n (fact (pred n)))

However, we can rewrite the above as follows:

   fact  =  (%f. %n. ifzero n 1 (times n (f (pred n))))  fact

All we've done is introduce an anonymous function of one argument
that when applied to fact gives us the original right-hand-side of
the defintion.  Let's give a name to this anonymous function just for
reference:

   F = %f. %n. ifzero n 1 (times n (f (pred n)))

Using this name instead of the term, the last equation for fact above
becomes 

  fact = F fact

Let's look at what Y F does for this F.  Let's apply it to 3 and
see what that's equal to.

Y F 3 = 
F (Y F) 3 =
(%n. ifzero n 1 (times n ((Y F) (pred n)))) 3 =
ifzero 3 1 (times 3 ((Y F) (pred 3))) =
times 3 ((Y F) (pred 3)) =
times 3 ((Y F) 2)

We can do the same thing with (Y F) 2.

(Y F) 2 =
F (Y F) 2 =
(%n. ifzero n 1 (times n ((Y F) (pred n)))) 2 =
times 2 ((Y F) 1)

Putting the above results together, we have

   (Y F) 3 = times 3 (times 2 ((Y F) 1))

Continuing in this way, we get

   (Y F) 3 = times 3 (times 2 (times 1 ((Y F) 0)))
           = times 3 (times 2 (times 1 1))
           = 6 

In conclusion, (Y F) for this F behaves just like we want fact to.

-}


{-

## Abstract Syntax of L

This is the representation of L you will be working with.  

-}

-- Identifiers for % expressions and variables
type Id = String

-- The "builtin" functions.
data Op = Succ | Pred | IfZero
           deriving (Show, Ord, Eq)

-- Expressions of L
data Exp = Var Id
         | Nat Integer
         | Op Op
         | Lam Id Exp
         | App Exp Exp
           deriving (Ord, Eq, Show)

-- "Pretty printer" for expressions.  You can override the Show method
-- for Exp using it if you like.  The instance declaration is below
-- (don't forget to remove Show from the "deriving" clause for Exp).
pp :: Exp -> String
pp (Var s) = s
pp (Nat n) = show n
pp (Op Succ) = "succ"
pp (Op Pred) = "pred"
pp (Op IfZero) = "ifzero"
pp (Lam x e) = "%" ++ x ++ "." ++ pp e
pp (App e e') = paren_fun e ++ " " ++ paren_arg e'
  where paren_fun e@(Lam _ _) = paren $ pp e
        paren_fun e = pp e
        paren_arg e@(App _ _) = paren $ pp e
        paren_arg e@(Lam _ _) = paren $ pp e
        paren_arg e = pp e
        paren s = "(" ++ s ++ ")"

-- instance Show Exp where
--   show = pp



{-

## Concrete Syntax of L

Reminder: iterated applications ((m n1) n2) ... can be written without
the parens, i.e. m n1 n2.... However, %-abstractions must be written
separately, e.g. "%x y. x y" is not allowed, it has to be written
"%x.%y. x y".

You don't need to know anything about this section except that
there is a function

  parse :: String -> Exp

that converts the usual representation (as we used in class) into
Exp.  For example:

   parse "%f. f 1 2" =
   Lam "f" App (App (Var "f") (Nat 1)) (Nat 2)

The parser is written using the imported "monadic parsing combinator"
library.

-}


nextChar :: Char -> ReadP Char
nextChar c = skipSpaces >> char c

pfailIf :: Bool -> ReadP ()
pfailIf b = if b then pfail else return ()

-- Amusing (?) anecdote: I spent an hour tracking down a bug that
-- turned out to be a missing letter ("n") in the alphabet string
-- below.
isAlpha :: Char -> Bool
isAlpha = flip elem "abcdefghijklmnopqrstuvwxyz"

isNum = flip elem "0123456789"

isAlphanum :: Char -> Bool
isAlphanum =  liftM2 (||) isAlpha isNum
             
identifierParser :: ReadP Id
identifierParser =
  skipSpaces
  >> liftM2 (:) (satisfy isAlpha) (munch isAlphanum)

natParser :: ReadP Exp
natParser =
  do
    skipSpaces
    num <- munch1 isNum
    return $ Nat $ (read num :: Integer)

wordParser :: String -> ReadP String
wordParser w =
  do id <- identifierParser
     pfailIf (w /= id)
     return w
     
succParser :: ReadP Op
succParser =
  wordParser "succ" >> return Succ

predParser :: ReadP Op
predParser =
  wordParser "pred" >> return Pred

ifzeroParser :: ReadP Op
ifzeroParser =
  wordParser "ifzero" >> return IfZero

opParser :: ReadP Exp
opParser =
  liftM Op $ succParser +++ predParser +++ ifzeroParser

varParser :: ReadP Exp
varParser =
  liftM Var identifierParser

atomParser :: ReadP Exp
atomParser = opParser <++ varParser +++ natParser

lamParser :: ReadP Exp
lamParser =
  liftM2
  Lam
  (nextChar '%' >> identifierParser)
  (nextChar '.' >>  expParser)

parenParser :: ReadP Exp
parenParser =
  between (nextChar '(') (nextChar ')') expParser

headParser :: ReadP Exp
headParser = atomParser +++ parenParser

argParser :: ReadP Exp
argParser = atomParser +++ lamParser +++ parenParser
  
argsParser :: ReadP [Exp]
argsParser =
  args1Parser <++ return []

args1Parser :: ReadP [Exp]
args1Parser =
  do e <- argParser
     es <- argsParser
     return $ e:es

appParser :: ReadP Exp
appParser =
  do e <- headParser
     args <- args1Parser
     return $ foldl1 App $ e : args
               
expParser :: ReadP Exp
expParser = appParser <++ atomParser
            +++ lamParser +++ parenParser 

parseWith :: ReadP a -> String -> a
parseWith p = fst . head . readP_to_S p

parse :: String -> Exp
parse = parseWith expParser


{-

## Evaluation

-}

-- QUESTION 1: 25 pts
--
-- subst x e e': substitute e for all "free" occurrences of (Var x) in
-- e'.  "Free" means that the variable it is not declared by a
-- surrounding %.  For example, in the expression
--
-- x (%x. x (%y.xz)) (%y.x)

-- there are 5 occurrences of x.  The first is "free".  The second is
-- the parameter for the % expression and is never substituted for.
-- The third and fourth occurrences refer to the parameter of the
-- enclosing % expression.  The fifth is free.  Therefore if we
-- substitute 0 for x we get 0 (%x. x (%y.xz)) (%y.0)
subst :: Id -> Exp -> Exp -> Exp
--subst = stub "subst"
subst d m (Var x) = if x==d
						          then m
						          else Var x
subst d m(Nat x) =  Nat x
--subst d m (Op _) = []
subst d m(Lam x e) = if (x==d)
						            then Lam x e
						            else Lam x (subst d m e)
subst d m(App e e') =  App (subst d m e) (subst d m e')

-- QUESTION 2: 25 pts
--
-- isClosed e is true if and only if there are no free variables in e
-- (see the discussion in the comment for subst).
-- Examples: (%x. %y. x y) is closed; (%x. y %y. x y) is not since the
-- first occurrence of y is free.
isClosed :: Exp -> Bool
isClosed y = isClosedList y []

isClosedList (Nat x) l = True
isClosedList (Op _) l = True
isClosedList (Var x) l = elem x l
isClosedList (Lam x e ) l = isClosedList e (x:l)
isClosedList (App e e') l = (isClosedList e l) && (isClosedList e' l)

-- QUESTION 3: 50 pts
--
-- eval e = v where e ==> v.  If there is no v such that e==>v, the
-- result is undefined.  Assume that e is closed.
suc (Nat x) = Nat (x+1)
pre (Nat x) = Nat (x-1)

eval :: Exp -> Exp
eval (Var n) = Var n
eval (Nat n) = Nat n
eval (App e e') =  if e == (Op Succ) 
					then if eval e' /= e'
							then suc (eval e')
						  else suc e'
					else if e == (Op Pred)
						then if eval e' /= e'
								then pre (eval e')
						    else pre e'
					else if e == (Op IfZero)
							e'
							
							
								


								
  
run :: Exp -> String
run e =
  if isClosed e
  then pp $ eval e
  else error "run: expression must be closed"

stub :: String -> a
stub s = error ("Not implemented: " ++ s)


{-
## Examples

Examples to test your evaluator on.  First, some functions for
building examples.

-}

yComb           = parse "%f. (%x. f(x x)) (%x. f(x x))"

mkLam :: [String] -> Exp -> Exp
mkLam [] body = body
mkLam (x:xs) body = Lam x (mkLam xs body)

-- def lhs rhs e gives a term that behaves like a function recursively
-- defined by lhs, rhs and e.  See the examples below for more.  It's
-- important to note that the resulting expression is not a named
-- function, even though the lhs string mentions a name.  It is
-- simply an expression that you can apply to arguments.
def :: String -> String -> Exp
def fnargs body
  = let (f:args) = words fnargs
    in App yComb $ Lam f (mkLam args (parse body))

-- apply e strs: parse the strings in strs and add the resulting
-- expressions as arguments to e.
apply :: Exp -> [String] -> Exp
apply e s = foldl App e (map parse s)


--
-- The examples.
--

-- map run nonRecExamples =
-- ["1","18","1","2","17","2","17","4","2","27"]
nonRecExamples =
  map
  parse
  [ "succ 0"
    -- 1
  , "succ (succ (pred 17))"
    -- 18
  , "ifzero 0 (succ 0) (pred 3)"
    -- 1
  , "ifzero 17 (succ 0) (pred 3)"
    -- 2
  , "(%x. x) 17"
    -- 17
  , "(%x.%y. ifzero x y 17) 0 2"
    -- 2
  , "(%x.%y. ifzero x y 17) 1 2"
    -- 17
  , "(%x.%y. ifzero x y (%z. succ z)) 1 2 3"
    -- 4
  , "(%x.%x.x) 1 2"
    -- 2
  , "(%f.%x. f (f (f x))) (%f.%x. f (f (f x))) succ 0"
    -- 27
  ]

{-
The rest of the examples involve recursion based on the Y
combinator.  If your evaluator works on the above, it will likely
work on the examples below.  However, if it doesn't, it might not
be so easy to debug.   The Debug.Trace module is handy.  In any
case, if your evaluator only works on the above examples, you will
receive goodly partial credit.
-}

-- run (apply stupidZero ["17"])
-- = 0
stupidZero = def "f x" "ifzero x 0 (f (pred x))"

-- run (apply plus ["34", "17"])
-- = 51
plus = def "plus m n" "ifzero m n (succ (plus (pred m) n))"

-- run (apply times ["34", "17"])
-- = 578
times =
  subst "plus" plus times'
  where
    times' =
      def "times m n" "ifzero m 0 (plus n (times (pred m) n))"

-- run (apply fact ["4"])
-- = 24
-- You don't need to try any bigger arguments!  This kind of
-- evaluator is quite inefficient because of the duplication that
-- often happens when substituting during evaluation.  
fact =
  subst "times" times fact'
  where
    fact' =
      def "fact n" "ifzero n 1 (times n (fact (pred n)))"

