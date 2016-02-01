{-  ASSIGNMENT 10.

DUE: Monday Dec 7.

This file contains a Prolog0 interpreter.  The assignment is to modify
it.  The three questions have equal weight.

There is an accompanying Prolog file "a10_prolog.pl" which should be
put in the same folder/directory as this code file.  Question 3
requires modifying it, so you should submit both this Haskell file and
the Prolog file.


Question 1.

The function "query1" prints one solution, using "dfs" to find it.
The function "query" should print all solutions, using "dft" to find
them.  Complete the definition of dft.  See the comments on the
functions for more details.  Running

  query "append(L, M, cons(1, cons(2, cons(3, cons(4, nil)))))"

should give output

  Solution found: [L->nil,M->cons(1,cons(2,cons(3,cons(4,nil))))]
  Solution found: [L->cons(1,nil),M->cons(2,cons(3,cons(4,nil)))]
  Solution found: [L->cons(1,cons(2,nil)),M->cons(3,cons(4,nil))]
  Solution found: [L->cons(1,cons(2,cons(3,nil))),M->cons(4,nil)]
  Solution found: [L->cons(1,cons(2,cons(3,cons(4,nil)))),M->nil]



Question 2.

Complete the definition of "bft".  See the comments on "bft" and
"bfsQuery1" for more details.  The Prolog0 file has a Prolog program
for finding a path in a simple maze.  If you run

  query "solution(L)"

the interpreter will diverge, stupidly trying forever to build a
looping path.  However,

  bfsQuery1 "solution(L)"

will return a solution path:

Solution found: [L->cons(c(0,0),cons(c(1,0),cons(c(2,0),cons(c(3,0),cons(c(3,1),cons(c(3,2),cons(c(3,3),nil)))))))]



Question 3:

This question is just an exercise in writing Prolog programs.  A
collection of "arithmetic expressions" is defined in the Prolog file:
they're the objects e such that the query `isarithex(e)` has a
solution.

You are to write Prolog rules for "var", which can be used to compute
the list of variables occurring in an arithmetic expression.  Running

  query "varstest"

should result in

  Solution found: []

Of course, your Prolog program should work on all arithmetic
expressions, not just the one baked into varstest!

-}

import Data.Map.Strict (Map)
import qualified  Data.Map as M
import Data.List (intercalate, find)
import Data.Maybe
import Text.ParserCombinators.ReadP
import Control.Monad
import Debug.Trace

type Id = String

data Exp  =  Var Id        -- convention: uppercase
           | Sym Id [Exp]  -- convention: lowercase
           deriving Eq

data Equation = Equation {equationL::Exp, equationR::Exp}
              deriving Eq

data Subst = Subst (Map Id Exp)

-- A type is "syntactic" if it makes sense to substitute into
-- it. E.g. equations are just pairs of expressions, so an obvious
-- definition of substitution for Equation is to substitute into each
-- of the expressions in the equation.
class Syntactic a where
  subst :: Subst -> a -> a

instance Syntactic Exp where
  subst s (Sym sym l) = Sym sym (map (subst s) l)
  subst (Subst m) (Var x) = maybe (Var x) id (M.lookup x m)

instance Syntactic Equation where
  subst s (Equation l r) =
    Equation (subst s l) (subst s r)

instance Syntactic a => Syntactic [a] where
  subst s l = map (subst s) l

instance Syntactic b => Syntactic (Map a b) where
  subst s m = M.map (subst s) m

instance Syntactic Subst where
  subst s (Subst m) = Subst $ subst s m

instance Syntactic a => Syntactic (Maybe a) where
  subst s (Just v) = Just (subst s v)
  subst s Nothing = Nothing

emptySubst :: Subst
emptySubst = Subst M.empty

singletonSubst :: Id -> Exp -> Subst
singletonSubst x e = Subst $ M.singleton x e

substCompose :: Subst -> Subst -> Subst
substCompose (Subst m0) (Subst m1) =
  Subst $ M.union (subst (Subst m0) m1) m0

occurs :: Id -> Exp -> Bool
occurs x (Var x') | x == x' = True
occurs x (Sym _ l) = any (occurs x) l
occurs x _ = False

-- The unification algorithm, exactly as in class except for some
-- Haskell-specific details being fleshed out.
unify :: [Equation] -> Maybe Subst
unify [] = Just emptySubst
unify (Equation (Sym symL argsL) (Sym symR argsR)  : eqs)
  | symL == symR && length argsL == length argsR
  = unify $ zipWith Equation argsL argsR ++ eqs
unify (Equation (Var x) (Var y) : eqs)
  | x==y
  = unify eqs       
unify (Equation (Var x) e : eqs) =
  do guard $ not $ occurs x e
     let s = singletonSubst x e
     s' <- unify (subst s eqs)
     return $ substCompose s' s
unify (Equation e (Var x) : eqs) =
  unify (Equation (Var x) e : eqs)
unify _ = Nothing


data Rule = Rule Exp [Exp] 

data Program = Program [Rule]
             deriving Show

-- Search trees for solutions.  At each node there is a branch for
-- each rule in the program.  Leaves are complete solutions to the
-- starting goal.  Note that because of Haskell's lazy evaluation, the
-- tree only gets elaborated on demand.  If we do a depth-first search
-- of the tree for the first solution in it, only the rule
-- applications on the way to this solution are done.
data Search = Branches [Search] | Solution Subst
            deriving Show
  
instance Show Rule where
  show (Rule e es) = show e ++ " :- " ++ show es

-- Add a numerical suffix to each variable in the expression.  This is
-- used to "freshen" the variables of a rule each time it is used.
suffixVars :: Int -> Exp -> Exp  
suffixVars n (Var x) =
  Var $ x ++ show n
suffixVars n (Sym sym args) =
  Sym sym $ map (suffixVars n) args

-- This is the core of the Prolog0 interpreter.
-- (search p n s gs): generate s search tree for solutions for the
-- goal list gs, building on the given substitution s, using the
-- number n to tag variables in the rules to make them distinct from
-- previous rule applications, and generating a branch for each rule
-- in the program p.
search :: Program -> Int -> Subst -> [Exp] -> Search
search p _ s [] = Solution s
search p@(Program rs) n s (g:gs) =
  Branches (map step rs)
  where step (Rule concl assums) =
          nextSearch $ unify [Equation g concl']
          where
            concl' = suffixVars n concl
            assums' = map (suffixVars n) assums
            nextSearch Nothing = Branches []
            nextSearch (Just s') =
              search p (n+1) (substCompose s' s) (subst s'
                                                  (assums'++gs))

-- Do a depth-first search of the search tree for the given goals,
-- returning the first solution found.
dfs :: Program -> [Exp] -> Maybe Subst
dfs p gs =
  findSolution $ search p 0 emptySubst gs
  where findSolution (Solution s) = Just s
        findSolution (Branches l) =
          let solutions = filter isJust $ map findSolution l
          in if null solutions
             then Nothing
             else head solutions

-- dft = depth-first traversal.  Do a depth-first search of the search
-- tree for the given goals, returning all the solutions found.
dft :: Program -> [Exp] -> [Subst]
dft p gs =
  


-- Do a breadth-first search of the search tree, returning the first
-- solution found.  In other words, return the solution (if any) that
-- is found at the lowest possible depth in the tree.
bfs :: Program -> [Exp] -> Maybe Subst
bfs p gs =
  undefined

defaultFileName = "a10_prolog.pl"

-- (query1 s): parse the Prolog program in defaultFileName, parse the
-- query s (a sequence of expressions separated by commas), run the
-- query against the Prolog program using a depth-first-search in the
-- search result tree for a solution, and print the first solution
-- found.
query1 :: String -> IO ()
query1 s =
  do p <- parseFile defaultFileName
     printResult $ dfs p $ parseWith goalsP s

-- Like query1, but using bread-first search instead of depth-first.
bfsQuery1 :: String -> IO ()
bfsQuery1 s =
  do p <- parseFile defaultFileName
     printResult $ bfs p $ parseWith goalsP s

printResult :: Maybe Subst -> IO()
printResult (Just s) =
  putStrLn $ "Solution found: " ++ show s

printResult Nothing =
  putStrLn $ "No"

-- print all solutions
query :: String -> IO()
query s = 
  do p <- parseFile defaultFileName
     printResults $ dft p $ parseWith goalsP s

printResults :: [Subst] -> IO()
printResults l =
  if null l then putStrLn "No."
  else mapM_ putStrLn $ map result $ l
  where result s = "Solution found: " ++ show s
        

--------------------------------------------------------------
--------------------------------------------------------------
--------------------------------------------------------------
--
-- Nothing of interest after this point.
--
--------------------------------------------------------------
--------------------------------------------------------------
--------------------------------------------------------------

instance Show Equation where
  show (Equation l r) = show l ++ " = " ++ show r

instance Show Exp where
  show (Var id) = id
  show (Sym sym []) = sym
  show (Sym sym l) = sym ++ "(" ++ argString ++ ")"
    where argString = intercalate "," (map show l)

-- Suppress printing of any pair (Var s) |-> e where s ends in a
-- numeral.  This is to clean up the presentation of search trees,
-- whose solutions contain substitutions for all the "temporary"
-- variables generated along the way.
instance Show Subst where
  show (Subst m) =
    "[" ++ intercalate "," (map showBinding bindings) ++ "]"
    where showBinding (x,e) = x ++ "->" ++ show e
          bindings = filter topLevel $ M.assocs m
          topLevel (x,_) = not $ last x `elem` "0123456789"

isUpper :: Char -> Bool
isUpper c =
  c `elem` "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
isLower :: Char -> Bool
isLower c=
  c `elem` "abcdefghijklmnopqrstuvwxyz"
  
isAlpha :: Char -> Bool
isAlpha c =
  isUpper c || isLower c

isDigit :: Char -> Bool
isDigit c =
  c `elem` "0123456789"

isAlphanum :: Char -> Bool
isAlphanum c =  isAlpha c || isDigit c

symP :: ReadP Id
symP =
  do skipSpaces
     first <- satisfy (\c -> isLower c || isDigit c)
     rest <- munch isAlphanum
     lookStr <- look
     guard (lookStr == "" || not (isAlphanum (head lookStr)))
     return $ first:rest

varP :: ReadP Exp
varP =
  do skipSpaces
     first <- satisfy isUpper
     rest <- munch isAlphanum
     lookStr <- look
     guard (lookStr == "" || not (isAlphanum (head lookStr)))
     return $ Var $ first:rest

stringP :: String -> ReadP String
stringP s =
  skipSpaces >> string s

parenP :: ReadP a -> ReadP a
parenP =
  between
  (stringP "(")
  (stringP ")")

listP :: Char -> ReadP a -> ReadP [a]
listP c p =
  sepBy p (skipSpaces >> char c)
  
tupleP :: ReadP a -> ReadP [a]
tupleP =
  parenP . listP ','

symExpP :: ReadP Exp
symExpP =
  do id <- symP
     s <- look
     l <- if s /= [] && head s == '(' then tupleP expP else return []
     return $ Sym id l

expP :: ReadP Exp
expP = varP <++ symExpP

equationP :: ReadP Equation
equationP =
  do l <- expP
     stringP "="
     r <- expP
     return $ Equation l r

clauseTailP :: ReadP [Exp]
clauseTailP =
  some +++ none
  where
    some = do stringP ":-"
              assums <- listP ',' expP
              stringP "."
              return assums
    none = stringP "." >> return []

ruleP :: ReadP Rule
ruleP =
  do concl <- expP
     assums <- clauseTailP
     return $ Rule concl assums

programP :: ReadP Program
programP =
  do rules <- toEndP $ many ruleP
     return $ Program rules

goalsP :: ReadP [Exp]
goalsP =
  toEndP (listP ',' expP)

toEndP p =
  do v <- p
     skipSpaces
     eof
     return v

parseWith :: ReadP a -> String -> a
parseWith p s =
  let result = readP_to_S p s in
  if null result
  then error "unparseable input"
  else fst $ head  result

parseExp :: String -> Exp
parseExp = parseWith $ toEndP expP 

parseFile :: String -> IO Program
parseFile fname =
  do string <- readFile fname
     let toParse = unlines $ filter notComment $ lines string
           where notComment ('%':_) = False
                 notComment _ = True
     return $ parseWith programP toParse

