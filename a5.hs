{-

# Assignment 5 COMP 3007 Fall 2015

Due: 23:55 Wed Oct 14 2015

**What to submit.** Submit this Haskell file with the questions
completed.

**Collaboration policy, what you can use etc.** See assignment 4.

This file contains two versions of the evaluator for our language with
proc, application and letrec.  The "primed" version (e.g. evalexp') is
only for Question 5.  As before, you can ignore the parser.

The questions, and a bunch of examples to test your code on, are at
the end of the file.

-}


import Text.ParserCombinators.ReadP
import Debug.Trace
import Data.List(intercalate)



--
-- Syntax and values of L2.
--


data Program = Program Exp
             deriving (Show, Eq)

data Exp = Var Id
         | TrueConst
         | FalseConst
         | Number Integer
         | PrimitiveApp Primitive [Exp]
         | If Exp Exp Exp
         | Cond [(Exp,Exp)]     -- for Q2
         | Let [Id] [Exp] Exp
         | SLet [Id] [Exp] Exp  -- for Q3
         | Proc [Id] Exp
         | App Exp [Exp]
         | Letrec [Id] [[Id]] [Exp] Exp
         deriving (Eq, Show)
--       deriving (Eq)
                    
data Primitive =
  Add | Subtract | Mult | Succ | Pred | IsZero
  deriving (Show, Eq)
                          
type Id = String

data Val = Int Integer
         | Bool Bool
         | ProcVal [Id] Exp Env
         deriving (Eq, Show)

-- instance Show Exp where
--   show = concreteExp

concrete :: Program -> String
concrete (Program e) =
  concreteExp e


concreteExp :: Exp -> String

concreteExp (Var x) = x

concreteExp (TrueConst) =
  "true"

concreteExp (FalseConst) =
  "false"

concreteExp (Number n) =
  show n

concreteExp (PrimitiveApp op args) =
  case lookup op primitiveSyntax of
   Just str -> str ++ concreteArgs args
   Nothing -> error "concreteExp"

concreteExp (If eBool eTrue eFalse) =
  " if " ++ concreteExp eBool ++
  " then " ++ concreteExp eTrue ++
  " else " ++ concreteExp eFalse
  
concreteExp (Cond clauses) =
  " cond " ++
  intercalate " " (map (\(t,r)-> show t ++ "==>" ++ show r) clauses) ++
  " end" 

concreteExp (Let ids rhss body) =
  "let"
  ++
  concat (zipWith binding ids rhss)
  ++
  " in "
  ++
  concreteExp body
  where
    binding id rhs =  " " ++ id ++ "=" ++ concreteExp rhs

concreteExp (SLet ids rhss body) =
  "slet"
  ++
  concat (zipWith binding ids rhss)
  ++
  " in "
  ++
  concreteExp body
  where
    binding id rhs =  " " ++ id ++ "=" ++ concreteExp rhs

concreteExp (Proc ids body) =
  "proc " ++ concreteParms ids ++ concreteExp body

concreteExp (App fn args) =
  let argString = intercalate " " (map concreteExp args)
  in
  parens $ concreteExp fn ++ " " ++ argString

concreteExp (Letrec fns parmss bods body) =
  "letrec " ++
  concat (zipWith3 binding fns parmss bods) ++
  "in " ++
  concreteExp body
  where binding f parms bod =
          f ++ concreteParms parms ++ " = " ++ concreteExp bod ++ " "

concreteArgs es =
  parens $ commas $ map concreteExp es

concreteParms =
  concreteArgs . map Var

primitiveSyntax =
  [(Add, "+"),
   (Subtract, "-"),
   (Mult, "*"),
   (Succ, "succ"),
   (Pred, "pred"),
   (IsZero, "iszero")
  ]

parens :: String -> String
parens str =
  "(" ++ str ++ ")"

commas :: [String] -> String
commas =
  intercalate ","
  


--
-- Parsing
-- 
-- You **don't** need to read this section.  All you need to know is
-- that it defines a function parse :: String -> Program that, well,
-- parses.
--

isAlpha :: Char -> Bool
isAlpha = flip elem "abcdefghijklmnopqrstuvwxyz"

isDigit = flip elem "0123456789"

isAlphanum :: Char -> Bool
isAlphanum c =  isAlpha c || isDigit c

anyWordP :: ReadP String
anyWordP =
  do skipSpaces
     first <- satisfy isAlpha
     rest <- munch isAlpha 
     return $ first:rest

reservedWords =
  ["let"
  ,"slet"
  ,"in"
  ,"if"
  ,"then"
  ,"else"
  ,"cond"
  ,"end"
  ,"true"
  ,"false"
  ,"succ"
  ,"pred"
  ,"iszero"
  ,"proc"
  ,"letrec"
  ]

stringP :: String -> ReadP String
stringP s =
  skipSpaces >> string s

pAssert :: (a -> Bool) -> ReadP a -> ReadP a
pAssert pred parser =
  do
    res <- parser
    if pred res then return res else pfail
      
identifierP :: ReadP Id
identifierP =
  do
    w <- anyWordP
    if w `elem` reservedWords
      then pfail
      else return w

primitiveP :: ReadP Primitive
primitiveP =
  choice
  $
  map (\(op,s)-> stringP s >> return op) primitiveSyntax

varP :: ReadP Exp  
varP =
  do id <- identifierP
     return $ Var id

trueP :: ReadP Exp       
trueP =
  stringP "true" >> return TrueConst

falseP :: ReadP Exp  
falseP =
  stringP "false" >> return FalseConst
     
numberP :: ReadP Exp
numberP =
  do
    skipSpaces
    neg <- option 1 (char '-' >> return (-1))
    num <- munch1 isDigit
    return $ Number $ (*) neg $ (read num :: Integer)

parenP :: ReadP a -> ReadP a
parenP =
  between
  (stringP "(")
  (stringP ")")

-- arg is separator
expListP :: String -> ReadP [Exp]
expListP s =
  sepBy expP (stringP s)

expList1P :: String -> ReadP [Exp]
expList1P s =
  pAssert (not . null) (expListP s)

primitiveAppP :: ReadP Exp
primitiveAppP =    
    do
      p <- primitiveP
      l <- parenP $ expListP ","
      return (PrimitiveApp p l)

ifP :: ReadP Exp      
ifP = 
    do stringP "if"
       b <- expP
       stringP "then"
       e1 <- expP
       stringP "else"
       e2 <- expP
       return (If b e1 e2)

letBindingP :: ReadP (Id,Exp)
letBindingP =
  do
    id <- identifierP
    stringP "="
    e <- expP
    return (id,e)

letBindings1P :: ReadP [(Id,Exp)]
letBindings1P =
  many1 letBindingP

letP :: ReadP Exp
letP =
    do stringP "let"
       letBindings <- letBindings1P
       stringP "in"
       body <- expP
       return (Let
               (map fst letBindings)
               (map snd letBindings)
               body)

sletP :: ReadP Exp
sletP =
    do stringP "slet"
       letBindings <- letBindings1P
       stringP "in"
       body <- expP
       return (SLet
               (map fst letBindings)
               (map snd letBindings)
               body)

parmListP :: ReadP [Id]
parmListP =
  parenP (sepBy identifierP (skipSpaces >> char ','))

procP :: ReadP Exp
procP =
  do
    stringP "proc"
    args <- parmListP
    body <- expP
    return $ Proc args body
       
appP :: ReadP Exp
appP =
    parenP
    $ do fn:args <- expList1P ""
         return $ App fn args

letrecBindingP :: ReadP (Id, [Id], Exp)
letrecBindingP =
  do
    id <- identifierP
    parms <- parmListP
    stringP "="
    body <- expP
    return (id, parms, body)

letrecBindings1P :: ReadP [ (Id, [Id], Exp) ]
letrecBindings1P =
  many1 letrecBindingP

letrecP :: ReadP Exp
letrecP =
  do
    stringP "letrec"
    bs <- letrecBindings1P
    stringP "in"
    body <- expP
    return $ Letrec (map one bs) (map two bs) (map three bs) body
  where one (x,y,z) = x
        two (x,y,z) = y
        three (x,y,z) = z

clauseP :: ReadP (Exp, Exp)
clauseP =
  do
    test <- expP
    stringP "==>"
    result <- expP
    return (test, result)

clauses1P :: ReadP [ (Exp, Exp) ]
clauses1P =
  many1 clauseP

condP :: ReadP Exp
condP =
  do
    stringP "cond"
    clauses <- clauses1P
    stringP "end"
    return $ Cond clauses
    
expP :: ReadP Exp
expP = 
  varP +++ trueP +++ falseP +++ numberP  +++ primitiveAppP
  +++ ifP +++ condP +++ letP +++ sletP +++ procP 
  +++ appP +++ letrecP

programP :: ReadP Program
programP =
  expP >>= (return . Program)

parseWith :: ReadP a -> String -> a
parseWith p s =
  let result = readP_to_S p s in
  if null result
  then error "unparseable input"
  else fst $ head  result

parse :: String -> Program
parse = parseWith programP


--
-- Environments
--

data Frame =  Frame [Id] [Val]
            deriving (Show, Eq)

data Env = EmptyEnv
         | ExtendedEnv Frame Env
         | RecExtendedEnv Frame Env
           deriving (Show, Eq)

-- instance Show Frame where
--   show (Frame ids _) = "{" ++ show ids ++ "/[...]}"

emptyEnv :: Env         

emptyEnv = EmptyEnv


extendEnv :: [Id] -> [Val] -> Env -> Env

extendEnv ids vals = 
  ExtendedEnv (Frame ids vals)

extendEnvRec :: [Id] -> [Val] -> Env -> Env
extendEnvRec ids vals env =
  RecExtendedEnv (Frame ids vals) env

applyEnv :: Env -> Id -> Val

applyEnv EmptyEnv id =
  error ("applyEnv: no binding for " ++ id)

applyEnv (ExtendedEnv fr env) id =
  case applyFrame fr id of
    Nothing -> applyEnv env id
    Just v  -> v

applyEnv (RecExtendedEnv fr env) id =
  case applyFrame fr id of
    Nothing
      -> applyEnv env id
    Just (ProcVal parms body closureEnv)
      -> ProcVal parms body (RecExtendedEnv fr env)

applyFrame :: Frame -> Id -> Maybe Val

applyFrame (Frame (id':ids) (v:vs)) id =
  if id'==id
  then Just v
  else applyFrame (Frame ids vs) id

applyFrame (Frame _ _) id =
  Nothing




--
-- Evaluation
--
                    
evalProgram :: Program -> Val
evalProgram (Program e) = evalExp emptyEnv e

evalExp :: Env -> Exp -> Val

evalExp env (Var id) =
  applyEnv env id
        
evalExp env TrueConst =
  Bool True

evalExp env FalseConst =
  Bool False

evalExp env (Number n) =
  Int n
  
evalExp env (PrimitiveApp p l) =
  applyPrimitive p (evalExps env l)
  
evalExp env (If b eTrue eFalse) =
  if evalExp env b == Bool True 
     then evalExp env eTrue
     else evalExp env eFalse


evalExp env (Cond []) = Int 0

evalExp env (Cond ((d, f) : ls)) = 
      if (evalExp env d== Bool True )
          then evalExp env f
          else evalExp env (Cond ls)


evalExp env (Let ids rhss body) =
  evalExp
  (extendEnv ids (evalExps env rhss) env)
  body

evalExp env (SLet [] [] e) = evalExp env e 
evalExp env (SLet (x:xs) (y:ys) e) | (length (x:xs) == 0 && length (y:ys)==0) =  evalExp env e
                                   | otherwise = evalExp (extendEnv [x] (evalExps env [y]) env ) (SLet xs ys e)

evalExp env (Proc ids body) =
  ProcVal ids body env

evalExp env (App fn args) = traceShow (boundIds (env))  $
  let ProcVal ids body closureEnv =  evalExp env fn
      argVals = evalExps env args 
  in
  evalExp (extendEnv ids argVals closureEnv) body
  

evalExp env (Letrec fns parmss rhss body) =
  evalExp
  (extendEnvRec fns (zipWith3 ProcVal parmss rhss (repeat emptyEnv)) env)
  body 

  
evalExps :: Env -> [Exp] -> [Val]  
evalExps env [] = []
evalExps env (e:es) =
  evalExp env e : evalExps env es

applyPrimitive :: Primitive -> [Val] -> Val
applyPrimitive Add [Int u, Int v] = Int $ u+v
applyPrimitive Subtract [Int u, Int v] = Int $ u-v
applyPrimitive Mult [Int u, Int v] = Int $ u*v
applyPrimitive Succ [Int u] = Int $ u+1
applyPrimitive Pred [Int u] = Int $ u-1
applyPrimitive IsZero [v] =
  if v == Int 0 then Bool True else Bool False
applyPrimitive _ _ = error "applyPrimitive"

run :: String -> Val
run = evalProgram . parse


--
-- Evaluation'
--
                    

evalProgram' :: Program -> Val
evalProgram' (Program e) = evalExp' emptyEnv e

evalExp' :: Env -> Exp -> Val

evalExp' env (Var id) =
  applyEnv env id
        
evalExp' env TrueConst =
  Bool True

evalExp' env FalseConst =
  Bool False

evalExp' env (Number n) =
  Int n
  
evalExp' env (PrimitiveApp p l) =
  applyPrimitive p (evalExps' env l)
  
evalExp' env (If b eTrue eFalse) =
  if evalExp' env b == Bool True 
     then evalExp' env eTrue
     else evalExp' env eFalse

-- Don't bother.
evalExp' env (Cond _) = undefined

evalExp' env (Let ids rhss body) =
  evalExp'
  (extendEnv ids (evalExps' env rhss) env)
  body

-- Don't bother
evalExp' env (SLet _ _ _) = undefined

evalExp' env (Proc ids body) =
  ProcVal ids body env

evalExp' env (App fn args) =
  let ProcVal ids body closureEnv =  evalExp' env fn
      argVals = evalExps' env args 
  in
  evalExp' (extendEnv ids argVals env) body -- ***

evalExp' env (Letrec fns parmss rhss body) =
  evalExp'
  (extendEnvRec fns (zipWith3 ProcVal parmss rhss (repeat emptyEnv)) env)
  body 

  
evalExps' :: Env -> [Exp] -> [Val]  
evalExps' env [] = []
evalExps' env (e:es) =
  evalExp' env e : evalExps' env es


run' :: String -> Val
run' = evalProgram' . parse


-- ---------------------------------------------------------------------


-- QUESTION 1
--
-- Define a function that takes an environment and an identifier, and
-- indicates whether or not the identifier has a value associated with
-- it in the environment.  In other words, (hasBinding env id) should
-- return False exactly if applyEnv env id raises an error.
--

hasBinding :: Env -> Id -> Bool

hasBinding EmptyEnv id = False

hasBinding (ExtendedEnv fr env) id =       
  case applyFrame fr id of 
    Nothing -> hasBinding env id 
    Just q -> True
                
hasBinding (RecExtendedEnv fr env) id = 
        case  applyFrame fr id of 
          Nothing -> hasBinding env id
          Just q-> True 

  


-- QUESTION 2
--
-- The Exp datatype (and parser) includes a "cond" constructor, which
-- is a generalized if-then-else ("cond" for "conditional").  E.g. the
-- language expression
--    cond iszero(x) ==> +(x,1)
--         iszero(pred(x)) ==> 2
--         iszero(pred(pred(x) ==> 3
--         true ==> 4
--    end
-- has 4 clauses, each of which is a test followed by an expression
-- to evaluate in the case the test evaluates to True.
--
-- To evaluate a "cond", evaluate the tests in order, and when one is
-- found whose value is not zero, return the value of the
-- corresponding result expression.  If no true test is found, return
-- 0 for the value of the cond expression.

-- In the above example, if x is bound to 2, the first 2 tests are
-- false and the third is true, so the result of the whole cond
-- expression is 3.  Modify the interpreter to handle this new
-- language feature; you'll need to modify the definition of evalExp
-- above.  Ignore evalExp'.



-- Question 3
--
-- Write a function boundIds that gives a list of all ids bound in the
-- environment.  Use this function and traceShow (imported from
-- Debug.Trace) to print out a new line of currently-bound ids each
-- time a function is called.  Primitive operations don't count: only
-- modify the evalExp clause for App.  See the examples section for
-- more.

boundIds :: Env -> [Id]
boundIds (EmptyEnv)  = []
boundIds (ExtendedEnv (Frame ls a) env) =   ls ++ boundIds env
boundIds (RecExtendedEnv (Frame ls a) env) = ls ++ boundIds env

-- Question 4
--
-- The Exp datatype (and parser) includes an "slet" constructor that
-- is syntactically identical to "let" except for using the keyword
-- "slet".  The difference is in how the let bindings are evaluated.
-- The regular "let" is *parallel* binding: the right-hand sides are
-- all evaluated in the same environment.  The "slet" is sequential:
-- each let binding clause is processed in turn, and the binding it
-- creates is added to the environment for evaluating the next
-- binding.

-- For example, "let x=3 y=+(x,1) in y" is an error since +(x,1) is
-- evaluated in the empty environment; "slet x=3 y=+(x,1) in y"
-- evaluates to 4.
--
-- Complete the evalExp clause(s) for SLet above.



-- Question 5
--
-- The "primed" version of the evaluator (run', evalExp' etc) is
-- identical to the regular evaluator except for line with "***"
-- beside it: here evalExp' uses env instead of closureEnv.  Give an
-- example where run and run' produce different results.

-- run q5Eg /= run' q5Eg
q5Eg :: String
q5Eg = q3eg



--
-- Examples / Test Data

-- Q1

bogusFrame idSentence =
  Frame ids (map (const $ Int 0) ids) where ids = words idSentence 

envExample =
  foldr ExtendedEnv EmptyEnv
  $ map bogusFrame  ["x y z", "u v", "s u x v", "a b c"]

 
-- Should be true.  
q1Test =
  map (hasBinding envExample) (words "x u g a i")
  ==
  [True, True, False, True, False]


-- Q2

condeg0 =
  "let x = 2 in \
  \cond iszero(x) ==> +(x,1) \
  \     iszero(pred(x)) ==> 2 \
  \     iszero(pred(pred(x))) ==> 3 \
  \     true ==> 4 \
  \end"

condeg1 =
  "let g = proc(x) cond iszero(x) ==> 0 true ==> 1 end in (g (g 3))"

condeg3 = 
  "let g = proc(x) cond iszero(x) ==> 0 end in (g (g 3))"

condeg2 =
  "let g = proc(x) cond iszero(x) ==> 0 false ==> 1 end in (g (g 3))"

-- Should be true.
q2Test =
  map run [condeg0, condeg1, condeg2]
  ==
  [Int 3, Int 1, Int 0]


-- Q3

q3eg =
  " let f=proc(x) +(x,3) in \
  \ let g = proc(h,y) succ((h (f y))) in \
  \ let fact = \
  \   letrec f(n) = if iszero(n) then 1 else *(n,(f pred(n))) \
  \   in f \
  \ in \
  \ (g fact 17)"

-- Output should be something like:

-- ["fact","g","f"]
-- ["h","y","f"]
-- ["h","y","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- ["n","f","g","f"]
-- Int 2432902008176640001


-- Q4

slet0 = "slet x=3 y=+(x,1) in y"
slet1 = "let x=3 y=4 in slet z=2 f=proc() +(x,z) in (f)"
slet2 = "let x=2 y=4 in slet x=succ(x) u=x z=y in +(x,+(u,z))"

-- should be true
q4Test =
  map run [slet0, slet1, slet2]
  ==
  [Int 4, Int 5, Int 10]


-- Miscellaneous examples just to illustrate the language.

eg0 = "+(2,3)"
eg1 = "+(+(2,3), 4)"
eg2 = "let x=17 y=2 in *(x,y)"
eg3 = "let x=0 y=1 in let x=2 in x"
eg4 = "let x=-(3,3) in if iszero(x) then 17 elsse x"
eg5 = "let x=0 in +(let y=2 z=3 in +(y,z), x)"
eg6 = "let x=1 in let f = proc (y) +(x,y) in let x=2 in (f 17)"

eg7 =
  "letrec even(x) = if iszero(x) then true else (odd pred(x)) \
         \odd(x)  = if iszero(x) then false else (even pred(x)) \
  \in (odd 12)"

eg8 =
  "let x=1 in \
  \let g = proc (m) succ(m) in \
  \letrec f(n) = if iszero(n) then x else (g (f pred(n))) in \
  \(f 1)"


-- evaluates to true
miscTest =
  map run [eg0, eg1, eg2, eg3, eg4, eg5, eg6, eg7, eg8]
  ==
  [Int 5,Int 9,Int 34,Int 2,Int 17,Int 5,Int 18,Bool False,Int 2]