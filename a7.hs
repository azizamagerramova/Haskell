{- ASSIGNMENT 7 COMP 3007 FALL 2015

DUE: Wed Nov 4 23:55

Collaboration policy, what you can use, etc, as before.

Readings: course notes, this file.



SUMMARY OF ASSIGNMENT.

In this assignment you will make some modifications to the interpreter
for L3.  The interpreter has already been modified slightly for
convenience.  In particular, the annoying need for "dummy" variables
to assign to, in order to return a value from a procedure, has been
removed.  Many of the commands have a "block" as a component, and
where a block used to have a list of commands, it now allows both
commands and expressions.  This cleans up a bunch of examples.

L3 has been updated with syntax for some new commands and expressions:
"for" loops, mutable pairs, and a "fluid let" construct.  These will
be further explained in the questions.  Your job is to write evaluator
clauses for these additions.

You should start by carefully reading *all* the supplied code *except*
for the parser.  The new L3 data type clauses have been indicated with
a comment, but a few other parts have been changed a bit for your
convenience in doing this assignment.

There are 3 equally-weighted questions.  Each question describes the
L3 addition you need to update the evaluator for.  To make sure you've
done everything, check that there are no more occurrences of
"undefined" in this file.  Test data can be found at the end of this
file.
  


QUESTION 1.  Standard "for" loops.  Example:

  r=1 n=5:
  for i=1,n by 1 do r := *(i,r) end;
  print(r)

computes n factorial for n=5.  The "by" part say how much to increment
i by each time through the loop.  The "by" can be omitted if it's 1 as
in this example.  Note: i can be assigned to in the body of the loop,
but any such value should be ignored at the start of each iteration
(see the example for1).


QUESTION 2.  "Fluid let."  This is a command of the form

  flet x = e
  in b

where e is an expression and b is a block (bindings + commands).  It
is very different from the familiar "let".  The variable x must
*already* have a binding.  The body b of the flet is evaluated in the
same environment as the flet itself, i.e. a new reference is *not*
created for x.  Right at the start of evaluation of b, x's reference
is updated to be the value of e.  Right after the evaluation of b, 
x's reference is restored to the value it had at the start.


QUESTION 3.  Mutable pairs (as in Lisp/Scheme).  These are pairs that
can have their components destructively modified.  Pairs are created
using "(,)", accessed using fst and snd, and destructively modified
using setfst and setsnd.  Example:

  t = ( (0,1), (2,3) )
  :
  print(t);
  setfst(snd(t), 4);
  print(t)

prints

  ((0, 1), (2, 3))
  ((0, 1), (4, 3))

The update for pairs to the type EVal indicates how such pairs should
be implemented.  Note that you will also need to update applyPrimitive
for fst and snd.  There is also a "null" constant added to L3 so that
pairs can be used to represent lists (null is like nil or []).

-}



import Text.ParserCombinators.ReadP
import Debug.Trace
import Data.IORef
import Control.Monad

--
-- Parsing: IGNORE until "STOP IGNORING"
-- 

primitivesSyntax =
  [(Add,      "+")
  ,(Subtract, "-")
  ,(Mult,     "*")
  ,(Succ,     "succ")
  ,(Pred,     "pred")
  ,(IsZero,   "iszero")
  ,(Less,     "<")
  ,(LessOrEq, "<=")
  ,(Eq,       "==")
  ,(And,      "and")
  ,(Or,       "or")
  ,(Not,      "not")
  ,(Fst,      "fst")
  ,(Snd,      "snd")
  ,(IsNull,   "isnull")
  ]

reservedWords =
  filter (all isAlpha) (map snd primitivesSyntax)
  ++
  ["if",
   "then",
   "else",
   "true",
   "false",
   "while",
   "do",
   "end",
   "print",
   "proc",
   "skip",
   "for",
   "flet",
   "in",
   "fst",
   "snd",
   "null"
  ]

isAlpha :: Char -> Bool
isAlpha = flip elem "abcdefghijklmnopqrstuvwxyz"

isDigit = flip elem "0123456789"

isAlphanum :: Char -> Bool
isAlphanum c =  isAlpha c || isDigit c

parenP :: ReadP a -> ReadP a
parenP =
  between
  (stringP "(")
  (stringP ")")

anyWordP :: ReadP String
anyWordP =
  do skipSpaces
     first <- satisfy isAlpha
     rest <- munch isAlpha 
     return $ first:rest

stringP :: String -> ReadP String
stringP s =
  skipSpaces >> string s

identifierP :: ReadP Id
identifierP =
  do
    skipSpaces
    first <- satisfy isAlpha
    rest <- munch isAlphanum
    if (first:rest) `elem` reservedWords
      then pfail
      else return $ first:rest

primitiveP :: ReadP Primitive
primitiveP =
  choice
  $
  map (\(op,s)-> stringP s >> return op) primitivesSyntax

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

primitiveAppP :: ReadP Exp
primitiveAppP =    
    do
      p <- primitiveP
      l <- parenP $ sepBy expP (stringP ",")
      return (PrimitiveApp p l)

procP :: ReadP Exp
procP =
  do
    stringP "proc"
    parms <- parmListP
    b <- blockP
    stringP "end"
    return $ Proc parms b
  where parmListP =
          parenP (sepBy identifierP (stringP ","))
          
appP :: ReadP Exp
appP =
    parenP
    $ do fn:args <- many1 expP
         return $ App fn args


assignP :: ReadP Cmd
assignP =
  do x <- identifierP
     stringP ":="
     e <- expP
     return $ Assign x e

ifP :: ReadP Cmd      
ifP = 
    do stringP "if"
       b <- expP
       stringP "then"
       b1 <- blockP
       stringP "else"
       b2 <- blockP
       stringP "end"
       return (If b b1 b2)

bindingP :: ReadP (Id,Exp)
bindingP =
  do
    id <- identifierP
    stringP "="
    e <- expP
    return (id,e)

bindingsP :: ReadP [(Id,Exp)]
bindingsP =
  many bindingP

cmdExpP =
  (expP >>= return . Right) +++ (cmdP >>= return . Left)

blockP :: ReadP Block
blockP =
  do bdgs <- do {bs <- bindingsP; stringP ":"; return bs}
             +++ return []
     cmdexps <- sepBy cmdExpP (stringP ";")
     let xs = map fst bdgs
         rhss = map snd bdgs
     return $ Block xs rhss cmdexps

whileP :: ReadP Cmd
whileP =
  do stringP "while"
     cond <- expP
     stringP "do"
     b <- blockP
     stringP "end"
     return $ While cond b

expP :: ReadP Exp
expP = 
  varP +++ trueP +++ falseP +++ numberP
  +++ primitiveAppP +++ procP +++ appP
  +++ nullP +++ pairP

cmdP :: ReadP Cmd  
cmdP =
  assignP +++ ifP +++ whileP +++ printP +++ skipP
  +++ forP +++ fletP +++ setfstP +++ setsndP

printP :: ReadP Cmd
printP =
  do stringP "print"
     arg <- parenP expP
     return $ Print arg

skipP :: ReadP Cmd
skipP = stringP "skip" >> return Skip

-- parsing for A7 additions

forP :: ReadP Cmd
forP =
  do stringP "for"
     id <- identifierP
     stringP "="
     start <- expP
     stringP ","
     end <- expP
     by <- (stringP "by" >> expP) +++ return (Number 1)
     stringP "do"
     b <- blockP
     stringP "end"
     return $ For id start end by b

fletP :: ReadP Cmd
fletP =
  do stringP "flet"
     id <- identifierP
     stringP "="
     e <- expP
     stringP "in"
     body <- blockP
     stringP "end"
     return $ Flet id e body

setfstP :: ReadP Cmd
setfstP =
  do stringP "setfst"
     parenP argsP
  where argsP = do e <- expP
                   stringP ","
                   e' <- expP
                   return (Setfst e e')     

setsndP :: ReadP Cmd
setsndP =
  do stringP "setsnd"
     parenP argsP
  where argsP = do e <- expP
                   stringP ","
                   e' <- expP
                   return (Setsnd e e')

nullP :: ReadP Exp
nullP =
  do stringP "null"
     return Null

pairP :: ReadP Exp
pairP =
  do parenP argsP
  where argsP = do e <- expP
                   stringP ","
                   e' <- expP
                   return (Pair e e')

programP :: ReadP Program
programP =
  do b <- blockP
     skipSpaces
     eof
     return $ Program b

parseWith :: ReadP a -> String -> a
parseWith p s =
  let result = readP_to_S p s
  in if null result
     then error "unparseable input"
     else fst $ head  result

parse :: String -> Program
parse = parseWith programP


--
-- STOP IGNORING
--


--
-- Abstract syntax and values of L3+
--


data Program = Program Block
             deriving (Show, Eq)

data Block = Block [Id] [Exp] [Either Cmd Exp]                      
           deriving (Show, Eq)
                      
data Cmd = Assign Id Exp
         | If Exp Block Block
         | While Exp Block
         | Print Exp
         | Skip
         | For Id Exp Exp Exp Block -- new for a7
         | Flet Id Exp Block        -- new for a7
         | Setfst Exp Exp           -- new for a7
         | Setsnd Exp Exp           -- new for a7
         deriving (Show, Eq)

data Exp = Var Id
         | TrueConst
         | FalseConst
         | Number Integer
         | Null                     -- new for a7
         | Pair Exp Exp             -- new for a7
         | PrimitiveApp Primitive [Exp]
         | Proc [Id] Block
         | App Exp [Exp]
         deriving (Show, Eq)
                    
data Primitive = Add
               | Subtract
               | Mult
               | Succ
               | Pred
               | IsZero
               | Less     -- less-than
               | LessOrEq -- less-than-or-equal
               | Eq       -- equal integers
               | And
               | Or
               | Not
               | Fst      -- new for a7
               | Snd      -- new for a7
               | IsNull   -- new for a7
  deriving (Show, Eq)
                          
type Id = String

-- Values of expressions.
data EVal = Int Integer
          | Bool Bool
          | ProcVal Exp Env
          | NullVal
          | PairVal DVal DVal  -- new for a7
          deriving (Show)

-- Values that can be bound to variables.  In this language, all
-- variables get bound to references to expression values.
data DVal = DVal (IORef EVal)

eValPP :: EVal ->  IO String
eValPP (Int n) = return $ show n
eValPP (Bool b) = return $ show b
eValPP NullVal = return "null"
eValPP (PairVal r r') =
  do v <- readRef r
     v' <- readRef r'
     s <- eValPP v
     s' <- eValPP v'
     return $ "(" ++ s ++ ", " ++ s' ++ ")"
eValPP _ = return $ "##"





--
-- ENVIRONMENTS
--

data Frame =  Frame [Id] [DVal]
            deriving (Show)

instance Show DVal where
  show x = "##"

data Env = EmptyEnv
         | ExtendedEnv Frame Env
           deriving (Show)

emptyEnv :: Env         
emptyEnv = EmptyEnv


extendEnv :: [Id] -> [DVal] -> Env -> Env
extendEnv ids vals = 
  ExtendedEnv (Frame ids vals)

applyEnv :: Env -> Id -> DVal
applyEnv EmptyEnv id =
  error ("applyEnv: no binding for " ++ id)
applyEnv u@(ExtendedEnv fr env) id =
  case applyFrame fr id of
    Nothing -> applyEnv env id
    Just v  -> v

applyFrame :: Frame -> Id -> Maybe DVal
applyFrame (Frame (id':ids) (v:vs)) id =
  if id'==id
  then Just v
  else applyFrame (Frame ids vs) id
applyFrame (Frame _ _) id =
  Nothing
  

--
-- EVALUATION
--

newRef :: EVal -> IO DVal
newRef v =
  liftM DVal $ newIORef v

newRefs :: [EVal] -> IO [DVal]
newRefs = mapM newRef

writeRef :: DVal -> EVal -> IO ()
writeRef (DVal r) v =
  writeIORef r v

readRef :: DVal -> IO EVal
readRef (DVal r) =
  readIORef r

evalBlock :: Env -> Block -> IO EVal
evalBlock env (Block ids rhss cmdexps) =
  do vs <- evalExps env rhss
     rs <- newRefs vs
     let env' = extendEnv ids rs env
     evalCmdExps env' cmdexps

evalProgram :: Program -> IO EVal
evalProgram (Program b) = evalBlock emptyEnv b

evalExp :: Env -> Exp -> IO(EVal)

evalExp env (Var id) =
  readRef $ applyEnv env id
        
evalExp env TrueConst =
  return $ Bool True

evalExp env FalseConst =
  return $ Bool False

evalExp env (Number n) =
  return $ Int n
  
evalExp env (PrimitiveApp p l) =
  do vs <- evalExps env l
     v <- applyPrimitive p vs
     return v 

evalExp env code@(Proc parms block) =
  return $ ProcVal code env

evalExp env (App fn args) =
  do ProcVal (Proc ps body) cenv <- evalExp env fn
     rs <- refsForArgs env ps args
     let env' = extendEnv ps rs cenv
     evalBlock env' body

evalExp env Null =
  undefined

evalExp env (Pair e e') =
  undefined
  
evalExps :: Env -> [Exp] -> IO [EVal]  
evalExps env [] = return []
evalExps env (e:es) =
  do v <- evalExp env e 
     vs <- evalExps env es
     return $ v:vs

evalCmd :: Env -> Cmd -> IO(EVal)

evalCmd env (Assign x e) =
  do v <- evalExp env e
     writeRef (applyEnv env x) v
     return v

evalCmd env (If test blockTrue blockFalse) =
  do b <- evalExp env test
     case b of
      Bool True -> evalBlock env blockTrue
      Bool False -> evalBlock env blockFalse
      other -> error "eval If: non-boolean test value"

evalCmd env (While test block) =
  while (Int 0)
  where while v =  do b <- evalExp env test
                      case b of
                       Bool True ->  do v' <- evalBlock env block
                                        while v'
                       other -> return v

evalCmd env (Print e) =
  do v <- evalExp env e
     s <- eValPP v
     putStrLn s
     return (Int 0)

evalCmd env Skip =
  return (Int 0)
  
evalCmd env (For id elo ehi eby block) =
  do
    intElo <- evalExp env elo
    eloRef <- newRef intElo
    let env2 = extendEnv [id] [eloRef] env 
    for eloRef env2 
  where for eloRef env2 = do 
                      Int l <- evalExp env2 ehi 
                      Int j <- readRef eloRef 
                      --d <- applyPrimitive LessOrEq [j,l]
                      i <- evalExp env2 eby
                      if (l>=i)
                          then do 
                            evalBlock env2 block 
                            m <- applyPrimitive Add [i,j]
                            writeRef eloRef m
                            for eloRef env2
                      else  return (Int 0)



evalCmd env (Flet id e b) =
  do 
    let a=applyEnv env id
    keepValue <- readRef a 
    expression <- evalExp env e
    writeRef a expression
    evalBlock env b 
    writeRef a keepValue
    return (Int 0)


evalCmd env (Setfst epair e) =
  undefined
  
evalCmd env (Setsnd epair e) =
  undefined
  

evalCmds :: Env -> [Cmd] -> IO EVal
evalCmds env = evalCmdExps env . map Left

evalCmdExps :: Env -> [Either Cmd Exp] -> IO EVal
evalCmdExps env cmdexps =
  ecs (Int 0) cmdexps
  where ecs v [] = return v
        ecs v ((Left c):cmdexps) = do v' <- evalCmd env c
                                      ecs v' cmdexps
        ecs v ((Right e):cmdexps) = do v' <- evalExp env e
                                       ecs v' cmdexps

refsForArgs :: Env -> [Id] -> [Exp] -> IO [DVal]
refsForArgs env [] [] = return []
refsForArgs env (x:xs) (e:es) =
  do rs <- refsForArgs env xs es
     v <- evalExp env e
     r <- newRef v       
     return (r:rs)

applyPrimitive :: Primitive -> [EVal] -> IO EVal
applyPrimitive Add [Int u, Int v] = return $ Int $ u+v
applyPrimitive Subtract [Int u, Int v] = return $ Int $ u-v
applyPrimitive Mult [Int u, Int v] = return $ Int $ u*v
applyPrimitive Succ [Int u] = return $ Int $ u+1
applyPrimitive Pred [Int u] = return $ Int $ u-1
applyPrimitive IsZero [v] =
  case v of
   Int 0 -> return $ Bool True
   other -> return $ Bool False       
applyPrimitive Less [Int u, Int v] = return $ Bool $ u<v
applyPrimitive LessOrEq [Int u, Int v] = return $ Bool $ u<=v
applyPrimitive Eq [Int u, Int v] = return $ Bool $ u==v
applyPrimitive And [Bool u, Bool v] = return $ Bool $ u&&v
applyPrimitive Or [Bool u, Bool v] = return $ Bool $ u||v
applyPrimitive Not [Bool u] = return $ Bool $ not u
applyPrimitive Fst [PairVal u v] = undefined
applyPrimitive Snd [PairVal u v] = undefined
applyPrimitive IsNull [v] = undefined
applyPrimitive _ _ = error "applyPrimitive"

run :: String -> IO ()
run s =
  do putStrLn ""
     v <- evalProgram $ parse s
     resultString <- eValPP v
     putStrLn $ "Result: " ++ resultString


--
-- Examples
--

-- > run for0
-- 120
-- Result: 0
for0 =
  " \
\ r=1 n=5: \ 
\ for i=1,n by 1 do r := *(i,r) end; \ 
\ print(r) \
\ "

-- > run for1
-- 120
-- Result: 0
for1 =
  " \
\ r=1 n=5: \ 
\ for i=1,n do r := *(i,r); i:=+(n,1) end; \ 
\ print(r) \
\ "

-- > run flet0
-- 3
-- 4
-- 3
-- Result: 0
flet0 =
  " \
\ x=0 f=0: \ 
\ f := proc(y) +(y,x) end; \ 
\ print( (f 3) ); \ 
\ flet x=1 in print ( (f 3) ) end; \ 
\ print( (f 3) ) \ 
\ "

-- > run pair0
-- 4
-- Result: 0
pair0 =
  " \ 
\ l = (1, (2, (3, (4, null)))) : \ 
\ print( fst(snd(snd(snd(l)))) ) \ 
\ "

-- > run pair1
-- ((0, 1), (2, 3))
-- ((0, 1), (4, 3))
-- Result: 0
pair1 =
  " \ 
\ t = ( (0,1), (2,3) ) \ 
\ : \ 
\ print(t); \ 
\ setfst(snd(t), 4); \ 
\ print(t) \ 
\ "

-- > run pair2
-- (1, (2, (3, (4, (5, (6, (7, null)))))))
-- Result: 0
pair2 =
  " \ 
\ l1 = (1, (2, (3, (4, null)))) \ 
\ l2 = (5, (6, (7, null))) \
\ lastpair = 0 \ 
\ : \ 
\ lastpair := proc(l) if isnull(snd(l)) \ 
\                     then l \ 
\                     else (lastpair snd(l)) \ 
\                     end \ 
\             end; \ 
\ setsnd( (lastpair l1), l2 ); \
\ print(l1) \ 
\ "


tests =
  [for0
  ,for1
  ,flet0
  ,pair0
  ,pair1
  ,pair2
  ]

test = mapM_ run tests  