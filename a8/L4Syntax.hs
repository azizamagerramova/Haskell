{-

This module is the base file of the interpreter.  It has the abstract
syntax datatypes and the parser.

-}

-- The part in parentheses specifies what's exported to importers of
-- this module.  The "(..)" means to export all the constructors in
-- the named data type.
module L4Syntax ( ClassDecl(..), MethodDecl(..), Kind(..),
                  Program(..), Exp(..), Primitive(..), Id,
                  parse, parseFile
                )
       where

import Text.ParserCombinators.ReadP
import Debug.Trace

--
-- Abstract syntax and values of L3
--

data Program = Program [ClassDecl] Exp
           deriving (Show, Eq)

-- Here we use a special feature of single-constructor data types that
-- lets us have accessors defined automatically.
data ClassDecl = ClassDecl { classDeclName :: Id
                           , classDeclSuper :: Id
                           , classDeclFields :: [Id]
                           , classDeclMethods :: [MethodDecl]
                           }
                 deriving (Show, Eq)
                          
data MethodDecl = MethodDecl { methodDeclName :: Id
                             , methodDeclKind :: Kind
                             , methodDeclParms :: [Id]
                             , methodDeclBody :: Exp
                             }
                  deriving (Show, Eq)

data Kind = Public | Protected | Private
          deriving (Show, Eq)
                           
data Exp = Var Id
         | IndexedField Integer   -- for a8 extra credit question
         | TrueConst
         | FalseConst
         | Int Integer
         | PrimitiveApp Primitive [Exp]
         | Assign Id Exp
         | Begin [Exp]
         | If Exp Exp Exp
         | Let [Id] [Exp] Exp
         | New Id [Exp]
         | Send Exp Id [Exp]
         | Super Id [Exp]
           deriving (Show, Eq)
                                        
data Primitive = Add
               | Subtract
               | Mult
               | Succ
               | Pred
               | Iszero
               | Pair
               | Nil
               | List
               | Null
               | Fst
               | Snd
               deriving (Show, Eq)
                          
type Id = String  

--
-- Parsing
-- 
-- You **don't** need to read this section.  All you need to know is
-- that it defines a function parse :: String -> Program that, well,
-- parses.  WARNING: if you do read this section, have some tissues
-- handy: there's a danger of having tears well up in your eyes
-- because of the beauty of the monadic parsing combinators.
--

primitivesSyntax =
  [(Add,      "+")
  ,(Subtract, "-")
  ,(Mult,     "*")
  ,(Succ,     "succ")
  ,(Pred,     "pred")
  ,(Iszero,   "iszero")
  ,(Pair,     "pair")
  ,(Nil,      "nil")
  ,(List,     "list")
  ,(Null,     "null")
  ,(Fst,      "fst")
  ,(Snd,      "snd")               
  ]

reservedWords =
  filter (all isAlpha) (map snd primitivesSyntax)
  ++
  ["if"
  ,"then"
  ,"else"
  ,"true"
  ,"false"
  ,"begin"
  ,"end"
  ,"let"
  ,"class"
  ,"method"
  ,"field"
  ,"new"
  ,"send"
  ,"super"
  ]

isAlpha :: Char -> Bool
isAlpha = flip elem alphabet
  where alphabet =
          "_abcdefghijklmnopqrstuvwxyz" ++
          "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

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

idP :: ReadP Id
idP =
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
  do id <- idP
     return $ Var id

indexedFieldP :: ReadP Exp
indexedFieldP =
  do stringP "["
     n <- munch isDigit
     stringP "]"
     return $ IndexedField $ (read n :: Integer)

trueP :: ReadP Exp       
trueP =
  stringP "true" >> return TrueConst

falseP :: ReadP Exp  
falseP =
  stringP "false" >> return FalseConst
     
intP :: ReadP Exp
intP =
  do
    skipSpaces
    neg <- option 1 (char '-' >> return (-1))
    num <- munch1 isDigit
    return $ Int $ (*) neg $ (read num :: Integer)

primitiveAppP :: ReadP Exp
primitiveAppP =    
    do
      p <- primitiveP
      l <- parenP $ sepBy expP (stringP ",")
      return (PrimitiveApp p l)

listP :: Char -> ReadP a -> ReadP [a]
listP c p =
  sepBy p (skipSpaces >> char c)
  
tupleP :: ReadP a -> ReadP [a]
tupleP =
  parenP . listP ','

assignP :: ReadP Exp
assignP =
  do x <- idP
     stringP ":="
     e <- expP
     return $ Assign x e

ifP :: ReadP Exp      
ifP = 
    do stringP "if"
       b <- expP
       stringP "then"
       eTrue <- expP
       stringP "else"
       eFalse <- expP
       return (If b eTrue eFalse)

bindingP :: ReadP (Id,Exp)
bindingP =
  do
    id <- idP
    stringP "="
    e <- expP
    return (id,e)

letP :: ReadP Exp
letP =
  do stringP "let"
     bs <- many1 bindingP
     stringP "in"
     body <- expP
     return $ Let (map fst bs) (map snd bs) body

beginP :: ReadP Exp
beginP =
    do stringP "begin"
       es <- listP ';' expP
       stringP "end"
       return (Begin es)

newP :: ReadP Exp
newP =        
  do stringP "new"
     methodName <- idP
     args <- tupleP expP
     return $ New methodName args

sendP :: ReadP Exp
sendP =      
  do stringP "send"
     ob <- expP
     methodName <- idP
     args <- tupleP expP
     return $ Send ob methodName args

superP :: ReadP Exp
superP =
  do stringP "super"
     methodName <- idP
     args <- tupleP expP
     return $ Super methodName args

methodDeclP :: ReadP MethodDecl
methodDeclP =
  do kind <- (stringP "public" >> return Public)
             +++ (stringP "protected" >> return Protected)
             +++ (stringP "private" >> return Private)
             +++ return Public
     stringP "method"
     name <- idP
     ids <- tupleP idP
     body <- expP
     return (MethodDecl name kind ids body)

fieldP :: ReadP Id
fieldP =
  stringP "field" >> idP

classDeclP :: ReadP ClassDecl
classDeclP =
  do stringP "class"
     name <- idP
     stringP "extends"
     super <- idP
     fields <- many fieldP
     methods <- many methodDeclP
     return (ClassDecl name super fields methods)

expP :: ReadP Exp
expP =
  foldr1 (+++)
  [varP
  ,indexedFieldP
  ,trueP
  ,falseP
  ,intP
  ,primitiveAppP
  ,assignP
  ,beginP
  ,ifP
  ,letP
  ,newP
  ,sendP
  ,superP
  ]

toEndP :: ReadP a -> ReadP a
toEndP p =
  do v <- p
     skipSpaces
     eof
     return v

programP :: ReadP Program
programP = 
  do cs <- many classDeclP
     e <- expP
     return $ Program cs e

programsP :: ReadP [Program]
programsP =
  toEndP $ many programP

parseWith :: ReadP a -> String -> a
parseWith p s =
  let result = readP_to_S p s
  in if null result
     then error "unparseable input"
     else fst $ head  result

parseFile :: String -> IO [Program]
parseFile fname =
  do string <- readFile fname
     let toParse = unlines $ filter notComment $ lines string
           where notComment ('%':_) = False
                 notComment _ = True
     return $ parseWith programsP toParse

parse :: String -> Program
parse = parseWith $ toEndP programP 

