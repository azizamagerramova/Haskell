--
-- L4 Runtime Version 2
--
-- The representation of objects is changed to use only a single part.
--

module L4Runtime2 ( Env, ClassEnv, EVal(..),
                    applyEnv, extendEnv, initialEnv, applyEnvIndex,
                    trueVal, falseVal,
                    readRef, writeRef,
                    newObject, objectClassName,
                    findMethod, elaborateClassDecls
                  )
       where

import L4Syntax
import Debug.Trace
import Data.Array.MArray
import Data.Array.IO
import Data.List (find, elemIndices)



--
--  Only the code from ClassEnv on changes between L4Runtime versions.
--



data EVal = IntVal Integer
          | NilVal
          | PairVal EVal EVal
          | ObjectVal Object

instance Show EVal where
  show (IntVal n) = show n
  show NilVal = "nil"
  show (PairVal u v) = "(" ++ show u ++ ", " ++ show v ++ ")"
  show (ObjectVal o) = show o

trueVal = IntVal 1
falseVal = IntVal 0
                      

data MemBlock = MemBlock (IOArray Int EVal)

instance Show MemBlock where
  show _ = "##"

data Ref = Ref MemBlock Int
type DVal = Ref

newMemBlock :: [EVal] -> IO MemBlock
newMemBlock vs =
  do array <- newListArray (0, length vs - 1) vs
     return $ MemBlock array

readRef :: Ref -> IO EVal
writeRef :: Ref -> EVal -> IO ()

readRef (Ref (MemBlock a) i) =
  readArray a i

writeRef (Ref (MemBlock a) i) v =
  writeArray a i v

--
-- ENVIRONMENTS
--

data Frame =  Frame [Id] MemBlock
            deriving (Show)

data Env = EmptyEnv
         | ExtendedEnv Frame Env
           deriving (Show)

emptyEnv :: Env         
emptyEnv = EmptyEnv

extendEnv :: [Id] -> [EVal] -> Env -> IO Env
extendEnv ids vs env =
  do mb <- newMemBlock vs
     return $ extendEnvBlock ids mb env
  
extendEnvBlock :: [Id] -> MemBlock -> Env -> Env
extendEnvBlock ids mb env = 
  ExtendedEnv (Frame ids mb) env

applyEnv :: Env -> Id -> Ref
applyEnv EmptyEnv id =
  error ("applyEnv: no binding for " ++ id)

applyEnv (ExtendedEnv fr env) id =
  case applyFrame fr id of
    Nothing -> applyEnv env id
    Just v  -> v

applyFrame :: Frame -> Id -> Maybe DVal
applyFrame (Frame ids a) id =
  if null ixs
  then Nothing
  else Just $ Ref a (last ixs)
  where ixs = elemIndices id ids
  

--
--  Only the code below changes between L4Runtime versions.
--

data ClassEnv = ClassEnv [Class]

data Class = Class { className :: Id
                   , classSuper :: Id
                   , classFields :: [Id]
                   , classMethods :: [Method]
                   }
           deriving (Show, Eq)

data Method = Method { methodName :: Id
                     , methodKind :: Kind
                     , methodParms :: [Id]
                     , methodBody :: Exp
                     }
            deriving (Show, Eq)

--writeRef :: Ref -> EVal -> IO ()
--extendEnv :: [Id] -> [EVal] -> Env -> IO Env

-- initial env for evalProgram
initialEnv :: IO Env
initialEnv =
  do 
    m<-emptyObject "%main"
    extendEnv ["%main"] [(ObjectVal (m))] EmptyEnv

-- Object c mb: c is a class name, mb is a memory block for the fields
-- in c and all its superclasses.  The layout of the fields is
-- important.  See the lecture notes for more on this.
data Object = Object Id MemBlock
            deriving Show

elaborateClassDecls :: [ClassDecl] -> ClassEnv
elaborateClassDecls =
  ClassEnv . map convertClass
  where convertClass (ClassDecl name super fields methods) =
          let methods' = map (convertMethod name super) methods
              in Class name super fields methods' 
        convertMethod cname csuper (MethodDecl mname kind parms body) =
          Method mname kind parms body

emptyObject :: Id -> IO Object
emptyObject c =
  do mb <- newMemBlock []
     return $ Object c mb

newObject :: ClassEnv -> Id -> IO Object
newObject cenv "object" =
  do mb <- newMemBlock []
     return $ Object "object" mb
newObject cenv c =
  do mb <- newMemBlock $
           map (const trueVal) (fieldIdsForInstance cenv c)
     return $ Object c mb

-- The list of fields for the given class plus all its superclasses.
-- Note: see the comment for the Object type about ordering.
fieldIdsForInstance :: ClassEnv -> Id -> [Id]
fieldIdsForInstance cenv "object" = []
fieldIdsForInstance cenv c =
  fieldIdsForInstance cenv (classSuper (findClass cenv c))
  ++ classFields (findClass cenv c)

objectClassName :: Object -> Id
objectClassName (Object c _) = c

-- (findMethod m c ob args): search for a method named m starting
-- from class c and then return the body of the method and the
-- environment to evaluate it in.
findMethod :: 
  ClassEnv -> Env -> Id -> Id -> Object -> [EVal] -> IO (Exp, Env)

findMethod cenv env "initialize" "object" self args =
  return $ (Int 0, emptyEnv)


findMethod cenv env m "object" self args =
  error "findMethod"
  
findMethod cenv env m c self args =  
  case findMethodInClass cenv m c of
    Just mdecl -> prepareMethodApp cenv env mdecl c self args
    Nothing -> findMethod cenv env m super self args
               where super = classSuper (findClass cenv c)
  
-- findClass cenv c: get the class named c.
findClass :: ClassEnv -> Id -> Class
findClass (ClassEnv cs) c = 
  case find ((c ==) . className) cs of 
    Just d -> d
    Nothing -> error $ "findClass: " ++ c

findMethodInClass :: ClassEnv -> Id -> Id -> Maybe Method
findMethodInClass cenv m c = 
  let Class _ _ _ methods = findClass cenv c in
  find ((m ==) . methodName) methods 
    
-- prepareMethodApp cenv env mDecl mClass self args: return the body
-- of the method declared by mDecl from class mClass, together with an
-- environment for all possible free variables in the body.  The
-- environment will have bindings for: the fields of mClass and its
-- superclasses; the method parameters; self; and a special variable
-- %super.  The variable "self" is for the object the method was
-- called on, and %super is an arbitrary object whose only purpose is
-- to contain the name of the superclass of mClass.
prepareMethodApp :: 
  ClassEnv -> Env -> Method -> Id -> Object -> [EVal] -> IO (Exp, Env)


prepareMethodApp
  cenv
  env
  (Method m (Private) ids body)
  mClass
  self@(Object _ mb)
  args
  = do fieldEnv <- buildFieldEnv cenv mClass self
       let sup = ObjectVal $ Object (super cenv mClass) mb
           ids' = "%super" : "self" : ids
           vs = sup : ObjectVal self : args
       bodyEnv <- extendEnv ids' vs fieldEnv
       print "Private"
       putStrLn("private method name is " ++ m ++ " class is " ++ (objectClassName self))
       case findMethodInClass cenv m (objectClassName self) of
          Just d -> return (body, bodyEnv)
          Nothing -> return (error "No access")
       

prepareMethodApp
  cenv
  env
  (Method m (Protected) ids body)
  mClass
  self@(Object _ mb)
  args
  = do fieldEnv <- buildFieldEnv cenv mClass self
       let sup = ObjectVal $ Object (super cenv mClass) mb
           ids' = "%super" : "self" : ids
           vs = sup : ObjectVal self : args
       bodyEnv <- extendEnv ids' vs fieldEnv
       case findMethodInClass cenv m (objectClassName self) of
        Just d -> return (body, bodyEnv)
        Nothing -> helper1 cenv env m body bodyEnv (objectClassName self) 
 

prepareMethodApp
  cenv
  env
  (Method m (Public) ids body)
  mClass
  self@(Object _ mb)
  args
  = do fieldEnv <- buildFieldEnv cenv mClass self
       let sup = ObjectVal $ Object (super cenv mClass) mb
           ids' = "%super" : "self" : ids
           vs = sup : ObjectVal self : args
       bodyEnv <- extendEnv ids' vs fieldEnv
       return (body, bodyEnv)

helper1 cenv env m body bodyEnv s=  
  do 
   let superRef = applyEnv env "%super"  
   ObjectVal super <- readRef superRef    
   case findMethodInClass cenv m (objectClassName super) of
     Just d ->  return (body, bodyEnv)
     Nothing -> return (error "No access")
       
-- buildFieldEnv cenv ob: an environment for all the field values in
-- the object ob.
buildFieldEnv :: ClassEnv -> Id -> Object -> IO Env
buildFieldEnv cenv c (Object _ mb) = 
  return $ extendEnvBlock (fieldIdsForInstance cenv c) mb emptyEnv

super :: ClassEnv -> Id -> Id  
super cenv c =
   classSuper $ findClass cenv c

---------------------

applyEnvIndex :: ClassEnv -> Env -> Integer -> IO(EVal)
applyEnvIndex cenv env n =
  undefined

