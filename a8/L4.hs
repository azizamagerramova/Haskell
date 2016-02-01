{- INTERPRETER FOR L4

The interpreter is broken up into three modules. This is the main one
that you can load the usual way.  However, the other two modules are
in their own files which need to be present in the same folder as this
file.

There are actually 4 different interpreters.  This module and the
syntax module stay the same, but there are four versions of L4Runtime.
This assigment uses version 2.

-}

module L4 where

import L4Syntax    -- L4 syntax and parser
import L4Runtime2  -- runtime reps of classes and objects
import Debug.Trace  


--
-- EVALUATION
--
evalProgram :: Program -> IO EVal
evalProgram (Program cs e) =
  do env <- initialEnv
     evalExp (elaborateClassDecls cs) env e

evalExp :: ClassEnv -> Env -> Exp -> IO(EVal)

evalExp cenv env (Var id) =
  readRef (applyEnv env id)

evalExp cenv env (IndexedField n) =
  applyEnvIndex cenv env n
        
evalExp cenv env TrueConst =
  return $ trueVal

evalExp cenv env FalseConst =
  return $ falseVal

evalExp cenv env (Int n) =
  return $ IntVal n
  
evalExp cenv env (PrimitiveApp p l) =
  do vs <- evalExps cenv env l
     return $ applyPrimitive p vs

evalExp cenv env (Assign x e) =
  do v <- evalExp cenv env e
     writeRef (applyEnv env x) v
     return v

evalExp cenv env (Begin [e]) =
  evalExp cenv env e
evalExp cenv env (Begin (e:es)) =
  evalExp cenv env e >> evalExp cenv env (Begin es)

evalExp cenv env (If test eTrue eFalse) =
  do b <- evalExp cenv env test
     case b of
      IntVal 1 -> evalExp cenv env eTrue
      IntVal 0 -> evalExp cenv env eFalse
      other -> error "eval If: non-boolean test value"

evalExp cenv env (Let ids es e) =
  do vs <- evalExps cenv env es
     env' <- extendEnv ids vs env
     evalExp cenv env' e 

evalExp cenv env (New c es) =
  do vs <- evalExps cenv env es
     ob <- newObject cenv c
     (body, env') <- findMethod cenv env "initialize" c ob vs
     evalExp cenv env' body
     return (ObjectVal ob)
        
evalExp cenv env (Send e m es) =
  do vs <- evalExps cenv env es
     ObjectVal ob <- evalExp cenv env e
     (body, env') <- findMethod cenv env m (objectClassName ob) ob vs
     evalExp cenv env' body
     
evalExp cenv env (Super m es) =
  do vs <- evalExps cenv env es
     let selfRef = applyEnv env "self"
         superRef = applyEnv env "%super"
     ObjectVal self <- readRef selfRef
     ObjectVal super <- readRef superRef
     (body, env') <- findMethod cenv env m (objectClassName super) self vs
     evalExp cenv env' body
  
evalExps :: ClassEnv -> Env -> [Exp] -> IO [EVal]  
evalExps cenv env [] = return []
evalExps cenv env (e:es) =
  do v <- evalExp cenv env e 
     vs <- evalExps cenv env es
     return $ v:vs

applyPrimitive :: Primitive -> [EVal] -> EVal
applyPrimitive Add [IntVal u, IntVal v] = IntVal $ u+v
applyPrimitive Subtract [IntVal u, IntVal v] = IntVal $ u-v
applyPrimitive Mult [IntVal u, IntVal v] = IntVal $ u*v
applyPrimitive Succ [IntVal u] = IntVal $ u+1
applyPrimitive Pred [IntVal u] = IntVal $ u-1
applyPrimitive Iszero [v] =
  case v of
   IntVal 0 -> trueVal
   other -> falseVal       
applyPrimitive Pair [u,v] = PairVal u v
applyPrimitive Nil [] = NilVal
applyPrimitive List l = foldr PairVal NilVal l
applyPrimitive Null [v] =
  case v of
   NilVal -> trueVal
   other -> falseVal
applyPrimitive Fst [PairVal u v] = u
applyPrimitive Snd [PairVal u v] = v
applyPrimitive _ _ = error "applyPrimitive"

run :: String -> IO (EVal)
run =
  evalProgram . parse


--
-- Examples
--

examples :: IO [Program]     
examples = parseFile "examples.txt"     

example :: Int -> IO Program
example i =
  do l <- examples
     return (l !! i)

evalExample :: Int -> IO EVal
evalExample i =
  do p <- example i
     evalProgram p

evalExamples =
  do l <- examples
     mapM_ evalPrint (zip [0 .. length l - 1] l)
       where evalPrint (i, eg) =
               do result <- evalProgram eg
                  putStrLn $ "\nExample " ++ show i ++ ":"
                  putStrLn $ show result

partsIllustration =
  "\   
  \ class c1 extends object \ 
  \   field x \
  \   field y \ 
  \   method initialize() begin x:=1; y:=17 end \ 
  \   method get1() x \ 
  \  \ 
  \ class c2 extends c1 \ 
  \   field x \ 
  \   method initialize() begin super initialize(); x:=2 end \ 
  \   method get2() x \ 
  \  \ 
  \ let o1 = new c1() \ 
  \     o2 = new c2() \ 
  \ in pair(send o2 get2(), send o2 get1()) \ 
  \ "




---------------------------------------------------------------

