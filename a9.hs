{- Assignment 9.

OPTIONAL ASSIGNMENT. This whole assignment is optional.  It will
either count for you or be replaced by your average on the other
assignments, whichever helps your final grade the most.

Before attempting this assignment you should carefully go over the
class notes related to type judgments, and understand the typechecker
from those lectures, its relationship to the type-judgment account of
type checking, and its use of the Maybe monad.  Learn You a Haskell
has some useful explanations of the Maybe monad.

This assignment, in addition to giving you experience with
typecheckers and further uses of abstraction in Haskell, will also
give a "hands-on" introduction to formal proofs, which will be useful
when we move on to logic programming (the pure kind, not the dark side
ruled by Prolog).

Your job is simply to fill in for the "undefined" parts.  In the end,
"finalTest" should evaluate to True.

Most of the work will be understanding the notion of proof presented
here.  The code itself gives a precise and concise account of proofs.
Some comments are provided as well.  Proofs are defined as tree-like
data structures that additionally satisfy a "well-formedness"
property.  This is completely specified in the code.

There is also a function that takes an expression, computes a type for
it, and builds a proof that the expression has that type.  This
function is where the "undefined"'s occur.  Some clauses are
completely defined, and these should give you a guide for how to
complete the other ones.

There is also a pretty-printer to generate a readable form of proofs.

The total amount of code you need to write is under 20 lines.

-}

import Debug.Trace
import A9Syntax
import Control.Monad
import Data.List(intercalate)

-- Type declarations/assumptions, used in type judgments.
data Decl = Decl { declId :: Id
                 , declTy :: Ty
                 }
          deriving (Eq, Show)

-- Type environments.
type TEnv = [Decl]

-- Type judgments
-- (J tenv e ty) says that e should have type ty assuming the variable
-- declarations in tenv.
data J = J { jTEnv :: TEnv
           , jExp :: Exp
           , jTy :: Ty
           }
       deriving (Show, Eq)

-- Typing rule names
data Rule = VarR
          | IntR
          | TrueR
          | FalseR
          | PairR
          | FstR
          | SndR
          | PrimitiveAppR
          | IfR 
          | LetR 
          | ProcR
          | AppR 
          | NoneR -- fake rule for incomplete proofs
          deriving (Show, Eq)

-- Proofs of type judgments
-- (Proof j r subproofs) is a derivation of j from the roots of
-- subproofs using the rule named r
data Proof = Proof { proofRoot :: J
                   , proofRule :: Rule
                   , proofSubproofs :: [Proof]
                   }
           deriving Show


-- Type environments

emptyTEnv :: TEnv
emptyTEnv = []

applyTEnv :: TEnv -> Id -> Maybe Ty
applyTEnv [] id = Nothing
applyTEnv (Decl x ty : ds) y =
  case applyTEnv ds y of
   Nothing | x==y -> Just ty
   Nothing -> Nothing
   other -> other

extendTEnv :: TEnv -> Id -> Ty -> TEnv
extendTEnv tenv x ty =
  tenv ++ [Decl x ty]


-- Pretty printing of proofs etc.  The Pretty class is defined in
-- the A9Syntax module.

instance Pretty Decl where
  pretty (Decl x ty) = x ++ ":" ++ pretty ty

instance Pretty J where
  pretty (J ds e ty) =
    intercalate "," (map pretty ds)
    ++ " |- "
    ++ pretty e ++ ":" ++ pretty ty

-- for "top-level" proofs only
instance Pretty Proof where
  pretty pf = p 0 pf where
    p n (Proof j r subproofs) =
      take (2*n) (repeat ' ')
      ++ pretty j
      ++ " BY " ++ show r ++ (if null subproofs then "" else "\n")
      ++ intercalate "\n" (map (p $ n+1) subproofs)

-- output a readable rendering of a proof
displayProof :: Proof -> IO()
displayProof = putStr . pretty


-- Proof well-formedness.
--
-- Each node of the proof tree must be a valid instance of a typing
-- rule.  The typing rules, defined by ruleInstance, assume an empty
-- environment.  For example, in the rule
--
--    tenv |- ea : tya    tenv |- eb : tyb
--    ------------------------------------
--         tenv |- (ea,eb) : (tya, tyb)
--
-- all the judgments share the same type environment.  Other rules are
-- similar in that all but one declaration perhaps are the same in the
-- type environments.  Instead of cluttering the individual rules with
-- type environments, the common part is omitted and handled
-- once-and-for-all by wellFormed.  The above rule (see ruleInstance)
-- becomes:
--
--        |- ea : tya    |- eb : tyb
--    ------------------------------------
--          |- (ea,eb) : (tya, tyb)
--
-- and wellFormed generalizes it to the first version above.
--

wellFormed :: Proof -> Bool

wellFormed (Proof j VarR subproofs) =
  case j of
   J tenv (Var x) ty ->
     applyTEnv tenv x == Just ty
     && null subproofs
   other -> False

-- remove the common part of the type environments before calling
-- ruleInstance.
wellFormed (Proof j r subproofs) =
  all wellFormed subproofs && ruleInstance r js' j'
  where js = map proofRoot subproofs
        j' = replaceEnv j
        js' = map replaceEnv js
        replaceEnv (J tenv e ty) = J (chop tenv) e ty
        chop ds = drop n ds
        n = length . commonPrefix $ map jTEnv (j:js)

commonPrefix :: [TEnv] -> TEnv

commonPrefix [] = error "commonPrefix"
commonPrefix tenvs | any null tenvs = []
commonPrefix tenvs
  | allEqual (map head tenvs)
  = head (head tenvs) : commonPrefix (map tail tenvs)
commonPrefix tenvs = []    

allEqual :: Eq a => [a] -> Bool
allequal [] = True
allEqual (x:xs) = all (x==) xs


-- (ruleInstance r js j) is true if the type judgment j follows from
-- js according to the rule named r.  The equations below can be taken
-- as a definition of the rules.
--
-- There is some clutter in these equations because Haskell requires
-- "linear patterns".  For example, in the rule FstR for typing
-- applications of the "fst" operation, what we'd really like to write
-- is the following.
--
-- ruleInstance
--   FstR
--   [J [] e (PairTy tya tyb)]
--   (J [] (Fst e) tya)
--   = True
--
-- Note that some pattern variables (e and tya) are repeated: what we
-- mean is that the two different matches for e should be equal, and
-- similarly for tya.  This is not allowed in Haskell, so we have to
-- use different names for the different occurrences, then require
-- them to be equal in a guard.  This gives the following.
--
-- ruleInstance
--   FstR
--   [J [] e' (PairTy tya' tyb)]
--   (J [] (Fst e) tya)
--   | e == e' && tya == tya'
--   = True
--
-- To help with reading these, ignore the primes and the guard.
--

ruleInstance :: Rule -> [J] -> J -> Bool

ruleInstance
  IntR
  []
  (J [] (Int n) IntTy)
  = True

ruleInstance
  TrueR
  []
  (J [] TrueConst BoolTy)
  = True

ruleInstance
  FalseR
  []
  (J [] FalseConst BoolTy)
  = True

ruleInstance
  PairR
  [J [] ea' tya'
  ,J [] eb' tyb'
  ]
  (J [] (Pair ea eb) (PairTy tya tyb))
  | ea == ea' && eb == eb' && tya == tya' && tyb == tyb'
  = True

ruleInstance
  FstR
  [J [] e' (PairTy tya' tyb)]
  (J [] (Fst e) tya)
  |  e == e' && tya == tya'
  = True

ruleInstance
  SndR
  [J [] e' (PairTy tya tyb')]
  (J [] (Snd e) tyb)
  |  e == e' && tyb == tyb'
  = True

ruleInstance
  PrimitiveAppR
  js
  (J [] (PrimitiveApp p args) ty)
  | ty == resultTy && js == js'
  = True
  where FunTy argTys resultTy = primitiveTy p
        js' = zipWith (J []) args argTys

ruleInstance    
  IfR
  [J [] e' BoolTy
  ,J [] et' ty'
  ,J [] ef' ty''
  ]
  (J [] (If e et ef) ty)
  | e == e' && et == et' && ef == ef' && ty == ty' && ty' == ty''
  = True

ruleInstance
  LetR
  [J [] e' tye,
   J [Decl x' tye'] b' ty'
  ]
  (J [] (Let x e b) ty)
  | x == x' && e == e' && b == b' && ty == ty' && tye == tye'
  = True

ruleInstance
  ProcR
  [J [Decl x' tya''] b' tyb'
  ]
  (J [] (Proc tya' x b) (FunTy [tya] tyb))
  | x == x' && b == b' && tya == tya' && tya' == tya'' && tyb == tyb'
  = True

ruleInstance
  AppR
  [J [] f' (FunTy [tya'] tyb')
  ,J [] arg' tya
  ]
  (J [] (App f arg) tyb)
  | f == f' && tya == tya' && arg == arg'
  = True
   
ruleInstance
  NoneR
  []
  _
  = True

ruleInstance _ _ _ = False                   



-- (elseNoneR j mpf): as a default use a degenerate proof with the
-- NoneR rule
elseNoneR :: J -> Maybe Proof -> Proof
elseNoneR j (Just p) = p
elseNoneR j Nothing = Proof j NoneR []

-- Use checkExp to get the type for the given expression, then prove
-- that the expression has this type.
proveTopLevel :: Exp -> Proof
proveTopLevel e =
  case checkExp emptyTEnv e of
   Just ty -> prove $ J emptyTEnv e ty
   Nothing -> error "proveTopLevel: no starting type"


-- Prove type judgments.
-- (prove j) = a proof of the type judgment j

prove :: J -> Proof

prove j@(J tenv (Var x) ty) =
  elseNoneR j $
  do ty <- applyTEnv tenv x
     return $ Proof j VarR []
     
prove j@(J tenv (Int n) ty) =
  elseNoneR j $
  do guard $ ty == IntTy
     return $ Proof j IntR []

prove j@(J tenv TrueConst ty) =
  elseNoneR j $
  do guard $ ty == BoolTy
     return $ Proof j TrueR []

prove j@(J tenv FalseConst ty) =
  elseNoneR j $
  do guard $ ty == BoolTy
     return $ Proof j FalseR []

prove j@(J tenv (Pair ea eb) ty) =
  elseNoneR j $
  do PairTy tya tyb <- return ty  -- see note 1 at end of file
     return $ Proof j PairR [prove (J tenv ea tya), prove (J tenv eb tyb)]
     
prove j@(J tenv (Fst e) ty) =
  elseNoneR j $
  do pairTy@(PairTy tya tyb) <- checkExp tenv e
     guard $ tya == ty
     let subproof = prove $ J tenv e pairTy
     return $ Proof j FstR [subproof]

prove j@(J tenv (Snd e) ty) =
  elseNoneR j $
  do pairTy@(PairTy tya tyb) <- checkExp tenv e
     guard $ tyb == ty
     let subproof = prove $ J tenv e pairTy
     return $ Proof j SndR [subproof]

prove j@(J tenv (PrimitiveApp p es) ty) =
  elseNoneR j $
  do let FunTy argTys resTy = primitiveTy p
     guard $ length argTys == length es
     let subproofs = map prove $ zipWith (J tenv) es argTys
     return $ Proof j PrimitiveAppR subproofs

prove j@(J tenv (If e et ef) ty) =
  elseNoneR j $
  do pairTy@(PairTy tya tyb) <- checkExp tenv e
     guard $ tya == ty
     let subproof = prove $ J tenv e pairTy
     return $ Proof j SndR [subproof] 



prove j@(J tenv (Let x e b) ty) =
  elseNoneR j $
  do eTy <- checkExp tenv e
     let ePf = prove $ J tenv e eTy
         tenv' = extendTEnv tenv x eTy
         bPf = prove $ J tenv' b ty
     return $ Proof j LetR [ePf, bPf]

prove j@(J tenv (Proc xTy x b) ty) =
  elseNoneR j $
  do eTy <- checkExp tenv b 
     let  tenv' = extendTEnv tenv x eTy
          bPf = prove $ J tenv' b ty
     return $ Proof j LetR [bPf]
  
prove j@(J tenv (App f arg) ty) =
  elseNoneR j $
  do PairTy tya tyb <- return ty  -- see note 1 at end of file
     return $ Proof j PairR [prove (J tenv f tya), prove (J tenv arg tyb)]



--
-- Typechecking
--
-- (check e) = Just ty if e has ty in the empty type environment
-- (check e) = Nothing  if e does not typecheck
--

check :: Exp -> Maybe Ty
checkExp :: TEnv -> Exp -> Maybe Ty
checkExps :: TEnv -> [Exp] -> Maybe [Ty]

check = checkExp emptyTEnv

checkExp tenv (Var id) =
  applyTEnv tenv id
  
checkExp tenv (Int n) =
  return IntTy
  
checkExp tenv TrueConst =
  return BoolTy
  
checkExp tenv FalseConst =
  return BoolTy
  
checkExp tenv (Pair e e') =
  do t1 <- checkExp tenv e
     t2 <- checkExp tenv e'
     return $ PairTy t1 t2
  
checkExp tenv (Fst e) =
  do PairTy ty _ <- checkExp tenv e
     return ty

checkExp tenv (Snd e) =
  do PairTy _ ty <- checkExp tenv e
     return ty
  
checkExp tenv (PrimitiveApp prim args) =
  do FunTy expectedArgTys ty' <- return (primitiveTy prim)
     argTys <- checkExps tenv args
     guard $ argTys == expectedArgTys
     return ty'
  
checkExp tenv (If test t f) =
  do testTy <- checkExp tenv test
     tTy <- checkExp tenv t
     fTy <- checkExp tenv f
     guard $ testTy == BoolTy && tTy == fTy
     return tTy
  
checkExp tenv (Let id e e') =
  do ty <- checkExp tenv e
     checkExp (extendTEnv tenv id ty) e'
     
checkExp tenv (Proc ty id e) =
  do resultTy <- checkExp (extendTEnv tenv id ty) e
     return $ FunTy [ty] resultTy

checkExp tenv (App fn arg) =
  do fnTy <- checkExp tenv fn
     argTy <- checkExp tenv arg
     case fnTy of
      FunTy [expectedArgTy] resultTy ->
        guard (argTy == expectedArgTy)
        >> return resultTy
      other -> Nothing  

checkExps tenv es =
  mapM (checkExp tenv) es


--
-- Examples
--

-- prove and pretty-print the result
proveAndDisplay :: Exp -> IO()
proveAndDisplay e =
  displayProof (proveTopLevel e)

proofTest :: Exp -> Bool
proofTest = wellFormed . proveTopLevel

-- should evaluate to True
finalTest = all proofTest [eg0, eg1, eg2]


eg0 = parse "let f = %(int x) +(x,1) in (f 17)"

eg1 = parse "let f = %([int->int] g) (g (g 3)) in let h = %(int x) x in (f h)"

eg2 = parse "let p = (1,(2,false)) in +(0,fst(snd(p)))"


{- Notes

1.  Perhaps oddly, there is a difference between

    do PairTy tya tyb <- return ty
       ...

    and

    do let PairTy tya tyb = ty
       ...

    The difference is in the case of a pattern matching failure.  In
    the first case, the result of the first line is Nothing, which gets
    passed down through the do.  In the second case, the pattern is
    "irrefutable" and generates a fatal error.
-}