import Data.List (intercalate)
import Data.List 
import Data.Either

type N = Integer

data Slot = Slot
          deriving (Show, Eq)

data Template =
  Template [Either String Slot]
  deriving Eq

-- explicitly define show for templates so that they print like in the
-- discussion above
instance Show Template where
  show (Template xs) =   concat ( map f xs)
    where f (Left x) = x
          f (Right x) = "{}"

--instance  Show Either where
--	show (Left x) = x
--	show (Right x) = x

instance Show Def where
  show (Def rs) = "Templates: " ++ (intercalate " // " $ map show rs)

           
-- An inductive definition is just a list of templates.
data Def =
  Def [Template]
  deriving Eq

data Derivation = Derivation Template [Derivation]
                deriving Show
--Q1 
templateArity :: Template -> Int
templateArity (Template xs) = sum $ map (\x-> either (\_ -> 0) (\_->1)x) xs

--Q2
templateInstance :: Template -> [String] -> String
subst :: [String] -> [Either String Slot] -> [Either String Slot]
subst [] xs = xs
subst (str : strs) (Right _ : xs) = Left str : subst strs xs
subst (str : strs) (x : xs) = x : subst (str : strs) xs

noLeft (Left x) = x
templateInstance (Template xs) ys = [y | x<-(map noLeft (subst  ys xs) ), y<-x] 


--Q3
derivationFoldR :: (Template -> [a] -> a) -> Derivation -> a
bpBase = Template [Left "()"]
bpStep1 = Template [Left "(", Right Slot, Left ")"]
bpStep2 = Template [Right Slot, Right Slot]

bp = Def [bpBase, bpStep1, bpStep2]
bp1 = Derivation bpBase []          -- ()
bp2 = Derivation bpStep1 [bp1]      -- (())
bp3 = Derivation bpStep2 [bp1, bp2] -- ()(())
bp4 = Derivation bpStep1 [bp3]      -- (()(()))

derivationFoldR f (Derivation r l ) = f r (map (derivationFoldR f) l)

