module Sands where

import Data.Map (Map)
import qualified Data.Map as M

type Var = String
data Term =
   Var Var
 | Lambda Var Term
 | App Term Var
 | K [Var] -- K [(String, [Vars])] 
 | Let [(Var, Term)] Term
 | Case Term Term 
 | Marker Var -- This is only used in the Stack
 | Alts [(Term, Term)] 
  deriving Show

id_fun :: Term
id_fun = Lambda "x" (Var "x")

app_id_fun :: Term
app_id_fun = App id_fun "y"

type Heap = Map Var Term
type Stack = [Term]

type Config = (Heap, Term, Stack)

-- Value is a K or a Lambda
isValue :: Term -> Bool
isValue x = case x of
  K _ -> True
  Lambda _ _ -> True
  _ -> False

-- Substitute
subst :: Var -> Var -> Term -> Term
subst y x t =
  case t of
    Var _x -> if x == _x then Var y else t
    Lambda z t -> Lambda z $ subst y x t
    App m _x -> if x == _x
                then App (subst y x m) y
                else App (subst y x m) _x
    _ -> t

-- One step of the semantics
op_sem :: Config -> Config
-- Lookup 
op_sem (h, Var x, s) =
  case M.lookup x h of
    Nothing -> error $ x ++ " is not in the heap"
    Just m ->
      let h' = M.delete x h
          mx = Marker x
      in (h', m, mx:s)
-- Update
op_sem (h, v, ((Marker x):s)) = 
  if isValue v
  then (M.insert x v h, v, s)
  else error $ "cant apply update on a non-value term"
-- Unwind
op_sem (h, App m x, s) = (h, m, (Var x):s)
-- Subst
op_sem (h, Lambda x m, (Var y:s)) = (h, subst y x m, s)
-- Case
op_sem (h, Case m alts, s) = (h, m, alts:s)
-- Branch
op_sem (h, K vars, ((Alts [(K vars', m)]):s)) =
  let match = zip vars vars' -- [(x,y)]
      m' = foldr (\(x,y) _m -> subst y x _m) m match
  in (h, m', s)
-- Letrec
op_sem (h, Let defs m, s) =
  let h' = foldr (\(x,n) h' -> M.insert x n h') h defs
  in (h', m, s)

init_conf :: Term -> Config
init_conf m = (M.empty, m, [])

semantics :: Config -> Config
semantics conf@(h, m, s) =
  if isValue m && length s == 0 
  then conf 
  else semantics $ op_sem conf 

sem :: Term -> Config
sem = semantics . init_conf 
