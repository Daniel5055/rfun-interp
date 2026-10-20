module Actor.Process where
import Actor.Ast
import Ast
import qualified Data.Map as M
import Debug.Trace

splitA :: Action
splitA = ArrLambda (Var id1) (LetIn (Var id2) (App eqFunc False [Var id1, Constr eqConstr []]) (LeftE (Tuple [Var id1, Var id2])))
  where
    id1 = makeIdent "_x"
    id2 = makeIdent "_y"
    eqFunc = makeIdent "eq"
    eqConstr = makeIdent "Eq"

-- Not really possible, as we are discarding data in a reversible system
fstA :: Action
fstA = ArrLambda (Tuple [Var id1, Var id2]) (LeftE (Var id1))
  where
    id1 = makeIdent "_x"
    id2 = makeIdent "_y"

bindA :: Action -> Action -> Action
bindA u = Comp (Comp splitA (Second u))

-- Should not really be possible in a reversible system to discard result
bind_A :: Action -> Action -> Action
bind_A u v = u `bindA` Comp fstA v

-- Translate do-like arrow notation to pure arrow notation
ppAction :: Action -> Action
ppAction (Proc p (ApplyCmd a e)) = Comp (ArrLambda p (LeftE e)) a
ppAction (Proc p (KCmd p' c)) = ppAction (Proc (Tuple [p, p']) c)
ppAction (Proc p (DoCmd [DoSeq c])) = ppAction (Proc p c)
ppAction (Proc p (DoCmd ((DoBind e c):ds))) = ppAction (Proc p c) `bindA` ppAction (Proc p (KCmd e (DoCmd ds)))
-- Don't see the point of this one in a reversable system
ppAction (Proc p (DoCmd ((DoSeq c):ds))) = ppAction (Proc p c) `bind_A` ppAction (Proc p (DoCmd ds))

ppAction (Comp a1 a2) = Comp (ppAction a1) (ppAction a2)
ppAction (First a) = First (ppAction a)
ppAction (Second a) = Second (ppAction a)
ppAction a = a

-- Lift anomymous lambda functions from actions and add as named functions to env
liftLambda :: Integer -> Action -> (Action, DefEnv, Integer)
liftLambda id (ArrLambda arg exp) = (Arr (Var lName), M.singleton (identifier lName) (FDef lFunc), id+1)
  where
    lName = makeIdent ("__" ++ show id)
    lFunc =
      Func
        lName
        Nothing
        [Clause lName [arg] (Guard []) exp]

liftLambda id0 (Comp a1 a2) = (Comp a1' a2', env1 `M.union` env2, id2)
  where
    (a1', env1, id1) = liftLambda id0 a1
    (a2', env2, id2) = liftLambda id1 a2
liftLambda id (First a) = (First a', env, id')
  where
    (a', env, id') = liftLambda id a
liftLambda id (Second a) = (Second a', env, id')
  where
    (a', env, id') = liftLambda id a
liftLambda id a = (a, M.empty, id)
