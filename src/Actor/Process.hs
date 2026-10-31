module Actor.Process where
import Actor.Ast
import Ast
import qualified Data.Map as M
import Debug.Trace

splitA :: Action
splitA = ArrLambda id1 (LetIn id2 (App eqFunc False [id1, Constr eqConstr []]) (LeftE (Tuple [id1, id2])))
  where
    id1 = Var $ makeIdent "_x"
    id2 = Var $ makeIdent "_y"
    eqFunc = makeIdent "eq"
    eqConstr = makeIdent "Eq"

-- Not really possible, as we are discarding data in a reversible system
fstA :: Action
fstA = ArrLambda (Tuple [id1, id2]) (LeftE id1)
  where
    id1 = Var $ makeIdent "_x"
    id2 = Var $ makeIdent "_y"

idA :: Action
idA = ArrLambda id1 (LeftE id1)
  where
    id1 = Var $ makeIdent "_x"

untagA :: Action
untagA = ArrLambda id1 (CaseOf id1 [
    (Constr _left [id2], Guard [], LeftE id2),
    (Constr _right [id3], Guard [], LeftE id3)
  ])
  where
    id1 = Var $ makeIdent "_x"
    id2 = Var $ makeIdent "_y"
    id3 = Var $ makeIdent "_z"
    _left = makeIdent "_left"
    _right = makeIdent "_right"

-- Translate cases into binary `Right (Right... (Left val) ...)`
caseA :: LExpr -> LExpr -> [(LExpr, CmdAction)] -> Action
caseA p e cs =
  Comp 
    (ArrLambda id1 (CaseOf e (
        zipWith (curry (\((exp, _), c) -> (exp, Guard [], LeftE c))) cs cases
    )))
   cond
  where
    id1 = Var $ makeIdent "_x"
    _left = makeIdent "_left"
    _right = makeIdent "_right"
    lf e = Constr _left [e]
    rf e = Constr _right [e]

    vars = map ((Tuple . map Var) . (\(e, _) -> boundVars e)) cs
    binaries = take (length cs) $ iterate (rf.) lf
    cases = zipWith ($) binaries vars
    -- right most case (idA) is filler and should not be reached ever
    cond = foldr (\(_, cmd) a -> AEither (ppAction (Proc p cmd)) a ) idA cs

boundVars :: LExpr -> [Ident]
boundVars (Constr _ exps) = concatMap boundVars exps
boundVars (Var id) = [id]
boundVars (Tuple exps) = concatMap boundVars exps
boundVars (List (ListCons exp list)) = boundVars exp ++ boundVars (List list)
boundVars (List (ListEnd exp)) = boundVars exp
boundVars (List ListNil) = []
-- Ignored for Application (not a 'pattern')
boundVars _ = []



bindA :: Action -> Action -> Action
bindA u = Comp (Comp splitA (Second u))

-- Should not really be possible in a reversible system to discard result
bind_A :: Action -> Action -> Action
bind_A u v = u `bindA` Comp fstA v

-- Pre process actions into pure arrow notation
ppAction :: Action -> Action

-- Translate do-like arrow notation to pure arrow notation
ppAction (Proc p (ApplyCmd a e)) = Comp (ArrLambda p (LeftE e)) a
ppAction (Proc p (KCmd p' c)) = ppAction (Proc (Tuple [p, p']) c)
ppAction (Proc p (DoCmd [DoSeq c])) = ppAction (Proc p c)
ppAction (Proc p (DoCmd ((DoBind e c):ds))) = ppAction (Proc p c) `bindA` ppAction (Proc p (KCmd e (DoCmd ds)))
-- Don't see the point of this one in a reversible system
ppAction (Proc p (DoCmd ((DoSeq c):ds))) = ppAction (Proc p c) `bind_A` ppAction (Proc p (DoCmd ds))

ppAction (Proc p (CaseOfCmd e cs)) = caseA p e cs

-- Translate Arrow choice into pure arrow notation, ABoth is given
ppAction (ABoth a1 a2) = ABoth a1 a2
ppAction (ALeft a ) = ABoth a idA
ppAction (ARight a ) = ABoth idA a
ppAction (AEither a1 a2) = Comp (ABoth a1 a2) untagA

-- Propagate through rest
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
