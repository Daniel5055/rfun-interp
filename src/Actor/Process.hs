module Actor.Process where
import Actor.Ast
import Ast
import Actor.Interp (Runtime)

splitA :: Action
splitA = ArrLambda (Var id1) (LetIn (Var id2) (App eqFunc True [Constr eqConstr []]) (LeftE (Tuple [Var id1, Var id2])))
  where
    id1 = makeIdent "_x"
    id2 = makeIdent "_y"
    eqFunc = makeIdent "eq"
    eqConstr = makeIdent "Eq"

idA :: Action
idA = ArrLambda (Var x) (LeftE (Var x))
  where
    x = makeIdent "_x"

-- Not really possible, as we are discarding data in a reversible system
fstA :: Action
fstA = ArrLambda (Tuple [Var id1, Var id2]) (LeftE (Var id1))
  where
    id1 = makeIdent "_x"
    id2 = makeIdent "_y"

bindA :: Action -> Action -> Action
bindA u = Comp (Comp (Comp splitA (First idA)) (Second u))

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

-- Lift lambdas
--liftLambda :: Runtime Action -> Runtime Action
--liftLambda rt = do
    --a <- rt
    --case a of
      --ArrLambda p exp -> undefined
  --where
    --rt' env as addr = Right (Arr (Var "_"), as, addr)
    --res = run 

--liftLambda (Comp a1 a2) = Comp <$> liftLambda a1 <*> liftLambda a2
--liftLambda (First a) = First <$> liftLambda a
--liftLambda (Second a) = First <$> liftLambda a
--liftLambda a = return a