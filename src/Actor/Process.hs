{-# LANGUAGE InstanceSigs #-}
module Actor.Process where
import Actor.Ast
import Ast
import qualified Data.Map as M
import Control.Arrow hiding ((<+>))
import Control.Applicative
import Data.Maybe (fromMaybe, isJust)
import Control.Monad (liftM, ap)

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

constA :: Action
constA = ArrLambda id1 (LeftE constr)
  where
    id1 = Var $ makeIdent "x"
    c = makeIdent "__"
    constr = Constr c []

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
    (ArrLambda p (CaseOf e (
        zipWith (curry (\((exp, _), c) -> (exp, Guard [], LeftE c))) cs cases
    )))
   cond
  where
    _left = makeIdent "_left"
    _right = makeIdent "_right"
    lf e = Constr _left [e]
    rf e = Constr _right [e]

    vars = map ((Tuple . map Var) . (\(e, _) -> boundVars (Tuple [p, e]))) cs
    binaries = take (length cs) $ iterate (rf.) lf
    cases = zipWith ($) binaries vars
    -- right most case (idA) is filler and should not be reached ever
    cond = foldr (\((_, cmd), vs) a -> AEither (ppAction (Proc vs cmd)) a) constA (zip cs vars)


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
ppAction (Proc p (ApplyCmd (Arr (App n inv [arg])) e)) = ArrLambda p (LeftE (App n inv [arg, e]))
ppAction (Proc p (ApplyCmd a e)) = Comp (ArrLambda p (LeftE e)) (ppAction a)
ppAction (Proc p (KCmd p' c)) = ppAction (Proc (Tuple [p, p']) c)
ppAction (Proc p (DoCmd [DoSeq c])) = ppAction (Proc p c)
ppAction (Proc p (DoCmd ((DoBind e c):ds))) = x
  where x = ppAction (Proc p c) `bindA` ppAction (Proc p (KCmd e (DoCmd ds)))
-- Don't see the point of this one in a reversible system
ppAction (Proc p (DoCmd ((DoSeq c):ds))) = ppAction (Proc p c) `bind_A` ppAction (Proc p (DoCmd ds))

ppAction (Proc p (CaseOfCmd e cs)) = ppAction $ caseA p e cs

-- Translate Arrow choice into pure arrow notation, ABoth is given
ppAction (ABoth a1 a2) = ABoth (ppAction a1) (ppAction a2)
ppAction (AEither a1 a2) = AEither (ppAction a1) (ppAction a2)
ppAction (ALeft a ) = ppAction $ ABoth a idA
ppAction (ARight a ) = ppAction $ ABoth idA a

-- Propagate through rest
ppAction (Comp a1 a2) = Comp (ppAction a1) (ppAction a2)
ppAction (First a) = First (ppAction a)
ppAction (Second a) = Second (ppAction a)
ppAction a = a

-- Lift anonymous lambda functions from actions and add as named functions to env
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
liftLambda id0 (ABoth a1 a2) = (ABoth a1' a2', env1 `M.union` env2, id2)
  where
    (a1', env1, id1) = liftLambda id0 a1
    (a2', env2, id2) = liftLambda id1 a2
liftLambda id0 (AEither a1 a2) = (AEither a1' a2', env1 `M.union` env2, id2)
  where
    (a1', env1, id1) = liftLambda id0 a1
    (a2', env2, id2) = liftLambda id1 a2
liftLambda id a = (a, M.empty, id)

data Path a = Path{ pathAction :: a, pathMsgs :: [MsgP], choicePathMsgs :: [MsgP], pathYield :: Maybe Action }
  deriving Show

newtype Paths a = Paths [Path a]
  deriving Show

allPathMsgs :: Paths a -> String
allPathMsgs (Paths ps) = unlines (map show ps')
  where
    ps' = map pathMsgs ps

instance Functor Paths where
  fmap f (Paths ps) = Paths $ map (f <$>) ps

instance Applicative Paths where
  pure a = Paths [pure a]
  (<*>) (Paths fs) (Paths ps) = Paths $ concatMap (\f -> map (f <*>) ps) fs

instance Monad Paths where
  -- Assume result of f is single path
  return = pure
  (>>=) :: Paths a -> (a -> Paths b) -> Paths b
  (>>=) (Paths ps) f =
    Paths $ map g ps
    where
      g p =
        p >>= (\a ->
          case f a of
            Paths [p] -> p
            Paths ps' -> error $ "cannot handle paths of length " ++ show (length ps'))

instance MonadFail Paths where
  fail = error

instance Monad Path where
  return = pure

  -- Maybe pick last y instead of alternative
  (>>=) (Path a p c y) f = Path a' (p ++ p') (c ++ c') (y <|> y')
    where Path a' p' c' y' = f a

instance Functor Path where
  fmap = liftM

instance Applicative Path where
  pure a = Path a [] [] Nothing
  (<*>) = ap


-- Assuming that p2 is always greater or equal in length to p1
compPath :: (a -> a -> a) -> [Path a] -> [Path a] -> [Path a]
compPath comp p1 p2 = concatMap f p1
  where f (Path a pats oPats Nothing) = map (\(Path a' pats' oPats' y') -> Path (comp a a') (pats ++ pats') (oPats ++ oPats') y') p2

optionalPaths :: Paths a -> Paths a
optionalPaths (Paths ps) = Paths $ map (\(Path a p c y) -> Path a [] (p++c) y) ps

choicePath :: (a -> a -> a) -> Paths a -> Paths a -> Paths a
choicePath choice p1@(Paths ps1) p2@(Paths ps2)
  | yields = Paths (ps1 ++ ps2)
  | mismatch = error "Mismatched yields in path choice"
  | otherwise = choice <$> optionalPaths p1 <*> optionalPaths p2
  where
      yields = all (\ (Path _ _ _ y) -> isJust y) (ps1 ++ ps2)
      mismatch = any (\ (Path _ _ _ y) -> isJust y) (ps1 ++ ps2)

catPaths :: Show a => [Paths a] -> Paths a
catPaths ((Paths ps1):pss) = Paths (ps1 ++ ps2)
  where (Paths ps2) = catPaths pss
catPaths [] = Paths []

reverseAction :: [MsgP] -> Action -> Paths Action
reverseAction msgs a = Paths flattened
  where
    flattened = map (\(Path a m c y) -> Path (flattenDo a) m c y) (filter noEmptyMsgs (map addSendsAndYields ps))
    Paths ps = reversiblePaths a
    noEmptyMsgs path = not (null (choicePathMsgs path) && null (pathMsgs path))
    addSendsAndYields path@(Path (Proc e (DoCmd ds)) p o y) =
        case y of
          Just (Yield aId1 aId2) -> Path (Comp (Proc e (DoCmd ds'')) (Yield aId2 aId1)) p o Nothing
          Nothing -> error $ "Error in reverse, Path without yield " ++ show path
      where
        (dSeq:ds') = reverse ds

        ds'' = reverse ((dSeq:sends) ++ ds')
        hole = Var $ makeIdent "_"
        -- TODO in future could have sending be inverse of message bit
        sends = map (\msg -> (DoBind (Tuple []) . ApplyCmd (Send (not (msgPInv msg)) hole)) (msgPat msg)) msgs

reversiblePaths :: Action -> Paths Action
reversiblePaths (Arr (Var x)) = pure $ ArrLambda arg (LeftE (App x False [arg]))
  where
    arg = Var $ makeIdent "_x"

reversiblePaths (Arr (App x inv args)) = pure $ Arr (App x (not inv) args)
reversiblePaths (First a) = First <$> reversiblePaths a
reversiblePaths (Second a) = Second <$> reversiblePaths a
-- a1 reversed should only have one branch
reversiblePaths (Comp a1 a2) = Comp <$> reversiblePaths a2 <*> reversiblePaths a1
reversiblePaths (Send inv pat) = Paths [(pure $ Recv (not inv) pat){ pathMsgs=[MsgP (not inv) (Tuple [addrHole, pat])]}]
-- TODO: eval matching not smart enough (or too smart) to match multiple variables of same name
  where addrHole = Var $ makeIdent "_addr"
reversiblePaths (Spawn inv actor) = pure $ Spawn (not inv) actor
-- Maybe aBoth and aEither might have distinct ways to reverse?
reversiblePaths (ABoth a1 a2) = choicePath ABoth (reversiblePaths a1) (reversiblePaths a2)
reversiblePaths (AEither a1 a2) = choicePath AEither (reversiblePaths a1) (reversiblePaths a2)
reversiblePaths (ARight a) = ARight <$> optionalPaths (reversiblePaths a)
reversiblePaths (ALeft a) = ALeft <$> optionalPaths (reversiblePaths a)
reversiblePaths y@(Yield _ _) = Paths [(pure idA){ pathYield=Just y }]


-- Todo Maybe add checks to avoid bad behaviour here
reversiblePaths (Proc e1 (ApplyCmd a0 e2)) = (\a -> Comp a (ArrLambda e3 (LeftE e1))) . f_a <$> ps
  where
    ps = reversiblePaths a0
    (f_a, e3) = reverseInExp e2

reversiblePaths (Proc e1 (DoCmd ds)) = res
  where
    res = (\d ds' -> Proc _id (DoCmd ([d] ++ reverse ds' ++ [DoSeq (ApplyCmd idA e1)]))) <$> psFirst <*> pds
  -- TODO This might clash with other variables...
    _id = Var $ makeIdent "_proc"
    DoSeq cmd = last ds
    psFirst = reverseDoAction (DoBind _id cmd)
    pds = mapM reverseDoAction (init ds)

reverseDoAction :: DoAction -> Paths DoAction
reverseDoAction (DoBind e1 (ApplyCmd a1 e2)) = (\a -> DoBind e3 (ApplyCmd a e1)) . f_a <$> ps
  where
    ps = reversiblePaths a1
    (f_a, e3) = reverseInExp e2
reverseDoAction (DoBind e1 (DoCmd [DoSeq cmd])) = reverseDoAction (DoBind e1 cmd)
reverseDoAction (DoBind e1 (DoCmd ds)) = do
  (DoBind e2 cmd'):ds'<- pds
  dFirst <- psFirst
  return $ DoBind e2 (DoCmd ([dFirst] ++ reverse ds' ++ [DoSeq cmd']))
  where
    DoSeq cmd = last ds
    psFirst = reverseDoAction (DoBind e1 cmd)
    pds = mapM reverseDoAction (init ds)
reverseDoAction (DoBind (Var p) (CaseOfCmd e1 cs))
  | identifier p == "_proc" = paths

  where
    paths = catPaths (map f cs)
    (f_a, e2) = reverseInExp e1
    cs' = map snd cs
    f :: (LExpr, CmdAction) -> Paths DoAction
    f (pat, c) =
      (\a -> DoBind e2 (ApplyCmd a (Var p))) . f_a <$> reversiblePaths (Proc pat c)

reverseDoAction (DoBind e (CaseOfCmd e1 cs)) = error "I haven't implemented bind cases yet"



reverseDoAction (DoSeq cmd) = error $ "Not possible to handle DoSeq not at end of do with cmd " ++ show cmd
reverseDoAction d = error $ "No case for " ++ show d

reverseInExp :: LExpr -> (Action -> Action, LExpr)
reverseInExp (App name inv args) = (f_a, argLast)
  where argLast = last args
        argInit = init args
        f_a a = Comp a (Arr (App name (not inv) argInit))
reverseInExp exp = (id, exp)

flattenDo :: Action -> Action
-- Translate do-like arrow notation to pure arrow notation
flattenDo (Proc p (ApplyCmd a e)) = Proc p (ApplyCmd (flattenDo a) e)
flattenDo (Proc p (DoCmd ds)) = Proc p (DoCmd ds')
  where ds' = concatMap flattenDo' ds
flattenDo (Proc p (CaseOfCmd e cs)) = error "Have not defined case do flattening yet"

-- Translate Arrow choice into pure arrow notation, ABoth is given
flattenDo (ABoth a1 a2) = ABoth (flattenDo a1) (flattenDo a2)
flattenDo (AEither a1 a2) = AEither (flattenDo a1) (flattenDo a2)
flattenDo (ALeft a ) = flattenDo $ ABoth a idA
flattenDo (ARight a ) = flattenDo $ ABoth idA a

-- Propagate through rest
flattenDo (Comp a1 a2) = Comp (flattenDo a1) (flattenDo a2)
flattenDo (First a) = First (flattenDo a)
flattenDo (Second a) = Second (flattenDo a)
flattenDo a = a

-- When reversing, nested do blocks are not inverted to become outer do blocks
-- So instead need to flatten nested dos into same block to prevent context loss
-- TODO need to improve this to be more robust
flattenDo' :: DoAction -> [DoAction]
flattenDo' (DoBind v1 ((ApplyCmd (Proc v2 (DoCmd ds)) v3)))
  | v2 == v3 = rest ++ [DoBind v1 c]
    where
      (DoSeq c) = last ds
      rest = init ds
flattenDo' (DoBind v1 ((ApplyCmd (Comp (Proc v2 (DoCmd ds)) a) v3)))
   | v2 == v3 = rest ++ [DoBind v4 c] ++ [DoBind v1 (ApplyCmd a v4)]
    where
      (DoSeq c) = last ds
      rest = init ds
      v4 = Var $ makeIdent "_d"
flattenDo' d = [d]
