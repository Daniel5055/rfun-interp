{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
module Actor.Interp where
import Ast (Value (TupleV, IntV, FunV, ConstrV), LExpr (App, Var, Tuple, Constr, List), Func (Func, funcName), makeIdent, Clause (..), Guard (Guard), Expr (CaseOf, LeftE, LetIn), Ident (identifier), Program, LExprList (ListNil, ListEnd, ListCons))
import Actor.Ast
import Control.Monad (liftM, ap)
import System.Posix.Internals (rtsIsThreaded_)
import Data.Foldable (find)
import qualified Data.Map as M
import Core.Interp (evalRMatchV, evalRMatchS, Substitution, Eval, runEval, idSub, failEval)
import qualified Core.Ast as C
import Interp (tcValue, tcLExpr, interp)
import Control.Applicative
import Actor.Process
import Data.List (union, (\\), delete)
import Debug.Trace


type Addr = Integer
data Msg = Msg { msgInv :: Bool, msgValue :: Value, msgAddr :: Addr }
    deriving (Show, Eq)

type Result = M.Map Addr Value

data ActorState = AS { aAddr :: Addr, aInbox :: [Msg], aState :: Value, aActor :: Actor }
    deriving Show

newtype Runtime a = Runtime { run :: DefEnv -> [ActorState] -> Addr -> Either String (a, [ActorState], Addr) }

instance Monad Runtime where
    return = pure

    (>>=) m f = Runtime rt2
        where
            rt2 env as nextAddr =
                case run m env as nextAddr of
                    Right (a, as', addr) -> run (f a) env as' addr
                    Left err -> Left err

instance Functor Runtime where
    fmap = liftM

instance Applicative Runtime where
    pure a = Runtime (\_ as addr -> Right (a, as, addr))

    (<*>) = ap

instance MonadFail Runtime where
    fail s = Runtime (\_ _ _-> Left s)


runtimeError :: String -> Runtime a
runtimeError s = Runtime (\_ _ _ -> Left s)


----- Side effect functions

expandEnv :: DefEnv -> Runtime a -> Runtime a
expandEnv env rt = Runtime rt'
    where rt' env' = run rt (env' `M.union` env)

isDone :: Runtime Bool
isDone = Runtime rt
    where
        rt _ as n = Right (null as, as, n)

yield :: ActorState -> Runtime ()
yield as = Runtime rt
    where
        rt _ as' n = Right ((), as' ++ [as], n)

spawn :: Actor -> Value -> Runtime Addr
spawn a v = Runtime rt
    where
        rt _ as nextAddr = Right (nextAddr, as ++ [AS nextAddr [] v a], nextAddr + 1)

send :: Addr -> Msg -> Runtime (Addr, Msg)
send addr msg = Runtime rt
    where
        rt _ as n = trace ("Sending to " ++ show addr ++ " with " ++ show msg) $
            case send' as addr msg of
                Just as' -> Right ((addr, msg), as', n)
                Nothing -> Left "Actor at address does not exist"

send' :: [ActorState] -> Addr -> Msg -> Maybe [ActorState]
send' (a:as) addr msg
    | aAddr a == addr = Just (a { aInbox = aInbox a ++ [msg] }:as)
    | otherwise = (a:) <$> send' as addr msg
send' [] addr msg = error $ "Sending to " ++ show addr ++ " with " ++ show msg ++ " with no actor states to receive"

getHeadActorState :: Runtime ActorState
getHeadActorState = Runtime rt
    where
        rt _ as n = Right (head as, as, n)

removeHeadActorState :: Runtime ()
removeHeadActorState = Runtime rt
    where
        rt _ (a:as) n = Right ((), as, n)

removeHeadActorStateMsg :: Msg -> Runtime ()
removeHeadActorStateMsg msg = Runtime rt
    where
        rt _ (a:as) n = Right ((), a{ aInbox=newInbox }:as, n)
            where
                newInbox = delete msg (aInbox a)


receive :: Bool -> LExpr -> Runtime Msg
receive inv exp = do
        inbox <- aInbox <$> getHeadActorState

        let pat = tcLExpr exp
        let vals = zip (map (tcValue . msgValue) inbox) inbox
        let f (val, msg) = do
            if msgInv msg == inv
                then do
                    sub <- evalRMatchS val pat
                    return msg
                else
                    empty
        let match = foldl1 (<|>) (map f vals)
        case runEval match of
            Right (msg, _) -> do
                removeHeadActorStateMsg msg
                inbox <- aInbox <$> getHeadActorState
                return msg
            Left _ -> error $ "Tried receiving msg which does not exist for pat " ++ show exp



-- When called, head actor state presumed to be the actor running
getAddr :: Runtime Addr
getAddr = aAddr <$> getHeadActorState

nextActor :: Runtime (ActorState, Path Action, Substitution)
nextActor = Runtime rt
    where rt env as n = let (state, path, sub, as') = matchActors as in Right ((state, path, sub), as', n)

getFuncEnv :: Runtime Program
getFuncEnv = Runtime rt
    where
        rt env as n = Right (toProg env, as, n)
        toProg = map (\(FDef f) -> f) . filter filterFunc . map snd . M.toList
        filterFunc (ADef _) = False
        filterFunc (FDef _) = True

lookupFunc :: String -> Runtime Func
lookupFunc s = Runtime rt
    where
        rt env as addr = (,as,addr) <$> findFunc s env
        findFunc s env =
            case M.lookup s env of
                Just def ->
                    case def of
                        FDef f -> Right f
                        ADef _ -> Left $ "Identifier " ++ s ++ " refers to actor not function"
                Nothing -> Left $ "Function " ++ s ++ "  does not exist"

lookupActor :: String -> Runtime Actor
lookupActor s = Runtime rt
    where
        rt env as addr = (,as,addr) <$> findActor s env
        findActor s env =
            case M.lookup s env of
                Just def ->
                    case def of
                        ADef a -> Right a
                        FDef _ -> Left $ "Identifier " ++ s ++ " refers to actor not function"
                Nothing -> Left $ "Function " ++ s ++ "  does not exist"


matchActors :: [ActorState] -> (ActorState, Path Action, Substitution, [ActorState])
matchActors (actorState@(AS addr inbox state actor):as) =
    case res of
        Right ((newInbox, path, sub), _) -> let
            newAs = AS addr newInbox state actor
            in (newAs, path, sub, newAs:as)
        Left _ -> (a', path', sub', as' ++ [actorState])

    where
        res = runEval $ matchActorClauses inbox (actorClause actor)
        (a', path', sub', as') = matchActors as
matchActors [] = error "Program stalled, no matching messages for remaining actors"


matchActorClauses :: [Msg] -> [ActorClause] -> Eval ([Msg], Path Action, Substitution)
matchActorClauses [] [ac] =
    if aClauseMsgs ac == [Tuple []]
        then return ([], Path (aClauseBody ac) (map (MsgP True) $ aClauseMsgs ac) [] Nothing, idSub)
        else failEval "No matching messages"
matchActorClauses [] _ = failEval "No messages in inbox"
matchActorClauses inbox (ac:acs) = matchActorClause ac <|> matchActorClauses inbox acs
    where
        matchActorClause ac' = forwardsMatch <|> backwardsMatch
            where
                Paths (forwards:backwards) = clausePatterns ac
                forwardsMatch = do
                    (matchMsgs, p, sub) <- matchPaths inbox (Paths [forwards])
                    return (inbox \\ matchMsgs, p, sub)
                backwardsMatch = do
                    (msgs, p, _) <- matchPaths inbox (Paths backwards)

                    return (inbox, p, idSub)
matchActorClauses inbox [] = failEval "No matching messages"

clausePatterns :: ActorClause -> Paths Action
clausePatterns ac = Paths (forwardsPath:backwardsPaths)
    where
        forwardsPath = Path (aClauseBody ac) (map (MsgP True) $ aClauseMsgs ac) [] Nothing
        Paths backwardsPaths = reverseAction (aClauseMsgs ac) (aClauseBody ac)

matchPaths :: [Msg] -> Paths Action -> Eval ([Msg], Path Action, Substitution)
matchPaths inbox (Paths (p:ps)) =
    matchPath inbox p <|> matchPaths inbox (Paths ps)
matchPaths inbox (Paths []) = failEval "No path found"

matchPath :: [Msg] -> Path Action -> Eval ([Msg], Path Action, Substitution)
matchPath inbox p = do
        let pats = zip (map (tcLExpr . msgPat) (pathMsgs p)) (pathMsgs p)
        let vals = zip (map (\msg -> tcValue (TupleV [IntV (msgAddr msg), msgValue msg])) inbox) inbox
        mAndS <- mapM (\pat -> foldl1 (<|>) $ map (f pat) vals ) pats
        let (msgs, sub) = foldl (\(msgs, sub') (msg, sub) -> (msg:msgs, M.union sub sub')) ([], M.empty) mAndS
        return (msgs, p, sub)
    where
        f (pat, msgP) (val, msg) = do
            if msgPInv msgP == msgInv msg
                then do
                    sub <- evalRMatchS val pat
                    return (msg, sub)
                else
                    empty

evalActor :: Result -> Runtime Result
evalActor res = do
    done <- isDone
    if done then return res else do
    (as, path, sub) <- nextActor

    traceM "----------------"
    traceM $ "Found path for Actor " ++ show (aAddr as)

    let sub' = M.insert "self" (tcValue (IntV (aAddr as))) sub
    let a = (ppAction . subAction sub') (pathAction path)
    let (action, env, _) = liftLambda 0 a
    (TupleV [FunV f, val]) <- expandEnv env (evalAction action (aState as))

    -- Head actor inbox maybe be changed, so get latest version
    as' <- getHeadActorState
    removeHeadActorState

    if f == ""
        then do
            traceM $ "Yielding to end with state " ++ show val
            evalActor $ M.insert (aAddr as) val res
        else do
            actor <- lookupActor f
            traceM $ "Yielding to " ++ f ++ " with state " ++ show val
            yield as'{ aState = val, aActor = actor }
            evalActor res

-- Evaluate runtime until it resolves to list of final actor states
evalAction :: Action -> Value -> Runtime Value
evalAction (Send inv pat) (TupleV [IntV targetAddr, msg]) = do
    sourceAddr <- getAddr
    send targetAddr (Msg inv msg sourceAddr)
    return $ TupleV []
evalAction (Send True pat) v =
    runtimeError $ "send expects 2-tuple, not " ++ show v

evalAction (Recv inv pat) val = do
    msg <- receive inv pat
    return $ TupleV [IntV (msgAddr msg), msgValue msg]

evalAction (Arr (App name inv args)) val = do
    env <- getFuncEnv
    case interp (env ++ [Func (makeIdent "_f") Nothing [Clause (makeIdent "_f") [Var (makeIdent "_x")] (Guard []) (LeftE (App name inv (args++[Var (makeIdent "_x")])))]]) "_f" [val] of
        Right v -> return v
        Left s -> runtimeError s
evalAction (Arr (Var name)) val = do
    env <- getFuncEnv
    case interp env (identifier name) [val] of
        Right v -> return v
        Left s -> runtimeError s

evalAction (Comp a1 a2) val = evalAction a1 val >>= evalAction a2

evalAction (First a) (TupleV [v1, v2]) = do
    v3 <- evalAction a v1
    return $ TupleV [v3, v2]
evalAction (First a) v =
    runtimeError $ "Expected 2-tuple value to `first` arrow, instead got " ++ show v

evalAction (Second a) (TupleV [v1, v2]) = do
    v3 <- evalAction a v2
    return $ TupleV [v1, v3]
evalAction (Second a) v =
    runtimeError $ "Expected 2-tuple value to `second` arrow, instead got " ++ show v

evalAction (Spawn True name) val = do
    a <- lookupActor (identifier name)
    IntV <$> spawn a val

evalAction (Yield (Just name) _) val = return $ TupleV [FunV (identifier name), val]
evalAction (Yield Nothing _) val = return $ TupleV [FunV "", val]

-- Arrow choice behaviour defined by this
evalAction (ABoth a1 a2) (ConstrV "_left" [x]) = do
    val <- evalAction a1 x
    return (ConstrV "_left" [val])
evalAction (ABoth a1 a2) (ConstrV "_right" [x]) = do
    val <- evalAction a2 x
    return (ConstrV "_right" [val])
evalAction (ABoth a1 a2) v = runtimeError $ "Expected either value, not " ++ show v

-- Arrow either must also be handled due to irreversibility of untag
evalAction (AEither a1 a2) c = do
    val <- evalAction (ABoth a1 a2) c
    case val of
        ConstrV "_left" [v] -> return v
        ConstrV "_right" [v] -> return v
evalAction a v = runtimeError $ "Missing eval action clause for " ++ show a

-- Accepts a program, function or actor to run, and arguments
-- Returns either an error, the return value of a function,
--  or the final states of the spawned actors
interpActor :: ActorProgram -> String -> Value -> Either String [Value]
interpActor p i val = do
    (res, as', _) <- run (evalActor M.empty) env as addr
    traceM "----------------"
    traceM "All actors terminated with empty inboxes:"
    if not $ null as' then Left "Actors left hanging" else
        return $ M.elems res
    where
        env = makeDefEnv p
        addr = 1
        as = [AS 0 [] val (findActor i env)]

        findActor s env =
            case M.lookup s env of
                Just def ->
                    case def of
                        ADef a -> a
                        FDef _ -> error $ "Identifier " ++ s ++ " refers to actor not function"
                Nothing -> error $ "Function " ++ s ++ "  does not exist"

makeDefEnv :: ActorProgram -> DefEnv
makeDefEnv prog = M.fromList $ map defName prog
    where
        defName :: Def -> (String, Def)
        defName def = case def of
            ADef a -> (identifier $ actorName a, def)
            FDef (Func f _ _) -> (identifier f, def)
            FDef _ -> ("", def)

subAction :: Substitution -> Action -> Action
subAction s (Arr exp) = Arr $ subLExpr s exp
-- If any variable in arg reference in sub, then ignore
subAction s (ArrLambda arg exp) = ArrLambda arg (subExpr s' exp)
    where
        -- Delete all bound variables from substition 
        names = lExpNames arg
        s' = foldr M.delete s names
subAction s (Comp a1 a2) = Comp (subAction s a1) (subAction s a2)
subAction s (First a) = First $ subAction s a
subAction s (Second a) = Second $ subAction s a
subAction s (Proc id cmd) = Proc id (subCmd s' cmd)
    where
        s' = foldr M.delete s names
        names = lExpNames id
subAction s (ALeft a) = ALeft $ subAction s a
subAction s (ARight a) = ALeft $ subAction s a
subAction s (ABoth a1 a2) = ABoth (subAction s a1) (subAction s a2)
subAction s (AEither a1 a2) = AEither (subAction s a1) (subAction s a2)
subAction s a = a

subCmd :: Substitution -> CmdAction -> CmdAction
subCmd s (ApplyCmd a exp) = ApplyCmd (subAction s a) (subLExpr s exp)
subCmd s (KCmd exp cmd) = KCmd (subLExpr s exp) (subCmd s cmd)
subCmd s (DoCmd ds) = DoCmd (map (subDo s) ds)
subCmd s (CaseOfCmd exp cs) = CaseOfCmd (subLExpr s exp) (map (\(e, c) -> (e, subCmd (s' e) c)) cs)
    where
        s' = foldr M.delete s . lExpNames

subDo :: Substitution -> DoAction -> DoAction
subDo s (DoSeq cmd) = DoSeq $ subCmd s cmd
subDo s (DoBind exp cmd) = DoBind (subLExpr s exp) (subCmd s cmd)

subLExpr :: Substitution -> LExpr -> LExpr
subLExpr s (Var name) =
    maybe (Var name) toConst (M.lookup (identifier name) s)
    where
        toConst :: C.Value -> LExpr
        toConst (C.ConstrV id vals) = Constr (makeIdent id) (map toConst vals)
subLExpr s (Constr name exps) = Constr name (map (subLExpr s) exps)
subLExpr s (Tuple exps) = Tuple (map (subLExpr s) exps)
subLExpr s (List (ListCons exp ls)) = List (ListCons (subLExpr s exp) ls')
    where (List ls') = subLExpr s (List ls)
subLExpr s (List (ListEnd exp)) = List (ListEnd (subLExpr s exp))
subLExpr s (List ListNil) = List ListNil
subLExpr s (App name inv exps) = App name inv (map (subLExpr s) exps)
subLExpr s c = c

subExpr :: Substitution -> Expr -> Expr
subExpr s (LeftE exp) = LeftE $ subLExpr s exp
subExpr s (LetIn arg exp1 exp2) = LetIn arg (subLExpr s exp1) (subExpr s' exp2)
    where
        -- Delete all bound variables from substition 
        names = lExpNames arg
        s' = foldr M.delete s names
subExpr s (CaseOf exp cs) = CaseOf (subLExpr s exp) cs
    where
        f (arg, g, exp') = (arg, g, subExpr (s' arg) exp')
        s' arg = foldr M.delete s (names arg)
        names = lExpNames


lExpNames :: LExpr -> [String]
lExpNames (Var name) = [identifier name]
lExpNames (Tuple exps) = foldl union [] (map lExpNames exps)
lExpNames (List (ListCons exp ls)) = lExpNames exp `union` lExpNames (List ls)
lExpNames (List (ListEnd exp)) = lExpNames exp
lExpNames _ = []


-- Actually probably better to implement this as a monad
-- Due to all the side effects which can modify actor queue
-- Such as sending messages and spawning

-- Actor queue -> Next addr -> New Actor Queue
--evalActors :: [ActorState] -> Addr -> [ActorState]
--evalActors (AS addr msgs actor) nextAddr = undefined

--evalActor :: Actor -> Addr -> [ActorState]
--evalActor (Actor name _ cls) msgs nextAddr = undefined




-- An actor spawns with state, and awaits a message of type a
-- If the message type is blank (also infered from not trying to receive)
--  then the actor will run immediately and yield

-- Each actor needs:
-- * an inbox to hold messages,
-- * an ordered list of messages to match
-- * a unique address (potential two if we split send and spawn addresses)

-- Actors kept in a run queue with following strat:
-- 1. Pop first actor in queue
-- 2. If not receiving, then run its body immediately
-- 3. Else, find first message matching receive clauses
-- 4. If yields to actor, add that actor to end of queue with new state
-- 5. Else, yielding to nothing does nothing (what to do with end state?) 




