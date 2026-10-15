{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
module Actor.Interp where
import Ast (Value (TupleV, IntV, FunV), LExpr (App, Var), Func (Func, funcName), makeIdent, Clause (..), Guard (Guard), Expr (CaseOf, LeftE), Ident (identifier))
import Actor.Ast
import Control.Monad (liftM, ap)
import System.Posix.Internals (rtsIsThreaded_)
import Data.Foldable (find)
import qualified Data.Map as M
import Core.Interp (evalRMatchV, evalRMatchS, Substitution, Eval, runEval, idSub, failEval)
import Interp (tcValue, tcLExpr, interp)
import Control.Applicative

type Addr = Integer
type Msg = Value

type Result = M.Map Addr Value

type DefEnv = M.Map String Def

data ActorState = AS { aAddr :: Addr, aInbox :: [Msg], aState :: Value, aActor :: Actor }

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
        rt _ as n =
            case send' as addr msg of
                Just as' -> Right ((addr, msg), as', n)
                Nothing -> Left "Actor at address does not exist"

send' :: [ActorState] -> Addr -> Msg -> Maybe [ActorState]
send' (a:as) addr msg
    | aAddr a == addr = Just (a { aInbox = aInbox a ++ [msg] }:as)
    | otherwise = (a:) <$> send' as addr msg

receive :: Runtime (ActorState, ActorClause, Substitution)
receive = Runtime rt
    where rt env as n = let (state, ac, s, as') = matchActor as in Right ((state, ac, s), as', n)

lookupFunc :: String -> Runtime Func
lookupFunc s = Runtime rt
    where
        rt env as addr = (,as,addr) <$> findFunc (s) env
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
        rt env as addr = (,as,addr) <$> findActor (s) env
        findActor s env =
            case M.lookup s env of
                Just def ->
                    case def of 
                        ADef a -> Right a
                        FDef _ -> Left $ "Identifier " ++ s ++ " refers to actor not function"
                Nothing -> Left $ "Function " ++ s ++ "  does not exist"
            

matchActor :: [ActorState] -> (ActorState, ActorClause, Substitution, [ActorState])
matchActor (actorState@(AS addr inbox state actor):as) =
    case res of
        Right ((ms, ac, s), _) -> (actorState, ac, s, as)
        Left _ -> (nAs, nAc, nSub, actorState:nAss)

    where
        res = runEval $ matchMessages (inbox) (actorClause actor)
        (nAs, nAc, nSub, nAss) = matchActor as
matchActor [] = error "Program stalled, no matching messages for remaining actors"


matchMessages :: [Msg] -> [ActorClause] -> Eval ([Msg], ActorClause, Substitution)
matchMessages (m:ms) acs = ((\(ac, s) -> (ms, ac, s)) <$>  matchClauses m acs) <|> matchMessages ms acs
matchMessages [] acs = failEval "No matching messages"

matchClauses :: Msg -> [ActorClause] -> Eval (ActorClause, Substitution)
matchClauses msg (ac:acs) = do
        let pat = tcLExpr $ aClauseMsg ac
        let val = tcValue msg
        ((ac,) <$> evalRMatchS val pat) <|> matchClauses msg acs

matchClauses msg [] = failEval "No matching clauses"

evalActor :: Result -> Runtime Result 
evalActor res = do
    (as, ac, sub) <- receive
    (TupleV [FunV f, val]) <- evalAction (aClauseBody ac) (aState as)
    if f == "" then evalActor $ M.insert (aAddr as) val res else do
        actor <- lookupActor f
        yield as{ aState = val, aActor = actor }
        evalActor res 

-- Evaluate runtime unitl it resolves to list of final actor states
evalAction :: forall s.  Action -> Value -> Runtime Value 
evalAction Send (TupleV [IntV addr, msg]) = 
    send addr msg >> return (TupleV [IntV addr, msg])
evalAction Send _ = 
    runtimeError "send expects two arguments, address and message"

evalAction (Arr (App name inv args)) val = do
    case interp [Func (makeIdent "f") Nothing [Clause (makeIdent "f") [Var (makeIdent "_x")] (Guard []) (LeftE (App name inv (args++[Var (makeIdent "_x")])))]] "f" ([val]) of
        Right v -> return v
        Left s -> runtimeError s
    
evalAction (Comp a1 a2) val = evalAction a1 val >>= evalAction a2

evalAction (First a) (TupleV [v1, v2]) = do
    v3 <- evalAction a v1
    return $ TupleV [v3, v2]
evalAction (First a) _ =
    runtimeError "Expected 2-tuple value to `first` arrow"

evalAction (Second a) (TupleV [v1, v2]) = do
    v3 <- evalAction a v2
    return $ TupleV [v1, v3]
evalAction (Second a) _ =
    runtimeError "Expected 2-tuple value to `second` arrow"

evalAction (Spawn name) val = do
    a <- lookupActor (identifier name)
    IntV <$> spawn a val 

evalAction (Yield (Just name)) val = return $ (TupleV [FunV (identifier name), val])
evalAction (Yield Nothing) val = return $ TupleV [FunV "", val]

-- Accepts a program, function or actor to run, and arguments
-- Returns either an error, the return value of a function,
--  or the final states of the spawned actors
interpActor :: ActorProgram -> String -> Value -> Either String [Value]
interpActor p i val = do
    (res, as', _) <- run (evalActor M.empty) env as addr
    if not $ null as then Left "Actors left hanging" else
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
makeDefEnv prog = M.fromList $ map (\def -> defName def) prog
    where
        defName :: Def -> (String, Def)
        defName def = case def of
            ADef a -> (identifier $ actorName a, def)
            FDef (Func f _ _) -> (identifier $ f, def)
            FDef _ -> ("", def)
    

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




