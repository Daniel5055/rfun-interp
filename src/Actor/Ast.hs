module Actor.Ast where

import Ast (LExpr, Ident, BType, Func, Expr)
import qualified Data.Map as M

type ActorProgram = [Def]

data Def   = ADef Actor
            | FDef Func
    deriving (Eq, Show)

data Action = Arr LExpr
            | ArrLambda LExpr Expr
            | Comp Action Action
            | First Action
            | Second Action
            | Send Bool LExpr
            | Spawn Bool Ident
            | Yield (Maybe Ident)

            -- Proc notation
            | Proc LExpr CmdAction

            -- Arrow Choice
            | ALeft Action
            | ARight Action
            | ABoth Action Action
            | AEither Action Action
    deriving (Eq, Show)

-- Do notation
data CmdAction = ApplyCmd Action LExpr
               | KCmd LExpr CmdAction
               | DoCmd [DoAction]
               | CaseOfCmd LExpr [(LExpr, CmdAction)]
    deriving (Eq, Show)

data DoAction = DoSeq CmdAction
              | DoBind LExpr CmdAction
    deriving (Eq, Show)

data Actor     = Actor    {   actorName     :: Ident
                            , actorTypeSig  :: Maybe ActorType
                            , actorClause   :: [ActorClause] }
              deriving (Eq, Show)

data ActorClause  = ActorClause { aClauseIdent :: Ident
                                , aClauseMsg   :: LExpr
                                , aClauseBody  :: Action }
              deriving (Eq, Show)

data ActorType = ActorT BType BType
              deriving (Eq, Show)

type DefEnv = M.Map String Def
