module Actor.Ast where

import Ast (LExpr, Ident, BType, Func)
import qualified Data.Map as M

type ActorProgram = [Def]

data Def   = ADef Actor
            | FDef Func
    deriving (Eq, Show)

data Action = Arr LExpr
            | Comp Action Action
            | First Action
            | Second Action
            | Send
            | Spawn Ident
            | Yield (Maybe Ident)
            | Do Ident [DoAction]
    deriving (Eq, Show)

-- Do notation
data ApplyAction = ApplyA Action LExpr
    deriving (Eq, Show)

data DoAction = DoSeq ApplyAction
              | DoBind LExpr ApplyAction
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
