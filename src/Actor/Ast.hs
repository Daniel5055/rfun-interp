module Actor.Ast where

import Ast (LExpr, Ident, BType, Func)

type ActorProgram = [Defs]

data Defs   = ADef Actor
            | FDef Func
    deriving (Eq, Show)

data Action  = Arr LExpr
            | Comp Action Action
            | First Action
            | Second Action
            | Send
            | Spawn Ident LExpr
            | Yield (Maybe Ident)
    deriving (Eq, Show)

data Actor     = Actor    {   actorName     :: Ident
                            , actorTypeSig  :: Maybe ActorType
                            , actorClause   :: [ActorClause] }
              deriving (Eq, Show)

data ActorClause  = ActorClause { aClauseIdent :: Ident
                                , aClauseMsg   :: LExpr
                                , aClauseBody  :: Action }
              deriving (Eq, Show)

data ActorType = ActorT BType BType BType
              deriving (Eq, Show)

