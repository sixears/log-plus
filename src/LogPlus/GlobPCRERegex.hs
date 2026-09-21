module LogPlus.GlobPCRERegex
  ( HasGlobPCRERegex( globPCRERegex ) )
where

import Base1T

-- monadio-plus ------------------------

import MonadIO.Directory  ( GlobPCRERegex )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

--------------------------------------------------------------------------------

class HasGlobPCRERegex α where globPCRERegex ∷ Lens' α GlobPCRERegex

-- that's all, folks! ----------------------------------------------------------
