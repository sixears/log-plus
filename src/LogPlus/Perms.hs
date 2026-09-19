module LogPlus.Perms
  ( HasPerms( perms ) )
where

import Base1T

-- unix --------------------------------

import System.Posix.Types  ( FileMode )

--------------------------------------------------------------------------------

class HasPerms α where perms ∷ Lens' α FileMode

-- that's all, folks! ----------------------------------------------------------
