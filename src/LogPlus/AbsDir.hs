{- XXX Move this to FPath, create instances for all main types there (incl.
       File, Dir, FPath) -}

module LogPlus.AbsDir
  ( HasAbsDir( absDir_ ) )
where

import Base1T

-- fpath -------------------------------

import FPath.AbsDir  ( AbsDir )

--------------------------------------------------------------------------------

class    HasAbsDir α      where absDir_ ∷ Lens' α AbsDir
instance HasAbsDir AbsDir where absDir_ = lens id (const id)

-- that's all, folks! ----------------------------------------------------------
