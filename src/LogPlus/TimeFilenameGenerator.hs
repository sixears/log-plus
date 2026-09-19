module LogPlus.TimeFilenameGenerator
  ( TimeFilenameGenerator, TimeFnGen )
where

import Base1T

-- fpath -------------------------------

import FPath.PathComponent  ( PathComponent )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.FilenameGenerator  ( FilenameGenerator( filenameGenerator ) )
import LogPlus.New                ( New( new ) )

--------------------------------------------------------------------------------

type TimeFnGen τ = PathComponent → τ → PathComponent

data TimeFilenameGenerator τ =
  TimeFilenameGenerator
    { _tfg_name ∷ 𝕊 -- ^ just for `Show`
    , _tfg_fngen ∷ TimeFnGen τ }

----------

instance Show (TimeFilenameGenerator τ) where
  show = _tfg_name

----------

instance New (TimeFilenameGenerator τ) (𝕊, TimeFnGen τ) where
  new (s,g) = TimeFilenameGenerator s g

----------

instance FilenameGenerator (TimeFilenameGenerator τ) (TimeFnGen τ) where
  filenameGenerator = _tfg_fngen

-- that's all, folks! ----------------------------------------------------------
