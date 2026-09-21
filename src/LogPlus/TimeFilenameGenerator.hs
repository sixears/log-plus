module LogPlus.TimeFilenameGenerator
  ( TimeFilenameGenerator, TimeFnGen, dayFilenameGenerator )
where

import Base1T

-- fpath -------------------------------

import FPath.Parseable      ( __parseS__ )
import FPath.PathComponent  ( PathComponent )

-- time --------------------------------

import Data.Time.Format  ( FormatTime, defaultTimeLocale, formatTime )

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

------------------------------------------------------------

{-| a simple time generator, which adds the date to the end of a filename -}
dayFilenameGenerator ∷ ∀ τ . (FormatTime τ, Show τ) => TimeFilenameGenerator τ
dayFilenameGenerator =
  let formatDate  = formatTime defaultTimeLocale "-%Y-%m-%d"
      pcDate      = __parseS__ ∘ formatDate
      pcGen pc_ d = pc_ ◇ pcDate d
      name_       = "dayFilenameGenerator"
  in  new @(TimeFilenameGenerator τ) @(𝕊,TimeFnGen τ) (name_,pcGen)

-- that's all, folks! ----------------------------------------------------------
