{- XXX move this to base-plus?  or Base1? or somewhere?   Rename `-Y` to `-May`-}

module LogPlus.UTCTime
  ( HasUTCTime( utcTime ), HasUTCTimeY( utcTimeY ) )
where

import Base1T

-- time --------------------------------

import Data.Time.Clock  ( UTCTime )

--------------------------------------------------------------------------------

class HasUTCTime α where
  utcTime ∷ Lens' α UTCTime

instance HasUTCTime UTCTime where
  utcTime = id

------------------------------------------------------------

class HasUTCTimeY α where
  utcTimeY ∷ Lens' α (𝕄 UTCTime)

instance HasUTCTimeY (𝕄 UTCTime) where
  utcTimeY = id

-- that's all, folks! ----------------------------------------------------------
