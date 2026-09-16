module LogPlus.HasUTCTime
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
  utcTimeY ∷ Lens' α (Maybe UTCTime)

instance HasUTCTimeY (Maybe UTCTime) where
  utcTimeY = id

-- that's all, folks! ----------------------------------------------------------
