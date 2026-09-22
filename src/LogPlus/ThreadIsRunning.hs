module LogPlus.ThreadIsRunning
  ( ThreadIsRunning(..), threadIsRunning )
where

import Base1T

-- async -------------------------------

import Control.Concurrent.Async  ( Async, poll )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.Async  ( HasAsync( async_ ) )

--------------------------------------------------------------------------------

data ThreadIsRunning = ThreadIsRunning | ThreadIsNotRunning deriving (Eq, Show)

----------------------------------------

threadIsRunning ∷ ∀ δ m . (MonadIO m, HasAsync δ ()) => δ -> m ThreadIsRunning
threadIsRunning x = liftIO $
  let a ∷ Async () = x ⊣ async_
  in  poll a≫ \ case
    𝓝   → return ThreadIsRunning
    𝓙 _ → return ThreadIsNotRunning

-- that's all, folks! ----------------------------------------------------------
