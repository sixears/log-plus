module LogPlus.Async
  ( HasAsync(..) )
where

import Base1T

-- async -------------------------------

import Control.Concurrent.Async  ( Async, wait )

--------------------------------------------------------------------------------

class HasAsync α β where
  async_      ∷ Lens' α (Async β)
  waitAsync   ∷ MonadIO μ => α → μ β
  waitAsync a = liftIO $ wait (a ⊣ async_)

----------

instance HasAsync (Async β) β where async_ = lens id (const id)

-- that's all, folks! ---------------------------------------------------------
