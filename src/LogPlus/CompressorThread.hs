module LogPlus.CompressorThread
 ( CompressorThread )
where

import Base1T

-- async -------------------------------

import Control.Concurrent.Async  ( Async )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.HasAsync  ( HasAsync( async_ ) )
import LogPlus.New       ( New( new ) )

--------------------------------------------------------------------------------

newtype CompressorThread = CompressorThread { unCompressorThread ∷ Async () }

----------

instance New CompressorThread (Async ()) where
  new = CompressorThread

----------

instance HasAsync CompressorThread () where
  async_ = lens unCompressorThread (const CompressorThread)

----------

instance Show CompressorThread where show _ = "CompressorThread"

-- that's all, folks! ----------------------------------------------------------
