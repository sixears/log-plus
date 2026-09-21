module LogPlus.CompressorThread
 ( CompressorThread, HasCompressorThreadMay( compressorThreadMay ) )
where

import Base1T

-- async -------------------------------

import Control.Concurrent.Async  ( Async )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.Async  ( HasAsync( async_ ) )
import LogPlus.New    ( New( new ) )

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

------------------------------------------------------------

class HasCompressorThreadMay α where
  compressorThreadMay ∷ Lens' α (𝕄 CompressorThread)

----------

instance HasCompressorThreadMay (𝕄 CompressorThread) where
  compressorThreadMay = lens id (const id)

-- that's all, folks! ----------------------------------------------------------
