module LogPlus.SizeBytes
  ( HasSizeBytes(..), SizeBytes )
where

import Base1T

-- base --------------------------------

import GHC.Enum  ( Enum )
import GHC.Num   ( Num )
import GHC.Real  ( Integral, Real )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.New  ( New( new ) )

--------------------------------------------------------------------------------

newtype SizeBytes = SizeBytes Word64
  deriving (Enum,Eq,Integral,Num,Ord,Real,Show)

----------

instance New SizeBytes Word64  where  new = SizeBytes

----------------------------------------

class    HasSizeBytes α          where  sizeBytes ∷ Lens' α SizeBytes
instance HasSizeBytes SizeBytes  where  sizeBytes = lens id (const id)

-- that's all, folks! ----------------------------------------------------------
