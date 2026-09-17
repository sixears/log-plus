module LogPlus.MaxFileSize
  ( HasMaxFileSize(..), MaxFileSize )
where

import Base1T

-- base --------------------------------

import GHC.Num  ( Num )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.New        ( New( new ) )
import LogPlus.SizeBytes  ( HasSizeBytes( sizeBytes ), SizeBytes )

--------------------------------------------------------------------------------

newtype MaxFileSize = MaxFileSize { unMaxFileSize ∷ SizeBytes }
  deriving  (Num,Show)

----------

instance New MaxFileSize SizeBytes where new = MaxFileSize

----------

instance New MaxFileSize Word64 where new = MaxFileSize ∘ new

----------

instance HasSizeBytes MaxFileSize where
  sizeBytes = lens unMaxFileSize (\ _ z → MaxFileSize z)

------------------------------------------------------------

class    HasMaxFileSize α            where  maxFileSize ∷ Lens' α MaxFileSize
instance HasMaxFileSize MaxFileSize  where  maxFileSize = lens id (const id)


-- that's all, folks! ----------------------------------------------------------
