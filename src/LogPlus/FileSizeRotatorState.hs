module LogPlus.FileSizeRotatorState
  ( FileSizeRotatorState )
where

import Base1T

-- monadio-plus ------------------------

import MonadIO.NamedHandle  ( ℍ )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.CompressorThread  ( CompressorThread
                                 , HasCompressorThreadMay(compressorThreadMay) )
import LogPlus.HMay              ( HasℍMay( 𝕙May ) )
import LogPlus.New               ( New( new ) )
import LogPlus.SizeBytes         ( SizeBytes, HasSizeBytes( sizeBytes ) )

--------------------------------------------------------------------------------

{-| intermediate state for logging to a file which is rotated by size -}

data FileSizeRotatorState =
  FileSizeRotatorState { -- ^ current filehandle to which logs are being written
                         _fsrst_handle  ∷ 𝕄 ℍ
                       , -- ^ size of the file that we are writing to
                         _fsrst_size    ∷ SizeBytes
                       , -- ^ thread of the last compressor that we kicked off
                         _fsrst_cmpthrd ∷ 𝕄 CompressorThread
                       }
  deriving Show

----------

instance Default FileSizeRotatorState where def = FileSizeRotatorState 𝓝 0 𝓝

----------

instance HasℍMay FileSizeRotatorState where
  𝕙May = lens _fsrst_handle (\ f h → f { _fsrst_handle = h })

----------

instance HasSizeBytes FileSizeRotatorState where
  sizeBytes = lens _fsrst_size (\ f s → f { _fsrst_size = s })

----------

instance HasCompressorThreadMay FileSizeRotatorState where
  compressorThreadMay = lens _fsrst_cmpthrd (\ f t → f { _fsrst_cmpthrd = t })

----------

instance New FileSizeRotatorState (𝕄 ℍ,  SizeBytes,𝕄 CompressorThread) where
  new (h,s,t) = FileSizeRotatorState h s t

----------

instance New FileSizeRotatorState (ℍ,  SizeBytes,𝕄 CompressorThread) where
  new (h,s,t) = FileSizeRotatorState (𝓙 h) s t

-- that's all, folks! ----------------------------------------------------------
