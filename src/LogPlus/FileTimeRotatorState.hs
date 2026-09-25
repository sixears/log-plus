module LogPlus.FileTimeRotatorState
  ( FileTimeRotatorState )
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

--------------------------------------------------------------------------------

{-| intermediate state for logging to a file which is rotated by time -}

data FileTimeRotatorState =
  FileTimeRotatorState { -- ^ current filehandle to which logs are being written
                         _ftrst_handle   ∷ 𝕄 ℍ
                       , -- ^ thread of the last compressor that we kicked off
                         _ftrst_cmpthrd  ∷ 𝕄 CompressorThread
                       }
  deriving Show

----------

instance Default FileTimeRotatorState where def = FileTimeRotatorState 𝓝 𝓝

----------

instance HasℍMay FileTimeRotatorState where
  𝕙May = lens _ftrst_handle (\ f h → f { _ftrst_handle = h })

----------

instance HasCompressorThreadMay FileTimeRotatorState where
  compressorThreadMay = lens _ftrst_cmpthrd (\ f t → f { _ftrst_cmpthrd = t })

----------

instance New FileTimeRotatorState (ℍ, 𝕄 CompressorThread) where
  new (h,t) = FileTimeRotatorState (𝓙 h) t

-- that's all, folks! ----------------------------------------------------------
