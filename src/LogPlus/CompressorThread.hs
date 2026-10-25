module LogPlus.CompressorThread
 ( CompressorThread, HasCompressorThreadMay( compressorThreadMay )
 , asyncCompressorThread, mvCompress )
where

import Base1T

-- async -------------------------------

import Control.Concurrent.Async  ( Async, async )

-- base-plus ---------------------------

import BasePlus.Async   ( HasAsync( async_ ) )
import BasePlus.EMonad  ( ꙝ' )
import BasePlus.New     ( New( new ) )

-- fpath -------------------------------

import FPath.AbsFile            ( AbsFile, HasAbsFile( absFile ) )
import FPath.FileLike           ( (⊙) )
import FPath.FilenameExtension  ( HasFilenameExtension( filenameExtension ) )

-- monaderror-io -----------------------

import MonadError           ( ж )
import MonadError.IO.Error  ( IOError )

-- monadio-plus ------------------------

import MonadIO.File  ( chmod, rename )

-- unix --------------------------------

import System.Posix.Types  ( FileMode )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.Compressor    ( Compressor )
import LogPlus.CompressorIO  ( HasCompressorIO( compressorIOF ) )

--------------------------------------------------------------------------------

data CompressorThread = CompressorThread { _compressorThread ∷ Async ()
                                         , _fname            ∷ AbsFile
                                           -- ^ name of the file being
                                           --   compressed
                                         }

----------

instance New CompressorThread (Async (), AbsFile) where
  new (as,fn) = CompressorThread as fn

----------

instance Show CompressorThread where
  show ct = [fmt|CompressorThread (%T)|] (_fname ct)

----------

instance HasAsync CompressorThread () where
  async_ = lens _compressorThread (\ ct as → ct { _compressorThread = as })

----------

instance HasAbsFile CompressorThread where
  absFile = lens _fname (\ ct fn → ct { _fname = fn })

------------------------------------------------------------

class HasCompressorThreadMay α where
  compressorThreadMay ∷ Lens' α (𝕄 CompressorThread)

----------

instance HasCompressorThreadMay (𝕄 CompressorThread) where
  compressorThreadMay = lens id (const id)

------------------------------------------------------------

{-| Move, and optionally compress, a file.

    Rename `from` to `to`, compressing it with `compress` if that is not
    `Nothing`. If the compressor is initiated, it is fired off in a separate
    thread, and the `ThreadId` is returned.  Once the compressor is complete, we
    `chmod` the resultant file to `file_perms`.  We do not `chmod` the `to` file
    if there is no compressor.
-}
mvCompress ∷ FileMode → (AbsFile,AbsFile,𝕄 Compressor) → IO (𝕄 CompressorThread)
mvCompress file_perms (from,to,do_compress) = do
  ꙝ' $ rename @IOError from to
  case do_compress of
    𝓝   → return 𝓝
    𝓙 c → 𝓙 ⊳ asyncCompressorThread c file_perms to

----------------------------------------

{-| Spawn a thread that runs a compressor, and fixes up the file permissions
    after.  We have to do it like this because most compressors don't allow us
    to specify the perms of the target file
 -}
asyncCompressorThread ∷ (MonadIO μ, HasCompressorIO δ, HasFilenameExtension δ)=>
                        δ → FileMode → AbsFile → μ CompressorThread
asyncCompressorThread c file_perms from = liftIO $ do
  let c' ∷ AbsFile → AbsFile → IO ()
      c' = \ from_ to_ → do (c ⊣ compressorIOF) from_ to_
                            ж $ chmod @IOError file_perms to_
      ext = c ⊣ filenameExtension
  as ← async (c' from (from⊙ext))
  return $ CompressorThread as from

-- that's all, folks! ----------------------------------------------------------
