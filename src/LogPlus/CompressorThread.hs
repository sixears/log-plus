module LogPlus.CompressorThread
 ( CompressorThread, HasCompressorThreadMay( compressorThreadMay )
 , asyncCompressorThread, mvCompress )
where

import Base1T

-- async -------------------------------

import Control.Concurrent.Async  ( Async, async )

-- fpath -------------------------------

import FPath.AbsFile   ( AbsFile )
import FPath.FileLike  ( (⊙) )

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

import LogPlus.Async              ( HasAsync( async_ ) )
import LogPlus.Compressor         ( Compressor )
import LogPlus.CompressorIO       ( HasCompressorIO( compressorIOF ) )
import LogPlus.EMonad             ( ꙝ' )
import LogPlus.FilenameExtension  ( HasFilenameExtension( filenameExtensionPC ))
import LogPlus.New                ( New( new ) )

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

{-| spawn a thread that runs a compressor, and fixes up the file permissions
    after -}
asyncCompressorThread ∷ (MonadIO μ, HasCompressorIO δ, HasFilenameExtension δ) =>
                        δ → FileMode → AbsFile → μ CompressorThread
asyncCompressorThread c file_perms to = liftIO $
  let c' ∷ AbsFile → AbsFile → IO ()
      c' = \ from_ to_ → do (c ⊣ compressorIOF) from_ to_
                            ж $ chmod @IOError file_perms to_
      ext = c ⊣ filenameExtensionPC
  in  new ⊳ async (c' to (to⊙ext))

-- that's all, folks! ----------------------------------------------------------
