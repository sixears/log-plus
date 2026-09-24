module LogPlus.FileSizeRotator
  ( fileSizeRotator )
where

import Base1T

-- base --------------------------------

import Data.List   ( and, reverse )
import Data.Maybe  ( isJust )
import System.IO   ( Handle )

-- base-unicode-symbols ----------------

import Data.Eq.Unicode  ( (≠) )

-- fpath -------------------------------

import FPath.AbsFile  ( AbsFile )

-- monaderror-io -----------------------

import MonadError           ( ж )
import MonadError.IO.Error  ( IOError )

-- monadio-plus ------------------------

import MonadIO.NamedHandle  ( HEncoding( NoEncoding ), ℍ
                            , handle, hClose )
import MonadIO.OpenFile     ( FileOpenMode( FileW ), openFile )

-- natural -----------------------------

import Natural.Length    ( щ )
import Natural.Unsigned  ( ɨ )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.Compressor              ( fileNumberedMoves )
import LogPlus.CompressorThread        ( CompressorThread, compressorThreadMay
                                       , mvCompress )
import LogPlus.FilenameGenerator       ( FilenameGenerator( filenameGenerator ))
import LogPlus.FileSizeRotatorOptions  ( FileSizeRotatorOptions )
import LogPlus.FileSizeRotatorState    ( FileSizeRotatorState )
import LogPlus.ℍMay                    ( 𝕙May )
import LogPlus.ListPlus                ( firstJust )
import LogPlus.MaxFiles                ( MaxFiles )
import LogPlus.MaxFileSize             ( maxFileSize )
import LogPlus.New                     ( new )
import LogPlus.Perms                   ( perms )
import LogPlus.SizeBytes               ( SizeBytes, sizeBytes )
import LogPlus.ThreadIsRunning         ( ThreadIsRunning( ThreadIsRunning
                                                        , ThreadIsNotRunning )
                                       , threadIsRunning
                                       )

--------------------------------------------------------------------------------

-- XXX what happens if we start logging to an extant file?
-- XXX use EMonad and friends?
fileSizeRotator ∷ ∀ ω μ . MonadIO μ =>
                  FileSizeRotatorOptions
                → AbsFile                -- ^ base filename (passed to `fngen`)
                → 𝕄 FileSizeRotatorState -- ^ incoming state; should be 𝓝 at
                                         --   first, will be self-managed for
                                         --   recursion
                → ω                      -- ^ SimpleDocStream (unused)
                → 𝕋                      -- ^ rendered text to write (used to
                                         --   calculate whether to rotate)
                → μ (Handle, FileSizeRotatorState) -- ^ new handle & state

fileSizeRotator opts fn st_ _sds t = do
  let st          = st_ ⧏ def
      l           = new @SizeBytes @Word64 (ɨ $ щ t) -- length of t
      bytes_would = (st ⊣ sizeBytes) + l
      -- create a new handle, return a thread reference for the compressor if
      -- used to compress the old one
      mkhandle    ∷ μ (ℍ, 𝕄 CompressorThread)
      mkhandle    = do
        mv_files ← fileNumberedMoves fn opts (st ⊣ 𝕙May)
        compressor_thread ← liftIO$ firstJust ⊳ forM (reverse mv_files)
                                                     (mvCompress $ opts ⊣ perms)
        let -- open a file, mode 0644, raise if it fails
            open_file ∷ MonadIO μ => AbsFile → μ ℍ
            open_file =
              ж ∘ openFile @IOError NoEncoding (FileW ∘ 𝓙 $ opts ⊣ perms)
        ẖ ∷ ℍ ← open_file ((filenameGenerator opts) fn (𝓝∷𝕄 MaxFiles))
        return (ẖ, compressor_thread)

  -- is there a compressor currently running?
  thread_is_running ← liftIO $ case st ⊣ compressorThreadMay of
                                 𝓝   → return ThreadIsNotRunning
                                 𝓙 ŧ → threadIsRunning ŧ
  case st ⊣ 𝕙May of
    𝓙 𝕙 → if and [ -- no extant thread
                   thread_is_running ≠ ThreadIsRunning
                 , -- we don't want empty files
                   (st ⊣ sizeBytes) ≠ 0
                 , -- extant file too big
                   bytes_would > opts ⊣ maxFileSize ∘ sizeBytes
                 ]
          then do -- time to make a new handle
            hClose 𝕙
            (𝕙',ṯ) ← mkhandle
            return (𝕙' ⊣ handle, new (𝕙',l,ṯ))
          else -- just return the extant handle
            if and [ thread_is_running ≡ ThreadIsNotRunning
                   , isJust $ st ⊣ compressorThreadMay ]
            then -- update bytes written; and dump the thread (it's now done)
                 return (𝕙 ⊣ handle,st & sizeBytes           ⊢ bytes_would
                                       & compressorThreadMay ⊢ 𝓝)
            else -- just update the bytes written
                 return (𝕙 ⊣ handle,st & sizeBytes ⊢ bytes_would)

    𝓝   → -- no extant handle, so create one
           mkhandle ≫ \ (𝕙',ṯ) → return (𝕙' ⊣ handle, new (𝕙',l,ṯ))

-- that's all, folks! ----------------------------------------------------------
