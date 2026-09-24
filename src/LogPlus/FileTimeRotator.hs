module LogPlus.FileTimeRotator
  ( fileTimeRotator, fileTimeRotator_ )
where

import Base1T

-- base --------------------------------

import Data.List   ( and )
import Data.Maybe  ( isJust )
import System.IO   ( Handle )

-- base-unicode-symbols ----------------

import Data.Eq.Unicode  ( (≠) )

-- fpath -------------------------------

import FPath                   ( (⫻) )
import FPath.AbsFile           ( AbsFile )
import FPath.Basename          ( basename )
import FPath.Error.FPathError  ( FPathIOError )
import FPath.PathComponent     ( PathComponent )
import FPath.RelFile           ( _RelFile_ )

-- lens --------------------------------

import Control.Lens.Getter  ( view )
import Control.Lens.Review  ( re )

-- monaderror-io -----------------------

import MonadError           ( ж )
import MonadError.IO.Error  ( IOError )

-- monadio-plus ------------------------

import MonadIO.File         ( unlink )
import MonadIO.NamedHandle  ( HEncoding( NoEncoding ), ℍ
                            , handle, hClose, hname )
import MonadIO.OpenFile     ( FileOpenMode( FileW ), openFile )

-- time --------------------------------

import Data.Time.Clock  ( UTCTime, getCurrentTime )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.AbsDir                  ( absDir_ )
import LogPlus.Compressor              ( fileCompressClean )
import LogPlus.CompressorThread        ( CompressorThread, asyncCompressorThread
                                       , compressorThreadMay )
import LogPlus.FilenameGenerator       ( FilenameGenerator( filenameGenerator ))
import LogPlus.FileTimeRotatorOptions  ( FileTimeRotatorOptions )
import LogPlus.FileTimeRotatorState    ( FileTimeRotatorState )
import LogPlus.ℍMay                    ( 𝕙May )
import LogPlus.New                     ( new )
import LogPlus.Perms                   ( perms )
import LogPlus.StdErr                  ( stdErrT )
import LogPlus.ThreadIsRunning         ( ThreadIsRunning( ThreadIsRunning
                                                        , ThreadIsNotRunning )
                                       , threadIsRunning
                                       )

--------------------------------------------------------------------------------

{-| Log to a file, which is rotated at a given date.

    Every time we're about to write a log, we check to see the `Day` of the
    supplied time, and if it's a later `Day` than the current log file being
    written to, we roll the log and potentially compress the old one.

    State (σ) is (current handle in use, filename corresponding to that handle,
    threadId of last-run compressor).
-}

-- τ is the time type, e.g. `Data.Time.Clock.UTCTime` or
-- `Data.Time.LocalTime.LocalTime`

-- XXX what happens if we start logging to an extant file?
-- XXX use EMonad and friends?
fileTimeRotator_ ∷ ∀ τ ω μ . MonadIO μ =>
                   FileTimeRotatorOptions τ
                 → -- | basename of the file to use for logging to; e.g.,
                   --   [pathComponent|logfile|]
                   PathComponent
                 → -- | time of the log (pulling it out of the log message(s) is
                   --   hard, and it's unclear how to handle groups of messages:
                   --   use the latest or the earliest? - and this makes testing
                   --   easier, so we hand in an explicit time; use, e.g.,
                   --   `Data.Time.Clock.UTCTime` or
                   --   `Data.Time.LocalTime.LocalTime`
                   τ
                 → -- | incoming state; should be 𝓝 at first, will be
                   --   self-managed for recursion
                   𝕄 FileTimeRotatorState
                 → ω -- ^ SimpleDocStream (unused)
                 → 𝕋 -- ^ rendered text to write (unused)
                 → μ (Handle,FileTimeRotatorState) -- ^ new handle & state


fileTimeRotator_ opts pc_ d st_ _sds _t = do
  let st = st_ ⧏ def
      -- type sig required to disambiguate
      pc' ∷ PathComponent
      pc' = (filenameGenerator opts) pc_ d
      fn = opts ⊣ absDir_ ⫻ pc' ⊣ re _RelFile_
      cur_pc = basename ∘ view hname ⊳ (st ⊣ 𝕙May) ≫ (⩼ _RelFile_)

      mkhandle    ∷ AbsFile → μ (ℍ, 𝕄 CompressorThread)
      mkhandle afn  = do
        (cmprs,rms) ← ѥ (fileCompressClean opts) ≫ \ case
          𝓡 (cmprs,rms) → return (cmprs,rms)
          𝓛 (e ∷ FPathIOError) → do
            stdErrT $ [fmt|error compressing/cleaning old logs: %T|] e
            return (𝓝,[])
        forM_ rms $ \ f → ѥ @IOError (unlink f) ≫ \ case
                            𝓡 () → return ()
                            𝓛 e  → stdErrT $ [fmt|error unlinking %T: %T|] f e

        compressor_thread ← case cmprs of
          𝓝         → return 𝓝
          𝓙 (fn',c) →
            𝓙 ⊳ asyncCompressorThread c (opts ⊣ perms) fn'

        let -- open a file, mode 0644, raise if it fails
            open_file ∷ MonadIO μ => AbsFile → μ ℍ
            open_file =
              ж ∘ openFile @IOError NoEncoding (FileW ∘ 𝓙 $ opts ⊣ perms)
        ẖ ∷ ℍ ← open_file afn
        return (ẖ, compressor_thread)

  -- is there a compressor currently running?
  thread_is_running ← liftIO $ case st ⊣ compressorThreadMay of
                                 𝓝   → return ThreadIsNotRunning
                                 𝓙 ŧ → threadIsRunning ŧ

  case st ⊣ 𝕙May of
    𝓙 𝕙 → if and [ -- no extant thread
                   thread_is_running ≠ ThreadIsRunning
                   -- new filename is called for
                 , 𝓙 pc' ≠ cur_pc
                 ]
          then do -- time to make a new handle
            hClose 𝕙
            (𝕙',ṯ) ← mkhandle fn
            return (𝕙' ⊣ handle, new (𝕙',ṯ))
          else -- just return the extant handle
            if and [ thread_is_running ≡ ThreadIsNotRunning
                   , isJust $ st ⊣ compressorThreadMay ]
            then -- dump the thread (it's now done)
                 return (𝕙 ⊣ handle,st & compressorThreadMay ⊢ 𝓝)
            else return (𝕙 ⊣ handle,st)

    𝓝   → -- no extant handle, so create one
           mkhandle fn ≫ \ (𝕙',ṯ) → return (𝕙' ⊣ handle, new (𝕙',ṯ))

--------------------

fileTimeRotator ∷ MonadIO μ =>
                  FileTimeRotatorOptions UTCTime
                → PathComponent
                → 𝕄 FileTimeRotatorState
                → ω
                → 𝕋
                → μ (Handle, FileTimeRotatorState)

fileTimeRotator o p s w t =
  liftIO getCurrentTime ≫ \ d → fileTimeRotator_ o p d s w t

-- that's all, folks! ----------------------------------------------------------
