module LogPlus.FileSizeRotator
  ( fileNumberedMoves, fileSizeRotator )
where

import Base1T

import Prelude  ( error )

-- base --------------------------------

import Data.List   ( and, reverse, zip )
import Data.Maybe  ( isJust )
import Data.Tuple  ( uncurry )
import System.IO   ( Handle )

-- base-unicode-symbols ----------------

import Data.Eq.Unicode  ( (≠) )

-- fpath -------------------------------

import qualified FPath.File

import FPath.AbsFile  ( AbsFile )

-- lens --------------------------------

import Control.Lens.Setter     ( over )
import Control.Lens.Traversal  ( both )

-- monaderror-io -----------------------

import MonadError           ( ж )
import MonadError.IO.Error  ( IOError )

-- monadio-plus ------------------------

import MonadIO.FStat        ( FExists( FExists ), lfexists )
import MonadIO.NamedHandle  ( HEncoding( NoEncoding ), ℍ
                            , handle, hClose, hname )
import MonadIO.OpenFile     ( FileOpenMode( FileW ), openFile )

-- natural -----------------------------

import Natural.Length    ( щ )
import Natural.Unsigned  ( ɨ )

-- safe --------------------------------

import Safe  ( tailSafe )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.Compressor              ( Compressor, compressorMay )
import LogPlus.CompressorThread        ( CompressorThread, compressorThreadMay
                                       , mvCompress )
import LogPlus.EMonad                  ( ꙝ )
import LogPlus.FilenameExtension       ( appendExtension )
import LogPlus.FilenameGenerator       ( filenameGenerator )
import LogPlus.FileSizeRotatorOptions  ( FileSizeRotatorOptions )
import LogPlus.FileSizeRotatorState    ( FileSizeRotatorState )
import LogPlus.ℍMay                    ( HasℍMay( 𝕙May ) )
import LogPlus.ListPlus                ( firstJust, takeWhileM )
import LogPlus.MaxFiles                ( MaxFiles, maxFiles )
import LogPlus.MaxFileSize             ( maxFileSize )
import LogPlus.New                     ( new )
import LogPlus.Perms                   ( perms )
import LogPlus.SizeBytes               ( SizeBytes, sizeBytes )
import LogPlus.ThreadIsRunning         ( ThreadIsRunning( ThreadIsRunning
                                                        , ThreadIsNotRunning )
                                       , threadIsRunning
                                       )

--------------------------------------------------------------------------------

{-| List of moves (and potentially compresses) to perform for numbered file
    rotation; this accounts for actual file existence.  This doesn't actually
    perform any destructive IO (just some `stat`s); rather provides a list of
    instructions.
-}
-- XXX how are we checking for which files need compressing?
-- XXX use EMonad and friends?

fileNumberedMoves ∷ MonadIO μ => AbsFile → FileSizeRotatorOptions → 𝕄 ℍ
                               → μ [(AbsFile, AbsFile, 𝕄 Compressor)]
fileNumberedMoves fn opts ɦ =
  let compress    = opts ⊣ compressorMay
      fngen       ∷ AbsFile → 𝕄 MaxFiles → AbsFile -- XXX
      fngen       = filenameGenerator opts
      max_files   = opts ⊣ maxFiles
      fngen' i    = maybe id appendExtension compress $ fngen fn i
      fn_nums     = 𝓙 ⊳ [0..(max_files-1)] -- -1 because we start at 0
      fn_pairs    = (over both fngen') ⊳ zip fn_nums (tailSafe fn_nums)
      abs_hname h =
        case h ⊣ hname of
          FPath.File.FileA a → a
          FPath.File.FileR r →
            error $ [fmt|relative file in hname: this should never happen %T|] r
      init_fnpair = (maybe (fngen fn 𝓝) abs_hname ɦ,fngen fn (𝓙 0),compress)
      -- `proto_moves` is the list of potential files to move, before filtering
      -- on whether they actually exist
      -- only compress when making the first archive file
      proto_moves = init_fnpair : (uncurry (,,𝓝) ⊳ (fn_pairs))
  in  flip takeWhileM proto_moves $ \ (from,_to,_do_compress) →
                                    (≡ 𝓙 FExists) ⊳⊳ ꙝ @IOError $ lfexists from

----------------------------------------

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
