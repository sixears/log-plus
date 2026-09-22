module LogPlus.Compressor
  ( Compressor, HasCompressorMay( compressorMay )
  , compressPzstd, fileCompressClean, fileNumberedMoves )
where

import Base1T

import Prelude  ( error )

-- base --------------------------------

import Data.List   ( sort, zip )
import Data.Tuple  ( uncurry )

-- extra -------------------------------

import Data.List.Extra  ( dropEnd )

-- natural -----------------------------

import Natural  ( (⊟) )

-- fpath -------------------------------

import qualified FPath.File

import FPath.AbsFile        ( AbsFile )
import FPath.Error.FPathError  ( AsFPathError, FPathIOError )
import FPath.PathComponent  ( pc )

-- lens --------------------------------

import Control.Lens.Getter     ( view )
import Control.Lens.Setter     ( over )
import Control.Lens.Traversal  ( both )

-- monaderror-io -----------------------

import MonadError.IO.Error  ( IOError )

-- monadio-plus ------------------------

import MonadIO.Directory              ( glob )
import MonadIO.File                   ( devnull )
import MonadIO.FStat                  ( FExists( FExists ), lfexists )
import MonadIO.Error.CreateProcError  ( ProcError )
import MonadIO.NamedHandle            ( ℍ, hname )
import MonadIO.Process                ( doProc )
import MonadIO.Process.CmdSpec        ( mkCmd )

-- safe --------------------------------

import Safe  ( lastMay, tailSafe )

------------------------------------------------------------
--                     local imports                       -
------------------------------------------------------------

import LogPlus.AbsDir             ( HasAbsDir( absDir_ ) )
import LogPlus.CompressorIO       ( CompressorIO,HasCompressorIO(compressorIO) )
import LogPlus.EMonad                  ( ꙝ )
import LogPlus.FilenameExtension  ( FilenameExtension
                                  , HasFilenameExtension( filenameExtension
                                                        , filenameExtensionPC )
                                  , appendExtension )
import LogPlus.FilenameGenerator  ( FilenameGenerator( filenameGenerator ))
import LogPlus.GlobPCRERegex      ( HasGlobPCRERegex( globPCRERegex ) )
import LogPlus.ListPlus           ( takeWhileM )
import LogPlus.MaxFiles           ( MaxFiles, HasMaxFiles(maxFiles, maxFiles16))
import LogPlus.Name               ( HasName( name, nameS ), Name )
import LogPlus.New                ( New( new ) )
import LogPlus.StdErr             ( eToStderrIO, stdErrT )

import LogPlus.Paths  qualified as  Paths

--------------------------------------------------------------------------------

{-| a way of compressing files -}
data Compressor = Compressor { -- | name purely for printing (`Show`) purposes
                               _cmp_name ∷ Name
                             , -- | takes from,to filenames and does the deed
                               _cmp_cmpr ∷ CompressorIO
                             , -- | filename extension to append (after a `.`)
                               _cmp_ext  ∷ FilenameExtension
                             }

----------

instance New Compressor (Name,CompressorIO,FilenameExtension) where
  new (n,io,fe) = Compressor n io fe

----------

instance Show Compressor where
  show c = let e = toString ∘ view filenameExtensionPC $ _cmp_ext c
           in  [fmt|Compressor: '%s' «%s»|] (c ⊣ nameS) e

----------

instance HasName Compressor where
  name = lens _cmp_name (\ c n → c { _cmp_name = n })

----------

instance HasCompressorIO Compressor where
  compressorIO = lens _cmp_cmpr (\ c x → c { _cmp_cmpr = x })

----------

instance HasFilenameExtension Compressor where
  filenameExtension = lens _cmp_ext (\ c x → c { _cmp_ext = x })

------------------------------------------------------------

class HasCompressorMay α where compressorMay ∷ Lens' α (𝕄 Compressor)

----------

instance HasCompressorMay (𝕄 Compressor) where
  compressorMay = lens id (const id)

------------------------------------------------------------

compressPzstd ∷ Compressor
compressPzstd =
  let pzstd ∷ MonadIO μ => AbsFile → AbsFile → ExceptT ProcError μ ()
      pzstd f t = do
        let args = ["--quiet", "--check", toText f, "-o", toText t, "--rm"]
            exe  = Paths.pzstd
        null ← devnull
        () ← snd ⊳ doProc (return ()) null (uncurry mkCmd (exe,args))
        return ()
      pzstdIO ∷ AbsFile → AbsFile → IO ()
      pzstdIO f t = join $ eToStderrIO ⊳ (ѥ @ProcError $ pzstd f t)
  in  new (new @Name @String "pstzd",new @CompressorIO pzstdIO,
           new @FilenameExtension [pc|zst|])

----------------------------------------

{-| List of moves (and potentially compresses) to perform for numbered file
    rotation; this accounts for actual file existence.  This doesn't actually
    perform any destructive IO (just some `stat`s); rather provides a list of
    instructions.
-}
-- XXX how are we checking for which files need compressing?
-- XXX use EMonad and friends?

fileNumberedMoves ∷ ∀ φ μ .
                    (MonadIO μ, HasMaxFiles φ, HasCompressorMay φ,
                     FilenameGenerator φ (AbsFile → 𝕄 MaxFiles → AbsFile)) =>
                    AbsFile → φ → 𝕄 ℍ → μ [(AbsFile, AbsFile, 𝕄 Compressor)]
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

{-| Provide the name of a file to compress (if any), and a list of older files
    to purge.  "Old" is determined by filename, which are assumed to be written
    in a lexical format that makes the oldest file lexically the first (e.g.,
    "logfile-2026-09-09").

    This doesn't actually perform any destructive IO (just some `stat`s and
    directory reads); rather it provides a list of instructions.
-}

-- XXX how are we checking for which files need compressing?
-- XXX use EMonad and friends?
fileCompressClean ∷ ∀ ε φ μ .
                    (MonadIO μ, AsIOError ε, AsFPathError ε, MonadError ε μ,
                     HasMaxFiles φ, HasGlobPCRERegex φ, HasAbsDir φ,
                     HasCompressorMay φ) =>
                    φ → μ (𝕄 (AbsFile, Compressor), [AbsFile])
fileCompressClean opts = do
  let compress    = opts ⊣ compressorMay
      max_files   = opts ⊣ maxFiles
  (fes,des,errs) ← glob (opts ⊣ globPCRERegex) (opts ⊣ absDir_)
  forM_ des $ \ (d,_st) → liftIO $ do
    stdErrT $ [fmt|Log compress/clean: ignoring globbed directory: %T|] d
  forM_ errs $ \ (f∷AbsFile,e∷FPathIOError) → liftIO $ do
    stdErrT $ [fmt|Log compress/clean: failed to read '%T': %T|] f e
  let fns    ∷ [AbsFile] = sort (fst ⊳ fes) -- the oldest is listed first
      rms    ∷ [AbsFile] = -- ⊟ 1 to account for the file we're about to write
        dropEnd (fromIntegral $ (max_files ⊣ maxFiles16)⊟1) fns
      cmprss ∷ 𝕄 (AbsFile, Compressor) = (,) ⊳ lastMay fns ⊵ compress
  return (cmprss, rms)

-- that's all, folks! ----------------------------------------------------------
