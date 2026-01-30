import Base1

import Prelude  ( Bounded, Double, Enum, Float, Int, (+), (-), (/)
                , fromEnum, fromIntegral, maxBound, minBound, toEnum )

-- base --------------------------------

import Control.Applicative     ( many, pure )
import Control.Monad           ( forever, forM, forM_, return, sequence, when )
import Control.Monad.IO.Class  ( MonadIO, liftIO )
import Data.Bifunctor          ( first )
import Data.Bool               ( Bool, (&&) )
import Data.Either             ( Either, either )
import Data.Eq                 ( Eq, (==) )
import Data.Foldable           ( foldl1, length )
import Data.Function           ( ($), flip, id )
import Data.Functor            ( fmap )
import Data.List               ( filter, sort )
import Data.List.NonEmpty      ( nonEmpty, unzip )
import Data.Maybe              ( Maybe( Just, Nothing ), catMaybes )
import Data.Monoid             ( (<>) )
import Data.Ord                ( (<), (<=), (>) )
import Data.Tuple              ( snd, uncurry )
import System.Exit             ( ExitCode( ExitFailure ) )
import System.IO               ( IO, print )
import System.IO.Error         ( doesNotExistErrorType, mkIOError )
import Text.Show               ( Show( show ) )

-- base-unicode-symbols ----------------

-- import Data.Function.Unicode  ( (∘) )

{-

-- fluffy ------------------------------

import Fluffy.Applicative         ( (⩥) )
import Fluffy.Duration            ( Duration, hours )
import Fluffy.ByteSize2           ( ByteSize, gibibytes )
import Fluffy.Functor2            ( (⊳) )
import Fluffy.IO.Error            ( AsIOError( _IOErr ) )
import Fluffy.Lens2               ( (⊣), (⋕) )
import Fluffy.Monad               ( (⪼), (≫) )
import Fluffy.MonadError          ( fromMaybe, splitMError )
import Fluffy.MonadIO             ( die, eitherIOThrow, say, warn )
import Fluffy.MonadIO.File        ( stat )
import Fluffy.Nat                 ( AtMost( Nil ), One, Two )
import Fluffy.Options             ( optParser )
import Fluffy.Parsec.Error        ( AsParseError )
import Fluffy.Parsec.Permutation  ( parsecP )
import Fluffy.Path                ( AbsDir, AbsFile, AsFilePath( toFPath ), Dir
                                  , File, MyPath( resolve ), RelFile
                                  , getCwd_, parseFile'
                                  )
import Fluffy.ToRational          ( fromRational )

-}

-- fpath -------------------------------

import FPath.AbsFile           ( AbsFile )
import FPath.Dirname           ( dirname )
import FPath.Error.FPathError  ( FPathIOError )
import FPath.File              ( File( FileA ) )

{-

-- lens --------------------------------

import Control.Lens.Getter  ( view )
import Control.Lens.TH      ( makeLenses )

-- logging-effect ----------------------

import Control.Monad.Log  ( MonadLog, Severity, WithSeverity
                          , discardSeverity, logDebug, msgSeverity, runLoggingT )

-}

-- monaderror-io -----------------------

import MonadError.IO        ( eitherIOThrowT )
import MonadError.IO.Error  ( IOError, ioError, userE )

-- monadio-plus ------------------------

import MonadIO              ( warn )
import MonadIO.File         ( AccessMode( ACCESS_W ), access )
import MonadIO.FPath        ( pResolve )
import MonadIO.FStat        ( FExists( FExists, NoFExists ), fexists )
import MonadIO.NamedHandle  ( HEncoding( NoEncoding ), handle )
import MonadIO.OpenFile     ( FileOpenMode( FileW ), withFile )

{-

-- mtl ---------------------------------

import Control.Monad.Except  ( MonadError, throwError )
import Control.Monad.Trans   ( lift )

-}

-- optparse-applicative ----------------

import Options.Applicative  ( Parser, ReadM, argument, str, eitherReader, flag
                            , flag', help, long, metavar, progDesc, short )

-- optparse-plus -----------------------

import OptParsePlus  ( parseOpts )

{-

-- path --------------------------------

import Path  ( Path )

-- proclib -----------------------------

import ProcLib.CommonOpt.DryRun       ( DryRunLevel
                                      , HasDryRunLevel( dryRunLevel )
                                      , dryRun2P
                                      )
import ProcLib.CommonOpt.Verbose      ( HasVerboseLevel( verboseLevel )
                                      , VerboseLevel( VerboseLevel ) )
import ProcLib.Error.CreateProcError  ( AsCreateProcError )
import ProcLib.Error.CreateProcIOError  ( ExecCreatePathIOParseError )
import ProcLib.Error.ExecError        ( AsExecError )
import ProcLib.Process                ( doProcIO )
import ProcLib.Types.ProcIO           ( ProcIO )

-- text --------------------------------

import Data.Text     ( Text
                     , isInfixOf, isPrefixOf, lines, pack, unlines, unpack )
-}

-- import Data.Text.IO  ( getContents, putStrLn )
import Data.Text.IO  ( getLine )

{-
-- tfmt --------------------------------

import Text.Fmt  ( fmt, fmtT )

-- unix --------------------------------

import System.Posix.Files  ( FileStatus, fileSize )
-}

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import Log  ( CSOpt( NoCallStack ), info', logToFileHandleNoAdornments, logToFiles, simpleRotator )

--------------------------------------------------------------------------------

-- whether to show all the values output by mplayer -identify rather than the
-- summary parsing
data ShowAll = ShowAll | NoShowAll
  deriving Eq

-- | whether to stop on the first bad file seen, or continue and summarize the
--   good data
data IgnoreBadFiles = IgnoreBadFiles | NoIgnoreBadFiles
  deriving Eq

-- | whether to read file names from stdin (one per line)
data FilesOnStdin = FilesOnStdin | NoFilesOnStdin
  deriving Eq

-- type AbsRelFile = Either AbsFile RelFile

data Options = Options { _fn        ∷ 𝕋 -- AbsFile
                       , _verbosity ∷ Int -- VerboseLevel One
                       , _quietude  ∷ Int -- VerboseLevel One
                       }

verbosity = lens _verbosity (\ o v → o { _verbosity = v })
quietude  = lens _quietude  (\ o q → o { _quietude  = q })

{-
instance HasVerboseLevel One Options where
  verboseLevel = _verbosestub

instance HasDryRunLevel Two Options where
  dryRunLevel = dryRunL
-}

parseOptions ∷ Parser Options
parseOptions = let argMeta          = metavar "FILE" <> help "file to query"
                   filesOnStdinHelp = "read files from stdin one per line"
             in Options ⊳ argument str argMeta -- pResolve {- many (argument fileReader argMeta) -}
{-
                        ⩥ dryRun2P
-}
                        ⊵ (length ⊳ many (flag' () (short 'v')))
                        ⊵ (length ⊳ many (flag' () (short 'q')))
{-
                        ⩥ flag NoShowAll ShowAll
                                 (short 'a' <> long "all"
                                            <> help "show all the info")
                        ⩥ flag NoIgnoreBadFiles IgnoreBadFiles
                                 (short 'E' <> long "ignore-error-files"
                                            <> help "continue past bad files")

                        ⩥ flag NoFilesOnStdin FilesOnStdin
                                 (short 's' <> long "files-on-stdin"
                                            <> help filesOnStdinHelp)

                        ⩥ pure (VerboseLevel Nil)
-}

{-

{- | error for missing thing -}
noSuchErr ∷ AsIOError ε ⇒ Text → Path β τ → ε
noSuchErr t f =
  let fpath = toFPath f
   in _IOErr ⋕ mkIOError doesNotExistErrorType (unpack t) Nothing (Just fpath)

{- | throw error for missing thing -}
noSuchE ∷ (AsIOError ε, MonadError ε η) ⇒ Text → Path β τ → η ω
noSuchE t f = throwError $ noSuchErr t f

{- | throw error for missing file or directory -}
noSuchDFE ∷ (AsIOError ε, MonadError ε η) ⇒ Path β τ → η ω
noSuchDFE = noSuchE "file or directory"

{- | throw error for missing directory -}
noSuchDirE ∷ (AsIOError ε, MonadError ε η) ⇒ Path β Dir → η ω
noSuchDirE = noSuchE "directory"

{- | throw error for missing file -}
noSuchFileE ∷ (AsIOError ε, MonadError ε η) ⇒ Path β File → η ω
noSuchFileE = noSuchE "file"

{- | error for missing file -}
noSuchFileErr ∷ AsIOError ε ⇒ Path β File → ε
noSuchFileErr = noSuchErr "file"

{- | error for missing directory -}
noSuchDirErr ∷ AsIOError ε ⇒ Path β Dir → ε
noSuchDirErr = noSuchErr "directory"

{- | error for missing file or directory -}
noSuchFDErr ∷ AsIOError ε ⇒ Path β τ → ε
noSuchFDErr = noSuchErr "file or directory"

{- | throw error for missing file as indicated by `Nothing` -}
maybeNoSuchFileE ∷ (AsIOError ε, MonadError ε η) ⇒
                   Path β File → η (Maybe α) → η α
maybeNoSuchFileE fn g = g ≫ fromMaybe (noSuchFileErr fn)

{- | Call a fn that returns a `Maybe` with `Nothing` for a missing file; throw a
     no such file IOError into IOError -}
maybeNoSuchFileE' ∷ (AsIOError ε, MonadError ε η) ⇒
                   Path β File → (Path β File → η (Maybe α)) → η α
maybeNoSuchFileE' fn g = g fn ≫ fromMaybe (noSuchFileErr fn)

statF ∷ (MonadIO μ, AsIOError ε, MonadError ε μ) ⇒
        (FileStatus → α) → Path β τ -> μ (Maybe α)
statF g fn = fmap g ⊳ stat fn

statF' ∷ (MonadIO μ, AsIOError ε, MonadError ε μ) ⇒
        (FileStatus → α) -> Path β File → μ α
statF' g fn = statF g fn ≫ fromMaybe (noSuchFileErr fn)

{- | The size of file; Nothing if file doesn't exist -}
fsize ∷ (MonadError ε μ, AsIOError ε, MonadIO μ) ⇒
        Path β File → μ (Maybe ByteSize)
fsize = statF (fromIntegral ∘ fileSize)

-}

{-
fileReader ∷ ReadM AbsRelFile
fileReader = eitherReader (first show ∘ parseFile' ∘ pack)
-}

----------------------------------------

{- | Given a file (rel or abs), and a base dir, get an absolute file and a Text
     representation of the input suitable for error messages
 -}
-- resolveFile ∷ AbsDir → AbsRelFile → (AbsFile, Text)
-- resolveFile cwd f = (either id (resolve cwd) f, pack $ either toFPath toFPath f)

----------------------------------------

-- type TextLog = MonadLog (WithSeverity Text)

{- | Given a file, try to read its vital statistics with midentify
 -}
{-
doFile ∷ (MonadIO μ, TextLog μ,
          AsCreateProcError ε, AsExecError ε, AsParseError ε, AsIOError ε) ⇒
         Options → AbsFile → Text → ProcIO ε μ (Maybe (ByteSize, Duration))
doFile opts af fn = do
  out ← midentify af
  sz  ← lift $ maybeNoSuchFileE' af fsize
  let idtxt = unlines ∘ sort $ filter filterIDs out

  lift $ forM_ (lines idtxt) logDebug

  if opts ⊣ showAll == ShowAll
  then lift $ say idtxt ⪼ return Nothing
  else lift $ Just ⊳ parsecMPI fn sz idtxt
-}

{-
doFiles' ∷ (MonadIO μ, TextLog μ) ⇒
           Options → AbsDir → [AbsRelFile]
         → μ [(AbsRelFile,
             Either ExecCreatePathIOParseError (Maybe (ByteSize, Duration)))]
doFiles' opts cwd filenames =
  let f fn = fmap (fn,) ∘ splitMError ∘ doProcIO opts $ uncurry (doFile opts) (resolveFile cwd fn)
   in sequence $ f ⊳ filenames

doFiles ∷ (MonadIO μ, TextLog μ) ⇒
          Options → AbsDir → [AbsRelFile] → μ [Maybe (ByteSize, Duration)]

doFiles opts cwd filenames = do
  z ← doFiles' opts cwd filenames
  if opts ⊣ ignoreBadFiles == IgnoreBadFiles
  then forM z ( \ (fn ,ei) → either ( \ _ → warn ("ERROR file: '" <> pack (either toFPath toFPath fn) <> "'") ⪼ return Nothing) return ei)
  else either (die (ExitFailure 255) ∘ pack ∘ show) return (sequence $ snd ⊳ z)
-}

-- | if the options say so, read stdin as one file-per-line, and attempt to
--   interpret each as a file; on error, throws to IO
{-
readStdinFiles ∷ MonadIO μ ⇒ Options → μ [AbsRelFile]
readStdinFiles (view filesOnStdin → FilesOnStdin) =
  liftIO $ getContents ≫ sequence ∘ fmap (eitherIOThrow ∘ parseFile') ∘ lines
readStdinFiles _ = return []
-}

{-| throw an ε into IO as a user error -}
ԙ ∷ ∀ ε α μ . (MonadIO μ, Printable ε) ⇒ ExceptT ε μ α → μ α
ԙ f = ѥ f ≫ \ case
         𝓛 e → ioError (userE $ toString e)
         𝓡 r → return r

я ∷ ∀ α μ . (MonadIO μ) ⇒ ExceptT FPathIOError μ α → μ α
я = ԙ

main ∷ IO ()
main = do
  -- XXX add option to log time + format
  opts ← parseOpts (progDesc "write to logs") parseOptions
  -- cwd ∷ AbsDir ← getCwd_
  fn ← я (pResolve @AbsFile $ _fn opts) ≫ \ fn →
         я (access ACCESS_W fn) ≫ \ case
           𝓝   → let dn = fn ⊣ dirname
                 in  я (access ACCESS_W dn) ≫ \ case
           -- XXX check dir exists and is writable
                   𝓝   → ioError (userE $ [fmt|no such dir: '%T'|] dn)
                   𝓙 𝓣 → return fn
                   𝓙 𝓕 → ioError (userE $ [fmt|dir not writable: '%T'|] dn)
           𝓙 𝓣 → return fn

  warn $ [fmtT|fn: '%T'|] fn

  let log_renderers    = []
      log_transformers = []
  -- eitherIOThrowT $ withFile @IOError NoEncoding (FileW (𝓙 0o644)) fn $
    {- \ h → -} {- logToFileHandleNoAdornments log_renderers log_transformers (h ⊣ handle) $ forever -}
  logToFiles log_renderers log_transformers (simpleRotator (𝓙 10) (𝓙 0o644) 10 (FileA fn)) (FileA fn) $ forever (liftIO getLine ≫ info' @()){- do
      l ← liftIO $ getLine
    -- XXX user-specifiable log level, or log without level?
      info' @() l -}

--  _ $ pResolve (_fn opts)

  let verbiage = 5 + opts ⊣ verbosity - opts ⊣ quietude
  {-
  logLevel ← if verbiage > fromEnum (maxBound :: Severity)
             then warn "too many verbose flags! (max 2)" ⪼ return maxBound
             else if verbiage < fromEnum (minBound :: Severity)
                  then warn "too many quiet flags! (max 5)" ⪼ return minBound
                  else return $ toEnum verbiage
  -}
  -- print verbiage

--  stdinFiles ← readStdinFiles opts

--  let filenames = opts ⊣ fns <> stdinFiles

  {-
  z'' ← flip runLoggingT ( \ m → when (msgSeverity m <= logLevel) (putStrLn (discardSeverity m)) ) $ doFiles opts cwd filenames

  z' ← case nonEmpty (catMaybes z'') of
          Nothing → return Nothing
          Just xs → let (sizes, durations) = unzip xs
                      in return $ Just (foldl1 (+) sizes, foldl1 (+) durations)

  case z' of
    Nothing                         → return ()
    Just (sizeTotal, durationTotal) →
      let gbperh ∷ Float
          gbperh = fromRational (gibibytes sizeTotal) /
                   fromRational (durationTotal ⊣ hours)
       in say $ [fmtT|Total: %T  %T  (%3.2fGiB/h)|] sizeTotal durationTotal gbperh
  -}

  return ()

-- that's all, folks! ----------------------------
