module Log
  ( CSOpt(..), FileSizeRotatorOptions(..), FileTimeRotatorOptions(..)
  , Log, ToDoc_( toDoc_ )
  , WithLog, WithLogIO

  , emergency, alert, critical, err, warn, notice, info, debug
  , emergency', alert', critical', err', warn', notice', info', debug'
  , emergencyT, alertT, criticalT, errT, warnT, noticeT, infoT, debugT

  , fromList
  , log, logMsg, log', logMsg', logT, logMsgT, logT', logMsgT'
  , logIO, logIO', logIOT
  , logIOL, logIOL', logIOLT
  , logRender, logRender'
  , logToFD', logToFD, logToFile, logToFiles, logToFileHandleNoAdornments
  , logToStderr, logToStderr'
  , stackParses, stdRenderers
  , logFilter, mapLog, mapLogE
  -- XXX , fileDayRotator
  , fileSizeRotator

  , compressPzstd
  -- tests & test data
  , tests, _log0, _log0m, _log1, _log1m )
where

-- XXX factor out rotators to separate modules
-- XXX move some functions to other modules

import Prelude  ( error, undefined ) -- XXX
-- import Debug.Trace  ( traceShow, trace ) -- XXX

-- async -------------------------------

import Control.Concurrent.Async  ( Async, async, poll, wait )

-- base --------------------------------

import qualified  Data.Foldable  as  Foldable

import Control.Applicative      ( Applicative( (<*>), pure ) )
import Control.Concurrent       ( ThreadId, forkIO, threadDelay )
import Control.Concurrent.MVar  ( MVar, tryReadMVar, newEmptyMVar, newMVar
                                , readMVar, swapMVar )
import Control.Monad            ( Monad( (>>=) )
                                , forM, forM_, join, mapM_, return, sequence )
import Control.Monad.IO.Class   ( MonadIO, liftIO )
import Data.Bifunctor           ( bimap )
import Data.Eq                  ( Eq )
import Data.Foldable            ( Foldable, all, concatMap, foldl', foldl1
                                , foldMap, foldr, foldr1 )
import Data.Function            ( ($), (&), const, flip, id )
import Data.Functor             ( Functor, fmap )
import Data.List                ( and, reverse, sort, sortOn, zip )
import Data.List.NonEmpty       ( NonEmpty( (:|) ), nonEmpty )
import Data.Maybe               ( catMaybes, isJust, maybe )
import Data.Monoid              ( Monoid )
import Data.Ord                 ( Ord, (>) )
import Data.Semigroup           ( Semigroup )
import Data.String              ( IsString, String )
import Data.Type.Equality       ( type(~) )
import Data.Tuple               ( fst, snd, uncurry )
import Data.Word                ( Word16, Word64 )
import GHC.Conc.Sync            ( ThreadStatus( ThreadBlocked, ThreadDied
                                              , ThreadFinished, ThreadRunning )
                                , threadStatus
                                )
import GHC.Enum                 ( Enum )
import GHC.Exts                 ( IsList( Item, fromList, toList ) )
import GHC.Generics             ( Generic )
import GHC.Num                  ( Num, (+), (-) )
import GHC.Real                 ( Integral, Real, (^), div, fromIntegral )
import GHC.Stack                ( CallStack )
import System.Exit              ( ExitCode )
import System.IO                ( Handle, IO, hFlush, hIsTerminalDevice, stderr )
import System.IO.Error          ( isDoesNotExistError )
import Text.Show                ( Show( show ) )

-- base-unicode-symbols ----------------

import Data.Bool.Unicode      ( (∧) )
import Data.Eq.Unicode        ( (≡), (≠) )
import Data.Function.Unicode  ( (∘) )
import Data.Monoid.Unicode    ( (⊕) )
import Prelude.Unicode        ( (×) )

-- data-default ------------------------

import Data.Default  ( Default( def ) )

-- data-textual ------------------------

import Data.Textual  ( Printable( print ), toString, toText )

-- deepseq -----------------------------

import Control.DeepSeq  ( NFData )

-- dlist -------------------------------

import qualified  Data.DList  as  DList
import Data.DList  ( DList, singleton )

-- exceptions --------------------------

import Control.Monad.Catch  ( MonadMask )

-- fstat -------------------------------

import FStat  ( FStat, size )

-- fpath -------------------------------

import qualified  FPath.File

import FPath                   ( (⫻), stripDirFPE )
import FPath.AbsDir            ( AbsDir )
import FPath.AbsFile           ( AbsFile, absfile )
import FPath.Basename          ( basename )
import FPath.Dir               ( Dir )
import FPath.Error.FPathError  ( FPathIOError )
import FPath.File              ( File )
import FPath.FileLike          ( FileLike, (⊙) )
import FPath.Parseable         ( __parseS__ )
import FPath.PathComponent     ( PathComponent, pc )
import FPath.RelFile           ( RelFile, _RelFile_, relfile )

-- lens --------------------------------

import Control.Lens.Getter     ( view )
import Control.Lens.Lens       ( Lens', lens )
import Control.Lens.Review     ( re )
import Control.Lens.Setter     ( over )
import Control.Lens.Traversal  ( both )

-- logging-effect ----------------------

import Control.Monad.Log  ( BatchingOptions( BatchingOptions
                                           , blockWhenFull, flushMaxQueueSize )
                          , Handler, MonadLog, LoggingT, PureLoggingT
                          , Severity(..)
                          , flushMaxDelay, logMessage
                          , runLoggingT, runPureLoggingT, withBatchedHandler
                          )

-- monaderror-io -----------------------

import MonadError           ( ѥ, ж )
import MonadError.IO.Error  ( AsIOError, IOError, _IOErr )

-- monadio-plus ------------------------

import MonadIO.Directory              ( GlobPCRERegex, __pwd__
                                      , directoryList, inDir, listdirStdOut )
import MonadIO.Error.CreateProcError  ( ProcError )
import MonadIO.File                   ( chmod, devnull, rename )
import MonadIO.FStat                  ( FExists( FExists ), lfexists )
import MonadIO.NamedHandle            ( ℍ, HEncoding( NoEncoding ),
                                        handle, hClose, hname )
import MonadIO.OpenFile               ( FileOpenMode( FileR, FileW ), openFile
                                      , readFileUTF8Lenient )
import MonadIO.Process                ( doProc )
import MonadIO.Process.CmdSpec        ( mkCmd )
import MonadIO.Temp                   ( __progNamePrefix__, __tempdir__
                                      , testsWithTempDir'' )

-- mono-traversable --------------------

import Data.MonoTraversable  ( Element
                             , MonoFoldable( ofoldl', ofoldl1Ex', ofoldr
                                           , ofoldr1Ex , ofoldMap, olength
                                           , otoList )
                             , MonoFunctor( omap )
                             )

-- more-unicode ------------------------

import Data.MoreUnicode.Applicative  ( (⋫) )
import Data.MoreUnicode.Bool         ( 𝔹, pattern 𝓕, pattern 𝓣 )
import Data.MoreUnicode.Either       ( 𝔼, pattern 𝓛, pattern 𝓡 )
import Data.MoreUnicode.Functor      ( (⊳), (⊳⊳), (⩺) )
import Data.MoreUnicode.Lens         ( (⊣), (⊢), (⊧), (⩼) )
import Data.MoreUnicode.Maybe        ( 𝕄, pattern 𝓙, pattern 𝓝, (⧏) )
import Data.MoreUnicode.Monad        ( (⪼), (≫) )
import Data.MoreUnicode.Natural      ( ℕ )
import Data.MoreUnicode.Semigroup    ( (◇) )
import Data.MoreUnicode.String       ( 𝕊 )
import Data.MoreUnicode.Text         ( 𝕋 )

-- mtl ---------------------------------

import Control.Monad.Except    ( ExceptT )
import Control.Monad.Identity  ( runIdentity )

-- natural -----------------------------

import Natural            ( (⊟) )
import Natural.Length     ( щ )
import Natural.Replicate  ( replicate_ )
import Natural.Unsigned   ( I64, Unsigned, ɨ )

-- parsec-plus -------------------------

import ParsecPlus  ( Parsecable( parser ) )

-- parser-plus -------------------------

import ParserPlus  ( caseInsensitiveString, tries )

-- prettyprinter -----------------------

import qualified  Prettyprinter.Render.Text  as  RenderText

import Prettyprinter  ( Doc
                      , LayoutOptions( LayoutOptions )
                      , PageWidth( AvailablePerLine, Unbounded )
                      , SimpleDocStream( SEmpty )
                      , layoutPretty, line', pretty, vsep
                      )

-- prettyprinter-ansi-terminal ---------

import qualified  Prettyprinter.Render.Terminal  as  RenderTerminal
import Prettyprinter.Render.Terminal  ( AnsiStyle )

-- safe --------------------------------

import Safe  ( headDef, tailSafe )

-- single ------------------------------

import Single( MonoSingle( osingle ), single )

-- tasty -------------------------------

import Test.Tasty        ( DependencyType( AllSucceed ), TestName, TestTree
                         , dependentTestGroup, testGroup )
import Test.Tasty.HUnit  ( Assertion
                         , assertBool, assertEqual, assertFailure,  testCase )

-- tasty-plus --------------------------

import TastyPlus         ( assertIsJust, assertLeft, assertListEq, assertListEqIO
                         , assertSuccess, runTestsP, runTestsReplay, runTestTree)
import TastyPlus.Equish  ( Equish( (≃) ) )

-- terminal-size -----------------------

import qualified  System.Console.Terminal.Size  as  TerminalSize

-- text --------------------------------

import Data.Text      qualified as  T
import Data.Text.Lazy qualified

import Data.Text     ( intercalate, length, lines, unlines )
import Data.Text.IO  ( hPutStr, hPutStrLn, putStrLn )

-- text-format -------------------------

import Text.Fmt  ( fmt )

-- text-printer ------------------------

import qualified  Text.Printer  as  P

-- time --------------------------------

import Data.Time.Clock                 ( getCurrentTime )

-- unix --------------------------------

import System.Posix.Types  ( CMode )

------------------------------------------------------------
--                     local imports                       -
------------------------------------------------------------

import Log.LogEntry       ( LogEntry, LogEntry
                          , logEntry, logdoc, _le0, _le1, _le2, _le3 )
import Log.LogRenderOpts  ( LogR, LogRenderOpts
                          , logRenderOpts', lroOpts, lroRenderer
                          , lroRenderSevCS, lroRenderTSSevCSH, lroWidth
                          , renderWithCallStack, renderWithSeverity
                          , renderWithStackHead, renderWithTimestamp
                          )

import LogPlus.Paths  qualified as  Paths

--------------------------------------------------------------------------------

class HasAsync α β where
  async_      ∷ Lens' α (Async β)
  waitAsync   ∷ MonadIO μ => α → μ β
  waitAsync a = liftIO $ wait (a ⊣ async_)

----------

instance HasAsync (Async β) β where async_ = lens id (const id)

------------------------------------------------------------

newtype CompressorThread = CompressorThread { unCompressorThread ∷ Async () }

----------

instance HasAsync CompressorThread () where
  async_ = lens unCompressorThread (const CompressorThread)

----------

instance Show CompressorThread where show _ = "CompressorThread"

------------------------------------------------------------

newtype Name = Name { unName ∷ 𝕊 }  deriving  (IsString,Show)

------------------------------------------------------------

class HasName α where
  name  ∷ Lens' α Name
  nameS ∷ Lens' α 𝕊
  nameS = lens (unName ∘ view name) (\ a s → a & name ⊢ Name s)

------------------------------------------------------------

{-| takes from,to filenames and does the deed -}
newtype CompressorIO = CompressorIO { unCompressorIO ∷ File → File → IO () }

------------------------------------------------------------

class HasCompressorIO α where
  compressorIO ∷ Lens' α CompressorIO
  compressorIOF ∷ Lens' α (File → File → IO())
  compressorIOF = lens (unCompressorIO ∘ view compressorIO)
                       (\ a f → a & compressorIO ⊢ CompressorIO f)

------------------------------------------------------------

{-| filename extension, e.g., to be appended after a `.` character -}
newtype FilenameExtension =
  FilenameExtension { unFilenameExtension ∷ PathComponent }

------------------------------------------------------------

class HasFilenameExtension α where
  filenameExtension   ∷ Lens' α FilenameExtension
  filenameExtensionPC ∷ Lens' α PathComponent
  filenameExtensionPC =
    lens (unFilenameExtension ∘ view filenameExtension)
         (\ a pc → a & filenameExtension ⊢ FilenameExtension pc)
  {-| append this extension to an existing PathComponent -}
  appendExtension     ∷ FileLike γ => α → γ → γ
  appendExtension a f = f ⊙ (a ⊣ filenameExtensionPC)

instance HasFilenameExtension FilenameExtension where
  filenameExtension = lens id (const id)

------------------------------------------------------------

{-| how to compress files -}
data Compressor = Compressor { -- | name purely for printing (`Show`) purposes
                               _cmp_name ∷ Name
                             , -- | takes from,to filenames and does the deed
                               _cmp_cmpr ∷ CompressorIO
                             , -- | filename extension to append (after a `.`)
                               _cmp_ext  ∷ FilenameExtension
                             }

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

-- XXX move & document this

-- odd ordering of variables make definition of Functor, Applicative, Monad
-- instances easier (or maybe possible)
data EMonad ε μ α = MonadIO μ => EMonad { runEMonadE ∷ μ (𝔼 ε α) }

--------------------

instance Functor (EMonad ε μ) where
  fmap f (EMonad m) = EMonad $ fmap (fmap f) m

--------------------

instance MonadIO μ => Applicative (EMonad ε μ) where
  pure x = EMonad $ return (𝓡 x)
  (EMonad f) <*> (EMonad x) = EMonad $ do
    f' ← f
    x' ← x
    return $ f' <*> x'

--------------------

instance MonadIO μ => Monad (EMonad ε μ) where
  (EMonad io) >>= f = EMonad $ do
    result ← io
    case result of
      𝓛 e → return (𝓛 e)      -- halt further computation
      𝓡 b → runEMonadE (f b)

--------------------

eMonad ∷ ∀ ε α μ . MonadIO μ => ExceptT ε μ α → EMonad ε μ α
eMonad = EMonad ∘ ѥ

ꙗ ∷ ∀ ε α μ . MonadIO μ => ExceptT ε μ α → EMonad ε μ α
ꙗ = eMonad

--------------------

{-| Given an Either, dump the Left to stderr; return Right as a Just -}
eToStderr ∷ ∀ ε α μ . (MonadIO μ, Printable ε) => 𝔼 ε α → μ (𝕄 α)
eToStderr (𝓛 e) = do { liftIO $ hPutStrLn stderr (toText e); return 𝓝 }
eToStderr (𝓡 r) = return (𝓙 r)

eToStderr' ∷ Printable ε => 𝔼 ε α → IO ()
eToStderr' = (const ()) ⩺ eToStderr

runEMonad ∷ ∀ ε α μ . (MonadIO μ, Printable ε) => EMonad ε μ α → μ (𝕄 α)
runEMonad m = runEMonadE m ≫ eToStderr

ꙝ ∷ ∀ ε α μ . (MonadIO μ, Printable ε) => ExceptT ε μ α → μ (𝕄 α)
ꙝ = runEMonad ∘ eMonad

ꙝ' ∷ ∀ ε α μ . (MonadIO μ, Printable ε) => ExceptT ε μ α → μ ()
ꙝ' = const () ⩺ ꙝ

----------------------------------------

eMonadTests ∷ TestTree
eMonadTests =
  let openr x = do
        openFile @IOError NoEncoding FileR x ≫ \ h → hClose h ⪼ return h
      passwd  = [absfile|/etc/passwd|]
      group   = [absfile|/etc/group|]
      nonsuch = [absfile|/etc/nonesuch|]
      run     ∷ (MonadIO μ, Show α, Printable ε) => ExceptT ε μ α → μ (𝕄 α)
      run     = runEMonad ∘ EMonad ∘ ѥ
      runE    ∷ (MonadIO μ, Show α, Printable ε) => ExceptT ε μ α → μ (𝔼 ε α)
      runE    = runEMonadE ∘ EMonad ∘ ѥ
      assertDoesNotExist ∷ (Show α, AsIOError ε) => 𝔼 ε α → Assertion
      assertDoesNotExist = assertLeft (  assertBool "isDoesNotExistError"
                                       ∘ (≡ 𝓙 𝓣)
                                       ∘ (isDoesNotExistError ⩺ (⩼ _IOErr)))
      testIsJust ∷ (Show α, Printable ε) =>
                   TestName → ExceptT ε IO α → TestTree
      testIsJust tn io = testCase tn $ run io ≫ assertIsJust

      testDoesNotExist ∷ (Show α, AsIOError ε, Printable ε) =>
                         TestName → ExceptT ε IO α → TestTree
      testDoesNotExist tn io = testCase tn $ runE io ≫ assertDoesNotExist

  in  testGroup "EMonad" $
                [ testIsJust       "open ok"        $ openr passwd
                , testDoesNotExist "open not ok"    $ openr nonsuch
                , testDoesNotExist "open not ok→ok" $ openr nonsuch⪼openr passwd
                , testDoesNotExist "open not ok × 2"$openr nonsuch⪼openr nonsuch
                , testDoesNotExist "open ok→not ok" $ openr passwd⪼openr nonsuch
                , testIsJust       "open ok→ok"     $ openr passwd ⪼ openr group
                ]

------------------------------------------------------------

{-| a list of LogEntries -}
newtype Log ω = Log { unLog ∷ DList (LogEntry ω) }
  deriving (Eq,Functor,Generic,Monoid,NFData,Semigroup,Show)

{-| `WithLog` adds in the `CallStack` constraint, so that if you declare your
    function to use this constraint, your function will be included in the
    logged callstack.  If you do not include the `CallStack` constraint, then
    the callpoint from within the function lacking the constraint (and anything
    calling it) will not be shown in the callstack.
 -}
type WithLog α η = (MonadLog (Log α) η, ?stack ∷ CallStack)
{-| `WithLog`, but with MonadIO, too -}
type WithLogIO α μ = (MonadIO μ, MonadLog (Log α) μ, ?stack ∷ CallStack)

type WithLogIOL α μ η = (MonadIO μ, MonadLog (Log α) η, ?stack ∷ CallStack)

type instance Element (Log ω) = LogEntry ω

{- This Foldable instance would give rise to toList being a list of α, i.e., the
   payload; rather than of LogEntry α; which, therefore, would be a
   contradiction of IsList.toList -- that will lead to surprises, I don't think
   it's a good idea.

instance Foldable Log where
  foldr ∷ ∀ α β . (α → β → β) → β → Log α → β
  foldr f b (Log ls) = foldr (f ∘ view attrs) b ls
-}

instance MonoFoldable (Log ω) where
  otoList    (Log dl)     = toList dl
  ofoldl'    f x (Log dl) = foldl' f x dl
  ofoldr     f x (Log dl) = foldr  f x dl
  ofoldMap   f (Log dl)   = foldMap f dl
  ofoldr1Ex  f (Log dl)   = foldr1 f dl
  ofoldl1Ex' f (Log dl)   = foldl1 f dl

instance MonoFunctor (Log ω) where
  omap f (Log dl) = Log (f ⊳ dl)

instance Printable ω => Printable (Log ω) where
  print = P.text ∘ T.unlines ∘ toList ∘ fmap toText ∘ unLog

instance Equish ω => Equish (Log ω) where
  l ≃ l' = olength l ≡ olength l'
         ∧ all (\ (x,x') → x ≃ x') (zip (otoList l) (otoList l'))

instance MonoSingle (Log ω) where
  osingle w = Log (single w)

------------------------------------------------------------

{-| this is called `ToDoc_` with an underscore to distinguish from any `ToDoc`
    class that took a parameter for the annotation type -}
class ToDoc_ α where
  toDoc_ ∷ α → Doc ()

instance ToDoc_ 𝕋 where
  toDoc_ = pretty

instance ToDoc_ (Doc()) where
  toDoc_ = id

------------------------------------------------------------

instance IsList (Log ω) where
  type Item (Log ω) = LogEntry ω
  fromList ∷ [LogEntry ω] → Log ω
  fromList ls = Log (DList.fromList ls)
  toList (Log ls) = DList.toList ls

----------------------------------------

{-| `vsep` returns an emptyDoc for an empty list; that results in a blank line.
     We often don't want that; the blank line appears whenever a log was
     filtered; which would really suck for heavily filtered logs (thus
     discouraging the use of logs for infrequently looked-at things - but then
     making it awkward to debug irritating edge-cases.  So we define a `vsep`
     variant, `vsep'`, which declares `Nothing` for empty docs, thus we can
     completely ignore them (don't call the logger at all).
-}
vsep' ∷ [Doc α] → 𝕄 (Doc α)
vsep' [] = 𝓝
vsep' xs = 𝓙 $ vsep xs

------------------------------------------------------------

{-| Log with a timestamp, thus causing IO.  This version keeps IO & logging as
    split monads, because once joined, the only way to split them is to run
    the logging.
-}
logIOL ∷ ∀ ρ ω μ η . (WithLogIOL ω μ η, ToDoc_ ρ) => Severity → ω → ρ → μ (η ())
logIOL sv p txt = do
  -- note that callstack starts here, *including* the call to logIO; this is
  -- deliberate, so that we see where in the code we made the log
  tm ← liftIO getCurrentTime
  return $
    logMessage ∘ Log ∘ singleton $ logEntry ?stack (𝓙 tm) sv (toDoc_ txt) p

--------------------

-- We redefine this, rather than simply calling logIOL, so as to not mess with
-- the callstack.
{-| Log with a timestamp, thus causing IO.  This version keeps IO & logging as
    split monads, because once joined, the only way to split them is to run
    the logging. -}
logIOL' ∷ ∀ ρ ω μ η . (WithLogIOL ω μ η, ToDoc_ ρ, Default ω) =>
           Severity → ρ → μ (η ())
logIOL' sv txt = do
  tm ← liftIO getCurrentTime
  return $
    logMessage ∘ Log ∘ singleton $ logEntry ?stack (𝓙 tm) sv (toDoc_ txt) def

--------------------

-- We redefine this, rather than simply calling logIOL, so as to not mess with
-- the callstack.
{-| log `Text` with a timestamp, thus causing IO -}
logIOLT ∷ ∀ ω μ η . (WithLogIOL ω μ η, Default ω) => Severity → 𝕋 → μ (η ())
logIOLT sv txt = do
  tm ← liftIO getCurrentTime
  return $
    logMessage ∘ Log ∘ singleton $ logEntry ?stack (𝓙 tm) sv (toDoc_ txt) def

----------------------------------------

{-| log with a timestamp, thus causing IO -}
logIO ∷ ∀ ρ ω μ . (WithLogIO ω μ, ToDoc_ ρ) => Severity → ω → ρ → μ ()
logIO sv p txt = do
  -- note that callstack starts here, *including* the call to logIO; this is
  -- deliberate, so that we see where in the code we made the log
  tm ← liftIO getCurrentTime
  logMessage ∘ Log ∘ singleton $ logEntry ?stack (𝓙 tm) sv (toDoc_ txt) p

--------------------

-- We redefine this, rather than simply calling logIO, so as to not mess with
-- the callstack.
{-| log with a timestamp, thus causing IO -}
logIO' ∷ ∀ ρ ω μ . (WithLogIO ω μ, ToDoc_ ρ, Default ω) => Severity → ρ → μ ()
logIO' sv txt = do
  tm ← liftIO getCurrentTime
  logMessage ∘ Log ∘ singleton $ logEntry ?stack (𝓙 tm) sv (toDoc_ txt) def

----------------------------------------

-- We redefine this, rather than simply calling logIO, so as to not mess with
-- the callstack.
{-| log `Text` with a timestamp, thus causing IO -}
logIOT ∷ ∀ ω μ . (WithLogIO ω μ, Default ω) => Severity → 𝕋 → μ ()
logIOT sv txt = do
  tm ← liftIO getCurrentTime
  logMessage ∘ Log ∘ singleton $ logEntry ?stack (𝓙 tm) sv (toDoc_ txt) def

----------------------------------------

{-| log with no IO, thus no timestamp -}
log ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ) => Severity → ω → ρ → η ()
log sv p txt =
  logMessage ∘ Log ∘ singleton $ logEntry ?stack 𝓝 sv (toDoc_ txt) p

{-| alias for `log`, to avoid clashing with `Prelude.log` -}
logMsg ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ) => Severity → ω → ρ → η ()
logMsg = log

----------

{-| `log`, with a default value -}
log' ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ, Default ω) => Severity → ρ → η ()
log' sv txt = do
  logMessage ∘ Log ∘ singleton $ logEntry ?stack 𝓝 sv (toDoc_ txt) def

----------

{-| alias for `log'`, for consistency with `logMsg` -}
logMsg' ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ, Default ω) => Severity → ρ → η ()
logMsg' = log'

----------

{-| `log`, with input type fixed to Text to avoid having to specify -}
logT ∷ ∀ ω η . (WithLog ω η) => Severity → ω → 𝕋 → η ()
logT sv p txt =
  logMessage ∘ Log ∘ singleton $ logEntry ?stack 𝓝 sv (toDoc_ txt) p

----------

{-| alias for `logT`, for consistency with `logMsg` -}
logMsgT ∷ ∀ ω η . (WithLog ω η) => Severity → ω → 𝕋 → η ()
logMsgT sv p txt =
  logMessage ∘ Log ∘ singleton $ logEntry ?stack 𝓝 sv (toDoc_ txt) p

----------

{-| `log'`, with input type fixed to Text to avoid having to specify -}
logT' ∷ ∀ ω η . (WithLog ω η, Default ω) => Severity → 𝕋 → η ()
logT' sv txt =
  logMessage ∘ Log ∘ singleton $ logEntry ?stack 𝓝 sv (toDoc_ txt) def

----------

{-| alias for `logT'`, for consistency with `logMsg`. -}
logMsgT' ∷ ∀ ω η . (WithLog ω η, Default ω) => Severity → 𝕋 → η ()
logMsgT' sv txt =
  logMessage ∘ Log ∘ singleton $ logEntry ?stack 𝓝 sv (toDoc_ txt) def

--------------------

emergency ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ) => ω → ρ → η ()
emergency = log Emergency

----------

emergency' ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ, Default ω) => ρ → η ()
emergency' = log Emergency def

----------

emergencyT ∷ ∀ ω η . (WithLog ω η, Default ω) => 𝕋 → η ()
emergencyT = emergency'

----------

alert ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ) => ω → ρ → η ()
alert = log Alert

----------

alert' ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ, Default ω) => ρ → η ()
alert' = log Alert def

----------

alertT ∷ ∀ ω η . (WithLog ω η, Default ω) => 𝕋 → η ()
alertT = alert'

----------

critical ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ) => ω → ρ → η ()
critical = log Critical

----------

critical' ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ, Default ω) => ρ → η ()
critical' = log Critical def

----------

criticalT ∷ ∀ ω η . (WithLog ω η, Default ω) => 𝕋 → η ()
criticalT = critical'

----------

err ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ) => ω → ρ → η ()
err = log Error

----------

err' ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ, Default ω) => ρ → η ()
err' = log Error def

----------

errT ∷ ∀ ω η . (WithLog ω η, Default ω) => 𝕋 → η ()
errT = err'

----------

warn ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ) => ω → ρ → η ()
warn = log Warning

----------

warn' ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ, Default ω) => ρ → η ()
warn' = log Warning def

----------

warnT ∷ ∀ ω η . (WithLog ω η, Default ω) => 𝕋 → η ()
warnT = warn'

----------

notice ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ) => ω → ρ → η ()
notice = log Notice

----------

notice' ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ, Default ω) => ρ → η ()
notice' = log Notice def

----------

noticeT ∷ ∀ ω η . (WithLog ω η, Default ω) => 𝕋 → η ()
noticeT = notice'

----------

info ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ) => ω → ρ → η ()
info = log Informational

----------

info' ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ, Default ω) => ρ → η ()
info' = log Informational def

----------

infoT ∷ ∀ ω η . (WithLog ω η, Default ω) => 𝕋 → η ()
infoT = info'

----------

debug ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ) => ω → ρ → η ()
debug = log Debug

----------

debug' ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ, Default ω) => ρ → η ()
debug' = log Debug def

----------

debugT ∷ ∀ ω η . (WithLog ω η, Default ω) => 𝕋 → η ()
debugT = debug'

----------------------------------------

type LogTransformer ω = LogEntry ω → [LogEntry ω]

{-| create a log filter from a predicate, for ease of making `LogTransformer`s -}
logFilter ∷ (LogEntry ω → 𝔹) → LogEntry ω  → [LogEntry ω]
logFilter p le = if p le then [le] else []

{-| render a log to a list of Docs, per `LogRenderOpts` and applying `LogEntry`
    transformers along the way -}
renderMapLog ∷ ∀ ω ρ ψ . Foldable ψ =>
               (LogEntry ω → Doc ρ) → ψ (LogTransformer ω) → Log ω
             → [Doc ρ]
renderMapLog renderer trx ls =
  let -- trx' ∷ LogTransformer ω
      trx' = foldr (\ a b → concatMap a ∘ b) (:[]) trx
   in renderer ⊳ (toList ls ≫ trx')

renderMapLog' ∷ ∀ ω ρ ψ . Foldable ψ =>
                (LogEntry ω → Doc ρ) → ψ (LogTransformer ω) → LogEntry ω
              → 𝕄 (Doc ρ)
renderMapLog' renderer trx le = vsep' ∘ renderMapLog renderer trx $ osingle le

----------------------------------------

{-| transform a monad ready to return (rather than effect) the logging -}
logRender ∷ ∀ ω α η .
            Monad η =>
            LogRenderOpts ω
          → [LogTransformer ω] -- log transformers, folded in order
                               -- from right-to-left
          → PureLoggingT (Log ω) η α
          → η (α, [𝕋])
logRender lro trx a = do
  (a',ls) ← runPureLoggingT a
  let lpretty ∷ Doc ρ → SimpleDocStream ρ
      lpretty = layoutPretty (lro ⊣ lroOpts)
      rendered = renderMapLog (lroRenderer lro) trx ls
  return $ (a', RenderText.renderStrict ∘ lpretty ⊳ rendered)

--------------------

{-| `logRender` with `()` is sufficiently common to warrant a cheap alias -}
logRender' ∷ ∀ ω η . Monad η =>
             LogRenderOpts ω → [LogTransformer ω] → PureLoggingT (Log ω) η ()
           → η [𝕋]
logRender' opts trx lg = snd ⊳ (logRender opts trx lg)

----------

logRender'Tests ∷ TestTree
logRender'Tests =
  let render o = runIdentity ∘ logRender' o []
      layoutSimple ∷ Doc ρ → SimpleDocStream ρ
      layoutSimple = layoutPretty (LayoutOptions Unbounded)
      docTxt ∷ Doc ρ → 𝕋
      docTxt = RenderText.renderStrict ∘ layoutSimple
      msgLen ∷ Doc ρ → Doc ()
      msgLen d = pretty (T.length $ docTxt d)
      msgTrim ∷ Doc ρ → Doc () -- trim to one line
      msgTrim d = pretty (headDef "" ∘ T.lines $ docTxt d)
      msgLenTransform ∷ LogEntry ρ → [LogEntry ρ]
      msgLenTransform le = [le & logdoc ⊧ msgLen]
      msgTrimTransform ∷ LogEntry ρ → [LogEntry ρ]
      msgTrimTransform le = [le & logdoc ⊧ msgTrim]
      exp2 ∷ [𝕋]
      exp2 = [ T.intercalate "\n" [ "[Info] log_entry 1"
                                  , "  stack0, called at c:1:2 in a:b"
                                  , "    stack1, called at f:5:6 in d:e"
                                  ]
             ]
      exp3 ∷ [𝕋]
      exp3 = [ "[1970-01-01Z00:00:00 Thu] [Info] «c#1» log_entry 1"
             , T.intercalate "\n" [   "[-----------------------] [CRIT] «y#9» "
                                    ⊕ "multi-line"
                                  ,   "                                       "
                                    ⊕ "log"
                                  ,   "                                       "
                                    ⊕ "message"
                                  ]
             , T.intercalate "\n"
                             [ "[1970-01-01Z00:00:00 Thu] [Warn] «y#9» this is a"
                             , "                                               "
                               ⊕ "vertically aligned"
                             , "                                               "
                               ⊕ "           message"
                             ]
             , "[-----------------------] [EMRG] «y#9» this is the last message"
             ]
      exp4 ∷ [𝕋]
      exp4 = [ "[1970-01-01Z00:00:00 Thu] [Info] «c#1» 11"
             , "[-----------------------] [CRIT] «y#9» 22"
             , "[1970-01-01Z00:00:00 Thu] [Warn] «y#9» 63"
             , "[-----------------------] [EMRG] «y#9» 24"
             ]
      exp5 ∷ [𝕋]
      exp5 = [ "[1970-01-01Z00:00:00 Thu] [Info] «c#1» log_entry 1"
             , "[-----------------------] [CRIT] «y#9» multi-line"
             , "[1970-01-01Z00:00:00 Thu] [Warn] «y#9» this is a"
             , "[-----------------------] [EMRG] «y#9» this is the last message"
             ]
      exp6 ∷ [𝕋]
      exp6 = [ "[1970-01-01Z00:00:00 Thu] [Info] «c#1» 11"
             , "[-----------------------] [CRIT] «y#9» 10"
             , "[1970-01-01Z00:00:00 Thu] [Warn] «y#9» 9"
             , "[-----------------------] [EMRG] «y#9» 24"
             ]
   in testGroup "logRender'" $
                [ assertListEq "render2" exp2 (render lroRenderSevCS _log0m)
                , assertListEqIO "render3"
                                 exp3 (logRender' lroRenderTSSevCSH [] _log1m)
                , assertListEqIO "drop 'em all"
                                 []
                                 (logRender' lroRenderTSSevCSH [\_ → []] _log1m)
                , assertListEqIO "message length"
                                 exp4
                                 (logRender' lroRenderTSSevCSH [msgLenTransform]
                                             _log1m)
                , assertListEqIO "message trim"
                                 exp5
                                 (logRender' lroRenderTSSevCSH
                                             [msgTrimTransform]
                                             _log1m)
                , assertListEqIO "message trim, then len"
                                 exp6
                                 (logRender' lroRenderTSSevCSH
                                             [msgLenTransform, msgTrimTransform]
                                             _log1m)
                , assertListEqIO "message len, then trim"
                                 exp4
                                 (logRender' lroRenderTSSevCSH
                                             [msgTrimTransform, msgLenTransform]
                                             _log1m)
                ]

----------------------------------------

whenJust ∷ ∀ α η . Monad η => (α → η ()) → 𝕄 α → η ()
whenJust _  𝓝  = return ()
whenJust io (𝓙 y) = io y

------------------------------------------------------------

flusher ∷ ∀ σ ρ ψ μ . (MonadIO μ, Foldable ψ) =>
          (𝕄 σ → 𝕋 → μ (Handle,σ)) -- ^ handle generator
        → MVar σ                   -- ^ incoming handle state
        → (SimpleDocStream ρ → 𝕋)  -- ^ render SimpleDocStream ρ to 𝕋
        → (Handle → 𝕋 → μ ())      -- ^ write messages to log
        → PageWidth
        → ψ (Doc ρ)                -- ^ messages to log
        → μ ()
flusher hgen stvar renderT logit pw messages = do
  let layout ∷ Foldable ψ => ψ (Doc π) → SimpleDocStream π
      layout ms = layoutPretty (LayoutOptions pw)
                               (vsep (Foldable.toList ms) ⊕ line')
      sds = layout messages
      t   = renderT sds
  st ← liftIO$ tryReadMVar stvar
  (h,st') ← hgen st t
  _ ← liftIO $ swapMVar stvar st'
  logit h t

----------------------------------------

newtype SizeBytes = SizeBytes Word64
  deriving (Enum,Eq,Integral,Num,Ord,Real,Show)

--------------------

class HasSizeBytes α where sizeBytes ∷ Lens' α SizeBytes

------------------------------------------------------------

-- XXX move this to ... somewhere.
takeWhileM ∷ Monad η => (α → η 𝔹) → [α] → η [α]
takeWhileM _ []    = return []
takeWhileM p (x:xs)= p x ≫ \ b → if b then (x:) ⊳ takeWhileM p xs else return []

----------------------------------------

pzstd ∷ MonadIO μ => File → File → ExceptT ProcError μ ()
pzstd f t = do
  p ← __pwd__
  let args = ["--quiet", "--check", toText f, "-o", toText t, "--rm"]
      exe  = Paths.pzstd
  null ← devnull
  () ← snd ⊳ doProc (return ()) null (uncurry mkCmd (exe,args))
  return ()

----------------------------------------

pzstdIO ∷ File → File → IO ()
pzstdIO f t = join $ eToStderr' ⊳ (ѥ @ProcError $ pzstd f t)

----------------------------------------

{-| The first non-𝓝 value in a list, if any -}
firstJust ∷ [𝕄 α] → 𝕄 α
firstJust []          = 𝓝
firstJust ((𝓙 x) : _) = 𝓙 x
firstJust (𝓝 : xs)    = firstJust xs

----------------------------------------

{-| Move, and optionally compress, a file.

    Rename `from` to `to`, compressing it with `compress` if that is not
    `Nothing`. If the compressor is initiated, it is fired off in a separate
    thread, and the `ThreadId` is returned.  Once the compressor is complete, we
    `chmod` the resultant file to `file_perms`.  We do not `chmod` the `to` file
    if there is no compressor.
-}
mv_compress ∷ CMode → (File,File,𝕄 Compressor) → IO (𝕄 CompressorThread)
mv_compress file_perms (from,to,do_compress) = do
  ꙝ' $ rename @IOError from to
  case do_compress of
    𝓝   → return 𝓝
    𝓙 c →
      let c' ∷ File → File → IO ()
          c' = \ fm tt → do (c ⊣ compressorIOF) fm tt
                            ж $ chmod @IOError file_perms tt
          ext = c ⊣ filenameExtensionPC
-- XXX      in  𝓙 ⊳ forkIO (c' to (to⊙ext))
      in  𝓙 ∘ CompressorThread ⊳ async (c' to (to⊙ext))
--      in  (c' to (to⊙ext)) ⪼ return 𝓝 -- for testing without threads


------------------------------------------------------------

data ThreadIsRunning = ThreadIsRunning | ThreadIsNotRunning
  deriving (Eq, Show)

------------------------------------------------------------

threadIsRunning ∷ ∀ δ m . (MonadIO m, HasAsync δ ()) => δ -> m ThreadIsRunning
threadIsRunning x = liftIO $
  let a ∷ Async () = x ⊣ async_
  in  poll a≫ \ case
    𝓝   → return ThreadIsRunning
    𝓙 _ → return ThreadIsNotRunning

----------------------------------------

{-| list of moves (and potentially compresses) to perform for numbered file
    rotation; this accounts for actual file existence -}
fileNumberedMoves ∷ MonadIO μ => File → FileSizeRotatorOptions → 𝕄 ℍ
                               → μ [(File, File, 𝕄 Compressor)]
fileNumberedMoves fn opts ɦ  =
  let compress    = opts ⊣ compressorMay
      fngen       = filenameGenerator opts
      max_files   = opts ⊣ maxFiles
      fngen' i    = maybe id appendExtension compress $ fngen fn i
      fn_nums     = 𝓙 ⊳ [0..(max_files-1)] -- -1 because we start at 0
      fn_pairs    = (over both fngen') ⊳ zip fn_nums (tailSafe fn_nums)
      init_fnpair = (maybe (fngen fn 𝓝) (view hname) ɦ,fngen fn (𝓙 0),compress)
      -- `proto_moves` is the list of potential files to move, before filtering
      -- on whether they actually exist
      -- only compress when making the first archive file
      proto_moves = init_fnpair : (uncurry (,,𝓝) ⊳ (fn_pairs))
  in  flip takeWhileM proto_moves $ \ (from,_to,_do_compress) →
        (≡ 𝓙 FExists) ⊳⊳ ꙝ @IOError $ lfexists from

------------------------------------------------------------

class HasℍMay      α where 𝕙May ∷ Lens' α (𝕄 ℍ)

------------------------------------------------------------

class HasCompressorThreadMay α where
  compressorThreadMay ∷ Lens' α (𝕄 CompressorThread)
  compressorThreadAsyncMay ∷ Lens' α (𝕄 (Async ()))
  compressorThreadAsyncMay =
    lens (fmap unCompressorThread ∘ view compressorThreadMay)
         (\ a x → a & compressorThreadMay ⊢ (CompressorThread ⊳ x))

----------

instance HasCompressorThreadMay (𝕄 CompressorThread) where
  compressorThreadMay = lens id (const id)

------------------------------------------------------------

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

------------------------------------------------------------

class MakeFileSizeRotatorState α where mkFSRSt ∷ α → FileSizeRotatorState

----------

instance MakeFileSizeRotatorState (𝕄 ℍ,  SizeBytes,𝕄 CompressorThread) where
  mkFSRSt (h,s,t) = FileSizeRotatorState h s t

----------

instance MakeFileSizeRotatorState (ℍ,  SizeBytes,𝕄 CompressorThread) where
  mkFSRSt (h,s,t) = FileSizeRotatorState (𝓙 h) s t

------------------------------------------------------------

{-| intermediate state for logging to a file which is rotated by time -}

data FileTimeRotatorState =
  FileTimeRotatorState { -- ^ current filehandle to which logs are being written
                         _ftrst_handle   ∷ 𝕄 ℍ
                       , -- ^ name of the file we're currently writing to
                         _ftrst_filename ∷ 𝕄 PathComponent
                       , -- ^ thread of the last compressor that we kicked off
                         _ftrst_cmpthrd  ∷ 𝕄 CompressorThread
                       }
  deriving Show

----------

instance Default FileTimeRotatorState where def = FileTimeRotatorState 𝓝 𝓝 𝓝

----------

instance HasℍMay FileTimeRotatorState where
  𝕙May = lens _ftrst_handle (\ f h → f { _ftrst_handle = h })

----------

instance HasCompressorThreadMay FileTimeRotatorState where
  compressorThreadMay = lens _ftrst_cmpthrd (\ f t → f { _ftrst_cmpthrd = t })

------------------------------------------------------------

class MakeFileTimeRotatorState α where mkFTRSt ∷ α → FileTimeRotatorState

{- XXX

----------

instance MakeFileTimeRotatorState (𝕄 ℍ, 𝕄 PathComponent, 𝕄 CompressorThread) where
  mkFTRSt (h,s,t) = FileTimeRotatorState h s t

----------

instance MakeFileTimeRotatorState (ℍ, 𝕄 PathComponent, 𝕄 CompressorThread) where
  mkFTRSt (h,s,t) = FileTimeRotatorState (𝓙 h) s t
-}

------------------------------------------------------------

newtype MaxFiles = MaxFiles { unMaxFiles ∷ Word16 } deriving (Enum,Num,Show)

--------------------

class HasMaxFiles α where maxFiles ∷ Lens' α MaxFiles

----------

instance HasMaxFiles MaxFiles where maxFiles = lens id (const id)

------------------------------------------------------------

newtype MaxFileSize = MaxFileSize { unMaxFileSize ∷ SizeBytes }
  deriving  (Num,Show)

----------

instance HasSizeBytes MaxFileSize where
  sizeBytes = lens unMaxFileSize (\ _ z → MaxFileSize z)

------------------------------------------------------------

class HasCompressorMay α where compressorMay ∷ Lens' α (𝕄 Compressor)

------------------------------------------------------------

class FilenameGenerator α β where
  filenameGenerator ∷ α → β

------------------------------------------------------------

type NumberedFnGen = File → 𝕄 MaxFiles → File

data NumberedFilenameGenerator =
  NumberedFilenameGenerator
    { _nfg_name  ∷ 𝕊 -- ^ just for `Show`
    , _nfg_fngen ∷ NumberedFnGen }

----------

instance Show NumberedFilenameGenerator where
  show = _nfg_name

----------

instance FilenameGenerator NumberedFilenameGenerator NumberedFnGen where
  filenameGenerator = _nfg_fngen

------------------------------------------------------------

{- XXX
class HasNumberedFilenameGenerator α where
  numberedFilenameGenerator ∷ Lens' α NumberedFilenameGenerator
-}
-- XXX  generateNumberedFilename  ∷ α → File → 𝕄 MaxFiles → File
-- XXX  generateNumberedFilename g f i = (g ⊣ filenameGenerator) f i

------------------------------------------------------------

type TimeFnGen τ = PathComponent → τ → PathComponent

data TimeFilenameGenerator τ =
  TimeFilenameGenerator
    { _tfg_name ∷ 𝕊 -- ^ just for `Show`
    , _tfg_fngen ∷ PathComponent → τ → PathComponent }

----------

instance Show (TimeFilenameGenerator τ) where
  show = _tfg_name

------------------------------------------------------------

{- XXX
class HasTimeFilenameGenerator α where
  timeFilenameGenerator ∷ Lens' α TimeFilenameGenerator
  generateTimeFilename  ∷ α → File → 𝕄 MaxFiles → File
  generateTimeFilename g f i =
    (unTimeFilenameGenerator $ g ⊣ timeFilenameGenerator) f i
-}

------------------------------------------------------------

class HasPerms α where perms ∷ Lens' α CMode

------------------------------------------------------------

class HasMaxFileSize α where maxFileSize ∷ Lens' α MaxFileSize

------------------------------------------------------------

{-| a simple filename generator, which adds (0-based) denary numbers to the end
    of the filename (after a '.') but pads them out to the required length as per
    `mxf` -}
simpleNumberedFilenameGenerator ∷ MaxFiles → NumberedFilenameGenerator
simpleNumberedFilenameGenerator mxf =
  let name = "simpleNumberedFilenameGenerator (" ◇ show mxf ◇ ")"
      parsePC = __parseS__ @PathComponent
      go_ fn 𝓝    = fn
      go_ fn (𝓙 i) =
        let numDigits ∷ (Integral α, Unsigned α) => α → I64
            numDigits 0 = 1
            numDigits n = countDigits n
              where
                countDigits 0 = 0
                countDigits x = 1 + countDigits (x `div` 10)

            padNumber ∷ I64 → I64 → 𝕊
            padNumber p n = let str = show n
                            in  (replicate_ (p ⊟ щ str) '0') ◇ str

            -- -1 because we start counting at '0'
            num = padNumber (numDigits $ unMaxFiles mxf - 1)

        in  (fn ⊙) ∘ parsePC ∘ num $ fromIntegral (unMaxFiles i)

  in  NumberedFilenameGenerator name go_

------------------------------------------------------------

{-| options for fileSizeRotator -}
data FileSizeRotatorOptions =
     FileSizeRotatorOptions { -- | How to compress old files, if at all.
                              --   If not `Nothing`, the IO will be run in
                              --   its own thread and only one will be run
                              --   at a time; logging will continue to the
                              --   open file, even if oversized, until the
                              --   prior compression has completed.
                              _fsro_cmprss ∷ 𝕄 Compressor
                            , -- | max file size; rotate (& compress?)
                              --   files once they are about to exceed
                              --   this.  Each file will receive at least
                              --   one log message, but if the next log
                              --   message would cause the file to exceed
                              --   this size, then it will be rotated
                              --   unless there is an ongoing unfinished
                              --   compression
                              _fsro_mxsz   ∷ MaxFileSize
                            , -- | Create files with these file
                              --   permissions. Note that during
                              --   compression, the perms may be wrong:
                              --   they are set after compression has
                              --   completed
                              _fsro_perms  ∷ CMode
                            , -- | maximum number of files to
                              --   manage/rotate; the numbers appended will
                              --   be zero-padded to all be the same length
                              _fsro_mxfs   ∷ MaxFiles
                            , -- | file name generator; takes the number of
                              --   the file numbered 0 for most recent,
                              --   incrementing; or 𝓝 for the file to
                              --   write current logs to
                              _fsro_fngen  ∷ NumberedFilenameGenerator
                            }
  deriving Show

----------

instance HasCompressorMay FileSizeRotatorOptions where
  compressorMay = lens _fsro_cmprss (\ f c → f { _fsro_cmprss = c })

----------

instance HasMaxFiles FileSizeRotatorOptions where
  maxFiles = lens _fsro_mxfs (\ f m → f { _fsro_mxfs = m })

----------

{- XXX
instance HasNumberedFilenameGenerator FileSizeRotatorOptions where
  numberedFilenameGenerator = lens _fsro_fngen (\ f g → f { _fsro_fngen = g })
-}

----------

instance HasPerms FileSizeRotatorOptions where
  perms = lens _fsro_perms (\ f p → f { _fsro_perms = p })

----------

instance HasMaxFileSize FileSizeRotatorOptions where
  maxFileSize = lens _fsro_mxsz (\ f z → f { _fsro_mxsz = z })

----------

instance FilenameGenerator FileSizeRotatorOptions NumberedFnGen where
  filenameGenerator = filenameGenerator ∘ _fsro_fngen

----------

{- A default set of `FileSizeRotatorOptions`, which takes a logfile basename;
   compresses the files, sets a max size of 100MiB, perms of -rw-r--r--, maxFiles
   of ten files, and using the `simpleNumberedFilenameGenerator` to append a
   log number on old files (after a `.`), padded with enough digits to allow for
   the maximum number of files.

 -}
mkFileSizeRotatorOptions ∷ MaxFiles → FileSizeRotatorOptions
mkFileSizeRotatorOptions mxf =
  let fngen = simpleNumberedFilenameGenerator mxf
  in  FileSizeRotatorOptions { _fsro_cmprss = 𝓙 compressPzstd
                             , _fsro_mxsz   = 100 × 1_024^3 -- 100MiB
                             , _fsro_perms  = 0o644
                             , _fsro_mxfs   = mxf
                             , _fsro_fngen  = fngen
                             }

------------------------------------------------------------

{-| a simple time generator, which adds the date to the end of a filename -}
dayFilenameGenerator ∷ TimeFilenameGenerator τ
dayFilenameGenerator = undefined

------------------------------------------------------------

{-| options for fileTimeRotator -}
data FileTimeRotatorOptions τ =
     FileTimeRotatorOptions { -- | How to compress old files, if at all.
                              --   If not `Nothing`, the IO will be run in
                              --   its own thread and only one will be run
                              --   at a time; logging will continue to the
                              --   open file, even if oversized, until the
                              --   prior compression has completed.
                              _ftro_cmprss ∷ 𝕄 Compressor
                            , -- | Create files with these file
                              --   permissions. Note that during
                              --   compression, the perms may be wrong:
                              --   they are set after compression has
                              --   completed
                              _ftro_perms  ∷ CMode
                            , -- | maximum number of files to
                              --   manage/rotate; the numbers appended will
                              --   be zero-padded to all be the same length
                              _ftro_mxfs   ∷ MaxFiles
                            , -- | file name generator; takes a timestamp or 𝓝
                              --   for the file to write current logs to
                              _ftro_fngen  ∷ TimeFilenameGenerator τ
                            , -- | file name glob (globs only over path
                              --   components, in the given directory)
                              _ftro_glob ∷ GlobPCRERegex
                            , -- | The directory to work in.  This rotator
                              --   can only use a single directory, due to
                              --   the globbing.
                              _ftro_dir ∷ AbsDir
                            }
  deriving Show

----------

instance HasCompressorMay (FileTimeRotatorOptions τ) where
  compressorMay = lens _ftro_cmprss (\ f c → f { _ftro_cmprss = c })

----------

instance HasMaxFiles (FileTimeRotatorOptions τ) where
  maxFiles = lens _ftro_mxfs (\ f m → f { _ftro_mxfs = m })

----------

{- XXX
instance HasNumberedFilenameGenerator FileTimeRotatorOptions where
  numberedFilenameGenerator = lens _ftro_fngen (\ f g → f { _ftro_fngen = g })
-}

----------

instance HasPerms (FileTimeRotatorOptions τ) where
  perms = lens _ftro_perms (\ f p → f { _ftro_perms = p })

----------

{- A default set of `FileTimeRotatorOptions`, which takes a logfile basename;
   compresses the files, sets a max time of 100MiB, perms of -rw-r--r--, maxFiles
   of ten files, and using the `simpleNumberedFilenameGenerator` to append a
   log number on old files (after a `.`), padded with enough digits to allow for
   the maximum number of files.

 -}
mkFileTimeRotatorOptions ∷ FileTimeRotatorOptions τ
mkFileTimeRotatorOptions =
  let fngen = dayFilenameGenerator
  in  FileTimeRotatorOptions { _ftro_cmprss = 𝓙 compressPzstd
                             , _ftro_perms  = 0o644
                             , _ftro_fngen  = fngen
                             }

------------------------------------------------------------

-- XXX what happens if we start logging to an extant file?
fileSizeRotator ∷ ∀ ω μ . MonadIO μ =>
                  FileSizeRotatorOptions
                → File                   -- ^ base filename (passed to `fngen`)
                → 𝕄 FileSizeRotatorState -- ^ incoming state; should be 𝓝 at
                                         --   first, will be self-managed for
                                         --   recursion
                → ω                      -- ^ SimpleDocStream (unused)
                → 𝕋                      -- ^ rendered text to write (used to
                                         --   calculate whether to rotate)
                → μ (Handle, FileSizeRotatorState) -- ^ new handle & state

fileSizeRotator opts fn st_ _sds t = do
  let st          = st_ ⧏ def
      l           = SizeBytes (ɨ $ щ t) -- length of t
      bytes_would = (st ⊣ sizeBytes) + l
      -- create a new handle, return a thread reference for the compressor if
      -- used to compress the old one
      mkhandle    ∷ μ (ℍ, 𝕄 CompressorThread)
      mkhandle    = do
        mv_files ← fileNumberedMoves fn opts (st ⊣ 𝕙May)
        tid' ← liftIO $ firstJust ⊳ forM (reverse mv_files)
                                         (mv_compress $ opts ⊣ perms)
        let -- open a file, mode 0644, raise if it fails
            open_file ∷ MonadIO μ => File → μ ℍ
            open_file =
              ж ∘ openFile @IOError NoEncoding (FileW ∘ 𝓙 $ opts ⊣ perms)
        ẖ ∷ ℍ ← open_file ((filenameGenerator opts) fn (𝓝∷𝕄 MaxFiles))
        return (ẖ, tid')

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
            return (𝕙' ⊣ handle, mkFSRSt (𝕙',l,ṯ))
          else -- just return the extant handle
            if and [ thread_is_running ≡ ThreadIsNotRunning
                   , isJust $ st ⊣ compressorThreadMay ]
            then -- update bytes written; and dump the thread (it's now done)
                 return (𝕙 ⊣ handle,st & sizeBytes           ⊢ bytes_would
                                       & compressorThreadMay ⊢ 𝓝)
            else -- just update the bytes written
                 return (𝕙 ⊣ handle,st & sizeBytes ⊢ bytes_would)

    𝓝   → -- no extant handle, so create one
           mkhandle ≫ \ (𝕙',ṯ) → return (𝕙' ⊣ handle, mkFSRSt (𝕙',l,ṯ))

--------------------

fileSizeRotatorTests ∷ TestTree
fileSizeRotatorTests =
  let nil       = const $ return ()
      do_log    ∷ 𝕄 Compressor → AbsDir
                → IO ([(AbsFile, FStat)], [(AbsDir, FStat)],
                      [(AbsFile, FPathIOError)],
                      [(AbsDir, FPathIOError)]
                     )
      do_log c d  = ж @IOError ∘ inDir d $ do
        let opts    = (mkFileSizeRotatorOptions 10) & compressorMay ⊢ c
                                                    & maxFileSize   ⊢ 10
                                                    & maxFiles      ⊢ 3
            rot     = -- XXX why the second logfile?
                      fileSizeRotator opts (FPath.File.FileR [relfile|logfile|])
            bopts   = BatchingOptions { flushMaxDelay = 1
                                      , blockWhenFull = 𝓣
                                      , flushMaxQueueSize = 1
                                      }
        -- we need to turn off batching here for predictable results
        logToFiles' (𝓙 bopts) [] [] rot $ mapM_ (warnT @())
                    [ "deleted??" -- this should get rotated away into the ether
                    , "123" -- each line gets a '\n' added, so that's four bytes
                    , "456" -- +4 => 8
                    , "7"   -- +2 => 10
                    , "abc" -- 4 bytes: should be a new file
                    , "defghijkl" -- 10 bytes: should be another new file
                    , "mnopqrstuvwxyz" -- 15 bytes: should be unbroken
                    {- , "αβγδεζηθικλ"
                    , "μνξ"
                    , "πρσ"
                    , "τφχ" -}
                    ]
        directoryList @FPathIOError @FPathIOError def d

  in  dependentTestGroup "simpleSizeRotator" AllSucceed $
        [ testsWithTempDir'' "no-compression" __tempdir__
            ((◇ [pc|-|]) ⊳ __progNamePrefix__) (do_log 𝓝) nil nil
            ([ ("check", const $ assertSuccess "check")
             , ("no file errors", \ (_,(_,_,efs,_)) →
                   assertEqual "file errors" [] efs
               )
             , ("no directory errors", \ (_,(_,_,_,dfs)) →
                   assertEqual "directory errors" [] dfs
               )
             , ("no subdirectories", \ (d,(_,ds,_,_)) →
                   assertEqual "directories" [d] (fst ⊳ ds)
               )
          -- , ("listdir", \ (d,_)→listdirStdOut def d⪼ assertSuccess "listdir")
             , ("logfile names", \ (d,(fs,_,_,_)) →
                   case sequence (stripDirFPE d ⊳ fst ⊳ fs) of
                     𝓛 e   → assertFailure $ show e
                     𝓡 fs' → let expect = [ [relfile|logfile|]
                                           , [relfile|logfile.0|]
                                           , [relfile|logfile.1|]
                                           , [relfile|logfile.2|]
                                           ]
                             in  assertEqual "files" expect (sort fs')
               )

             , ("logfile sizes", \ (_,(fs,_,_,_)) → do
                   let sizes  = sortOn fst $ bimap basename size ⊳ fs
                       expect = [ ([relfile|logfile|],15)
                                , ([relfile|logfile.0|],10)
                                , ([relfile|logfile.1|],4)
                                , ([relfile|logfile.2|],10)
                                ]
                   assertEqual "file sizes" expect sizes
               )
             ]
             {- ◇ ((\ (i∷ℕ,fn∷RelFile) → ("cat " ◇ show i, \ (d,_) → do
                   ѥ (readFileUTF8Lenient @IOError fn) ≫ \ case
                     𝓛 e → liftIO $ assertFailure (show e)
                     𝓡 t → liftIO $ do
                       putStrLn ("---- " ◇ T.pack (show fn) ◇ "----")
                       putStrLn t
                       putStrLn "----"
                       assertSuccess ("cat" ◇ T.pack (show i))
               )) ⊳ [ (0,[relfile|logfile.0|])
                    , (1,[relfile|logfile.1|])
                    , (2,[relfile|logfile.2|])
                    ])
             -}
            )

        , testsWithTempDir'' "with-compression" __tempdir__
            ((◇ [pc|-|]) ⊳ __progNamePrefix__) (do_log(𝓙 compressPzstd)) nil nil
            ([ ("check", const $ assertSuccess "check")
             , ("no file errors", \ (_,(_,_,efs,_)) →
                   assertEqual "file errors" [] efs
               )
             , ("no directory errors", \ (_,(_,_,_,dfs)) →
                   assertEqual "directory errors" [] dfs
               )
             , ("no subdirectories", \ (d,(_,ds,_,_)) →
                   assertEqual "directories" [d] (fst ⊳ ds)
               )
          -- , ("listdir", \ (d,_)→listdirStdOut def d⪼ assertSuccess "listdir")
             , ("logfile names", \ (d,(fs,_,_,_)) →
                   case sequence (stripDirFPE d ⊳ fst ⊳ fs) of
                     𝓛 e   → assertFailure $ show e
                     𝓡 fs' → let expect = [ [relfile|logfile|]
                                           , [relfile|logfile.0.zst|]
                                           ]
                             in  assertEqual "files" expect (sort fs')
               )

             , ("logfile sizes", \ (_,(fs,_,_,_)) → do
                   let sizes  = sortOn fst $ bimap basename size ⊳ fs
                       expect = [ -- the 10-byte limit will only effect when
                                  -- compression is complete, which in practice
                                  -- won't be untill all the writing is done; so
                                  -- it all gets piled onto here
                                  ([relfile|logfile|],39)
                                  -- although 10 bytes uncompressed, the header
                                  -- will actually increase the file size
                                , ([relfile|logfile.0.zst|],35)
                                ]
                   assertEqual "file sizes" expect sizes
               )
             ]
             {- ◇ ((\ (i∷ℕ,fn∷RelFile) → ("cat " ◇ show i, \ (d,_) → do
                   ѥ (readFileUTF8Lenient @IOError fn) ≫ \ case
                     𝓛 e → liftIO $ assertFailure (show e)
                     𝓡 t → liftIO $ do
                       putStrLn ("---- " ◇ T.pack (show fn) ◇ "----")
                       putStrLn t
                       putStrLn "----"
                       assertSuccess ("cat" ◇ T.pack (show i))
               )) ⊳ [ (0,[relfile|logfile.0|])
                    , (1,[relfile|logfile.1|])
                    , (2,[relfile|logfile.2|])
                    ])
             -}
            )
        ]

----------------------------------------

{-| Log to a file, which is rotated at a given date.

    Every time we're about to write a log, we check to see the `Day` of the
    supplied time, and if it's a later `Day` than the current log file being
    written to, we roll the log and potentially compress the old one.

    State (σ) is (current handle in use, filename corresponding to that handle,
    threadId of last-run compressor).
-}

-- τ is the time type, e.g. `Data.Time.Clock.UTCTime` or
-- `Data.Time.LocalTime.LocalTime`
-- XXX fileTimeRotator ∷ ∀ τ ω μ . (MonadIO μ, σ ~ (𝕄 ℍ,𝕄 RelFile,𝕄 ThreadId)) =>
-- XXX what happens if we start logging to an extant file?
{- XXX
fileTimeRotator_ ∷ ∀ τ ω μ . MonadIO μ =>
                   FileTimeRotatorOptions τ
                   -- | time of the log (pulling it out of the log message(s) is
                   --   hard, and it's unclear how to handle groups of messages -
                   --   use the latest or the earliest? - and this makes testing
                   --   easier, so we hand in an explicit time
                 → τ
                   -- | incoming state; should be 𝓝 at first, will be
                   --   self-managed for recursion
                 → 𝕄 FileTimeRotatorState
                 → ω                               -- ^ SimpleDocStream (unused)
                   -- | rendered text to write (used to calculate whether to
                   --   rotate)
                 → 𝕋
                 → μ (Handle,FileTimeRotatorState) -- ^ new handle & state


fileTimeRotator_ compress z file_perms max_files d fngen rx st_ _sds t = do
  let (ɦ,fn,tid) = st_ ⧏ (𝓝,𝓝,𝓝)
      -- l           = SizeBytes (ɨ $ щ t) -- length of t
      fn'         = fngen z ⊣ re _RelFile_
      mkhandle    ∷ μ (ℍ, 𝕄 ThreadId)
      mkhandle    = do
        -- XXX just clean up & compress old files
        {- mv_files ← fileNumberedMoves max_files fngen ɦ compress
        tid' ← liftIO $ firstJust ⊳ forM (reverse mv_files) (mv_compress file_perms)
        -}
        let -- open a file, mode 0644, raise if it fails
            open_file ∷ MonadIO μ => AbsFile → μ ℍ
            open_file = ж ∘ openFile @IOError NoEncoding (FileW (𝓙 file_perms))
        ẖ ∷ ℍ ← open_file $ d⫻fn'
        return (ẖ, 𝓝) -- return (ẖ, tid')

{- XXX make this work
  thread_is_running ← liftIO $ case tid of
                                 𝓝   → return ThreadIsNotRunning
                                 𝓙 ŧ → threadIsRunning ŧ
-}
  case ɦ of -- do we have an open filehandle?
    𝓝   → mkhandle ≫ \ (𝕙',ṯ) → return (𝕙' ⊣ handle,(𝓙 𝕙',𝓙 fn',ṯ))
    𝓙 𝕙 → if and [ -- XXX thread_is_running ≠ ThreadIsRunning
                  fn ≠ 𝓙 fn'
                 ]
          then do -- time to make a new handle
            hClose 𝕙
            (𝕙',ṯ) ← mkhandle
            return (𝕙' ⊣ handle,(𝓙 𝕙',𝓙 fn',ṯ))
          else return (𝕙 ⊣ handle,(𝓙 𝕙,fn,tid))
-}

----------------------------------------

{-| Write to an FD with given options, using `withBatchedHandler`. Each log entry
    is vertically separated. -}
withFDHandler ∷ ∀ α σ ρ μ . (MonadIO μ, MonadMask μ, Show σ) =>
               -- | generate a handle from maybe-state, input docstream/text
               (𝕄 σ → SimpleDocStream ρ → 𝕋 → IO (Handle,σ))
             → (SimpleDocStream ρ → 𝕋) -- ^ render the text from the docstream
             → (Handle → 𝕋 → IO())     -- ^ write the text to the handle
             → PageWidth
             → BatchingOptions
             → 𝕄 σ                     -- ^ incoming state for handle generation
             → (Handler μ (Doc ρ) → μ α) -- A.K.A, (Doc ρ → μ ()) → μ α
               -- ^ how to run the logging, e.g., runLoggingT++ (runs the log,
               --   does the IO)
             → μ (α,σ)

withFDHandler hgen renderT logit pw bopts st handler = do
  -- even though this looks like it should happen every time through the loop;
  -- tracing it, it clearly doesn't.  I don't know why, I guess it's something
  -- to do with the construction of monadlog: but I don't seem to need to worry
  -- about the cost of creating new mvars
  stvar ∷ MVar σ ← liftIO $ maybe newEmptyMVar newMVar st
  let layout ∷ Foldable ψ => ψ (Doc π) → SimpleDocStream π
      layout ms = layoutPretty (LayoutOptions pw)
                               (vsep (Foldable.toList ms) ⊕ line')
      -- flush ∷ Foldable ψ => ψ (Doc ρ) → IO ()
      flush ms = flusher (\ ṡ t → hgen ṡ (layout ms) t) stvar renderT logit pw ms
  a ← withBatchedHandler bopts flush handler
  st' ← liftIO $ readMVar stvar
  return (a,st')

----------------------------------------

{-| Write to an FD with given options, immediately (in thread), no batching.
    Each log entry has a newline appended. -}
withSimpleHandler ∷ ∀ ω α ρ μ .
                    MonadIO μ =>
                    (SimpleDocStream ρ → 𝕋)
                  → PageWidth
                  → Handle
                  → (Handle → 𝕋 → IO ())
                  → (LogEntry ω → 𝕄 (Doc ρ))
                  → LoggingT (Log ω) μ α
                  → μ α
withSimpleHandler renderT pw fd hWrite entryToDoc =
  let hPutNewline h = hPutStrLn h ""
      layout = layoutPretty (LayoutOptions pw)
      renderEntry e = let go d = do let sds ∷ SimpleDocStream ρ
                                        sds = layout d
                                    hWrite fd (renderT sds)
                                    hPutNewline fd
                      in  whenJust go (entryToDoc e)
      renderEach l = do liftIO $ forM_ (toList l) renderEntry

   in (flip runLoggingT) (renderEach)

----------------------------------------

{-| Options suitable for logging to a file; notably a 1s flush delay and keep
    messages rather than dropping if the queue fills.
 -}
fileBatchingOptions ∷ BatchingOptions
fileBatchingOptions = BatchingOptions { flushMaxDelay     = 1_000_000
                                      , blockWhenFull     = 𝓣
                                      , flushMaxQueueSize = 100
                                      }

{-| Options suitable for logging to a tty; notably a short flush delay (0.2s),
    and drop messages rather than blocking if the queue fills (which should
    be unlikely, with a length of 100 & 0.1s flush).
 -}

----------------------------------------

ttyBatchingOptions ∷ BatchingOptions
-- The max delay is a matter of experimentation; too high, and messages appear
-- long after their effects on stdout are apparent (not *wrong*, but a bit
-- misleading/inconvenient); too low, and the message lines get broken up
-- and intermingled with stdout (again, not *wrong*, but a terrible user
-- experience).
ttyBatchingOptions = BatchingOptions { flushMaxDelay     = 2_000
                                     , blockWhenFull     = 𝓕
                                     , flushMaxQueueSize = 100
                                     }


----------------------------------------

{-| Write a Log to a filehandle, with given rendering and options.
    The handle is created by a generator function, which may keep state.
-}
-- XXX Show just for debugging
logToHandles ∷ ∀ α σ ρ ω μ  . (MonadIO μ, MonadMask μ, Show σ) =>
               (𝕄 σ → SimpleDocStream ρ → 𝕋 → IO (Handle, σ))
               -- ^ handle generator
             → (SimpleDocStream ρ → 𝕋)
             → (LogEntry ω → 𝕄 (Doc ρ)) -- ^ render a LogEntry
             → 𝕄 BatchingOptions
             → PageWidth
             → LoggingT (Log ω) μ α
             → μ (α,σ)

logToHandles hgen renderT renderEntry mbopts width io = do
  let -- renderIO ∷ Handle → SimpleDocStream ρ → IO()
      renderIO h t = hPutStr h t ⪼ hFlush h
  (fh,ṡṫ) ← liftIO $ hgen 𝓝 SEmpty ""

  (a,ṣṭ) ← case mbopts of
    𝓝       → (,ṡṫ) ⊳ withSimpleHandler renderT width fh renderIO renderEntry io
    𝓙 bopts →
      let -- renderDoc ∷ Log ω → 𝕄 (Doc ρ)
          renderDoc =
            vsep ∘ toList ⩺ nonEmpty ∘ catMaybes ∘ fmap renderEntry ∘ otoList

          -- handler ∷ (𝕄 (Doc ρ) → μ ()) → μ α
          handler h  = runLoggingT io (whenJust h ∘ renderDoc)
      in  withFDHandler hgen renderT renderIO width bopts (𝓙 ṡṫ) handler
  return (a,ṣṭ)

----------------------------------------

{-| simple handle generator for use with logToHandles, that always uses a single
    filehandle -}
staticHandle ∷ ∀ ρ μ . MonadIO μ =>
               Handle → 𝕄 Handle → SimpleDocStream ρ → 𝕋 → μ (Handle,Handle)
staticHandle h _ _ _ = return (h,h)

----------------------------------------

{-| write a log to a filehandle, generated at need, with given options but no
    adornments -}
-- XXX Show just for debugging
logToHandlesNoAdornments ∷ ∀ α ω μ σ . (MonadIO μ, MonadMask μ, Show σ) =>
                           (𝕄 σ → SimpleDocStream AnsiStyle → 𝕋 → IO (Handle, σ))
                           -- ^ handle generator
                         → 𝕄 BatchingOptions
                         → LogRenderOpts ω
                         → [LogTransformer ω]
                         → LoggingT (Log ω) μ α
                         → μ (α,σ)
logToHandlesNoAdornments hgen bopts lro trx io =
  logToHandles hgen RenderText.renderStrict
               (renderMapLog' (lroRenderer lro) trx) bopts (lro ⊣ lroWidth) io

--------------------

{-| write a Log to a filehandle, with given options but no adornments -}
logToHandleNoAdornments ∷ ∀ ω α μ . (MonadIO μ, MonadMask μ) =>
                          𝕄 BatchingOptions
                        → LogRenderOpts ω
                        → [LogTransformer ω]
                        → Handle
                        → LoggingT (Log ω) μ α
                        → μ α
logToHandleNoAdornments bopts lro trx h =
  fst ⩺ logToHandlesNoAdornments (staticHandle h) bopts lro trx

--------------------

{-| write a Log to a filehandle, with given options and ANSI adornments -}
logToHandleAnsi ∷ ∀ ω α μ . (MonadIO μ, MonadMask μ) =>
                  𝕄 BatchingOptions
                → LogRenderOpts ω
                → [LogTransformer ω]
                → Handle
                → LoggingT (Log ω) μ α
                → μ α
logToHandleAnsi bopts lro trx h io =
  let hgen = staticHandle h
      renderT     = Data.Text.Lazy.toStrict ∘ RenderTerminal.renderLazy
      renderEntry = renderMapLog' (lroRenderer lro) trx
      width       = lro ⊣ lroWidth
  in  fst ⊳ logToHandles hgen renderT renderEntry bopts width io

----------------------------------------

{-| log to a regular file, with unbounded width -}
logToFileHandleNoAdornments ∷ ∀ ω α μ . (MonadIO μ, MonadMask μ) =>
                              [LogR ω] → [LogTransformer ω] → Handle
                            → LoggingT (Log ω) μ α → μ α
logToFileHandleNoAdornments ls trx =
  let lro = logRenderOpts' ls Unbounded
   in logToHandleNoAdornments (𝓙 fileBatchingOptions) lro trx

--------------------

{-| log to a tty, using current terminal width -}
logToTTY' ∷ ∀ ω α μ . (MonadIO μ, MonadMask μ) =>
            [LogR ω] → [LogTransformer ω] → Handle → LoggingT (Log ω) μ α → μ α
logToTTY' ls trx h io = do
  size_ ← liftIO $ TerminalSize.size
  let lro = case size_ of
              𝓙 sz → let width = AvailablePerLine (TerminalSize.width sz) 1.0
                      in logRenderOpts' ls width
              𝓝    → logRenderOpts' ls Unbounded
  logToHandleAnsi (𝓙 ttyBatchingOptions) lro trx h io

--------------------

{-| Log to a file handle; if it looks like a terminal, use Ansi logging and low
    batch time; else go unadorned with higher batch time. -}
logToFD' ∷ ∀ ω α μ . (MonadIO μ, MonadMask μ) =>
           [LogR ω] → [LogTransformer ω] → Handle → LoggingT (Log ω) μ α
         → μ α
logToFD' ls trx h io = do
  isatty ← liftIO $ hIsTerminalDevice h
  if isatty
  then logToTTY'  ls trx h io
  else logToFileHandleNoAdornments ls trx h io

----------------------------------------

data CSOpt = NoCallStack | CallStackHead | FullCallStack
  deriving (Enum, Eq, Show)

----------

instance Parsecable CSOpt where
  parser =
    -- Lookup table of String to CSOpt; these are the strings that will be parsed
    -- to CSOpt (with `Parseable`).  Parsing is case-insensitive.
    let stackOptions ∷ NonEmpty (String,CSOpt)
        stackOptions =    ("NoCallStack"   , NoCallStack)
                     :| [ ("NoCS"          , NoCallStack)
                        , ("CSHead"        , CallStackHead)
                        , ("CSH"           , CallStackHead)
                        , ("CallStackHead" , CallStackHead)
                        , ("FCS"           , FullCallStack)
                        , ("FullCallStack" , FullCallStack)
                        , ("FullCS"        , FullCallStack)
                        , ("CallStack"     , FullCallStack)
                        , ("Stack"         , FullCallStack)
                        ]
    in  tries [ caseInsensitiveString st ⋫ return cso | (st,cso) ← stackOptions ]

----------------------------------------

{-| lookup table of CSOpt to possible (case-insensitive) string representations-}
stackParses ∷ CSOpt → [String]
stackParses NoCallStack   = [ "NoCallStack", "NoCS" ]
stackParses CallStackHead = [ "CallStackHead", "CSHead", "CSH" ]
stackParses FullCallStack = [ "FullCallStack", "FullCS", "CallStack", "Stack" ]

----------------------------------------

stdRenderers ∷ CSOpt → [LogR ω]
stdRenderers NoCallStack =
  [ renderWithTimestamp, renderWithSeverity ]
stdRenderers CallStackHead =
  [ renderWithTimestamp, renderWithSeverity, renderWithStackHead ]
stdRenderers FullCallStack =
  [ renderWithCallStack, renderWithTimestamp, renderWithSeverity ]

----------------------------------------

{-| log to a plain file with given callstack choice, and given annotators -}
logToFile ∷ ∀ ω α μ . (MonadIO μ, MonadMask μ) =>
            CSOpt → [LogTransformer ω] → Handle → LoggingT (Log ω) μ α → μ α
logToFile cso trx =
  logToFileHandleNoAdornments (stdRenderers cso) trx

----------------------------------------

{-| run `io`, logging to rotating files -}
-- XXX Show just for debugging
logToFiles' ∷ ∀ α ω μ σ . (MonadIO μ, MonadMask μ, HasCompressorThreadMay σ, Show σ) =>
             𝕄 BatchingOptions
           → [LogR ω]                                               -- ^ trx
           → [LogTransformer ω]                                     -- ^ ls
           → (𝕄 σ → SimpleDocStream AnsiStyle → 𝕋 → IO (Handle, σ))
             -- ^ rt (rotator)
           → LoggingT (Log ω) μ α                                   -- ^ io
           → μ α
logToFiles' opts ls trx rt io = do
 let lro  = logRenderOpts' ls Unbounded
 (r,st) ← logToHandlesNoAdornments rt opts lro trx io
 -- if there's any compressors running, wait for them
 case st ⊣ compressorThreadMay of
   𝓝    → return ()
   𝓙 ct → waitAsync ct
 return r

----------------------------------------

{-| run `io`, logging to rotating files -}
-- XXX Show just for debugging
logToFiles ∷ ∀ α ω μ σ . (MonadIO μ, MonadMask μ, HasCompressorThreadMay σ, Show σ) =>
             [LogR ω]                                               -- ^ trx
           → [LogTransformer ω]                                     -- ^ ls
           → (𝕄 σ → SimpleDocStream AnsiStyle → 𝕋 → IO (Handle, σ))
             -- ^ rt (rotator)
           → LoggingT (Log ω) μ α                                   -- ^ io
           → μ α
logToFiles = logToFiles' (𝓙 fileBatchingOptions)

----------------------------------------

compressPzstd ∷ Compressor
compressPzstd =
  Compressor "pstzd" (CompressorIO pzstdIO) (FilenameExtension [pc|zst|])


----------------------------------------

{-| an instance of time rotator that defaults perms to 0o644, max files to 10,
    uses a pattern that appends dates to the end of the filenames -}
{- ω is unused SimpleDocStream
simpleSizeRotator ∷ ∀ ω μ σ . (MonadIO μ, σ ~ (𝕄 ℍ, SizeBytes, 𝕄 ThreadId)) =>
                    𝕄 Compressor → 𝕄 Word16 → 𝕄 CMode → SizeBytes → File
                  → 𝕄 σ → ω → 𝕋 → μ (Handle, σ)
-}
{-
simpleDayRotator ∷ ∀ τ ω μ σ . (MonadIO μ, σ ~ (𝕄 ℍ, 𝕄 RelFile, 𝕄 ThreadId)) =>
                   𝕄 Compressor → 𝕄 Word16 → 𝕄 CMode → SizeBytes → AbsDir
                 → τ → 𝕄 σ → ω → 𝕋 → μ (Handle, σ)
simpleDayRotator compressor max_files perms sz d =
  let numDigits ∷ (Integral α, Unsigned α) => α → I64
      numDigits 0 = 1
      numDigits n = countDigits n
        where
          countDigits 0 = 0
          countDigits x = 1 + countDigits (x `div` 10)

      padNumber ∷ I64 → I64 → 𝕊
      padNumber p n = let str = show n in (replicate_ (p ⊟ щ str) '0') ◇ str

      max_files' = max_files ⧏ 10
      num = padNumber (numDigits max_files')
--      fngen 𝓝    = fn
--      fngen (𝓙 i) = (fn ⊙) ∘ __parseS__ @PathComponent ∘ num $ fromIntegral i
  in  \ z → fileTimeRotator compressor z (perms ⧏ 0o644) max_files' d fngen
                            regex
-}

----------------------------------------

{-| log to a terminal with given callstack choice -}
logToTTY ∷ ∀ ω α μ . (MonadIO μ, MonadMask μ) =>
           CSOpt → [LogTransformer ω] → Handle → LoggingT (Log ω) μ α → μ α
logToTTY cso trx = logToTTY' (stdRenderers cso) trx

--------------------

{-| log to a file handle; if it looks like a terminal, use ANSI logging and
    current terminal width; else go unadorned with unbounded width -}
logToFD ∷ ∀ ω α μ . (MonadIO μ, MonadMask μ) =>
          CSOpt → [LogTransformer ω] → Handle → LoggingT (Log ω) μ α → μ α
logToFD cso trx h io = do
  isatty ← liftIO $ hIsTerminalDevice h
  if isatty
  then logToTTY  cso trx h io
  else logToFile cso trx h io

----------------------------------------

{- | log to stderr, assuming it's a terminal, with given callstack choice &
     filter -}
logToStderr ∷ ∀ ω α μ . (MonadIO μ, MonadMask μ) =>
              CSOpt → [LogTransformer ω] → LoggingT (Log ω) μ α → μ α
logToStderr cso trx = logToTTY cso trx stderr

--------------------

logToStderr' ∷ ∀ ω α μ . (MonadIO μ, MonadMask μ) =>
               [LogR ω] → [LogTransformer ω] → LoggingT (Log ω) μ α → μ α
logToStderr' annos trx = logToTTY' annos trx stderr

----------------------------------------

{-| log to a handle, assuming it's a terminal, with no log decorations -}
logToTTYPlain ∷ ∀ ω α μ . (MonadIO μ, MonadMask μ) =>
                [LogTransformer ω] → Handle → LoggingT (Log ω) μ α → μ α
logToTTYPlain trx = logToTTY' [] trx

----------------------------------------

mapLog ∷ ∀ α β . ([LogEntry α] → [LogEntry β]) → Log α → Log β
mapLog f (Log l) = Log ∘ fromList $ f (toList l)

mapLogE ∷ ∀ α β . (LogEntry α → LogEntry β) → Log α → Log β
mapLogE f = mapLog (fmap f)

--------------------------------------------------------------------------------
--                                   tests                                    --
--------------------------------------------------------------------------------

-- test data ---------------------------

_log0 ∷ Log ()
_log0 = fromList [_le0]

_log0m ∷ MonadLog (Log ()) η => η ()
_log0m = logMessage _log0

_log1 ∷ Log ()
_log1 = fromList [ _le0, _le1, _le2, _le3 ]

_log1m ∷ MonadLog (Log ()) η => η ()
_log1m = logMessage _log1

_log2 ∷ MonadLog (Log ℕ) η => η ()
_log2 = do logT Warning       1 "start"
           logT Informational 3 "middle"
           logT Critical      2 "end"

_log0io ∷ (MonadIO μ, MonadLog (Log ℕ) μ) => μ ()
_log0io = do logIO @𝕋 Warning 1 "start"
             liftIO $ threadDelay 1_000_000
             logIO @𝕋 Informational 3 "middle"
             liftIO $ threadDelay 1_000_000
             logIO @𝕋 Critical 2 "end"

_log1io ∷ (MonadIO μ, MonadLog (Log ℕ) μ) => μ ()
_log1io = do logIO @𝕋 Warning 1 "start"
             liftIO $ threadDelay 1_000_000
             logIO @𝕋 Informational 3 "you shouldn't see this"
             liftIO $ threadDelay 1_000_000
             logIO @𝕋 Critical 2 "end"

-- tests -------------------------------

tests ∷ TestTree
tests = testGroup "Log" [ logRender'Tests, eMonadTests, fileSizeRotatorTests ]

----------------------------------------

_test ∷ IO ExitCode
_test = runTestTree tests

--------------------

_tests ∷ String → IO ExitCode
_tests = runTestsP tests

_testr ∷ String → ℕ → IO ExitCode
_testr = runTestsReplay tests

{-| manual tests - run these by hand, there is no automated testing option for
    these -}
_testm ∷ IO ()
_testm = do
  logToStderr   NoCallStack   []        _log0io
  logToTTYPlain               [] stderr _log0io
  logToTTY      NoCallStack   [] stderr _log0io
  logToTTY      CallStackHead [] stderr _log0io
  logToTTY      CallStackHead [] stderr _log0io

-- that's all, folks! ----------------------------------------------------------
