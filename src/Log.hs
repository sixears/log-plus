module Log
  ( CSOpt(..), Log, ToDoc_( toDoc_ ), WithLog, WithLogIO

  , emergency, alert, critical, err, warn, notice, info, debug
  , emergency', alert', critical', err', warn', notice', info', debug'
  , emergencyT, alertT, criticalT, errT, warnT, noticeT, infoT, debugT

  , fromList
  , log, logMsg, log', logMsg', logT, logMsgT, logT', logMsgT'
  , logIO, logIO', logIOT
  , logIOL, logIOL', logIOLT
  , logRender, logRender'
  , logToFD', logToFD, logToFile, logToFiles, logToFileHandleNoAdornments, logToStderr
  , logToStderr'
  , stackOptions, stackParses, stdRenderers
  , logFilter, mapLog, mapLogE
  , simpleRotator
  -- test data
  , tests, _log0, _log0m, _log1, _log1m )
where

-- base --------------------------------

import qualified Control.Concurrent.MVar  as  MVar
import qualified  Data.Foldable           as  Foldable

import Control.Applicative      ( Applicative( (<*>), pure ) )
import Control.Concurrent       ( forkIO, threadDelay )
import Control.Monad            ( Monad, (>>=), forM_, join, return )
import Control.Monad.IO.Class   ( MonadIO, liftIO )
import Data.Bool                ( Bool( True ) )
import Data.Either              ( either )
import Data.Eq                  ( Eq )
import Data.Foldable            ( Foldable, all, concatMap, foldl', foldl1
                                , foldMap, foldr, foldr1 )
import Data.Function            ( ($), (&), const, flip, id )
import Data.Functor             ( Functor, fmap )
import Data.List                ( reverse, zip )
import Data.List.NonEmpty       ( NonEmpty( (:|) ), nonEmpty )
import Data.Maybe               ( Maybe( Just, Nothing ), catMaybes, maybe )
import Data.Monoid              ( Monoid )
import Data.Ord                 ( Ord, (>) )
import Data.Semigroup           ( Semigroup )
import Data.String              ( String )
import Data.Tuple               ( fst, snd, uncurry )
import Data.Word                ( Word16, Word64 )
import GHC.Enum                 ( Enum )
import GHC.Exts                 ( IsList( Item, fromList, toList ) )
import GHC.Generics             ( Generic )
import GHC.Num                  ( Num, (+) )
import GHC.Real                 ( Integral, Real, div, fromIntegral )
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

-- data-default ------------------------

import Data.Default  ( Default( def ) )

-- data-textual ------------------------

import Data.Textual  ( Printable( print ), toText )

-- deepseq -----------------------------

import Control.DeepSeq  ( NFData )

-- dlist -------------------------------

import qualified  Data.DList  as  DList
import Data.DList  ( DList, singleton )

-- exceptions --------------------------

import Control.Monad.Catch  ( MonadMask )

-- fpath -------------------------------

import FPath.AbsFile        ( absfile )
import FPath.File           ( File )
import FPath.FileLike       ( (⊙) )
import FPath.Parseable      ( __parse'__ )
import FPath.PathComponent  ( PathComponent, pc )

-- lens --------------------------------

import Control.Lens.Getter     ( view )
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

import MonadIO.Error.CreateProcError  ( ProcError )
import MonadIO.File                   ( devnull, rename )
import MonadIO.FStat                  ( FExists( FExists ), lfexists )
import MonadIO.NamedHandle            ( ℍ, HEncoding( NoEncoding ),
                                        handle, hClose, hname )
import MonadIO.OpenFile               ( FileOpenMode( FileR, FileW ), openFile )
import MonadIO.Process                ( doProc )
import MonadIO.Process.CmdSpec        ( mkCmd )

-- mono-traversable --------------------

import Data.MonoTraversable  ( Element
                             , MonoFoldable( ofoldl', ofoldl1Ex', ofoldr
                                           , ofoldr1Ex , ofoldMap, olength
                                           , otoList )
                             , MonoFunctor( omap )
                             )

-- more-unicode ------------------------

import Data.MoreUnicode.Applicative  ( (⋫) )
import Data.MoreUnicode.Bool         ( 𝔹, pattern 𝓣 )
import Data.MoreUnicode.Either       ( 𝔼, pattern 𝓛, pattern 𝓡 )
import Data.MoreUnicode.Functor      ( (⊳), (⊳⊳), (⩺) )
import Data.MoreUnicode.Lens         ( (⊣), (⊧), (⩼) )
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

import Safe  ( headDef )

-- single ------------------------------

import Single( MonoSingle( osingle ), single )

-- tasty -------------------------------

import Test.Tasty        ( TestName, TestTree, testGroup )
import Test.Tasty.HUnit  ( Assertion, assertBool, testCase )

-- tasty-plus --------------------------

import TastyPlus         ( assertIsJust, assertLeft, assertListEq, assertListEqIO
                         , runTestsP, runTestsReplay, runTestTree )
import TastyPlus.Equish  ( Equish( (≃) ) )

-- terminal-size -----------------------

import qualified  System.Console.Terminal.Size  as  TerminalSize

-- text --------------------------------

import qualified Data.Text.Lazy

import Data.Text     ( intercalate, length, lines, unlines )
import Data.Text.IO  ( hPutStr, hPutStrLn )

-- text-printer ------------------------

import qualified  Text.Printer  as  P

-- time --------------------------------

import Data.Time.Clock     ( getCurrentTime )

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

{- | A list of LogEntries. -}
newtype Log ω = Log { unLog ∷ DList (LogEntry ω) }
  deriving (Eq,Functor,Generic,Monoid,NFData,Semigroup,Show)

{- | `WithLog` adds in the `CallStack` constraint, so that if you declare your
     function to use this constraint, your function will be included in the
     logged callstack.  If you do not include the `CallStack` constraint, then
     the callpoint from within the function lacking the constraint (and anything
     calling it) will not be shown in the callstack.
 -}
type WithLog α η = (MonadLog (Log α) η, ?stack ∷ CallStack)
{- | `WithLog`, but with MonadIO, too. -}
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

instance Printable ω ⇒ Printable (Log ω) where
  print = P.text ∘ unlines ∘ toList ∘ fmap toText ∘ unLog

instance Equish ω ⇒ Equish (Log ω) where
  l ≃ l' = olength l ≡ olength l'
         ∧ all (\ (x,x') → x ≃ x') (zip (otoList l) (otoList l'))

instance MonoSingle (Log ω) where
  osingle w = Log (single w)

------------------------------------------------------------

{- | This is called `ToDoc_` with an underscore to distinguish from any `ToDoc`
     class that took a parameter for the annotation type. -}
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

{- | `vsep` returns an emptyDoc for an empty list; that results in a blank line.
      We often don't want that; the blank line appears whenever a log was
      filtered; which would really suck for heavily filtered logs (thus
      discouraging the use of logs for infrequently looked-at things - but then
      making it awkward to debug irritating edge-cases.  So we define a `vsep`
      variant, `vsep'`, which declares `Nothing` for empty docs, thus we can
      completely ignore them (don't call the logger at all).
-}
vsep' ∷ [Doc α] → 𝕄 (Doc α)
vsep' [] = Nothing
vsep' xs = Just $ vsep xs

------------------------------------------------------------

{- | Log with a timestamp, thus causing IO.  This version keeps IO & logging as
     split monads, because once joined, the only way to split them is to run
     the logging.
 -}
logIOL ∷ ∀ ρ ω μ η . (WithLogIOL ω μ η, ToDoc_ ρ) ⇒ Severity → ω → ρ → μ (η ())
logIOL sv p txt = do
  -- note that callstack starts here, *including* the call to logIO; this is
  -- deliberate, so that we see where in the code we made the log
  tm ← liftIO getCurrentTime
  return $
    logMessage ∘ Log ∘ singleton $ logEntry ?stack (Just tm) sv (toDoc_ txt) p

--------------------

-- We redefine this, rather than simply calling logIOL, so as to not mess with
-- the callstack.
{- | Log with a timestamp, thus causing IO.  This version keeps IO & logging as
     split monads, because once joined, the only way to split them is to run
     the logging. -}
logIOL' ∷ ∀ ρ ω μ η . (WithLogIOL ω μ η, ToDoc_ ρ, Default ω) ⇒
           Severity → ρ → μ (η ())
logIOL' sv txt = do
  tm ← liftIO getCurrentTime
  return $
    logMessage ∘ Log ∘ singleton $ logEntry ?stack (Just tm) sv (toDoc_ txt) def

--------------------

-- We redefine this, rather than simply calling logIOL, so as to not mess with
-- the callstack.
{- | Log `Text` with a timestamp, thus causing IO. -}
logIOLT ∷ ∀ ω μ η . (WithLogIOL ω μ η, Default ω) ⇒ Severity → 𝕋 → μ (η ())
logIOLT sv txt = do
  tm ← liftIO getCurrentTime
  return $
    logMessage ∘ Log ∘ singleton $ logEntry ?stack (Just tm) sv (toDoc_ txt) def

----------------------------------------

{- | Log with a timestamp, thus causing IO. -}
logIO ∷ ∀ ρ ω μ . (WithLogIO ω μ, ToDoc_ ρ) ⇒ Severity → ω → ρ → μ ()
logIO sv p txt = do
  -- note that callstack starts here, *including* the call to logIO; this is
  -- deliberate, so that we see where in the code we made the log
  tm ← liftIO getCurrentTime
  logMessage ∘ Log ∘ singleton $ logEntry ?stack (Just tm) sv (toDoc_ txt) p

--------------------

-- We redefine this, rather than simply calling logIO, so as to not mess with
-- the callstack.
{- | Log with a timestamp, thus causing IO. -}
logIO' ∷ ∀ ρ ω μ . (WithLogIO ω μ, ToDoc_ ρ, Default ω) ⇒ Severity → ρ → μ ()
logIO' sv txt = do
  tm ← liftIO getCurrentTime
  logMessage ∘ Log ∘ singleton $ logEntry ?stack (Just tm) sv (toDoc_ txt) def

----------------------------------------

-- We redefine this, rather than simply calling logIO, so as to not mess with
-- the callstack.
{- | Log `Text` with a timestamp, thus causing IO. -}
logIOT ∷ ∀ ω μ . (WithLogIO ω μ, Default ω) ⇒ Severity → 𝕋 → μ ()
logIOT sv txt = do
  tm ← liftIO getCurrentTime
  logMessage ∘ Log ∘ singleton $ logEntry ?stack (Just tm) sv (toDoc_ txt) def

----------------------------------------

{- | Log with no IO, thus no timestamp. -}
log ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ) ⇒ Severity → ω → ρ → η ()
log sv p txt =
  logMessage ∘ Log ∘ singleton $ logEntry ?stack Nothing sv (toDoc_ txt) p

{- | Alias for `log`, to avoid clashing with `Prelude.log`. -}
logMsg ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ) ⇒ Severity → ω → ρ → η ()
logMsg = log

----------

{- | `log`, with a default value. -}
log' ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ, Default ω) ⇒ Severity → ρ → η ()
log' sv txt = do
  logMessage ∘ Log ∘ singleton $ logEntry ?stack Nothing sv (toDoc_ txt) def

----------

{- | Alias for `log'`, for consistency with `logMsg`. -}
logMsg' ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ, Default ω) ⇒ Severity → ρ → η ()
logMsg' = log'

----------

{- | `log`, with input type fixed to Text to avoid having to specify. -}
logT ∷ ∀ ω η . (WithLog ω η) ⇒ Severity → ω → 𝕋 → η ()
logT sv p txt =
  logMessage ∘ Log ∘ singleton $ logEntry ?stack Nothing sv (toDoc_ txt) p

----------

{- | Alias for `logT`, for consistency with `logMsg`. -}
logMsgT ∷ ∀ ω η . (WithLog ω η) ⇒ Severity → ω → 𝕋 → η ()
logMsgT sv p txt =
  logMessage ∘ Log ∘ singleton $ logEntry ?stack Nothing sv (toDoc_ txt) p

----------

{- | `log'`, with input type fixed to Text to avoid having to specify. -}
logT' ∷ ∀ ω η . (WithLog ω η, Default ω) ⇒ Severity → 𝕋 → η ()
logT' sv txt =
  logMessage ∘ Log ∘ singleton $ logEntry ?stack Nothing sv (toDoc_ txt) def

----------

{- | Alias for `logT'`, for consistency with `logMsg`. -}
logMsgT' ∷ ∀ ω η . (WithLog ω η, Default ω) ⇒ Severity → 𝕋 → η ()
logMsgT' sv txt =
  logMessage ∘ Log ∘ singleton $ logEntry ?stack Nothing sv (toDoc_ txt) def

--------------------

emergency ∷ (WithLog ω η, ToDoc_ ρ) ⇒ ω → ρ → η ()
emergency = log Emergency

----------

emergency' ∷ (WithLog ω η, ToDoc_ ρ, Default ω) ⇒ ρ → η ()
emergency' = log Emergency def

----------

emergencyT ∷ (WithLog ω η, Default ω) ⇒ 𝕋 → η ()
emergencyT = emergency'

----------

alert ∷ (WithLog ω η, ToDoc_ ρ) ⇒ ω → ρ → η ()
alert = log Alert

----------

alert' ∷ (WithLog ω η, ToDoc_ ρ, Default ω) ⇒ ρ → η ()
alert' = log Alert def

----------

alertT ∷ (WithLog ω η, Default ω) ⇒ 𝕋 → η ()
alertT = alert'

----------

critical ∷ (WithLog ω η, ToDoc_ ρ) ⇒ ω → ρ → η ()
critical = log Critical

----------

critical' ∷ (WithLog ω η, ToDoc_ ρ, Default ω) ⇒ ρ → η ()
critical' = log Critical def

----------

criticalT ∷ (WithLog ω η, Default ω) ⇒ 𝕋 → η ()
criticalT = critical'

----------

err ∷ (WithLog ω η, ToDoc_ ρ) ⇒ ω → ρ → η ()
err = log Error

----------

err' ∷ (WithLog ω η, ToDoc_ ρ, Default ω) ⇒ ρ → η ()
err' = log Error def

----------

errT ∷ (WithLog ω η, Default ω) ⇒ 𝕋 → η ()
errT = err'

----------

warn ∷ (WithLog ω η, ToDoc_ ρ) ⇒ ω → ρ → η ()
warn = log Warning

----------

warn' ∷ (WithLog ω η, ToDoc_ ρ, Default ω) ⇒ ρ → η ()
warn' = log Warning def

----------

warnT ∷ (WithLog ω η, Default ω) ⇒ 𝕋 → η ()
warnT = warn'

----------

notice ∷ (WithLog ω η, ToDoc_ ρ) ⇒ ω → ρ → η ()
notice = log Notice

----------

notice' ∷ (WithLog ω η, ToDoc_ ρ, Default ω) ⇒ ρ → η ()
notice' = log Notice def

----------

noticeT ∷ (WithLog ω η, Default ω) ⇒ 𝕋 → η ()
noticeT = notice'

----------

info ∷ (WithLog ω η, ToDoc_ ρ) ⇒ ω → ρ → η ()
info = log Informational

----------

info' ∷ (WithLog ω η, ToDoc_ ρ, Default ω) ⇒ ρ → η ()
info' = log Informational def

----------

infoT ∷ (WithLog ω η, Default ω) ⇒ 𝕋 → η ()
infoT = info'

----------

debug ∷ (WithLog ω η, ToDoc_ ρ) ⇒ ω → ρ → η ()
debug = log Debug

----------

debug' ∷ (WithLog ω η, ToDoc_ ρ, Default ω) ⇒ ρ → η ()
debug' = log Debug def

----------

debugT ∷ (WithLog ω η, Default ω) ⇒ 𝕋 → η ()
debugT = debug'

----------------------------------------

type LogTransformer ω = LogEntry ω → [LogEntry ω]

{- | Create a log filter from a predicate, for ease of making `LogTransformer`s.
 -}
logFilter ∷ (LogEntry ω → 𝔹) → LogEntry ω  → [LogEntry ω]
logFilter p le = if p le then [le] else []

{- | Render a log to a list of Docs, per `LogRenderOpts` and applying
     `LogEntry` transformers along the way.
-}
renderMapLog ∷ Foldable ψ ⇒
               (LogEntry ω → Doc ρ) → ψ (LogTransformer ω) → Log ω
             → [Doc ρ]
renderMapLog renderer trx ls =
  let -- trx' ∷ LogTransformer ω
      trx' = foldr (\ a b → concatMap a ∘ b) (:[]) trx
   in renderer ⊳ (toList ls ≫ trx')

renderMapLog' ∷ Foldable ψ ⇒
                (LogEntry ω → Doc ρ) → ψ (LogTransformer ω) → LogEntry ω
              → 𝕄 (Doc ρ)
renderMapLog' renderer trx le = vsep' ∘ renderMapLog renderer trx $ osingle le

----------------------------------------

{- | Transform a monad ready to return (rather than effect) the logging. -}
logRender ∷ Monad η ⇒
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

{- | `logRender` with `()` is sufficiently common to warrant a cheap alias. -}
logRender' ∷ Monad η ⇒
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
      msgLen d = pretty (length $ docTxt d)
      msgTrim ∷ Doc ρ → Doc () -- trim to one line
      msgTrim d = pretty (headDef "" ∘ lines $ docTxt d)
      msgLenTransform ∷ LogEntry ρ → [LogEntry ρ]
      msgLenTransform le = [le & logdoc ⊧ msgLen]
      msgTrimTransform ∷ LogEntry ρ → [LogEntry ρ]
      msgTrimTransform le = [le & logdoc ⊧ msgTrim]
      exp2 ∷ [𝕋]
      exp2 = [ intercalate "\n" [ "[Info] log_entry 1"
                                , "  stack0, called at c:1:2 in a:b"
                                , "    stack1, called at f:5:6 in d:e"
                                ]
             ]
      exp3 ∷ [𝕋]
      exp3 = [ "[1970-01-01Z00:00:00 Thu] [Info] «c#1» log_entry 1"
             , intercalate "\n" [   "[-----------------------] [CRIT] «y#9» "
                                  ⊕ "multi-line"
                                ,   "                                       "
                                  ⊕ "log"
                                ,   "                                       "
                                  ⊕ "message"
                                ]
             , intercalate "\n"
                           [ "[1970-01-01Z00:00:00 Thu] [Warn] «y#9» this is a"
                           ,   "                                               "
                             ⊕ "vertically aligned"
                           ,   "                                               "
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

whenJust ∷ Monad η ⇒ (α → η ()) → 𝕄 α → η ()
whenJust _  Nothing  = return ()
whenJust io (Just y) = io y

------------------------------------------------------------

newtype NonEmptyMVar α = NonEmptyMVar { getMVar ∷ MVar.MVar α }

newMVar ∷ α → MonadIO μ => μ (NonEmptyMVar α)
newMVar = liftIO ∘ (NonEmptyMVar ⩺ MVar.newMVar)

-- Read the value (guaranteed to be present)
readMVar ∷ MonadIO μ => NonEmptyMVar α → μ α
readMVar = liftIO ∘ MVar.readMVar ∘ getMVar

-- Replace the value, ensuring the MVar remains non-empty
swapMVar ∷ MonadIO μ => NonEmptyMVar α → α → μ α
swapMVar (NonEmptyMVar mvar) = liftIO ∘ MVar.swapMVar mvar

-- Set the value, ensuring the MVar remains non-empty
setMVar ∷ MonadIO μ => NonEmptyMVar α → α → μ ()
-- we need to use MVar.swapMVar to ensure that the value is never empty, (which
-- would happen if we used take-then-put); and that the function doesn't stall
-- (which would happen when the mvar is full, i.e., always)
setMVar mvar val = swapMVar mvar val ⪼ return ()

------------------------------------------------------------

flusher ∷ ∀ δ σ ρ ψ μ . (MonadIO μ, Foldable ψ) => -- δ is, e.g., Handle
          (σ → 𝕋 → μ (δ,σ))               -- ^ handle generator
        → NonEmptyMVar σ                  -- ^ incoming handle state
        → (SimpleDocStream ρ → 𝕋)         -- ^ render SimpleDocStream ρ to 𝕋
--        → (δ → SimpleDocStream ρ → μ ())  -- ^ write messages to log
        → (δ → 𝕋 → μ ())  -- ^ write messages to log
        → PageWidth
        → ψ (Doc ρ)                       -- ^ messages to log
        → μ ()
flusher hgen stvar renderT r pw messages = do
  let layout ∷ Foldable ψ ⇒ ψ (Doc π) → SimpleDocStream π
      layout ms = layoutPretty (LayoutOptions pw)
                               (vsep (Foldable.toList ms) ⊕ line')
      sds = layout messages
      t   = renderT sds
  st ← liftIO$ readMVar stvar
  (h,st') ← hgen st t
  liftIO $ setMVar stvar st'
  -- XXX
  r h t

----------------------------------------

newtype SizeBytes = SizeBytes Word64
  deriving (Enum,Eq,Integral,Num,Ord,Real,Show)

{-| Log to a file, which is rotated by size.

    Every time we're about to write a log, we check to see the size of the file
    (as monitored from prior logwriting), and if we're about to exceed the given
    max size (and this isn't the first write to the file): we rotate the files,
    and log to a new file.
-}
-- state (σ) is (current handle in use,bytes written so far,
--               index (starts at zero, incrementing))

-- XXX add mode selector

takeWhileM ∷ Monad m => (a → m Bool) → [a] → m [a]
takeWhileM _ []     = return []
takeWhileM p (x:xs) = p x ≫ \ b → if b then (x:) ⊳ takeWhileM p xs else return []

pzstd ∷ MonadIO μ => File → File → ExceptT ProcError μ ()
pzstd f t = do
  let args = ["--quiet", "--check", toText f, "-o", toText t, "--rm"]
      exe  = Paths.pzstd
  null ← devnull
  () ← snd ⊳ doProc (return ()) null (uncurry mkCmd (exe,args))
  return ()

pzstd' ∷ File → File → IO ()
pzstd' f t = join $ eToStderr' ⊳ (ѥ @ProcError $ pzstd f t)

-- XXX  check threadID for completion: do not rotate if still compressing
-- XXX  choose compressor
-- XXX  -async compressor-
-- XXX  factor out compression
-- XXX  always write to the name
-- XXX  make compressor an IO job as input var (the rotator will fork it)

-- XXX test with & without compressor.

fileSizeRotator ∷ ∀ σ ω μ . (MonadIO μ, σ ~ (𝔼 File ℍ,SizeBytes,Word16)) =>
                  𝕄 (File → File → IO(), PathComponent) → SizeBytes → CMode → Word16
                → (Word16 → File) → σ → ω → 𝕋 → μ (Handle,σ)
fileSizeRotator compress max_size file_mode max_files fngen (ɦ,bytes_written,x) _sds t = do
  let l           = SizeBytes (ɨ $ щ t) -- length of t
      bytes_would = bytes_written + l
      fngen' i    = maybe id (\ e → (⊙ e)) (snd ⊳ compress) $ fngen i
      mkhandle fn = do
        -- only compress when making the first archive file
        let proto_moves = (either id (view hname) ɦ, fngen 0, compress)
                        : (uncurry (,,𝓝) ⊳
                          ((over both fngen')⊳zip [0..max_files] [1..max_files]))
        mv_files ← flip takeWhileM proto_moves $ \ (from,_to,_do_compress) →
          (≡ 𝓙 FExists) ⊳⊳ ꙝ @IOError $ lfexists from
        liftIO $ forM_ (reverse mv_files) $ \ (from,to,do_compress) → do
          ꙝ' $ rename @IOError from to
          case do_compress of
            𝓝 → return 𝓝
            𝓙 (c,ext) → 𝓙 ⊳ forkIO (c to (to⊙ext))
        let -- open a file, mode 0644, raise if it fails
            open_file ∷ MonadIO μ => File → μ ℍ
            open_file = ж ∘ openFile @IOError NoEncoding (FileW (𝓙 file_mode))
        open_file fn
  case ɦ of
    𝓡 𝕙 → if bytes_written ≠ 0 ∧ bytes_would > max_size
          -- XXX move old file; allow setting of perms
          then do hClose 𝕙
                  𝕙' ← mkhandle (𝕙 ⊣ hname)
                  return (𝕙' ⊣ handle,(𝓡 𝕙',l,x+1))
          else return (𝕙 ⊣ handle,(𝓡 𝕙,bytes_would,x))
    𝓛 ħ → mkhandle ħ ≫ \ 𝕙' → return (𝕙' ⊣ handle,(𝓡 𝕙',l,x+1))

----------------------------------------

{- | Write to an FD with given options, using `withBatchedHandler`.
     Each log entry is vertically separated.
 -}
withFDHandler ∷ ∀ α δ σ ρ μ . (MonadIO μ, MonadMask μ) ⇒
               (σ → SimpleDocStream ρ → 𝕋 → IO (δ,σ))
             → (SimpleDocStream ρ → 𝕋)
             → (δ → 𝕋 → IO())
             → PageWidth
             → BatchingOptions
             → σ
             → (Handler μ (Doc ρ) → μ α) -- A.K.A, (Doc ρ → μ ()) → μ α
             → μ (α,σ)

withFDHandler hgen renderT r pw bopts st handler = do
  -- even though this looks like it should happen every time through the loop;
  -- tracing it, it clearly doesn't.  I don't know why, I guess it's something
  -- to do with the construction of monadlog: but I don't seem to need to worry
  -- about the cost of creating new mvars
  stvar ← newMVar st
  let layout ∷ Foldable ψ ⇒ ψ (Doc π) → SimpleDocStream π
      layout ms = layoutPretty (LayoutOptions pw)
                               (vsep (Foldable.toList ms) ⊕ line')
      -- flush ∷ Foldable ψ ⇒ ψ (Doc ρ) → IO ()
      flush ms = flusher (\ ṡ t → hgen ṡ (layout ms) t) stvar renderT r pw ms
  a ← withBatchedHandler bopts flush handler
  st' ← readMVar stvar
  return (a,st')

----------------------------------------

{- | Write to an FD with given options, immediately (in thread), no batching.
     Each log entry has a newline appended.
 -}
withSimpleHandler ∷ MonadIO μ ⇒
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
      renderEntry e = let go d = do let sds {- ∷ SimpleDocStream ρ -} = layout d
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
                                      , blockWhenFull     = True
                                      , flushMaxQueueSize = 100
                                      }

{-| Options suitable for logging to a tty; notably a short flush delay (0.1s),
    and drop messages rather than blocking if the queue fills (which should
    be unlikely, with a length of 100 & 0.1s flush).
 -}
{-
ttyBatchingOptions ∷ BatchingOptions
-- The max delay is a matter of experimentation; too high, and messages appear
-- long after their effects on stdout are apparent (not *wrong*, but a bit
-- misleading/inconvenient); too low, and the message lines get broken up
-- and intermingled with stdout (again, not *wrong*, but a terrible user
-- experience).
ttyBatchingOptions = BatchingOptions { flushMaxDelay     = 2_000
                                     , blockWhenFull     = False
                                     , flushMaxQueueSize = 100
                                     }
-}

----------------------------------------

{-| Write a Log to a filehandle, with given rendering and options.
    The handle is created by a generator function, which may keep state.
-}
logToHandles ∷ ∀ α σ ρ ω μ  . (MonadIO μ, MonadMask μ) =>
               (σ → SimpleDocStream ρ → 𝕋 → IO (Handle, σ)) -- ^ handle generator
             → (SimpleDocStream ρ → 𝕋)
             → (LogEntry ω → 𝕄 (Doc ρ)) -- ^ render a LogEntry
             → 𝕄 BatchingOptions
             → PageWidth
             → σ
             → LoggingT (Log ω) μ α
             → μ (α,σ)

logToHandles hgen renderT renderEntry mbopts width st io = do
  let renderIO h t = hPutStr h t ⪼ hFlush h -- ∷ Handle→ SimpleDocStream ρ →IO()
  (fh,ṡṫ) ← liftIO $ hgen st SEmpty ""
  a ← case mbopts of
    𝓝       → withSimpleHandler renderT width fh renderIO renderEntry io
    𝓙 bopts →
      let renderDoc {- Log ω → 𝕄 (Doc ρ) -} =
            vsep ∘ toList ⩺ nonEmpty ∘ catMaybes ∘ fmap renderEntry ∘otoList

          -- handler ∷ (𝕄 (Doc ρ) → μ ()) → μ α
          handler h  = runLoggingT io (whenJust h ∘ renderDoc)

          -- XXX use PathComponent, possibly in conjunction with
          -- AbsFile.updateBasename, to make this safe
          -- fngen = __parse'__ @AbsFile ∘ [fmt|/tmp/foo.%d.zst|]
          -- hgen  = fileSizeRotator 10 fngen
--       in fst ⊳ withFDHandler hgen renderT renderIO width bopts (𝓙 fh,0,0) handler
       in fst ⊳ withFDHandler hgen renderT renderIO width bopts ṡṫ handler
  return (a,ṡṫ)

----------------------------------------

{-| simple handle generator for use with logToHandles, that always uses a single
    filehandle -}
staticHandle ∷ ∀ ρ μ . MonadIO μ =>
               Handle → SimpleDocStream ρ → 𝕋 → μ (Handle,Handle)
staticHandle h _ _ = return (h,h)

----------------------------------------

{- | Write a log to a filehandle, generated at need, with given options but no
     adornments. -}
logToHandlesNoAdornments ∷ ∀ α ω μ σ . (MonadIO μ, MonadMask μ) ⇒
                           (σ → SimpleDocStream AnsiStyle → 𝕋 → IO (Handle, σ))
                           -- ^ handle generator
                         → 𝕄 BatchingOptions
                         → LogRenderOpts ω
                         → [LogTransformer ω]
                         → σ
                         → LoggingT (Log ω) μ α
                         → μ α
logToHandlesNoAdornments hgen bopts lro trx st io =
  fst ⊳ logToHandles hgen RenderText.renderStrict
                     (renderMapLog' (lroRenderer lro) trx) bopts (lro ⊣ lroWidth)
                     st io

--------------------

{- | Write a Log to a filehandle, with given options but no adornments. -}
logToHandleNoAdornments ∷ (MonadIO μ, MonadMask μ) ⇒
                          𝕄 BatchingOptions
                        → LogRenderOpts ω
                        → [LogTransformer ω]
                        → Handle
                        → LoggingT (Log ω) μ α
                        → μ α
logToHandleNoAdornments = logToHandlesNoAdornments staticHandle

--------------------

{- | Write a Log to a filehandle, with given options and Ansi adornments. -}
logToHandleAnsi ∷ (MonadIO μ, MonadMask μ) ⇒
                  𝕄 BatchingOptions
                → LogRenderOpts ω
                → [LogTransformer ω]
                → Handle
                → LoggingT (Log ω) μ α
                → μ α
logToHandleAnsi bopts lro trx fh io =
  fst ⊳ logToHandles staticHandle
                     (Data.Text.Lazy.toStrict ∘ RenderTerminal.renderLazy)
                     (renderMapLog' (lroRenderer lro) trx)
                     bopts
                     (lro ⊣ lroWidth)
                     fh
                     io

----------------------------------------

{- | Log to a regular file, with unbounded width. -}
logToFileHandleNoAdornments ∷ (MonadIO μ, MonadMask μ) ⇒
                              [LogR ω] → [LogTransformer ω] → Handle
                            → LoggingT (Log ω) μ α → μ α
logToFileHandleNoAdornments ls trx =
  let lro = logRenderOpts' ls Unbounded
   in logToHandleNoAdornments (Just fileBatchingOptions) lro trx

--------------------

{- | Log to a tty, using current terminal width. -}
logToTTY' ∷ (MonadIO μ, MonadMask μ) ⇒
            [LogR ω] → [LogTransformer ω] → Handle → LoggingT (Log ω) μ α → μ α
logToTTY' ls trx h io = do
  size ← liftIO $ TerminalSize.size
  let lro = case size of
              Just sz → let width = AvailablePerLine (TerminalSize.width sz) 1.0
                         in logRenderOpts' ls width
              Nothing → logRenderOpts' ls Unbounded
  logToHandleAnsi Nothing lro trx h io

--------------------

{- | Log to a file handle; if it looks like a terminal, use Ansi logging and low
     batch time; else go unadorned with higher batch time. -}
logToFD' ∷ (MonadIO μ, MonadMask μ) ⇒
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

{- | Lookup table of CSOpt to possible (case-insensitive) string
     representations. -}
stackParses ∷ CSOpt → [String]
stackParses NoCallStack   = [ "NoCallStack", "NoCS" ]
stackParses CallStackHead = [ "CallStackHead", "CSHead", "CSH" ]
stackParses FullCallStack = [ "FullCallStack", "FullCS", "CallStack", "Stack" ]

{- | Lookup table of String to CSOpt; these are the strings that will be parsed
     to CSOpt (with `Parseable`).  Parsing is case-insensitive. -}
stackOptions ∷ NonEmpty (String,CSOpt)
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

instance Parsecable CSOpt where
  parser =
    tries [ caseInsensitiveString st ⋫ return cso | (st,cso) ← stackOptions ]

stdRenderers ∷ CSOpt → [LogR ω]
stdRenderers NoCallStack =
  [ renderWithTimestamp, renderWithSeverity ]
stdRenderers CallStackHead =
  [ renderWithTimestamp, renderWithSeverity, renderWithStackHead ]
stdRenderers FullCallStack =
  [ renderWithCallStack, renderWithTimestamp, renderWithSeverity ]

{- | Log to a plain file with given callstack choice, and given annotators. -}
logToFile ∷ (MonadIO μ, MonadMask μ) ⇒
            CSOpt → [LogTransformer ω] → Handle → LoggingT (Log ω) μ α → μ α
logToFile cso trx =
  logToFileHandleNoAdornments (stdRenderers cso) trx

{-| run `io`, logging to rotating files -}
logToFiles ∷ ∀ α ω μ σ . (MonadIO μ, MonadMask μ, σ ~ (𝔼 File ℍ, SizeBytes, Word16)) =>
             [LogR ω] → [LogTransformer ω]
           → (σ → SimpleDocStream AnsiStyle → 𝕋 → IO (Handle, σ))
           → File → LoggingT (Log ω) μ α → μ α
logToFiles ls trx rt fn io =
 let opts = Just fileBatchingOptions
     lro  = logRenderOpts' ls Unbounded
 in  logToHandlesNoAdornments rt opts lro trx (𝓛 fn,0,0) io

compressPzstd ∷ (File → File → IO (), PathComponent)
compressPzstd = (pzstd', [pc|zst|])

{-| an instance of file rotator that defaults perms to 0o644, max files to 10,
    uses a pattern that appends numbers to the end of the filenames, and compresses
    archive files with pzstd -}
-- XXX set the compressor
-- XXX while duplicate the file name?
simpleRotator ∷ ∀ ω μ . MonadIO μ =>
                𝕄 Word16 → 𝕄 CMode → SizeBytes → File → (𝔼 File ℍ, SizeBytes, Word16) → ω → 𝕋
              → μ (Handle, (𝔼 File ℍ, SizeBytes, Word16))
simpleRotator max_files perms sz fn =
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
  in  fileSizeRotator (𝓙 compressPzstd) sz (perms ⧏ 0o644) max_files'
                      ((fn ⊙) ∘ __parse'__ @PathComponent ∘ num ∘ fromIntegral)

--------------------

{- | Log to a terminal with given callstack choice. -}
logToTTY ∷ (MonadIO μ, MonadMask μ) ⇒
           CSOpt → [LogTransformer ω] → Handle → LoggingT (Log ω) μ α → μ α
logToTTY cso trx = logToTTY' (stdRenderers cso) trx

--------------------

{- | Log to a file handle; if it looks like a terminal, use Ansi logging and
     current terminal width; else go unadorned with unbounded width. -}
logToFD ∷ (MonadIO μ, MonadMask μ) ⇒
          CSOpt → [LogTransformer ω] → Handle → LoggingT (Log ω) μ α → μ α
logToFD cso trx h io = do
  isatty ← liftIO $ hIsTerminalDevice h
  if isatty
  then logToTTY  cso trx h io
  else logToFile cso trx h io

----------------------------------------

{- | Log to stderr, assuming it's a terminal, with given callstack choice &
     filter. -}
logToStderr ∷ (MonadIO μ, MonadMask μ) ⇒
              CSOpt → [LogTransformer ω] → LoggingT (Log ω) μ α → μ α
logToStderr cso trx = logToTTY cso trx stderr

logToStderr' ∷ (MonadIO μ, MonadMask μ) ⇒
               [LogR ω] → [LogTransformer ω] → LoggingT (Log ω) μ α → μ α
logToStderr' annos trx = logToTTY' annos trx stderr

{- | Log to a handle, assuming it's a terminal, with no log decorations. -}
logToTTYPlain ∷ (MonadIO μ, MonadMask μ) ⇒
                [LogTransformer ω] → Handle → LoggingT (Log ω) μ α → μ α
logToTTYPlain trx = logToTTY' [] trx

----------------------------------------

mapLog ∷ ([LogEntry α] → [LogEntry β]) → Log α → Log β
mapLog f (Log l) = Log ∘ fromList $ f (toList l)

mapLogE ∷ (LogEntry α → LogEntry β) → Log α → Log β
mapLogE f = mapLog (fmap f)

--------------------------------------------------------------------------------
--                                   tests                                    --
--------------------------------------------------------------------------------

-- test data ---------------------------

_log0 ∷ Log ()
_log0 = fromList [_le0]

_log0m ∷ MonadLog (Log ()) η ⇒ η ()
_log0m = logMessage _log0

_log1 ∷ Log ()
_log1 = fromList [ _le0, _le1, _le2, _le3 ]

_log1m ∷ MonadLog (Log ()) η ⇒ η ()
_log1m = logMessage _log1

_log2 ∷ MonadLog (Log ℕ) η ⇒ η ()
_log2 = do logT Warning       1 "start"
           logT Informational 3 "middle"
           logT Critical      2 "end"

_log0io ∷ (MonadIO μ, MonadLog (Log ℕ) μ) ⇒ μ ()
_log0io = do logIO @𝕋 Warning 1 "start"
             liftIO $ threadDelay 1_000_000
             logIO @𝕋 Informational 3 "middle"
             liftIO $ threadDelay 1_000_000
             logIO @𝕋 Critical 2 "end"

_log1io ∷ (MonadIO μ, MonadLog (Log ℕ) μ) ⇒ μ ()
_log1io = do logIO @𝕋 Warning 1 "start"
             liftIO $ threadDelay 1_000_000
             logIO @𝕋 Informational 3 "you shouldn't see this"
             liftIO $ threadDelay 1_000_000
             logIO @𝕋 Critical 2 "end"

-- tests -------------------------------

tests ∷ TestTree
tests = testGroup "Log" [ logRender'Tests, eMonadTests ]

----------------------------------------

_test ∷ IO ExitCode
_test = runTestTree tests

--------------------

_tests ∷ String → IO ExitCode
_tests = runTestsP tests

_testr ∷ String → ℕ → IO ExitCode
_testr = runTestsReplay tests

{- | Manual tests - run these by hand, there is no automated testing option
     for these. -}
_testm ∷ IO ()
_testm = do
  logToStderr   NoCallStack   []        _log0io
  logToTTYPlain               [] stderr _log0io
  logToTTY      NoCallStack   [] stderr _log0io
  logToTTY      CallStackHead [] stderr _log0io
  logToTTY      CallStackHead [] stderr _log0io

-- that's all, folks! ----------------------------------------------------------
