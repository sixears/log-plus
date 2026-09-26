module Log
  ( Log, ToDoc_( toDoc_ )
  , WithLog, WithLogIO

  , emergency, alert, critical, err, warn, notice, info, debug
  , emergency', alert', critical', err', warn', notice', info', debug'
  , emergencyT, alertT, criticalT, errT, warnT, noticeT, infoT, debugT

  , fromList
  , log, logMsg, log', logMsg', logT, logMsgT, logT', logMsgT'
  , logIO, logIO', logIOT
  , logIOL, logIOL', logIOLT
  , logToFD', logToFD, logToFile, logToFiles, logToFiles'
  , logToFileHandleNoAdornments
  , logToStderr, logToStderr'
  , logFilter, mapLog, mapLogE
  , logToTTY, logToTTYPlain

  , HasCompressorMay( compressorMay )

  , compressPzstd
  )
where

import Base1T  hiding  ( toList )

-- XXX factor out rotators to separate modules
-- XXX move some functions to other modules

-- import Debug.Trace  ( traceShow, trace ) -- XXX

-- base --------------------------------

import qualified  Data.Foldable  as  Foldable

import Control.Concurrent.MVar  ( MVar, tryReadMVar, newEmptyMVar, newMVar
                                , readMVar, swapMVar )
import Data.List.NonEmpty       ( nonEmpty )
import Data.Maybe               ( catMaybes )
import GHC.Exts                 ( IsList( toList ) )
import System.IO                ( Handle, hFlush, hIsTerminalDevice, stderr )

-- dlist -------------------------------

import Data.DList  ( DList, singleton )

-- exceptions --------------------------

import Control.Monad.Catch  ( MonadMask )

-- logging-effect ----------------------

import Control.Monad.Log  ( BatchingOptions( BatchingOptions
                                           , blockWhenFull, flushMaxQueueSize )
                          , Handler, LoggingT
                          , Severity( Critical, Emergency, Error, Alert, Warning
                                    , Notice, Informational, Debug )
                          , flushMaxDelay, logMessage, runLoggingT
                          , withBatchedHandler
                          )

-- mono-traversable --------------------

import Data.MonoTraversable  ( MonoFoldable( otoList ) )

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

-- terminal-size -----------------------

import qualified  System.Console.Terminal.Size  as  TerminalSize

-- text --------------------------------

import Data.Text.Lazy qualified

import Data.Text.IO  ( hPutStr, hPutStrLn )

-- time --------------------------------

import Data.Time.Clock  ( getCurrentTime )

------------------------------------------------------------
--                     local imports                       -
------------------------------------------------------------

import Log.LogEntry          ( LogEntry, logEntry )
import Log.LogRenderOpts     ( LogR, LogRenderOpts
                             , logRenderOpts', lroRenderer, lroWidth )

import LogPlus.Async              ( HasAsync( waitAsync ) )
import LogPlus.CallStackOption    ( CallStackOption, stdRenderers)
import LogPlus.Compressor         ( HasCompressorMay( compressorMay )
                                  , compressPzstd )
import LogPlus.CompressorThread   ( HasCompressorThreadMay(compressorThreadMay))
import LogPlus.Log                ( Log, WithLog, WithLogIO, WithLogIOL
                                  , mapLog, mapLogE )
import LogPlus.LogRender          ( renderMapLog' )
import LogPlus.LogTransformer     ( LogTransformer )
import LogPlus.New                ( New( new ) )

--------------------------------------------------------------------------------

{-| this is called `ToDoc_` with an underscore to distinguish from any `ToDoc`
    class that took a parameter for the annotation type -}
class ToDoc_ α where
  toDoc_ ∷ α → Doc ()

instance ToDoc_ 𝕋 where
  toDoc_ = pretty

instance ToDoc_ (Doc()) where
  toDoc_ = id

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
    logMessage ∘ new ∘ singleton $ logEntry ?stack (𝓙 tm) sv (toDoc_ txt) p

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
    logMessage ∘ new @(Log ω) @(DList (LogEntry ω)) ∘ singleton $
      logEntry ?stack (𝓙 tm) sv (toDoc_ txt) def

--------------------

-- We redefine this, rather than simply calling logIOL, so as to not mess with
-- the callstack.
{-| log `Text` with a timestamp, thus causing IO -}
logIOLT ∷ ∀ ω μ η . (WithLogIOL ω μ η, Default ω) => Severity → 𝕋 → μ (η ())
logIOLT sv txt = do
  tm ← liftIO getCurrentTime
  return $
    logMessage ∘ new @(Log ω) @(DList (LogEntry ω)) ∘ singleton $
      logEntry ?stack (𝓙 tm) sv (toDoc_ txt) def

----------------------------------------

{-| log with a timestamp, thus causing IO -}
logIO ∷ ∀ ρ ω μ . (WithLogIO ω μ, ToDoc_ ρ) => Severity → ω → ρ → μ ()
logIO sv p txt = do
  -- note that callstack starts here, *including* the call to logIO; this is
  -- deliberate, so that we see where in the code we made the log
  tm ← liftIO getCurrentTime
  logMessage ∘ new ∘ singleton $ logEntry ?stack (𝓙 tm) sv (toDoc_ txt) p

--------------------

-- We redefine this, rather than simply calling logIO, so as to not mess with
-- the callstack.
{-| log with a timestamp, thus causing IO -}
logIO' ∷ ∀ ρ ω μ . (WithLogIO ω μ, ToDoc_ ρ, Default ω) => Severity → ρ → μ ()
logIO' sv txt = do
  tm ← liftIO getCurrentTime
  logMessage ∘ new @(Log ω) @(DList (LogEntry ω)) ∘ singleton $
      logEntry ?stack (𝓙 tm) sv (toDoc_ txt) def

----------------------------------------

-- We redefine this, rather than simply calling logIO, so as to not mess with
-- the callstack.
{-| log `Text` with a timestamp, thus causing IO -}
logIOT ∷ ∀ ω μ . (WithLogIO ω μ, Default ω) => Severity → 𝕋 → μ ()
logIOT sv txt = do
  tm ← liftIO getCurrentTime
  logMessage ∘ new @(Log ω) @(DList (LogEntry ω)) ∘ singleton $
      logEntry ?stack (𝓙 tm) sv (toDoc_ txt) def

----------------------------------------

{-| log with no IO, thus no timestamp -}
log ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ) => Severity → ω → ρ → η ()
log sv p txt =
  logMessage ∘ new ∘ singleton $ logEntry ?stack 𝓝 sv (toDoc_ txt) p

{-| alias for `log`, to avoid clashing with `Prelude.log` -}
logMsg ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ) => Severity → ω → ρ → η ()
logMsg = log

----------

{-| `log`, with a default value -}
log' ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ, Default ω) => Severity → ρ → η ()
log' sv txt = do
  logMessage ∘ new @(Log ω) @(DList (LogEntry ω)) ∘ singleton $
    logEntry ?stack 𝓝 sv (toDoc_ txt) def

----------

{-| alias for `log'`, for consistency with `logMsg` -}
logMsg' ∷ ∀ ω η ρ . (WithLog ω η, ToDoc_ ρ, Default ω) => Severity → ρ → η ()
logMsg' = log'

----------

{-| `log`, with input type fixed to Text to avoid having to specify -}
logT ∷ ∀ ω η . (WithLog ω η) => Severity → ω → 𝕋 → η ()
logT sv p txt =
  logMessage ∘ new ∘ singleton $ logEntry ?stack 𝓝 sv (toDoc_ txt) p

----------

{-| alias for `logT`, for consistency with `logMsg` -}
logMsgT ∷ ∀ ω η . (WithLog ω η) => Severity → ω → 𝕋 → η ()
logMsgT sv p txt =
  logMessage ∘ new ∘ singleton $ logEntry ?stack 𝓝 sv (toDoc_ txt) p

----------

{-| `log'`, with input type fixed to Text to avoid having to specify -}
logT' ∷ ∀ ω η . (WithLog ω η, Default ω) => Severity → 𝕋 → η ()
logT' sv txt =
  logMessage ∘ new @(Log ω) @(DList (LogEntry ω)) ∘ singleton $
    logEntry ?stack 𝓝 sv (toDoc_ txt) def

----------

{-| alias for `logT'`, for consistency with `logMsg`. -}
logMsgT' ∷ ∀ ω η . (WithLog ω η, Default ω) => Severity → 𝕋 → η ()
logMsgT' sv txt =
  logMessage ∘ new @(Log ω) @(DList (LogEntry ω)) ∘ singleton $
    logEntry ?stack 𝓝 sv (toDoc_ txt) def

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

{-| create a log filter from a predicate, for ease of making `LogTransformer`s -}
logFilter ∷ (LogEntry ω → 𝔹) → LogEntry ω  → [LogEntry ω]
logFilter p le = if p le then [le] else []

{-
{- XXX maove this to LogPlus.LogRender -}
{-| render a log to a list of Docs, per `LogRenderOpts` and applying `LogEntry`
    transformers along the way -}
renderMapLog ∷ ∀ ω ρ ψ . Foldable ψ =>
               (LogEntry ω → Doc ρ) → ψ (LogTransformer ω) → Log ω
             → [Doc ρ]
renderMapLog renderer trx ls =
  let -- trx' ∷ LogTransformer ω
      trx' = foldr (\ a b → concatMap a ∘ b) (:[]) trx
   in renderer ⊳ (toList ls ≫ trx')

--------------------

{- XXX maove this to LogPlus.LogRender -}
renderMapLog' ∷ ∀ ω ρ ψ . Foldable ψ =>
                (LogEntry ω → Doc ρ) → ψ (LogTransformer ω) → LogEntry ω
              → 𝕄 (Doc ρ)
renderMapLog' renderer trx le = vsep' ∘ renderMapLog renderer trx $ osingle le

----------------------------------------

{- XXX maove this to LogPlus.LogRender -}
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

{- XXX maove this to LogPlus.LogRender -}
{-| `logRender` with `()` is sufficiently common to warrant a cheap alias -}
logRender' ∷ ∀ ω η . Monad η =>
             LogRenderOpts ω → [LogTransformer ω] → PureLoggingT (Log ω) η ()
           → η [𝕋]
logRender' opts trx lg = snd ⊳ (logRender opts trx lg)
-}

----------

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

------------------------------------------------------------

----------------------------------------

{-| Write to an FD with given options, using `withBatchedHandler`. Each log entry
    is vertically separated. -}
withFDHandler ∷ ∀ α σ ρ μ . (MonadIO μ, MonadMask μ) =>
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
logToHandles ∷ ∀ α σ ρ ω μ  . (MonadIO μ, MonadMask μ) =>
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
logToHandlesNoAdornments ∷ ∀ α ω μ σ . (MonadIO μ, MonadMask μ) =>
                           (𝕄 σ→SimpleDocStream AnsiStyle→𝕋→IO (Handle, σ))
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

----------------------------------------

{-| log to a plain file with given callstack choice, and given annotators -}
logToFile ∷ ∀ ω α μ . (MonadIO μ, MonadMask μ) =>
            CallStackOption → [LogTransformer ω] → Handle → LoggingT (Log ω) μ α
          → μ α
logToFile cso trx =
  logToFileHandleNoAdornments (stdRenderers cso) trx

----------------------------------------

{-| run `io`, logging to rotating files -}
logToFiles' ∷ ∀ α ω μ σ . (MonadIO μ, MonadMask μ, HasCompressorThreadMay σ) =>
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
logToFiles ∷ ∀ α ω μ σ . (MonadIO μ, MonadMask μ, HasCompressorThreadMay σ) =>
             [LogR ω]                                               -- ^ trx
           → [LogTransformer ω]                                     -- ^ ls
           → (𝕄 σ → SimpleDocStream AnsiStyle → 𝕋 → IO (Handle, σ))
             -- ^ rt (rotator)
           → LoggingT (Log ω) μ α                                   -- ^ io
           → μ α
logToFiles = logToFiles' (𝓙 fileBatchingOptions)

----------------------------------------

{-| log to a terminal with given callstack choice -}
logToTTY ∷ ∀ ω α μ . (MonadIO μ, MonadMask μ) =>
           CallStackOption → [LogTransformer ω] → Handle → LoggingT (Log ω) μ α
         → μ α
logToTTY cso trx = logToTTY' (stdRenderers cso) trx

--------------------

{-| log to a file handle; if it looks like a terminal, use ANSI logging and
    current terminal width; else go unadorned with unbounded width -}
logToFD ∷ ∀ ω α μ . (MonadIO μ, MonadMask μ) =>
          CallStackOption → [LogTransformer ω] → Handle → LoggingT (Log ω) μ α
        → μ α
logToFD cso trx h io = do
  isatty ← liftIO $ hIsTerminalDevice h
  if isatty
  then logToTTY  cso trx h io
  else logToFile cso trx h io

----------------------------------------

{- | log to stderr, assuming it's a terminal, with given callstack choice &
     filter -}
logToStderr ∷ ∀ ω α μ . (MonadIO μ, MonadMask μ) =>
              CallStackOption → [LogTransformer ω] → LoggingT (Log ω) μ α → μ α
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

-- that's all, folks! ----------------------------------------------------------
