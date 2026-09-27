module LogPlus.LogRenderOpts
  ( LogR, LogRenderOpts

  , logRenderOpts'

  , lroOpts, lroRenderPlain, lroRenderSevCS, lroRenderSevCSH
  , lroRenderTSSev, lroRenderTSSevCS, lroRenderTSSevCSH
  , lroRenderer, lroWidth

  , renderWithCallStack, renderWithSeverity, renderWithStackHead
  , renderWithTimestamp

  , tests
  )
where

import Base1T

-- base --------------------------------

import Data.Type.Equality  ( type(~) )
import GHC.Stack           ( SrcLoc )
import System.IO           ( Handle, stdout )

-- lens --------------------------------

import Control.Lens  ( view )

-- logging-effect ----------------------

import Control.Monad.Log  ( Severity( Alert, Debug, Critical, Emergency, Error
                                    , Informational, Notice, Warning ) )

-- mono-traversable --------------------

import Data.MonoTraversable  ( Element, MonoFoldable( otoList )
                             , MonoFunctor( omap ) )

-- prettyprinter -----------------------

import Prettyprinter              ( Doc, LayoutOptions( LayoutOptions )
                                  , PageWidth( Unbounded )
                                  , defaultLayoutOptions, layoutPageWidth
                                  , layoutPretty, line, pretty, reAnnotate, vsep
                                  )
import Prettyprinter.Render.Text  ( renderStrict )

-- prettyprinter-ansi-terminal ---------


import qualified  Prettyprinter.Render.Terminal  as  Terminal
import Prettyprinter.Render.Terminal  ( AnsiStyle )

-- tasty-plus --------------------------

import TastyPlus  ( (≟), assertListEq )

-- text --------------------------------

import qualified  Data.Text  as  T

import Data.Text  ( Text )

------------------------------------------------------------
--                     Local Imports                      --
------------------------------------------------------------

import LogPlus.LogEntry    ( LogEntry , logdoc, logEntry )
import LogPlus.Render      ( renderWithCallStack, renderWithSeverity
                           , renderWithSeverityAndTimestamp
                           , renderWithSeverityAnsi, renderWithStackHead
                           , renderWithTimestamp
                           )
import LogPlus.T.TestData  ( _le0 )

--------------------------------------------------------------------------------

type LogR ω = (LogEntry ω → Doc AnsiStyle) → LogEntry ω → Doc AnsiStyle

------------------------------------------------------------

newtype LogRenderer ω = LogRenderer { unLogRenderer ∷ [LogR ω] }

--------------------

type instance Element (LogRenderer ω) = (LogR ω)

--------------------

instance MonoFunctor (LogRenderer ω) where
  omap f (LogRenderer ls) = LogRenderer (f ⊳ ls)

----------------------------------------

class HasLogRenderer ω α where
  logRenderer ∷ Lens' α (LogRenderer ω)

--------------------

instance HasLogRenderer ω (LogRenderer ω) where
  logRenderer = id

------------------------------------------------------------

data LogRenderOpts ω =
  LogRenderOpts { {-| List of log annotators; applied in list order, tail of the
                      list first; hence, given that many renderers add something
                      to the LHS, the head of the list would be lefthand-most in
                      the resulting output.
                   -}
                  _lroRenderers    ∷ LogRenderer ω
                , _lroWidth        ∷ PageWidth
                }

--------------------

instance Default (LogRenderOpts ω) where
  def = LogRenderOpts (LogRenderer []) Unbounded

--------------------

instance HasLogRenderer ω (LogRenderOpts ω) where
  logRenderer ∷ Lens' (LogRenderOpts ω) (LogRenderer ω)
  logRenderer = lens _lroRenderers (\ opts rs → opts { _lroRenderers = rs })

------------------------------------------------------------

logRenderOpts' ∷ [LogR ω] → PageWidth → LogRenderOpts ω
logRenderOpts' as w = LogRenderOpts (LogRenderer as) w

{- | `LogRenderOpts` with no adornments.  Page width is `Unbounded`; you can
     override this with lens syntax, e.g.,

     > lroRenderPlain & lroWidth .~ AvailablePerLine 80 1.0
 -}
lroRenderPlain ∷ LogRenderOpts ω
lroRenderPlain = logRenderOpts' [] Unbounded

{- | `LogRenderOpts` with severity. -}
lroRenderSev ∷ LogRenderOpts ω
lroRenderSev = logRenderOpts' [ renderLogWithSeverity ] Unbounded

{- | `LogRenderOpts` with timestamp & severity. -}
lroRenderTSSev ∷ LogRenderOpts ω
lroRenderTSSev =
  logRenderOpts' [ renderLogWithTimestamp, renderLogWithSeverity ] Unbounded

{- | `LogRenderOpts` with severity & callstack. -}
lroRenderSevCS ∷ LogRenderOpts ω
lroRenderSevCS =
  logRenderOpts' [ renderLogWithCallStack, renderLogWithSeverity ] Unbounded

{- | `LogRenderOpts` with timestamp, severity & callstack. -}
lroRenderTSSevCS ∷ LogRenderOpts ω
lroRenderTSSevCS =
  logRenderOpts' [ renderLogWithCallStack,renderLogWithTimestamp
                 , renderLogWithSeverity ]
                Unbounded

{- | `LogRenderOpts` with severity & callstack head. -}
lroRenderSevCSH ∷ LogRenderOpts ω
lroRenderSevCSH =
  logRenderOpts' [ renderLogWithSeverity, renderLogWithStackHead ] Unbounded

{- | `LogRenderOpts` with timestamp, severity & callstack head.
 -}
lroRenderTSSevCSH ∷ LogRenderOpts ω
lroRenderTSSevCSH =
  logRenderOpts' [ renderLogWithTimestamp, renderLogWithSeverity
                 , renderLogWithStackHead ]
                Unbounded

{- | A single renderer for a LogEntry, using the renderers selected in
     LogRenderOpts. -}
lroRenderer ∷ LogRenderOpts ω → LogEntry ω → Doc AnsiStyle
lroRenderer opts =
  let foldf ∷ Foldable ψ ⇒ ψ (α → α) → α → α
      foldf = flip (foldr ($))
   in foldf (unLogRenderer (opts ⊣ logRenderer))
            (reAnnotate ф ∘ view logdoc)

lroWidth ∷ Lens' (LogRenderOpts ω) PageWidth
lroWidth = lens _lroWidth (\ opts w → opts { _lroWidth = w })

lroOpts ∷ Lens' (LogRenderOpts ω) LayoutOptions
lroOpts = lens (LayoutOptions ∘ _lroWidth)
               (\ opts lo → opts { _lroWidth = layoutPageWidth lo })

----------

renderLogWithSeverity ∷ LogR ω
renderLogWithSeverity = renderWithSeverityAnsi

----------

renderLogWithTimestamp ∷ LogR ω
renderLogWithTimestamp = renderWithTimestamp

----------

renderLogWithStackHead ∷ LogR ω
renderLogWithStackHead = renderWithStackHead

----------

renderLogWithCallStack ∷ LogR ω
renderLogWithCallStack = renderWithCallStack

----------

renderLogWithSeverityAndTimestamp ∷ LogR ω
renderLogWithSeverityAndTimestamp = renderWithSeverityAndTimestamp

--------------------

renderLogEntries ∷ (MonoFoldable χ, Element χ ~ LogEntry ω) ⇒
                       LogRenderOpts ω → χ → Doc AnsiStyle
renderLogEntries opts = (⊕ line) ∘ (vsep ∘ fmap (lroRenderer opts) ∘ otoList)

renderIO ∷ (MonadIO μ, MonoFoldable χ, Element χ ~ LogEntry ω) ⇒
           Handle → LogRenderOpts ω → χ → μ ()
renderIO h o =
  liftIO ∘ Terminal.renderIO h ∘ layoutPretty (o ⊣ lroOpts) ∘ renderLogEntries o

{-| Test ANSI rendering; designed to run just to stderr, rather than within
    a Tasty test harness -}
ansiTests ∷ IO ()
ansiTests = let mkle sev = logEntry @[(String,SrcLoc)] @()
                                    [] Nothing sev (pretty $ show sev) ()
                logs = mkle ⊳ [ Emergency, Alert, Critical, Error, Warning
                              , Notice, Informational, Debug ]
             in renderIO stdout lroRenderSev logs

-- that's all, folks! ----------------------------------------------------------
