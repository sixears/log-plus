module LogPlus.LogRenderOpts
  ( LogR, LogRenderOpts

  , logRenderOpts'

  , lroOpts, lroRenderPlain, lroRenderSev, lroRenderSevCS, lroRenderSevCSH
  , lroRenderTSSev, lroRenderTSSevCS, lroRenderTSSevCSH
  , lroRenderer, lroWidth

  , renderLogWithCallStack
  , renderLogWithSeverity
  , renderLogWithSeverityAndTimestamp
  , renderLogWithStackHead
  , renderLogWithTimestamp

  , renderWithCallStack, renderWithSeverity, renderWithStackHead
  , renderWithTimestamp
  )
where

import Base1T

-- lens --------------------------------

import Control.Lens  ( view )

-- mono-traversable --------------------

import Data.MonoTraversable  ( Element, MonoFunctor( omap ) )

-- prettyprinter -----------------------

import Prettyprinter              ( Doc, LayoutOptions( LayoutOptions )
                                  , PageWidth( Unbounded )
                                  , layoutPageWidth, reAnnotate
                                  )

-- prettyprinter-ansi-terminal ---------

import Prettyprinter.Render.Terminal  ( AnsiStyle )

------------------------------------------------------------
--                     Local Imports                      --
------------------------------------------------------------

import LogPlus.LogEntry    ( LogEntry , logdoc )
import LogPlus.Render      ( renderWithCallStack, renderWithSeverity
                           , renderWithSeverityAndTimestamp
                           , renderWithSeverityAnsi, renderWithStackHead
                           , renderWithTimestamp
                           )

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

-- that's all, folks! ----------------------------------------------------------
