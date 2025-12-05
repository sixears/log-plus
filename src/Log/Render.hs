module Log.Render
  ( renderWithCallStack, renderWithSeverity, renderWithSeverityAndTimestamp
  , renderWithSeverityAnsi, renderWithStackHead, renderWithTimestamp )
where

-- base --------------------------------

import Data.Function  ( ($) )
import Data.Functor   ( fmap )
import Data.Maybe     ( Maybe( Just, Nothing ) )
import Data.String    ( String )
import Data.Tuple     ( snd )
import GHC.Stack      ( SrcLoc
                      , getCallStack, prettySrcLoc, srcLocFile,srcLocStartLine )

-- base-unicode-symbols ----------------

import Data.Function.Unicode  ( (∘) )
import Data.Monoid.Unicode    ( (⊕) )

-- has-callstack -----------------------

import HasCallstack  ( HasCallstack( callstack, stackhead ) )

-- logging-effect ----------------------

import Control.Monad.Log  ( Severity( Alert, Critical, Debug, Emergency, Error
                                    , Informational, Notice , Warning ) )

-- more-unicode ------------------------

import Data.MoreUnicode.Doc      ( (⊞) )
import Data.MoreUnicode.Functor  ( (⊳) )
import Data.MoreUnicode.Lens     ( (⊣) )
import Data.MoreUnicode.Maybe    ( pattern 𝓝 )
import Data.MoreUnicode.Monoid   ( ю )

-- prettyprinter -----------------------

import Prettyprinter          ( Doc, align, annotate, brackets, emptyDoc, indent
                              , line, pretty, vsep )
import Prettyprinter.Render.Terminal
                              ( AnsiStyle, Color( Black, Green, Red, Yellow
                                                , White )
                              , bgColorDull, bgColor, bold, color,underlined
                              )

-- text --------------------------------

import qualified  Data.Text.Lazy  as  LT

import Data.Text  ( Text )

-- tfmt --------------------------------

import Text.Fmt  ( formatUTCYDoW, fmt )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import Log.HasSeverity   ( HasSeverity( severity ) )
import Log.HasUTCTime    ( HasUTCTimeY( utcTimeY ), )

--------------------------------------------------------------------------------

renderSeverity ∷ HasSeverity τ ⇒ τ → Doc ρ
renderSeverity sv =
  pretty $ case sv ⊣ severity of
             Emergency     → ("EMRG" ∷ Text)
             Alert         → "ALRT"
             Critical      → "CRIT"
             Error         → "Erro"
             Warning       → "Warn"
             Notice        → "Note"
             Informational → "Info"
             Debug         → "Debg"

--------------------

renderSeverityAnsi ∷ HasSeverity τ ⇒ τ → Doc AnsiStyle
renderSeverityAnsi m =
  let red    = color Red
      yellow = color Yellow
      green  = color Green
      white  = color White
      black  = color Black
      b = bold
      u = underlined
      bgBlack = bgColorDull Black
      bgRed   = bgColor     Red
      anno ls = annotate (ю (bgBlack : ls))
      annoR ls = annotate (ю (bgRed : ls))
   in case m ⊣ severity of
        Emergency     → annoR [b,u,black] "EMRG"
        Alert         → anno  [b,u,red] "ALRT"
        Critical      → anno  [red] "CRIT"
        Error         → anno  [red] "Erro"
        Warning       → anno  [yellow] "Warn"
        Notice        → anno  [u,green] "Note"
        Informational → anno  [green] "Info"
        Debug         → anno  [white] "Debg"

--------------------

renderWithSeverityAnsi ∷ HasSeverity τ ⇒ (τ → Doc AnsiStyle) → τ → Doc AnsiStyle
renderWithSeverityAnsi f m = brackets (renderSeverityAnsi m) ⊞ align (f m)

----------

renderWithSeverity ∷ HasSeverity τ ⇒ (τ → Doc ρ) → τ → Doc ρ
renderWithSeverity f m = brackets (renderSeverity m) ⊞ align (f m)

----------------------------------------

renderTimestamp  ∷ HasUTCTimeY τ ⇒ τ → Doc ρ
renderTimestamp m = pretty (formatUTCYDoW 𝓝 $ m ⊣ utcTimeY)

----------

renderWithTimestamp ∷ HasUTCTimeY τ ⇒ (τ → Doc ρ) → τ → Doc ρ
renderWithTimestamp f m = brackets (renderTimestamp m) ⊞ align (f m)

----------------------------------------

locToText ∷ SrcLoc → Text
locToText loc = [fmt|«%s#%w»|] (srcLocFile loc) (srcLocStartLine loc)

----------

renderLocation ∷ Maybe SrcLoc → Doc α
renderLocation (Just loc) = pretty $ locToText loc
renderLocation Nothing    = emptyDoc

--------------------

renderWithStackHead ∷ HasCallstack δ ⇒ (δ -> Doc ρ) -> δ -> Doc ρ
renderWithStackHead f m =
  let renderStackHead = renderLocation ∘ fmap snd
   in renderStackHead (stackhead m) ⊞ align (f m)

----------------------------------------

prettyCallSite ∷ (String,SrcLoc) → Doc ρ
prettyCallSite (f,loc) =
          pretty (LT.pack f) ⊕ ", called at " ⊕
          pretty (LT.pack (GHC.Stack.prettySrcLoc loc))

renderCallStack ∷ [(String,SrcLoc)] → Doc ann
renderCallStack [] = "empty callstack"
renderCallStack (root:[]) =
  prettyCallSite root
renderCallStack (root:rest) =
  prettyCallSite root ⊕ line ⊕ indent 2 (vsep (prettyCallSite ⊳ rest))

----------

renderWithCallStack ∷ HasCallstack δ ⇒ (δ -> Doc ρ) -> δ -> Doc ρ
renderWithCallStack f m =
  f m ⊕ line ⊕ indent 2 (renderCallStack (getCallStack $ m ⊣ callstack))

----------------------------------------

renderWithSeverityAndTimestamp ∷ (HasSeverity τ, HasUTCTimeY τ) ⇒
                                 (τ → Doc ρ) → τ → Doc ρ
renderWithSeverityAndTimestamp f m =
  brackets (renderTimestamp m ⊕ "|" ⊕ renderSeverity m) ⊞ align (f m)

-- that's all, folks! ----------------------------------------------------------
