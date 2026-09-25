module LogPlus.LogRender
  ( logRender, logRender', renderMapLog, renderMapLog' )
where

import Base1T  hiding  ( toList )

-- base --------------------------------

import Data.Foldable  ( concatMap )
import GHC.Exts       ( toList )

-- logging-effect ----------------------

import Control.Monad.Log  ( PureLoggingT, runPureLoggingT )

-- prettyprinter -----------------------

import qualified  Prettyprinter.Render.Text  as  RenderText

import Prettyprinter  ( Doc, SimpleDocStream, layoutPretty, vsep )

-- single ------------------------------

import Single( MonoSingle( osingle ) )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import Log.LogEntry            ( LogEntry )
import Log.LogRenderOpts       ( LogRenderOpts, lroOpts, lroRenderer )
import LogPlus.Log             ( Log )
import LogPlus.LogTransformer  ( LogTransformer )

--------------------------------------------------------------------------------

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

----------------------------------------

{-| render a log to a list of Docs, per `LogRenderOpts` and applying `LogEntry`
    transformers along the way -}
renderMapLog ∷ ∀ ω ρ ψ . Foldable ψ =>
               (LogEntry ω → Doc ρ) → ψ (LogTransformer ω) → Log ω
             → [Doc ρ]
renderMapLog renderer trx ls =
  let trx' ∷ LogTransformer ω
      trx' = foldr (\ a b → concatMap a ∘ b) (:[]) trx
   in renderer ⊳ (toList ls ≫ trx')

----------

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

----------------------------------------


{-| `logRender` with `()` is sufficiently common to warrant a cheap alias -}
logRender' ∷ ∀ ω η . Monad η =>
             LogRenderOpts ω → [LogTransformer ω] → PureLoggingT (Log ω) η ()
           → η [𝕋]
logRender' opts trx lg = snd ⊳ (logRender opts trx lg)

-- that's all, folks! ----------------------------------------------------------
