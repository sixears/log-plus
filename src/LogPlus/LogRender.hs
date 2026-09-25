module LogPlus.LogRender
  ( logRender, logRender', renderMapLog, renderMapLog' )
where

import Base1T  hiding  ( toList )

-- base --------------------------------

import Data.Foldable  ( concatMap )
import GHC.Exts       ( toList )

-- logging-effect ----------------------

import Control.Monad.Log  ( MonadLog, PureLoggingT, runPureLoggingT )

-- prettyprinter -----------------------

import qualified  Prettyprinter.Render.Text  as  RenderText

import Prettyprinter  ( Doc, SimpleDocStream, layoutPretty, vsep )

-- single ------------------------------

import Single( MonoSingle( osingle ) )

-- tasty-plus --------------------------

import TastyPlus  ( assertListEq, assertListEqIO)

-- text --------------------------------

import Data.Text  qualified as  T

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

{-

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

-}

-- that's all, folks! ----------------------------------------------------------
