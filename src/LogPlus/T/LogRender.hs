module LogPlus.T.LogRender
  ( tests )
where

import Base1T

-- base --------------------------------

import Control.Monad.Identity  ( runIdentity )
import Data.Monoid             ( mconcat )

-- logging-effect ----------------------

import Control.Monad.Log  ( MonadLog, PureLoggingT, Severity( Informational ) )

-- prettyprinter -----------------------

import qualified  Prettyprinter.Render.Text  as  RenderText

import Prettyprinter  ( Doc, LayoutOptions( LayoutOptions ), PageWidth(Unbounded)
                      , SimpleDocStream, layoutPretty, pretty )

-- safe --------------------------------

import Safe  ( headDef )

-- tasty-plus --------------------------

import TastyPlus  ( assertListCmp, assertListEq, assertListEqIO )

-- text --------------------------------

import Data.Text  qualified as  T

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import Log                ( Log, WithLog, log )
import Log.LogEntry       ( LogEntry, logdoc )
import Log.LogRenderOpts  ( logRenderOpts', lroRenderSevCS, lroRenderTSSevCSH
                          , renderWithCallStack, renderWithSeverity )

import LogPlus.LogRender   ( logRender' )
import LogPlus.T.TestData  ( _log0m, _log1m )

--------------------------------------------------------------------------------

{- | Log some text (at Informational severity); should produce at least 3 stack
     frames -}
_sf_plus_3 ∷ WithLog () η ⇒ 𝕋 → η ()
_sf_plus_3 t = let -- add an additional callstack to test the formatting
                   _sf_plus_2 ∷ WithLog () η ⇒ η ()
                   _sf_plus_2 = log Informational () t
                in _sf_plus_2

_3sf ∷ MonadLog (Log ()) η ⇒ 𝕄 𝕋 → η ()
_3sf Nothing  = _sf_plus_3 "3 stack frames"
_3sf (Just t) = _sf_plus_3 t

_3sf' ∷ WithLog () η ⇒ η ()
_3sf' = _3sf (Just "3 frames of stack")

_4sf ∷ WithLog () η ⇒ 𝕄 𝕋 → η ()
_4sf Nothing  = _sf_plus_3 "4 stack frames"
_4sf (Just t) = _sf_plus_3 t

-- don't inline this, as then it would disappear from the callstack and screw up
-- our testing
{-# NOINLINE _4sf' #-}
_4sf' ∷ MonadLog (Log ()) η ⇒ η ()
_4sf' = _4sf (Just "4 stack frames")

-- don't inline this, as then it would disappear from the callstack and screw up
-- our testing
{-# NOINLINE _5sf #-}
_5sf ∷ WithLog () η ⇒ η ()
_5sf = _4sf (Just "5+ stack frames")

----------------------------------------

logRenderTests ∷ TestTree
logRenderTests =
  let indent n t         = T.replicate n " " ⊕ t
      indents' _ []      = []
      indents' n (t:ts)  = t:(indent n ⊳ ts)
      exp3sf'            =
        indents' 9 [ "[Info] 3 frames of stack"
                   , "log, called at src/LogPlus/T/LogRender.hs:"
                   , "  _sf_plus_2, called at src/LogPlus/T/LogRender.hs:"
                   , "  _sf_plus_3, called at src/LogPlus/T/LogRender.hs:"
                   ]
      exp4sf'            =
        indents' 9 [ "[Info] 4 stack frames"
                   , "log, called at src/LogPlus/T/LogRender.hs:"
                   , "  _sf_plus_2, called at src/LogPlus/T/LogRender.hs:"
                   , "  _sf_plus_3, called at src/LogPlus/T/LogRender.hs:"
                   , "  _4sf, called at src/LogPlus/T/LogRender.hs:"
                   ]
      exp5sf             =
        indents' 9 [ "[Info] 5+ stack frames"
                   , "log, called at src/LogPlus/T/LogRender.hs:"
                   , "  _sf_plus_2, called at src/LogPlus/T/LogRender.hs:"
                   , "  _sf_plus_3, called at src/LogPlus/T/LogRender.hs:"
                   , "  _4sf, called at src/LogPlus/T/LogRender.hs:"
                   , "  _5sf, called at src/LogPlus/T/LogRender.hs:"
                   ]
      renderers          = [ renderWithSeverity, renderWithCallStack ]
      lrOpts             = logRenderOpts' renderers Unbounded
      render             ∷ Monad η ⇒ PureLoggingT (Log ()) η () → η [𝕋]
      render             = logRender' lrOpts []
      renderL            ∷ PureLoggingT (Log ()) Identity () → [𝕋]
      renderL            = mconcat ∘ fmap T.lines ∘ runIdentity ∘ render
      assertListPrefices ∷ 𝕋 → [𝕋] → [𝕋] → TestTree
      assertListPrefices = assertListCmp toText toText T.isPrefixOf
      check ∷ 𝕋 → [𝕋] → PureLoggingT (Log ()) Identity () → TestTree
      check name exp got = assertListPrefices name exp (renderL got)

   in testGroup "logRender"
                [ check "_3sf'" exp3sf' _3sf'
                , check "_4sf'" exp4sf' _4sf'
                , check "_5sf" exp5sf _5sf
                ]

----------------------------------------

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

-- tests -----------------------------------------------------------------------

tests ∷ TestTree
-- XXX tests = dependentTestGroup "LogRender" AllSucceed [ logRenderTests, logRender'Tests ]
tests = testGroup "LogRender" [ logRenderTests, logRender'Tests ]

----------------------------------------

_test ∷ IO ExitCode
_test = runTestTree tests

--------------------

_tests ∷ String → IO ExitCode
_tests = runTestsP tests

_testr ∷ String → ℕ → IO ExitCode
_testr = runTestsReplay tests

-- that's all, folks! ----------------------------------------------------------
