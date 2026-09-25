module LogPlus.T.LogRender
  ( tests )
where

import Base1T

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

--------------------------------------------------------------------------------

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
tests = testGroup "Log" [ {- XXX logRender'Tests -} ]

----------------------------------------

_test ∷ IO ExitCode
_test = runTestTree tests

--------------------

_tests ∷ String → IO ExitCode
_tests = runTestsP tests

_testr ∷ String → ℕ → IO ExitCode
_testr = runTestsReplay tests

-- that's all, folks! ----------------------------------------------------------
