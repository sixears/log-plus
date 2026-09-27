module LogPlus.T.LogRenderOpts
  ( tests )
where

import Base1T

-- base --------------------------------

import Data.Type.Equality  ( type(~) )
import GHC.Stack           ( SrcLoc )
import System.IO           ( Handle, stdout )

-- logging-effect ----------------------

import Control.Monad.Log  ( Severity( Alert, Debug, Critical, Emergency, Error
                                    , Informational, Notice, Warning ) )

-- mono-traversable --------------------

import Data.MonoTraversable  ( Element, MonoFoldable( otoList ) )

-- prettyprinter -----------------------

import Prettyprinter              ( Doc, PageWidth( Unbounded )
                                  , defaultLayoutOptions, layoutPretty, line
                                  , pretty, vsep
                                  )
import Prettyprinter.Render.Text  ( renderStrict )

-- prettyprinter-ansi-terminal ---------

import qualified  Prettyprinter.Render.Terminal  as  Terminal

import Prettyprinter.Render.Terminal  ( AnsiStyle )

-- tasty-plus --------------------------

import TastyPlus  ( (≟), assertListEq )

-- text --------------------------------

import qualified  Data.Text  as  T

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.LogEntry       ( LogEntry, logEntry )
import LogPlus.LogRenderOpts  ( LogRenderOpts, lroRenderer, logRenderOpts'
                              , lroOpts, lroRenderSev, renderLogWithCallStack
                              , renderLogWithSeverity
                              , renderLogWithSeverityAndTimestamp
                              , renderLogWithStackHead, renderLogWithTimestamp
                              )
import LogPlus.T.TestData     ( _le0 )

--------------------------------------------------------------------------------

lroRendererTests ∷ TestTree
lroRendererTests =
  let renderDoc ∷ Doc α → 𝕋
      renderDoc = renderStrict ∘ layoutPretty defaultLayoutOptions

      check nme exp rs = let opts     = logRenderOpts' rs Unbounded
                             rendered = lroRenderer opts _le0
                          in testCase nme $ exp ≟ renderDoc rendered
      checks nme exp rs = let opts     = logRenderOpts' rs Unbounded
                              rendered = lroRenderer opts _le0
                           in assertListEq nme exp (T.lines $ renderDoc rendered)
   in testGroup "lroRenderer"
                [ check "plain" "log_entry 1" []
                , check "sev" "[Info] log_entry 1" [renderLogWithSeverity]
                , check "ts" "[1970-01-01Z00:00:00 Thu] log_entry 1"
                             [renderLogWithTimestamp]
                , check "ts" "«c#1» log_entry 1" [renderLogWithStackHead]
                , checks "cs" [ "log_entry 1"
                              , "  stack0, called at c:1:2 in a:b"
                              , "    stack1, called at f:5:6 in d:e"
                              ]
                             [renderLogWithCallStack]
                , check "ts-sev"
                    "[1970-01-01Z00:00:00 Thu] [Info] log_entry 1"
                        [renderLogWithTimestamp,renderLogWithSeverity]
                , check "sev-ts"
                    "[Info] [1970-01-01Z00:00:00 Thu] log_entry 1"
                        [renderLogWithSeverity,renderLogWithTimestamp]
                , checks "ts-sev-cs"
                         [ "[1970-01-01Z00:00:00 Thu] [Info] log_entry 1"
                         ,   "                                 "
                           ⊕ "  stack0, called at c:1:2 in a:b"
                         ,   "                                 "
                           ⊕ "    stack1, called at f:5:6 in d:e"
                         ]
                         [ renderLogWithTimestamp, renderLogWithSeverity
                         , renderLogWithCallStack ]
                , checks "cs-ts-sev"
                         [ "[1970-01-01Z00:00:00 Thu] [Info] log_entry 1"
                         , "  stack0, called at c:1:2 in a:b"
                         , "    stack1, called at f:5:6 in d:e"
                         ]
                         [ renderLogWithCallStack
                         , renderLogWithTimestamp, renderLogWithSeverity ]
                , checks "sev-cs-ts"
                         [ "[Info] [1970-01-01Z00:00:00 Thu] log_entry 1"
                         , "         stack0, called at c:1:2 in a:b"
                         , "           stack1, called at f:5:6 in d:e"
                         ]
                         [ renderLogWithSeverity, renderLogWithCallStack
                         , renderLogWithTimestamp ]
                , checks "cs-sevts"
                         [ "[1970-01-01Z00:00:00 Thu|Info] log_entry 1"
                         , "  stack0, called at c:1:2 in a:b"
                         , "    stack1, called at f:5:6 in d:e"
                         ]
                         [ renderLogWithCallStack
                         , renderLogWithSeverityAndTimestamp ]
                , checks "sh-sevts"
                         [ "[1970-01-01Z00:00:00 Thu|Info] «c#1» log_entry 1"]
                         [ renderLogWithSeverityAndTimestamp
                         , renderLogWithStackHead ]
                ]


--------------------------------------------------------------------------------
--                                   tests                                    --
--------------------------------------------------------------------------------

tests ∷ TestTree
tests = testGroup "LogRenderOpts" [ lroRendererTests ]

----------------------------------------

_test ∷ IO ExitCode
_test = runTestTree tests

--------------------

_tests ∷ String → IO ExitCode
_tests = runTestsP tests

_testr ∷ String → ℕ → IO ExitCode
_testr = runTestsReplay tests

----------------------------------------

renderLogEntries ∷ (MonoFoldable χ, Element χ ~ LogEntry ω) ⇒
                       LogRenderOpts ω → χ → Doc AnsiStyle
renderLogEntries opts = (⊕ line) ∘ (vsep ∘ fmap (lroRenderer opts) ∘ otoList)

--------------------

renderIO ∷ (MonadIO μ, MonoFoldable χ, Element χ ~ LogEntry ω) ⇒
           Handle → LogRenderOpts ω → χ → μ ()
renderIO h o =
  liftIO ∘ Terminal.renderIO h ∘ layoutPretty (o ⊣ lroOpts) ∘ renderLogEntries o

--------------------

{-| Test ANSI rendering; designed to run just to stderr, rather than within
    a Tasty test harness -}
ansiTests ∷ IO ()
ansiTests = let mkle sev = logEntry @[(String,SrcLoc)] @()
                                    [] Nothing sev (pretty $ show sev) ()
                logs = mkle ⊳ [ Emergency, Alert, Critical, Error, Warning
                              , Notice, Informational, Debug ]
             in renderIO stdout lroRenderSev logs

--------------------

{- | Manual tests, designed to be run at the ghci prompt. -}
_testm ∷ IO()
_testm = do
  ansiTests

-- that's all, folks! ----------------------------------------------------------
