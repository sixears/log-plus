{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax       #-}

module T.Log
  ( tests )
where

import Base1T

-- base --------------------------------

import Control.Monad.Identity  ( runIdentity )
import Data.Monoid             ( mconcat )
import System.IO               ( stderr )

-- logging-effect ----------------------

import Control.Monad.Log  ( MonadLog, PureLoggingT, Severity( Informational ) )

-- prettyprinter -----------------------

import Prettyprinter  ( PageWidth( Unbounded ) )

-- tasty -------------------------------

import Test.Tasty  ( DependencyType( AllSucceed ), dependentTestGroup )

-- tasty-plus --------------------------

import TastyPlus   ( assertListCmp )

-- text --------------------------------

import Data.Text  ( isPrefixOf, lines, replicate )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import qualified  Log.LogRenderOpts

import qualified  LogPlus.EMonad

import qualified  LogPlus.T.FileSizeRotator
import qualified  LogPlus.T.FileTimeRotator
import qualified  LogPlus.T.LogRender

import Log                      ( Log, WithLog, log, logRender', logToStderr
                                , logToTTY, logToTTYPlain )
import LogPlus.CallStackOption  ( CallStackOption( CallStackHead, NoCallStack ) )
import Log.LogRenderOpts        ( logRenderOpts', renderWithSeverity
                                , renderWithCallStack )

import LogPlus.T.TestData  ( _log0io )

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

--------------------------------------------------------------------------------
--                                   tests                                    --
--------------------------------------------------------------------------------

logRenderTests ∷ TestTree
logRenderTests =
  let indent n t         = replicate n " " ⊕ t
      indents' _ []      = []
      indents' n (t:ts)  = t:(indent n ⊳ ts)
      exp3sf'            = indents' 9 [ "[Info] 3 frames of stack"
                                      , "log, called at src/T/Log.hs:"
                                      , "  _sf_plus_2, called at src/T/Log.hs:"
                                      , "  _sf_plus_3, called at src/T/Log.hs:"
                                      ]
      exp4sf'            = indents' 9 [ "[Info] 4 stack frames"
                                      , "log, called at src/T/Log.hs:"
                                      , "  _sf_plus_2, called at src/T/Log.hs:"
                                      , "  _sf_plus_3, called at src/T/Log.hs:"
                                      , "  _4sf, called at src/T/Log.hs:"
                                      ]
      exp5sf             = indents' 9 [ "[Info] 5+ stack frames"
                                      , "log, called at src/T/Log.hs:"
                                      , "  _sf_plus_2, called at src/T/Log.hs:"
                                      , "  _sf_plus_3, called at src/T/Log.hs:"
                                      , "  _4sf, called at src/T/Log.hs:"
                                      , "  _5sf, called at src/T/Log.hs:"
                                      ]
      renderers          = [ renderWithSeverity, renderWithCallStack ]
      lrOpts             = logRenderOpts' renderers Unbounded
      render             ∷ Monad η ⇒ PureLoggingT (Log ()) η () → η [𝕋]
      render             = logRender' lrOpts []
      renderL            ∷ PureLoggingT (Log ()) Identity () → [𝕋]
      renderL            = mconcat ∘ fmap lines ∘ runIdentity ∘ render
      assertListPrefices ∷ 𝕋 → [𝕋] → [𝕋] → TestTree
      assertListPrefices = assertListCmp toText toText isPrefixOf
      check ∷ 𝕋 → [𝕋] → PureLoggingT (Log ()) Identity () → TestTree
      check name exp got = assertListPrefices name exp (renderL got)

   in testGroup "logRender"
                [ check "_3sf'" exp3sf' _3sf'
                , check "_4sf'" exp4sf' _4sf'
                , check "_5sf" exp5sf _5sf
                ]

----------------------------------------

tests ∷ TestTree
tests = dependentTestGroup "Log" AllSucceed
                           [ LogPlus.EMonad.tests
                           , Log.LogRenderOpts.tests, logRenderTests
                           , LogPlus.T.LogRender.tests
                           , LogPlus.T.FileSizeRotator.tests
                           , LogPlus.T.FileTimeRotator.tests ]

----------------------------------------

_test ∷ IO ExitCode
_test = runTestTree tests

--------------------

_tests ∷ String → IO ExitCode
_tests = runTestsP tests

_testr ∷ String → ℕ → IO ExitCode
_testr = runTestsReplay tests

----------------------------------------

{-| manual tests - run these by hand, there is no automated testing option for
    these -}
_testm ∷ IO ()
_testm = do
  logToStderr   NoCallStack   []        _log0io
  logToTTYPlain               [] stderr _log0io
  logToTTY      NoCallStack   [] stderr _log0io
  logToTTY      CallStackHead [] stderr _log0io
  logToTTY      CallStackHead [] stderr _log0io

-- that's all, folks! ----------------------------------------------------------
