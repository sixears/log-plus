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

import System.IO  ( stderr )

-- tasty -------------------------------

import Test.Tasty  ( DependencyType( AllSucceed ), dependentTestGroup )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import qualified  Log.LogRenderOpts

import qualified  LogPlus.EMonad

import qualified  LogPlus.T.FileSizeRotator
import qualified  LogPlus.T.FileTimeRotator
import qualified  LogPlus.T.LogRender

import Log  ( logToStderr, logToTTY, logToTTYPlain )

import LogPlus.CallStackOption  ( CallStackOption( CallStackHead, NoCallStack ) )

import LogPlus.T.TestData  ( _log0io )

--------------------------------------------------------------------------------
--                                   tests                                    --
--------------------------------------------------------------------------------

tests ∷ TestTree
tests = dependentTestGroup "Log" AllSucceed
                           [ LogPlus.EMonad.tests
                           , Log.LogRenderOpts.tests -- XXX, logRenderTests
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
