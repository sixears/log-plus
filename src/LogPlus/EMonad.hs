{-| variant of `BasePlus.EMonad` that reports errors to the log, rather than
    directly to stderr -}
module LogPlus.EMonad
  ( ꙗ, ꙝ, ꙝ', ꙝE, ꙝE', eMonad, runEMonad, runEMonad', runEMonadErr, runEMonadIO
  , runEMonadIO', runEMonadIOErr, tests )
where

import Base1T  hiding  ( toList )

-- base --------------------------------

import GHC.Exts  ( IsList( toList ) )

-- base-plus ---------------------------

import qualified  BasePlus.EMonad  as  BaseEMonad

import BasePlus.EMonad  ( EMonad, eMonad, ꙗ )

-- fpath -------------------------------

import FPath.AbsFile  ( AbsFile, absfile )
import FPath.File     ( File( FileA ), FileAs )

-- lens --------------------------------

import Control.Lens.Getter  ( view )

-- logging-effect ----------------------

import Control.Monad.Log  ( PureLoggingT, Severity( Error ), runPureLoggingT )

-- monaderror-io -----------------------

import MonadError.IO.Error  ( IOError )

-- monadio-plus ------------------------

import MonadIO.NamedHandle  ( HEncoding( NoEncoding ), ℍ, hClose, hname )
import MonadIO.OpenFile     ( FileOpenMode( FileR ), openFile )

-- natural -----------------------------

import Natural  ( ỻ )

-- tasty-hunit -------------------------

import Test.Tasty.HUnit  ( Assertion, assertEqual )

-- tasty-plus --------------------------

import TastyPlus  ( assertEq, assertIsJust, assertIsNothing, assertJust )

------------------------------------------------------------
--                     local imports                       -
------------------------------------------------------------

import LogPlus              ( log, logIO )
import LogPlus.HasSeverity  ( severity )
import LogPlus.Log          ( Log, WithLog, WithLogIO )
import LogPlus.LogEntry     ( LogEntry, simpleDoc )

--------------------------------------------------------------------------------

{-| Run  a sequence of potentially errorful computations: any error causes
    termination, with the error written to the log at the given level.  Note that
    the naming - with this version postfixed with an apostrophe - is basic
    huffman coding: the use of the additional attributes in the log (`p`) is
    rare. -}
runEMonad' ∷ ∀ ε ω α μ . (WithLog ω μ, Printable ε) =>
            Severity → ω → EMonad ε μ α → μ (𝕄 α)
runEMonad' sv p =
  let runEMonadX = BaseEMonad.runEMonadX
  in  runEMonadX (either (\ e → log sv p (toText e) ⪼ return 𝓝) (return ∘ 𝓙))

{-| Run a sequence of potentially errorful computations: any error causes
    termination, with the error written to the log at the given level. The
    additional attributes added to the log (`p` in `runEMonad'`) are implicitly
    supplied as `def`. -}
runEMonad ∷ ∀ ε ω α μ . (WithLog ω μ, Default ω, Printable ε) =>
            Severity → EMonad ε μ α → μ (𝕄 α)
runEMonad sv = runEMonad' sv def

{-| `runEMonad`, but with the severity implicitly specified as `Error` -}
runEMonadErr ∷ ∀ ε ω α μ . (WithLog ω μ, Default ω, Printable ε) =>
               EMonad ε μ α → μ (𝕄 α)
runEMonadErr = runEMonad Error

{-| `runEMonad'`, but with a timestamp added, thus causing IO -}
runEMonadIO' ∷ ∀ ε ω α μ . (WithLogIO ω μ, Printable ε) =>
               Severity → ω → EMonad ε μ α → μ (𝕄 α)
runEMonadIO' sv p =
  let runEMonadX = BaseEMonad.runEMonadX
  in  runEMonadX (either(\ e → logIO sv p (toText e) ⪼ return 𝓝)(return ∘ 𝓙))

{-| `runEMonad`, but with a timestamp added, thus causing IO -}
runEMonadIO ∷ ∀ ε ω α μ . (WithLogIO ω μ, Default ω, Printable ε) =>
              Severity → EMonad ε μ α → μ (𝕄 α)
runEMonadIO sv = runEMonadIO' sv def

{-| `runEMonadIO`, but with the severity implicitly specified as `Error` -}
runEMonadIOErr ∷ ∀ ε ω α μ . (WithLogIO ω μ, Default ω, Printable ε) =>
                 EMonad ε μ α → μ (𝕄 α)
runEMonadIOErr = runEMonadIO Error

{-| shortcut for making and running an `EMonad`, with a unicode alias -}
ꙝ ∷ (WithLog ω μ, Default ω, Printable ε, MonadIO μ) =>
    Severity → ExceptT ε μ α → μ (𝕄 α)
ꙝ sv = runEMonad sv ∘ eMonad

{-| like `ꙝ`, discarding the result -}
ꙝ' ∷ (WithLog ω μ, Default ω, Printable ε, MonadIO μ) =>
     Severity → ExceptT ε μ α → μ ()
ꙝ' sv = const () ⩺ ꙝ sv

{-| like `ꙝ`, using the `Error` severity -}
ꙝE ∷ (WithLog ω μ, Default ω, Printable ε, MonadIO μ) =>
     ExceptT ε μ α → μ (𝕄 α)
ꙝE = runEMonad Error ∘ eMonad

{-| like `ꙝE`, discarding the result -}
ꙝE' ∷ (WithLog ω μ, Default ω, Printable ε, MonadIO μ) =>
      ExceptT ε μ α → μ ()
ꙝE' = const () ⩺ ꙝ Error

----------------------------------------

eMonadTests ∷ TestTree
eMonadTests =
  let openr ∷ (MonadIO μ, FileAs γ, MonadError IOError μ) => γ → μ ℍ
      openr x = openFile NoEncoding FileR x ≫ \ h → hClose h ⪼ return h


      complexTest ∷ ∀ τ ε . (Printable τ, Printable ε) =>
                    τ → ExceptT ε (PureLoggingT (Log ()) IO) ℍ
                  → (𝕄 ℍ → [LogEntry ()] → Assertion) → TestTree
      complexTest nm go ck = testCase (toString nm) $ do
        let ck' (h,toList → lg) = ck h lg
        runPureLoggingT (runEMonad Error ∘ BaseEMonad.eMonad $ go) ≫ ck'

      simpleTest ∷ AbsFile → (𝕄 ℍ → [LogEntry ()] → Assertion) → TestTree
      simpleTest fn = complexTest fn (openr fn)

      passwd  = [absfile|/etc/passwd|]
      nonsuch = [absfile|/etc/nonesuch|]
      group   = [absfile|/etc/group|]

  in  testGroup "EMonad" $
        [ simpleTest passwd $ \ h ls → do
            assertEqual  "no logs"         [] ls
            assertIsJust h
            assertJust  (assertEq (FileA passwd) ∘ view hname) h

        --------------------------------

        , simpleTest nonsuch $ \ h ls → do
            assertEqual "one log" (ỻ ls) 1
            assertIsNothing h
            let logEntry = ls !! 0
            let expect =
                  ю [ toText nonsuch
                    , ": openFdAt: does not exist (No such file or directory)" ]
            assertJust (\ le → assertEq (show $ le ⊣ severity) "Error") logEntry
            assertJust (\ le → assertEq (simpleDoc le) expect) logEntry

        --------------------------------

        , complexTest ("open not ok→ok"∷𝕋)
                      (openr nonsuch ⪼ openr passwd) $ \ h ls → do
            assertEqual "one log" (ỻ ls) 1
            assertIsNothing h
            let logEntry = ls !! 0
            let expect =
                  ю [ toText nonsuch
                    , ": openFdAt: does not exist (No such file or directory)" ]
            assertJust (\ le → assertEq (show $ le ⊣ severity) "Error") logEntry
            assertJust (\ le → assertEq (simpleDoc le) expect) logEntry

        --------------------------------

        , complexTest ("open not ok × 2"∷𝕋)
                      (openr nonsuch ⪼ openr nonsuch) $ \ h ls → do
            assertEqual "one log" (ỻ ls) 1
            assertIsNothing h
            let logEntry = ls !! 0
            let expect =
                  ю [ toText nonsuch
                    , ": openFdAt: does not exist (No such file or directory)" ]
            assertJust (\ le → assertEq (show $ le ⊣ severity) "Error") logEntry
            assertJust (\ le → assertEq (simpleDoc le) expect) logEntry

        --------------------------------

        , complexTest ("open ok→not ok"∷𝕋)
                      (openr passwd ⪼ openr nonsuch) $ \ h ls → do
            assertEqual "one log" (ỻ ls) 1
            assertIsNothing h
            let logEntry = ls !! 0
            let expect =
                  ю [ toText nonsuch
                    , ": openFdAt: does not exist (No such file or directory)" ]
            assertJust (\ le → assertEq (show $ le ⊣ severity) "Error") logEntry
            assertJust (\ le → assertEq (simpleDoc le) expect) logEntry

        --------------------------------

        , complexTest ("open ok→ok"∷𝕋)
                      (openr passwd ⪼ openr group) $ \ h ls → do
            assertEqual  "no logs"         [] ls
            assertIsJust h
            assertJust  (assertEq (FileA group) ∘ view hname) h
      ]

-- tests -----------------------------------------------------------------------

tests ∷ TestTree
tests = testGroup "LogPlus.EMonad" [ eMonadTests ]

----------------------------------------

_test ∷ IO ExitCode
_test = runTestTree tests

--------------------

_tests ∷ String → IO ExitCode
_tests = runTestsP tests

_testr ∷ String → ℕ → IO ExitCode
_testr = runTestsReplay tests

-- that's all, folks! ----------------------------------------------------------
