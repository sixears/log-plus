{- XXX move this somewhere -}

module LogPlus.EMonad
  ( ꙗ, ꙝ, ꙝ', tests )
where

import Base1T

-- base --------------------------------

import System.IO.Error  ( isDoesNotExistError )

-- fpath -------------------------------

import FPath.AbsFile  ( absfile )

-- monaderror-io -----------------------

import MonadError.IO.Error  ( IOError, _IOErr )

-- monadio-plus ------------------------

import MonadIO.NamedHandle  ( HEncoding( NoEncoding ), hClose )
import MonadIO.OpenFile     ( FileOpenMode( FileR ), openFile )

-- tasty-hunit -------------------------

import Test.Tasty.HUnit  ( Assertion, assertBool )

-- tasty-plus --------------------------

import TastyPlus  ( assertIsJust, assertLeft )

------------------------------------------------------------
--                     local imports                       -
------------------------------------------------------------

import LogPlus.StdErr  ( eToStderr )

--------------------------------------------------------------------------------

-- XXX move & document this

-- odd ordering of variables make definition of Functor, Applicative, Monad
-- instances easier (or maybe possible)
{-| an either/error monad, designed to exit with the first error -}
data EMonad ε μ α = MonadIO μ => EMonad { runEMonadE ∷ μ (𝔼 ε α) }

--------------------

instance Functor (EMonad ε μ) where
  fmap f (EMonad m) = EMonad $ fmap (fmap f) m

--------------------

instance MonadIO μ => Applicative (EMonad ε μ) where
  pure x = EMonad $ return (𝓡 x)
  (EMonad f) <*> (EMonad x) = EMonad $ do
    f' ← f
    x' ← x
    return $ f' <*> x'

--------------------

instance MonadIO μ => Monad (EMonad ε μ) where
  (EMonad io) >>= f = EMonad $ do
    result ← io
    case result of
      𝓛 e → return (𝓛 e)      -- halt further computation
      𝓡 b → runEMonadE (f b)

--------------------

{-| construct an `EMonad` from an `ExceptT`; e.g., a `monadError` -}
eMonad ∷ ∀ ε α μ . MonadIO μ => ExceptT ε μ α → EMonad ε μ α
eMonad = EMonad ∘ ѥ

{-| unicode alias for `eMonad` (`EMonad` construction) -}
ꙗ ∷ ∀ ε α μ . MonadIO μ => ExceptT ε μ α → EMonad ε μ α
ꙗ = eMonad

--------------------

{-| run a sequence of potentially errorful computations; writing any failures to
    stderr, maybe returning a result -}
runEMonad ∷ ∀ ε α μ . (MonadIO μ, Printable ε) => EMonad ε μ α → μ (𝕄 α)
runEMonad m = runEMonadE m ≫ eToStderr

{-| shortcut for making and running an `EMonad`, with a unicode alias -}
ꙝ ∷ ∀ ε α μ . (MonadIO μ, Printable ε) => ExceptT ε μ α → μ (𝕄 α)
ꙝ = runEMonad ∘ eMonad

{-| like `ꙝ`, discarding the result -}
ꙝ' ∷ ∀ ε α μ . (MonadIO μ, Printable ε) => ExceptT ε μ α → μ ()
ꙝ' = const () ⩺ ꙝ

----------------------------------------

eMonadTests ∷ TestTree
eMonadTests =
  let openr x = do
        openFile @IOError NoEncoding FileR x ≫ \ h → hClose h ⪼ return h
      passwd  = [absfile|/etc/passwd|]
      group   = [absfile|/etc/group|]
      nonsuch = [absfile|/etc/nonesuch|]
      run     ∷ (MonadIO μ, Show α, Printable ε) => ExceptT ε μ α → μ (𝕄 α)
      run     = runEMonad ∘ EMonad ∘ ѥ
      runE    ∷ (MonadIO μ, Show α, Printable ε) => ExceptT ε μ α → μ (𝔼 ε α)
      runE    = runEMonadE ∘ EMonad ∘ ѥ
      assertDoesNotExist ∷ (Show α, AsIOError ε) => 𝔼 ε α → Assertion
      assertDoesNotExist = assertLeft (  assertBool "isDoesNotExistError"
                                       ∘ (≡ 𝓙 𝓣)
                                       ∘ (isDoesNotExistError ⩺ (⩼ _IOErr)))
      testIsJust ∷ (Show α, Printable ε) =>
                   TestName → ExceptT ε IO α → TestTree
      testIsJust tn io = testCase tn $ run io ≫ assertIsJust

      testDoesNotExist ∷ (Show α, AsIOError ε, Printable ε) =>
                         TestName → ExceptT ε IO α → TestTree
      testDoesNotExist tn io = testCase tn $ runE io ≫ assertDoesNotExist

  in  testGroup "EMonad" $
        [ testIsJust       "open ok"         $ openr passwd
        , testDoesNotExist "open not ok"     $ openr nonsuch
        , testDoesNotExist "open not ok→ok"  $ openr nonsuch ⪼ openr passwd
        , testDoesNotExist "open not ok × 2" $ openr nonsuch ⪼ openr nonsuch
        , testDoesNotExist "open ok→not ok"  $ openr passwd  ⪼ openr nonsuch
        , testIsJust       "open ok→ok"      $ openr passwd  ⪼ openr group
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
