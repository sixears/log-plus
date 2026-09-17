module LogPlus.StdErr
  ( stdErr, stdErrT, eToStderr, eToStderrIO )
where

import Base1T

-- base --------------------------------

import System.IO  ( stderr )

-- text --------------------------------

import Data.Text.IO  ( hPutStrLn )

--------------------------------------------------------------------------------

{-| write some text to stderr (in case something fails within the logging) -}
stdErr ∷ (MonadIO μ, Printable τ) => τ → μ ()
stdErr = liftIO ∘ hPutStrLn stderr ∘ toText

----------

{-| `stdErr`, input type reified to `𝕋` -}
stdErrT ∷ MonadIO μ => 𝕋 → μ ()
stdErrT = stdErr

--------------------

{-| given an Either, dump a `Left` to stderr; return `Right` as a `Just` -}
eToStderr ∷ ∀ ε α μ . (MonadIO μ, Printable ε) => 𝔼 ε α → μ (𝕄 α)
eToStderr (𝓛 e) = stdErrT (toText e) ⪼ return 𝓝
eToStderr (𝓡 r) = return (𝓙 r)

----------

{-| `eToStderr`, reified to `IO()` -}
eToStderrIO ∷ Printable ε => 𝔼 ε α → IO ()
eToStderrIO = const () ⩺ eToStderr

-- that's all, folks! ----------------------------------------------------------
