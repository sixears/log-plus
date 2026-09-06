import Base1

-- base --------------------------------

import Control.Monad  ( forever )

-- fpath -------------------------------

import FPath.AbsFile           ( AbsFile )
import FPath.Dirname           ( dirname )
import FPath.Error.FPathError  ( FPathIOError )
import FPath.File              ( File( FileA ) )

-- monaderror-io -----------------------

import MonadError.IO.Error  ( ioError )

-- monadio-plus ------------------------

import MonadIO        ( warn )
import MonadIO.File   ( AccessMode( ACCESS_W ), access )
import MonadIO.FPath  ( pResolve )

-- optparse-applicative ----------------

import Options.Applicative  ( Parser
                            , argument, flag, help, long, metavar, progDesc, short, str )

-- optparse-plus -----------------------

import OptParsePlus  ( parseOpts )

-- text --------------------------------

import Data.Text.IO  ( getLine )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import Log  ( compressorMay, compressPzstd, fileSizeRotator, info', logToFiles
            , mkFileSizeRotatorOptions )

--------------------------------------------------------------------------------

data Compress = CompressPzstd | NoCompress

data Options = Options { _fn ∷ 𝕋, _compress ∷ Compress }

parseOptions ∷ Parser Options
parseOptions = let argMeta = metavar "FILE" <> help "file to query"
               in  Options ⊳ argument str argMeta
                           ⊵ flag CompressPzstd NoCompress
                                  (ю [ short 'N' ,long "no-compress"
                                     , help "do not compress old logs" ])

{-| throw an ε into IO as a user error -}
ԙ ∷ ∀ ε α μ . (MonadIO μ, Printable ε) ⇒ ExceptT ε μ α → μ α
ԙ f = ѥ f ≫ \ case
         𝓛 e → ioError (userE $ toString e)
         𝓡 r → return r

я ∷ ∀ α μ . (MonadIO μ) ⇒ ExceptT FPathIOError μ α → μ α
я = ԙ

main ∷ IO ()
main = do
  -- XXX add option to log time + format
  opts ← parseOpts (progDesc "write to logs") parseOptions
  -- XXX resolve local filenames
  -- cwd ∷ AbsDir ← getCwd_
  fn ← я (pResolve @AbsFile $ _fn opts) ≫ \ fn →
         я (access ACCESS_W fn) ≫ \ case
           𝓝   → let dn = fn ⊣ dirname
                 in  я (access ACCESS_W dn) ≫ \ case
                   𝓝   → ioError (userE $ [fmt|no such dir: '%T'|] dn)
                   𝓙 𝓣 → return fn
                   𝓙 𝓕 → ioError (userE $ [fmt|dir not writable: '%T'|] dn)
           𝓙 𝓣 → return fn
           𝓙 𝓕 → ioError (userE $ [fmt|file not writable: '%T'|] fn)

  warn $ [fmtT|fn: '%T'|] fn

  let log_renderers    = []
      log_transformers = []
      fsr_opts         = mkFileSizeRotatorOptions 10 & compressorMay ⊢ compressor
                         where compressor = case _compress opts of
                                              CompressPzstd → 𝓙 compressPzstd
                                              NoCompress    → 𝓝
      rotator          = fileSizeRotator fsr_opts (FileA fn)

  logToFiles log_renderers log_transformers rotator $ forever (liftIO getLine ≫ info' @())

-- that's all, folks! ----------------------------
