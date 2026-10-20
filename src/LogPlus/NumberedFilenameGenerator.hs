module LogPlus.NumberedFilenameGenerator
  ( NumberedFilenameGenerator, NumberedFnGen, simpleNumberedFilenameGenerator )
where

import Base1T

-- base --------------------------------

import GHC.Real  ( Integral, div )

-- base-plus ---------------------------

import BasePlus.New  ( New( new ) )

-- fpath -------------------------------

import FPath.AbsFile            ( AbsFile )
import FPath.FileLike           ( (⊙) )
import FPath.FilenameExtension  ( FilenameExtension )
import FPath.Parseable          ( __parseS__ )

-- natural -----------------------------

import Natural            ( (⊟) )
import Natural.Length     ( щ )
import Natural.Replicate  ( replicate_ )
import Natural.Unsigned   ( I64, Unsigned )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.FilenameGenerator  ( FilenameGenerator( filenameGenerator ) )
import LogPlus.MaxFiles           ( HasMaxFiles( maxFiles16 ), MaxFiles )

--------------------------------------------------------------------------------

type NumberedFnGen = AbsFile → 𝕄 MaxFiles → AbsFile

data NumberedFilenameGenerator =
  NumberedFilenameGenerator
    { _nfg_name  ∷ 𝕊 -- ^ just for `Show`
    , _nfg_fngen ∷ NumberedFnGen }

----------

instance Show NumberedFilenameGenerator where
  show = _nfg_name

----------

instance New NumberedFilenameGenerator (𝕊, NumberedFnGen) where
  new (s,g) = NumberedFilenameGenerator s g

----------

instance FilenameGenerator NumberedFilenameGenerator NumberedFnGen where
  filenameGenerator = _nfg_fngen

------------------------------------------------------------

{-| a simple filename generator, which adds (0-based) denary numbers to the end
    of the filename (after a '.') but pads them out to the required length as per
    `mxf` -}
simpleNumberedFilenameGenerator ∷ MaxFiles → NumberedFilenameGenerator
simpleNumberedFilenameGenerator mxf =
  let name_ = "simpleNumberedFilenameGenerator (" ◇ show mxf ◇ ")"
      parseFE = __parseS__ @FilenameExtension
      go_ ∷ (HasMaxFiles β) => AbsFile → 𝕄 β → AbsFile
      go_ fn 𝓝    = fn
      go_ fn (𝓙 i) =
        let numDigits ∷ (Integral α, Unsigned α) => α → I64
            numDigits 0 = 1
            numDigits n = countDigits n
              where
                countDigits 0 = 0
                countDigits x = 1 + countDigits (x `div` 10)

            padNumber ∷ I64 → I64 → 𝕊
            padNumber p n = let str = show n
                            in  (replicate_ (p ⊟ щ str) '0') ◇ str

            -- -1 because we start counting at '0'
            num = padNumber (numDigits $ (mxf ⊣ maxFiles16) - 1)

        in  (fn ⊙) ∘ parseFE ∘ num $ fromIntegral (i ⊣ maxFiles16)

  in  new @NumberedFilenameGenerator @(𝕊,NumberedFnGen) (name_,go_)

-- that's all, folks! ----------------------------------------------------------
