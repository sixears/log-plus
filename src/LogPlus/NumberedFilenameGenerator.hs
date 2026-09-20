module LogPlus.NumberedFilenameGenerator
  ( NumberedFilenameGenerator, NumberedFnGen, simpleNumberedFilenameGenerator )
where

import Base1T

-- base --------------------------------

import GHC.Real  ( Integral, div )

-- fpath -------------------------------

import FPath.AbsFile        ( AbsFile )
import FPath.FileLike       ( (⊙) )
import FPath.Parseable      ( __parseS__ )
import FPath.PathComponent  ( PathComponent )

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
import LogPlus.New                ( New( new ) )

--------------------------------------------------------------------------------

type NumberedFnGen = AbsFile → 𝕄 MaxFiles → AbsFile
-- XXX type NumberedFnGen = FileLike α => α → 𝕄 MaxFiles → α

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
      parsePC = __parseS__ @PathComponent
-- XXX
--      go_ ∷ (FileLike α, HasMaxFiles β) => α → 𝕄 β → α
--      go_ ∷ (HasMaxFiles β) => PathComponent → 𝕄 β → PathComponent
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

        in  (fn ⊙) ∘ parsePC ∘ num $ fromIntegral (i ⊣ maxFiles16)

  in  new @NumberedFilenameGenerator @(𝕊,NumberedFnGen) (name_,go_)

-- that's all, folks! ----------------------------------------------------------
