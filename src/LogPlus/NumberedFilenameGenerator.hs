module LogPlus.NumberedFilenameGenerator
  ( NumberedFilenameGenerator, NumberedFnGen )
where

import Base1T

-- fpath -------------------------------

import FPath.AbsFile  ( AbsFile )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.FilenameGenerator  ( FilenameGenerator( filenameGenerator ) )
import LogPlus.MaxFiles           ( MaxFiles )
import LogPlus.New                ( New( new ) )

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

-- that's all, folks! ----------------------------------------------------------
