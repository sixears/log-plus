module LogPlus.CompressorIO
  ( CompressorIO, HasCompressorIO(..) )
where

import Base1T

-- fpath -------------------------------

import FPath.AbsFile  ( AbsFile )

-- lens --------------------------------

import Control.Lens.Getter  ( view )

------------------------------------------------------------
--                     local imports                       -
------------------------------------------------------------

import LogPlus.New  ( New( new ) )

--------------------------------------------------------------------------------

{-| takes from,to filenames and does the deed -}
newtype CompressorIO = CompressorIO { unCompressorIO ∷ AbsFile→AbsFile→IO() }

----------

instance New CompressorIO (AbsFile → AbsFile → IO()) where new = CompressorIO

------------------------------------------------------------

class HasCompressorIO α where
  compressorIO ∷ Lens' α CompressorIO
  compressorIOF ∷ Lens' α (AbsFile → AbsFile → IO())
  compressorIOF = lens (unCompressorIO ∘ view compressorIO)
                       (\ a f → a & compressorIO ⊢ CompressorIO f)

----------

instance HasCompressorIO CompressorIO where compressorIO = lens id (const id)

-- that's all, folks! ----------------------------------------------------------
