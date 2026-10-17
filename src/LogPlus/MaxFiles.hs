module LogPlus.MaxFiles
  ( HasMaxFiles( maxFiles, maxFiles16 ), MaxFiles )
where

import Base1T

-- base --------------------------------

import GHC.Enum  ( Enum )
import GHC.Num   ( Num )

-- base-plus ---------------------------

import BasePlus.Word16  ( IsWord16( word16 ) )
import BasePlus.New     ( New( new ) )

-- lens --------------------------------

import Control.Lens.Getter  ( view )
import Control.Lens.Iso     ( iso )

--------------------------------------------------------------------------------

newtype MaxFiles = MaxFiles { unMaxFiles ∷ Word16 } deriving (Enum,Num,Show)

----------

instance New MaxFiles Word16 where new = MaxFiles

----------

instance IsWord16 MaxFiles where word16 = iso unMaxFiles MaxFiles

------------------------------------------------------------

class HasMaxFiles α where
  maxFiles   ∷ Lens' α MaxFiles
  maxFiles16 ∷ Lens' α Word16
  maxFiles16 = lens (unMaxFiles ∘ view maxFiles)
                    (\ a i → a & maxFiles ⊢ MaxFiles i)

----------

instance HasMaxFiles MaxFiles  where  maxFiles = lens id (const id)

-- that's all, folks! ----------------------------------------------------------
