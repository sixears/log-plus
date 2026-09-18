module LogPlus.MaxFiles
  ( HasMaxFiles( maxFiles, maxFiles16 ), MaxFiles )
where

import Base1T

-- base --------------------------------

import GHC.Enum  ( Enum )
import GHC.Num   ( Num )

-- lens --------------------------------

import Control.Lens.Getter  ( view )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.New  ( New( new ) )

--------------------------------------------------------------------------------

newtype MaxFiles = MaxFiles { unMaxFiles ∷ Word16 } deriving (Enum,Num,Show)

----------

instance New MaxFiles Word16 where new = MaxFiles

------------------------------------------------------------

class HasMaxFiles α where
  maxFiles   ∷ Lens' α MaxFiles
  maxFiles16 ∷ Lens' α Word16
  maxFiles16 = lens (unMaxFiles ∘ view maxFiles)
                    (\ a i → a & maxFiles ⊢ MaxFiles i)

----------

instance HasMaxFiles MaxFiles  where  maxFiles = lens id (const id)

-- that's all, folks! ----------------------------------------------------------
