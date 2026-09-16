module LogPlus.Name
  ( HasName( name, nameS ), Name )
where

import Base1T

-- base --------------------------------

import Data.String  ( IsString )

-- lens --------------------------------

import Control.Lens.Getter  ( view )

------------------------------------------------------------
--                     local imports                       -
------------------------------------------------------------

import LogPlus.New  ( New( new ) )

--------------------------------------------------------------------------------

newtype Name = Name { unName ∷ 𝕊 }  deriving  (IsString,Show)

----------

instance New Name 𝕊  where  new = Name

------------------------------------------------------------

class HasName α where
  name  ∷ Lens' α Name
  nameS ∷ Lens' α 𝕊
  nameS = lens (unName ∘ view name) (\ a s → a & name ⊢ Name s)

----------

instance HasName Name  where  name = lens id (const id)

-- that's all, folks! ----------------------------------------------------------
