module LogPlus.ℍMay
  ( HasℍMay(..) )
where

import Base1T

-- monadio-plus ------------------------

import MonadIO.NamedHandle  ( ℍ )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

--------------------------------------------------------------------------------

class    HasℍMay α      where  𝕙May ∷ Lens' α (𝕄 ℍ)
instance HasℍMay (𝕄 ℍ)  where  𝕙May = lens id (const id)

-- that's all, folks! ----------------------------------------------------------
