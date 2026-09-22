module LogPlus.ListPlus
  ( takeWhileM )
where

import Base1T

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

--------------------------------------------------------------------------------

takeWhileM ∷ Monad η => (α → η 𝔹) → [α] → η [α]
takeWhileM _ []    = return []
takeWhileM p (x:xs)= p x ≫ \ b → if b then (x:) ⊳ takeWhileM p xs else return []
-- that's all, folks! ----------------------------------------------------------
