module LogPlus.ListPlus
  ( firstJust, takeWhileM )
where

import Base1T

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

--------------------------------------------------------------------------------

takeWhileM ∷ Monad η => (α → η 𝔹) → [α] → η [α]
takeWhileM _ []    = return []
takeWhileM p (x:xs)= p x ≫ \ b→ if b then (x:) ⊳ takeWhileM p xs else return []

----------------------------------------

{-| The first non-𝓝 value in a list, if any -}
firstJust ∷ [𝕄 α] → 𝕄 α
firstJust []          = 𝓝
firstJust ((𝓙 x) : _) = 𝓙 x
firstJust (𝓝 : xs)    = firstJust xs

-- that's all, folks! ----------------------------------------------------------
