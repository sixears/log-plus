{- XXX move this somewhere -}

module LogPlus.New
  ( New( new ) )
where

--------------------------------------------------------------------------------

class New α β where new ∷ β → α

-- that's all, folks! ----------------------------------------------------------
