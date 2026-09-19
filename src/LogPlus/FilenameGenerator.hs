module LogPlus.FilenameGenerator
  ( FilenameGenerator( filenameGenerator ) )
where

--------------------------------------------------------------------------------

class FilenameGenerator α β where filenameGenerator ∷ α → β

-- that's all, folks! ----------------------------------------------------------
