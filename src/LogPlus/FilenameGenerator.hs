module LogPlus.FilenameGenerator
  ( FilenameGenerator( filenameGenerator ) )
where

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

--------------------------------------------------------------------------------

class FilenameGenerator α β where filenameGenerator ∷ α → β

-- that's all, folks! ----------------------------------------------------------
