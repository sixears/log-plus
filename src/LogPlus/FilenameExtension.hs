module LogPlus.FilenameExtension
  ( FilenameExtension
  , HasFilenameExtension( appendExtension, filenameExtension
                        , filenameExtensionPC )
  )
where

import Base1T

-- fpath -------------------------------

import FPath.FileLike       ( FileLike, (⊙) )
import FPath.PathComponent  ( PathComponent )

-- lens --------------------------------

import Control.Lens.Getter  ( view )

------------------------------------------------------------
--                     local imports                       -
------------------------------------------------------------

import LogPlus.New  ( New( new ) )

--------------------------------------------------------------------------------

{-| filename extension, e.g., to be appended after a `.` character -}
newtype FilenameExtension =
  FilenameExtension { unFilenameExtension ∷ PathComponent }

instance New FilenameExtension PathComponent  where  new = FilenameExtension

------------------------------------------------------------

class HasFilenameExtension α where
  filenameExtension   ∷ Lens' α FilenameExtension
  filenameExtensionPC ∷ Lens' α PathComponent
  filenameExtensionPC =
    lens (unFilenameExtension ∘ view filenameExtension)
         (\ a p → a & filenameExtension ⊢ FilenameExtension p)
  {-| append this extension to an existing PathComponent -}
  appendExtension     ∷ FileLike γ => α → γ → γ
  appendExtension a f = f ⊙ (a ⊣ filenameExtensionPC)

----------

instance HasFilenameExtension FilenameExtension where
  filenameExtension = lens id (const id)

-- that's all, folks! ----------------------------------------------------------
