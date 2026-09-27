module LogPlus.ToDoc_
  ( ToDoc_( toDoc_ ) )
where

import Base1T

-- prettyprinter -----------------------

import Prettyprinter  ( Doc, pretty )

--------------------------------------------------------------------------------

{-| this is called `ToDoc_` with an underscore to distinguish from any `ToDoc`
    class that took a parameter for the annotation type -}
class ToDoc_ α where toDoc_ ∷ α → Doc ()

instance ToDoc_ (Doc()) where toDoc_ = id
instance ToDoc_ 𝕋       where toDoc_ = pretty

-- that's all, folks! ----------------------------------------------------------
