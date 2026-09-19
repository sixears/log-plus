module LogPlus.Compressor
  ( Compressor, HasCompressorMay( compressorMay ) )
where

import Base1T

-- lens --------------------------------

import Control.Lens.Getter  ( view )

------------------------------------------------------------
--                     local imports                       -
------------------------------------------------------------

import LogPlus.CompressorIO       ( CompressorIO,HasCompressorIO(compressorIO) )
import LogPlus.FilenameExtension  ( FilenameExtension
                                  , HasFilenameExtension( filenameExtension
                                                        , filenameExtensionPC ))
import LogPlus.Name               ( HasName( name, nameS ), Name )
import LogPlus.New                ( New( new ) )

--------------------------------------------------------------------------------

{-| a way of compressing files -}
data Compressor = Compressor { -- | name purely for printing (`Show`) purposes
                               _cmp_name ∷ Name
                             , -- | takes from,to filenames and does the deed
                               _cmp_cmpr ∷ CompressorIO
                             , -- | filename extension to append (after a `.`)
                               _cmp_ext  ∷ FilenameExtension
                             }

----------

instance New Compressor (Name,CompressorIO,FilenameExtension) where
  new (n,io,fe) = Compressor n io fe

----------

instance Show Compressor where
  show c = let e = toString ∘ view filenameExtensionPC $ _cmp_ext c
           in  [fmt|Compressor: '%s' «%s»|] (c ⊣ nameS) e

----------

instance HasName Compressor where
  name = lens _cmp_name (\ c n → c { _cmp_name = n })

----------

instance HasCompressorIO Compressor where
  compressorIO = lens _cmp_cmpr (\ c x → c { _cmp_cmpr = x })

----------

instance HasFilenameExtension Compressor where
  filenameExtension = lens _cmp_ext (\ c x → c { _cmp_ext = x })

------------------------------------------------------------

class HasCompressorMay α where compressorMay ∷ Lens' α (𝕄 Compressor)

----------

instance HasCompressorMay (𝕄 Compressor) where
  compressorMay = lens id (const id)

-- that's all, folks! ----------------------------------------------------------
