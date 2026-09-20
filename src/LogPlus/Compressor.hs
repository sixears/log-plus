module LogPlus.Compressor
  ( Compressor, HasCompressorMay( compressorMay ), compressPzstd )
where

import Base1T

-- base --------------------------------

import Data.Tuple  ( uncurry )

-- fpath -------------------------------

import FPath.AbsFile        ( AbsFile )
import FPath.PathComponent  ( pc )

-- lens --------------------------------

import Control.Lens.Getter  ( view )

-- monadio-plus ------------------------

import MonadIO.File                   ( devnull )
import MonadIO.Error.CreateProcError  ( ProcError )
import MonadIO.Process                ( doProc )
import MonadIO.Process.CmdSpec        ( mkCmd )

------------------------------------------------------------
--                     local imports                       -
------------------------------------------------------------

import LogPlus.CompressorIO       ( CompressorIO,HasCompressorIO(compressorIO) )
import LogPlus.FilenameExtension  ( FilenameExtension
                                  , HasFilenameExtension( filenameExtension
                                                        , filenameExtensionPC ))
import LogPlus.Name               ( HasName( name, nameS ), Name )
import LogPlus.New                ( New( new ) )
import LogPlus.StdErr             ( eToStderrIO )

import LogPlus.Paths  qualified as  Paths

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

------------------------------------------------------------

compressPzstd ∷ Compressor
compressPzstd =
  let pzstd ∷ MonadIO μ => AbsFile → AbsFile → ExceptT ProcError μ ()
      pzstd f t = do
        let args = ["--quiet", "--check", toText f, "-o", toText t, "--rm"]
            exe  = Paths.pzstd
        null ← devnull
        () ← snd ⊳ doProc (return ()) null (uncurry mkCmd (exe,args))
        return ()
      pzstdIO ∷ AbsFile → AbsFile → IO ()
      pzstdIO f t = join $ eToStderrIO ⊳ (ѥ @ProcError $ pzstd f t)
  in  new (new @Name @String "pstzd",new @CompressorIO pzstdIO,
           new @FilenameExtension [pc|zst|])

-- that's all, folks! ----------------------------------------------------------
