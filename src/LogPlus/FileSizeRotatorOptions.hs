module LogPlus.FileSizeRotatorOptions
  ( FileSizeRotatorOptions )
where

import Base1T

-- base --------------------------------

import GHC.Real  ( (^) )

-- base-unicode-symbols ----------------

import Prelude.Unicode  ( (×) )

-- unix --------------------------------

import System.Posix.Types  ( FileMode )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.Compressor                ( Compressor
                                         , HasCompressorMay( compressorMay )
                                         , compressPzstd
                                         )
import LogPlus.FilenameGenerator         ( FilenameGenerator( filenameGenerator ) )
import LogPlus.MaxFiles                  ( HasMaxFiles( maxFiles ), MaxFiles )
import LogPlus.MaxFileSize               ( HasMaxFileSize( maxFileSize )
                                         , MaxFileSize )
import LogPlus.New                       ( New( new ) )
import LogPlus.NumberedFilenameGenerator ( NumberedFilenameGenerator
                                         , NumberedFnGen
                                         , simpleNumberedFilenameGenerator
                                         )
import LogPlus.Perms                     ( HasPerms( perms ) )

--------------------------------------------------------------------------------

{-| options for fileSizeRotator -}
data FileSizeRotatorOptions =
     FileSizeRotatorOptions { -- | How to compress old files, if at all.
                              --   If not `Nothing`, the IO will be run in
                              --   its own thread and only one will be run
                              --   at a time; logging will continue to the
                              --   open file, even if oversized, until the
                              --   prior compression has completed.
                              _fsro_cmprss ∷ 𝕄 Compressor
                            , -- | max file size; rotate (& compress?)
                              --   files once they are about to exceed
                              --   this.  Each file will receive at least
                              --   one log message, but if the next log
                              --   message would cause the file to exceed
                              --   this size, then it will be rotated
                              --   unless there is an ongoing unfinished
                              --   compression
                              _fsro_mxsz   ∷ MaxFileSize
                            , -- | Create files with these file
                              --   permissions. Note that during
                              --   compression, the perms may be wrong:
                              --   they are set after compression has
                              --   completed
                              _fsro_perms  ∷ FileMode
                            , -- | maximum number of files to
                              --   manage/rotate; the numbers appended will
                              --   be zero-padded to all be the same length
                              _fsro_mxfs   ∷ MaxFiles
                            , -- | file name generator; takes the number of
                              --   the file numbered 0 for most recent,
                              --   incrementing; or 𝓝 for the file to
                              --   write current logs to
                              _fsro_fngen  ∷ NumberedFilenameGenerator
                            }
  deriving Show

----------

instance HasCompressorMay FileSizeRotatorOptions where
  compressorMay = lens _fsro_cmprss (\ f c → f { _fsro_cmprss = c })

----------

instance HasMaxFiles FileSizeRotatorOptions where
  maxFiles = lens _fsro_mxfs (\ f m → f { _fsro_mxfs = m })

----------

instance HasPerms FileSizeRotatorOptions where
  perms = lens _fsro_perms (\ f p → f { _fsro_perms = p })

----------

instance HasMaxFileSize FileSizeRotatorOptions where
  maxFileSize = lens _fsro_mxsz (\ f z → f { _fsro_mxsz = z })

----------

instance FilenameGenerator FileSizeRotatorOptions NumberedFnGen where
  filenameGenerator = filenameGenerator ∘ _fsro_fngen

----------

{- A default set of `FileSizeRotatorOptions`, which takes a logfile basename;
   compresses the files, sets a max size of 100MiB, perms of -rw-r--r--,
   maxFiles of ten files, and using the `simpleNumberedFilenameGenerator` to
   append a log number on old files (after a `.`), padded with enough digits to
   allow for the maximum number of files.
 -}
instance New FileSizeRotatorOptions MaxFiles where
  new mxf =
    let fngen = simpleNumberedFilenameGenerator mxf
    in  FileSizeRotatorOptions { _fsro_cmprss = 𝓙 compressPzstd
                               , _fsro_mxsz   = 100 × 1_024^(3∷Word8) -- 100MiB
                               , _fsro_perms  = 0o644
                               , _fsro_mxfs   = mxf
                               , _fsro_fngen  = fngen
                               }

-- that's all, folks! ----------------------------------------------------------
