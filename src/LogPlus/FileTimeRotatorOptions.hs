module LogPlus.FileTimeRotatorOptions
  ( FileTimeRotatorOptions )
where

import Base1T

-- fpath -------------------------------

import FPath.AbsDir  ( AbsDir )

-- monadio-plus ------------------------

import MonadIO.Directory  ( GlobPCRERegex )

-- time --------------------------------

import Data.Time.Format  ( FormatTime )

-- unix --------------------------------

import System.Posix.Types  ( FileMode )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.AbsDir                 ( HasAbsDir( absDir_ ) )
import LogPlus.Compressor             ( Compressor
                                       , HasCompressorMay( compressorMay )
                                       , compressPzstd
                                       )
import LogPlus.FilenameGenerator      ( FilenameGenerator( filenameGenerator ) )
import LogPlus.GlobPCRERegex          ( HasGlobPCRERegex( globPCRERegex ) )
import LogPlus.MaxFiles               ( HasMaxFiles( maxFiles )
                                       , MaxFiles )
import LogPlus.New                    ( New( new ) )
import LogPlus.Perms                  ( HasPerms( perms ) )
import LogPlus.TimeFilenameGenerator  ( TimeFilenameGenerator, TimeFnGen
                                      , dayFilenameGenerator )

--------------------------------------------------------------------------------

------------------------------------------------------------

{-| options for fileTimeRotator -}
data FileTimeRotatorOptions τ =
     FileTimeRotatorOptions { -- | How to compress old files, if at all.
                              --   If not `Nothing`, the IO will be run in
                              --   its own thread and only one will be run
                              --   at a time; logging will continue to the
                              --   open file, even if oversized, until the
                              --   prior compression has completed.
                              _ftro_cmprss ∷ 𝕄 Compressor
                            , -- | Create files with these file
                              --   permissions. Note that during
                              --   compression, the perms may be wrong:
                              --   they are set after compression has
                              --   completed
                              _ftro_perms  ∷ FileMode
                            , -- | Maximum number of files to
                              --   manage/rotate; the numbers appended will
                              --   be zero-padded to all be the same length.
                              --   Note that this number includes the current
                              --   file being written, so if set to (say) 3,
                              --   there should never be more than 3 matching
                              --   files (including the current one).
                              _ftro_mxfs   ∷ MaxFiles
                            , -- | file name generator; takes a timestamp or 𝓝
                              --   for the file to write current logs to
                              _ftro_fngen  ∷ TimeFilenameGenerator τ
                            , -- | file name glob (globs only over path
                              --   components, in the given directory)
                              _ftro_glob ∷ GlobPCRERegex
                            , -- | The directory to work in.  This rotator
                              --   can only use a single directory, due to
                              --   the globbing.
                              _ftro_dir ∷ AbsDir
                            }
  deriving Show

----------

instance HasCompressorMay (FileTimeRotatorOptions τ) where
  compressorMay = lens _ftro_cmprss (\ f c → f { _ftro_cmprss = c })

----------

instance HasMaxFiles (FileTimeRotatorOptions τ) where
  maxFiles = lens _ftro_mxfs (\ f m → f { _ftro_mxfs = m })

----------

instance HasPerms (FileTimeRotatorOptions τ) where
  perms = lens _ftro_perms (\ f p → f { _ftro_perms = p })

----------

instance FilenameGenerator (FileTimeRotatorOptions τ) (TimeFnGen τ) where
  filenameGenerator = filenameGenerator ∘ _ftro_fngen

----------

instance HasAbsDir (FileTimeRotatorOptions τ) where
  absDir_ = lens _ftro_dir (\ o d → o { _ftro_dir = d })

----------

instance HasGlobPCRERegex (FileTimeRotatorOptions τ) where
  globPCRERegex = lens _ftro_glob (\ o g → o { _ftro_glob = g })

----------

{- A default set of `FileTimeRotatorOptions`, which takes a logfile basename;
   compresses the files, sets a max time of 100MiB, perms of -rw-r--r--, maxFiles
   of ten files, and using the `simpleNumberedFilenameGenerator` to append a
   log number on old files (after a `.`), padded with enough digits to allow for
   the maximum number of files.

 -}
instance (FormatTime τ, Show τ) => New (FileTimeRotatorOptions τ)
                                       (AbsDir,GlobPCRERegex)     where
  new (dir,pcre) = let fngen = dayFilenameGenerator
                   in  FileTimeRotatorOptions { _ftro_cmprss = 𝓙 compressPzstd
                                              , _ftro_perms  = 0o644
                                              , _ftro_mxfs   = new (10 ∷ Word16)
                                              , _ftro_fngen  = fngen
                                              , _ftro_glob   = pcre
                                              , _ftro_dir    = dir
                                              }

-- that's all, folks! ----------------------------------------------------------
