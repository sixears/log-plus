module LogPlus.T.FileTimeRotator
  ( tests )
where

import Base1T

-- base --------------------------------

import Data.Bifunctor  ( bimap )
import Data.List       ( sort, sortOn )

-- base-plus ---------------------------

import BasePlus.Maybe   ( whenJust )
import BasePlus.New     ( new )

-- fpath -------------------------------

import FPath                   ( stripDirFPE )
import FPath.AbsDir            ( AbsDir )
import FPath.AbsFile           ( AbsFile )
import FPath.Basename          ( basename )
import FPath.Error.FPathError  ( FPathIOError )
import FPath.PathComponent     ( pc )
import FPath.RelFile           ( relfile )

-- fstat -------------------------------

import FStat  ( FStat, size )

-- logging-effect ----------------------

import Control.Monad.Log  ( BatchingOptions( BatchingOptions, blockWhenFull
                                           , flushMaxQueueSize ), flushMaxDelay)

-- monaderror-io -----------------------

import MonadError           ( ж )
import MonadError.IO.Error  ( IOError )

-- monadio-plus ------------------------

import MonadIO.Directory    ( directoryList, inDir, listdirStdOut, mkGlobRegex )
import MonadIO.NamedHandle  ( namedHandleMay, hClose )
import MonadIO.OpenFile     ( readFileUTF8Lenient, writeFile )
import MonadIO.Temp         ( __progNamePrefix__,__tempdir__,testsWithTempDir'')

-- tasty -------------------------------

import Test.Tasty  ( DependencyType( AllSucceed ), dependentTestGroup )

-- tasty-hunit -------------------------

import Test.Tasty.HUnit  ( assertEqual, assertFailure )

-- text --------------------------------

import qualified  Data.Text     as  T
import qualified  Data.Text.IO  as  TIO

-- time --------------------------------

import Data.Time.Calendar.OrdinalDate  ( fromOrdinalDate )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus                  ( logToFiles', warnT )

import LogPlus.Compressor       ( Compressor, compressorMay, compressPzstd )
import LogPlus.FileTimeRotator  ( fileTimeRotator_ )
import LogPlus.MaxFiles         ( maxFiles )

--------------------------------------------------------------------------------

fileTimeRotatorTests ∷ TestTree
fileTimeRotatorTests =
  let list_dirs = 𝓕 -- set to 𝓣 to list the contents of the written dir
      cat_files = 𝓕 -- set to 𝓣 to cat the written files

      cat_file fn = ("cat " ◇ toString fn, \ (_,_) → do
                     ѥ (readFileUTF8Lenient @IOError fn) ≫ \ case
                       𝓛 e → liftIO $ assertFailure (show e)
                       𝓡 t → liftIO $ do
                         TIO.putStrLn ("---- " ◇ T.pack (show fn) ◇ "----")
                         TIO.putStrLn t
                         TIO.putStrLn "----"
                         assertSuccess ("cat" ◇ toText fn)
                    )

      nil       = const $ return ()
      do_log    ∷ 𝕄 Compressor → AbsDir
                → IO ([(AbsFile, FStat)], [(AbsDir, FStat)],
                      [(AbsFile, FPathIOError)],
                      [(AbsDir, FPathIOError)]
                     )
      do_log c d  = ж @IOError ∘ inDir d $ do
        let opts    = let pcre = mkGlobRegex ("logfile-.*"∷𝕊)
                      in  new (d,pcre) & compressorMay ⊢ c & maxFiles ⊢ 3
            rot x   =
              \ st w t → do
                (h,st') ← fileTimeRotator_ opts ([pc|logfile|])
                                           (fromOrdinalDate 2026 x) st w t
                return (h,st')
            bopts   = BatchingOptions { flushMaxDelay = 1
                                      , blockWhenFull = 𝓣
                                      , flushMaxQueueSize = 1
                                      }

        -- write to first file, and third file, to test what happens with extant
        -- files
        writeFile @IOError (𝓙 0o600) [relfile|logfile-2026-09-09|]("wibble\n"∷𝕋)
        writeFile @IOError (𝓙 0o600) [relfile|logfile-2026-09-11|]("wobble\n"∷𝕋)

        -- we need to turn off batching here for predictable results
        -- 2026-09-09
        ((),st) ← logToFiles' 𝓝 (𝓙 bopts) [] [] (rot 252) $ mapM_ (warnT @())
                    [ "deleted??" -- this should get rotated away into the ether
                    ]
        -- 2026-09-10
        ((),ṡt) ← logToFiles' (𝓙 st)(𝓙 bopts) [] [] (rot 253)$ mapM_ (warnT @())
                    [ "123" -- 4
                    , "456" -- 8
                    , "7"   -- 10
                    , "abc" -- 14 bytes total (including newlines)
                    ]
        -- 2026-09-11
        ((),sṫ) ← logToFiles' (𝓙 ṡt)(𝓙 bopts) [] [] (rot 254)$ mapM_ (warnT @())
                    [ "αβγδεζηθικλ" -- 12 bytes (incl. '\n') + 7 "wobble\n" == 19
                    , "μνξ"         -- 23
                    , "πρσ"         -- 27
                    , "τφχ"         -- 31
                    ]
        -- 2026-09-12
        ((),ṡṫ) ← logToFiles' (𝓙 sṫ)(𝓙 bopts) [] [] (rot 255)$ mapM_ (warnT @())
                    [ "defghijkl"      -- 10 bytes (incl. '\n')
                    , "mnopqrstuvwxyz" -- 15 bytes makes 25
                    ]
        whenJust hClose (ṡṫ ⊣ namedHandleMay)
        directoryList @FPathIOError @FPathIOError def d

  in  dependentTestGroup "simpleTimeRotator" AllSucceed $

        [ testsWithTempDir'' "no-compression" __tempdir__
            ((◇ [pc|-|]) ⊳ __progNamePrefix__) (do_log 𝓝) nil nil
            ([ ("check", const $ assertSuccess "check")
             , ("no file errors", \ (_,(_,_,efs,_)) →
                   assertEqual "file errors" [] efs
               )
             , ("no directory errors", \ (_,(_,_,_,dfs)) →
                   assertEqual "directory errors" [] dfs
               )
             , ("no subdirectories", \ (d,(_,ds,_,_)) →
                   assertEqual "directories" [d] (fst ⊳ ds)
               )
             ]
             ◇ if list_dirs
               then [ ("listdir",
                       \ (d,_) → listdirStdOut def d ⪼ assertSuccess "listdir")
                    ]
               else []
             ◇
             [
               ("logfile names", \ (d,(fs,_,_,_)) →
                   case sequence (stripDirFPE d ⊳ fst ⊳ fs) of
                     𝓛 e   → assertFailure $ show e
                     𝓡 fs' → let expect = [ [relfile|logfile-2026-09-10|]
                                          , [relfile|logfile-2026-09-11|]
                                          , [relfile|logfile-2026-09-12|]
                                          ]
                             in  assertEqual "files" expect (sort fs')
               )

             , ("logfile sizes", \ (_,(fs,_,_,_)) → do
                   let sizes  = sortOn fst $ bimap basename size ⊳ fs
                       expect = [ ([relfile|logfile-2026-09-10|],14)
                                , ([relfile|logfile-2026-09-11|],31)
                                , ([relfile|logfile-2026-09-12|],25)
                                ]
                   assertEqual "file sizes" expect sizes
               )
             ]

             ◇ if cat_files
               then cat_file ⊳ [ [relfile|logfile-2026-09-10|]
                               , [relfile|logfile-2026-09-11|]
                               , [relfile|logfile-2026-09-12|]
                               ]
               else []
            )

        , testsWithTempDir'' "with-compression" __tempdir__
            ((◇ [pc|-|]) ⊳ __progNamePrefix__) (do_log(𝓙 compressPzstd)) nil nil
            ([ ("check", const $ assertSuccess "check")
             , ("no file errors", \ (_,(_,_,efs,_)) →
                   assertEqual "file errors" [] efs
               )
             , ("no directory errors", \ (_,(_,_,_,dfs)) →
                   assertEqual "directory errors" [] dfs
               )
             , ("no subdirectories", \ (d,(_,ds,_,_)) →
                   assertEqual "directories" [d] (fst ⊳ ds)
               )
          -- , ("listdir", \ (d,_)→listdirStdOut def d⪼ assertSuccess "listdir")
             , ("logfile names", \ (d,(fs,_,_,_)) →
                   case sequence (stripDirFPE d ⊳ fst ⊳ fs) of
                     𝓛 e   → assertFailure $ show e
                     𝓡 fs' → let expect = [ [relfile|logfile-2026-09-10.zst|]
                                          , [relfile|logfile-2026-09-11.zst|]
                                          , [relfile|logfile-2026-09-12|]
                                          ]
                             in  assertEqual "files" expect (sort fs')
               )

             , ("logfile sizes", \ (_,(fs,_,_,_)) → do
                   let sizes  = sortOn fst $ bimap basename size ⊳ fs
                       expect = [ ([relfile|logfile-2026-09-10.zst|],39)
                                , ([relfile|logfile-2026-09-11.zst|],56)
                                , ([relfile|logfile-2026-09-12|],25)
                                ]
                   assertEqual "file sizes" expect sizes
               )
             ]

             ◇ if cat_files
               then -- don't cat the .zst files (unless you want a mess...)
                    cat_file ⊳ [ [relfile|logfile-2026-09-12|]
                               ]
               else []
            )
        ]

----------------------------------------

tests ∷ TestTree
tests = testGroup "FileTimeRotator" [ fileTimeRotatorTests ]

----------------------------------------

_test ∷ IO ExitCode
_test = runTestTree tests

--------------------

_tests ∷ String → IO ExitCode
_tests = runTestsP tests

_testr ∷ String → ℕ → IO ExitCode
_testr = runTestsReplay tests

-- that's all, folks! ----------------------------------------------------------
