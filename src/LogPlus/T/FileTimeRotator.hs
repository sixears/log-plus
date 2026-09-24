module LogPlus.T.FileTimeRotator
  ( tests )
where

import Base1T

-- base --------------------------------

import Data.Bifunctor  ( bimap )
import Data.List       ( sort, sortOn )

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

import MonadIO.Directory  ( directoryList, inDir, mkGlobRegex )
import MonadIO.Temp       ( __progNamePrefix__, __tempdir__, testsWithTempDir'')

-- tasty -------------------------------

import Test.Tasty  ( DependencyType( AllSucceed ), dependentTestGroup )

-- tasty-hunit -------------------------

import Test.Tasty.HUnit  ( assertEqual, assertFailure )

-- time --------------------------------

import Data.Time.Calendar.OrdinalDate  ( fromOrdinalDate )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import Log                      ( logToFiles', warnT )

import LogPlus.Compressor       ( Compressor, compressorMay, compressPzstd )
import LogPlus.FileTimeRotator  ( fileTimeRotator_ )
import LogPlus.MaxFiles         ( maxFiles )
import LogPlus.New              ( new )

--------------------------------------------------------------------------------

fileTimeRotatorTests ∷ TestTree
fileTimeRotatorTests =
  let nil       = const $ return ()
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
        -- we need to turn off batching here for predictable results
        logToFiles' (𝓙 bopts) [] [] (rot 252) $ mapM_ (warnT @())
                    [ "deleted??" -- this should get rotated away into the ether
                    ]
        logToFiles' (𝓙 bopts) [] [] (rot 253) $ mapM_ (warnT @())
                    [ "123"
                    , "456"
                    , "7"
                    , "abc"
                    ]
        logToFiles' (𝓙 bopts) [] [] (rot 254) $ mapM_ (warnT @())
                    [ "αβγδεζηθικλ"
                    , "μνξ"
                    , "πρσ"
                    , "τφχ"
                    ]
        -- x ≡ 255 → 2026-09-12
        logToFiles' (𝓙 bopts) [] [] (rot 255) $ mapM_ (warnT @())
                    [ "defghijkl" -- 10 bytes: should be another new file
                    , "mnopqrstuvwxyz" -- 15 bytes: should be unbroken
                    ]
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
          -- , ("listdir", \ (d,_)→listdirStdOut def d⪼assertSuccess "listdir")
             , ("logfile names", \ (d,(fs,_,_,_)) →
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
                                , ([relfile|logfile-2026-09-11|],24)
                                , ([relfile|logfile-2026-09-12|],25)
                                ]
                   assertEqual "file sizes" expect sizes
               )
             ]
             {- ◇ ((\ (i∷ℕ,fn∷RelFile) → ("cat " ◇ show i, \ (d,_) → do
                   ѥ (readFileUTF8Lenient @IOError fn) ≫ \ case
                     𝓛 e → liftIO $ assertFailure (show e)
                     𝓡 t → liftIO $ do
                       putStrLn ("---- " ◇ T.pack (show fn) ◇ "----")
                       putStrLn t
                       putStrLn "----"
                       assertSuccess ("cat" ◇ T.pack (show i))
               )) ⊳ [ (0,[relfile|logfile.0|])
                    , (1,[relfile|logfile.1|])
                    , (2,[relfile|logfile.2|])
                    ])
             -}
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
                                , ([relfile|logfile-2026-09-11.zst|],49)
                                , ([relfile|logfile-2026-09-12|],25)
                                ]
                   assertEqual "file sizes" expect sizes
               )
             ]
             {- ◇ ((\ (i∷ℕ,fn∷RelFile) → ("cat " ◇ show i, \ (d,_) → do
                   ѥ (readFileUTF8Lenient @IOError fn) ≫ \ case
                     𝓛 e → liftIO $ assertFailure (show e)
                     𝓡 t → liftIO $ do
                       putStrLn ("---- " ◇ T.pack (show fn) ◇ "----")
                       putStrLn t
                       putStrLn "----"
                       assertSuccess ("cat" ◇ T.pack (show i))
               )) ⊳ [ (0,[relfile|logfile.0|])
                    , (1,[relfile|logfile.1|])
                    , (2,[relfile|logfile.2|])
                    ])
             -}
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
