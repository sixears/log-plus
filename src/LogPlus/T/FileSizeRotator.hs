module LogPlus.T.FileSizeRotator
  ( tests )
where

import Base1T

-- base --------------------------------

import Data.Bifunctor  ( bimap )
import Data.List       ( sort, sortOn )

-- fpath -------------------------------

import FPath                   ( (⫻), stripDirFPE )
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

import MonadIO.Directory  ( directoryList, inDir )
import MonadIO.Temp       ( __progNamePrefix__, __tempdir__, testsWithTempDir'' )

-- tasty -------------------------------

import Test.Tasty  ( DependencyType( AllSucceed ), dependentTestGroup )

-- tasty-hunit -------------------------

import Test.Tasty.HUnit  ( assertEqual, assertFailure )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import Log                      ( logToFiles', warnT )

import LogPlus.Compressor       ( Compressor, compressorMay, compressPzstd )
import LogPlus.FileSizeRotator  ( fileSizeRotator )
import LogPlus.MaxFiles         ( MaxFiles, maxFiles )
import LogPlus.MaxFileSize      ( maxFileSize )
import LogPlus.New              ( new )

--------------------------------------------------------------------------------

tests ∷ TestTree
tests =
  let nil       = const $ return ()
      do_log    ∷ 𝕄 Compressor → AbsDir
                → IO ([(AbsFile, FStat)], [(AbsDir, FStat)],
                      [(AbsFile, FPathIOError)],
                      [(AbsDir, FPathIOError)]
                     )
      do_log c d  = ж @IOError ∘ inDir d $ do
        let opts    = (new @_ @MaxFiles 10) & compressorMay ⊢ c
                                                    & maxFileSize   ⊢ 10
                                                    & maxFiles      ⊢ 3
            rot     = fileSizeRotator opts (d ⫻ [relfile|logfile|])
            bopts   = BatchingOptions { flushMaxDelay = 1
                                      , blockWhenFull = 𝓣
                                      , flushMaxQueueSize = 1
                                      }
        -- we need to turn off batching here for predictable results
        logToFiles' (𝓙 bopts) [] [] rot $ mapM_ (warnT @())
                    [ "deleted??" -- this should get rotated away into the ether
                    , "123" -- each line gets a '\n' added, so that's four bytes
                    , "456" -- +4 => 8
                    , "7"   -- +2 => 10
                    , "abc" -- 4 bytes: should be a new file
                    , "defghijkl" -- 10 bytes: should be another new file
                    , "mnopqrstuvwxyz" -- 15 bytes: should be unbroken
                    ]
        directoryList @FPathIOError @FPathIOError def d

  in  dependentTestGroup "simpleSizeRotator" AllSucceed $
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
                     𝓡 fs' → let expect = [ [relfile|logfile|]
                                           , [relfile|logfile.0|]
                                           , [relfile|logfile.1|]
                                           , [relfile|logfile.2|]
                                           ]
                             in  assertEqual "files" expect (sort fs')
               )

             , ("logfile sizes", \ (_,(fs,_,_,_)) → do
                   let sizes  = sortOn fst $ bimap basename size ⊳ fs
                       expect = [ ([relfile|logfile|],15)
                                , ([relfile|logfile.0|],10)
                                , ([relfile|logfile.1|],4)
                                , ([relfile|logfile.2|],10)
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
            ((◇ [pc|-|]) ⊳ __progNamePrefix__)(do_log(𝓙 compressPzstd)) nil nil
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
                     𝓡 fs' → let expect = [ [relfile|logfile|]
                                           , [relfile|logfile.0.zst|]
                                           ]
                             in  assertEqual "files" expect (sort fs')
               )

             , ("logfile sizes", \ (_,(fs,_,_,_)) → do
                   let sizes  = sortOn fst $ bimap basename size ⊳ fs
                       expect = [ -- the 10-byte limit will only effect when
                                  -- compression is complete, which in practice
                                  -- won't be untill all the writing is done; so
                                  -- it all gets piled onto here
                                  ([relfile|logfile|],39)
                                  -- although 10 bytes uncompressed, the header
                                  -- will actually increase the file size
                                , ([relfile|logfile.0.zst|],35)
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

-- that's all, folks! ----------------------------------------------------------
