module LogPlus.FileSizeRotator
  ( fileNumberedMoves )
where

import Base1T

import Prelude  ( error )

-- base --------------------------------

import Data.List       ( zip )
import Data.Tuple      ( uncurry )

-- fpath -------------------------------

import FPath.AbsFile  ( AbsFile )
import FPath.File     ( File( FileA, FileR ) )

-- lens --------------------------------

import Control.Lens.Setter     ( over )
import Control.Lens.Traversal  ( both )

-- monaderror-io -----------------------

import MonadError.IO.Error  ( IOError )

-- monadio-plus ------------------------

import MonadIO.FStat        ( FExists( FExists ), lfexists )
import MonadIO.NamedHandle  ( ℍ, hname )

-- safe --------------------------------

import Safe  ( tailSafe )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.Compressor              ( Compressor, compressorMay )
import LogPlus.EMonad                  ( ꙝ )
import LogPlus.FilenameExtension       ( appendExtension )
import LogPlus.FilenameGenerator       ( filenameGenerator )
import LogPlus.FileSizeRotatorOptions  ( FileSizeRotatorOptions )
import LogPlus.ListPlus                ( takeWhileM )
import LogPlus.MaxFiles                ( MaxFiles, maxFiles )

--------------------------------------------------------------------------------

{-| List of moves (and potentially compresses) to perform for numbered file
    rotation; this accounts for actual file existence.  This doesn't actually
    perform any destructive IO (just some `stat`s); rather provides a list of
    instructions.
-}
-- XXX how are we checking for which files need compressing?
-- XXX use EMonad and friends?

fileNumberedMoves ∷ MonadIO μ => AbsFile → FileSizeRotatorOptions → 𝕄 ℍ
                               → μ [(AbsFile, AbsFile, 𝕄 Compressor)]
fileNumberedMoves fn opts ɦ =
  let compress    = opts ⊣ compressorMay
      fngen       ∷ AbsFile → 𝕄 MaxFiles → AbsFile -- XXX
      fngen       = filenameGenerator opts
      max_files   = opts ⊣ maxFiles
      fngen' i    = maybe id appendExtension compress $ fngen fn i
      fn_nums     = 𝓙 ⊳ [0..(max_files-1)] -- -1 because we start at 0
      fn_pairs    = (over both fngen') ⊳ zip fn_nums (tailSafe fn_nums)
      abs_hname h =
        case h ⊣ hname of
          FileA a → a
          FileR r →
            error $ [fmt|relative file in hname: this should never happen %T|] r
      init_fnpair = (maybe (fngen fn 𝓝) abs_hname ɦ,fngen fn (𝓙 0),compress)
      -- `proto_moves` is the list of potential files to move, before filtering
      -- on whether they actually exist
      -- only compress when making the first archive file
      proto_moves = init_fnpair : (uncurry (,,𝓝) ⊳ (fn_pairs))
  in  flip takeWhileM proto_moves $ \ (from,_to,_do_compress) →
                                    (≡ 𝓙 FExists) ⊳⊳ ꙝ @IOError $ lfexists from

-- that's all, folks! ----------------------------------------------------------
