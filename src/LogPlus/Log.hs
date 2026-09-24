module LogPlus.Log
  ( Log, WithLog, WithLogIO, WithLogIOL, mapLog, mapLogE )
where

import Base1T  hiding  ( toList )

-- base --------------------------------

import Data.Foldable  ( all, foldMap )
import Data.List      ( zip )
import Data.Monoid    ( Monoid )
import GHC.Exts       ( IsList( toList ) )
import GHC.Generics   ( Generic )

-- deepseq -----------------------------

import Control.DeepSeq  ( NFData )

-- dlist -------------------------------

import qualified  Data.DList  as  DList
import Data.DList  ( DList )

-- logging-effect ----------------------

import Control.Monad.Log  ( MonadLog )

-- single ------------------------------

import Single( MonoSingle( osingle ), single )

-- mono-traversable --------------------

import Data.MonoTraversable  ( Element
                             , MonoFoldable( ofoldl', ofoldl1Ex', ofoldr
                                           , ofoldr1Ex , ofoldMap, olength
                                           , otoList )
                             , MonoFunctor( omap )
                             )

-- tasty-plus --------------------------

import TastyPlus.Equish  ( Equish( (≃) ) )

-- text --------------------------------

import Data.Text      qualified as  T

-- text-printer ------------------------

import qualified  Text.Printer  as  P

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import Log.LogEntry  ( LogEntry, LogEntry )

import LogPlus.New  ( New( new ) )

--------------------------------------------------------------------------------

{-| a list of LogEntries -}
newtype Log ω = Log { unLog ∷ DList (LogEntry ω) }
  deriving (Eq,Functor,Generic,Monoid,NFData,Semigroup,Show)

----------

type instance Element (Log ω) = LogEntry ω

----------

instance New (Log ω) (DList (LogEntry ω)) where new = Log

{- This Foldable instance would give rise to toList being a list of α, i.e., the
   payload; rather than of LogEntry α; which, therefore, would be a
   contradiction of IsList.toList -- that will lead to surprises, I don't think
   it's a good idea.

instance Foldable Log where
  foldr ∷ ∀ α β . (α → β → β) → β → Log α → β
  foldr f b (Log ls) = foldr (f ∘ view attrs) b ls
-}

----------

instance MonoFoldable (Log ω) where
  otoList    (Log dl)     = toList dl
  ofoldl'    f x (Log dl) = foldl' f x dl
  ofoldr     f x (Log dl) = foldr  f x dl
  ofoldMap   f (Log dl)   = foldMap f dl
  ofoldr1Ex  f (Log dl)   = foldr1 f dl
  ofoldl1Ex' f (Log dl)   = foldl1 f dl

----------

instance MonoFunctor (Log ω) where
  omap f (Log dl) = Log (f ⊳ dl)

----------

instance Printable ω => Printable (Log ω) where
  print = P.text ∘ T.unlines ∘ toList ∘ fmap toText ∘ unLog

----------

instance Equish ω => Equish (Log ω) where
  l ≃ l' = olength l ≡ olength l'
         ∧ all (\ (x,x') → x ≃ x') (zip (otoList l) (otoList l'))

----------

instance MonoSingle (Log ω) where
  osingle w = Log (single w)

----------

instance IsList (Log ω) where
  type Item (Log ω) = LogEntry ω
  fromList ∷ [LogEntry ω] → Log ω
  fromList = new ∘ DList.fromList
  toList   = DList.toList ∘ unLog

----------------------------------------

{-| `WithLog` adds in the `CallStack` constraint, so that if you declare your
    function to use this constraint, your function will be included in the
    logged callstack.  If you do not include the `CallStack` constraint, then
    the callpoint from within the function lacking the constraint (and anything
    calling it) will not be shown in the callstack.
 -}
type WithLog α η = (MonadLog (Log α) η, ?stack ∷ CallStack)
{-| `WithLog`, but with MonadIO, too -}
type WithLogIO α μ = (MonadIO μ, MonadLog (Log α) μ, ?stack ∷ CallStack)

type WithLogIOL α μ η = (MonadIO μ, MonadLog (Log α) η, ?stack ∷ CallStack)

----------------------------------------

mapLog ∷ ∀ α β . ([LogEntry α] → [LogEntry β]) → Log α → Log β
mapLog f l =
  new @(Log β) @(DList (LogEntry β)) ∘ fromList $ f (toList $ unLog l)

mapLogE ∷ ∀ α β . (LogEntry α → LogEntry β) → Log α → Log β
mapLogE f = mapLog (fmap f)

-- that's all, folks! ----------------------------------------------------------
