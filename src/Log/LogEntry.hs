{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE UnicodeSyntax     #-}

module Log.LogEntry
  ( LogEntry, attrs, logdoc, logEntry, mapDoc, mapPrefixDoc, prefix, simpleDoc
  , _le0, _le1, _le2, _le3, _le4n, _le5n )
where

import Prelude  ( seq )

-- base --------------------------------

import Data.Bool      ( Bool( False, True ) )
import Data.Eq        ( Eq( (==) ) )
import Data.Function  ( ($), (&) )
import Data.Functor   ( Functor( fmap ) )
import Data.Maybe     ( Maybe( Just, Nothing ) )
import Data.Ord       ( (<) )
import Data.String    ( String )
import GHC.Generics   ( Generic )
import GHC.Num        ( abs )
import GHC.Stack      ( CallStack, SrcLoc( SrcLoc ), fromCallSiteList )
import Text.Show      ( Show( show ) )

-- base-unicode-symbols ----------------

import Data.Bool.Unicode     ( (∧) )
import Data.Eq.Unicode       ( (≡) )
import Data.Function.Unicode ( (∘) )
import Data.Monoid.Unicode   ( (⊕) )

-- data-textual ------------------------

import Data.Textual  ( Printable( print ) )

-- deepseq -----------------------------

import Control.DeepSeq  ( NFData( rnf ) )

-- has-callstack -----------------------

import HasCallstack  ( HasCallstack( callsitelist, callstack ) )

-- lens --------------------------------

import Control.Lens.Lens  ( Lens, Lens', lens )

-- logging-effect ----------------------

import Control.Monad.Log  ( Severity( Critical, Emergency, Informational
                                    , Warning ) )

-- more-unicode ------------------------

import Data.MoreUnicode.Lens     ( (⊣), (⊢), (⊧) )
import Data.MoreUnicode.Natural  ( ℕ )
import Data.MoreUnicode.Text     ( 𝕋 )

-- prettyprinter -----------------------

import Prettyprinter              ( Doc, (<+>), align, defaultLayoutOptions
                                  , layoutPretty, pretty, vsep )
import Prettyprinter.Render.Text  ( renderStrict )

-- tasty-plus --------------------------

import TastyPlus.Equish  ( Equish( (≃) ) )

-- text --------------------------------

import Data.Text  ( Text, pack, take )

-- text-printer ------------------------

import qualified  Text.Printer  as  P

-- tfmt --------------------------------

import Text.Fmt  ( fmt )

-- time --------------------------------

import Data.Time.Calendar  ( fromGregorian )
import Data.Time.Clock     ( UTCTime( UTCTime ), diffUTCTime,secondsToDiffTime )

------------------------------------------------------------
--                     local imports                      ---
-----------------------------------------------------------

import Log.HasSeverity   ( HasSeverity( severity ) )
import Log.HasUTCTime    ( HasUTCTimeY( utcTimeY ) )

--------------------------------------------------------------------------------

{- | A single log entry with timestamp, callstack, severity. -}
data LogEntry ω = LogEntry { _callstack ∷ CallStack
                           , _timestamp ∷ Maybe UTCTime
                           , _severity  ∷ Severity
                           , _logdoc    ∷ Doc ()
                           , _attrs     ∷ ω
                           }
  deriving (Generic,Show)

-- Functor -----------------------------

instance Functor LogEntry where
  fmap f le = le & attrs ⊧ f

-- Eq ----------------------------------

instance Eq ω ⇒ Eq (LogEntry ω) where
  le == le' = let simpleDoc' l = layoutPretty defaultLayoutOptions (l ⊣ logdoc)
               in   le ⊣ callsitelist ≡ le' ⊣ callsitelist
                  ∧ le ⊣ utcTimeY     ≡ le' ⊣ utcTimeY
                  ∧ le ⊣ severity     ≡ le' ⊣ severity
                  ∧ simpleDoc' le     ≡ simpleDoc' le'
                  ∧ le ⊣ attrs        ≡ le' ⊣ attrs

-- Equish ------------------------------

instance Equish ω ⇒ Equish (LogEntry ω) where
  {- | Approximately equal; that is, equal but with timestamps differing by no
       more than 10s (absolute); and no check on the callsitelist. -}
  le ≃ le' = let simpleDoc' l = layoutPretty defaultLayoutOptions (l ⊣ logdoc)
              in   (case ((le ⊣ utcTimeY), (le' ⊣ utcTimeY)) of
                      (Nothing, Nothing) → True
                      (Just t,  Just t') → abs (diffUTCTime t t') < 10
                      (_, _)             → False
                   )

                 ∧ le ⊣ severity     ≡ le' ⊣ severity
                 ∧ simpleDoc' le     ≡ simpleDoc' le'
                 ∧ le ⊣ attrs        ≃ le' ⊣ attrs

{- | Construct a log entry, with no callstack -}
logEntryNoCS ∷ Maybe UTCTime → Severity → Doc() → ω → LogEntry ω
logEntryNoCS = logEntry ([] ∷ [(String,SrcLoc)])

-- HasCallstack ------------------------

instance HasCallstack (LogEntry ω) where
  callstack = lens _callstack (\ le cs → le { _callstack = cs })

-- HasSeverity -------------------------

instance HasSeverity (LogEntry ω) where
  severity = lens _severity (\ le sv → le { _severity = sv })

-- HasUTCTimeY -------------------------

instance HasUTCTimeY (LogEntry ω) where
  utcTimeY = lens _timestamp (\ le tm → le { _timestamp = tm })

-- NFData ------------------------------

instance NFData ω ⇒ NFData (LogEntry ω) where
  -- the uses of seq are naughty, but neither Severity nor Doc() are instances
  -- of Doc.  Severity is just an enumeration, but Doc() really should be.
  -- We're being very bad, but I can't be bothered to create a correct orphan
  -- instance at this point.
  rnf (LogEntry cs ts sv dc at) = rnf (rnf cs, rnf ts, seq sv, seq dc, rnf at)

----------------------------------------

logdoc ∷ Lens' (LogEntry ω)  (Doc ())
logdoc = lens _logdoc (\ le d → le { _logdoc = d })

----------------------------------------

attrs ∷ Lens (LogEntry ω) (LogEntry ω') ω ω'
attrs = lens _attrs (\ le as → le { _attrs = as })

----------------------------------------

logEntry ∷ HasCallstack α ⇒
           α → Maybe UTCTime → Severity → Doc() → ω → LogEntry ω
logEntry cs = LogEntry (cs ⊣ callstack)

----------------------------------------

{- | Change the `logdoc` to some function of the whole `LogEntry`. -}
mapDoc ∷ (LogEntry ω → Doc ()) → LogEntry ω → LogEntry ω
mapDoc f e = e & logdoc ⊢ f e

----------------------------------------

{- | Prefix the `logdoc` with some other `Doc()`. -}
prefix ∷ LogEntry ω → Doc() → LogEntry ω
prefix e d = e & logdoc ⊧ (d ⊕)

----------------------------------------

{- | Prefix the `logdoc` with some function of the whole `LogEntry`. -}
mapPrefixDoc ∷ (LogEntry ω → Doc()) → LogEntry ω → LogEntry ω
mapPrefixDoc f = mapDoc (\ e → f e ⊕ e ⊣ logdoc)

-- rendering -----------------------------------------------

instance Printable ω ⇒ Printable (LogEntry ω) where
  print le =
    let renderDoc = renderStrict ∘ layoutPretty defaultLayoutOptions
     in P.text $ [fmt|[%Z|%-4t] %k %t <%T>|]
                                          (le ⊣ utcTimeY)
                                          (take 4 ∘ pack ∘ show $ le ⊣ severity)
                                          le
                                          (renderDoc $ le ⊣ logdoc)
                                          (le ⊣ attrs)

----------------------------------------

{- | Simplest rendering of a `LogEntry`; just the message as `𝕋`. -}
simpleDoc ∷ LogEntry ω → 𝕋
simpleDoc l = renderStrict $ layoutPretty defaultLayoutOptions (l ⊣ logdoc)

-- test data -------------------------------------------------------------------

_cs0 ∷ CallStack
_cs0 = fromCallSiteList []

_cs1 ∷ CallStack
_cs1 = fromCallSiteList [ ("stack0", SrcLoc "z" "x" "y" 9 8 7 6) ]

_cs2 ∷ CallStack
_cs2 = fromCallSiteList [ ("stack0", SrcLoc "a" "b" "c" 1 2 3 4)
                        , ("stack1", SrcLoc "d" "e" "f" 5 6 7 8) ]

_tm ∷ UTCTime
_tm = UTCTime (fromGregorian 1970 1 1) (secondsToDiffTime 0)

_le0 ∷ LogEntry ()
_le0 = logEntry _cs2 (Just _tm) Informational (pretty ("log_entry 1" ∷ Text)) ()

_le1 ∷ LogEntry ()
_le1 =
  logEntry _cs1 Nothing Critical (pretty ("multi-line\nlog\nmessage" ∷ Text)) ()

infixr 5 ⊞
-- hsep
(⊞) ∷ Doc α → Doc α → Doc α
(⊞) = (<+>)

_le2 ∷ LogEntry ()
_le2 =
  let valign = align ∘ vsep
      msg    = "this is" ⊞ valign [ "a"
                                  , "vertically"
                                    ⊞ valign [ "aligned"
                                             , "message"
                                             ]
                                  ]
   in logEntry _cs1 (Just _tm) Warning msg ()
_le3 ∷ LogEntry ()
_le3 =
  logEntry _cs1 Nothing Emergency (pretty ("this is the last message" ∷Text)) ()

_le4n ∷ LogEntry ℕ
_le4n = logEntryNoCS Nothing Warning  (pretty ("start" ∷ Text)) 1

_le5n ∷ LogEntry ℕ
_le5n = logEntryNoCS Nothing Critical (pretty ("end" ∷ Text)) 2

-- that's all, folks! ----------------------------------------------------------
