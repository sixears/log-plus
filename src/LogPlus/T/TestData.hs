module LogPlus.T.TestData
  ( _le0, _le1, _le2, _le3, _le4n, _le5n, _log0io, _log0m, _log1m )
where

import Base1T

-- base --------------------------------

import Control.Concurrent  ( threadDelay )
import GHC.Stack           ( SrcLoc( SrcLoc ), fromCallSiteList )

-- logging-effect ----------------------

import Control.Monad.Log  ( MonadLog
                          , Severity( Emergency,Critical,Informational,Warning )
                          , logMessage
                          )

-- more-unicode ------------------------

import Data.MoreUnicode.Doc  ( (⊞) )

-- prettyprinter -----------------------

import Prettyprinter  ( align, pretty, vsep )

-- time --------------------------------

import Data.Time.Calendar  ( fromGregorian )
import Data.Time.Clock     ( UTCTime( UTCTime ), secondsToDiffTime )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus           ( logIO, logT )
import LogPlus.Log       ( Log )
import LogPlus.LogEntry  ( LogEntry, logEntry, logEntryNoCS )

--------------------------------------------------------------------------------

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
_le0 = logEntry _cs2 (Just _tm) Informational (pretty ("log_entry 1" ∷ 𝕋)) ()

_le1 ∷ LogEntry ()
_le1 =
  logEntry _cs1 Nothing Critical (pretty ("multi-line\nlog\nmessage" ∷ 𝕋)) ()

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
  logEntry _cs1 Nothing Emergency (pretty ("this is the last message" ∷𝕋)) ()

_le4n ∷ LogEntry ℕ
_le4n = logEntryNoCS Nothing Warning  (pretty ("start" ∷ 𝕋)) 1

_le5n ∷ LogEntry ℕ
_le5n = logEntryNoCS Nothing Critical (pretty ("end" ∷ 𝕋)) 2

----------------------------------------

_log0 ∷ Log ()
_log0 = fromList [_le0]

_log0m ∷ MonadLog (Log ()) η => η ()
_log0m = logMessage _log0

_log1 ∷ Log ()
_log1 = fromList [ _le0, _le1, _le2, _le3 ]

_log1m ∷ MonadLog (Log ()) η => η ()
_log1m = logMessage _log1

_log2 ∷ MonadLog (Log ℕ) η => η ()
_log2 = do logT Warning       1 "start"
           logT Informational 3 "middle"
           logT Critical      2 "end"

_log0io ∷ (MonadIO μ, MonadLog (Log ℕ) μ) => μ ()
_log0io = do logIO @𝕋 Warning 1 "start"
             liftIO $ threadDelay 1_000_000
             logIO @𝕋 Informational 3 "middle"
             liftIO $ threadDelay 1_000_000
             logIO @𝕋 Critical 2 "end"

_log1io ∷ (MonadIO μ, MonadLog (Log ℕ) μ) => μ ()
_log1io = do logIO @𝕋 Warning 1 "start"
             liftIO $ threadDelay 1_000_000
             logIO @𝕋 Informational 3 "you shouldn't see this"
             liftIO $ threadDelay 1_000_000
             logIO @𝕋 Critical 2 "end"

-- that's all, folks! ----------------------------------------------------------
