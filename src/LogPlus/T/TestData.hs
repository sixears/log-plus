module LogPlus.T.TestData
  ( _log0io, _log0m, _log1m )
where

import Base1T

-- base --------------------------------

import Control.Concurrent  ( threadDelay )

-- logging-effect ----------------------

import Control.Monad.Log  ( MonadLog
                          , Severity( Critical, Informational, Warning )
                          , logMessage
                          )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import Log  ( logIO, logT )

import Log.LogEntry  ( _le0,_le1,_le2,_le3 )

import LogPlus.Log  ( Log )

--------------------------------------------------------------------------------

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
