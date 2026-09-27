module LogPlus.BatchingOptions
  ( fileBatchingOptions, ttyBatchingOptions )
where

import Base1T

-- logging-effect ----------------------

import Control.Monad.Log  ( BatchingOptions( BatchingOptions )
                          , blockWhenFull, flushMaxDelay, flushMaxQueueSize )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

--------------------------------------------------------------------------------

{-| Options suitable for logging to a file; notably a 1s flush delay and keep
    messages rather than dropping if the queue fills.
 -}
fileBatchingOptions ∷ BatchingOptions
fileBatchingOptions = BatchingOptions { flushMaxDelay     = 1_000_000
                                      , blockWhenFull     = 𝓣
                                      , flushMaxQueueSize = 100
                                      }

----------------------------------------

{-| Options suitable for logging to a tty; notably a short flush delay (0.2s),
    and drop messages rather than blocking if the queue fills (which should
    be unlikely, with a length of 100 & 0.1s flush).
 -}

ttyBatchingOptions ∷ BatchingOptions
-- The max delay is a matter of experimentation; too high, and messages appear
-- long after their effects on stdout are apparent (not *wrong*, but a bit
-- misleading/inconvenient); too low, and the message lines get broken up
-- and intermingled with stdout (again, not *wrong*, but a terrible user
-- experience).
ttyBatchingOptions = BatchingOptions { flushMaxDelay     = 2_000
                                     , blockWhenFull     = 𝓕
                                     , flushMaxQueueSize = 100
                                     }

-- that's all, folks! ----------------------------------------------------------
