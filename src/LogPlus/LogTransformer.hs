module LogPlus.LogTransformer
  ( LogTransformer )
where

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import LogPlus.LogEntry  ( LogEntry )

--------------------------------------------------------------------------------

type LogTransformer ω = LogEntry ω → [LogEntry ω]

-- that's all, folks! ----------------------------------------------------------
