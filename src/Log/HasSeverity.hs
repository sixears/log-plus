{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax     #-}

module Log.HasSeverity
  ( HasSeverity( severity ) )
where

import Base1T

-- logging-effect ----------------------

import Control.Monad.Log  ( Severity )

--------------------------------------------------------------------------------

class    HasSeverity α        where severity ∷ Lens' α Severity
instance HasSeverity Severity where severity = id

-- that's all, folks! ----------------------------------------------------------
