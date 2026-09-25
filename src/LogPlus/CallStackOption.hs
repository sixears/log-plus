module LogPlus.CallStackOption
  ( CallStackOption(..), stackParses, stdRenderers )
where

import Base1T

-- base --------------------------------

import Data.Enum  ( Enum )

-- parsec-plus -------------------------

import ParsecPlus  ( Parsecable( parser ) )

-- parser-plus -------------------------

import ParserPlus  ( caseInsensitiveString, tries )

------------------------------------------------------------
--                     local imports                      --
------------------------------------------------------------

import Log.LogRenderOpts  ( LogR, renderWithCallStack, renderWithSeverity
                          , renderWithStackHead, renderWithTimestamp )

--------------------------------------------------------------------------------

data CallStackOption = NoCallStack | CallStackHead | FullCallStack
  deriving (Enum, Eq, Show)

----------

instance Parsecable CallStackOption where
  parser =
    -- Lookup table of String to `CallStackOption`; these are the strings that
    -- will be parsed to `CallStackOption` (with `Parseable`).  Parsing is
    -- case-insensitive.
    let stackOptions ∷ NonEmpty (String,CallStackOption)
        stackOptions =    ("NoCallStack"   , NoCallStack)
                     :| [ ("NoCS"          , NoCallStack)
                        , ("CSHead"        , CallStackHead)
                        , ("CSH"           , CallStackHead)
                        , ("CallStackHead" , CallStackHead)
                        , ("FCS"           , FullCallStack)
                        , ("FullCallStack" , FullCallStack)
                        , ("FullCS"        , FullCallStack)
                        , ("CallStack"     , FullCallStack)
                        , ("Stack"         , FullCallStack)
                        ]
    in  tries [ caseInsensitiveString st ⋫ return cso | (st,cso) ← stackOptions ]

------------------------------------------------------------

{-| lookup table of `CallStackOption` to possible (case-insensitive) string
    representations-}
stackParses ∷ CallStackOption → [String]
stackParses NoCallStack   = [ "NoCallStack", "NoCS" ]
stackParses CallStackHead = [ "CallStackHead", "CSHead", "CSH" ]
stackParses FullCallStack = [ "FullCallStack", "FullCS", "CallStack", "Stack" ]

----------------------------------------

stdRenderers ∷ CallStackOption → [LogR ω]
stdRenderers NoCallStack =
  [ renderWithTimestamp, renderWithSeverity ]
stdRenderers CallStackHead =
  [ renderWithTimestamp, renderWithSeverity, renderWithStackHead ]
stdRenderers FullCallStack =
  [ renderWithCallStack, renderWithTimestamp, renderWithSeverity ]

-- that's all, folks! ----------------------------------------------------------
