||| High-level definition of the time library.
module Data.Time

import Data.Refined
import Data.Refined.Bits8
import Data.Refined.Integer
import Derive.Prelude
import Derive.Refined

%default total
%language ElabReflection

||| An hour ranging from 0 to 23.
public export
record Hour where
  constructor MkHour
  hour : Bits8
  {auto 0 valid : FromTo 0 23 hour}

namespace Hour
  %runElab derive "Hour" [Show, Eq, Ord, RefinedInteger]

||| A minute ranging from 0 to 59.
public export
record Minute where
  constructor MkMinute
  minute : Bits8
  {auto 0 valid : FromTo 0 59 minute}

namespace Minute
  %runElab derive "Minute" [Show, Eq, Ord, RefinedInteger]

||| A second ranging from 0 to 59.
public export
record Second where
  constructor MkSecond
  second : Bits8
  {auto 0 valid : FromTo 0 59 second}

namespace Second
  %runElab derive "Second" [Show, Eq, Ord, RefinedInteger]

||| A fraction of a second from 0.
|||
||| This number is what comes after `,` or `.`.
||| For example, if you provide `25`, then the fraction is `,25` (or `.25`).
public export
record Fraction where
  constructor MkFraction
  fraction : Integer
  {auto 0 valid : From 0 fraction}

namespace Fraction
  %runElab derive "Fraction" [Show, Eq, Ord]
