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

||| A second ranging from 0 to 60.
|||
||| `60` is used for leap seconds.
public export
record Second where
  constructor MkSecond
  second : Bits8
  {auto 0 valid : FromTo 0 60 second}

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
  {auto 0 valid : fraction > -1}

namespace Fraction
  %runElab derive "Fraction" [Show, Eq, Ord]

||| Sign of an UTC `Offset` or of an offset `Duration`.
|||
||| `Plus` stands for `+`.
||| `Minus` stands for `-`.
public export
data Sign = Plus | Minus

%runElab derive "Sign" [Show, Eq]

Ord Sign where
  compare Plus  Plus  = EQ
  compare Minus Minus = EQ
  compare Plus  Minus = GT
  compare Minus Plus  = LT

namespace Duration

  ||| Number of hours of a time `Duration`.
  public export
  record Hours where
    constructor MkHours
    hours : Integer
    {auto 0 valid : hours > -1}

  %runElab derive "Hours" [Show, Eq, Ord]

  ||| Number of minutes of a time `Duration`.
  public export
  record Minutes where
    constructor MkMinutes
    minutes : Integer
    {auto 0 valid : minutes > -1}

  %runElab derive "Minutes" [Show, Eq, Ord]

  ||| Number of seconds of a time `Duration`.
  public export
  record Seconds where
    constructor MkSeconds
    seconds : Integer
    {auto 0 valid : seconds > -1}

  %runElab derive "Seconds" [Show, Eq, Ord]

  ||| Fractions of a second of a time `Duration`.
  |||
  ||| This number is what comes after `,` or `.`.
  ||| For example, if you provide `25`, then the fraction is `,25` (or `.25`).
  public export
  record Fraction where
    constructor MkFraction
    fraction : Integer
    {auto 0 valid : fraction > -1}

  %runElab derive "Fraction" [Show, Eq, Ord]

  ||| A time `Duration` as per ISO 8601 PTnHnMnS.sss format.
  public export
  record Duration where
    constructor MkDuration
    hours    : Hours
    minutes  : Minutes
    seconds  : Seconds
    fraction : Duration.Fraction

  %runElab derive "Duration" [Show, Eq, Ord]

namespace Offset

  ||| Number of hour of an UTC offset.
  |||
  ||| The range from `0` to `14` covers the existing offsets.
  ||| In theory, more could be added in the future.
  public export
  record Hours where
    constructor MkHours
    hours : Bits8
    {auto 0 valid : FromTo 0 14 hours}

  namespace Hours
    %runElab derive "Offset.Hours" [Show, Eq, Ord, RefinedInteger]

  ||| `ElemOf [m, n] o` is an alias for `(Equal m || Equal n) o`.
  |||
  ||| For example, using `hdec0` you can write:
  |||
  ||| ```idris example
  ||| hdec0 {p = ElemOf [0, 15, 30, 40]} value
  ||| ```
  private
  0 ElemOf : List t -> t -> Type
  ElemOf []        = const Void
  ElemOf (x :: []) = Equal x
  ElemOf (x :: xs) = Equal x || ElemOf xs

  ||| Number of minutes for an UTC offset of a time in complement of an hour.
  |||
  ||| At the time being, only values 0, 30 and 45 have been used.
  ||| For consistency, the value 15 has been added here.
  public export
  record Minutes where
    constructor MkMinutes
    minutes : Bits8
    {auto 0 valid : ElemOf [0, 15, 30, 45] minutes}

  namespace Minutes
    %runElab derive "Offset.Minutes" [Show, Eq, Ord, RefinedInteger]

  ||| A zero value time offset cannot be stated with a negative sign.
  |||
  ||| ```idris example
  ||| validOffset Minus 0 0 == False
  ||| ```
  |||
  ||| This is as per ISO 8601.
  private
  validOffset : Sign -> Offset.Hours -> Offset.Minutes -> Bool
  validOffset Minus 0 0 = False
  validOffset _     _ _ = True

  ||| An UTC offset for a given time.
  public export
  record Offset where
    constructor MkOffset
    sign    : Sign
    hours   : Offset.Hours
    minutes : Offset.Minutes
    {auto 0 valid : validOffset sign hours minutes = True}

  %runElab derive "Offset" [Show, Eq, Ord]
