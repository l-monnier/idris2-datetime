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
||| For example, if you provide `0.25`, then the fraction part is `,25`
||| (or `.25`).
public export
record Fraction where
  constructor MkFraction
  fraction : Double
  {auto 0 valid : Integer.From 0 (cast $ floor fraction)}

namespace Fraction
  %runElab derive "Fraction" [Show, Eq, Ord]

  refineFraction : Double -> Maybe Fraction
  refineFraction fraction = case hdec0 {p = Integer.From 0} (cast $ floor fraction) of
    Just0 _  => Just (MkFraction fraction)
    Nothing0 => Nothing

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
    {auto 0 valid : From 0 hours}

  namespace Hours
    %runElab derive "Hours" [Show, Eq, Ord, RefinedInteger]

  Semigroup Hours where
    (MkHours h1) <+> (MkHours h2) = case refineHours (h1 + h2) of
      Just hours => hours
      -- This case cannot be reached as both numbers are equal or above 0.
      Nothing    => MkHours 0

  ||| Number of minutes of a time `Duration`.
  public export
  record Minutes where
    constructor MkMinutes
    minutes : Integer
    {auto 0 valid : From 0 minutes}

  namespace Minutes
    %runElab derive "Minutes" [Show, Eq, Ord, RefinedInteger]

  Semigroup Minutes where
    (MkMinutes m1) <+> (MkMinutes m2) = case refineMinutes (m1 + m2) of
      Just minutes => minutes
      -- This case cannot be reached as both numbers are equal or above 0.
      Nothing    => MkMinutes 0

  ||| Number of seconds of a time `Duration`.
  public export
  record Seconds where
    constructor MkSeconds
    seconds : Integer
    {auto 0 valid : From 0 seconds}

  namespace Seconds
    %runElab derive "Seconds" [Show, Eq, Ord, RefinedInteger]

  Semigroup Seconds where
    (MkSeconds s1) <+> (MkSeconds s2) = case refineSeconds (s1 + s2) of
      Just seconds => seconds
      -- This case cannot be reached as both numbers are equal or above 0.
      Nothing    => MkSeconds 0

  ||| Fractions of a second of a time `Duration`.
  |||
  ||| This number is what comes after `,` or `.`.
  ||| For example, if you provide `0.25`, then the fraction part is `,25`
  ||| (or `.25`).
  public export
  record Fraction where
    constructor MkFraction
    fraction : Double
    {auto 0 valid : Integer.From 0 (cast $ floor fraction)}

  %runElab derive "Fraction" [Show, Eq, Ord]

  refineFraction : Double -> Maybe Duration.Fraction
  refineFraction fraction = case hdec0 {p = Integer.From 0} (cast $ floor fraction) of
    Just0 _  => Just (MkFraction fraction)
    Nothing0 => Nothing

  Semigroup Duration.Fraction where
    (MkFraction f1) <+> (MkFraction f2) = case Duration.refineFraction (f1 + f2) of
      Just fraction => fraction
      -- This case cannot be reached as both numbers are equal or above 0.
      Nothing    => MkFraction 0

  ||| A time `Duration` as per ISO 8601 PTnHnMnS.sss format.
  public export
  record Duration where
    constructor MkDuration
    sign     : Sign
    hours    : Hours
    minutes  : Minutes
    seconds  : Seconds
    fraction : Duration.Fraction

  %runElab derive "Duration" [Show, Eq, Ord]

  ||| An UTC offset expressed as a `Duration` as per ISO 8601-2:2019.
  public export
  record OffsetDuration where
    constructor MkOffsetDuration
    sign     : Sign
    duration : Duration

  %runElab derive "OffsetDuration" [Show, Eq, Ord]

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
