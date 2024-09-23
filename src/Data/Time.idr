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

||| An `Integer` with the constraints of a natural number.
public export
record Natural where
  constructor MkNatural
  n : Integer
  {auto 0 valid : From 0 n}

namespace Natural
  %runElab derive "Natural" [Show, Eq, Ord, RefinedInteger]

||| Integers lower than `0` will be converted to `0`.
public export
Num Natural where

  fromInteger x = case refineNatural x of
    Just n  => n
    Nothing => 0

  (MkNatural n1) + (MkNatural n2) = case refineNatural (n1 + n2) of
    Just n  => n
    -- This case is never reached as natural numbers not below 0.
    Nothing => 0

  (MkNatural n1) * (MkNatural n2) = case refineNatural (n1 * n2) of
    Just n  => n
    -- This case is never reached as natural numbers are not below 0.
    Nothing => 0

||| As natural numbers cannot be negative, results are capped at 0.
|||
||| `negate` always returns `0`.
||| `(-)` returns `0` if the result of the substraction would be below 0.
public export
Neg Natural where
  negate _ = MkNatural 0

  (MkNatural n1) - (MkNatural n2) = case refineNatural (n1 - n2) of
    Just n  => n
    Nothing => 0

||| `Double`s part of the right half-open unit interval [0,1).
|||
||| Only values from 0 (included) and lower than 1 are accepted.
public export
record RightHalfOpenUI where
  constructor MkRightHalfOpenUI
  x : Double
  -- TODO find a way to use `Equal` rather than `FromTo`.
  {auto 0 valid : Integer.FromTo 0 0 (cast $ floor x)}

namespace RightHalfOpenUI
  %runElab derive "RightHalfOpenUI" [Show, Eq, Ord]

public export
refineRightHalfOpenUI : Double -> Maybe RightHalfOpenUI
refineRightHalfOpenUI x = case hdec0 {p = Integer.FromTo 0 0} (cast $ floor x) of
  Just0 _  => Just (MkRightHalfOpenUI x)
  Nothing0 => Nothing

||| Values outside bounds are converted back to `0`.
|||
||| `fromInteger` always returns `0`.
||| `(+)` returns a value different than `0` only if the result
||| is greater than `0` and below `1`.
|||
||| On the other hand, no returned values are converted for `(*)`.
||| Multiplication of values within the unit interval will always
||| result in a value within that same interval.
public export
Num RightHalfOpenUI where

  fromInteger _ = MkRightHalfOpenUI 0

  (MkRightHalfOpenUI d1) + (MkRightHalfOpenUI d2) =
    case refineRightHalfOpenUI (d1 + d2) of
      Just d  => d
      Nothing => 0

  (MkRightHalfOpenUI d1) * (MkRightHalfOpenUI d2) =
    case refineRightHalfOpenUI (d1 * d2) of
      Just d  => d
      -- This case is never reached as multiplication of values of this interval
      -- is always within the interval.
      Nothing => 0

||| As the unit interval cannot be negative, results are capped at 0.
|||
||| `negate` always returns `0`.
||| `(-)` returns `0` if the result of the substraction would be below 0.
public export
Neg RightHalfOpenUI where

  negate _ = 0

  (MkRightHalfOpenUI d1) - (MkRightHalfOpenUI d2) =
    case refineRightHalfOpenUI (d1 - d2) of
      Just d => d
      Nothing => 0

namespace Duration

  ||| A time `Duration` as per ISO 8601 PTnHnMnS.sss format.
  public export
  record Duration where
    constructor MkDuration
    ||| `Plus` (standing for the "+" sign) or `Minus` (standing for the "−" sign).
    sign     : Sign

    hours    : Natural
    minutes  : Natural
    seconds  : Natural

    ||| Fractions of a second of a time `Duration`.
    |||
    ||| This number is what comes after `,` or `.`.
    ||| For example, if you provide `0.25`, then the fraction part is `,25`
    ||| (or `.25`).
    fraction : RightHalfOpenUI

  %runElab derive "Duration" [Show, Eq, Ord]

  refineDuration :
       Sign
    -> (hours : Integer)
    -> (minutes : Integer)
    -> (seconds : Integer)
    -> (fraction : Double)
    -> Maybe Duration
  refineDuration sign hours minutes seconds fraction = do
    hours' <- refineNatural hours
    minutes' <- refineNatural minutes
    seconds' <- refineNatural seconds
    fraction <- refineRightHalfOpenUI fraction
    pure $ MkDuration sign hours' minutes' seconds' fraction

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
