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

-- TODO use Seconds instead of Double for more clarity.
public export
Seconds : Type
Seconds = Double

||| A second expressed as a `Double` ranging from `0.0` to `60.0`.
|||
||| `60.0` is used for leap seconds.
public export
record Second where
  constructor MkSecond
  second : Seconds
  {auto 0 valid : Integer.FromTo 0 60 (cast $ floor second)}


public export
refineSecond : Double -> Maybe Second
refineSecond s = case hdec0 {p = Integer.FromTo 0 60} (cast $ floor s) of
  Just0 _  => Just (MkSecond s)
  Nothing0 => Nothing

namespace Second
  %runElab derive "Second" [Show, Eq, Ord]

  ||| Returns a `Second` from the provided `Double`.
  |||
  ||| At the exception of leap seconds, seconds range from `0` and `59`.
  ||| Consequently, any value below or above will get converted to the remaining
  ||| of its modulo `60`.
  |||
  ||| For example:
  |||
  ||| - `70.1` will get converted to `10.1`
  ||| - `(-10)` will get converted to `50.0`
  ||| - `60` will not get converted and will remain `60`
  public export
  fromDouble : Double -> Second
  fromDouble x =
    let
      sec : Integer -> Double
      sec 60 = 60
      sec s  = cast (s `mod` 60) + (x - cast s)
    in
    case refineSecond (sec $ cast x) of
      Just s => s
      -- This case cannot be reached as `sec` will always be
      -- within `0` and `60`.
      Nothing => MkSecond 0

||| At the exception of leap seconds, seconds range from `0` and `59`.
||| Consequently, any result below or above will get converted to the remaining
||| of its modulo `60`.
|||
||| For example:
|||
||| - `70.1` will get converted to `10.1`
||| - `(-10)` will get converted to `50.0`
||| - `60` will get converted to `0.0`
public export
Num Second where
  fromInteger x = Second.fromDouble (cast x)

  (MkSecond s1) + (MkSecond s2) = Second.fromDouble (s1 + s2)

  (MkSecond s1) * (MkSecond s2) = Second.fromDouble (s1 * s2)

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
  %runElab derive "Fraction" [Show]

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

||| Negates the provided value if the `Sign` is `Minus`.
|||
||| Otherwise, returns the original value.
private
applySign : Neg a => Sign -> a -> a
applySign Plus  = id
applySign Minus = negate

namespace Duration

  ||| A time `Duration` in the format PTnHnMnS.sss.
  |||
  ||| Note that each n can be negative, meaning that individual duration units
  ||| can be below `0`.
  ||| This is a per the "composite representation" format described in
  ||| ISO 8601-2:2019.
  public export
  record Duration where
    constructor MkDuration
    hours   : Integer
    minutes : Integer
    seconds : Double

  %runElab derive "Duration" [Show]

  ||| Converts a `Duration` to seconds.
  toSeconds : Duration -> Double
  toSeconds (MkDuration h m s) = cast (3600 * h + 60 * m) + s

  ||| Converts seconds to a `Duration`.
  |||
  ||| The `Duration` is normalised, meaning that seconds above `59` will be
  ||| converted to minutes and minutes above `59` will be converted to hours.
  |||
  ||| This also applies if seconds are negative: seconds below `59` will be
  ||| to minutes and minutes below `59` will be converted to hours.
  fromSeconds : Double -> Duration
  fromSeconds seconds =
    let
      -- `mod` and `div` are implemented in the mathematical form.
      -- This means that for negative numbers, the remaining will
      -- remain the same regardless of the sign of the divisor.
      --
      -- For example, `mod (-10) (-60) == 50`.
      -- In our case we want `-10`. To achieve our goal, we
      -- use an absolute value and negate the end result.
      absSec := abs seconds

      absSecInt : Integer
      absSecInt = cast absSec

      sign : (Eq a, Neg a) => a -> a
      sign x = if seconds < 0 && x /= 0 then negate x else x

      s := sign $ cast (absSecInt `mod` 60) + (absSec - cast absSecInt)
      min := absSecInt `div` 60
      m := sign $ min `mod` 60
      h := sign $ min `div` 60
    in
      MkDuration h m s

  ||| Normalises a `Duration`.
  |||
  ||| Minutes and seconds are between `0` and `59`.
  ||| When below or above, hours and minutes are adjusted accordingly.
  normalise : Duration -> Duration
  normalise = fromSeconds . toSeconds

  ||| Applies a comparison to `Duration`.
  |||
  ||| This prevents code duplication in the implementation
  ||| of the `Eq` and `Ord` interfaces.
  private
  compare : (Double -> Double -> Bool) -> Duration -> Duration -> Bool
  compare op d1 d2 with (toSeconds d1, toSeconds d2)
    _ | (x, y) = op x y

  ||| `Duration`s are converted to seconds before being compared.
  |||
  ||| This means that `Duration`s are equal if they represent the same amount
  ||| of time. This does not imply that they are the same.
  |||
  ||| For example `(MkDuration 0 180 0 0) == (MkDuration 3 0 0 0) = True`.
  ||| Both represent an amount of time of 3 hours.
  Eq Duration where
    (==) = compare (==)

  ||| `Duration`s are converted to seconds before being compared.
  |||
  ||| This is a similar behaviour as described for the `Eq` instance.
  Ord Duration where
    (<) = compare (<)

  ||| For the `(*)` operation, the returned `Duration` is normalised.
  |||
  ||| To the contrary, for the `(+)` operation, each duration unit
  ||| are individually added, meaning that there is no normalisation.
  public export
  Num Duration where

    fromInteger = fromSeconds . cast

    (MkDuration h1 m1 s1) + (MkDuration h2 m2 s2) = MkDuration (h1 + h2) (m1 + m2) (s1 + s2)

    d1 * d2 = fromSeconds (toSeconds d1 * toSeconds d2)

  ||| Note that durations of 0 are always positive.
  public export
  Neg Duration where

    negate (MkDuration h m s) = MkDuration (-h) (-m) (-s)

    (MkDuration h1 m1 s1) - (MkDuration h2 m2 s2) = MkDuration (h1 - h2) (m1 - m2) (s1 - s2)

  ||| `Duration`s get normalised when getting their absolute value.
  public export
  Abs Duration where
    abs = normalise . fromSeconds . abs . toSeconds

  ||| `Duration`s get normalised when being divided.
  public export
  Fractional Duration where
    d1 / d2 = normalise $ fromSeconds $ toSeconds d1 / toSeconds d2

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
  ||| At the time being, only values `0`, `30` and `45` have been used.
  ||| For consistency, the value `15` has been added here.
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
