||| High-level definition of the time library.
module Data.Time

import Data.Refined
import Data.Refined.Integer
import Derive.Prelude
import Derive.Refined

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Private utility functions
--------------------------------------------------------------------------------

private
interface
  (Ord dividendTy, Abs dividendTy, Neg dividendTy, Ord divisorTy, Neg divisorTy)
  => EuclidianDivision dividendTy divisorTy where 

  ||| Similar to `div`.
  eDiv : dividendTy -> divisorTy -> divisorTy

  ||| Similar to `mod`.
  eMod : dividendTy -> divisorTy -> dividendTy

  ||| Combination of the `eDiv` and `eMod` functions.
  |||
  ||| Returns the quotient and remainder as a `Pair`.
  eDivMod : dividendTy -> divisorTy -> (divisorTy, dividendTy)
 
  ||| Integer division truncated toward zero.
  |||
  ||| It behaves the same as `eDiv` when both dividend and divisor are positive
  ||| or negative.
  ||| When either the divisor or the dividend is negative, the returned quotient
  ||| will be rounded toward zero.
  |||
  ||| ```idris example
  ||| (-9) `quot` 4 == 2
  ||| ```
  eQuot : dividendTy -> divisorTy -> divisorTy

  ||| Signed integer remainder.
  |||
  ||| Similar as `eMod`, but with a negative value for negative input.
  eRem : dividendTy -> divisorTy -> dividendTy

  ||| Combination of `eQuot` and `eRem`.
  |||
  ||| Returns the quotient and remainder of a division as a `Pair`.
  eQuotRem : dividendTy -> divisorTy -> (divisorTy, dividendTy)

  eDivMod dividend divisor = (dividend `eDiv` divisor, dividend `eMod` divisor)

  eQuot dividend divisor =
    case (compare dividend 0, compare divisor 0) of
      (LT, GT) => negate (abs dividend `eDiv` divisor)
      _        => dividend `eDiv` divisor

  eRem a b =
    case (compare a 0, compare b 0) of
      (LT, GT) => negate (abs a `eMod` b)
      _ => a `eMod` b

  eQuotRem dividend divisor =
    (dividend `eQuot` divisor, dividend `eRem` divisor)

EuclidianDivision Integer Integer where
  eDiv dividend divisor = div dividend divisor
  eMod a b = mod a b

EuclidianDivision Double Integer where
  eDiv dividend divisor = div (cast dividend) divisor
  eMod a b = let aInt = cast a in cast (mod aInt b) + a - (cast aInt)

||| `True` predicate.
private
data IsTrue : Bool -> Type where
  Yes : IsTrue True

private
HDec0 Bool IsTrue where
  hdec0 False = Nothing0
  hdec0 True = Just0 Yes

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

||| Returns the value after the decimal place.
|||
||| For example:
|||
||| ```idris
||| decimal 10.42 == 0.42
|||
||| decimal (-10.42) == (-0.42)
||| ```
private
decimal : Double -> Double
decimal x =
  if x < 0
  then x - ceiling x
  else x - floor x

--------------------------------------------------------------------------------
-- General types used through the module
--------------------------------------------------------------------------------

||| Type alias for `Seconds` expressed as a `Double`.
public export
Seconds : Type
Seconds = Double

--------------------------------------------------------------------------------
-- Time Duration
--------------------------------------------------------------------------------

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
  public export
  toSeconds : Duration -> Seconds
  toSeconds (MkDuration h m s) = cast (3600 * h + 60 * m) + s

  ||| Converts seconds to a `Duration`.
  |||
  ||| The `Duration` is normalised, meaning that seconds above `59` will be
  ||| converted to minutes and minutes above `59` will be converted to hours.
  |||
  ||| This also applies if seconds are negative: seconds below `59` will be
  ||| converted to negative minutes and minutes below `59` will be converted to
  ||| negative hours.
  public export
  fromSeconds : Seconds -> Duration
  fromSeconds seconds =
    let
      (min, s) := seconds `eQuotRem` 60
      (h, m)   := min `eQuotRem` 60
    in
      MkDuration h m s

  ||| Normalises a `Duration`.
  |||
  ||| Minutes and seconds are between `0` and `59`.
  ||| When below or above, hours and minutes are adjusted accordingly.
  public export
  normalise : Duration -> Duration
  normalise = fromSeconds . toSeconds

  ||| Applies a comparison to `Duration`.
  |||
  ||| This prevents code duplication in the implementation
  ||| of the `Eq` and `Ord` interfaces.
  private
  compare : (Seconds -> Seconds -> Bool) -> Duration -> Duration -> Bool
  compare op d1 d2 with (toSeconds d1, toSeconds d2)
    _ | (x, y) = op x y

  ||| `Duration`s are converted to seconds before being compared.
  |||
  ||| This means that `Duration`s are equal if they represent the same amount
  ||| of time. This does not imply that they are the same.
  |||
  ||| For example `(MkDuration 0 180 0 0) == (MkDuration 3 0 0 0) = True`.
  ||| Both represent an amount of time of 3 hours.
  public export
  Eq Duration where
    (==) = compare (==)

  ||| `Duration`s are converted to seconds before being compared.
  |||
  ||| This is a similar behaviour as described for the `Eq` instance.
  public export
  Ord Duration where
    (<) = compare (<)

  ||| For the `(+)` operation, duration units are individually added.
  ||| This means that there is no normalisation.
  public export
  Num Duration where

    fromInteger = fromSeconds . cast

    (MkDuration h1 m1 s1) + (MkDuration h2 m2 s2) = MkDuration (h1 + h2) (m1 + m2) (s1 + s2)

    d1 * d2 = fromSeconds (toSeconds d1 * toSeconds d2)

  ||| For the `(-)` operation, duration units are individually added.
  ||| This means that there is no normalisation.
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

--------------------------------------------------------------------------------
-- Time Offset
--------------------------------------------------------------------------------

namespace Offset

  ||| Sign of an UTC `Offset` or of an offset `Duration`.
  |||
  ||| `Plus` stands for `+`.
  ||| `Minus` stands for `-`.
  public export
  data Sign = Plus | Minus

  %runElab derive "Sign" [Show, Eq]

  public export
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

  ||| Number of hour of an UTC offset.
  |||
  ||| The range from `0` to `14` covers the existing offsets.
  ||| In theory, more could be added in the future.
  public export
  record Hours where
    constructor MkHours
    hours : Integer
    {auto 0 valid : FromTo 0 14 hours}

  namespace Hours
    %runElab derive "Offset.Hours" [Show, Eq, Ord, RefinedInteger]

  ||| Number of minutes for an UTC offset of a time in complement of an hour.
  |||
  ||| At the time being, only values `0`, `30` and `45` have been used.
  ||| For consistency, the value `15` has been added here.
  public export
  record Minutes where
    constructor MkMinutes
    minutes : Integer
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
  |||
  ||| For the `Offset` to be valid:
  |||
  ||| - the `hours` must range from `0` to `14` (included);
  ||| - the `minutes` must be `0`, `15`, `30`, `45`;
  ||| - if the `sign` is `Minus`, `hours` or `minutes` must not be `0`.
  public export
  record Offset where
    constructor MkOffset
    sign    : Sign
    hours   : Offset.Hours
    minutes : Offset.Minutes
    {auto 0 valid : IsTrue (validOffset sign hours minutes)}

  %runElab derive "Offset" [Show, Eq, Ord]

  ||| Returns `Just` an `Offset` if the provided values are valid.
  |||
  ||| Otherwise returns `Nothing`.
  public export
  maybeOffset : Sign -> (hours : Integer) -> (minutes : Integer) -> Maybe Offset
  maybeOffset sign hours minutes = do
    hours'   <- refineHours hours
    minutes' <- refineMinutes minutes
    case hdec0 {p = IsTrue} (validOffset sign hours' minutes') of
      Just0 _  => Just (MkOffset sign hours' minutes')
      Nothing0 => Nothing

  ||| Converts an `Offset` to a `Duration`.
  public export
  toDuration : Offset -> Duration
  toDuration (MkOffset sign hours minutes) =
    let
      nH : Integer
      nH = cast $ applySign sign  hours.hours

      nM : Integer
      nM := cast $ applySign sign minutes.minutes
    in
    MkDuration nH nM 0

  ||| Converts an `Offset` to `Seconds`.
  public export
  toSeconds : Offset -> Seconds
  toSeconds (MkOffset sign h m) =
    cast $ applySign sign (3600 * h.hours + 60 * m.minutes)

--------------------------------------------------------------------------------
-- Time Zone
--------------------------------------------------------------------------------

namespace TimeZone

  ||| A time zone which can be UTC, an UTC offset or an arbitrary `Duration`.
  public export
  data TimeZone = Z | Offset Offset.Offset | Duration Duration.Duration

  %runElab derive "TimeZone" [Show]

  ||| Converts a `TimeZone` to a `Duration`
  public export
  toDuration : TimeZone -> Duration
  toDuration Z                   = MkDuration 0 0 0
  toDuration (Offset offset)     = toDuration offset
  toDuration (Duration duration) = duration

  ||| Converts a `TimeZone` to `Seconds`.
  public export
  toSeconds : TimeZone -> Seconds
  toSeconds Z                   = 0
  toSeconds (Offset offset)     = toSeconds offset
  toSeconds (Duration duration) = toSeconds duration

  ||| Returns `True` if two `TimeZone`s represent the same amount of time.
  |||
  ||| This means that `True` shall be returned, even if the two `TimeZone`s
  ||| are expressed in different ways (for example as an `Offset` and as
  ||| a `Duration`).
  public export
  Eq TimeZone where
    Z  == Z  = True
    o1 == Z  = toSeconds o1 == 0
    Z  == o2 = 0 == toSeconds o2
    o1 == o2 = toSeconds o1 == toSeconds o2

  ||| Returns `True` if the `TimeZone` represents a lesser amount of time.
  |||
  ||| As for `Eq` the nature of the `TimeZone`s does not matter, only the
  ||| amount of time they represent.
  public export
  Ord TimeZone where
    Z  < Z  = False
    o1 < Z  = toSeconds o1 < 0
    Z  < o2 = 0 < toSeconds o2
    o1 < o2 = toSeconds o1 < toSeconds o2

--------------------------------------------------------------------------------
-- Time
--------------------------------------------------------------------------------

||| An hour ranging from 0 to 23.
public export
record Hour where
  constructor MkHour
  hour : Integer
  {auto 0 valid : FromTo 0 23 hour}

namespace Hour
  %runElab derive "Hour" [Show, Eq, Ord, RefinedInteger]

  ||| Converts an `Hour` to `Seconds`.
  |||
  ||| Each hours represents 3600 seconds.
  public export
  toSeconds : Hour -> Seconds
  toSeconds (MkHour h) = cast $ 3600 * h

||| A minute ranging from 0 to 59.
public export
record Minute where
  constructor MkMinute
  minute : Integer
  {auto 0 valid : FromTo 0 59 minute}

namespace Minute
  %runElab derive "Minute" [Show, Eq, Ord, RefinedInteger]

  ||| Converts a `Minute` to `Seconds`.
  |||
  ||| Each minute represents 60 seconds.
  public export
  toSeconds : Minute -> Seconds
  toSeconds (MkMinute m) = cast $ 60 * m

||| Returns the maximum number of seconds for a given time.
|||
||| This number can be `59` or `60` depending if the provided
||| time (in the form of `Hour`, `Minute` and a potential `Offset`)
||| could potentially have a leap second or not.
public export
maxSeconds : Hour -> Minute -> Maybe TimeZone -> Integer
maxSeconds _  14 Nothing   = 60
maxSeconds _  29 Nothing   = 60
maxSeconds _  44 Nothing   = 60
maxSeconds _  59 Nothing   = 60
maxSeconds h  m  (Just tz) =
  if ((cast $ toSeconds h + toSeconds m + toSeconds tz) + 60) `mod` 86400 == 0
  then 60
  else 59
maxSeconds _   _ _         = 59

||| An ISO 8601 time.
|||
||| If the value of `timeZone` is `Nothing`, then the `Time` is considered as a
||| local time.
|||
||| For a `Time` to be valid:
|||
||| - the `hour` must range from `0` to `23` (included);
||| - the `minute` must range from `0` to `59` (included);
||| - unless if it is a leap second, the `second` must range
|||   from `0` to `59` (included);
||| - if it is a leap second, the `second` can range up to `60` (included).
|||
||| For leap second to be considered as valid:
|||
||| - if the `timeZone` is `Nothing` (local time), the `minute` must be
|||   `14`, `29`, `44` or `59`. This is considering the fact that leap seconds
|||   are added at 23:59 UTC time and the smallest unit used in practice for
|||   time offsets is 15 minutes.
||| - if the `timeZone` is `Just Z` (UTC), the `hour` must be `23` and the
|||   `minute` must be `59`.
||| - if the `timeZone` is `Just (Offset Offset.Offset)` or
|||   `Just (Duration Duration.Duration)`, the computation of this offset to the
|||   time must result to `23` `hour` and `59` `minute` (23:59 UTC).
public export
record Time where
  constructor MkTime
  hour     : Hour
  minute   : Minute
  second   : Double
  timeZone : Maybe TimeZone
  {auto 0 valid: FromTo 0 (maxSeconds hour minute timeZone) (cast second)}

%runElab derive "Time" [Show]

||| Returns `Just` a `Time` if the provided parameters are valid.
|||
||| Otherwise, returns `Nothing`.
||| See documentation of the `Time` type for details on what are the valid
||| parameters.
public export
maybeTime :
  (hour : Integer) ->
  (minute : Integer) ->
  Seconds ->
  Maybe TimeZone ->
  Maybe Time
maybeTime hour minute second timeZone = do
  h <- refineHour hour
  m <- refineMinute minute
  case hdec0 {p = FromTo 0 (maxSeconds h m timeZone)} (cast second) of
    Just0 _  => Just (MkTime h m second timeZone)
    Nothing0 => Nothing

||| Converts a `Time` to `Seconds`.
public export
toSeconds : Time -> Seconds
toSeconds (MkTime h m s t) =
  let
    -- In case of a lead second, remove it and then put it back.
    -- This way the modulo 86400 calculation remains coherent.
    leap : Seconds
    leap = if s == 60 then 1 else 0

    rawSec : Seconds
    rawSec= toSeconds h + toSeconds m + s + (offsetSec t) - leap

    intSec : Integer
    intSec = cast rawSec
  in
  (cast $ intSec `mod` 86400) + decimal rawSec + leap
  where
    offsetSec : (Maybe TimeZone) -> Seconds
    offsetSec (Just o)  = TimeZone.toSeconds o
    offsetSec (Nothing) = 0

||| Convert `Seconds` to a local `Time`.
|||
||| As `Time` is clipped to `86400` seconds a day,
||| values above will loop.
||| Also, values below `0` will loop back.
||| The below examples returns `Time`s representing:
|||
||| - `fromSeconds 86410`: 00:00:10;
||| - `fromSeconds (-10)`: 23:59:50.
public export
fromSeconds : Seconds -> Time
fromSeconds sec =
  let
    secNorm   := sec `eMod` 86400
    (min, s)  := secNorm `eDivMod` 60
    (hour, m) := min `eDivMod` 60
    h         := hour `eMod` (the Integer 24)
  in
  case maybeTime h m s Nothing of
    Just time => time
    -- This case cannot be reached as the number of seconds is normalised.
    Nothing   => MkTime 0 0 0 Nothing

||| Returns `True` if the two `Time`s represent a same amount of time.
|||
||| The way they are built (with or without `TimeZone`) is irrelevant.
public export
Eq Time where
  t1 == t2 = toSeconds t1 == toSeconds t2

||| Returns `True` if the first `Time` represents a lesser amount of time.
public export
Ord Time where
  t1 < t2 = toSeconds t1 < toSeconds t2

||| Returns an UTC `Time` (Coordinated Universal Time).
|||
||| A leap second (a value of `60` for the second) is only accepted
||| for hour `23`, minute `59`:
|||
||| ```Idris
||| utc 23 59 60
||| ```
public export
utc :
  (hour : Hour) ->
  (minute : Minute) ->
  (second : Seconds) ->
  {auto 0 valid: FromTo 0 (maxSeconds hour minute (Just Z)) (cast second)} ->
  Time
utc hour minute second = MkTime hour minute second (Just Z)

||| Returns a local `Time`.
|||
||| A leap second (a value of `60` for the second) is only accepted
||| for minutes `14`, `29`, `44` and `59`.
||| For example, the below value is fine:
|||
||| ```idris
||| utc 14 29 60
||| ```
public export
local :
  (hour : Hour) ->
  (minute : Minute) ->
  (second : Seconds) ->
  {auto 0 valid: FromTo 0 (maxSeconds hour minute Nothing) (cast second)} ->
  Time
local hour minute second = MkTime hour minute second Nothing

||| Returns a `Time` with an offset.
|||
||| A leap second (a value of `60` for the second) is only accepted
||| if the resulting UTC time is `23` hour, `59` minute.
public export
offsetTime :
  (hour : Hour) ->
  (minute : Minute) ->
  (second : Seconds) ->
  (offset : Offset) ->
  { auto 0 valid:
    FromTo
      0
      (maxSeconds hour minute (Just $ Offset offset))
      (cast second)
  } ->
  Time
offsetTime hour minute second offset =
  MkTime hour minute second (Just $ Offset offset)

||| Returns a `Time` with an offset provided the provided values are valid.
|||
||| A leap second (a value of `60` for the second) is only accepted
||| if the resulting UTC time is `23` hour, `59` minute.
public export
maybeOffsetTime :
  (hour : Integer) ->
  (minute : Integer) ->
  Seconds ->
  Offset ->
  Maybe Time
maybeOffsetTime hour minute second offset =
  maybeTime hour minute second (Just $ Offset offset)

||| A `Time` with an offset expressed as a `Duration`.
|||
||| A leap second (a value of `60` for the second) is only accepted
||| if the resulting UTC time is `23` hour, `59` minute.
public export
offsetDurationTime :
  (hour : Hour) ->
  (minute : Minute) ->
  (second : Seconds) ->
  (duration : Duration) ->
  { auto 0 valid:
    FromTo
      0
      (maxSeconds hour minute (Just $ TimeZone.Duration $ duration))
      (cast second)
  } ->
  Time
offsetDurationTime hour minute second duration =
  MkTime hour minute second (Just $ TimeZone.Duration $ duration)

||| Returns a `Time` from a `Duration`.
|||
||| Time units will be clipped to their maximal values.
||| `23` for `Hour`, `59` for `Minute` and `59` for `Second`.
public export
fromDuration : Duration -> Maybe Time
fromDuration duration with (normalise duration)
  _ | MkDuration nH nM nSS =
    maybeTime (cast nH) (cast nM) (cast nSS) Nothing

||| Returns the `Duration` between two `Time`s.
|||
||| You may use this function qualified (`Time.diff`) for more clarity.
public export
diff : Time -> Time -> Duration
diff t1 t2 = fromSeconds (toSeconds t1 - toSeconds t2)

||| Adds a `Duration` to a `Time`.
|||
||| If any, the `Offset` remains untouched.
public export
addDuration : Time -> Duration -> Time
addDuration time duration =
  let
    durationSec := toSeconds duration
  in
  -- If the duration is very small, leap second must be preserved.
  if decimal time.second + durationSec  < 1
  then case maybeTime
    time.hour.hour
    time.minute.minute
    (time.second + durationSec)
    time.timeZone of
    Just t  => t
    -- Cannot be reached as the initial time was valid
    -- and there is no second unit change.
    Nothing => MkTime 0 0 0 Nothing
  else
    let
      t := fromSeconds (toSeconds time + toSeconds duration)
    in
    case maybeTime t.hour.hour t.minute.minute t.second time.timeZone of
      Just t  => t
      -- Cannot be reached as `fromSeconds` does not generate `Time`s
      -- with leap second.
      Nothing => MkTime 0 0 0 Nothing
