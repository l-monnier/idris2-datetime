||| High-level definition of the time library.
module Data.Time

import Data.Refined
import Data.Refined.Integer
import Derive.Prelude
import Derive.Refined

%default total
%language ElabReflection

||| Type alias for `Seconds` expressed as a `Double`.
public export
Seconds : Type
Seconds = Double

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
  toSeconds : Minute -> Seconds
  toSeconds (MkMinute m) = cast $ 60 * m

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
  toSeconds : Duration -> Seconds
  toSeconds (MkDuration h m s) = cast (3600 * h + 60 * m) + s

  ||| Converts seconds to a `Duration`.
  |||
  ||| The `Duration` is normalised, meaning that seconds above `59` will be
  ||| converted to minutes and minutes above `59` will be converted to hours.
  |||
  ||| This also applies if seconds are negative: seconds below `59` will be
  ||| to minutes and minutes below `59` will be converted to hours.
  fromSeconds : Seconds -> Duration
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
  Eq Duration where
    (==) = compare (==)

  ||| `Duration`s are converted to seconds before being compared.
  |||
  ||| This is a similar behaviour as described for the `Eq` instance.
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

namespace Offset

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

  ||| `True` predicate.
  private
  data IsTrue : Bool -> Type where
    Yes : IsTrue True

  private
  HDec0 Bool IsTrue where
    hdec0 False = Nothing0
    hdec0 True = Just0 Yes

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

namespace TimeZone

  ||| A time zone which can be UTC, an UTC offset or an arbitrary `Duration`.
  public export
  data TimeZone = Z | Offset Offset.Offset | Duration Duration.Duration

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

||| Returns the maximum number of seconds for a given time.
|||
||| This number can be `59` or `60` depending if the provided
||| time (in the form of `Hour`, `Minute` and a potential `Offset`)
||| could potentially have a leap second or not.
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
  (cast $ intSec `mod` 86400) + (rawSec - cast intSec) + leap
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
    secInt : Integer
    secInt = cast sec

    secNorm := secInt `mod` 86400

    fraction := sec - (cast secInt)

    hour := secNorm `div` 3600
    minute := (secNorm - (hour * 3600)) `div` 60
    second := secNorm - (hour * 3600) - (minute * 60)
  in
  case maybeTime hour minute (cast second + fraction) Nothing of
    Just time => time
    -- This case cannot be reached as the number of seconds is normalised.
    Nothing   => MkTime 0 0 0 Nothing

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
||| a leap second (a value of `60` for the second) is only accepted
||| if the resulting UTC time is `23` hour, `59` minute.
public export
offsetTime :
  (hour : Hour) ->
  (minute : Minute) ->
  (second : Seconds) ->
  (offset : Offset) ->
  {auto 0 valid: FromTo 0 (maxSeconds hour minute (Just $ Offset offset)) (cast second)} ->
  Time
offsetTime hour minute second offset =
  MkTime hour minute second (Just $ Offset offset)

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

namespace Duration

  ||| Converts a `Duration` to a `Time`
  |||
  ||| Time units will be clipped to their maximal values.
  ||| `23` for `Hour`, `59` for `Minute` and `59` for `Second`.
  public export
  toTime : Duration -> Maybe Time
  toTime duration with (normalise duration)
    _ | MkDuration nH nM nSS =
      maybeTime (cast nH) (cast nM) (cast nSS) Nothing
