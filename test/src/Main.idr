module Main

import Data.Refined
import Data.Refined.Integer

import Hedgehog

import Data.Time

%default total

doubleGen : Gen Double
doubleGen = double (linear (-315576000000) 315576000000)

propNonDestructive : Property
propNonDestructive = property $ do
  x <- forAll doubleGen
  (Duration.toSeconds $ Duration.fromSeconds x) === x

propNormRemains : Property
propNormRemains = property $ do
  x <- forAll doubleGen
  normalise (Duration.fromSeconds x) === (Duration.fromSeconds x)

testUtc : Property
testUtc = property1 $
  (show $ utc 23 59 59.9) === show (MkTime 23 59 59.9 (Just Z))

props : Group
props = MkGroup "Test `Duration`"
  [ ("Prop `toSeconds` and `toSeconds` are non-destructive", propNonDestructive)
  , ("Prop normalise remains", propNormRemains)
  , ("Test UTC", testUtc)
  ]

main : IO ()
main = test [props]
