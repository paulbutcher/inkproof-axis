/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Ticks
import Inkproof.Axis.Label

namespace Inkproof.Axis

/-- The text `b^n` for the integer `n`, with the locale's minus sign for a negative exponent. -/
def powerText (loc : Locale) (base : Nat) (n : Int) : String :=
  String.ofList (Nat.toDigits 10 base ++ '^' :: (if n < 0 then [loc.minus] else []) ++ Nat.toDigits 10 n.natAbs)

/-- `x` as a power of `base` in plain text, 2^24 for 16777216 in base 2, or `none` when it is not one. -/
def powerLabel (loc : Locale) (base : Nat) (x : Float) : Option String :=
  if x.isFinite && 0 < x && 2 ≤ base then
    let n : Int := (logBase base x).round.toInt64.toInt
    if powBase base n == x then some (powerText loc base n) else none
  else none

/-- The `powerLabel` of each tick, or no labels unless every tick is a power of `base`. -/
def powerLabels (loc : Locale) (base : Nat) (ts : List Float) : List String :=
  match ts.mapM (powerLabel loc base) with
  | some ls => ls
  | none => []

end Inkproof.Axis
