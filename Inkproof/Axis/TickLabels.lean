/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Label

namespace Inkproof.Axis

private def floorInt (x : Float) : Int := x.floor.toInt64.toInt

private def maxPrecision : Nat := 15

/-- Whether every tick is, to float noise, a whole number of units of `10 ^ -p`, small enough for `floorInt` to be exact. -/
private def exactAt (p : Nat) (ts : List Float) : Bool :=
  ts.all fun t =>
    let y := t * Float.pow 10 p.toFloat
    t.isFinite && y.abs < 4503599627370496 && (y - y.round).abs ≤ 1e-9 * (1 + y.abs)

/-- Labels for ticks at the fewest decimals that show every tick and keep adjacent labels distinct, or none when no precision up to 15 decimals does (ticks too fine or too large for a float to carry). Only integer arithmetic is printed, so the result is the same on every platform. -/
def tickLabels (loc : Locale) (ts : List Float) : List String :=
  letI : IntCast Float := ⟨Float.ofInt⟩
  letI : NatCast Float := ⟨Nat.toFloat⟩
  let labelsAt (p : Nat) := ts.map (label loc floorInt p)
  match (List.range (maxPrecision + 1)).find? fun p =>
      exactAt p ts && ((labelsAt p).zip (labelsAt p).tail).all fun (a, b) => a != b with
  | some p => labelsAt p
  | none => []

end Inkproof.Axis
