/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Label

namespace Inkproof.Axis

/-- How numbers are written: the locale's separators, the decimals (`none` chooses the fewest that show every value and keep neighbours distinct), and the suffixes for 10 ^ 3, 10 ^ 6 and so on (empty for no compact notation). -/
structure NumberFormat where
  locale : Locale := Locale.en
  precision : Option Nat := none
  compact : List String := []

namespace NumberFormat

/-- Compact suffixes for thousands, millions, billions and trillions. -/
def short : List String := ["k", "M", "B", "T"]

/-- The number of thousands-steps `x` is scaled down by: the compact suffixes whose unit does not exceed `|x|`. -/
def magnitude (fmt : NumberFormat) (x : Float) : Nat :=
  (List.range fmt.compact.length).countP fun i => ((1000 ^ (i + 1) : Nat).toFloat ≤ x.abs)

/-- The suffix for a scaling of `j` thousands-steps. -/
def suffix (fmt : NumberFormat) : Nat → String
  | 0 => ""
  | j + 1 => fmt.compact.getD j ""

/-- `x` in units of `1000 ^ j`. -/
def scaleDown (j : Nat) (x : Float) : Float := x / (1000 ^ j : Nat).toFloat

end NumberFormat

/-- The label of a float at `p` decimals, rounded to nearest. -/
def floatLabel (loc : Locale) (p : Nat) (x : Float) : String :=
  letI : IntCast Float := ⟨Float.ofInt⟩
  letI : NatCast Float := ⟨Nat.toFloat⟩
  label loc (fun y => y.floor.toInt64.toInt) p x

/-- The text of `x` at `p` decimals, in the compact unit its size selects. -/
def NumberFormat.formatAt (fmt : NumberFormat) (p : Nat) (x : Float) : String :=
  let j := fmt.magnitude x
  floatLabel fmt.locale p (NumberFormat.scaleDown j x) ++ fmt.suffix j

private def maxPrecision : Nat := 15

/-- Whether `v` is, to float noise, a whole number of units of `10 ^ -p`, small enough for the rounding to be exact. -/
private def exactAt (p : Nat) (v : Float) : Bool :=
  let y := v * Float.pow 10 p.toFloat
  v.isFinite && y.abs < 4503599627370496 && (y - y.round).abs ≤ 1e-9 * (1 + y.abs)

private def roundsAt (p : Nat) (v : Float) : Bool :=
  v.isFinite && (v * Float.pow 10 p.toFloat).abs < 4503599627370496

/-- The text of each value. A fixed precision rounds every value to it, and gives nothing if one is not finite or too large. Otherwise the fewest decimals up to 15 that show every value exactly and keep adjacent texts distinct are used, and nothing is given if none does. Only integer arithmetic is printed, so the result is the same on every platform. -/
def NumberFormat.formatAll (fmt : NumberFormat) (xs : List Float) : List String :=
  let scaled := xs.map fun x => NumberFormat.scaleDown (fmt.magnitude x) x
  let textsAt (p : Nat) := xs.map (fmt.formatAt p)
  match fmt.precision with
  | some p => if scaled.all (roundsAt p) then textsAt p else []
  | none =>
    match (List.range (maxPrecision + 1)).find? fun p =>
        scaled.all (exactAt p) && ((textsAt p).zip (textsAt p).tail).all fun (a, b) => a != b with
    | some p => textsAt p
    | none => []

/-- The text of one value, or `none` when it cannot be written (not finite, or too large or too fine for a float to carry). -/
def NumberFormat.format (fmt : NumberFormat) (x : Float) : Option String :=
  (fmt.formatAll [x]).head?

end Inkproof.Axis
