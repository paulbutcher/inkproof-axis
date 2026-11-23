/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.TickLabels

namespace Inkproof.Axis.Proofs

theorem floatLabel_eq (loc : Locale) (p : Nat) (x : Float) :
    floatLabel loc p x = String.ofList (formatChars loc p
      ((x * (10 ^ p : Nat).toFloat + (Float.ofInt 1) / (Float.ofInt 2)).floor.toInt64.toInt)) := rfl

theorem formatAt_eq (fmt : NumberFormat) (p : Nat) (x : Float) :
    fmt.formatAt p x = floatLabel fmt.locale p (NumberFormat.scaleDown (fmt.magnitude x) x) ++
      fmt.suffix (fmt.magnitude x) := rfl

theorem magnitude_of_compact_nil (fmt : NumberFormat) (h : fmt.compact = []) (x : Float) :
    fmt.magnitude x = 0 := by
  simp [NumberFormat.magnitude, h]

theorem magnitude_eq (fmt : NumberFormat) (x : Float) :
    fmt.magnitude x = (List.range fmt.compact.length).countP
      fun i => ((1000 ^ (i + 1) : Nat).toFloat ≤ x.abs) := rfl

theorem scaleDown_eq (j : Nat) (x : Float) : NumberFormat.scaleDown j x = x / (1000 ^ j : Nat).toFloat := rfl

theorem formatAll_of_precision (fmt : NumberFormat) (p : Nat) (h : fmt.precision = some p)
    (xs : List Float) : fmt.formatAll xs = [] ∨ fmt.formatAll xs = xs.map (fmt.formatAt p) := by
  unfold NumberFormat.formatAll
  simp only [h]
  split <;> simp

theorem suffix_zero (fmt : NumberFormat) : fmt.suffix 0 = "" := rfl

theorem suffix_succ (fmt : NumberFormat) (j : Nat) : fmt.suffix (j + 1) = fmt.compact.getD j "" := rfl

theorem format_eq (fmt : NumberFormat) (x : Float) : fmt.format x = (fmt.formatAll [x]).head? := rfl

theorem tickLabels_eq (loc : Locale) (ts : List Float) :
    tickLabels loc ts = ({ locale := loc : NumberFormat }).formatAll ts := rfl

end Inkproof.Axis.Proofs
