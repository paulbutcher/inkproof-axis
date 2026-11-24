/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.PowerLabel
import Inkproof.Axis.Proofs.Decade

namespace Inkproof.Axis.Proofs

theorem logTicks_eq (lo hi : Float) (target : Nat) : logTicks lo hi target = logTicksIn 10 lo hi target := rfl

theorem logTicksAt_eq (m : LogMultiples) (lo hi : Float) (target : Nat) :
    logTicksAt m lo hi target = logTicksAtIn 10 m lo hi target := rfl

theorem logMinorTicks_eq (m : LogMultiples) (lo hi : Float) (target : Nat) :
    logMinorTicks m lo hi target = logMinorTicksIn 10 m lo hi target := rfl

theorem logTicksIn_of_base_lt_two (base : Nat) (h : base < 2) (lo hi : Float) (target : Nat) :
    logTicksIn base lo hi target = [] := by
  unfold logTicksIn
  split <;> simp [h]

theorem mantissas_eq (m : LogMultiples) : m.mantissas = m.mantissasIn 10 := rfl

theorem mantissasIn_decades (base : Nat) : LogMultiples.decades.mantissasIn base = [1] := rfl

theorem mantissasIn_oneTwoFive (base : Nat) :
    LogMultiples.oneTwoFive.mantissasIn base = [1, 2, 5].filter (· < base) := rfl

theorem mantissasIn_integers (base : Nat) :
    LogMultiples.integers.mantissasIn base = (List.range (base - 1)).map (· + 1) := rfl

theorem mantissasIn_two_integers : LogMultiples.integers.mantissasIn 2 = [1] := by decide

theorem mantissasIn_ten_integers : LogMultiples.integers.mantissasIn 10 = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide

/-- A minor tick is one of the integer-multiple ticks that the labelled ticks lack. Its being strictly ascending within the range follows from the integer-multiple ticks' being so, which is checked at run time and tested, as the Float entry points are not proved. -/
theorem mem_logMinorTicksIn (base : Nat) (m : LogMultiples) (lo hi : Float) (target : Nat) (t : Float) :
    t ∈ logMinorTicksIn base m lo hi target ↔
      t ∈ logTicksAtIn base .integers lo hi target ∧ (logTicksAtIn base m lo hi target).contains t = false := by
  simp [logMinorTicksIn]

theorem logMinorTicksIn_decades (base : Nat) (lo hi : Float) (target : Nat) :
    logMinorTicksIn base .decades lo hi target =
      (logTicksAtIn base .integers lo hi target).filter fun t => !(logTicksIn base lo hi target).contains t := rfl

theorem powerText_eq (loc : Locale) (base : Nat) (n : Int) :
    powerText loc base n =
      String.ofList (Nat.toDigits 10 base ++ '^' :: (if n < 0 then [loc.minus] else []) ++ Nat.toDigits 10 n.natAbs) := rfl

theorem powerText_en_two_24 : powerText Locale.en 2 24 = "2^24" := by decide

theorem powerText_en_ten_neg_3 : powerText Locale.en 10 (-3) = "10^-3" := by decide

theorem powerLabel_spec (loc : Locale) (base : Nat) (x : Float) (s : String)
    (h : powerLabel loc base x = some s) :
    ∃ n : Int, powBase base n == x ∧ s = powerText loc base n := by
  unfold powerLabel at h
  split at h
  · dsimp only at h
    split at h
    · injection h with h
      exact ⟨_, ‹_›, h.symm⟩
    · simp at h
  · simp at h

theorem powerLabels_of_mapM (loc : Locale) (base : Nat) (ts : List Float) (ls : List String)
    (h : ts.mapM (powerLabel loc base) = some ls) : powerLabels loc base ts = ls := by
  simp [powerLabels, h]

theorem powerLabels_of_none (loc : Locale) (base : Nat) (ts : List Float)
    (h : ts.mapM (powerLabel loc base) = none) : powerLabels loc base ts = [] := by
  simp [powerLabels, h]

end Inkproof.Axis.Proofs
