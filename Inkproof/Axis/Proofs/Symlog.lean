/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Ticks
import Inkproof.Axis.Scales

namespace Inkproof.Axis.Proofs

theorem mirrorAboutZero_eq {α : Type} [Neg α] [OfNat α 0] (ps : List α) :
    mirrorAboutZero ps = (ps.map (-·)).reverse ++ 0 :: ps := rfl

theorem symlogTicks_eq (lo hi linthresh : Float) (target : Nat) (a b : Float)
    (h : ordered lo hi = some (a, b)) :
    symlogTicks lo hi linthresh target =
      (mirrorAboutZero (logTicks linthresh (max (-a) b) target)).filter fun t => a ≤ t && t ≤ b := by
  simp [symlogTicks, h]

theorem logTicksAt_decades (lo hi : Float) (target : Nat) :
    logTicksAt .decades lo hi target = logTicks lo hi target := rfl

theorem LogMultiples.mantissas_decades : LogMultiples.decades.mantissas = [1] := rfl

theorem LogMultiples.mantissas_oneTwoFive : LogMultiples.oneTwoFive.mantissas = [1, 2, 5] := rfl

theorem LogMultiples.mantissas_integers : LogMultiples.integers.mantissas = [1, 2, 3, 4, 5, 6, 7, 8, 9] := rfl

theorem logScaleTicksAt_eq (m : LogMultiples) (s : Inkproof.Scale.Log Float) (target : Nat) :
    logScaleTicksAt m s target = logTicksAt m s.domainStart s.domainEnd target := rfl

/- The other multiples are the Float entry point's `multipleTicks` over a window of exponents, checked with `Ticks.Valid` and replaced by `linearTicks` or `logTicks` otherwise, so the entry point is the `if` chain in `logTicksAt`; the proved properties are those of `multipleTicks` (`multipleTicks_valid`, `mem_multipleTicks`). A case theorem over the chain did not close in a few attempts, as `floorInt` is private and the chain's `Valid` test makes each branch's statement differ. -/

end Inkproof.Axis.Proofs
