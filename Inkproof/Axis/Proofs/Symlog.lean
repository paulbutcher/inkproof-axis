/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Ticks

namespace Inkproof.Axis.Proofs

theorem mirrorAboutZero_eq {α : Type} [Neg α] [OfNat α 0] (ps : List α) :
    mirrorAboutZero ps = (ps.map (-·)).reverse ++ 0 :: ps := rfl

theorem symlogTicks_eq (lo hi linthresh : Float) (target : Nat) (a b : Float)
    (h : ordered lo hi = some (a, b)) :
    symlogTicks lo hi linthresh target =
      (mirrorAboutZero (logTicks linthresh (max (-a) b) target)).filter fun t => a ≤ t && t ≤ b := by
  simp [symlogTicks, h]

end Inkproof.Axis.Proofs
