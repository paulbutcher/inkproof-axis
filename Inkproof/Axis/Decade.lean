/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Grid

universe u

namespace Inkproof.Axis

/-- The integers that are multiples of `stride` and lie in `[lg lo, lg hi]`, ascending: the exponents of the ticks of a log scale. -/
def decadeExponents {α : Type u} [IntCast α] [NatCast α] [Neg α] [Div α] (fl : α → Int) (lg : α → α) (lo hi : α) (stride : Nat) : List Int :=
  let g := Grid.cover fl (lg lo) (lg hi) (stride : α)
  (List.range g.count).map fun i => g.index i * stride

/-- The powers `pw e` of the exponents of `decadeExponents`. Consecutive ticks are `stride` apart in the exponent, so evenly spaced on a log scale. -/
def decadeTicks {α : Type u} [IntCast α] [NatCast α] [Neg α] [Div α] (fl : α → Int) (lg : α → α) (pw : Int → α) (lo hi : α) (stride : Nat) : List α :=
  (decadeExponents fl lg lo hi stride).map pw

/-- The products `m * pw e` of each multiple `ms` and each exponent `e` from `e0` to `e1`, in exponent then multiple order, kept where they lie in `[lo, hi]`. -/
def multipleTicks {α : Type u} [Mul α] [LE α] [LT α] [DecidableLE α] (pw : Int → α) (ms : List α) (lo hi : α) (e0 e1 : Int) : List α :=
  ((List.range (e1 - e0 + 1).toNat).flatMap fun (i : Nat) => ms.map fun m => m * pw (e0 + (i : Int))).filter fun t => decide (lo ≤ t) && decide (t ≤ hi)

end Inkproof.Axis
