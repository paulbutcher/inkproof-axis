/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

universe u

namespace Inkproof.Axis

/-- The category indices below `n` that lie in `[lo, hi]` and are multiples of `stride`, ascending. Band `i` is at position `i`. Empty when `stride` is zero. -/
def categoricalTicks {α : Type u} [IntCast α] [Neg α] (fl : α → Int) (n : Nat) (lo hi : α) (stride : Nat) : List Nat :=
  let lo' := max (-fl (-lo)) 0
  let hi' := min (fl hi) ((n : Int) - 1)
  let s : Int := stride
  let j0 := (lo' - 1) / s + 1
  let j1 := hi' / s
  (List.range (j1 - j0 + 1).toNat).map fun (k : Nat) => ((j0 + (k : Int)) * s).toNat

end Inkproof.Axis
