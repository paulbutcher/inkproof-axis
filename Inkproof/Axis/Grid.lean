/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

universe u

namespace Inkproof.Axis

/-- The integer multiples `(first + i) * step` for `i < count`: the shape every tick list takes, so that spacing and order follow from `step`. -/
structure Grid (α : Type u) where
  step : α
  first : Int
  count : Nat

namespace Grid

def index {α : Type u} (g : Grid α) (i : Nat) : Int := g.first + i

def value {α : Type u} [IntCast α] [Mul α] (g : Grid α) (i : Nat) : α := (g.index i : α) * g.step

def values {α : Type u} [IntCast α] [Mul α] (g : Grid α) : List α := (List.range g.count).map g.value

/-- The multiples of `step` in `[lo, hi]`, given a floor function `fl`. Empty when the interval holds none, in particular when `hi < lo`. -/
def cover {α : Type u} [IntCast α] [Neg α] [Div α] (fl : α → Int) (lo hi step : α) : Grid α :=
  let a := -fl (-(lo / step))
  let b := fl (hi / step)
  { step, first := a, count := (b - a + 1).toNat }

end Grid

/-- Whether a list is strictly increasing and lies within `[lo, hi]`. -/
def Ticks.Valid {α : Type u} [LE α] [LT α] [DecidableLE α] [DecidableLT α] (lo hi : α) : List α → Bool
  | [] => true
  | [x] => decide (lo ≤ x) && decide (x ≤ hi)
  | x :: y :: rest => decide (lo ≤ x) && decide (x < y) && Ticks.Valid lo hi (y :: rest)

end Inkproof.Axis
