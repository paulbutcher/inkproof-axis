/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Decade
import Inkproof.Axis.Proofs.Grid

universe u

namespace Inkproof.Axis.Proofs

open Lean.Grind

attribute [local instance] Ring.intCast Semiring.natCast

theorem decadeExponents_spacing {α : Type u} [IntCast α] [NatCast α] [Neg α] [Div α] (fl : α → Int)
    (lg : α → α) (lo hi : α) (stride : Nat) (i : Nat)
    (h : i + 1 < (decadeExponents fl lg lo hi stride).length) :
    (decadeExponents fl lg lo hi stride)[i + 1] = (decadeExponents fl lg lo hi stride)[i] + stride := by
  simp only [decadeExponents, List.getElem_map, List.getElem_range, Grid.index]
  rw [Int.add_mul, Int.add_mul]; simp [Int.add_mul]; omega

variable {α : Type u} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

/-- Given a floor function, a logarithm and a power that agree at the ends of `[lo, hi]` in the sense of `hlo` and `hhi`, and a strictly increasing power, the decade ticks lie within the interval and are strictly increasing. -/
theorem decadeTicks_valid [DecidableLE α] [DecidableLT α] {fl : α → Int} (hfl : IsFloor fl)
    {lg : α → α} {pw : Int → α} {lo hi : α} {stride : Nat} (hs : 0 < stride)
    (hmono : ∀ a b : Int, a < b → pw a < pw b)
    (hlo : ∀ e : Int, lg lo ≤ Int.cast e → lo ≤ pw e)
    (hhi : ∀ e : Int, Int.cast e ≤ lg hi → pw e ≤ hi) :
    Ticks.Valid lo hi (decadeTicks fl lg pw lo hi stride) = true := by
  obtain ⟨m, rfl⟩ : ∃ m, stride = m + 1 := ⟨stride - 1, by omega⟩
  have hst : 0 < (Nat.cast (m + 1) : α) := natCast_pos m
  have hcast : ∀ i, (Int.cast ((Grid.cover fl (lg lo) (lg hi) (Nat.cast (m + 1) : α)).index i
      * ((m + 1 : Nat) : Int)) : α) = (Grid.cover fl (lg lo) (lg hi) (Nat.cast (m + 1) : α)).value i := by
    intro i
    simp only [Grid.value, Ring.intCast_mul, Ring.intCast_natCast]
    rfl
  unfold decadeTicks decadeExponents
  rw [List.map_map, List.range_eq_range']
  cases hc : (Grid.cover fl (lg lo) (lg hi) (Nat.cast (m + 1) : α)).count with
  | zero => simp [Ticks.Valid]
  | succ n =>
    refine valid_map_range _ ?_ _ _ ?_ ?_
    · intro i j h
      apply hmono
      simp only [Grid.index]
      exact Int.mul_lt_mul_of_pos_right (by omega) (by omega)
    · apply hlo
      simp only [hcast]
      exact cover_lo hfl hst 0
    · intro i _ h2
      apply hhi
      simp only [hcast]
      exact cover_hi hfl hst (by omega)

end Inkproof.Axis.Proofs
