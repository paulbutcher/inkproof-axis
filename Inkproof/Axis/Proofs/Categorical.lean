/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Categorical
import Inkproof.Axis.Proofs.Grid

universe u

namespace Inkproof.Axis.Proofs

open Lean.Grind

attribute [local instance] Ring.intCast Semiring.natCast

theorem first_nonneg (x : Int) (hx : 0 ≤ x) {s : Nat} (hs : 0 < s) (j : Nat) :
    0 ≤ ((x - 1) / (s : Int) + 1 + j) * s := by
  have hs' : (0 : Int) < s := by omega
  have h2 := Int.lt_ediv_add_one_mul_self (x - 1) hs'
  have : -1 ≤ (x - 1) / (s : Int) := by
    refine Classical.byContradiction fun hneg => ?_
    have h5 := Int.mul_le_mul_of_nonneg_right (show (x - 1) / (s : Int) + 1 ≤ -1 by omega)
      (Int.le_of_lt hs')
    omega
  exact Int.mul_nonneg (by omega) (by omega)

section
variable {α : Type u} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

/-- Each category tick is a category (`x < n`) whose position lies in `[lo, hi]`. -/
theorem categoricalTicks_mem {fl : α → Int} (hfl : IsFloor fl) (n : Nat) (lo hi : α) {stride : Nat}
    (hs : 0 < stride) {x : Nat} (hx : x ∈ categoricalTicks fl n lo hi stride) :
    x < n ∧ lo ≤ Int.cast (x : Int) ∧ (Int.cast (x : Int) : α) ≤ hi := by
  unfold categoricalTicks at hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  have hs' : (0 : Int) < stride := by omega
  generalize hlo : -fl (-lo) = a at *
  generalize hhi : fl hi = b at *
  have ha : lo ≤ (Int.cast a : α) := by
    have := (hfl (-lo)).1
    have h3 : (Int.cast (-fl (-lo)) : α) = -Int.cast (fl (-lo)) := Ring.intCast_neg _
    rw [hlo] at h3
    grind
  have hb : (Int.cast b : α) ≤ hi := by rw [← hhi]; exact (hfl hi).1
  have h1 := Int.ediv_mul_le (max a 0 - 1) (Int.ne_of_gt hs')
  have h2 := Int.lt_ediv_add_one_mul_self (max a 0 - 1) hs'
  have h3 := Int.ediv_mul_le (min b ((n : Int) - 1)) (Int.ne_of_gt hs')
  have hk' : (min b ((n : Int) - 1)) / stride - ((max a 0 - 1) / stride + 1) + 1 > (k : Int) := by omega
  have hmul : ((max a 0 - 1) / (stride : Int) + 1 + k) * stride ≥ ((max a 0 - 1) / (stride : Int) + 1) * stride :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  have hmul2 : ((max a 0 - 1) / (stride : Int) + 1 + k) * stride ≤ (min b ((n : Int) - 1)) / stride * stride :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  have hnn := first_nonneg (max a 0) (Int.le_max_right _ _) hs k
  refine ⟨by omega, ?_, ?_⟩
  all_goals
    simp only [Int.toNat_of_nonneg hnn]
  · exact Std.le_trans ha (intCast_le (by omega))
  · exact Std.le_trans (intCast_le (by omega)) hb

end

theorem categoricalTicks_spacing {α : Type u} [IntCast α] [Neg α] (fl : α → Int) (n : Nat) (lo hi : α)
    (stride : Nat) (i : Nat) (h : i + 1 < (categoricalTicks fl n lo hi stride).length) :
    (categoricalTicks fl n lo hi stride)[i + 1] = (categoricalTicks fl n lo hi stride)[i] + stride := by
  have hs : 0 < stride := by
    refine Classical.byContradiction fun h0 => ?_
    have : stride = 0 := by omega
    subst this
    simp [categoricalTicks] at h
  simp only [categoricalTicks, List.getElem_map, List.getElem_range]
  have h1 := first_nonneg (max (-fl (-lo)) 0) (Int.le_max_right _ _) hs i
  have h2 := first_nonneg (max (-fl (-lo)) 0) (Int.le_max_right _ _) hs (i + 1)
  have h3 : ((max (-fl (-lo)) 0 - 1) / (stride : Int) + 1 + ((i + 1 : Nat) : Int)) * stride
      = ((max (-fl (-lo)) 0 - 1) / (stride : Int) + 1 + (i : Int)) * stride + stride := by
    rw [show (max (-fl (-lo)) 0 - 1) / (stride : Int) + 1 + ((i + 1 : Nat) : Int)
      = ((max (-fl (-lo)) 0 - 1) / (stride : Int) + 1 + (i : Int)) + 1 by omega, Int.add_mul]
    omega
  omega

theorem categoricalTicks_sorted {α : Type u} [IntCast α] [Neg α] (fl : α → Int) (n : Nat) (lo hi : α)
    (stride : Nat) : (categoricalTicks fl n lo hi stride).Pairwise (· < ·) := by
  rcases Nat.eq_zero_or_pos stride with rfl | hs
  · simp [categoricalTicks]
  unfold categoricalTicks
  rw [List.pairwise_map]
  refine List.pairwise_lt_range.imp ?_
  intro i j hij
  have h1 := first_nonneg (max (-fl (-lo)) 0) (Int.le_max_right _ _) hs i
  have h2 := first_nonneg (max (-fl (-lo)) 0) (Int.le_max_right _ _) hs j
  have h3 := Int.mul_lt_mul_of_pos_right
    (show (max (-fl (-lo)) 0 - 1) / (stride : Int) + 1 + (i : Int) < (max (-fl (-lo)) 0 - 1) / (stride : Int) + 1 + (j : Int) by omega)
    (show (0 : Int) < stride by omega)
  omega

end Inkproof.Axis.Proofs
