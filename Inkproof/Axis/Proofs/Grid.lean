/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Grid
import Init.Grind.Ordered.Ring
import Init.Grind.Ordered.Field

universe u

namespace Inkproof.Axis.Proofs

open Lean.Grind

attribute [local instance] Ring.intCast Semiring.natCast

section
variable {α : Type u} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

theorem natCast_pos (n : Nat) : 0 < (Nat.cast (n + 1) : α) := by
  induction n with
  | zero =>
    have h1 := OrderedRing.zero_lt_one (R := α)
    grind
  | succ n ih =>
    have h1 := OrderedRing.zero_lt_one (R := α)
    grind

theorem intCast_lt {a b : Int} (h : a < b) : (Int.cast a : α) < Int.cast b := by
  obtain ⟨n, hn⟩ : ∃ n : Nat, b = a + (n + 1 : Nat) := ⟨(b - a - 1).toNat, by omega⟩
  have := natCast_pos (α := α) n
  subst hn
  rw [Ring.intCast_add]
  simp only [Ring.intCast_natCast]
  grind

theorem intCast_le {a b : Int} (h : a ≤ b) : (Int.cast a : α) ≤ Int.cast b := by
  rcases Int.lt_or_eq_of_le h with h | rfl
  · exact Std.le_of_lt (intCast_lt h)
  · exact Std.le_refl _

/-- What a floor function must satisfy: `fl x` is the greatest integer at most `x`. -/
def IsFloor (fl : α → Int) : Prop := ∀ x : α, (Int.cast (fl x) : α) ≤ x ∧ x < Int.cast (fl x) + 1

omit [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
theorem value_succ_sub (g : Grid α) (i : Nat) : g.value (i + 1) - g.value i = g.step := by
  simp only [Grid.value, Grid.index]
  have : ((g.first + ((i + 1 : Nat) : Int) : Int) : α) = Int.cast (g.first + i) + 1 := by
    rw [show g.first + ((i + 1 : Nat) : Int) = (g.first + i) + 1 by omega, Ring.intCast_add, Ring.intCast_one]
  rw [this]
  grind

theorem value_lt {g : Grid α} (hs : 0 < g.step) {i j : Nat} (h : i < j) : g.value i < g.value j := by
  simp only [Grid.value, Grid.index]
  exact OrderedRing.mul_lt_mul_of_pos_right (intCast_lt (by omega)) hs

theorem value_le {g : Grid α} (hs : 0 < g.step) {i j : Nat} (h : i ≤ j) : g.value i ≤ g.value j := by
  simp only [Grid.value, Grid.index]
  rcases Int.lt_or_eq_of_le (show g.first + i ≤ g.first + j by omega) with h | h
  · exact Std.le_of_lt (OrderedRing.mul_lt_mul_of_pos_right (intCast_lt h) hs)
  · rw [h]; exact Std.le_refl _

theorem cover_lo {fl : α → Int} (hfl : IsFloor fl) {lo hi step : α} (hs : 0 < step)
    (i : Nat) : lo ≤ (Grid.cover fl lo hi step).value i := by
  have h1 := (hfl (-(lo / step))).1
  have hne : step ≠ 0 := by grind
  have h2 : lo / step * step = lo := Field.div_mul_cancel hne
  have h3 : (Int.cast (-fl (-(lo / step))) : α) = -Int.cast (fl (-(lo / step))) := Ring.intCast_neg _
  have h4 : lo / step ≤ (Int.cast (-fl (-(lo / step))) : α) := by grind
  have h5 : (Int.cast (-fl (-(lo / step))) : α) ≤ Int.cast ((Grid.cover fl lo hi step).index i) :=
    intCast_le (by simp only [Grid.cover, Grid.index]; omega)
  have h6 : lo / step ≤ Int.cast ((Grid.cover fl lo hi step).index i) := Std.le_trans h4 h5
  have h7 := OrderedRing.mul_le_mul_of_nonneg_right h6 (Std.le_of_lt hs)
  have hst : (Grid.cover fl lo hi step).step = step := rfl
  simp only [Grid.value, hst]
  grind

theorem cover_hi {fl : α → Int} (hfl : IsFloor fl) {lo hi step : α} (hs : 0 < step) {i : Nat}
    (hi' : i < (Grid.cover fl lo hi step).count) : (Grid.cover fl lo hi step).value i ≤ hi := by
  have h1 := (hfl (hi / step)).1
  have hne : step ≠ 0 := by grind
  have h2 : hi / step * step = hi := Field.div_mul_cancel hne
  have h5 : (Int.cast ((Grid.cover fl lo hi step).index i) : α) ≤ Int.cast (fl (hi / step)) :=
    intCast_le (by simp only [Grid.cover, Grid.index] at *; omega)
  have h6 := Std.le_trans h5 h1
  have h7 := OrderedRing.mul_le_mul_of_nonneg_right h6 (Std.le_of_lt hs)
  have hst : (Grid.cover fl lo hi step).step = step := rfl
  simp only [Grid.value, hst]
  grind

omit [Field α] [OrderedRing α] in
theorem valid_map_range {lo hi : α} [DecidableLE α] [DecidableLT α] (f : Nat → α)
    (hlt : ∀ i j, i < j → f i < f j) :
    ∀ (n s : Nat), lo ≤ f s → (∀ i, s ≤ i → i < s + n → f i ≤ hi) →
      Ticks.Valid lo hi ((List.range' s n).map f) = true := by
  intro n
  induction n with
  | zero => intros; simp [Ticks.Valid]
  | succ n ih =>
    intro s hlo hhi
    rw [List.range'_succ, List.map_cons]
    cases n with
    | zero =>
      simp [Ticks.Valid]
      exact ⟨hlo, hhi s (Nat.le_refl _) (by omega)⟩
    | succ m =>
      rw [List.range'_succ, List.map_cons]
      have hv := ih (s + 1) (Std.le_of_lt (Std.lt_of_le_of_lt hlo (hlt s (s + 1) (by omega))))
        (fun i h1 h2 => hhi i (by omega) (by omega))
      rw [List.range'_succ, List.map_cons] at hv
      simp only [Ticks.Valid, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hlo, hlt s (s + 1) (by omega)⟩, hv⟩

theorem cover_valid [DecidableLE α] [DecidableLT α] {fl : α → Int} (hfl : IsFloor fl)
    {lo hi step : α} (hs : 0 < step) :
    Ticks.Valid lo hi (Grid.cover fl lo hi step).values = true := by
  unfold Grid.values
  rw [List.range_eq_range']
  cases hc : (Grid.cover fl lo hi step).count with
  | zero => simp [Ticks.Valid]
  | succ n =>
    refine valid_map_range _ (fun i j h => value_lt hs h) _ _ (cover_lo hfl hs 0) ?_
    intro i _ h2
    exact cover_hi hfl hs (by omega)

end

end Inkproof.Axis.Proofs
