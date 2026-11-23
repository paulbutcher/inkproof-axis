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

theorem mem_multipleTicks {β : Type u} [Mul β] [LE β] [LT β] [DecidableLE β] {pw : Int → β} {ms : List β}
    {lo hi : β} {e0 e1 : Int} {t : β} :
    t ∈ multipleTicks pw ms lo hi e0 e1 ↔
      (∃ e, e0 ≤ e ∧ e ≤ e1 ∧ ∃ m ∈ ms, t = m * pw e) ∧ lo ≤ t ∧ t ≤ hi := by
  simp only [multipleTicks, List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨i, hi', m, hm, rfl⟩, h1, h2⟩
    exact ⟨⟨e0 + i, by omega, by omega, m, hm, rfl⟩, h1, h2⟩
  · rintro ⟨⟨e, h1, h2, m, hm, rfl⟩, h3, h4⟩
    exact ⟨⟨(e - e0).toNat, by omega, m, hm, by congr 2; omega⟩, h3, h4⟩

omit [Field α] [OrderedRing α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] in
theorem valid_of_pairwise [DecidableLE α] [DecidableLT α] {lo hi : α} :
    ∀ l : List α, l.Pairwise (· < ·) → (∀ x ∈ l, lo ≤ x ∧ x ≤ hi) → Ticks.Valid lo hi l = true
  | [], _, _ => by simp [Ticks.Valid]
  | [x], _, h => by
    have := h x (by simp)
    simp [Ticks.Valid, this.1, this.2]
  | x :: y :: rest, hp, h => by
    have hx := h x (by simp)
    have hxy : x < y := (List.pairwise_cons.1 hp).1 y (by simp)
    have ih := valid_of_pairwise (y :: rest) (List.pairwise_cons.1 hp).2
      (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp only [Ticks.Valid, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hx.1, hxy⟩, ih⟩

omit [Std.LawfulOrderLT α] in
/-- With ascending positive multiples, positive powers, and every multiple of a lower power below every multiple of a higher one, the multiple ticks are strictly ascending and inside the range. -/
theorem multipleTicks_valid [DecidableLE α] [DecidableLT α] {pw : Int → α} {ms : List α} {lo hi : α}
    {e0 e1 : Int} (hms : ms.Pairwise (· < ·)) (hpos : ∀ e, 0 < pw e)
    (hsep : ∀ e e' : Int, e < e' → ∀ m ∈ ms, ∀ m' ∈ ms, m * pw e < m' * pw e') :
    Ticks.Valid lo hi (multipleTicks pw ms lo hi e0 e1) = true := by
  apply valid_of_pairwise
  · refine List.Pairwise.filter _ ?_
    rw [List.pairwise_flatMap]
    refine ⟨fun i _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      exact hms.imp fun {a b} hab => OrderedRing.mul_lt_mul_of_pos_right hab (hpos _)
    · exact List.pairwise_lt_range.imp fun {i j} hij => by
        intro x hx y hy
        simp only [List.mem_map] at hx hy
        obtain ⟨m, hm, rfl⟩ := hx
        obtain ⟨m', hm', rfl⟩ := hy
        exact hsep _ _ (by omega) m hm m' hm'
  · intro x hx
    have := mem_multipleTicks.1 hx
    exact ⟨this.2.1, this.2.2⟩

end Inkproof.Axis.Proofs
