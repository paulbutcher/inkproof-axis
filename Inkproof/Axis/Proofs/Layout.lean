/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Layout
import Inkproof.Axis.Proofs.Grid

universe u v

namespace Inkproof.Axis.Proofs

open Lean.Grind

attribute [local instance] Ring.intCast Semiring.natCast

theorem everyNth_sublist {β : Type v} (k : Nat) (l : List β) : (everyNth k l).Sublist l := by
  fun_induction everyNth k l with
  | case1 => exact List.Sublist.slnil
  | case2 x xs ih => exact (ih.trans (List.drop_sublist _ _)).cons_cons x

theorem everyNth_ne_nil {β : Type v} (k : Nat) {l : List β} (h : l ≠ []) : everyNth k l ≠ [] := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => unfold everyNth; simp

section
variable {α : Type u} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]
  [DecidableLE α] {β : Type v}

/-- Neighbours that are clear of each other, with spans that run forward, are clear of every later element. -/
theorem clearChain_pairwise {span : β → Span α} {gap : α} (hg : 0 ≤ gap) (l : List β) :
    (∀ x ∈ l, (span x).lo ≤ (span x).hi) → clearChain span gap l = true →
      l.Pairwise fun a b => (span a).hi + gap ≤ (span b).lo := by
  induction l with
  | nil => intros; exact List.Pairwise.nil
  | cons a rest ih =>
    intro hwf hc
    cases rest with
    | nil => exact List.pairwise_singleton _ _
    | cons b rest' =>
      simp only [clearChain, Bool.and_eq_true, decide_eq_true_eq] at hc
      have ih' := ih (fun x hx => hwf x (List.mem_cons_of_mem _ hx)) hc.2
      refine List.Pairwise.cons ?_ ih'
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hc.1
      · have h1 := (List.pairwise_cons.1 ih').1 y hy
        have h2 := hwf b (by simp)
        have h3 := hc.1
        grind

omit [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
theorem thin_sublist (span : β → Span α) (gap : α) (items : List β) :
    (thin span gap items).2.Sublist items := by
  unfold thin
  split
  · exact everyNth_sublist _ _
  · exact List.take_sublist _ _

omit [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
theorem thin_ne_nil (span : β → Span α) (gap : α) {items : List β} (h : items ≠ []) :
    (thin span gap items).2 ≠ [] := by
  unfold thin
  split
  · exact everyNth_ne_nil _ h
  · cases items with
    | nil => exact absurd rfl h
    | cons x xs => simp

theorem thin_clear {span : β → Span α} {gap : α} (hg : 0 ≤ gap) {items : List β}
    (hw : ∀ x ∈ items, (span x).lo ≤ (span x).hi) :
    (thin span gap items).2.Pairwise fun a b => (span a).hi + gap ≤ (span b).lo := by
  unfold thin
  split
  · rename_i i hi
    exact clearChain_pairwise hg _ (fun x hx => hw x ((everyNth_sublist _ _).subset hx))
      (List.find?_some (p := fun i => clearChain span gap (everyNth (i + 1) items)) hi)
  · cases items with
    | nil => exact List.Pairwise.nil
    | cons x xs => exact List.pairwise_singleton _ _

omit [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
theorem layout_kept {spans : Rotation → β → Span α} {gap : α} {items : List β} :
    ∃ r, (layout spans gap items).rotation = r ∧
      (layout spans gap items).kept = (thin (spans r) gap items).2 := by
  unfold layout
  dsimp only
  split
  · split <;> exact ⟨_, rfl, rfl⟩
  · split <;> exact ⟨_, rfl, rfl⟩

omit [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
theorem layout_sublist (spans : Rotation → β → Span α) (gap : α) (items : List β) :
    (layout spans gap items).kept.Sublist items := by
  obtain ⟨r, _, h⟩ := layout_kept (spans := spans) (gap := gap) (items := items)
  rw [h]; exact thin_sublist _ _ _

omit [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α] in
theorem layout_ne_nil (spans : Rotation → β → Span α) (gap : α) {items : List β} (h : items ≠ []) :
    (layout spans gap items).kept ≠ [] := by
  obtain ⟨r, _, e⟩ := layout_kept (spans := spans) (gap := gap) (items := items)
  rw [e]; exact thin_ne_nil _ _ h

/-- Whatever rotation is chosen, the labels kept have `gap` between neighbours and later ones, provided every label's span runs forward in every rotation. -/
theorem layout_clear {spans : Rotation → β → Span α} {gap : α} (hg : 0 ≤ gap) {items : List β}
    (hw : ∀ r, ∀ x ∈ items, (spans r x).lo ≤ (spans r x).hi) :
    (layout spans gap items).kept.Pairwise fun a b =>
      (spans (layout spans gap items).rotation a).hi + gap ≤ (spans (layout spans gap items).rotation b).lo := by
  obtain ⟨r, hr, h⟩ := layout_kept (spans := spans) (gap := gap) (items := items)
  rw [hr, h]
  exact thin_clear hg (hw r)

omit [DecidableLE α] in
theorem extent_nonneg {c w h : α} (hc : 0 ≤ c) (hw : 0 ≤ w) (hh : 0 ≤ h) (r : Rotation) : 0 ≤ r.extent c w h := by
  cases r with
  | horizontal => exact hw
  | diagonal =>
    have := OrderedRing.mul_le_mul_of_nonneg_right (show 0 ≤ w + h by grind) hc
    simp only [Rotation.extent]
    grind
  | vertical => exact hh

omit [DecidableLE α] in
theorem centred_wf {pos ext : α} (h : 0 ≤ ext) : (Span.centred pos ext).lo ≤ (Span.centred pos ext).hi := by
  have h2 := intCast_lt (α := α) (show (0 : Int) < 2 by omega)
  have hne : ((2 : Int) : α) ≠ 0 := by grind
  have h3 : ext / ((2 : Int) : α) * ((2 : Int) : α) = ext := Field.div_mul_cancel hne
  have h4 : 0 ≤ ext / ((2 : Int) : α) := by
    by_cases hc : 0 ≤ ext / ((2 : Int) : α)
    · exact hc
    · exfalso
      have := OrderedRing.mul_lt_mul_of_pos_right (Std.not_le.1 hc) (Ring.intCast_zero (α := α) ▸ h2)
      grind
  simp only [Span.centred]
  grind

omit [DecidableLE α] in
theorem centred_length (pos ext : α) : (Span.centred pos ext).hi - (Span.centred pos ext).lo = ext := by
  have h2 := intCast_lt (α := α) (show (0 : Int) < 2 by omega)
  have hne : ((2 : Int) : α) ≠ 0 := by grind
  have h3 : ext / ((2 : Int) : α) * ((2 : Int) : α) = ext := Field.div_mul_cancel hne
  simp only [Span.centred]
  grind

/-- Given a host measurement of each label as a non-negative width and height, the labels kept never overlap: each ends at least `gap` before the next begins, along the axis, in the rotation chosen. -/
theorem layout_noOverlap {c gap : α} (hc : 0 ≤ c) (hg : 0 ≤ gap) (pos : β → α) (measure : β → α × α)
    {items : List β} (hm : ∀ x ∈ items, 0 ≤ (measure x).1 ∧ 0 ≤ (measure x).2) :
    let spans (r : Rotation) (x : β) : Span α :=
      Span.centred (pos x) (r.extent c (measure x).1 (measure x).2)
    (layout spans gap items).kept.Pairwise fun a b =>
      (spans (layout spans gap items).rotation a).hi + gap ≤ (spans (layout spans gap items).rotation b).lo := by
  intro spans
  exact layout_clear (spans := spans) hg fun r x hx => centred_wf (extent_nonneg hc (hm x hx).1 (hm x hx).2 r)
end


theorem everyNth_getElem? {β : Type v} (k : Nat) (l : List β) (j : Nat) :
    (everyNth k l)[j]? = l[j * max k 1]? := by
  induction l using everyNth.induct k generalizing j with
  | case1 => simp [everyNth]
  | case2 x xs ih =>
    unfold everyNth
    cases j with
    | zero => simp
    | succ j =>
      simp only [List.getElem?_cons_succ, ih, List.getElem?_drop]
      have : (j + 1) * max k 1 = (j * max k 1 + (max k 1 - 1)) + 1 := by
        rw [Nat.add_mul]; omega
      rw [this, List.getElem?_cons_succ]
      congr 1; omega

section
variable {α : Type u} {β : Type v} [Add α] [LE α] [DecidableLE α]

theorem thin_stride_le_length (span : β → Span α) (gap : α) (items : List β) :
    (thin span gap items).1 ≤ items.length := by
  unfold thin
  split
  · rename_i i hi
    obtain ⟨_, j, hj, hij, _⟩ := List.find?_eq_some_iff_getElem.1 hi
    simp at hj hij
    omega
  · exact Nat.le_refl _

theorem thin_stride_le (span : β → Span α) (gap : α) (items : List β) {t : Nat} (ht : 1 ≤ t)
    (h : clearChain span gap (everyNth t items) = true) : (thin span gap items).1 ≤ t := by
  by_cases hl : t ≤ items.length
  · have hs : ((List.range items.length).find? fun i => clearChain span gap (everyNth (i + 1) items)).isSome := by
      rw [List.find?_isSome]
      exact ⟨t - 1, by simp; omega, by simpa [Nat.sub_add_cancel ht] using h⟩
    unfold thin
    split
    · rename_i i hi
      obtain ⟨_, j, hj, hij, hbefore⟩ := List.find?_eq_some_iff_getElem.1 hi
      simp at hj hij
      refine Nat.le_of_not_lt fun hlt => ?_
      have := hbefore (t - 1) (by omega)
      simp [Nat.sub_add_cancel ht, h] at this
    · rename_i hn
      rw [hn] at hs
      simp at hs
  · exact Nat.le_trans (thin_stride_le_length _ _ _) (by omega)

theorem thin_eq_everyNth (span : β → Span α) (gap : α) {items : List β} (h : items ≠ []) :
    1 ≤ (thin span gap items).1 ∧ (thin span gap items).2 = everyNth (thin span gap items).1 items := by
  cases items with
  | nil => exact absurd rfl h
  | cons x xs =>
    have hs : ((List.range (x :: xs).length).find? fun i => clearChain span gap (everyNth (i + 1) (x :: xs))).isSome := by
      rw [List.find?_isSome]
      refine ⟨xs.length, by simp, ?_⟩
      have : everyNth (xs.length + 1) (x :: xs) = [x] := by
        unfold everyNth
        simp [everyNth]
      simp [this, clearChain]
    unfold thin
    split
    · simp
    · rename_i hn
      rw [hn] at hs
      simp at hs

/-- No rotation keeps labels at a smaller stride than the one chosen. -/
theorem layout_stride_le (spans : Rotation → β → Span α) (gap : α) (items : List β) (r : Rotation) :
    (layout spans gap items).stride ≤ (thin (spans r) gap items).1 := by
  unfold layout
  dsimp only
  cases r <;> (split <;> (try split) <;> dsimp only <;> omega)

/-- The chosen rotation is the least one with the least stride: a later rotation is chosen only if it is strictly better than every earlier one. -/
theorem layout_rotation_least (spans : Rotation → β → Span α) (gap : α) (items : List β) :
    ((layout spans gap items).rotation = .diagonal →
      (thin (spans .diagonal) gap items).1 < (thin (spans .horizontal) gap items).1) ∧
    ((layout spans gap items).rotation = .vertical →
      (thin (spans .vertical) gap items).1 < (thin (spans .horizontal) gap items).1 ∧
      (thin (spans .vertical) gap items).1 < (thin (spans .diagonal) gap items).1) := by
  unfold layout
  dsimp only
  split <;> (try split) <;> simp <;> omega
end

end Inkproof.Axis.Proofs
