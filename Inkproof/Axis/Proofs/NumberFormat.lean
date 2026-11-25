/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.TickLabels

namespace Inkproof.Axis.Proofs

theorem floatLabel_eq (loc : Locale) (p : Nat) (x : Float) :
    floatLabel loc p x = String.ofList (formatChars loc p
      ((x * (10 ^ p : Nat).toFloat + (Float.ofInt 1) / (Float.ofInt 2)).floor.toInt64.toInt)) := rfl

theorem formatAt_eq (fmt : NumberFormat) (p : Nat) (x : Float) :
    fmt.formatAt p x = floatLabel fmt.locale p (NumberFormat.scaleDown (fmt.magnitude x) x) ++
      fmt.suffix (fmt.magnitude x) ++ fmt.unit := rfl

theorem magnitude_of_compact_nil (fmt : NumberFormat) (h : fmt.compact = []) (x : Float) :
    fmt.magnitude x = 0 := by
  simp [NumberFormat.magnitude, h]

theorem magnitude_eq (fmt : NumberFormat) (x : Float) :
    fmt.magnitude x = (List.range fmt.compact.length).countP
      fun i => ((1000 ^ (i + 1) : Nat).toFloat ≤ x.abs) := rfl

theorem scaleDown_eq (j : Nat) (x : Float) : NumberFormat.scaleDown j x = x / (1000 ^ j : Nat).toFloat := rfl

theorem formatAll_of_precision (fmt : NumberFormat) (p : Nat) (h : fmt.precision = some p)
    (ht : fmt.trim = false) (xs : List Float) : fmt.formatAll xs = [] ∨ fmt.formatAll xs = xs.map (fmt.formatAt p) := by
  unfold NumberFormat.formatAll
  simp only [h, ht]
  split <;> simp

theorem formatAll_of_precision_trim (fmt : NumberFormat) (p : Nat) (h : fmt.precision = some p)
    (ht : fmt.trim = true) (xs : List Float) :
    fmt.formatAll xs = [] ∨ fmt.formatAll xs = xs.map (fmt.formatTrimmedAt p) := by
  unfold NumberFormat.formatAll
  simp only [h, ht]
  split <;> simp

theorem formatTrimmedAt_eq (fmt : NumberFormat) (p : Nat) (x : Float) :
    fmt.formatTrimmedAt p x =
      String.ofList (trimFraction fmt.locale (floatLabel fmt.locale p
        (NumberFormat.scaleDown (fmt.magnitude x) x)).toList) ++ fmt.suffix (fmt.magnitude x) ++ fmt.unit := rfl

theorem formatAll_trim_auto (fmt : NumberFormat) (h : fmt.precision = none) (ht : fmt.trim = true)
    (xs : List Float) :
    fmt.formatAll xs = (match xs.mapM fmt.formatTrimmedExact with | some texts => texts | none => []) := by
  unfold NumberFormat.formatAll
  simp only [h, ht]
  rfl

theorem formatTrimmedExact_spec (fmt : NumberFormat) (x : Float) (s : String)
    (h : fmt.formatTrimmedExact x = some s) : ∃ p ≤ 15, s = fmt.formatTrimmedAt p x := by
  unfold NumberFormat.formatTrimmedExact at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have := List.mem_range.mp (List.mem_of_find?_eq_some hp)
  exact ⟨p, by simp only [maxPrecision] at this; omega, rfl⟩

theorem mem_of_mapM_some {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ls : List β), xs.mapM f = some ls → ∀ s ∈ ls, ∃ x ∈ xs, f x = some s
  | [], ls, h, s, hs => by simp at h; subst h; simp at hs
  | x :: xs, ls, h, s, hs => by
    simp only [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hr : xs.mapM f with
      | none => simp [hx, hr] at h
      | some r =>
        simp [hx, hr] at h
        subst h
        rcases List.mem_cons.mp hs with rfl | hs
        · exact ⟨x, List.mem_cons_self, hx⟩
        · obtain ⟨z, hz, e⟩ := mem_of_mapM_some f xs r hr s hs
          exact ⟨z, List.mem_cons_of_mem _ hz, e⟩

/-- Every text of the automatic trimmed format is a value written at some precision up to 15. -/
theorem mem_formatAll_trim_auto (fmt : NumberFormat) (h : fmt.precision = none) (ht : fmt.trim = true)
    (xs : List Float) (s : String) (hs : s ∈ fmt.formatAll xs) :
    ∃ x ∈ xs, ∃ p ≤ 15, s = fmt.formatTrimmedAt p x := by
  rw [formatAll_trim_auto fmt h ht] at hs
  split at hs
  · rename_i texts hm
    obtain ⟨x, hx, e⟩ := mem_of_mapM_some _ xs texts hm s hs
    obtain ⟨p, hp, rfl⟩ := formatTrimmedExact_spec fmt x s e
    exact ⟨x, hx, p, hp, rfl⟩
  · simp at hs

theorem formatAt_unit (fmt : NumberFormat) (p : Nat) (x : Float) :
    ∃ s, fmt.formatAt p x = s ++ fmt.unit := ⟨_, rfl⟩

theorem formatTrimmedAt_unit (fmt : NumberFormat) (p : Nat) (x : Float) :
    ∃ s, fmt.formatTrimmedAt p x = s ++ fmt.unit := ⟨_, rfl⟩

/-- Every text `formatAll` gives ends in the unit. -/
theorem formatAll_unit (fmt : NumberFormat) (xs : List Float) (s : String) (hs : s ∈ fmt.formatAll xs) :
    ∃ t, s = t ++ fmt.unit := by
  unfold NumberFormat.formatAll at hs
  dsimp only at hs
  split at hs
  · split at hs
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
      exact formatTrimmedAt_unit fmt _ x
    · simp at hs
  · split at hs
    · rename_i texts hm
      obtain ⟨x, _, e⟩ := mem_of_mapM_some _ xs texts hm s hs
      obtain ⟨p, _, rfl⟩ := formatTrimmedExact_spec fmt x s e
      exact formatTrimmedAt_unit fmt p x
    · simp at hs
  · split at hs
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
      exact formatAt_unit fmt _ x
    · simp at hs
  · split at hs
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
      exact formatAt_unit fmt _ x
    · simp at hs

theorem trimFraction_of_not_mem (loc : Locale) (cs : List Char) (h : loc.decimal ∉ cs) :
    trimFraction loc cs = cs := by
  simp [trimFraction, h]

/-- With a fraction that has no zeros to drop, nothing changes; a fraction of zeros loses the separator too. -/
theorem trimFraction_split (loc : Locale) (whole frac : List Char) (hd : loc.decimal ≠ '0')
    (hf : loc.decimal ∉ frac) :
    trimFraction loc (whole ++ loc.decimal :: frac) =
      whole ++ (if (frac.reverse.dropWhile (· = '0')).isEmpty then [] else
        loc.decimal :: (frac.reverse.dropWhile (· = '0')).reverse) := by
  have hmem : loc.decimal ∈ whole ++ loc.decimal :: frac := by simp
  unfold trimFraction
  simp only [hmem, ite_true]
  rw [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append,
    List.dropWhile_append]
  rcases hdw : frac.reverse.dropWhile (· = '0') with _ | ⟨c, r⟩
  · simp [hd]
  · have hc : c ∈ frac := by
      have := (List.dropWhile_sublist (l := frac.reverse) (fun x => decide (x = '0'))).subset
        (a := c) (by rw [hdw]; simp)
      simpa using this
    have hne : c ≠ loc.decimal := fun e => hf (e ▸ hc)
    simp [hne]

theorem trimFraction_en_half : trimFraction Locale.en "0.50".toList = "0.5".toList := by decide

theorem trimFraction_en_whole : trimFraction Locale.en "1.0".toList = "1".toList := by decide

theorem trimFraction_en_hundred : trimFraction Locale.en "100".toList = "100".toList := by decide

end Inkproof.Axis.Proofs
