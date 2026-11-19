/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Proofs.Calendar
import Inkproof.Core.Proofs.Decimal
import Inkproof.Axis.TimeLabel

namespace Inkproof.Axis.Proofs

open Inkproof.Core.Calendar Inkproof.Core.Decimal Inkproof.Axis

theorem timeLabel_shows (step : Nat) (t : Int) : (timeLabel step t).Shows t := by
  have hz := daysFromCivil_civilFromDays (t / 86400)
  unfold timeLabel
  rcases h : civilFromDays (t / 86400) with ⟨y, m, d⟩
  rw [h] at hz
  simp only []
  split
  · split
    · subst_vars; exact ⟨y, by simpa using hz⟩
    · exact ⟨y, hz⟩
  · split
    · exact ⟨y, hz⟩
    · refine ⟨rfl, rfl, ?_⟩
      intro x hx
      split at hx <;> simp_all

theorem timeLabel_wf (step : Nat) (t : Int) : (timeLabel step t).WF := by
  have hv := civilFromDays_valid (t / 86400)
  have hb := daysInMonth_bounds (civilFromDays (t / 86400)).1 (civilFromDays (t / 86400)).2.1
  have hs : (t % 86400).toNat < 86400 := by omega
  unfold timeLabel
  rcases h : civilFromDays (t / 86400) with ⟨y, m, d⟩
  rw [h] at hv hb
  simp only [] at hv hb ⊢
  split
  · split <;> simp only [TimeLabel.WF] <;> omega
  · split
    · simp only [TimeLabel.WF]; omega
    · refine ⟨by omega, by omega, ?_⟩
      intro x hx
      split at hx <;> simp_all <;> omega

/-- `twoDigits` writes the tens digit then the units digit. -/
theorem twoDigits_spec {n : Nat} (h : n < 100) :
    twoDigits n = [(n / 10).digitChar, (n % 10).digitChar] := by
  have : n / 10 % 10 = n / 10 := Nat.mod_eq_of_lt (by omega)
  simp [twoDigits, lsDigits, this]

/-- Two digit characters read back as the number they write. -/
theorem twoValue_spec {a b : Nat} (ha : a < 10) (hb : b < 10) :
    twoValue a.digitChar b.digitChar = some (10 * a + b) := by
  simp only [twoValue, digitChar_isDigit ha, digitChar_isDigit hb, digitsValue, Bool.and_self,
    ite_true, List.foldl_cons, List.foldl_nil]
  have h1 := digitChar_toNat ha
  have h2 := digitChar_toNat hb
  simp [h1, h2]

private theorem twoValue_twoDigits {n : Nat} (h : n < 100) :
    twoValue (n / 10).digitChar (n % 10).digitChar = some n := by
  have := twoValue_spec (a := n / 10) (b := n % 10) (by omega) (by omega)
  simpa [show 10 * (n / 10) + n % 10 = n by omega] using this

/-- A month's name is read back as the month. -/
theorem monthOf_monthName {months : List String} (hm : MonthNames.Valid months) {m : Nat}
    (h1 : 1 ≤ m) (h2 : m ≤ 12) : monthOf months (monthName months m) = some m := by
  obtain ⟨hl, hn, -⟩ := hm
  have hlt : m - 1 < months.length := by omega
  have : (months.map String.toList).idxOf (monthName months m) = m - 1 := by
    have e : monthName months m = (months.map String.toList)[m - 1]'(by simpa using hlt) := by
      simp [monthName, List.getD_eq_getElem?_getD, hlt]
    rw [e]
    exact List.Nodup.idxOf_getElem hn _ _
  simp [monthOf, this, hlt]
  omega

private theorem monthName_ne {months : List String} (hm : MonthNames.Valid months) (m : Nat) (c : Char)
    (hc : c = ' ' ∨ c = ':') : c ∉ monthName months m := by
  intro hmem
  obtain ⟨-, -, hs⟩ := hm
  rcases Nat.lt_or_ge (m - 1) months.length with h | h
  · have hmem' : c ∈ (months[m - 1]).toList := by
      simpa [monthName, List.getD_eq_getElem?_getD, h] using hmem
    have := hs _ (List.getElem_mem h) c hmem'
    rcases hc with rfl | rfl <;> simp_all
  · simp [monthName, List.getD_eq_getElem?_getD, List.getElem?_eq_none h] at hmem

private theorem not_colon_formatDecimal (d : Nat) : ':' ∉ formatDecimal 0 d := by
  obtain ⟨w, f, he, -, -, hd, -⟩ := formatNat_spec 0 d
  have hs := formatDecimal_spec 0 d
  simp [he] at hs
  rw [hs]
  intro hmem
  have := hd ':' (List.mem_append_left f hmem)
  simp at this

/-- The text of a label reads back as the label. -/
theorem parseTimeLabel_render {months : List String} (hm : MonthNames.Valid months) {l : TimeLabel}
    (hl : l.WF) : parseTimeLabel months (l.render months) = some l := by
  cases l with
  | clock h m s =>
    obtain ⟨hh, hmm, hs⟩ := hl
    have e1 := twoValue_twoDigits (n := h) (by omega)
    have e2 := twoValue_twoDigits (n := m) (by omega)
    cases s with
    | none => simp [TimeLabel.render, twoDigits_spec (by omega : h < 100), twoDigits_spec (by omega : m < 100), parseTimeLabel, parseClock, e1, e2]
    | some x =>
      have e3 := twoValue_twoDigits (n := x) (by have := hs x rfl; omega)
      simp [TimeLabel.render, twoDigits_spec (by omega : h < 100), twoDigits_spec (by omega : m < 100), twoDigits_spec (by have := hs x rfl; omega : x < 100), parseTimeLabel, parseClock, e1, e2, e3]
  | date m d =>
    obtain ⟨h1, h2, -⟩ := hl
    have hc : ':' ∉ monthName months m ++ ' ' :: formatDecimal 0 d := by
      simp only [List.mem_append, List.mem_cons, not_or]
      exact ⟨monthName_ne hm m ':' (Or.inr rfl), by decide, not_colon_formatDecimal d⟩
    have hsp : ' ' ∉ monthName months m := monthName_ne hm m ' ' (Or.inl rfl)
    simp only [TimeLabel.render, parseTimeLabel, hc, ite_false,
      splitAtChar_some ' ' _ _ hsp, monthOf_monthName hm h1 h2, parseDecimal_formatDecimal]
    simp
  | month m =>
    obtain ⟨h1, h2⟩ := hl
    have hc : ':' ∉ monthName months m := monthName_ne hm m ':' (Or.inr rfl)
    have hsp : ' ' ∉ monthName months m := monthName_ne hm m ' ' (Or.inl rfl)
    simp only [TimeLabel.render, parseTimeLabel, hc, ite_false, splitAtChar_none _ _ hsp,
      monthOf_monthName hm h1 h2]
    rfl

/-- The text of the label of the tick at `t` reads back as a label that states the tick's own clock fields or a calendar date it falls on. -/
theorem parse_timeLabel {months : List String} (hm : MonthNames.Valid months) (step : Nat) (t : Int) :
    ∃ l, parseTimeLabel months ((timeLabel step t).render months) = some l ∧ l.Shows t :=
  ⟨timeLabel step t, parseTimeLabel_render hm (timeLabel_wf step t), timeLabel_shows step t⟩

/-- `parseClock` reads the digit pairs of a clock text. -/
theorem parseClock_spec {h m : Nat} (hh : h < 100) (hm : m < 100) :
    parseClock (twoDigits h ++ ':' :: twoDigits m) = some (.clock h m none) := by
  simp [twoDigits_spec hh, twoDigits_spec hm, parseClock, twoValue_twoDigits hh, twoValue_twoDigits hm]

/-- `monthName` is the caller's name for the month. -/
theorem monthName_spec (months : List String) {m : Nat} (h1 : 1 ≤ m) (h2 : m ≤ months.length) :
    monthName months m = (months[m - 1]'(by omega)).toList := by
  simp [monthName, List.getD_eq_getElem?_getD, show m - 1 < months.length by omega]

/-- `timeLabels` renders the label of each tick. -/
theorem timeLabels_eq (months : List String) (step : Nat) (ticks : List Int) :
    timeLabels months step ticks =
      ticks.map fun t => String.ofList ((timeLabel step t).render months) := rfl

end Inkproof.Axis.Proofs
