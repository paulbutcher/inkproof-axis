/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Proofs.Calendar
import Inkproof.Axis.MonthTicks

namespace Inkproof.Axis.Proofs

open Inkproof.Core.Calendar Inkproof.Axis

theorem monthIndex_monthStartDay (k : Int) : monthIndex (monthStartDay k) = k := by
  have h := civilFromDays_daysFromCivil (k / 12) ((k % 12).toNat + 1) 1 (by omega) (by omega)
    (Nat.le_refl 1) (by have := daysInMonth_bounds (k / 12) ((k % 12).toNat + 1); omega)
  unfold monthIndex monthStartDay
  rw [h]
  simp only []
  omega

theorem monthIndex_succ_le (z : Int) : monthIndex z ≤ monthIndex (z + 1) := by
  have hv := civilFromDays_valid z
  unfold monthIndex
  rw [civilFromDays_succ]
  rcases hc : civilFromDays z with ⟨y, m, d⟩
  rw [hc] at hv
  obtain ⟨h1, h2, -, -⟩ := hv
  dsimp only at h1 h2
  simp only [nextDay]
  split
  · dsimp only; omega
  · split <;> dsimp only <;> omega

theorem monthIndex_mono {a b : Int} (h : a ≤ b) : monthIndex a ≤ monthIndex b := by
  obtain ⟨j, rfl⟩ : ∃ j : Nat, b = a + j := ⟨(b - a).toNat, by omega⟩
  induction j with
  | zero => simp
  | succ j ih =>
    have := monthIndex_succ_le (a + j)
    have e : a + ((j + 1 : Nat) : Int) = a + j + 1 := by omega
    rw [e]
    have := ih (by omega)
    omega

theorem monthStartDay_lt {j k : Int} (h : j < k) : monthStartDay j < monthStartDay k := by
  by_cases hc : monthStartDay j < monthStartDay k
  · exact hc
  · have := monthIndex_mono (Int.not_lt.mp hc)
    rw [monthIndex_monthStartDay, monthIndex_monthStartDay] at this
    omega

theorem mem_monthStarts {n : Nat} {a b s : Int} :
    s ∈ monthStarts n a b ↔
      ∃ k, k % ((max n 1 : Nat) : Int) = 0 ∧ s = 86400 * monthStartDay k ∧ a ≤ s ∧ s ≤ b := by
  unfold monthStarts
  simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨k, ⟨⟨i, -, rfl⟩, h⟩, rfl⟩
    exact ⟨_, h.1, rfl, h.2.1, h.2.2⟩
  · rintro ⟨k, hk, rfl, ha, hb⟩
    have h0 := monthIndex_mono (a := a / 86400) (b := monthStartDay k) (by omega)
    have h1 := monthIndex_mono (a := monthStartDay k) (b := b / 86400) (by omega)
    rw [monthIndex_monthStartDay] at h0 h1
    refine ⟨k, ⟨⟨(k - monthIndex (a / 86400)).toNat, by omega, by omega⟩, hk, ha, hb⟩, rfl⟩

theorem monthStarts_sorted (n : Nat) (a b : Int) : (monthStarts n a b).Pairwise (· < ·) := by
  unfold monthStarts
  simp only []
  have hr : (List.map (fun i : Nat => monthIndex (a / 86400) + i)
      (List.range (monthIndex (b / 86400) - monthIndex (a / 86400) + 1).toNat)).Pairwise (· < ·) :=
    List.pairwise_map.mpr (List.Pairwise.imp (fun h => by omega) List.pairwise_lt_range)
  exact List.Pairwise.map (R := (· < ·)) _
    (fun j k h => by have := monthStartDay_lt h; omega) (hr.filter _)

theorem mem_localInstants {off : Int → Int} {w c : Int} :
    c ∈ localInstants off w ↔
      c + off c = w ∧ (off (w - 86400) = w - c ∨ off (w + 86400) = w - c) := by
  unfold localInstants
  simp only [List.mem_filter, decide_eq_true_eq]
  split <;> simp <;> omega

theorem nodup_localInstants (off : Int → Int) (w : Int) : (localInstants off w).Nodup := by
  unfold localInstants
  refine List.Nodup.sublist List.filter_sublist ?_
  split
  · simp
  · simp; omega

private theorem mem_flatMap_filter {off : Int → Int} {n : Nat} {lo hi t : Int} :
    t ∈ ((monthStarts n (lo - 86400) (hi + 86400)).flatMap (localInstants off)).filter
      (fun t => lo ≤ t ∧ t ≤ hi) ↔
    lo ≤ t ∧ t ≤ hi ∧ ∃ k, k % ((max n 1 : Nat) : Int) = 0 ∧ lo - 86400 ≤ 86400 * monthStartDay k ∧
      86400 * monthStartDay k ≤ hi + 86400 ∧ t ∈ localInstants off (86400 * monthStartDay k) := by
  simp only [List.mem_filter, List.mem_flatMap, mem_monthStarts, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨w, ⟨k, hk, rfl, ha, hb⟩, ht⟩, h1, h2⟩
    exact ⟨h1, h2, k, hk, ha, hb, ht⟩
  · rintro ⟨h1, h2, k, hk, ha, hb, ht⟩
    exact ⟨⟨_, ⟨k, hk, rfl, ha, hb⟩, ht⟩, h1, h2⟩

/-- Every tick is in range and is an instant at which the local wall clock reads midnight on the first of a month whose index is a multiple of `n` (`n = 0` counts as 1). -/
theorem monthTicks_sound {off : Int → Int} {n : Nat} {lo hi t : Int}
    (h : t ∈ monthTicks off n lo hi) :
    lo ≤ t ∧ t ≤ hi ∧ (t + off t) % 86400 = 0 ∧
      (civilFromDays ((t + off t) / 86400)).2.2 = 1 ∧
      monthIndex ((t + off t) / 86400) % ((max n 1 : Nat) : Int) = 0 := by
  unfold monthTicks at h
  rw [(List.mem_mergeSort).trans mem_flatMap_filter] at h
  obtain ⟨h1, h2, k, hk, -, -, ht⟩ := h
  rw [(mem_localInstants).1 ht |>.1]
  have e : 86400 * monthStartDay k / 86400 = monthStartDay k := by omega
  rw [e, monthIndex_monthStartDay]
  refine ⟨h1, h2, by omega, ?_, hk⟩
  unfold monthStartDay
  rw [civilFromDays_daysFromCivil _ _ _ (by omega) (by omega) (Nat.le_refl 1)
    (by have := daysInMonth_bounds (k / 12) ((k % 12).toNat + 1); omega)]

/-- No local midnight on the first of a month is skipped, provided the offset at the tick is at most a day and equals the offset a day before or after the wall-clock reading (that is, no offset change within a day of the tick makes it otherwise). -/
theorem monthTicks_complete {off : Int → Int} {n : Nat} {lo hi t : Int} {k : Int}
    (hlo : lo ≤ t) (hhi : t ≤ hi) (hoff : -86400 ≤ off t ∧ off t ≤ 86400)
    (hk : k % ((max n 1 : Nat) : Int) = 0) (hw : t + off t = 86400 * monthStartDay k)
    (hnear : off (t + off t - 86400) = off t ∨ off (t + off t + 86400) = off t) :
    t ∈ monthTicks off n lo hi := by
  unfold monthTicks
  rw [(List.mem_mergeSort).trans mem_flatMap_filter]
  refine ⟨hlo, hhi, k, hk, by omega, by omega, ?_⟩
  rw [mem_localInstants, ← hw]
  refine ⟨rfl, ?_⟩
  rcases hnear with h | h
  · left; omega
  · right; omega

theorem monthTicks_sorted (off : Int → Int) (n : Nat) (lo hi : Int) :
    (monthTicks off n lo hi).Pairwise (· < ·) := by
  unfold monthTicks
  have hnd : (((monthStarts n (lo - 86400) (hi + 86400)).flatMap (localInstants off)).filter
      fun t => lo ≤ t ∧ t ≤ hi).Nodup := by
    refine List.Nodup.sublist List.filter_sublist ?_
    unfold List.Nodup
    rw [List.pairwise_flatMap]
    refine ⟨fun w _ => nodup_localInstants off w, ?_⟩
    refine (monthStarts_sorted n _ _).imp ?_
    intro w v hwv x hx y hy
    have := (mem_localInstants.1 hx).1
    have := (mem_localInstants.1 hy).1
    rintro rfl
    omega
  have hs := List.pairwise_mergeSort (le := fun a b : Int => decide (a ≤ b))
    (by intro a b c; simpa using Int.le_trans) (by intro a b; simp; omega)
    (((monthStarts n (lo - 86400) (hi + 86400)).flatMap (localInstants off)).filter
      fun t => lo ≤ t ∧ t ≤ hi)
  have hn2 := (List.mergeSort_perm _ (fun a b : Int => decide (a ≤ b))).nodup_iff.mpr hnd
  have := hs.and (List.nodup_iff_pairwise_ne.mp hn2)
  exact this.imp fun ⟨h1, h2⟩ => by simp at h1; omega

theorem civilFromDays_monthStartDay (k : Int) :
    civilFromDays (monthStartDay k) = (k / 12, (k % 12).toNat + 1, 1) :=
  civilFromDays_daysFromCivil _ _ _ (by omega) (by omega) (Nat.le_refl 1)
    (by have := daysInMonth_bounds (k / 12) ((k % 12).toNat + 1); omega)

theorem timeLabelsAt_eq (off : Int → Int) (months : List String) (step : Nat) (ticks : List Int) :
    timeLabelsAt off months step ticks =
      ticks.map fun t => String.ofList ((timeLabel step (t + off t)).render months) := by
  simp [timeLabelsAt, timeLabels]

theorem timeTickLabelsAt_eq (off : Int → Int) (months : List String) (step : Float)
    (ticks : List Float) :
    timeTickLabelsAt off months step ticks =
      if ticks.all (fun t => t.isFinite && t.abs < 1e15 && step.isFinite && 0 ≤ step && step < 1e15) then
        timeLabelsAt off months step.floor.toUInt64.toNat (ticks.map fun t => t.floor.toInt64.toInt)
      else [] := rfl

theorem timeContexts_eq (months : List String) (step : Nat) (ticks : List Int) :
    timeContexts months step ticks =
      (ticks.zip (none :: ticks.map some)).map fun (t, p) => timeContext months step p t := rfl

theorem timeContext_clock (months : List String) (step : Nat) (prev : Option Int) (t : Int) (h m s)
    (hl : timeLabel step t = .clock h m s) :
    timeContext months step prev t =
      if (prev.map fun q => (civilFromDays (q / 86400)).2) = some (civilFromDays (t / 86400)).2 then none
      else some (String.ofList ((TimeLabel.date (civilFromDays (t / 86400)).2.1
        (civilFromDays (t / 86400)).2.2).render months)) := by
  simp [timeContext, hl]

theorem timeContext_year (months : List String) (step : Nat) (prev : Option Int) (t : Int)
    (hl : ∀ h m s, timeLabel step t ≠ .clock h m s) :
    timeContext months step prev t =
      if (prev.map fun q => (civilFromDays (q / 86400)).1) = some (civilFromDays (t / 86400)).1 then none
      else some (toString (civilFromDays (t / 86400)).1) := by
  unfold timeContext
  split
  · rename_i h m s e; exact absurd e (hl h m s)
  · simp

theorem timeContextsAt_eq (off : Int → Int) (months : List String) (step : Nat) (ticks : List Int) :
    timeContextsAt off months step ticks = timeContexts months step (ticks.map fun t => t + off t) := rfl

theorem timeTickContextsAt_eq (off : Int → Int) (months : List String) (step : Float)
    (ticks : List Float) :
    timeTickContextsAt off months step ticks =
      if ticks.all (fun t => t.isFinite && t.abs < 1e15 && step.isFinite && 0 ≤ step && step < 1e15) then
        timeContextsAt off months step.floor.toUInt64.toNat (ticks.map fun t => t.floor.toInt64.toInt)
      else [] := rfl

end Inkproof.Axis.Proofs
