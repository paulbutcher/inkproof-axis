/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Proofs.MonthTicks
import Inkproof.Axis.ClockTicks

namespace Inkproof.Axis.Proofs

open Inkproof.Axis

private theorem le_mul_cdiv {m a : Int} (hm : 0 < m) : a ≤ m * (-((-a) / m)) := by
  have := Int.mul_ediv_self_le (x := -a) (k := m) (by omega)
  rw [Int.mul_neg]; omega

theorem mem_multiplesIn {n : Nat} {a b w : Int} :
    w ∈ multiplesIn n a b ↔ w % ((max n 1 : Nat) : Int) = 0 ∧ a ≤ w ∧ w ≤ b := by
  have hm : (0 : Int) < ((max n 1 : Nat) : Int) := by omega
  unfold multiplesIn
  simp only [List.mem_map, List.mem_range]
  generalize ((max n 1 : Nat) : Int) = m at hm ⊢
  have ha := le_mul_cdiv (a := a) hm
  have hb := Int.mul_ediv_self_le (x := b) (k := m) (by omega)
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi' : (i : Int) ≤ b / m - -((-a) / m) := by omega
    have h3 : m * (-((-a) / m) + i) ≤ m * (b / m) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have h4 : m * (-((-a) / m)) ≤ m * (-((-a) / m) + i) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    exact ⟨by simp, by omega, by omega⟩
  · rintro ⟨h0, h1, h2⟩
    obtain ⟨q, rfl⟩ : ∃ q, w = m * q := ⟨w / m, by have := Int.emod_add_mul_ediv w m; omega⟩
    have hq1 : q ≤ b / m := (Int.le_ediv_iff_mul_le hm).2 (by rw [Int.mul_comm]; exact h2)
    have hq0 : -((-a) / m) ≤ q := by
      have : -q ≤ (-a) / m := (Int.le_ediv_iff_mul_le hm).2 (by
        rw [Int.neg_mul, Int.mul_comm q m]; omega)
      omega
    exact ⟨(q - -((-a) / m)).toNat, by omega, by congr 1; omega⟩

theorem multiplesIn_sorted (n : Nat) (a b : Int) : (multiplesIn n a b).Pairwise (· < ·) := by
  have hm : (0 : Int) < ((max n 1 : Nat) : Int) := by omega
  unfold multiplesIn
  simp only []
  generalize ((max n 1 : Nat) : Int) = m at hm ⊢
  refine List.pairwise_map.mpr (List.pairwise_lt_range.imp fun {i j} h => ?_)
  have : (i : Int) < j := by exact_mod_cast h
  exact Int.mul_lt_mul_of_pos_left (by omega) hm

private theorem mem_clockTicks_aux {off : Int → Int} {n : Nat} {lo hi t : Int} :
    t ∈ clockTicks off n lo hi ↔
      lo ≤ t ∧ t ≤ hi ∧ ∃ w, w % ((max n 1 : Nat) : Int) = 0 ∧ lo - 86400 ≤ w ∧ w ≤ hi + 86400 ∧
        t ∈ localInstants off w := by
  unfold clockTicks
  rw [List.mem_mergeSort]
  simp only [List.mem_filter, List.mem_flatMap, mem_multiplesIn, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨w, ⟨hw, ha, hb⟩, ht⟩, h1, h2⟩
    exact ⟨h1, h2, w, hw, ha, hb, ht⟩
  · rintro ⟨h1, h2, w, hw, ha, hb, ht⟩
    exact ⟨⟨w, ⟨hw, ha, hb⟩, ht⟩, h1, h2⟩

/-- Every tick is in range and an instant at which the local wall clock reads a multiple of `step` (`step = 0` counts as 1). -/
theorem clockTicks_sound {off : Int → Int} {n : Nat} {lo hi t : Int}
    (h : t ∈ clockTicks off n lo hi) :
    lo ≤ t ∧ t ≤ hi ∧ (t + off t) % ((max n 1 : Nat) : Int) = 0 := by
  obtain ⟨h1, h2, w, hw, -, -, ht⟩ := mem_clockTicks_aux.1 h
  rw [(mem_localInstants).1 ht |>.1]
  exact ⟨h1, h2, hw⟩

/-- No instant at which the local wall clock reads a multiple of `step` is skipped, provided the offset at it is at most a day and equals the offset a day before or after the wall-clock reading (that is, no offset change within a day of the tick makes it otherwise). -/
theorem clockTicks_complete {off : Int → Int} {n : Nat} {lo hi t : Int}
    (hlo : lo ≤ t) (hhi : t ≤ hi) (hoff : -86400 ≤ off t ∧ off t ≤ 86400)
    (hk : (t + off t) % ((max n 1 : Nat) : Int) = 0)
    (hnear : off (t + off t - 86400) = off t ∨ off (t + off t + 86400) = off t) :
    t ∈ clockTicks off n lo hi := by
  refine mem_clockTicks_aux.2 ⟨hlo, hhi, t + off t, hk, by omega, by omega, ?_⟩
  rw [mem_localInstants]
  refine ⟨rfl, ?_⟩
  rcases hnear with h | h
  · left; omega
  · right; omega

theorem clockTicks_sorted (off : Int → Int) (n : Nat) (lo hi : Int) :
    (clockTicks off n lo hi).Pairwise (· < ·) := by
  unfold clockTicks
  have hnd : (((multiplesIn n (lo - 86400) (hi + 86400)).flatMap (localInstants off)).filter
      fun t => lo ≤ t ∧ t ≤ hi).Nodup := by
    refine List.Nodup.sublist List.filter_sublist ?_
    unfold List.Nodup
    rw [List.pairwise_flatMap]
    refine ⟨fun w _ => nodup_localInstants off w, ?_⟩
    refine (multiplesIn_sorted n _ _).imp ?_
    intro w v hwv x hx y hy
    have := (mem_localInstants.1 hx).1
    have := (mem_localInstants.1 hy).1
    rintro rfl
    omega
  have hs := List.pairwise_mergeSort (le := fun a b : Int => decide (a ≤ b))
    (by intro a b c; simpa using Int.le_trans) (by intro a b; simp; omega)
    (((multiplesIn n (lo - 86400) (hi + 86400)).flatMap (localInstants off)).filter
      fun t => lo ≤ t ∧ t ≤ hi)
  have hn2 := (List.mergeSort_perm _ (fun a b : Int => decide (a ≤ b))).nodup_iff.mpr hnd
  have := hs.and (List.nodup_iff_pairwise_ne.mp hn2)
  exact this.imp fun ⟨h1, h2⟩ => by simp at h1; omega

theorem durationTicksAt_fst (off : Int → Int) (lo hi : Float) (target : Nat) :
    (durationTicksAt off lo hi target).1 = durationStep ((if hi < lo then lo else hi) - (if hi < lo then hi else lo)) target := by
  unfold durationTicksAt
  dsimp only
  split <;> split <;> rfl

end Inkproof.Axis.Proofs
