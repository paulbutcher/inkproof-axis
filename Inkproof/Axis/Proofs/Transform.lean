/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Ticks

namespace Inkproof.Axis.Proofs

theorem mapBack_valid (increasing : Bool) (fix inv : Float → Float) (lo hi : Float) (us : List Float) :
    mapBack increasing fix inv lo hi us = [] ∨ Ticks.Valid lo hi (mapBack increasing fix inv lo hi us) := by
  by_cases h : Ticks.Valid lo hi (backTicks increasing fix inv lo hi us) = true
  · right; simp [mapBack, h]
  · left; simp [mapBack, h]

theorem mem_dropRepeats (ts : List Float) (t : Float) (h : t ∈ dropRepeats ts) : t ∈ ts := by
  unfold dropRepeats at h
  induction ts with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.foldr_cons] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

theorem mem_backTicks (increasing : Bool) (fix inv : Float → Float) (lo hi : Float) (us : List Float) (t : Float)
    (h : t ∈ backTicks increasing fix inv lo hi us) : ∃ u ∈ us, t = fix (inv u) := by
  unfold backTicks at h
  have h := (List.mem_filter.mp (mem_dropRepeats _ _ h)).1
  have h : t ∈ us.map fun u => fix (inv u) := by
    cases increasing <;> simpa using h
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h
  exact ⟨u, hu, rfl⟩

theorem mem_mapBack (increasing : Bool) (fix inv : Float → Float) (lo hi : Float) (us : List Float) (t : Float)
    (h : t ∈ mapBack increasing fix inv lo hi us) : ∃ u ∈ us, t = fix (inv u) := by
  by_cases hv : Ticks.Valid lo hi (backTicks increasing fix inv lo hi us) = true
  · simp only [mapBack, hv, ite_true] at h
    exact mem_backTicks _ _ _ _ _ _ _ h
  · simp [mapBack, hv] at h

theorem transformTicks_of_unordered (fwd inv round : Float → Float) (lo hi : Float) (target : Nat)
    (h : ordered lo hi = none) : transformTicks fwd inv round lo hi target = [] := by
  simp [transformTicks, h]

theorem transformTicks_eq (fwd inv round : Float → Float) (lo hi a b u0 u1 : Float) (target : Nat)
    (h : ordered lo hi = some (a, b)) (hu : ordered (fwd a) (fwd b) = some (u0, u1)) :
    transformTicks fwd inv round lo hi target =
      mapBack (fwd a < fwd b) round inv a b (gridTicks u0 u1 (niceStep (u1 - u0) target)) := by
  simp [transformTicks, h, hu]

theorem transformTicks_of_unspread (fwd inv round : Float → Float) (lo hi a b : Float) (target : Nat)
    (h : ordered lo hi = some (a, b)) (hu : ordered (fwd a) (fwd b) = none) :
    transformTicks fwd inv round lo hi target = [] := by
  simp [transformTicks, h, hu]

end Inkproof.Axis.Proofs
