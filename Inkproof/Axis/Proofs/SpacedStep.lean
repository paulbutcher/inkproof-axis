/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Scales

namespace Inkproof.Axis.Proofs

theorem stepMultiples_eq : stepMultiples = [1, 2, 2.5, 5] := rfl

theorem scaleByPow10_nonneg (m : Float) (k : Int) (h : 0 ≤ k) :
    scaleByPow10 m k = m * Float.pow 10 (Float.ofInt k) := by
  simp [scaleByPow10, h]

theorem scaleByPow10_neg (m : Float) (k : Int) (h : ¬ 0 ≤ k) :
    scaleByPow10 m k = m / Float.pow 10 (Float.ofInt (-k)) := by
  simp [scaleByPow10, h]

theorem spacedStep_none (multiples : List Float) (span extent spacing : Float)
    (h : ¬ ((span * spacing / extent).isFinite && 0 < span * spacing / extent)) :
    spacedStep multiples span extent spacing = none := by
  simp [spacedStep, h]

/-- A step is at least the length that keeps ticks the spacing apart, `span * spacing / extent` in the units of the range: at `extent / span` pixels per unit, ticks a step apart are at least `spacing` pixels apart. -/
theorem spacedStep_ge (multiples : List Float) (span extent spacing step : Float)
    (h : spacedStep multiples span extent spacing = some step) :
    span * spacing / extent ≤ step := by
  dsimp only [spacedStep] at h
  split at h
  · have := List.find?_some h
    simpa using this
  · simp at h

/-- A step is one of the candidates `m * 10 ^ e` for a multiple `m`. -/
theorem spacedStep_mem (multiples : List Float) (span extent spacing step : Float)
    (h : spacedStep multiples span extent spacing = some step) :
    ∃ m ∈ multiples, ∃ e : Int, step = scaleByPow10 m e := by
  dsimp only [spacedStep] at h
  split at h
  · have := List.mem_of_find?_eq_some h
    simp only [List.mem_flatMap, List.mem_map] at this
    obtain ⟨e, _, m, hm, rfl⟩ := this
    exact ⟨m, hm, e, rfl⟩
  · simp at h

theorem gridTicks_valid (lo hi step : Float) :
    gridTicks lo hi step = [] ∨ Ticks.Valid lo hi (gridTicks lo hi step) = true := by
  unfold gridTicks
  split
  · dsimp only
    split
    · right; simp_all
    · left; rfl
  · left; rfl

theorem gridTicks_of_not_step (lo hi step : Float) (h : ¬ (step.isFinite && 0 < step) = true) :
    gridTicks lo hi step = [] := by
  simp [gridTicks, h]

local instance : IntCast Float := ⟨Float.ofInt⟩

/-- The ticks are multiples of the step: `i + first` times it, over the multiples that `Grid.cover` finds within the range. -/
theorem mem_gridTicks (lo hi step t : Float) (h : t ∈ gridTicks lo hi step) :
    ∃ i < (Grid.cover (fun x : Float => x.floor.toInt64.toInt) lo hi step).count,
      t = (Grid.cover (fun x : Float => x.floor.toInt64.toInt) lo hi step).value i := by
  unfold gridTicks at h
  split at h
  · dsimp only at h
    split at h
    · obtain ⟨i, hi, e⟩ := by simpa [Grid.values] using h
      exact ⟨i, hi, e.symm⟩
    · simp at h
  · simp at h

theorem spacedLinearTicks_eq (multiples : List Float) (lo hi extent spacing a b step : Float)
    (h : ordered lo hi = some (a, b)) (hs : spacedStep multiples (b - a) extent spacing = some step) :
    spacedLinearTicks multiples lo hi extent spacing = gridTicks a b step := by
  simp [spacedLinearTicks, h, hs]

theorem spacedLinearTicks_of_step_none (multiples : List Float) (lo hi extent spacing a b : Float)
    (h : ordered lo hi = some (a, b)) (hs : spacedStep multiples (b - a) extent spacing = none) :
    spacedLinearTicks multiples lo hi extent spacing = [] := by
  simp [spacedLinearTicks, h, hs]

theorem spacedLinearTicks_of_unordered (multiples : List Float) (lo hi extent spacing : Float)
    (h : ordered lo hi = none) : spacedLinearTicks multiples lo hi extent spacing = [] := by
  simp [spacedLinearTicks, h]

theorem linearScaleTicksSpaced_eq (multiples : List Float) (s : Inkproof.Scale.Linear Float) (extent spacing : Float) :
    linearScaleTicksSpaced multiples s extent spacing =
      spacedLinearTicks multiples s.domainStart s.domainEnd extent spacing := rfl

end Inkproof.Axis.Proofs
