/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.MonthTicks
import Inkproof.Axis.Ticks

namespace Inkproof.Axis

/-- The multiples of `n` (`n = 0` counts as 1) from `a` to `b`, ascending. -/
def multiplesIn (n : Nat) (a b : Int) : List Int :=
  let m : Int := (max n 1 : Nat)
  let j0 := -((-a) / m)
  ((List.range (b / m - j0 + 1).toNat).map fun i : Nat => m * (j0 + i))

/-- Ascending instants from `lo` to `hi` at which the local wall clock, `off t` seconds east of UTC at instant `t`, reads a multiple of `step` seconds since local midnight of 1970-01-01 (`step = 0` counts as 1). A clock reading skipped by an offset change has no instant, and one repeated has two. `fun _ => 0` gives UTC. -/
def clockTicks (off : Int → Int) (step : Nat) (lo hi : Int) : List Int :=
  (((multiplesIn step (lo - 86400) (hi + 86400)).flatMap (localInstants off)).filter
    fun t => lo ≤ t ∧ t ≤ hi).mergeSort

/-- The step `durationTicks` would choose for the range, and ticks at clock intervals of it on the local clock of the zone given by `off` (see `clockTicks`), so that `timeTickLabelsAt off months step ticks` labels them. Steps under a second, and a range that is empty, reversed, or not finite and under 10 ^ 15 seconds in size, give `durationTicks` for the range with the step it chose.Only the step is proved (`durationTicksAt_fst`); the ticks are converted through `Float`, which is not an ordered field, so their placement is covered by tests. -/
def durationTicksAt (off : Int → Int) (lo hi : Float) (target : Nat) : Float × List Float :=
  let a := if hi < lo then hi else lo
  let b := if hi < lo then lo else hi
  let step := durationStep (b - a) target
  if a.isFinite && b.isFinite && a.abs < 1e15 && b.abs < 1e15 && a < b && 1 ≤ step && step < 1e15 then
    (step, (clockTicks off step.floor.toUInt64.toNat a.ceil.toInt64.toInt b.floor.toInt64.toInt).map Float.ofInt)
  else (step, durationTicks lo hi target)

/-- The shortest entry of `durationSteps` at least `span * spacing / extent` seconds, the step that keeps ticks `spacing` pixels apart over `extent` pixels showing `span` seconds; below a second, a 1, 2 or 5 times a power of ten, and above the table a power-of-ten number of days. `none` unless that length is positive and finite. -/
def durationStepSpaced (span extent spacing : Float) : Option Float :=
  let raw := span * spacing / extent
  if raw.isFinite && 0 < raw then
    if raw < 1 then spacedStep [1, 2, 5] span extent spacing
    else match durationSteps.find? (raw ≤ ·) with
      | some s => some s
      | none => (spacedStep [1, 2, 5] (span / 86400) extent spacing).map (· * 86400)
  else none

/-- `durationTicksAt` with the step chosen by `durationStepSpaced` for `extent` pixels and `spacing` pixels between ticks, so that 12 days over 700 pixels at 50 gives a daily step. No ticks, with a zero step, where the range is empty, reversed, not finite or over 10 ^ 15 seconds in size, or the step is below a second or no step can be chosen. -/
def durationTicksAtSpaced (off : Int → Int) (lo hi extent spacing : Float) : Float × List Float :=
  match ordered lo hi, durationStepSpaced (hi - lo) extent spacing with
  | some (a, b), some step =>
    if a.abs < 1e15 && b.abs < 1e15 && 1 ≤ step && step < 1e15 then
      (step, (clockTicks off step.floor.toUInt64.toNat a.ceil.toInt64.toInt b.floor.toInt64.toInt).map Float.ofInt)
    else (step, [])
  | _, _ => (0, [])

end Inkproof.Axis
