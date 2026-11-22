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

end Inkproof.Axis
