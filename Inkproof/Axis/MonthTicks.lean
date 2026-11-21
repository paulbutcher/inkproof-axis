/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.TimeLabel

namespace Inkproof.Axis

open Inkproof.Core.Calendar

/-- The month a day (counted from 1970-01-01) falls in, as twelve times its year plus its month number from zero. -/
def monthIndex (day : Int) : Int :=
  let c := civilFromDays day
  12 * c.1 + c.2.1 - 1

/-- The first day of month `k` (see `monthIndex`), counted from 1970-01-01. -/
def monthStartDay (k : Int) : Int := daysFromCivil (k / 12) ((k % 12).toNat + 1) 1

/-- The seconds, in ascending order, at which a month whose index is a multiple of `n` (`n = 0` counts as 1) starts, from `a` to `b`. Months counted from January of year 0, so `n = 3` gives the quarters and `n = 12` the years. -/
def monthStarts (n : Nat) (a b : Int) : List Int :=
  let k0 := monthIndex (a / 86400)
  let k1 := monthIndex (b / 86400)
  (((List.range (k1 - k0 + 1).toNat).map (fun i : Nat => k0 + i)).filter fun k =>
    k % ((max n 1 : Nat) : Int) = 0 ∧ a ≤ 86400 * monthStartDay k ∧ 86400 * monthStartDay k ≤ b).map
      fun k => 86400 * monthStartDay k

/-- The instants at which the wall clock reads `wall` when `off t` is the seconds east of UTC at instant `t`. The offset is tried at a day either side of `wall`, so an offset change near it is still found. -/
def localInstants (off : Int → Int) (wall : Int) : List Int :=
  let c1 := wall - off (wall - 86400)
  let c2 := wall - off (wall + 86400)
  (if c1 = c2 then [c1] else [c1, c2]).filter fun c => c + off c = wall

/-- Ascending instants from `lo` to `hi` at which the local wall clock, `off t` seconds east of UTC at instant `t`, reads midnight on the first of a month whose index is a multiple of `n` (see `monthStarts`). `fun _ => 0` gives UTC. -/
def monthTicks (off : Int → Int) (n : Nat) (lo hi : Int) : List Int :=
  (((monthStarts n (lo - 86400) (hi + 86400)).flatMap (localInstants off)).filter
    fun t => lo ≤ t ∧ t ≤ hi).mergeSort

/-- `timeLabels` for ticks whose local time is `off t` seconds east of UTC at instant `t`, so days and months begin at local midnight. -/
def timeLabelsAt (off : Int → Int) (months : List String) (step : Nat) (ticks : List Int) : List String :=
  timeLabels months step (ticks.map fun t => t + off t)

/-- `timeTickLabels` for ticks whose local time is `off t` seconds east of UTC at instant `t`, with the offset of each tick taken at its floor in whole seconds. -/
def timeTickLabelsAt (off : Int → Int) (months : List String) (step : Float) (ticks : List Float) : List String :=
  if ticks.all fun t => t.isFinite && t.abs < 1e15 && step.isFinite && 0 ≤ step && step < 1e15 then
    timeLabelsAt off months step.floor.toUInt64.toNat (ticks.map fun t => t.floor.toInt64.toInt)
  else []

end Inkproof.Axis
