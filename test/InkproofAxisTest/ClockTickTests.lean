/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis
import InkproofTools.Test.Harness

namespace InkproofAxisTest.ClockTickTests

open InkproofTools.Test
open Inkproof.Axis

private def months : List String :=
  ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

/-- One hour ahead of UTC from 2024-03-31T01:00Z to 2024-10-27T01:00Z, as in London. -/
private def london (t : Int) : Int := if 1711846800 ≤ t ∧ t < 1729990800 then 3600 else 0

private def kolkata (_ : Int) : Int := 19800

private def dailyAcrossChange : TestCase := .mk "Daily ticks stay at local midnight across a change" <|
  do
    let ts := clockTicks london 86400 1711670400 1712102400
    check (ts == [1711670400, 1711756800, 1711843200, 1711926000, 1712012400, 1712098800]) s!"{ts}"

private def halfHourZone : TestCase := .mk "Hourly ticks in a half-hour zone sit on local hours" <|
  do
    let ts := clockTicks kolkata 3600 1704067200 (1704067200 + 4 * 3600)
    check (ts == [1704067200 + 1800, 1704067200 + 5400, 1704067200 + 9000, 1704067200 + 12600]) s!"{ts}"

private def repeatedHour : TestCase := .mk "A repeated clock reading ticks at both instants" <|
  do
    let ts := clockTicks london 3600 1729983000 1729994000
    check (ts == [1729983600, 1729987200, 1729990800]) s!"{ts}"

private def labelled : TestCase := .mk "durationTicksAt gives ticks the labels read as local" <|
  do
    let (step, ts) := durationTicksAt london 1711670400 1712102400 5
    check (step == 86400) s!"{step}"
    let ls := timeTickLabelsAt london months step ts
    check (ls == ["Mar 29", "Mar 30", "Mar 31", "Apr", "Apr 2", "Apr 3"]) s!"{ls}"
    let (s2, ts2) := durationTicksAt london 0 0.5 5
    check (s2 < 1 && ts2 == durationTicks 0 0.5 5) "sub-second"

private def properties : TestCase := .mk "Clock ticks ascend and fall on the local clock" <|
  forAll 500 (fun g =>
    let (lo, g) := g.below 2000000000
    let (w, g) := g.below 3000000
    let (k, g) := g.below 12
    ((lo, w, k), g)) fun (lo, w, k) => do
    let lo : Int := lo
    let step : Nat := #[60, 900, 3600, 7200, 21600, 86400, 172800, 604800, 5, 1800, 600, 43200][k]!
    let w := w % (step * 2000 + 1)
    let ts := clockTicks london step lo (lo + w)
    check ((ts.zip ts.tail).all fun (a, b) => a < b) s!"{ts}"
    for t in ts do
      check ((t + london t) % step == 0 && lo ≤ t && t ≤ lo + w) s!"{t}"

def tests : List TestCase := [dailyAcrossChange, halfHourZone, repeatedHour, labelled, properties]

end InkproofAxisTest.ClockTickTests
