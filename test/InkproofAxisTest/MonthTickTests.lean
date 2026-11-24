/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis
import InkproofTools.Test.Harness

namespace InkproofAxisTest.MonthTickTests

open InkproofTools.Test
open Inkproof.Axis Inkproof.Core.Calendar

private def months : List String :=
  ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

/-- One hour ahead of UTC from 2024-03-31T01:00Z to 2024-10-27T01:00Z, as in London. -/
private def london (t : Int) : Int := if 1711846800 ≤ t ∧ t < 1729990800 then 3600 else 0

private def utcMonths : TestCase := .mk "UTC month ticks fall on the first of each month" <|
  do
    let ts := monthTicks (fun _ => 0) 1 1704067200 1714521600
    check (ts == [1704067200, 1706745600, 1709251200, 1711929600, 1714521600]) s!"{ts}"
    check (monthTicks (fun _ => 0) 3 1704067200 1735689600 == [1704067200, 1711929600, 1719792000, 1727740800, 1735689600])
      "quarters"

private def localMonths : TestCase := .mk "Month ticks follow the offset across a change" <|
  do
    let ts := monthTicks london 1 1704067200 1717200000
    check (ts == [1704067200, 1706745600, 1709251200, 1711926000, 1714518000, 1717196400]) s!"{ts}"
    check (timeLabelsAt london months 2678400 ts == ["Jan", "Feb", "Mar", "Apr", "May", "Jun"]) "labels"
    check (timeLabelsAt london months 3600 [1711926000 - 3600, 1711926000] == ["23:00", "Apr 1"]) "midnight"

private def contexts : TestCase := .mk "Context lines name the year or the day where it changes" <|
  do
    let ts := monthTicks london 1 1701388800 1709251200
    check (timeContextsAt london months 2678400 ts == [some "2023", some "2024", none, none]) "years"
    let hs : List Int := [1711926000 - 7200, 1711926000 - 3600, 1711926000, 1711926000 + 3600]
    check (timeContextsAt london months 3600 hs == [some "Mar 31", none, none, none]) "midnight has a label of its own"
    check (timeContextsAt (fun _ => 0) months 28800 [3600, 32400, 61200, 90000] == [some "Jan 1", none, none, some "Jan 2"]) "days"

private def properties : TestCase := .mk "Month ticks ascend and are local midnights on day 1" <|
  forAll 500 (fun g =>
    let (lo, g) := g.below 2000000000
    let (w, g) := g.below 200000000
    let (n, g) := g.below 14
    ((lo, w, n), g)) fun (lo, w, n) => do
    let lo : Int := lo
    let ts := monthTicks london n lo (lo + w)
    check ((ts.zip ts.tail).all fun (a, b) => a < b) s!"{ts}"
    for t in ts do
      let l := t + london t
      check (l % 86400 == 0 && (civilFromDays (l / 86400)).2.2 == 1) s!"{t}"

def tests : List TestCase := [utcMonths, localMonths, contexts, properties]

end InkproofAxisTest.MonthTickTests
