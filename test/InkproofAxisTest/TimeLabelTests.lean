/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis
import InkproofTools.Test.Harness

namespace InkproofAxisTest.TimeLabelTests

open InkproofTools.Test
open Inkproof.Axis Inkproof.Core.Calendar

private def months : List String :=
  ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

private def steps : List Nat := [1, 5, 30, 60, 900, 3600, 21600, 86400, 7 * 86400]

private def knownTimes : TestCase := .mk "Known instants are labelled by clock, date and month" <|
  let leapDay := 1709208000
  do
    check (timeLabels months 3600 [leapDay] == ["12:00"]) "leap day noon"
    check (timeLabels months 1 [leapDay + 61] == ["12:01:01"]) "seconds shown"
    check (timeLabels months 3600 [leapDay - 12 * 3600] == ["Feb 29"]) "midnight marks the day"
    check (timeLabels months 86400 [leapDay - 12 * 3600] == ["Feb 29"]) "day step"
    check (timeLabels months 86400 [leapDay - 12 * 3600 + 86400] == ["Mar"]) "first of a month, daily"
    check (timeLabels months 86400 [leapDay - 12 * 3600 + 2 * 86400] == ["Mar 2"]) "after the leap day"
    check (timeLabels months 86400 [951782400, 951782400 + 86400] == ["Feb 29", "Mar"]) "2000 is a leap year"
    check (timeLabels months 86400 [4107542400 - 86400, 4107542400] == ["Feb 28", "Mar"]) "2100 is not"
    check (timeLabels months 3600 [-3600] == ["23:00"]) "before the epoch"

private def genTicks (g : Rng) : (Nat × List Int) × Rng :=
  let (i, g) := g.below steps.length
  let (a, g) := g.below 4000000000
  let (n, g) := g.below 40
  let step := steps.getD i 1
  let first : Int := (a : Int) - 1000000000
  ((step, (List.range (n + 1)).map fun k => first + (k * step : Nat)), g)

private def parseBack : TestCase := .mk "Labels parse back as labels of the tick's own fields" <|
  forAll 3000 genTicks fun (step, ts) => do
    for t in ts do
      let l := timeLabel step t
      check (parseTimeLabel months (l.render months) == some l) s!"{t}: {l.render months}"
      let sod := (t % 86400).toNat
      match l with
      | .clock h m s =>
        check (h * 3600 + m * 60 == sod / 60 * 60 && s.getD (sod % 60) == sod % 60) s!"{t}: {repr l}"
      | .date m d => check ((civilFromDays (t / 86400)).2 == (m, d)) s!"{t}: {repr l}"
      | .month m => check ((civilFromDays (t / 86400)).2 == (m, 1)) s!"{t}: {repr l}"

private def distinctAdjacent : TestCase := .mk "Labels of adjacent duration ticks differ" <|
  forAll 3000 (fun g =>
    let (lo, g) := g.below 2000000000
    let (w, g) := g.below 100000000
    ((lo.toFloat, lo.toFloat + w.toFloat + 60), g)) fun (lo, hi) => do
    let ts := durationTicks lo hi 6
    let step := durationStep (hi - lo) 6
    let ls := timeTickLabels months step ts
    check (ls.length == ts.length) s!"{ls.length} labels for {ts.length} ticks"
    check ((ls.zip ls.tail).all fun (a, b) => a != b) s!"adjacent equal: {ls}"

private def degenerate : TestCase := .mk "Non-finite ticks have no labels" <|
  do
    check (timeTickLabels months 60 [0, 0.0 / 0.0]).isEmpty "nan"
    check (timeTickLabels months 60 [1.0 / 0.0]).isEmpty "inf"
    check (timeTickLabels months (0.0 / 0.0) [0]).isEmpty "nan step"

private def style : TimeStyle := { clock := .h12 "am" "pm", date := .numeric '/' false, contextDate := .numeric '/' false }

private def styled : TestCase := .mk "Styled labels: 12-hour clock, numeric dates, short context date" <|
  let day := 1594944000
  do
    check (timeLabelsWith style months 3600 [day + 3 * 3600, day + 15 * 3600, day + 12 * 3600, day] == ["3am", "3pm", "12pm", "7/17"]) s!"{timeLabelsWith style months 3600 [day + 3 * 3600, day + 15 * 3600, day + 12 * 3600, day]}"
    check (timeLabelsWith style months 900 [day + 15 * 3600 + 1800] == ["3:30pm"]) "minutes"
    check (timeLabelsWith style months 1 [day + 15 * 3600 + 1805] == ["3:30:05pm"]) "seconds"
    check (timeLabelsWith style months 86400 [day, day + 86400 * 15] == ["7/17", "8"]) "days"
    check (timeLabelsWith style months 86400 [day - 16 * 86400] == ["7"]) "first of month"
    check (timeLabelsWith {} months 3600 [day + 3 * 3600] == timeLabels months 3600 [day + 3 * 3600]) "default"
    let cs := timeContextsWith style months 3600 [day + 3 * 3600, day + 4 * 3600, day + 22 * 3600 + 3600 * 3]
    check (cs == [some "7/17/20", none, some "7/18/20"]) s!"{cs}"
    check (timeContextsWith { contextDate := .numeric '.' true } months 3600 [day + 3 * 3600] == [some "17.7.20"]) "day first"
    check (timeContextsWith {} months 3600 [day + 3 * 3600] == timeContexts months 3600 [day + 3 * 3600]) "default context"
    let ts := (timeTickLabelsAtWith style (fun _ => 0) months 3600 [Float.ofInt (day + 3 * 3600)])
    check (ts == ["3am"]) s!"{ts}"
    let cx := (timeTickContextsAtWith style (fun _ => 0) months 3600 [Float.ofInt (day + 3 * 3600)])
    check (cx == [some "7/17/20"]) s!"{cx}"

def tests : List TestCase := [knownTimes, parseBack, distinctAdjacent, degenerate, styled]

end InkproofAxisTest.TimeLabelTests
