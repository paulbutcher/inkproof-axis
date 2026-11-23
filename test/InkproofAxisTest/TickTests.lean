/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis
import InkproofTools.Test.Harness

namespace InkproofAxisTest.TickTests

open InkproofTools.Test
open Inkproof.Axis

private def pairs (xs : List Float) : List (Float × Float) := xs.zip xs.tail

private def ascending (xs : List Float) : Bool := (pairs xs).all fun (a, b) => a < b

private def within (lo hi : Float) (xs : List Float) : Bool := xs.all fun x => lo ≤ x && x ≤ hi

/-- A range with a span from 1e-9 to 1e9 and an offset up to 1e9, so that spans below the resolution of the offset occur. -/
private def genRange (g : Rng) : (Float × Float) × Rng :=
  let (m, g) := g.below 1000
  let (e, g) := g.below 19
  let (o, g) := g.below 3
  let (s, g) := g.below 1000
  let span := (m.toFloat + 1) * Float.pow 10 (e.toFloat - 12)
  let offset := match o with | 0 => 0 | 1 => s.toFloat * 1e6 | _ => -(s.toFloat) * 1e3
  ((offset, offset + span), g)

private def linearInRange : TestCase := .mk "Linear ticks lie in the range and ascend" <|
  forAll 3000 genRange fun (lo, hi) => do
    let ts := linearTicks lo hi 6
    check (within lo hi ts) s!"outside range: {ts}"
    check (ascending ts) s!"not ascending: {ts}"
    check (ts.length ≤ 12) s!"too many ticks: {ts.length}"

private def linearSpacing : TestCase := .mk "Linear ticks are evenly spaced where floats allow" <|
  forAll 3000 genRange fun (lo, hi) => do
    let ts := linearTicks lo hi 6
    match pairs ts with
    | [] => pure ()
    | (a, b) :: rest =>
      let step := b - a
      let tol := 1e-9 * (max lo.abs hi.abs) + 1e-9 * step
      check (rest.all fun (x, y) => (y - x - step).abs ≤ tol) s!"uneven: {ts}"

private def linearPresent : TestCase := .mk "Linear ticks exist for ranges well above float resolution" <|
  forAll 2000 genRange fun (lo, hi) => do
    if (hi - lo) / (max lo.abs hi.abs) > 1e-6 then
      check ((linearTicks lo hi 6).length ≥ 2) s!"too few ticks for {lo}, {hi}"
    else pure ()

private def linearReversed : TestCase := .mk "A reversed range gives the ticks of its ascending interval" <|
  forAll 1000 genRange fun (lo, hi) =>
    check (linearTicks hi lo 6 == linearTicks lo hi 6) "reversed differs"

private def degenerate : TestCase := .mk "Degenerate ranges have no ticks" <|
  let nan := 0.0 / 0.0
  let inf := 1.0 / 0.0
  (do
    check (linearTicks 1 1 6).isEmpty "empty range"
    check (linearTicks nan 1 6).isEmpty "nan"
    check (linearTicks 0 inf 6).isEmpty "inf"
    check (linearTicks (-inf) inf 6).isEmpty "both inf"
    check (logTicks 0 100 6).isEmpty "log from zero"
    check (logTicks (-1) 100 6).isEmpty "log negative"
    check (durationTicks 5 5 6).isEmpty "duration empty"
    check (categoricalIndices 5 nan 3 4).isEmpty "categorical nan"
    check ((linearTicks 0 1 0).length ≥ 1) "zero target")

private def linearKnown : TestCase := .mk "Linear ticks of 0 to 10 are the even integers or so" <|
  let ts := linearTicks 0 10 5
  do
    check (ts.length ≥ 3 && ts.length ≤ 11) s!"{ts}"
    check (ts.head? == some 0) s!"{ts}"
    check (ts.getLast? == some 10) s!"{ts}"

private def logTests : TestCase := .mk "Log ticks lie in the range, ascend and are evenly spaced in the exponent" <|
  forAll 3000 (fun g =>
    let (e, g) := g.below 30
    let (w, g) := g.below 100
    let (m, g) := g.below 9
    let lo := (m + 1).toFloat * Float.pow 10 (e.toFloat - 15)
    ((lo, lo * Float.pow 10 (w.toFloat / 4 + 0.3)), g)) fun (lo, hi) => do
    let ts := logTicks lo hi 5
    check (within lo hi ts) s!"outside: {lo} {hi} {ts}"
    check (ascending ts) s!"not ascending: {ts}"
    check (ts.length ≤ 12) s!"too many: {ts.length}"
    let ds := (pairs ts).map fun (a, b) => b.log10 - a.log10
    match ds with
    | [] => pure ()
    | d :: rest =>
      if hi / lo ≥ 100 then
        check (rest.all fun x => (x - d).abs < 1e-6) s!"uneven in log space: {ts}"
      else pure ()

private def logKnown : TestCase := .mk "Log ticks of 1 to 1e6 are decades" <|
  let ts := logTicks 1 1e6 7
  check (ts == [1, 10, 100, 1000, 10000, 100000, 1000000]) s!"{ts}"

private def logMultiplesKnown : TestCase := .mk "Log ticks at chosen multiples fill each decade" <|
  let a := logTicksAt .oneTwoFive 1 100 6
  let b := logTicksAt .integers 1 30 6
  let c := logTicksAt .oneTwoFive 3 700 6
  let minor := (logTicksAt .integers 1 100 6).filter fun t => !(logTicksAt .oneTwoFive 1 100 6).contains t
  do
    check (a == [1, 2, 5, 10, 20, 50, 100]) s!"{a}"
    check (b == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 20, 30]) s!"{b}"
    check (c == [5, 10, 20, 50, 100, 200, 500]) s!"{c}"
    check (minor.length == 12 && minor.head? == some 3) s!"{minor}"
    check (logTicksAt .decades 1 1e6 7 == logTicks 1 1e6 7) "decades unchanged"
    check (logTicksAt .integers 1 1e6 4 == logTicks 1 1e6 4) "thins over many decades"
    check (logScaleTicksAt .oneTwoFive ⟨1, 100, 0, 800⟩ 6 == a) "scale adapter"
    check (logTicksAt .oneTwoFive 0 100 6).isEmpty "from zero"
    check (logTicksAt .integers (-1) 100 6).isEmpty "negative"
    check (logTicksAt .integers 1 1 6).isEmpty "empty range"
    check (logTicksAt .integers (0.0 / 0.0) 10 6).isEmpty "nan"

private def logMultiplesProps : TestCase := .mk "Multiple ticks lie in the range, ascend, and include every multiple in it" <|
  forAll 2000 (fun g =>
    let (e, g) := g.below 20
    let (w, g) := g.below 12
    let (m, g) := g.below 9
    let lo := (m + 1).toFloat * Float.pow 10 (e.toFloat - 10)
    ((lo, lo * Float.pow 10 (w.toFloat / 4 + 0.3)), g)) fun (lo, hi) => do
    let ts := logTicksAt .integers lo hi 6
    check (within lo hi ts) s!"outside: {lo} {hi} {ts}"
    check (ascending ts) s!"not ascending: {ts}"
    let want := (List.range 40).flatMap fun i => (List.range 9).map fun m =>
      (m + 1).toFloat * Float.pow 10 (i.toFloat - 12)
    let inside := want.filter fun t => lo ≤ t && t ≤ hi
    if hi.log10 - lo.log10 ≤ 6 && inside.length ≥ 2 then
      check (inside == ts) s!"missing: {lo.log10} {hi.log10} {ts.map Float.log10} {inside.map Float.log10}"
    else pure ()

private def symlogKnown : TestCase := .mk "Symlog ticks mirror the decades about zero within the range" <|
  do
    let ts := symlogTicks (-1000) 1000 1 7
    check (ts == [-1000, -100, -10, -1, 0, 1, 10, 100, 1000]) s!"{ts}"
    let us := symlogTicks (-50) 1000 1 7
    check (us == [-10, -1, 0, 1, 10, 100, 1000]) s!"{us}"
    check (symlogTicks (-1000) 1000 0 7 == [0]) "no threshold"

private def durationKnown : TestCase := .mk "Duration ticks fall on clock intervals" <|
  let ts := durationTicks 0 3600 6
  do
    check (ts == [0, 600, 1200, 1800, 2400, 3000, 3600]) s!"{ts}"
    let day := durationTicks 0 (30 * 86400) 6
    check (day.all fun t => (t / 86400) == (t / 86400).floor) s!"{day}"

private def durationProps : TestCase := .mk "Duration ticks lie in the range and ascend" <|
  forAll 3000 (fun g =>
    let (lo, g) := g.below 100000
    let (w, g) := g.below 10000000
    let (d, g) := g.below 4
    ((lo.toFloat, lo.toFloat + (w.toFloat + 1) / Float.pow 10 d.toFloat), g)) fun (lo, hi) => do
    let ts := durationTicks lo hi 6
    check (within lo hi ts) s!"outside range: {ts}"
    check (ascending ts) s!"not ascending: {ts}"

private def categoricalProps : TestCase := .mk "Category indices lie in the range, below n, and are evenly spaced" <|
  forAll 3000 (fun g =>
    let (n, g) := g.below 200
    let (lo, g) := g.below 300
    let (w, g) := g.below 300
    let (t, g) := g.below 12
    ((n, lo.toFloat - 50, lo.toFloat - 50 + w.toFloat / 2, t), g)) fun (n, lo, hi, t) => do
    let ts := categoricalIndices n lo hi t
    check (ts.all fun i => i < n && lo ≤ i.toFloat && i.toFloat ≤ hi) s!"outside: {ts}"
    check (ts.length ≤ max t 1) s!"too many: {ts.length}"
    match ts with
    | a :: b :: rest =>
      let step := b - a
      check (((a :: b :: rest).zip (b :: rest)).all fun (x, y) => y - x == step) s!"uneven: {ts}"
    | _ => pure ()

private def scaleAdapters : TestCase := .mk "Scale adapters tick the scale's visible domain" <|
  let s : Inkproof.Scale.Linear Float := ⟨0, 10, 0, 800⟩
  let c : Inkproof.Scale.Categorical String Float := ⟨#["a", "b", "c", "d"], 0, 400⟩
  do
    check (linearScaleTicks s 5 == linearTicks 0 10 5) "linear"
    check (durationScaleTicks s 5 == durationTicks 0 10 5) "duration"
    check (logScaleTicks ⟨1, 1000, 0, 800⟩ 5 == logTicks 1 1000 5) "log"
    check (categoricalScaleTicks c (-1) 10 4 == ["a", "b", "c", "d"]) "categorical"

def tests : List TestCase :=
  [linearInRange, linearSpacing, linearPresent, linearReversed, degenerate, linearKnown, logTests,
    logKnown, logMultiplesKnown, logMultiplesProps, symlogKnown, scaleAdapters, durationKnown, durationProps, categoricalProps]

end InkproofAxisTest.TickTests
