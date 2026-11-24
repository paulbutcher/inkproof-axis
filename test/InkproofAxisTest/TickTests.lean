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

private def roundDigits (digits : Nat) (x : Float) : Float :=
  if x == 0 then x
  else
    let k : Int := digits - 1 - (Float.floor x.abs.log10).toInt64.toInt
    if 0 ≤ k then (x * Float.pow 10 (Float.ofInt k)).round / Float.pow 10 (Float.ofInt k)
    else (x / Float.pow 10 (Float.ofInt (-k))).round * Float.pow 10 (Float.ofInt (-k))

private def asinhFwd (x : Float) : Float := Float.log (x + Float.sqrt (x * x + 1))

private def weibullFwd (p : Float) : Float := Float.log (-Float.log (1 - p))

private def weibullInv (u : Float) : Float := 1 - Float.exp (-Float.exp u)

private def transformKnown : TestCase := .mk "Transform ticks sit at the transformed scale's own steps" <|
  do
    check (transformTicks id id id 0 100 5 == linearTicks 0 100 5) "identity"
    check (transformTicks id id id 100 0 5 == linearTicks 0 100 5) "reversed"
    check (transformTicks (fun x => -x) (fun x => -x) id 0 100 5 == linearTicks 0 100 5) "decreasing"
    check (transformTicks id id id 1 1 5 == []) "empty"
    check (transformTicks (fun _ => 0) id id 0 1 5 == []) "unspread"
    let ts := transformTicks asinhFwd Float.sinh (roundDigits 3) (-1000) 1000 7
    check (ts.length ≥ 3) s!"{ts}"
    check (ts.contains 0) s!"zero: {ts}"

private def transformProps : TestCase := .mk "Transform ticks lie in the range, ascend and are rounded back values of even steps" <|
  forAll 2000 (fun g =>
    let (m, g) := g.below 1000
    let (e, g) := g.below 6
    let (t, g) := g.below 9
    ((-(m.toFloat + 1) * Float.pow 10 e.toFloat, (m.toFloat + 1) * Float.pow 10 e.toFloat, t + 2), g)) fun (lo, hi, t) => do
    let ts := transformTicks asinhFwd Float.sinh (roundDigits 3) lo hi t
    check (within lo hi ts) s!"outside range: {ts}"
    check (ascending ts) s!"not ascending: {ts}"
    let step := niceStep (asinhFwd hi - asinhFwd lo) t
    let us := ts.map asinhFwd
    check (us.all fun u => ((u / step) - (u / step).round).abs < 0.01) s!"not on the steps: {us}"

private def weibullProps : TestCase := .mk "Weibull ticks lie in the range and ascend" <|
  forAll 200 (fun g => let (m, g) := g.below 40; (((m.toFloat + 1) / 100, 0.99 - m.toFloat / 100 / 3), g)) fun (lo, hi) => do
    let ts := transformTicks weibullFwd weibullInv (roundDigits 3) lo hi 6
    check (within lo hi ts && ascending ts) s!"weibull: {ts}"
private def spacedKnown : TestCase := .mk "Spaced linear steps follow the pixel spacing and the multiples" <|
  do
    check (spacedStep stepMultiples 120000 1000 40 == some 5000) s!"{spacedStep stepMultiples 120000 1000 40}"
    check (spacedStep stepMultiples 120000 800 40 == some 10000) "10000"
    check (spacedStep stepMultiples 1 800 40 == some 0.05) s!"{spacedStep stepMultiples 1 800 40}"
    check (spacedStep stepMultiples 1 800 0 == none) "no spacing"
    check (spacedStep [] 1 800 40 == none) "no multiples"
    check (spacedLinearTicks stepMultiples 0 120000 1000 40 == (List.range 25).map (·.toFloat * 5000)) "ticks"
    let s : Inkproof.Scale.Linear Float := ⟨0, 10, 0, 800⟩
    check (linearScaleTicksSpaced stepMultiples s 800 40 == spacedLinearTicks stepMultiples 0 10 800 40) "scale"

private def spacedProps : TestCase := .mk "Spaced linear ticks lie in the range, ascend and keep the spacing" <|
  forAll 3000 genRange fun (lo, hi) => do
    let ts := spacedLinearTicks stepMultiples lo hi 700 45
    check (within lo hi ts) s!"outside range: {ts}"
    check (ascending ts) s!"not ascending: {ts}"
    match spacedStep stepMultiples (hi - lo) 700 45 with
    | some step => check ((hi - lo) * 45 / 700 ≤ step) "step too short"
    | none => check ts.isEmpty "ticks without a step"

private def logBaseKnown : TestCase := .mk "Log ticks in other bases, minor ticks and power labels" <|
  do
    let two := logTicksIn 2 1 1024 12
    check (two == (List.range 11).map fun i => Float.pow 2 i.toFloat) s!"{two}"
    check (logTicksIn 2 3 70 4 == [4, 16, 64]) s!"{logTicksIn 2 3 70 4}"
    check (logTicksIn 10 1 1e6 7 == logTicks 1 1e6 7) "base 10 is logTicks"
    check (logTicksIn 1 1 100 5).isEmpty "base 1"
    check (logTicksAtIn 3 .integers 1 27 5 == [1, 2, 3, 6, 9, 18, 27]) s!"{logTicksAtIn 3 .integers 1 27 5}"
    check ((logMinorTicks .oneTwoFive 1 100 6) == [3, 4, 6, 7, 8, 9, 30, 40, 60, 70, 80, 90]) s!"{logMinorTicks .oneTwoFive 1 100 6}"
    check (logMinorTicks .decades 1 100 6 == (logTicksAt .integers 1 100 6).filter fun t => t != 1 && t != 10 && t != 100) "decades"
    check (logMinorTicksIn 2 .decades 1 64 8).isEmpty "base 2 has none"
    check (logMinorTicks .integers 1 100 6).isEmpty "none beyond the labelled"
    check (powerLabel .en 2 16777216 == some "2^24") s!"{powerLabel .en 2 16777216}"
    check (powerLabel .en 10 0.001 == some "10^-3") s!"{powerLabel .en 10 0.001}"
    check (powerLabel .plain 2 0.5 == some "2^−1") s!"{powerLabel .plain 2 0.5}"
    check (powerLabel .en 2 24 == none) "not a power"
    check (powerLabel .en 2 0 == none && powerLabel .en 2 (-4) == none && powerLabel .en 1 4 == none) "outside"
    check (powerLabels .en 2 [1, 2, 4] == ["2^0", "2^1", "2^2"]) "labels"
    check (powerLabels .en 2 [1, 3] == []) "one not a power"

private def logBaseProps : TestCase := .mk "Ticks in base 2 lie in the range, ascend and are powers; minor ticks are apart from the labelled ones" <|
  forAll 2000 (fun g =>
    let (e, g) := g.below 40
    let (w, g) := g.below 12
    let (m, g) := g.below 9
    let lo := (m + 1).toFloat * Float.pow 2 (e.toFloat - 20)
    ((lo, lo * Float.pow 2 (w.toFloat / 2 + 0.3)), g)) fun (lo, hi) => do
    let ts := logTicksIn 2 lo hi 6
    check (within lo hi ts && ascending ts) s!"base 2: {lo} {hi} {ts}"
    let lbl := logTicksAtIn 3 .oneTwoFive lo hi 6
    let minor := logMinorTicksIn 3 .oneTwoFive lo hi 6
    check (within lo hi minor && ascending minor) s!"minor: {minor}"
    check (minor.all fun t => !lbl.contains t) "minor among labelled"
    let ten := logMinorTicks .oneTwoFive lo hi 6
    check (within lo hi ten && ascending ten) s!"minor ten: {ten}"
    check (ten.all fun t => !(logTicksAt .oneTwoFive lo hi 6).contains t) "minor ten among labelled"

def tests : List TestCase :=
  [linearInRange, linearSpacing, linearPresent, linearReversed, degenerate, linearKnown, logTests,
    logKnown, logMultiplesKnown, logMultiplesProps, symlogKnown, scaleAdapters, durationKnown, durationProps, categoricalProps, spacedKnown, spacedProps, transformKnown, transformProps, weibullProps, logBaseKnown, logBaseProps]

end InkproofAxisTest.TickTests
