/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis
import InkproofTools.Test.Harness

namespace InkproofAxisTest.LabelTests

open InkproofTools.Test
open Inkproof.Axis

private def locales : List Locale := [.en, .de, .fr, .plain]

/-- Spans from 1e-6 to 1e9 around zero or a modest offset, where floats can carry the labels. -/
private def genRange (g : Rng) : (Float × Float) × Rng :=
  let (m, g) := g.below 1000
  let (e, g) := g.below 16
  let (o, g) := g.below 3
  let (s, g) := g.below 1000
  let span := (m.toFloat + 1) * Float.pow 10 (e.toFloat - 6)
  let offset := match o with | 0 => 0 | 1 => s.toFloat * 7 | _ => -(s.toFloat) * 13
  ((offset, offset + span), g)

private def readBack (loc : Locale) (s : String) : Option Float :=
  (parseChars loc s.toList).map fun (n, p) => Float.ofInt n / Float.pow 10 p.toFloat

private def labelsMatchTicks : TestCase := .mk "Labels are distinct, one per tick, and read back as the ticks" <|
  forAll 3000 genRange fun (lo, hi) => do
    let ts := linearTicks lo hi 6
    for loc in locales do
      let ls := tickLabels loc ts
      check (ls.length == ts.length) s!"{ls.length} labels for {ts}"
      check ((ls.zip ls.tail).all fun (a, b) => a != b) s!"adjacent labels equal: {ls}"
      for (t, l) in ts.zip ls do
        match readBack loc l with
        | some v => check ((v - t).abs ≤ 1e-9 * (1 + t.abs)) s!"{l} reads back as {v}, not {t}"
        | none => check false s!"{l} does not parse"

private def localesAgree : TestCase := .mk "Locales differ in notation, not in value" <|
  forAll 1000 genRange fun (lo, hi) => do
    let ts := linearTicks lo hi 6
    let reads (loc : Locale) := (tickLabels loc ts).map fun l => parseChars loc l.toList
    check (reads .en == reads .de) "en and de disagree"
    check (reads .en == reads .fr) "en and fr disagree"

private def precisionFollowsSpacing : TestCase := .mk "Precision is the fewest decimals that show the ticks" <|
  forAll 1000 genRange fun (lo, hi) => do
    let ts := linearTicks lo hi 6
    let decimals (l : String) := (l.toList.dropWhile (· != '.')).length.pred
    let ls := tickLabels .plain ts
    match ts, ls with
    | _ :: _, _ :: _ =>
      let p := (ls.map decimals).foldl max 0
      check (p == 0 || ls.any fun l => decimals l == p && !l.endsWith "0") s!"trailing zeros: {ls}"
    | _, _ => pure ()

private def degenerate : TestCase := .mk "Labels for no ticks, or ticks no float can show, are empty" <|
  do
    check ((tickLabels .en []).isEmpty) "empty"
    check ((tickLabels .en [0, 1e300, 2e300]).isEmpty) "huge"
    check ((tickLabels .en [0, 0.5 * Float.pow 10 (-20), Float.pow 10 (-20)]).isEmpty) "tiny"
    check ((tickLabels .en [0, 1, 0.0 / 0.0]).isEmpty) "nan"

private def known : TestCase := .mk "Grouping and separators follow the locale" <|
  do
    check (tickLabels .en [-1500, 0, 1500000] == ["-1,500", "0", "1,500,000"]) s!"{tickLabels .en [-1500, 0, 1500000]}"
    check (tickLabels .de [0.5, 1, 1500.5] == ["0,5", "1,0", "1.500,5"]) s!"{tickLabels .de [0.5, 1, 1500.5]}"
    check (tickLabels .fr [1000, 2000] == ["1\u202F000", "2\u202F000"]) s!"{tickLabels .fr [1000, 2000]}"

private def formats : TestCase := .mk "Number formats: compact units, fixed precision, single values" <|
  do
    let c : NumberFormat := { compact := NumberFormat.short }
    check (c.formatAll [0, 1500, 3000000] == ["0.0", "1.5k", "3.0M"]) s!"{c.formatAll [0, 1500, 3000000]}"
    check (c.format 1200 == some "1.2k") s!"{c.format 1200}"
    check (c.format 999 == some "999") s!"{c.format 999}"
    check (c.format (-2.5e9) == some "-2.5B") s!"{c.format (-2.5e9)}"
    check (({ compact := NumberFormat.short, locale := .de } : NumberFormat).format 1200 == some "1,2k") "de"
    let f : NumberFormat := { precision := some 1 }
    check (f.format 3.14159 == some "3.1") s!"{f.format 3.14159}"
    check (f.format 1234.56 == some "1,234.6") s!"{f.format 1234.56}"
    check (f.format (0.0 / 0.0) == none) "nan"
    check ((NumberFormat.mk .en none [] false "").format 2.5 == some "2.5") "default precision"

private def trimmedKnown : TestCase := .mk "Trimmed labels drop trailing zeros per label" <| do
    let t : NumberFormat := { trim := true }
    check (t.formatAll [0, 0.5, 1] == ["0", "0.5", "1"]) s!"{t.formatAll [0, 0.5, 1]}"
    check (t.formatAll [100, 250] == ["100", "250"]) s!"{t.formatAll [100, 250]}"
    check ((NumberFormat.mk .en (some 3) [] true "").formatAll [1, 1.25] == ["1", "1.25"]) "fixed"
    check ((NumberFormat.mk .de none NumberFormat.short true "").formatAll [1500, 2000] == ["1,5k", "2k"]) "compact"
    check (t.formatAll [0.1 + 0.2] == ["0.3"]) "noise"

private def unitKnown : TestCase := .mk "A unit ends every label, after the compact suffix" <| do
    let pct : NumberFormat := { unit := "%", trim := true }
    check (pct.formatAll [0, 25, 50] == ["0%", "25%", "50%"]) s!"{pct.formatAll [0, 25, 50]}"
    let b : NumberFormat := { unit := "B", compact := NumberFormat.short }
    check (b.formatAll [1000, 1500] == ["1.0kB", "1.5kB"]) s!"{b.formatAll [1000, 1500]}"
    check (({ unit := " MB" } : NumberFormat).format 2 == some "2 MB") "spaced"

private def trimmedReadBack : TestCase := .mk "Trimmed labels read back as the ticks" <|
  forAll 1000 genRange (fun (lo, hi) => do
    let ts := linearTicks lo hi 6
    let texts := ({ trim := true } : NumberFormat).formatAll ts
    if !texts.isEmpty then
      check (texts.length == ts.length) "one per tick"
      for (t, s) in ts.zip texts do
        match readBack .en s with
        | some v => check ((v - t).abs ≤ 1e-9 * (1 + t.abs)) s!"{s} for {t}"
        | none => check false s!"unreadable {s}"
        check (!(s.endsWith "0") || !(s.contains '.')) s!"padded: {s}")

def tests : List TestCase :=
  [labelsMatchTicks, localesAgree, precisionFollowsSpacing, degenerate, known, formats, trimmedKnown, unitKnown, trimmedReadBack]

end InkproofAxisTest.LabelTests
