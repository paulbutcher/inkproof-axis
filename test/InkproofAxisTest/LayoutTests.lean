/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis
import InkproofTools.Test.Harness

namespace InkproofAxisTest.LayoutTests

open InkproofTools.Test
open Inkproof.Axis

/-- A host whose text is 7 units wide per character and 12 high. -/
private def measure (s : String) : Float × Float := (7 * s.length.toFloat, 12)

private def alongAxis (r : Rotation) (s : String) : Float :=
  let (w, h) := measure s
  match r with
  | .horizontal => w
  | .diagonal => (w + h) * 0.7071067811865476
  | .vertical => h

private def genLabels (g : Rng) : (List (Float × String) × Float) × Rng :=
  let (n, g) := g.below 40
  let (spacing, g) := g.below 60
  let (gap, g) := g.below 10
  let (lens, g) := (List.range n).foldl (fun (acc, g) _ =>
    let (l, g) := g.below 9
    (acc ++ [l + 1], g)) (([] : List Nat), g)
  ((lens.zipIdx.map fun (l, i) => ((i * (spacing + 1)).toFloat, String.ofList (List.replicate l '0')), gap.toFloat), g)

private def neverOverlap : TestCase := .mk "Kept labels never overlap, in order, and are some of the labels" <|
  forAll 3000 genLabels fun (labels, gap) => do
    let r := layoutLabels measure gap labels
    check (r.kept.length ≤ labels.length) "more kept than given"
    check (labels.isEmpty || !r.kept.isEmpty) "nothing kept"
    check (r.kept.all fun l => labels.contains l) "kept a label that was not given"
    for (a, b) in r.kept.zip r.kept.tail do
      let ea := alongAxis r.rotation a.2
      let eb := alongAxis r.rotation b.2
      check (a.1 + ea / 2 + gap ≤ b.1 - eb / 2) s!"{a} overlaps {b} at {repr r.stride}"

private def keepsAllWhenRoomy : TestCase := .mk "Labels with room are all kept, unrotated" <|
  do
    let labels := (List.range 6).map fun i => ((i * 100).toFloat, "1234")
    let r := layoutLabels measure 4 labels
    check (r.kept.length == 6) "dropped"
    check (match r.rotation with | .horizontal => true | _ => false) "rotated"
    check (r.stride == 1) "thinned"

private def rotatesBeforeThinning : TestCase := .mk "Crowded wide labels are rotated rather than thinned" <|
  do
    let labels := (List.range 6).map fun i => ((i * 20).toFloat, "123456789")
    let r := layoutLabels measure 2 labels
    check (r.kept.length == 6) "thinned"
    check (match r.rotation with | .horizontal => false | _ => true) "not rotated"

private def thinsWhenRotationFails : TestCase := .mk "Labels too close even rotated are thinned" <|
  do
    let labels := (List.range 12).map fun i => ((i * 5).toFloat, "12345")
    let r := layoutLabels measure 0 labels
    check (r.stride > 1 && r.kept.length < 12 && !r.kept.isEmpty) s!"{r.kept.length} kept at stride {r.stride}"

private def unusableDropped : TestCase := .mk "A label with no usable measurement is dropped" <|
  do
    let bad (s : String) : Float × Float := if s == "x" then (-1, 12) else if s == "y" then (0.0 / 0.0, 1) else measure s
    let r := layoutLabels bad 0 [(0, "x"), (100, "ok"), (200, "y"), (300, "ok")]
    check (r.kept.map (·.2) == ["ok", "ok"]) s!"{r.kept}"
    check ((layoutLabels measure 0 []).kept.isEmpty) "empty"

private def verticalSpansHeight : TestCase := .mk "A vertical axis thins by height in either order, keeping labels apart" <|
  forAll 3000 genLabels fun (labels, gap) => do
    for ls in [labels, labels.reverse] do
      let (stride, kept) := layoutLabelsVertical measure gap ls
      check (ls.isEmpty || !kept.isEmpty) "nothing kept"
      check (kept.all fun l => ls.contains l) "kept a label that was not given"
      for (a, b) in kept.zip kept.tail do
        check (a.1 + (measure a.2).2 / 2 + gap ≤ b.1 - (measure b.2).2 / 2) s!"{a} overlaps {b} at {stride}"
    let tall := (List.range 13).map fun i => ((i * 20).toFloat, "123456789")
    check ((layoutLabelsVertical measure 2 tall.reverse).2.length == 13) "thinned by width"

def tests : List TestCase :=
  [neverOverlap, keepsAllWhenRoomy, rotatesBeforeThinning, thinsWhenRotationFails, unusableDropped, verticalSpansHeight]

end InkproofAxisTest.LayoutTests
