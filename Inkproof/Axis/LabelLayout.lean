/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Layout

namespace Inkproof.Axis

/-- Which of the labels at positions along the axis to show, and how to turn them, given the host's measurement of a label as its width and height. Rule: the rotation that keeps the most labels wins, the least rotation among equals, and labels are thinned to every `k`th at the least `k` that leaves `gap` between neighbours. A label whose measurement is negative or not a number cannot be placed and is dropped, as is a negative or non-numeric gap taken as zero. -/
def layoutLabels (measure : String → Float × Float) (gap : Float) (labels : List (Float × String)) :
    Layout (Float × String) :=
  letI : IntCast Float := ⟨Float.ofInt⟩
  let usable (l : Float × String) := let (w, h) := measure l.2; 0 ≤ w && 0 ≤ h && w.isFinite && h.isFinite
  let spans (r : Rotation) (l : Float × String) : Span Float :=
    let (w, h) := measure l.2
    Span.centred l.1 (r.extent 0.7071067811865476 w h)
  layout spans (if 0 ≤ gap then gap else 0) (labels.filter usable)

/-- Which of the labels at positions along a vertical axis to show, given the host's measurement of a label as its width and height. Labels are unrotated and span their height; positions may run in either direction, and the labels kept are in ascending position order with their stride. Unusable measurements and gaps are treated as in `layoutLabels`. -/
def layoutLabelsVertical (measure : String → Float × Float) (gap : Float) (labels : List (Float × String)) :
    Nat × List (Float × String) :=
  letI : IntCast Float := ⟨Float.ofInt⟩
  let usable (l : Float × String) := let (w, h) := measure l.2; 0 ≤ w && 0 ≤ h && w.isFinite && h.isFinite
  let span (l : Float × String) : Span Float := Span.centred l.1 (measure l.2).2
  thinSorted span (if 0 ≤ gap then gap else 0) (labels.filter usable)

end Inkproof.Axis
