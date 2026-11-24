/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Grid
import Inkproof.Axis.Decade
import Inkproof.Axis.Categorical

namespace Inkproof.Axis

private def floorInt (x : Float) : Int := x.floor.toInt64.toInt

/-- A step of 1, 2, 5 or 10 times a power of ten, about `span / target` long. -/
def niceStep (span : Float) (target : Nat) : Float :=
  let raw := span / (max target 1).toFloat
  let p := Float.pow 10 raw.log10.floor
  let f := raw / p
  (if f < 1.5 then 1 else if f < 3 then 2 else if f < 7 then 5 else 10) * p

/-- Lengths in seconds that read naturally as clock and calendar intervals. -/
def durationSteps : List Float :=
  [1, 2, 5, 10, 15, 30, 60, 120, 300, 600, 900, 1800, 3600, 7200, 10800, 21600, 43200, 86400, 172800, 604800]

/-- The shortest entry of `durationSteps` at least `span / target`; below a second, a power-of-ten step, and above the table a power-of-ten number of days. -/
def durationStep (span : Float) (target : Nat) : Float :=
  let raw := span / (max target 1).toFloat
  if raw < 1 then niceStep span target
  else match durationSteps.find? (raw ≤ ·) with
    | some s => s
    | none => niceStep (span / 86400) target * 86400

def ordered (lo hi : Float) : Option (Float × Float) :=
  let (lo, hi) := if hi < lo then (hi, lo) else (lo, hi)
  if lo.isFinite && hi.isFinite && lo < hi then some (lo, hi) else none

private def maxTicks : Nat := 100000

/-- The multiples of `step` in `[lo, hi]`, or no ticks unless the list is strictly increasing and within the interval, which floats cannot always deliver (a step below the spacing of floats at `hi`). -/
private def gridTicks (lo hi step : Float) : List Float :=
  if step.isFinite && 0 < step then
    letI : IntCast Float := ⟨Float.ofInt⟩
    let g := Grid.cover floorInt lo hi step
    let ts := g.values
    if g.count ≤ maxTicks && Ticks.Valid lo hi ts then ts else []
  else []

/-- Ticks for a linear scale over the visible range between `lo` and `hi`, about `target` of them, at multiples of a 1, 2 or 5 times a power of ten. A reversed range is read as its ascending interval; an empty or non-finite range has no ticks. -/
def linearTicks (lo hi : Float) (target : Nat) : List Float :=
  match ordered lo hi with
  | some (lo, hi) => gridTicks lo hi (niceStep (hi - lo) target)
  | none => []

/-- Ticks for an elapsed-duration scale over a visible range in seconds, at natural clock intervals. -/
def durationTicks (lo hi : Float) (target : Nat) : List Float :=
  match ordered lo hi with
  | some (lo, hi) => gridTicks lo hi (durationStep (hi - lo) target)
  | none => []

/-- The logarithm in base `b`, exact at powers of two and of ten. -/
def logBase (b : Nat) (x : Float) : Float :=
  if b == 2 then x.log2 else if b == 10 then x.log10 else x.log / b.toFloat.log

/-- `b ^ e`. -/
def powBase (b : Nat) (e : Int) : Float := Float.pow b.toFloat (Float.ofInt e)

/-- Ticks for a log scale of base `base` over the positive range `[lo, hi]`: powers of `base`, every `k`th when there are more than `target`. A range holding fewer than two powers falls back to `linearTicks`, and one reaching zero or below, or a base below 2, has none. -/
def logTicksIn (base : Nat) (lo hi : Float) (target : Nat) : List Float :=
  match ordered lo hi with
  | some (lo, hi) =>
    if lo ≤ 0 || base < 2 then []
    else
      letI : IntCast Float := ⟨Float.ofInt⟩
      letI : NatCast Float := ⟨fun n => n.toFloat⟩
      let decades := logBase base hi - logBase base lo
      let stride := (decades / (max target 1).toFloat).ceil.toUInt64.toNat |> max 1
      let ts := decadeTicks floorInt (logBase base) (powBase base) lo hi stride
      if ts.length ≥ 2 && Ticks.Valid lo hi ts then ts else linearTicks lo hi target
  | none => []

/-- Ticks for a log scale over the positive range `[lo, hi]`: powers of ten, every `k`th when there are more than `target`. A range holding fewer than two powers of ten falls back to `linearTicks`, and one reaching zero or below has none. -/
def logTicks (lo hi : Float) (target : Nat) : List Float := logTicksIn 10 lo hi target

/-- Where within each power of the base a log axis is ticked: at powers only, at 1, 2 and 5, or at every integer from 1 below the base. -/
inductive LogMultiples where
  | decades
  | oneTwoFive
  | integers

/-- The multiples of a power of `base` that `m` ticks, ascending: those of 1, 2 and 5, or of 1 to 9, below the base. -/
def LogMultiples.mantissasIn (base : Nat) : LogMultiples → List Nat
  | .decades => [1]
  | .oneTwoFive => [1, 2, 5].filter (· < base)
  | .integers => (List.range (base - 1)).map (· + 1)

/-- The multiples of a power of ten that `m` ticks, ascending. -/
def LogMultiples.mantissas (m : LogMultiples) : List Nat := m.mantissasIn 10

/-- Ticks for a log scale of base `base` over `[lo, hi]` at the multiples `m` of each power of the base, as `logTicksIn` does for `.decades`. When the range spans more than `target` powers they thin to powers as `logTicksIn` does, and when fewer than two multiples fall inside they fall back to `linearTicks`. For minor ticks apart from the labelled ones, see `logMinorTicksIn`. -/
def logTicksAtIn (base : Nat) (m : LogMultiples) (lo hi : Float) (target : Nat) : List Float :=
  match m, ordered lo hi with
  | .decades, _ => logTicksIn base lo hi target
  | _, none => []
  | _, some (lo, hi) =>
    if lo ≤ 0 || base < 2 then []
    else if logBase base hi - logBase base lo > (max target 1).toFloat then logTicksIn base lo hi target
    else
      let ts := multipleTicks (powBase base) ((m.mantissasIn base).map Nat.toFloat) lo hi
        (floorInt (logBase base lo) - 1) (floorInt (logBase base hi) + 1)
      if ts.length ≥ 2 && Ticks.Valid lo hi ts then ts else linearTicks lo hi target

/-- `logTicksAtIn` in base ten. -/
def logTicksAt (m : LogMultiples) (lo hi : Float) (target : Nat) : List Float := logTicksAtIn 10 m lo hi target

/-- The minor ticks of a log axis of base `base` whose labelled ticks are at the multiples `m`: those at every integer multiple of a power of the base that the labelled ticks lack, ascending. None where the labelled ticks are already every integer multiple, as for base 2, or thinned to powers. -/
def logMinorTicksIn (base : Nat) (m : LogMultiples) (lo hi : Float) (target : Nat) : List Float :=
  let labelled := logTicksAtIn base m lo hi target
  (logTicksAtIn base .integers lo hi target).filter fun t => !labelled.contains t

/-- `logMinorTicksIn` in base ten. -/
def logMinorTicks (m : LogMultiples) (lo hi : Float) (target : Nat) : List Float := logMinorTicksIn 10 m lo hi target

/-- `ps` negated and reversed, then zero, then `ps`: the ticks of a symmetric axis from those of its positive side. -/
def mirrorAboutZero {α : Type} [Neg α] [OfNat α 0] (ps : List α) : List α :=
  (ps.map (-·)).reverse ++ 0 :: ps

/-- Ticks for a symmetric log or arcsinh scale over the visible range between `lo` and `hi`: zero, the `logTicks` of `[linthresh, m]` with `m` the larger magnitude of the range's ends, and their negatives, kept where they fall within the range. `linthresh` is the magnitude below which the scale is roughly linear; if it is not positive, only zero is ticked. -/
def symlogTicks (lo hi linthresh : Float) (target : Nat) : List Float :=
  match ordered lo hi with
  | some (lo, hi) =>
    let m := max (-lo) hi
    (mirrorAboutZero (logTicks linthresh m target)).filter fun t => lo ≤ t && t ≤ hi
  | none => []

/-- The category indices to label for a categorical scale with `n` categories, band `i` at position `i`, over the visible range `[lo, hi]`: every `k`th, with `k` the least stride that gives at most `target`. -/
def categoricalIndices (n : Nat) (lo hi : Float) (target : Nat) : List Nat :=
  match ordered lo hi with
  | some (lo, hi) =>
    letI : IntCast Float := ⟨Float.ofInt⟩
    let visible := (min hi (n.toFloat - 1) - max lo 0).floor + 1
    let stride := (visible / (max target 1).toFloat).ceil.toUInt64.toNat |> max 1
    categoricalTicks floorInt n lo hi stride
  | none => []

end Inkproof.Axis
