/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

universe u v

namespace Inkproof.Axis

/-- The interval a label occupies along the axis. -/
structure Span (α : Type u) where
  lo : α
  hi : α

inductive Rotation where
  | horizontal
  | diagonal
  | vertical

namespace Rotation

/-- The length along the axis of a `w` by `h` label turned by this rotation; `c` is the cosine of 45 degrees. -/
def extent {α : Type u} [Add α] [Mul α] (c : α) : Rotation → α → α → α
  | horizontal, w, _ => w
  | diagonal, w, h => (w + h) * c
  | vertical, _, h => h

end Rotation

/-- A label centred at `pos` with length `ext` along the axis. -/
def Span.centred {α : Type u} [IntCast α] [Add α] [Sub α] [Div α] (pos ext : α) : Span α :=
  ⟨pos - ext / ((2 : Int) : α), pos + ext / ((2 : Int) : α)⟩

/-- Every `k`th element from the first; every element when `k` is at most one. -/
def everyNth {β : Type v} (k : Nat) : List β → List β
  | [] => []
  | x :: xs => x :: everyNth k (xs.drop (k - 1))
termination_by l => l.length
decreasing_by simp; omega

/-- Whether each element's span ends at least `gap` before the next one starts. -/
def clearChain {α : Type u} {β : Type v} [Add α] [LE α] [DecidableLE α] (span : β → Span α) (gap : α) :
    List β → Bool
  | a :: b :: rest => decide ((span a).hi + gap ≤ (span b).lo) && clearChain span gap (b :: rest)
  | _ => true

/-- The elements at the least stride that leaves a gap between neighbours, and that stride; only the first element if no stride does. -/
def thin {α : Type u} {β : Type v} [Add α] [LE α] [DecidableLE α] (span : β → Span α) (gap : α)
    (items : List β) : Nat × List β :=
  match (List.range items.length).find? fun i => clearChain span gap (everyNth (i + 1) items) with
  | some i => (i + 1, everyNth (i + 1) items)
  | none => (items.length, items.take 1)

structure Layout (β : Type v) where
  rotation : Rotation
  stride : Nat
  kept : List β

/-- Keeps as many labels as fit with `gap` between neighbours: the rotation with the least stride wins, and a tie goes to the least rotation. `spans r` gives the span of a label turned by `r`. -/
def layout {α : Type u} {β : Type v} [Add α] [LE α] [DecidableLE α] (spans : Rotation → β → Span α) (gap : α)
    (items : List β) : Layout β :=
  let at_ (r : Rotation) : Layout β :=
    ⟨r, (thin (spans r) gap items).1, (thin (spans r) gap items).2⟩
  let a := at_ .horizontal
  let b := at_ .diagonal
  let c := at_ .vertical
  if b.stride < a.stride then (if c.stride < b.stride then c else b)
  else if c.stride < a.stride then c else a

end Inkproof.Axis
