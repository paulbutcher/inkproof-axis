/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Inkproof.Core.Decimal

universe u

namespace Inkproof.Axis

open Inkproof.Core.Decimal

/-- How a locale writes numbers. Grouping inserts `group` between runs of `groupSize` integer digits, counted from the right. -/
structure Locale where
  decimal : Char
  group : Option Char
  groupSize : Nat
  minus : Char

namespace Locale

/-- The separators and minus sign are not digits, grouping has a size, and the grouping character differs from the decimal one and the minus sign. Labels parse back only for such locales. -/
def Valid (l : Locale) : Prop :=
  ¬ l.decimal.isDigit ∧ ¬ l.minus.isDigit ∧
    ∀ g, l.group = some g → ¬ g.isDigit ∧ g ≠ l.decimal ∧ g ≠ l.minus ∧ 0 < l.groupSize

def en : Locale := ⟨'.', some ',', 3, '-'⟩

def de : Locale := ⟨',', some '.', 3, '-'⟩

/-- French style: a narrow no-break space groups and the decimal separator is a comma. -/
def fr : Locale := ⟨',', some '\u202F', 3, '-'⟩

/-- Unicode minus sign, no grouping. -/
def plain : Locale := ⟨'.', none, 3, '−'⟩

end Locale

/-- Puts `g` between runs of `k` characters, from the front. -/
def groupRuns (g : Char) (k : Nat) (l : List Char) : List Char :=
  if _h : 0 < k ∧ k < l.length then l.take k ++ g :: groupRuns g k (l.drop k) else l
termination_by l.length
decreasing_by simp only [List.length_drop]; omega

/-- Groups integer digits given least significant first. -/
def groupWhole (loc : Locale) (whole : List Char) : List Char :=
  match loc.group with
  | some g => groupRuns g loc.groupSize whole
  | none => whole

/-- The label of the number `n / 10 ^ p`, written with `p` decimals. -/
def formatChars (loc : Locale) (p : Nat) (n : Int) : List Char :=
  let ds := scaledDigits p n.natAbs
  let whole := groupWhole loc (ds.drop p |>.map Nat.digitChar)
  let frac := ds.take p |>.map Nat.digitChar
  (if n < 0 then [loc.minus] else []) ++ whole.reverse ++
    (if p = 0 then [] else loc.decimal :: frac.reverse)

def ungroupWhole (loc : Locale) (whole : List Char) : List Char :=
  match loc.group with
  | some g => whole.filter (· ≠ g)
  | none => whole

/-- Reads a label back as the mantissa `n` and decimals `p` of the number `n / 10 ^ p`, or `none` if it is not one. -/
def parseChars (loc : Locale) (cs : List Char) : Option (Int × Nat) :=
  let (neg, rest) := match cs with
    | c :: r => if c = loc.minus then (true, r) else (false, cs)
    | [] => (false, [])
  let (whole, frac) := splitAtChar loc.decimal rest
  let whole := ungroupWhole loc whole
  let frac := frac.getD []
  if !whole.isEmpty && (whole ++ frac).all Char.isDigit then
    let v : Int := digitsValue (whole ++ frac)
    some (if neg then -v else v, frac.length)
  else none

/-- `x` in units of `10 ^ -p`, rounded to the nearest, given a floor function. -/
def scaled {α : Type u} [IntCast α] [NatCast α] [Mul α] [Add α] [Div α] (fl : α → Int) (p : Nat) (x : α) : Int :=
  fl (x * ((10 ^ p : Nat) : α) + ((1 : Int) : α) / ((2 : Int) : α))

/-- The label of `x` at `p` decimals. -/
def label {α : Type u} [IntCast α] [NatCast α] [Mul α] [Add α] [Div α] (loc : Locale) (fl : α → Int) (p : Nat) (x : α) : String :=
  String.ofList (formatChars loc p (scaled fl p x))

end Inkproof.Axis
