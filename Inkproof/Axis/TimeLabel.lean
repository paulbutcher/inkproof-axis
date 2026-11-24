/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Core.Calendar
import Inkproof.Core.Decimal

namespace Inkproof.Axis

open Inkproof.Core.Calendar Inkproof.Core.Decimal

/-- What a time-axis label shows: a clock time, a calendar date, or a whole month. -/
inductive TimeLabel where
  | clock (hour minute : Nat) (second : Option Nat)
  | date (month day : Nat)
  | month (month : Nat)
  deriving DecidableEq, Repr

/-- The label of the tick at `t` seconds after 1970-01-01T00:00:00 UTC on an axis whose ticks are `step` seconds apart. Seconds are shown when the step is not a whole number of minutes. A tick that starts a day (a month, for steps of a day or more) shows its date instead of a time, as the first tick of a new day or month. -/
def timeLabel (step : Nat) (t : Int) : TimeLabel :=
  let c := civilFromDays (t / 86400)
  let m := c.2.1
  let d := c.2.2
  let s := (t % 86400).toNat
  if 86400 ≤ step then (if d = 1 then .month m else .date m d)
  else if s = 0 then .date m d
  else .clock (s / 3600) (s / 60 % 60) (if 0 < step ∧ step % 60 = 0 then none else some (s % 60))

/-- The year-independent facts the label states about the tick at `t`: its clock fields, or a calendar date the tick falls on. -/
def TimeLabel.Shows (t : Int) : TimeLabel → Prop
  | .clock h m s => h = (t % 86400).toNat / 3600 ∧ m = (t % 86400).toNat / 60 % 60 ∧
      ∀ x, s = some x → x = (t % 86400).toNat % 60
  | .date m d => ∃ y, daysFromCivil y m d = t / 86400
  | .month m => ∃ y, daysFromCivil y m 1 = t / 86400

/-- The fields of a label fit the two digits or the month names its text gives them. -/
def TimeLabel.WF : TimeLabel → Prop
  | .clock h m s => h < 24 ∧ m < 60 ∧ ∀ x, s = some x → x < 60
  | .date m d => 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ 31
  | .month m => 1 ≤ m ∧ m ≤ 12

/-- Twelve distinct month names, none containing a space or a colon. Labels parse back only for such names. -/
def MonthNames.Valid (months : List String) : Prop :=
  months.length = 12 ∧ (months.map String.toList).Nodup ∧
    ∀ s ∈ months, ∀ c ∈ s.toList, c ≠ ' ' ∧ c ≠ ':'

/-- The two low decimal digits of `n`, most significant first. -/
def twoDigits (n : Nat) : List Char := (lsDigits n 2).reverse.map Nat.digitChar

def monthName (months : List String) (m : Nat) : List Char := (months.getD (m - 1) "").toList

/-- The text of a label, with month `m` (1 for January) named `months[m - 1]`. -/
def TimeLabel.render (months : List String) : TimeLabel → List Char
  | .clock h m none => twoDigits h ++ ':' :: twoDigits m
  | .clock h m (some s) => twoDigits h ++ ':' :: twoDigits m ++ ':' :: twoDigits s
  | .date m d => monthName months m ++ ' ' :: formatDecimal 0 d
  | .month m => monthName months m

/-- How a clock time is written: `h24` as 04:00 or 16:30, `h12` as 4am or 4:30pm with the given morning and afternoon marks (which belong to the locale). -/
inductive ClockStyle where
  | h24
  | h12 (am pm : String)

/-- How a calendar date is written: `named` as Mar 29, or `numeric` as 3/29 (3/29/20 with a year) with the given separator, the day first when `dayFirst`. -/
inductive DateStyle where
  | named
  | numeric (sep : Char) (dayFirst : Bool)

/-- The writing of the labels of a time axis: its clock times, its calendar dates, and the dates of its context lines (which also carry the two-digit year when numeric). -/
structure TimeStyle where
  clock : ClockStyle := .h24
  date : DateStyle := .named
  contextDate : DateStyle := .named

/-- The hour on a 12-hour clock, 1 to 12. -/
def hour12 (h : Nat) : Nat := if h % 12 = 0 then 12 else h % 12

/-- A month and day written as digits in the order and with the separator the style gives. -/
def numericDate (sep : Char) (dayFirst : Bool) (m d : Nat) : List Char :=
  if dayFirst then formatDecimal 0 d ++ sep :: formatDecimal 0 m else formatDecimal 0 m ++ sep :: formatDecimal 0 d

/-- The text of a label in the given style, with month `m` (1 for January) named `months[m - 1]` where the style names months. -/
def TimeLabel.renderWith (style : TimeStyle) (months : List String) : TimeLabel → List Char
  | .clock h m s =>
    match style.clock with
    | .h24 => TimeLabel.render months (.clock h m s)
    | .h12 am pm =>
      let mark := (if h < 12 then am else pm).toList
      match s with
      | none => if m = 0 then formatDecimal 0 (hour12 h) ++ mark else formatDecimal 0 (hour12 h) ++ ':' :: twoDigits m ++ mark
      | some s => formatDecimal 0 (hour12 h) ++ ':' :: twoDigits m ++ ':' :: twoDigits s ++ mark
  | .date m d =>
    match style.date with
    | .named => TimeLabel.render months (.date m d)
    | .numeric sep dayFirst => numericDate sep dayFirst m d
  | .month m =>
    match style.date with
    | .named => TimeLabel.render months (.month m)
    | .numeric .. => formatDecimal 0 m

/-- The number written by two digit characters. -/
def twoValue (a b : Char) : Option Nat :=
  if a.isDigit && b.isDigit then some (digitsValue [a, b]) else none

def parseClock : List Char → Option TimeLabel
  | [a, b, ':', c, d] => do pure (.clock (← twoValue a b) (← twoValue c d) none)
  | [a, b, ':', c, d, ':', e, f] => do pure (.clock (← twoValue a b) (← twoValue c d) (some (← twoValue e f)))
  | _ => none

def monthOf (months : List String) (name : List Char) : Option Nat :=
  let i := (months.map String.toList).idxOf name
  if i < months.length then some (i + 1) else none

/-- Reads the text of a label back, or `none` if it is not one. -/
def parseTimeLabel (months : List String) (cs : List Char) : Option TimeLabel :=
  if ':' ∈ cs then parseClock cs
  else match splitAtChar ' ' cs with
    | (name, some ds) => do
      let m ← monthOf months name
      match parseDecimal ds with
      | some (d, 0) => if 0 ≤ d then some (.date m d.toNat) else none
      | _ => none
    | (name, none) => (monthOf months name).map .month

/-- Labels for ticks given in seconds after 1970-01-01T00:00:00 UTC and spaced `step` seconds apart; the month names, which carry the locale, come from the caller. -/
def timeLabels (months : List String) (step : Nat) (ticks : List Int) : List String :=
  ticks.map fun t => String.ofList ((timeLabel step t).render months)

/-- `timeLabels` for ticks and a step in float seconds, as `durationTicks` returns them (the step rounds down to a whole number of seconds). No labels if a tick is not a finite number of seconds below 10 ^ 15 in size. -/
def timeTickLabels (months : List String) (step : Float) (ticks : List Float) : List String :=
  if ticks.all fun t => t.isFinite && t.abs < 1e15 && step.isFinite && 0 ≤ step && step < 1e15 then
    timeLabels months step.floor.toUInt64.toNat (ticks.map fun t => t.floor.toInt64.toInt)
  else []

/-- The line a host draws under the label of the tick at `t`, given the previous tick `prev` (none for the first): the year where a date or month label starts a new year, or is first; the date where a clock label starts a new day, or is first. -/
def timeContext (months : List String) (step : Nat) (prev : Option Int) (t : Int) : Option String :=
  let c := civilFromDays (t / 86400)
  let p := prev.map fun q => civilFromDays (q / 86400)
  match timeLabel step t with
  | .clock .. => if p.map (·.2) = some c.2 then none else some (String.ofList ((TimeLabel.date c.2.1 c.2.2).render months))
  | _ => if p.map (·.1) = some c.1 then none else some (toString c.1)

/-- `timeContext` of each tick, for ticks as `timeLabels` takes them. -/
def timeContexts (months : List String) (step : Nat) (ticks : List Int) : List (Option String) :=
  (ticks.zip (none :: ticks.map some)).map fun (t, p) => timeContext months step p t

/-- `timeLabels` with the writing of `style`. -/
def timeLabelsWith (style : TimeStyle) (months : List String) (step : Nat) (ticks : List Int) : List String :=
  ticks.map fun t => String.ofList ((timeLabel step t).renderWith style months)

/-- `timeContext` with the writing of `style`: a numeric context date is month, day and the two-digit year. -/
def timeContextWith (style : TimeStyle) (months : List String) (step : Nat) (prev : Option Int) (t : Int) : Option String :=
  let c := civilFromDays (t / 86400)
  let p := prev.map fun q => civilFromDays (q / 86400)
  match timeLabel step t with
  | .clock .. =>
    if p.map (·.2) = some c.2 then none
    else match style.contextDate with
      | .named => some (String.ofList ((TimeLabel.date c.2.1 c.2.2).render months))
      | .numeric sep dayFirst => some (String.ofList (numericDate sep dayFirst c.2.1 c.2.2 ++ sep :: twoDigits (c.1 % 100).toNat))
  | _ => if p.map (·.1) = some c.1 then none else some (toString c.1)

/-- `timeContextWith` of each tick, for ticks as `timeLabels` takes them. -/
def timeContextsWith (style : TimeStyle) (months : List String) (step : Nat) (ticks : List Int) : List (Option String) :=
  (ticks.zip (none :: ticks.map some)).map fun (t, p) => timeContextWith style months step p t

end Inkproof.Axis
