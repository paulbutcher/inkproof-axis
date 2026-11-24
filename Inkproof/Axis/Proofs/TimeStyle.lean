/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.ClockTicks
import Inkproof.Axis.Proofs.TimeLabel

namespace Inkproof.Axis.Proofs

open Inkproof.Axis Inkproof.Core.Decimal

theorem renderWith_default (months : List String) (l : TimeLabel) :
    l.renderWith {} months = l.render months := by
  cases l <;> rfl

theorem timeLabelsWith_default (months : List String) (step : Nat) (ticks : List Int) :
    timeLabelsWith {} months step ticks = timeLabels months step ticks := by
  simp [timeLabelsWith, timeLabels, renderWith_default]

theorem timeLabelsAtWith_default (off : Int → Int) (months : List String) (step : Nat) (ticks : List Int) :
    timeLabelsAtWith {} off months step ticks = timeLabelsAt off months step ticks :=
  timeLabelsWith_default ..

theorem timeTickLabelsAtWith_default (off : Int → Int) (months : List String) (step : Float) (ticks : List Float) :
    timeTickLabelsAtWith {} off months step ticks = timeTickLabelsAt off months step ticks := by
  simp [timeTickLabelsAtWith, timeTickLabelsAt, timeLabelsAtWith_default]

theorem timeContextWith_default (months : List String) (step : Nat) (prev : Option Int) (t : Int) :
    timeContextWith {} months step prev t = timeContext months step prev t := by
  unfold timeContextWith timeContext
  rfl

theorem timeContextsWith_default (months : List String) (step : Nat) (ticks : List Int) :
    timeContextsWith {} months step ticks = timeContexts months step ticks := by
  simp [timeContextsWith, timeContexts, timeContextWith_default]

theorem hour12_pos (h : Nat) : 1 ≤ hour12 h := by
  unfold hour12; split <;> omega

theorem hour12_le (h : Nat) : hour12 h ≤ 12 := by
  unfold hour12; split <;> omega

theorem hour12_of_lt (h : Nat) (h1 : 0 < h) (h2 : h < 12) : hour12 h = h := by
  unfold hour12; split <;> omega

private def twelve : TimeStyle := { clock := .h12 "am" "pm" }

private def numeric : TimeStyle := { date := .numeric '/' false }

theorem render_h12_on_the_hour : (TimeLabel.clock 3 0 none).renderWith twelve [] = "3am".toList := by decide +kernel

theorem render_h12_afternoon : (TimeLabel.clock 15 30 none).renderWith twelve [] = "3:30pm".toList := by decide +kernel

theorem render_h12_midnight : (TimeLabel.clock 0 0 none).renderWith twelve [] = "12am".toList := by decide +kernel

theorem render_h12_noon : (TimeLabel.clock 12 0 none).renderWith twelve [] = "12pm".toList := by decide +kernel

theorem render_h12_seconds : (TimeLabel.clock 15 30 (some 5)).renderWith twelve [] = "3:30:05pm".toList := by decide +kernel

theorem render_numeric_date : (TimeLabel.date 3 29).renderWith numeric [] = "3/29".toList := by decide +kernel

theorem render_numeric_date_dayFirst :
    (TimeLabel.date 3 29).renderWith { date := .numeric '.' true } [] = "29.3".toList := by decide +kernel

theorem render_numeric_month : (TimeLabel.month 3).renderWith numeric [] = "3".toList := by decide +kernel

/-- The label of the tick at 2020-03-29 03:00 UTC on an hourly axis, in 12-hour style. -/
theorem timeLabelsWith_hourly_example :
    timeLabelsWith twelve [] 3600 [1585450800] = ["3am"] := by decide +kernel

/-- The context line of that tick, the first, as a short date. -/
theorem timeContextWith_short_example :
    timeContextWith { contextDate := .numeric '/' false } [] 3600 none 1594958400 = some "7/17/20" := by decide +kernel

theorem durationStepSpaced_of_find (span extent spacing step : Float)
    (hr : (span * spacing / extent).isFinite && 0 < span * spacing / extent)
    (h1 : ¬ span * spacing / extent < 1)
    (h : durationSteps.find? (span * spacing / extent ≤ ·) = some step) :
    durationStepSpaced span extent spacing = some step := by
  simp [durationStepSpaced, hr, h1, h]

/-- The step found in the table of clock intervals reaches the length that keeps ticks the spacing apart. -/
theorem durationStepSpaced_ge_of_find (span extent spacing step : Float)
    (h : durationSteps.find? (span * spacing / extent ≤ ·) = some step) :
    span * spacing / extent ≤ step := by
  simpa using List.find?_some h

theorem durationStepSpaced_of_lt_one (span extent spacing : Float)
    (hr : (span * spacing / extent).isFinite && 0 < span * spacing / extent)
    (h1 : span * spacing / extent < 1) :
    durationStepSpaced span extent spacing = spacedStep [1, 2, 5] span extent spacing := by
  simp [durationStepSpaced, hr, h1]

theorem durationStepSpaced_none (span extent spacing : Float)
    (h : ¬ ((span * spacing / extent).isFinite && 0 < span * spacing / extent)) :
    durationStepSpaced span extent spacing = none := by
  simp [durationStepSpaced, h]

theorem numericDate_eq (sep : Char) (dayFirst : Bool) (m d : Nat) :
    numericDate sep dayFirst m d =
      if dayFirst then formatDecimal 0 d ++ sep :: formatDecimal 0 m else formatDecimal 0 m ++ sep :: formatDecimal 0 d := rfl

theorem timeContextsAtWith_eq (style : TimeStyle) (off : Int → Int) (months : List String) (step : Nat) (ticks : List Int) :
    timeContextsAtWith style off months step ticks = timeContextsWith style months step (ticks.map fun t => t + off t) := rfl

theorem timeTickContextsAtWith_eq (style : TimeStyle) (off : Int → Int) (months : List String) (step : Float)
    (ticks : List Float) :
    timeTickContextsAtWith style off months step ticks =
      if ticks.all (fun t => t.isFinite && t.abs < 1e15 && step.isFinite && 0 ≤ step && step < 1e15) then
        timeContextsAtWith style off months step.floor.toUInt64.toNat (ticks.map fun t => t.floor.toInt64.toInt)
      else [] := rfl

theorem durationTicksAtSpaced_eq (off : Int → Int) (lo hi extent spacing : Float) :
    durationTicksAtSpaced off lo hi extent spacing =
      match ordered lo hi, durationStepSpaced (hi - lo) extent spacing with
      | some (a, b), some step =>
        if a.abs < 1e15 && b.abs < 1e15 && 1 ≤ step && step < 1e15 then
          (step, (clockTicks off step.floor.toUInt64.toNat a.ceil.toInt64.toInt b.floor.toInt64.toInt).map Float.ofInt)
        else (step, [])
      | _, _ => (0, []) := rfl

end Inkproof.Axis.Proofs
