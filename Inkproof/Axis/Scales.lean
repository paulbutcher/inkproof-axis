/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.Ticks
import Inkproof.Scale

universe u

namespace Inkproof.Axis

open Inkproof.Scale

/-- Ticks over the visible domain of a linear scale. -/
def linearScaleTicks (s : Linear Float) (target : Nat) : List Float :=
  linearTicks s.domainStart s.domainEnd target

/-- Ticks over the visible domain of a scale of elapsed seconds (`Linear.ofDurations`). -/
def durationScaleTicks (s : Linear Float) (target : Nat) : List Float :=
  durationTicks s.domainStart s.domainEnd target

/-- Ticks over the visible domain of a log scale, which holds data values rather than their logarithms. -/
def logScaleTicks (s : Log Float) (target : Nat) : List Float :=
  logTicks s.domainStart s.domainEnd target

/-- The categories to label over `[lo, hi]`, in band index units, the visible part of a categorical scale. -/
def categoricalScaleTicks {κ : Type u} (s : Categorical κ Float) (lo hi : Float) (target : Nat) : List κ :=
  (categoricalIndices s.categories.size lo hi target).filterMap (s.categories[·]?)

end Inkproof.Axis
