/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis
import Inkproof.Axis.Proofs

/-! The theorems apply to `Rat` with every hypothesis discharged, so a real caller can meet them. -/

namespace InkproofAxisTest.RatTests

open Inkproof.Axis Inkproof.Axis.Proofs

theorem ratFloor : IsFloor (fun q : Rat => q.floor) := fun q => ⟨by exact_mod_cast Rat.floor_le q, by exact_mod_cast Rat.lt_floor_add_one q⟩

theorem ratTicksValid (lo hi step : Rat) (hs : 0 < step) :
    Ticks.Valid lo hi (Grid.cover (fun q : Rat => q.floor) lo hi step).values = true :=
  cover_valid ratFloor hs

theorem ratCategoricalMem (n : Nat) (lo hi : Rat) {stride : Nat} (hs : 0 < stride) {x : Nat}
    (hx : x ∈ categoricalTicks (fun q : Rat => q.floor) n lo hi stride) :
    x < n ∧ lo ≤ ((x : Int) : Rat) ∧ ((x : Int) : Rat) ≤ hi :=
  categoricalTicks_mem ratFloor n lo hi hs hx

end InkproofAxisTest.RatTests
