/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.NumberFormat

namespace Inkproof.Axis

/-- Labels for ticks at the fewest decimals that show every tick and keep adjacent labels distinct, or none when no precision up to 15 decimals does (ticks too fine or too large for a float to carry). -/
def tickLabels (loc : Locale) (ts : List Float) : List String :=
  ({ locale := loc : NumberFormat }).formatAll ts

end Inkproof.Axis
