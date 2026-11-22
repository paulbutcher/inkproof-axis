/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std.Time

namespace Inkproof.Axis

open Std.Time

/-- Seconds east of UTC at a unix second under a parsed POSIX TZ rule. -/
def PosixZone.offsetAt (rule : TimeZone.RecurringRule) (t : Int) : Int :=
  (rule.timezoneAt (Timestamp.ofSecondsSinceUnixEpoch (Second.Offset.ofInt t))).offset.second.val

/-- The offset function of a POSIX TZ rule such as `CET-1CEST,M3.5.0,M10.5.0/3`, for `monthTicks`, `durationTicksAt` and `timeTickLabelsAt`; an error if the rule does not parse. -/
def posixZone (rule : String) : Except String (Int → Int) :=
  (TimeZone.parsePosixTz rule).map PosixZone.offsetAt

theorem PosixZone.offsetAt_eq (rule : TimeZone.RecurringRule) (t : Int) :
    PosixZone.offsetAt rule t =
      (rule.timezoneAt (Timestamp.ofSecondsSinceUnixEpoch (Second.Offset.ofInt t))).offset.second.val :=
  rfl

theorem posixZone_eq (rule : String) :
    posixZone rule = (TimeZone.parsePosixTz rule).map
      fun r t => (r.timezoneAt (Timestamp.ofSecondsSinceUnixEpoch (Second.Offset.ofInt t))).offset.second.val :=
  rfl

end Inkproof.Axis
