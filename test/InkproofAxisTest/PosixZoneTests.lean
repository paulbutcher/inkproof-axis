/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis.PosixZone
import InkproofTools.Test.Harness

namespace InkproofAxisTest.PosixZoneTests

open InkproofTools.Test
open Inkproof.Axis

private def berlin : TestCase := .mk "A CET rule is an hour ahead in winter and two in summer" <|
  do
    match posixZone "CET-1CEST,M3.5.0,M10.5.0/3" with
    | .error e => check false e
    | .ok f =>
      check (f 1704067200 == 3600) s!"{f 1704067200}"
      check (f 1719792000 == 7200) s!"{f 1719792000}"
      check (f 1711846799 == 3600 ∧ f 1711846800 == 7200) "change at 01:00Z on the last Sunday of March"

private def noDst : TestCase := .mk "A rule without daylight saving is constant" <|
  do
    match posixZone "IST-5:30" with
    | .error e => check false e
    | .ok f => check (f 0 == 19800 ∧ f 1719792000 == 19800) "offset"

private def rejects : TestCase := .mk "A malformed rule is an error" <|
  check (match posixZone "" with | .error _ => true | .ok _ => false) "empty rule accepted"

def tests : List TestCase := [berlin, noDst, rejects]

end InkproofAxisTest.PosixZoneTests
