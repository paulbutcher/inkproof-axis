/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Axis
import InkproofTools.Test.Platform
import InkproofAxisTest.ClockTickTests
import InkproofAxisTest.PosixZoneTests
import InkproofAxisTest.LabelTests
import InkproofAxisTest.LayoutTests
import InkproofAxisTest.MonthTickTests
import InkproofAxisTest.TickTests
import InkproofAxisTest.TimeLabelTests

open InkproofAxisTest InkproofTools.Test

def main (args : List String) : IO UInt32 :=
  runTests (platformTest (args.contains "--expect-wasm") :: TickTests.tests ++ ClockTickTests.tests ++ LabelTests.tests ++ LayoutTests.tests ++ MonthTickTests.tests ++ PosixZoneTests.tests ++ TimeLabelTests.tests)
