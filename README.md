# Inkproof.Axis

Ticks and labels for chart axes, for every scale kind. Part of Inkproof. Released under the Apache 2.0 license; see `LICENSE`.

The library builds natively and under Lasm from the same source. `lakefile.lean` records the Lean, Inkproof.Scale and Inkproof.Float versions it builds against.

## Using it

```lean
require «inkproof-axis» from git "https://github.com/paulbutcher/inkproof-axis" @ "vX.Y.Z"
```

Replace `vX.Y.Z` with the latest release tag; `CHANGELOG.md` lists the releases.

`import Inkproof.Axis` brings in everything a program runs. `import Inkproof.Axis.Proofs` adds the published theorems, which a browser build need not link.

## What it does

- Choose tick positions for a linear axis: `linearTicks` for a range, `linearScaleTicks` for an `Inkproof.Scale.Linear`; the step comes from `niceStep`.
- Choose a linear axis's step from the pixels wanted between ticks and the multiples a step may take (1, 2, 2.5, 5 as `stepMultiples`): `spacedLinearTicks`, `linearScaleTicksSpaced`, `spacedStep`, over `gridTicks`.
- Choose tick positions for a logarithmic axis, at powers of ten: `logTicks`, `logScaleTicks`, over `decadeTicks` and `decadeExponents`.
- Choose tick positions for a logarithmic axis at 1, 2 and 5 or at every integer within each decade, with the denser set's extra ticks usable as minor gridlines: `logTicksAt` with a `LogMultiples`, `logScaleTicksAt`, over `multipleTicks`.
- Choose tick positions for any scale given by a forward and inverse transform (Weibull, arcsinh, a caller's own), at nice steps in the transformed space mapped back and rounded by a function the caller gives: `transformTicks`, over `mapBack`, `backTicks`, `gridTicks`.
- Choose tick positions for a logarithmic axis in any base, powers of two for base 2, at powers, at 1, 2 and 5 or at every integer multiple, and the minor ticks kept apart from the labelled ones for minor gridlines: `logTicksIn`, `logTicksAtIn`, `logMinorTicksIn` (and `logMinorTicks` in base ten), over `logBase` and `powBase`.
- Write a tick that is a power as plain text, 2^24 or 10^-3: `powerLabel`, `powerLabels`, `powerText`.
- Choose tick positions for a symmetric log or arcsinh axis, zero and powers of ten mirrored about it: `symlogTicks`, over `mirrorAboutZero`.
- Choose tick positions for a categorical (band) axis: `categoricalTicks`, `categoricalIndices`, and `categoricalScaleTicks` for an `Inkproof.Scale.Categorical`.
- Choose tick positions for an elapsed-time axis, at clock intervals from a second to a week: `durationTicks`, `durationScaleTicks`, `durationStep`, `durationSteps`.
- Generate evenly spaced ticks over any ordered field, with spacing, order and range proved: `Grid`, `Grid.cover`, `Grid.values`, `Ticks.Valid`.
- Format tick values as number labels for a locale (decimal separator, digit grouping, minus sign), with the fewest decimals that keep adjacent labels distinct: `tickLabels`, `label`, `scaled`, `formatChars`, `Locale` (`en`, `de`, `fr`, `plain`).
- Write any number as text in a locale, with fixed or automatic decimals and compact units (1.2k, 3M), the same format tick labels use: `NumberFormat` (`locale`, `precision`, `compact`, and `trim` to drop each label's own trailing zeros, so 0, 0.5, 1 read as such; `unit` to end every label in a unit such as %, MB; `NumberFormat.short`), `NumberFormat.format` for one value, `NumberFormat.formatAll` for a list, `NumberFormat.formatAt`, `floatLabel`.
- Group the digits of a number in runs with a separator, from the front of the list given: `groupRuns`.
- Parse a formatted number back to its value and precision: `parseChars`, `ungroupWhole`, with `parse_label` proving the round trip.
- Label a unix-time axis (seconds since 1970-01-01 UTC) with clock times and dates at the precision the step needs, the first tick of a day or month marked, month names from the caller: `timeTickLabels`, `timeLabels`, `timeLabel`, `TimeLabel`, with `parseTimeLabel` and `Proofs.parse_timeLabel` proving a label reads back as the tick's own fields.
- Write time-axis labels in a chosen style, a 12-hour clock (3am, 3:30pm), numeric dates (3/29, with the first of a month as 4/1) and a short context date (7/17/20), the marks and separators given by the caller: `TimeStyle` (`ClockStyle`, `DateStyle`), `timeLabelsAtWith`, `timeTickLabelsAtWith`, `timeContextsAtWith`, `timeTickContextsAtWith`, over `timeLabelsWith`, `timeContextsWith`, `TimeLabel.renderWith`.
- Tick a unix-time axis on the first of every month, or every n months, at local midnight in a timezone given as an offset function from instant to seconds east of UTC, and label ticks in that local time: `monthTicks` (pass `fun _ => 0` for UTC), `timeLabelsAt`, `timeTickLabelsAt`, with `Proofs.monthTicks_sound`, `monthTicks_complete` and `monthTicks_sorted`.
- Add a second line under a time-axis label where a coarser unit starts, the year on a date or month label, the date on a clock label, for a host to draw under the label at the label's anchor with a line height it measures itself: `timeTickContextsAt`, `timeContextsAt`, `timeContexts`, `timeContext`.
- Tick a unix-time axis at clock intervals (hours, days, weeks) on a timezone's local clock, so day ticks sit at local midnight across daylight-saving changes: `durationTicksAt` (also returns the step for `timeTickLabelsAt`) over `clockTicks`, with `Proofs.clockTicks_sound`, `clockTicks_complete` and `clockTicks_sorted`.
- Tick a unix-time axis at clock intervals chosen by the pixels wanted between ticks, a daily step for 12 days over 700 pixels at 50: `durationTicksAtSpaced`, `durationStepSpaced`.
- Get a time zone with daylight saving as the offset function the time-axis entry points take, from a POSIX TZ rule such as `CET-1CEST,M3.5.0,M10.5.0/3`: `posixZone`, with `posixZone_eq`. It is in `Inkproof.Axis.PosixZone`, which `Inkproof.Axis` does not import, as it needs `Std.Time`.
- Decide which axis labels to show and whether to rotate them so they do not overlap, using text sizes measured by the host: `layoutLabels`, and `layoutLabelsVertical` for a vertical axis (spans labels by height, positions in either order), and the generic `layout`, `thin`, `everyNth`, `clearChain`, `Rotation`, `Span`, `Layout`.

## Guarantees

Over any ordered field, ticks are evenly spaced, strictly ascending and inside the range (`Proofs.cover_valid`, `Proofs.decadeTicks_valid`), labels read back as the value they show (`Proofs.parse_label`), and kept labels never overlap (`Proofs.layout_noOverlap`). The `Float` entry points check their result with `Ticks.Valid` and return no ticks rather than invalid ones. An empty, non-finite or non-positive (log) range has no ticks. Text is never measured and no locale assumed here; both come from the caller. See `DESIGN.md`.
