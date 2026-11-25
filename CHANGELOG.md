# Changelog

## [0.17.0]

- `NumberFormat.unit`: a unit written after every label and its compact suffix (inkproof-axis#66).

## [0.16.0]

- With a numeric date style, the tick on the first of a month is labelled month/day, not the bare month (inkproof-axis#64).

## [0.15.0]

- Linear steps from a pixel spacing and 2.5 multiples, and labels without trailing zeros (inkproof-axis#57).
- Log ticks at 1, 2 and 5 or every integer in any base, minor ticks apart from labelled ones, and `b^n` power labels (inkproof-axis#56).
- Time ticks and labels in a chosen style, with clock steps from a pixel spacing (inkproof-axis#55).
- `transformTicks`: ticks at the steps of a scale given by a transform pair, for Weibull and arcsinh axes (inkproof-axis#58).

## [0.14.0]

- `timeTickContextsAt`, `timeContextsAt` and `timeContexts` give the year or day a time axis label starts, to draw as a second line.

## [0.13.1]

- The README no longer pins a version or lists supported versions.

## [0.13.0]

- `NumberFormat` writes numbers in a locale with fixed or automatic decimals and compact units, and `tickLabels` uses it.

## [0.12.0]

- `logTicksAt` and `logScaleTicksAt` tick a log axis at 1, 2 and 5 or at every integer within each decade, chosen by `LogMultiples`.

## [0.11.0]

- `posixZone` builds the offset function for `monthTicks` and `durationTicksAt` from a POSIX TZ rule, in its own module `Inkproof.Axis.PosixZone`.

## [0.10.0]

- `symlogTicks` ticks a symmetric log or arcsinh axis at zero and powers of ten mirrored about it.

## [0.9.0]

- `clockTicks` and `durationTicksAt` tick a unix-time axis at clock intervals on a timezone's local clock, given as an offset function, with the step for `timeTickLabelsAt`.

## [0.8.0]

- `monthTicks` ticks every n-th calendar month at midnight in a timezone given as an offset function, and `timeLabelsAt` and `timeTickLabelsAt` label ticks in that local time.

## [0.7.0]

- `timeTickLabels` and `timeLabels` label unix-time ticks in UTC at the precision the step needs, marking the first tick of a day or month, with `parseTimeLabel` proved to read each label back; depends on `inkproof-core` v0.13.0.

## [0.6.0]

- `layoutLabelsVertical` lays out labels on a vertical axis by their height, with positions in either order.

## [0.5.4]

- README lists `groupRuns` under What it does.

## [0.5.3]

- README lists what the library does.

## [0.5.2]

- Lasm tests run under @lasm/cli 0.8.0.

## [0.5.1]

- Requires Float v0.5.0 and Scale v0.6.1, matching Gpu and Viewport.

## [0.5.0]

- Digit and decimal-parsing code moves to core's `Inkproof.Core.Decimal`; `Axis.lsDigits`, `digitCount`, `digitsValue`, `splitAtChar` and their theorems are removed.

## [0.4.0]

- Labels use core's `Nat.digitChar`; `Axis.digitChar` is removed and its theorems restate over the core function.

## [0.3.0]

- Tick labels with locale definitions, with proved read-back and distinct adjacent labels.

## [0.2.0]

- Label layout against host text measurements, with proved non-overlap of the labels kept.

## [0.1.0]

- Ticks for linear, log, elapsed-duration and categorical scales, with proved range, order and spacing.
