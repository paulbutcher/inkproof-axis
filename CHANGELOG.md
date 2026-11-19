# Changelog

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
