# Inkproof.Axis

Ticks and labels for chart axes, for every scale kind. Part of Inkproof. Released under the Apache 2.0 license; see `LICENSE`.

## Supported versions

| Inkproof.Axis | Lean | Inkproof.Scale | Inkproof.Float |
| --- | --- | --- | --- |
| `v0.5.2` | `leanprover/lean4:v4.35.0` | `v0.6.1` | `v0.5.0` |

The library builds natively and under Lasm from the same source.

## Using it

```lean
require «inkproof-axis» from git "https://github.com/paulbutcher/inkproof-axis" @ "v0.5.2"
```

`import Inkproof.Axis` brings in everything a program runs. `import Inkproof.Axis.Proofs` adds the published theorems, which a browser build need not link.

## What it does

- Choose tick positions for a linear axis: `linearTicks` for a range, `linearScaleTicks` for an `Inkproof.Scale.Linear`; the step comes from `niceStep`.
- Choose tick positions for a logarithmic axis, at powers of ten: `logTicks`, `logScaleTicks`, over `decadeTicks` and `decadeExponents`.
- Choose tick positions for a categorical (band) axis: `categoricalTicks`, `categoricalIndices`, and `categoricalScaleTicks` for an `Inkproof.Scale.Categorical`.
- Choose tick positions for an elapsed-time axis, at clock intervals from a second to a week: `durationTicks`, `durationScaleTicks`, `durationStep`, `durationSteps`.
- Generate evenly spaced ticks over any ordered field, with spacing, order and range proved: `Grid`, `Grid.cover`, `Grid.values`, `Ticks.Valid`.
- Format tick values as number labels for a locale (decimal separator, digit grouping, minus sign), with the fewest decimals that keep adjacent labels distinct: `tickLabels`, `label`, `scaled`, `formatChars`, `Locale` (`en`, `de`, `fr`, `plain`).
- Group the digits of a number in runs with a separator, from the front of the list given: `groupRuns`.
- Parse a formatted number back to its value and precision: `parseChars`, `ungroupWhole`, with `parse_label` proving the round trip.
- Decide which axis labels to show and whether to rotate them so they do not overlap, using text sizes measured by the host: `layoutLabels`, and `layoutLabelsVertical` for a vertical axis (spans labels by height, positions in either order), and the generic `layout`, `thin`, `everyNth`, `clearChain`, `Rotation`, `Span`, `Layout`.

## Guarantees

Over any ordered field, ticks are evenly spaced, strictly ascending and inside the range (`Proofs.cover_valid`, `Proofs.decadeTicks_valid`), labels read back as the value they show (`Proofs.parse_label`), and kept labels never overlap (`Proofs.layout_noOverlap`). The `Float` entry points check their result with `Ticks.Valid` and return no ticks rather than invalid ones. An empty, non-finite or non-positive (log) range has no ticks. Text is never measured and no locale assumed here; both come from the caller. See `DESIGN.md`.
