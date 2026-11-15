# Inkproof.Axis design

Inkproof.Axis chooses ticks for every scale kind. Requirement IDs refer to `REQUIREMENTS.md` in `inkproof-coordination`.

## Packages and modules

- The package depends on `inkproof-scale` at a release tag; it builds natively and under Lasm from the same source.
- Runtime modules live under `Inkproof.Axis`; published theorems live under `Inkproof.Axis.Proofs`, which runtime modules never import. No axioms are declared; the tests check that.

## Generic core

- A tick list is a `Grid`: the integer multiples `(first + i) * step` for `i < count`. Even spacing, order and range follow from the shape, so every scale kind reduces to choosing `step`, `first` and `count` (AXIS-1, PROOF-12).
- `Grid.cover` returns the multiples of a step in `[lo, hi]`. Over any ordered field with `IsFloor fl` (which `Rat.floor` meets), `cover_valid` proves spacing, order and range.
- Choosing the step (`niceStep`, `durationStep`) is not proved: any positive step gives valid ticks.

## Scale kinds

- Linear and elapsed-duration scales use `Grid.cover` over the visible domain. A step is 1, 2 or 5 times a power of ten; durations use clock intervals (`durationSteps`) from a second to a week, and power-of-ten days beyond.
- Log scales tick at integer powers of ten, every `stride`th when many (`decadeTicks`); `decadeTicks_valid` assumes a strictly increasing power and a logarithm agreeing at the ends. Under two powers in range falls back to linear.
- Categorical scales tick at every `stride`th band index inside the visible range and the categories (`categoricalTicks`); the theorems give membership, strict order and spacing.

## Degenerate ranges and floats

- An empty, non-finite or non-positive (log) range has no ticks, and a reversed range is read as its ascending interval. Nothing panics.
- Floats are not a field, so the Float front ends (`linearTicks` and the others) are tested, not proved. Each checks its result with `Ticks.Valid` and returns no ticks if range or order would break (step below float spacing at the range).
- `Inkproof.Axis.Scales` applies the front ends to Scale's `Linear`, `Log` and `Categorical` structures.

## Labels

- A `Locale` gives the decimal separator, grouping and minus sign; `Locale.Valid` is the hypothesis under which labels read back (AXIS-2, PROOF-12). `en`, `de`, `fr` and `plain` are provided.
- A label is integer arithmetic: `scaled` rounds a tick to a whole number of units of `10 ^ -p`, and `formatChars` writes that integer with `p` decimals. No float is printed, so labels agree on every platform.
- `parseChars_formatChars` proves a label reads back as its mantissa and precision; `label_adjacent_ne` proves adjacent grid ticks at least one unit apart get different labels.
- `tickLabels` chooses the fewest decimals (up to 15) that show every tick and keep adjacent labels distinct, and returns no labels if none does. Like the Float tick front ends it is tested, not proved.
## Label layout

- Text is measured by the host: `layoutLabels` takes a function from a label to its width and height, and calls nothing else (AXIS-3, PROOF-13).
- A label is a `Span` along the axis centred on its position, as long as its rotation makes it (`Rotation.extent`: 0, 45 or 90 degrees, with the cosine of 45 degrees a literal so platforms agree). `layout` is generic over the number type and the label.
- Rule: at each rotation, keep every `k`th label at the least `k` leaving `gap` between neighbours; the rotation keeping the most labels wins, the least rotation among equals. At least one label is kept.
- `layout_noOverlap` proves neighbours and later labels never overlap, given non-negative measurements and gap; `Layout` results are a sublist of the input. `layoutLabels` drops labels whose measurement is negative or not a number, which the hypothesis excludes, and is tested, not proved, as floats are not an ordered field.

