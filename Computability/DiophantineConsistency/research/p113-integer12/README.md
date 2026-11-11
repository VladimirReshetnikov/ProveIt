# Package 113: iPRA endpoints for the twelve-integer saturated equation

Equation: `con-zfc-diophantine-forms/113-saturated-pell/integer12_saturated/rational.json`,
twelve unrestricted integer unknowns `j C z h r v w T c n t s`, 123 operations
(75 `mul`, 25 `add`, 23 `sub`), exact degree 1084, at the six fixed integers of the source34
tuple (package 138's ports, `P138Ports.ports6`).

## Lean

All modules are in `Lean/DiophantineConsistency/P113/`.

| Layer | Modules |
| --- | --- |
| registers | `P113Value` (the DAG's registers, `value_scale`: `δ⁴ · value` is a three-root norm) |
| front | `P113Front` (113's front registers are package 138's at the native index) |
| soundness (zero ⟹ halt) | `P113Roots`, `P113Fold`, `P113Chain`, `P113Leaf` |
| completeness (halt ⟹ zero) | `P113Cone`, `P113Canonical`, `P113Complete` |
| syntax | `P113Syntax` (generated) |
| endpoints | `IPRAInteger113` |

`IPRAInteger113` proves `native_equivalence`, `standard_equivalence` and `reference_equivalence`.
In the native and the standard iPRA theory, "the equation has no integer zero"
(`nativeNoZero (signedSplit expression)`) is equivalent to the native rendering of "machine 215
does not halt", and so of Con(ZFC). The reference endpoint is the order-erased form of the same
equivalence in the equality-only reference theory. The axioms are `propext`, `Classical.choice`
and `Quot.sound`.

### How it reuses package 138

* **Soundness.** A zero gives three integral roots (`P113Roots.roots`: three-adic separation),
  the coprime saturation `E = τ²`, `Df = f²`, and the guards `G > 0`, `η ζ > 0`. These fill
  package 138's folded front (`P138Rank.Folded`) except for one field: 138's positive budget
  becomes the signs plus the **weak window** `|k| (|Y| − 1) < |c| < |k| (|Y| + 1)`
  (`P113Fold.Folded113`). Package 138's chain (first index, ratio bound, signed projector,
  orientation, leaf) is re-run over that record (`P113Chain.FoldedW`) with two arithmetic changes,
  `|c| > 2|k|` in the no-wrap step and `|H| ≥ |X| (2|Y| + 2)` in the ratio bound. In the leaf,
  `η > 0` comes from the guard rather than from the half-binomial.
* **Completeness.** Package 138's canonical record, plus the strict cones
  `2^1113 F < q`, `C 2^666104 < q` (`P113Cone.strict_cones`, from the fine cell window
  `cell < ρ^3296 + ρ^2196`; the record itself only stores `q ≤ 2 Uc ≤ 3q`), give `G > 0`. Then
  the nearest-square witness `t` makes `Pair > 0`, Pell existence gives `s, g` with
  `(3 Pair − 4) s² + 1 = g²`, and the supported-modulus interpolation with `N = 4 s τ c²` gives
  `I = τ U`, `Df = f²` and every residue class of `T` modulo `U` through `T_old = τ T`.
  `P113Canonical.canonical_strict` is `P138Canonical.canonical` re-run (generated with two edits)
  so that package 138's accepted record and its dependents are untouched.

## Tools

* `tools/gen_literal113.py [--check]`: generates `P113Syntax.lean` from the pinned JSON
  (SHA-256 `4afd94ea…ba50`), with a numeric model check of every register; `--check` regenerates
  byte-identically.
* `tools/check_ports113.py`: the JSON's six coefficient leaves and `coefficients/BINDING.json`
  are bound, by the package's `INHERITED_SOURCE_PINS.json`, to exactly package 138's pinned
  payloads (and their repository copies); `research/p138-integer11/tools/check_ports138.py`
  checks those payloads against `P138Ports.ports6`.

Run them as `py -I -X utf8 -B <tool>`.

## Scope

Among the twelve-integer equations, 113 is Pareto-optimal in its row (operations, degree). Across
variable counts it is dominated, for example by package 125 (eleven integers, degree 488,
118 operations; `P125/IPRAInteger125`).
