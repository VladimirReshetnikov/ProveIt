# The admissible942 tuple: a Lean calibration (started)

7 November 2026. Claude session; not a paired replay.

## Why this tuple

Package 183's fourteen-positive 150 / 65
(`183-pell-carrier65/equation/carrier65.json`) and package 192's
thirteen-positive 174 / 69 are bound to the admissible942 ports
(`candidates/one-page-admissible942/coefficients/`, recipe and proof
[`research/admissible942-independent/PROOF.md`](../admissible942-independent/PROOF.md)).
The tree's endpoints for these formulas are at the CURRENT2011 ports.

## Layout

admissible942 is the CURRENT2011 layout on a two-band kernel:

- `ρ = 2^47`, `L = 4027`, `d = 189269`;
- the 942 rows are exactly the tree's `WangTiles942.tile`, in order;
- complemented 34-bit clause coefficients `1 + 2^10(1 + w + 2^8 n + 2^17 p + 2^25 s)`;
- label copies at `942/960/969/978` (as `CurrentKernel2011`), Boolean dummy
  `977`, marker `1005` (2011: `1004`);
- two reflected clause bands at `1992`/`2998` (gap `1006`), bare terms `ρ^18`,
  `ρ^1005`, `D_R = ρ^9`; padding at `4004..4022`;
- completeness controller Pca942: `λ = 246929`, `C0 = dλ = 46736004901`,
  `K ≡ 15862373587` and `Γ ≡ 11595945771 (mod C0)`, `ord_C0 Γ = 740784`.

So the CURRENT2011 in-model chain (window, cell transfer, cell decoding,
whole-field alignment, occupation, `ArithmeticWangSoundness.marked_halts`),
its controller and its K-chain construction are the templates, not Compact44.
183's form is the Carrier65 polynomial, for which port-parametric in-model
lemmas already exist (`ArithmeticCarrierSoundness2011.expressionAt_equations`,
`ArithmeticConstructionZero.equations_zero`). 192's form reduces to it through
`ModelThirteenCarrier`, which needs retargeting.

## Finite binding

[`tools/check_recipe.py`](tools/check_recipe.py) rebuilds `WangTiles942.tile`
from `WangTiles942Data.lean`, applies the recipe and reproduces all four
payloads (β 189,269 bits, K 189,693, MC 189,269, MF_source 189,270; minimal
big-endian bytes) exactly. This is a finite check outside Lean.

[`tools/check_forms.py`](tools/check_forms.py) closes the form side of the
binding:

- 183's `equation/carrier65.json` (pinned SHA-256 `bf58ed66…`) is identical,
  modulo associativity and commutativity of `+` and `*`, to the Lean
  `ObjectCurrentEquation2011.expressionAt p` with `p = (β, K, MC, MF_source)`;
- 192's `compact13/positive13_square.json` (`9574f3db…`) is identical in the
  same sense to `ModelThirteenCarrier.expressionAt69 p`;
- every single-gate operation change is detected (65/65 and 69/69);
- 183's coefficient files and 192's pinned hashes are the four admissible942
  payloads.

So the endpoints only need the tuple calibration: the per-form Lean syntax and
its port-parametric algebra already exist.
