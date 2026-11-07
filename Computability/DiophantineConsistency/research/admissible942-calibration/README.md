# The admissible942 tuple: a Lean calibration (183 closed)

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

## Lean status

The modules live in
[`Lean/DiophantineConsistency/Adm942/`](../../Lean/DiophantineConsistency/Adm942/).
They are ports of the CURRENT2011 in-model chain, with the 2011 theorem names
kept.

- **Window layer (done).** `Adm942MaskData`, `Adm942Kernel`, `Adm942Ports`,
  `Adm942MaskConstants`, `Adm942CarrierRadix`, `Adm942HalfBinomial`,
  `Adm942RankForcing`, `Adm942WindowInterface`, `Adm942WindowZero`. In every
  model of IΣ₁, a positive zero of `expressionAt` at the admissible942 ports
  gives `q u = 2^(189269·N)` and the admissible942 `Window`.
  [`tools/check_ports.py`](tools/check_ports.py) checks that the Lean digit lists
  give the pinned payloads, and also checks the mask populations, residues,
  coefficient mass and support gaps.
- **Soundness (done).** `Adm942CellLocal`, `Adm942CellLabels`,
  `Adm942CellTransfer`, `Adm942CellDecoding`, `Adm942WholeField`,
  `Adm942Occupation`, `Adm942CellWindow`, `Adm942Soundness`.
  `Adm942Soundness.zero_halts` / `zero_halts_below`: a positive zero makes the
  decimal215 run halt before `q u`, through
  `ArithmeticWangSoundness.marked_halts` on `WangTiles942`.
  - Compared with 2011, the doubled clause band is replaced by two clean bands
    1006 apart, decoded with carry-in at most 57.
  - The alignment offsets are `{0} ∪ [20, 961]`. `r = 20` is refuted by the
    south colour of tile 941 and `21..961` by a two-selector count. The 2011
    `r = 19` orbit argument and the padding staircase are not needed.
- **Construction (done modulo `LocalNormalization`).** `Adm942ControllerData`,
  `Adm942ControllerChoice`, `Adm942Controller`, `Adm942KernelResidue`,
  `Adm942ConstructionUnit`, `Adm942PackingCells`, `Adm942ConstructionAssembly`,
  `Adm942CurrentConstruction`. `Adm942CurrentConstruction.halt_positive_zero`: a
  halt of the decimal215 run gives a positive zero. Its only hypothesis is
  `Adm942PackingCells.LocalNormalization`, a closed statement about ordinary
  natural numbers, exactly as in 2011.
  - The unit uses the 2011 lcm exponent, since `ord_C0 Γ = 740784` does not
    divide `λ − 1`.
  - `K ≡ 15862373587 (mod C0)` is proved without ever writing out `K`: one
    Horner fold over the tile table, checked by `decide +kernel`.
  - A Python check confirmed that `LocalNormalization` is true:
    - `low`, `product`, `low_origin` and the bounds hold exhaustively;
    - `block` held on 17,472 checks: 300 random admissible triples plus all
      triples with `mc = 0`, each with all 32 bit settings;
    - as negative controls, non-admissible triples break the high mask.
- **Local Normalization (done).** `Adm942LocalColumns`,
  `Adm942LocalNormalization`, `Adm942Construction`.
  - The proof is direct. `K·cellN` is a radix-`2^47` sum of columns, each
    bounded by the coefficient mass `< 2^53`, and column 4026 vanishes. So
    `% BN` and `/ BN` split the column sum exactly.
  - Every tested digit then equals its column, with enough room below it,
    and each digit passes the mask test from the adjacency hypotheses.
  - The only kernel decision is a linear walk over the 4027 high-mask digits.
  - `Adm942Construction.halt_positive_zero_closed` is the construction with no
    remaining hypothesis.
- **183 endpoint (done).** `IPRACarrier65Adm942`: `positiveBridge`, then
  native, standard and equality-only iPRA equivalences between the absence
  of positive zeros of 183's 150/65 and `¬mappedNativeRefutation`.
- **Open.** The 192 retarget (`ModelThirteenCarrier`,
  `ArithmeticThirteenOuter`) onto the admissible942 window.

All axioms are within `[propext, Classical.choice, Quot.sound]`.
