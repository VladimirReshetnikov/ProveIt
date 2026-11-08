# The block-mask2963 tuple: a Lean calibration (started)

Package 188 (`con-zfc-diophantine-forms/188-pell-orientation-exact-projection/`)
binds its two 14-positive native companions to the block-mask2963 tuple
(`candidates/one-page-block-mask2963/`; ordinary proof in
`research/low-padding-independent/PROOF.md`, recipe simplification in
`research/block-mask-recipe/NOTE.md`):

- the scaled companion 118 / 66 is `ModelCarrierCurrent.expressionAt118`;
- the ordinary companion 94 / 67 is `Carrier94Syntax.expressionAt94`.

Both already have iPRA endpoints, but at the CURRENT2011 ports. This directory
records the finite binding to block-mask2963 and the Lean port of the
calibration. The port uses the admissible942 port (`Lean/DiophantineConsistency/Adm942/`,
[`../admissible942-calibration/README.md`](../admissible942-calibration/README.md))
as its template.

## Layout

block-mask2963 is the admissible942 layout with **one** clean clause band at
1956 instead of two. The padding is bit 2 of fields 1..916, merged with the
origin test as `4·G917`.

| | CURRENT2011 | admissible942 | block-mask2963 |
| --- | --- | --- | --- |
| ρ, L, d | 2^47, 2011, 94517 | 2^47, 4027, 189269 | 2^47, 2963, 139261 |
| tile table, selector order | `WangTiles942.tile`, physical order | same table, index | same table, index |
| support `Es` | [0,951) ∪ [960,986) ∪ {1004} | … ∪ {1005} | … ∪ {1005} |
| clause | one doubled band at 1005 | two bands, 1992 / 2998 | one band at 1956 (exponents 971..1956), mask 2^44 − 2 |
| bare / spatial | ρ^18, ρ^1004, ρ^(L+9) | ρ^18, ρ^1005, ρ^(L+9) | ρ^18, ρ^1005, ρ^(L+9) |
| padding | bit-3 staircase | top 4004..4022 | bit 2 of fields 1..916 |
| coefficient mass | 7659829036801887 | 7659829036801887 | 3829914518400945 (the carry bound 57 still holds) |
| controller λ, ord_C0 Γ | 120199 | 246929, 740784 ∤ λ−1 | 1362521, 1362520 = λ−1 |

What differs from admissible942:

- fields 971..1005 see the reflected band (even label weights only, at most
  2^44 − 1024);
- with a single band there is no clean-band choice, so phase zero must come
  first, from the marker parity at 1005 in cell 0 (PROOF §7), and decoding
  after it;
- alignment is the same finite split, r ∈ {0} ∪ [20, 961].

The direct column-sum proof of the Local Normalization Lemma carries over:
- digits equal columns at every tested field up to 1956;
- columns above the clause stay below 2^53;
- field 2962 is zero.

## Finite binding

All four checks are outside Lean, and each prints `ok`.

- [`tools/check_recipe.py`](tools/check_recipe.py) rebuilds
  `WangTiles942.tile` from `WangTiles942Data.lean`. It then checks:
  - the frozen 3297-entry weight list equals the Lean weights, with
    selectors at their index;
  - the recipe reproduces β, K, MC and MF_source (69,685 bytes, minimal
    big-endian) exactly, against the candidate's and 188's coefficient files
    and every pinned hash;
  - the mask, kernel and geometry facts, and the controller constants (with a
    self-test against the admissible942 Lean numerals).
- [`tools/check_forms.py`](tools/check_forms.py) compares 188's
  `q66_d118.json` and `q67_d94.json` with `expressionAt118` and
  `expressionAt94`, by normalized signed sums and by modular evaluation at the
  actual ports. Every single-gate mutation is detected (66/66 and 67/67).
- [`tools/ln_check.py`](tools/ln_check.py) checks the block-mask2963 Local
  Normalization statement: every field, with `block` checked on 17,472 cases,
  plus negative controls.
- [`tools/col_check.py`](tools/col_check.py) checks the column bounds that the
  direct Local Normalization proof needs.
