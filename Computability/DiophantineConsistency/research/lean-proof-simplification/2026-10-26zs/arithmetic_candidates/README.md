# One selected arithmetic client cleanup — UNCOMPILED

Snapshot: `9d9d1123b39927d30363f1dcd53c23f0575c30ee`.
The selected candidate modifies only the `fourBlocks_cast` proof body in
`CurrentPackingRank2011.lean`. A rejected `rank_gt_twice_window` cleanup and a
combined module are retained as comparison-only artifacts, with no new credit.
No imports, definitions, theorem
statements, assumptions, subtraction guards, or downstream proofs are changed.
No Lean installation or invocation was performed. The checks below are not Lean
validation. Final strict novelty review cleared the selected **local wrapper-detour removal**
at closing revision `451b548a`; the algebraic certificate itself is existing
work, not a new result. Independent source-only proof review passed: patch replay and unchanged
external text, five retained subtraction guards, exact coefficient-dictionary
polynomial verification, 13,230 additional guarded models and a negative guard
control. No concrete extra elaboration issue was identified beyond the ordinary
uncompiled `unfold` / `push_cast` / `linear_combination` status. The growth cleanup is EXCLUDED by the strict baseline:
prior packet zc lines 349–375 and 570–583 already proposes systematic power
normalization followed by a standard growth bound and `omega`.

## 1. Delete the intermediate packing-polynomial rebindings

Source: [CurrentPackingRank2011.lean, lines 51–75](https://github.com/VladimirReshetnikov/ProveIt/blob/9d9d1123b39927d30363f1dcd53c23f0575c30ee/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentPackingRank2011.lean#L51-L75).

The original first casts the repunit balance, derives `hbeta`, instantiates
`NativeSourceMask.packing_four_block` as `hh`, spells out a second full four-block
expression as `hB`, rewrites back through both expressions, unfolds the rank,
and performs a second cast normalization and `ring` call.

Retain the original seven prerequisite lines, including positivity of the high
mask product and every natural-subtraction domain. Then use:

```lean
  unfold fourBlocks rank NativeRankVariation.windowRank
  push_cast [Nat.cast_sub (by omega : 1 ≤ C),Nat.cast_sub hHJ,
    Nat.cast_sub hCq,Nat.cast_sub (by omega : 1 ≤ q N-F),
    Nat.cast_sub (by omega : F ≤ q N)]
  linear_combination -(q N : ℤ) * hb
```

Why the coefficient is negative: after casting, put `J = repunit width N` and
let `q` abbreviate the integer cast of `q N`. The exact polynomial difference is

`fourBlocks - rank = -q * (beta*J + 1 - q)`.

The parenthesized quantity is precisely the left-minus-right residual of
`hb`, obtained from the existing [repunit balance, lines 34–43](https://github.com/VladimirReshetnikov/ProveIt/blob/9d9d1123b39927d30363f1dcd53c23f0575c30ee/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentNativePacking2011.lean#L34-L43).
The underlying [windowRank definition, lines 19–21](https://github.com/VladimirReshetnikov/ProveIt/blob/9d9d1123b39927d30363f1dcd53c23f0575c30ee/Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeRankVariation.lean#L19-L21)
retains the high port's beta shift exactly once.

**Tradeoff:** this bypasses the reusable `NativeSourceMask.packing_four_block`
lemma and duplicates its small polynomial certificate at this concrete client.
It does not improve or replace the general theorem. The benefit is removing two
large expression rebindings and a second unfold/cast/ring phase. Retaining the
existing shared-lemma proof is a reasonable maintainability choice; this is not
claimed as a new rank bridge, cast framework, or arithmetic theorem.

## Excluded comparison: direct exponential lower bound for the cube

Source: [CurrentPackingRank2011.lean, lines 88–100](https://github.com/VladimirReshetnikov/ProveIt/blob/9d9d1123b39927d30363f1dcd53c23f0575c30ee/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentPackingRank2011.lean#L88-L100).

Replace the auxiliary `u < q`, `0 < u`, `2 ≤ q`, `2 ≤ q²`, and the two-step
comparison through `2*q` with:

```lean
  have hc : 2*(width*N) < q N^3 := by
    rw [q_binary,← pow_mul]
    have h : (width*N)*3 < 2^((width*N)*3) := Nat.lt_two_pow_self
    omega
```

For `u = width*N`, this uses `q³ = 2^(3u)` and
`2u ≤ 3u < 2^(3u)`. The scalar inequality also holds at `u = 0`; the theorem's
existing `[NeZero N]` assumption is retained because the final `fourBlocks_cast`
bridge still uses it. The last three lines connecting the actual four-block
lower bound to the integer rank are byte-identical.

This is a four-line saving at one exact client, but the mechanism is already
covered by prior proposals and receives **zero new credit**. No generic helper
is introduced or charged to another module. It is not part of the selected patch.

## Metrics and files

Counts include all nonblank-or-blank physical lines in the replaced proof bodies
(the bodies here contain no blank lines); theorem headers are excluded. UTF-8
byte counts are recorded separately; no performance claims are made.

| Change | Proof lines before | After | Saved | Bytes before | After |
|---|---:|---:|---:|---:|---:|
| **Selected packing certificate** | **23** | **12** | **11** | **1037** | **586** |
| Excluded growth comparison | 11 | 7 | 4 | 597 | 333 |
| Combined comparison only | 34 | 19 | 15 | 1634 | 919 |

**Selected whole module: 138 → 127 lines. New credit: 11 proof lines removed.**
Combined comparison-only module: 138 → 123 lines, not a 15-line new result.
Added Lean helpers: 0. Added imports: 0.

- `fourblocks_certificate/fourblocks_certificate.patch`: selected patch.
- `rank_growth/rank_growth.patch`: EXCLUDED comparison patch.
- `combined/combined.patch`: COMPARISON ONLY; not selected.
- Each directory has a complete `candidate/CurrentPackingRank2011.lean` and metrics.
- `build_candidates.py`: deterministic exact replacements guarded by the original
  file SHA-256 `614f47e52f31dfc199f98387e5c720f1ae51fb0725ce8d9f21223b540a30c546`.
  It uses the included exact snapshot copy `source/CurrentPackingRank2011.lean`. All
  artifact paths are relative to this directory; no checkout or network is needed.
- `check_artifacts.py`: patch replay (`--fuzz=0`), identical statements/imports,
  and byte-identical text outside the two target proof bodies. The selected patch
  changes only the first body. Safety checks use explicit `require` calls rather
  than Python `assert`, and were rerun successfully under `python -O`.
- `test_arithmetic.py`: four non-Lean unittest tests; symbolic polynomial identity
  (SymPy), 29,160 bounded natural packing cases with all cast domains, a deliberate
  missing-positive-high-product counterexample, and 4,097 **comparison-only**
  growth cases including zero. The growth model test does not imply new credit.
- `artifact_checks.json`, `unittest_output.txt`, and per-candidate check JSON:
  recorded local results. These checks do not validate Lean elaboration or kernels.

## Other fresh modules screened, not proposed

`CurrentControllerPositions2011`, `CurrentDummySafety2011`,
`NativePackingPopulation`, and `CurrentWordRephase2011` were inspected with their
immediate dependencies. Their proofs mostly already use the relevant direct
interfaces. Potential optional-cell constant-folding, generic carry transport,
prefix/word bounds, sum-distributivity, and coarse nonwrapping rewrites were not
promoted: too small/generic, existing mechanisms, or insufficient net benefit
once helper overhead is charged. Only the packing-polynomial client cleanup is selected; the growth change
is retained solely as an excluded comparison.
