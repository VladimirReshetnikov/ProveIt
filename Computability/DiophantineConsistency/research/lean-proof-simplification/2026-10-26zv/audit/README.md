# Independent sixth-iteration source and patch audit

**Main residual deletion: 15 physical / 15 nonblank production lines.**
An additional two-line add/and/or rewrite gives **17 / 17** across all four
files. No helpers, declarations, or imports are added or removed. These are
routine proof-body cleanups at fresh clients, not new mathematical machinery.
All metrics count complete affected production files, including helper costs.
Duplicate baselines, alternate patches, tests, notes, and tooling are not savings.

| Complete production file | Physical before → after | Saving |
|---|---:|---:|
| `CurrentControllerPositions2011.lean` | 178 → 174 | 4 |
| `CurrentWordRephase2011.lean` | 122 → 116 | 6 |
| `CurrentPackingRank2011.lean` | 138 → 133 | 5 |
| `NativePackingPopulation.lean` (secondary housekeeping) | 57 → 55 | 2 |

## Evidence and limits

- `integrated_results.json` checks all **702** supplied Lean baseline sources
  against recorded SHA-256 and Git-blob SHA-1 receipts for pin
  `9d9d1123b39927d30363f1dcd53c23f0575c30ee`. This binds bytes to the supplied
  local commit receipt; the auditor does not resolve remote commit objects or
  independently prove every baseline source. An additional late receipt binds
  all four targets and 15 selected dependency/context files to identical blobs
  at `60fcb2a69b7f1fdd4c3592ea5f164223cad50abe`, including the two supporting
  HilbertTenthProblem sources shipped in the baseline. This is not a claim
  that the whole transitive import closure stayed unchanged.
- Every main patch reconstructs its full-file candidate exactly, without context
  fuzz. All existing proof headers and all non-proof scaffolding, definitions,
  imports, options, attributes, and section/omit contexts are preserved under a
  bounded lexical normalization that retains identifier boundaries and strings.
  Only the five explicitly named existing proof bodies may differ.
- The three main patches compose in **all six orders**. All four patches compose
  in **all 24 orders**. This is textual composition, not Lean elaboration.
- The two isolated position patches are independently checked against the
  original baseline and the corresponding combined-candidate proof bodies.
  They are **alternatives** to the combined patch. Their unchanged diff contexts
  may overlap, so arbitrary sequential application is not promised. Never apply
  the combined patch together with the isolates.
- `integrated_results_optimized.json` is byte-identical under Python `-O`.
  `portability_results.json` verifies an unrelated cwd, the default sibling
  baseline, the explicit baseline override, zero observed auditor writes, and
  **15 distinct tampered controls rejected in both modes**. Candidate mutations
  use newly generated matching patches, so rejection is not merely a stale diff.
- **All proposed Lean remains UNCOMPILED.** There is no elaboration, kernel check,
  axiom/dependency-graph audit, or performance measurement. The independent
  mathematical reading and finite Python controls do not establish tactic success.
  No toolchain installation, network fetch, or incoming program was executed.

## Mathematical review and separately priced dependencies

1. **Literal affine positions.** With the unchanged literal `p=120199`,
   `position k j = 2+120198*j.val`; `j.val+1≤p^k` gives the endpoint budget by
   linear arithmetic. After `pow_succ`, `p^k` is an opaque natural atom and
   multiplications are by numeral coefficients, so nonlinear automation is not
   mathematically needed. Injectivity follows from the nonzero literal slope.
   The singleton `k=0` case and full representative range are unchanged.
   **Price:** more explicit use of the fixed literal and numeral normalization;
   no new imported module or positivity-certificate dependency. Faster checking
   is not claimed. The three optional-support proof rewrites were withdrawn
   after the late `zq` review; their original bodies and all support code remain
   unchanged, and their obsolete patches are not delivered.
2. **Exact rephase fields.** Unfolding `raw` locally in recurrence and decomposition
   and rewriting `W'` rotations to `W` removes the intermediate function equality.
   **Price:** the same definition is unfolded twice rather than once via `hraw`;
   no new dependency. The modular scalar-transport block is unchanged. Equal
   rotations do **not** assert equality of ordinary multipliers or quotient
   witnesses. Existing packing/source/carry/digit witnesses and their constructors
   are unchanged; the new quotient remains recomputed by the original code.
3. **Direct rank growth.** For every natural `u`, including zero,
   `2u≤3u<2^(3u)=(2^u)^3`. This replaces a chain of positivity and square bounds.
   The public `[NeZero N]` context, `0<C`, `C+F<q N`, top complement bound,
   ordinary natural-to-integer cast bridge, and concrete population witness are
   retained. **Price:** the same `Nat.lt_two_pow_self` is instantiated at `3u`,
   plus the already available power-multiplication identity. No stronger theorem
   layer or helper is introduced.
4. **Disjoint-add housekeeping.** The same add/and/or identity rewrites the sum
   directly; disjointness removes the AND term and the existing OR bound closes
   the goal. Both strict representative bounds and disjointness are still needed.
   **Price:** no dependency change, only two bookkeeping lines removed. No new
   population theorem, assumption, witness, or bound is claimed.

The unchanged physical safety file is hash-bound and its original `j.val+1<N`
and `j.val+s<N` guards are checked. The `omit [NeZero N]` contexts for generic
constructed-word equality and the cube bound are preserved. No new nonzero
hypothesis narrows their `N=0` behavior.

## Independent arithmetic controls

The JSON records 31 selected literal affine representatives, 105 physical
stride tests, 352 original physical exponent-guard instances (66 stride-zero),
257 direct growth bounds including zero, 3,280 disjoint-sum instances including
zero width, and 1,439 cyclic congruence instances with unequal ordinary products.
Negative controls expose omitted physical guards, carries from overlapping
bits, missing strict block bounds,
and the difference between congruence and ordinary equality. These are bounded
sanity controls, not a proof of the generic Lean statements or implementations.

## Portable read-only checker

Python 3.9+ standard library only. The checker writes nothing and invokes no
subprocess, compiler, network, Git command, or bundled script. All checks use
explicit runtime guards, not Python `assert`. JSON is stdout-only.

```sh
python3 -B audit/check_integrated.py
python3 -O -B audit/check_integrated.py
python3 -B audit/check_integrated.py --baseline-tree /path/to/repository
```

The default is the sibling `baseline/` with repository-relative source paths.
The bounded proof parser is tailored to these delivered files, **not a general
Lean parser or a replacement for elaboration**. The separate optional harness
writes and restores an isolated temporary package and runs only the copied,
locally authored Python auditor:

```sh
python3 -B audit/selftest_auditor.py
```

The late `zq` optional-support retirement removes three former candidates and
nine formerly counted lines; no superseded five-edit position candidate is
delivered. The documentary novelty boundary is in `catalog/novelty_decisions.json` and
`catalog/EXCLUSION_AND_ADOPTION_LEDGER.md`. Prior proposal collections and the
fifth iteration are assumed applied for novelty review; this does not assert
that every historical alternate patch forms one compiled cumulative checkout.
