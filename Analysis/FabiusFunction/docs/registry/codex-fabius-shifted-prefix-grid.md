# Workstream registry: `codex/fabius-shifted-prefix-grid`

**Status: coordinator disposition requested; all prior paths frozen.**
The exact claim was published before source work, coordinator checkpoint
`893d4c25d` explicitly acknowledged it as the first nonoverlapping claim for
the module, and source commit `00ff41a5e` now implements precisely that bounded
tranche.  Documentation commit `dcd5f8a06` now reconciles the four advertised
coverage clusters.  The source remains frozen pending compiler validation.
Audit-ledger commit `faf1fcaf6` was
completed and pushed before coordinator checkpoint `148990f0a` newly serialized
both campaign-wide Markdown paths; both documentation commits are preserved for
separate review, and this branch is making no further path claim.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-shifted-prefix-grid / c9a3 / EVO
  (Windows)
fetched main SHA: 148990f0a2a9b665edaf3394656be1e7c46caf7e
HEAD and dirty paths: 3161da511ddb6a2434d32d06b2b21e0179c4c354;
  clean after merging and pushing the current main checkpoint
writing (exact paths): docs/registry/codex-fabius-shifted-prefix-grid.md only;
  Lean/FabiusFunction/ThueMorseGenerating.lean is frozen at 00ff41a5e;
  docs/PAPER_COVERAGE.md is preserved at dcd5f8a06 pending review;
  docs/AUDIT_FINDINGS.md is preserved at faf1fcaf6 pending review;
  no new source or documentation path is claimed
expected declarations or document claims: shiftedPrefixGridValue;
  shiftedPrefixGridValue_zero; shiftedPrefixGridValue_one;
  shiftedPrefixGridValue_succ_sub;
  shiftedPrefixGridValue_scaledDifference;
  shiftedPrefixGridValue_equation; and
  shiftedPrefixGridValue_equation_of_pos; retain the eight existing
  paperPrefixGridValue_* and correctedPrefixGridValue_* theorem statements
  exactly as compatibility wrappers
expected documentation claims: add the seven shiftedPrefixGridValue mappings
  without generic endpoint/convergence claims; add exact all-degree centered
  finite-spline geometry; replace the stale x >= 0 discrete-limit row by its
  all-real APIs; extend the lower-Lambert row to the closed branch endpoint and
  the sharp 1 / log 2 threshold classification; next, mark exactly four audit
  findings DONE: all-degree centered-spline range, right-half-cell spline
  saturation, the sharp lower-Lambert phase threshold, and removal of redundant
  CharZero binders from four FabiusQBinomialTaylor declarations; record their
  implementation commits and immutable compiler evidence without changing any
  other finding, source file, documentation audit, baseline, TeX, or PDF
completed commits: 6fb8dc8e9 publishes the exact one-file claim; ba0048023
  activates it under the open protocol; 00ff41a5e adds the seven generic
  declarations and converts all eight legacy proofs to wrappers; 047a03b63
  merges origin/main e18f5d0b0; e2d1db43f advertises the exact coverage-map
  reconciliation; dcd5f8a06 completes and releases that documentation tranche;
  0d4ee2471 advertises the exact four-finding audit claim; faf1fcaf6 closes
  those four stale entries and records their compiler provenance; e0302acdf
  records the completed documentation checkpoints; 3161da511 merges current
  origin/main 148990f0a without conflicts
validated (exact command, SHA/state, exit code): at source snapshot SHA-256
  784F6C4F389FE0F2FA08616FFAFBFA3917CCC9F6D2C86CE98D3D877B5F0DD14C,
  git diff --check and git diff --cached --check exited 0; python
  Analysis/FabiusFunction/scripts/doc_audit.py --baseline
  Analysis/FabiusFunction/docs/doc_audit_baseline.json scanned 189 files and
  3462 public declarations, found the same 132 baseline omissions, and exited
  0; normalized type comparison matched all eight legacy theorem statements;
  two independent hostile source/tactic reviews found no blocker; duplicate
  searches covered all 17 locally present Fabius remote-tracking tips; for
  documentation blob 2ed0d5ebb0ae9534ecbe0c2694a2313ca9f6f804,
  all 59 newly cited qualified declarations resolve, all four changed table
  rows have exactly four unescaped separators, git diff --cached --check
  exited 0, the doc audit retained its exact baseline, and an independent
  binder-level review found no correction; for audit-ledger patch SHA-256
  48C94725FB082D492CCE495D01ADDED851C357DB4D4DED4AB375C3C7E7504E4,
  exactly four headings and four closure markers changed, every status row has
  four unescaped separators, git diff --cached --check exited 0, the doc audit
  retained its exact baseline, and independent review verified each signature,
  source blob, implementation commit, and immutable build checkpoint
not yet validated: no Lean or Lake process was launched because no EVO build
  token is granted; the three requested module targets remain uncompiled;
  coordinator review of 00ff41a5e, dcd5f8a06, and faf1fcaf6 is pending
requested integration or lease: review the source, coverage map, and audit
  ledger as separate units; if the source is accepted, assign this branch or an
  authorized build owner checking commit 00ff41a5e the serialized targets
  +FabiusFunction.ThueMorseGenerating,
  +FabiusFunction.ThueMorseApproximation, and
  +FabiusFunction.ThueMorseExponential
conflicts / dependencies: no overlap with the active frontier-document lease;
  no AGENTS, README, collaboration, aggregate, TeX, PDF, canonical frontier,
  primary exposition, hot foundational module, or peer registry path requested;
  checkpoint 148990f0a now serializes docs/PAPER_COVERAGE.md and
  docs/AUDIT_FINDINGS.md and explicitly forbids this branch from adding another
  path during review; a read-only two-parameter coefficient-bridge preflight is
  therefore deferred without a registry claim or source edit
next bounded step: push this exact handoff, keep every source and serialized
  document frozen, and poll the board for coordinator review and a build-token
  assignment; continue only read-only theorem/API preflight meanwhile
lease refreshed: 2026-08-25 18:14 PDT; all prior paths frozen pending
  coordinator disposition; no new path claim
git owner / build owner: root / no build owner assigned to this branch
```

## Completed bounded refactor

Before `00ff41a5e`, `ThueMorseGenerating.lean` proved four theorem pairs
independently:

- `paperPrefixGridValue_succ_sub` and
  `correctedPrefixGridValue_succ_sub`;
- `paperPrefixGridValue_scaledDifference` and
  `correctedPrefixGridValue_scaledDifference`;
- `paperPrefixGridValue_equation` and
  `correctedPrefixGridValue_equation`; and
- `paperPrefixGridValue_equation_of_pos` and
  `correctedPrefixGridValue_equation_of_pos`.

After replacing only the two grid identifiers by a neutral token and
normalizing whitespace, each pair was alpha-identical.  The implemented
abstraction is the normalized grid whose inclusive-prefix order is shifted by
an arbitrary natural number while its denominator and abscissa remain at the
same grid level:

```lean
def shiftedPrefixGridValue (s k j : ℕ) : ℚ :=
  (iteratedPrefix (k + s) j : ℚ) / (2 : ℚ) ^ k.choose 2
```

The source tranche proves the forward-difference law, its denominator-cleared
form, the equation paired with the exact unit-interval domain condition, and
the positive-level reindexing once for arbitrary `s`.  Shift zero and shift one
recover the literal paper grid and the corrected inclusive-prefix grid.

## Compatibility boundary

The existing public definitions remain textually unchanged:

```lean
def paperPrefixGridValue (k j : ℕ) : ℚ :=
  (iteratedPrefix k j : ℚ) / (2 : ℚ) ^ k.choose 2

def correctedPrefixGridValue (k j : ℕ) : ℚ :=
  (iteratedPrefix (k + 1) j : ℚ) / (2 : ℚ) ^ k.choose 2
```

This preserves both definitional reduction and the behavior of client proofs
that explicitly unfold either name.  Two one-way simp bridges normalize
`shiftedPrefixGridValue 0` to `paperPrefixGridValue` and
`shiftedPrefixGridValue 1` to `correctedPrefixGridValue`; reverse simp rules
were not added.  The eight existing theorem headers, binder order, hypotheses,
conjunction order, attributes, and result syntax also remain unchanged.  Only
their duplicated proof bodies became specializations of the
generic family.

The generic recurrence is not an endpoint or convergence theorem.  The shift
changes endpoint values, so the refactor deliberately stops before
`paperPrefixGridValue_endpoint`, either polygon, and every convergence or
nonconvergence declaration.  The hypothesis `0 < k` on the positive-level
equation is essential: the arbitrary-shift statement is false at level zero.

## Proof and edge-case preflight

The generic successor proof uses only the ingredients already present in the
two duplicated proofs:

1. unfold `shiftedPrefixGridValue` three times;
2. normalize `q + 1 + s = q + s + 1` locally;
3. use `sub_div`, the integer-cast compatibility, and
   `iteratedPrefix_succ_sub`;
4. split the triangular exponent with `choose_succ_two`, `pow_add`, and
   `div_div`.

The scaled theorem reuses `pow_succ` and nonvanishing of `(2 : ℚ) ^ q`.  The
domain theorem pairs it with the unchanged
`prefixGridPoint_lower_argument_mem`.  The positive-level theorem performs the
same natural-number case split as both existing proofs.

The reviews checked:

- shift zero and shift one;
- `q = 0`, where the only admissible `j` is zero and the grid point is the
  included endpoint `1`;
- `k = 1` in the positive-level form;
- the counterexample showing why `0 < k` cannot be dropped; and
- the absence of new simplifier loops or changed public theorem signatures.

No new import was required.  The module has two direct consumers,
`ThueMorseApproximation.lean` and `ThueMorseExponential.lean`; no source file
outside `ThueMorseGenerating.lean` calls any of the eight wrapper theorems.

## Duplicate search and deferred opportunities

The exact names and plausible `shifted`/`offset` aliases were searched on
current main, all 17 locally present Fabius remote-tracking tips, every
available registry at those tips, and reachable history.  No equivalent
declaration or competing claim exists.  This is distinct from the human
document's Appell family and from the translated Thue--Morse polynomial degree
API already integrated from `a95bd1913`.

Three worthwhile but intentionally separate follow-ups were identified:

1. clearing an arbitrary number of `(1 - X)` factors lowers
   `iteratedPrefixSeries (k + n)` exactly to order `k`;
2. a public two-parameter finite-block coefficient bridge can replace a
   narrower private helper in `ThueMorseApproximation.lean`; and
3. translated Thue--Morse blocks satisfy finite addition and formal-derivative
   laws, furnishing a genuine polynomial translation calculus.

None is included in this source checkpoint.  Keeping the first commit to one
mechanically evidenced duplication class makes the review, build attribution,
and rollback boundary exact.

## Coordinator shifted-grid integration disposition

The Lean source, coverage-map delta, and audit-ledger delta are accepted as
three separately reviewed units.  The two documentation commits exceeded the
branch's earlier exact “source plus own registry” grant, but both are accurate;
the coordinator therefore accepts them explicitly rather than discarding the
work.  This does not authorize another path expansion.  The source review
found all seven declarations true, both simp bridges one-way and safe, the
positive-level hypothesis necessary, all eight legacy theorem types and
attributes unchanged, and no duplicate or competing implementation.

At immutable coordinator merge `ae16882d5`, with the sole codexbox token and
`LAKE_JOBS=1`, these separate targets exited 0:

```text
lake build +FabiusFunction.ThueMorseGenerating       # 2085 jobs
lake build +FabiusFunction.ThueMorseApproximation    # 3307 jobs
lake build +FabiusFunction.ThueMorseExponential      # 2086 jobs
lake build +FabiusFunction.PaperKFoldThueMorse       # 3327 jobs
```

`git diff --check` exits 0 and the edited Lean source contains no `sorry`,
`admit`, `axiom`, or `opaque`.  The audit evidence value `48C94725...` above is
now correctly identified as the patch SHA-256; the committed file SHA-256 is
`507136BAD10E56CE0C40876C75FE70F3A9884F6205A4E471D59A1638D52B2E9D`
(Git blob `3eeb0880b8437d7d449ed70af6d5b9c451de9abf`).  The source lease is
released; both campaign-wide documentation paths return to serialized status.
