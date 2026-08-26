# Workstream registry: `codex/fabius-shifted-prefix-grid`

**Status: source validation requested; coverage-map claim advertised.**
The exact claim was published before source work, coordinator checkpoint
`893d4c25d` explicitly acknowledged it as the first nonoverlapping claim for
the module, and source commit `00ff41a5e` now implements precisely that bounded
tranche.  The source is frozen pending compiler validation.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-shifted-prefix-grid / c9a3 / EVO
  (Windows)
fetched main SHA: e18f5d0b0e3ec78e2b14e7006af6c7e916b42923
HEAD and dirty paths: 047a03b638aafccf591d7ea5ac494d7ff8c8d9a4;
  clean after pushing the source checkpoint
writing (exact paths): docs/registry/codex-fabius-shifted-prefix-grid.md only;
  Lean/FabiusFunction/ThueMorseGenerating.lean is frozen at 00ff41a5e;
  requested future documentation path is docs/PAPER_COVERAGE.md
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
  the sharp 1 / log 2 threshold classification
completed commits: 6fb8dc8e9 publishes the exact one-file claim; ba0048023
  activates it under the open protocol; 00ff41a5e adds the seven generic
  declarations and converts all eight legacy proofs to wrappers; 047a03b63
  merges origin/main e18f5d0b0 and is pushed to the feature branch
validated (exact command, SHA/state, exit code): at source snapshot SHA-256
  784F6C4F389FE0F2FA08616FFAFBFA3917CCC9F6D2C86CE98D3D877B5F0DD14C,
  git diff --check and git diff --cached --check exited 0; python
  Analysis/FabiusFunction/scripts/doc_audit.py --baseline
  Analysis/FabiusFunction/docs/doc_audit_baseline.json scanned 189 files and
  3462 public declarations, found the same 132 baseline omissions, and exited
  0; normalized type comparison matched all eight legacy theorem statements;
  two independent hostile source/tactic reviews found no blocker; duplicate
  searches covered all 17 locally present Fabius remote-tracking tips
not yet validated: no Lean or Lake process was launched because no EVO build
  token is granted; the three requested module targets remain uncompiled
requested integration or lease: retain the source path through validation and
  assign this branch, or an authorized build owner checking commit 00ff41a5e,
  serialized targets
  +FabiusFunction.ThueMorseGenerating,
  +FabiusFunction.ThueMorseApproximation, and
  +FabiusFunction.ThueMorseExponential
conflicts / dependencies: no overlap with the active frontier-document lease;
  no AGENTS, README, collaboration, aggregate, TeX, PDF, canonical frontier,
  primary exposition, hot foundational module, or peer registry path requested;
  current EVO build ownership remains with codex/fabius-exposition-integration;
  searches of every advertised registry/tip found only historical notes that
  PAPER_COVERAGE is stale, not a current claim for that path
next bounded step: push this exact Markdown claim, fetch and reread the board
  and registries, then reconcile only docs/PAPER_COVERAGE.md while keeping the
  Lean source frozen and polling for an explicit build-token handoff
lease refreshed: 2026-08-25 17:35 PDT; source frozen pending validation;
  documentation claim awaits its registry-first push
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
