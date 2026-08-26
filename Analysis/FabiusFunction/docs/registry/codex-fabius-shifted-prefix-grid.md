# Workstream registry: `codex/fabius-shifted-prefix-grid`

**Status: exact one-file source lease requested; read-only pending coordinator
acknowledgement.**  This continuation branch starts directly from accepted
main checkpoint `431f6c173` and carries none of the historical
`codex/fabius-theorem-refinements` divergence.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-shifted-prefix-grid / c9a3 / EVO
  (Windows)
fetched main SHA: 431f6c17376fc89ccd9eded293b65cb5624e5b94
HEAD and dirty paths: 431f6c17376fc89ccd9eded293b65cb5624e5b94;
  clean before this registry-only claim
writing (exact paths): docs/registry/codex-fabius-shifted-prefix-grid.md only;
  requested future source path is Lean/FabiusFunction/ThueMorseGenerating.lean
expected declarations or document claims: shiftedPrefixGridValue;
  shiftedPrefixGridValue_zero; shiftedPrefixGridValue_one;
  shiftedPrefixGridValue_succ_sub;
  shiftedPrefixGridValue_scaledDifference;
  shiftedPrefixGridValue_equation; and
  shiftedPrefixGridValue_equation_of_pos; retain the eight existing
  paperPrefixGridValue_* and correctedPrefixGridValue_* theorem statements
  exactly as compatibility wrappers
completed commits: none on this continuation branch before this registry claim
validated (exact command, SHA/state, exit code): no build launched; three
  independent read-only source/API reviews agreed on the abstraction and one
  hostile review required preserving both legacy definitions verbatim; exact
  duplicate searches covered current main, all 15 advertised Fabius remote
  tips, their registries, and reachable history
not yet validated: proposed Lean source is not written or compiled; the
  coordinator-reserved build token was not used
requested integration or lease: exact write lease for
  Lean/FabiusFunction/ThueMorseGenerating.lean, with later serialized targets
  +FabiusFunction.ThueMorseGenerating,
  +FabiusFunction.ThueMorseApproximation, and
  +FabiusFunction.ThueMorseExponential when the board assigns the EVO token
conflicts / dependencies: no overlap with the active frontier-document lease;
  no AGENTS, README, collaboration, aggregate, TeX, PDF, canonical frontier,
  primary exposition, hot foundational module, or peer registry path requested
next bounded step: push this registry-only claim to the named feature branch,
  then remain read-only until the coordinator acknowledges the exact source
  and build leases
```

## Proposed bounded refactor

`ThueMorseGenerating.lean` currently proves four theorem pairs independently:

- `paperPrefixGridValue_succ_sub` and
  `correctedPrefixGridValue_succ_sub`;
- `paperPrefixGridValue_scaledDifference` and
  `correctedPrefixGridValue_scaledDifference`;
- `paperPrefixGridValue_equation` and
  `correctedPrefixGridValue_equation`; and
- `paperPrefixGridValue_equation_of_pos` and
  `correctedPrefixGridValue_equation_of_pos`.

After replacing only the two grid identifiers by a neutral token and
normalizing whitespace, each pair is alpha-identical.  The intended
abstraction is the normalized grid whose inclusive-prefix order is shifted by
an arbitrary natural number while its denominator and abscissa remain at the
same grid level:

```lean
def shiftedPrefixGridValue (s k j : ℕ) : ℚ :=
  (iteratedPrefix (k + s) j : ℚ) / (2 : ℚ) ^ k.choose 2
```

The source tranche would prove the forward-difference law, its
denominator-cleared form, the equation paired with the exact unit-interval
domain condition, and the positive-level reindexing once for arbitrary `s`.
Shift zero and shift one recover the literal paper grid and the corrected
inclusive-prefix grid.

## Compatibility boundary

The existing public definitions will remain textually unchanged:

```lean
def paperPrefixGridValue (k j : ℕ) : ℚ :=
  (iteratedPrefix k j : ℚ) / (2 : ℚ) ^ k.choose 2

def correctedPrefixGridValue (k j : ℕ) : ℚ :=
  (iteratedPrefix (k + 1) j : ℚ) / (2 : ℚ) ^ k.choose 2
```

This preserves both definitional reduction and the behavior of client proofs
that explicitly unfold either name.  Two one-way simp bridges will normalize
`shiftedPrefixGridValue 0` to `paperPrefixGridValue` and
`shiftedPrefixGridValue 1` to `correctedPrefixGridValue`; reverse simp rules
will not be added.  The eight existing theorem headers, binder order,
hypotheses, conjunction order, attributes, and result syntax will also remain
unchanged.  Only their duplicated proof bodies become specializations of the
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

No new import is expected.  The module has two direct consumers,
`ThueMorseApproximation.lean` and `ThueMorseExponential.lean`; no source file
outside `ThueMorseGenerating.lean` calls any of the eight wrapper theorems.

## Duplicate search and deferred opportunities

The exact proposed names and plausible `shifted`/`offset` aliases were searched
on current main, all 15 locally advertised Fabius branch tips, every registry
at those tips, and reachable history.  No equivalent declaration or active
claim exists.  This is distinct from the human document's Appell family and
from the translated Thue--Morse polynomial degree API already integrated from
`a95bd1913`.

Three worthwhile but intentionally separate follow-ups were identified:

1. clearing an arbitrary number of `(1 - X)` factors lowers
   `iteratedPrefixSeries (k + n)` exactly to order `k`;
2. a public two-parameter finite-block coefficient bridge can replace a
   narrower private helper in `ThueMorseApproximation.lean`; and
3. translated Thue--Morse blocks satisfy finite addition and formal-derivative
   laws, furnishing a genuine polynomial translation calculus.

None is included in this lease request.  Keeping the first commit to one
mechanically evidenced duplication class makes the review, build attribution,
and rollback boundary exact.
