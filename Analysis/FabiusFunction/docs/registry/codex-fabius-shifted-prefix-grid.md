# Workstream registry: `codex/fabius-shifted-prefix-grid`

**Status: finite-jet source checkpoint accepted, compiled, and released; the
advertised same-path all-order refinement and disjoint one-file finite-Appell
claim are active without a local build token.**
The exact claim was published before source work, coordinator checkpoint
`893d4c25d` explicitly acknowledged it as the first nonoverlapping claim for
the module, and source commit `00ff41a5e` now implements precisely that bounded
tranche.  Documentation commit `dcd5f8a06` now reconciles the four advertised
coverage clusters.  Coordinator checkpoint `c9eac55c5` accepts all three
units, records four green focused builds at merge `ae16882d5`, and releases the
source lease.
Audit-ledger commit `faf1fcaf6` was
completed and pushed before coordinator checkpoint `148990f0a` newly serialized
both campaign-wide Markdown paths.  Those paths remain serialized.  After
merging current main at `77c15879f`, this branch now advertises the exact
two-file finite-jet claim below before editing either source.  Source commit
`51af7f7e1` now implements exactly that claim.  After merging current main at
`1381df9bb`, the branch records below the precise module-guide corrections and
three all-order approximation declarations proposed for the next bounded
checkpoint.  Coordinator extraction `62ab80d03` validates the finite-jet
source, and checkpoint `682222de1` releases both paths for that advertised
follow-up.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-shifted-prefix-grid / c9a3 / EVO
  (Windows)
fetched main SHA: 682222de194637f3a5650b7c1ffce349577cb5ae
HEAD and dirty paths: 6413191f128684b966347a284218a54547fddab7;
  docs/registry/codex-fabius-shifted-prefix-grid.md only, recording coordinator
  validation/release and correcting the finite-jet Generating blob evidence
writing (exact paths): docs/registry/codex-fabius-shifted-prefix-grid.md only;
  after this registry correction is pushed, exactly
  Lean/FabiusFunction/FabiusQBinomialTaylor.lean,
  Lean/FabiusFunction/ThueMorseGenerating.lean and
  Lean/FabiusFunction/ThueMorseApproximation.lean
expected declarations or document claims:
  active finite-Appell claim in FabiusQBinomialTaylor.lean:
  thueMorseTranslatedPowerSumPolynomial_comp_X_add_C, the canonical finite
  translation law with range (d + 1);
  thueMorseTranslatedPowerSumPolynomial_hasseDeriv, total in the derivative
  order j and requiring no j <= d or k <= d hypothesis;
  thueMorseTranslatedPowerSumPolynomial_derivative, the all-d ordinary
  derivative specialization including d = 0; and the subtraction-free
  thueMorseTranslatedPowerSumPolynomial_derivative_succ compatibility-style
  convenience form, matching the established dyadic-kernel API;
  add the direct Mathlib.Algebra.Polynomial.HasseDeriv import and one accurate
  module-guide sentence identifying the finite translation/Appell structure;
  active released same-path follow-up:
  coeff_thueMorseBlockPolynomial_mul_eq_thueMorseSeries_mul and
  coeff_thueMorseBlockPolynomial_mul_invOneSubPow_eq_iteratedPrefix in the
  upstream generating-series module;
  iteratedPrefix_eq_approximationPolynomial_coeff_all in the approximation
  module; delete the subsumed downstream private
  coeff_thueMorseSeries_mul_inv_eq_finite; retain the exact public header,
  binders, argument order, type, and attributes of
  iteratedPrefix_eq_approximationPolynomial_coeff as a compatibility wrapper;
  simplify its sole downstream caller to use the all-order theorem;
  in the proposed follow-up, add
  one_sub_X_pow_mul_approximationPolynomialInt_all and
  thueMorseBlockPolynomial_mul_invOneSubPow_eq_approximationPolynomialInt,
  making the polynomial and power-series factorizations uniform at order zero
  and turning iteratedPrefix_eq_approximationPolynomial_coeff_all into one
  case-free coefficient calculation; add
  correctedPrefixCoefficient_eq_stepApproximant_all without a positivity
  hypothesis, retain the exact header and type of
  correctedPrefixCoefficient_eq_stepApproximant as a compatibility wrapper,
  and route the moving-cell caller through the all-order form
expected documentation claims: in the active one-file claim, extend the module
  guide and declaration comments with the block-level Appell mechanism and
  record its exact relationship to the assembled Appell identities currently
  stated in the serialized research-frontier document; no frontier edit or PDF
  build is requested; in the proposed finite-jet follow-up, correct two
  guide-level precision issues: distinguish the literal formal-power-series
  prefix identity from coefficientwise finite stabilization of the
  infinite-product shorthand in ThueMorseGenerating.lean, and say that the
  order-zero cutoff admits only index zero rather than suggesting the series
  has only one coefficient in ThueMorseApproximation.lean; document both new
  all-order factorizations and the all-order histogram bridge; do not edit a
  campaign-wide Markdown, TeX, PDF, root aggregate, or other serialized path
completed commits: 6fb8dc8e9 publishes the exact one-file claim; ba0048023
  activates it under the open protocol; 00ff41a5e adds the seven generic
  declarations and converts all eight legacy proofs to wrappers; 047a03b63
  merges origin/main e18f5d0b0; e2d1db43f advertises the exact coverage-map
  reconciliation; dcd5f8a06 completes and releases that documentation tranche;
  0d4ee2471 advertises the exact four-finding audit claim; faf1fcaf6 closes
  those four stale entries and records their compiler provenance; e0302acdf
  records the completed documentation checkpoints; 3161da511 merges current
  origin/main 148990f0a without conflicts; 8ea040921 reports the resulting
  branch-specific freeze and coordinator handoff; c8501fa81 preserves the
  read-only finite-block preflight; 77c15879f semantically resolves the sole
  own-registry conflict while merging origin/main ba2be1b78; 4cb8d7676
  publishes the exact two-file claim; 122788a95 merges the frontier
  build-authorization checkpoint 383bc9672 before source work; 585f8f8ba moves
  both convolution bridges to their minimal generating-series dependency;
  51af7f7e1 implements the complete two-file source tranche; 7c6eaeff9 records
  its validation request; 1381df9bb merges the main checkpoint 407da44a6
  without conflicts; 4ade2afd7 advertises the all-order same-path follow-up
  without unfreezing source; 5e7ee8309 merges coordinator checkpoint
  c2aa5a25c without conflicts and preserves both frozen source blobs;
  a0b289ee7 records the synchronized 25-ref collision audit; e38876942
  publishes the disjoint finite-Appell claim; 6413191f1 merges the validated
  finite-jet acceptance checkpoint 682222de1 without conflicts
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
  source blob, implementation commit, and immutable build checkpoint; the
  value 48C94725FB082D492CCE495D01ADDED851C357DB4D4DED4AB375C3C7E7504E4 is
  the audit patch SHA-256, while the accepted committed file has SHA-256
  507136BAD10E56CE0C40876C75FE70F3A9884F6205A4E471D59A1638D52B2E9D
  and Git blob 3eeb0880b8437d7d449ed70af6d5b9c451de9abf;
  coordinator merge ae16882d5 subsequently validated
  +FabiusFunction.ThueMorseGenerating (2085 jobs),
  +FabiusFunction.ThueMorseApproximation (3307 jobs),
  +FabiusFunction.ThueMorseExponential (2086 jobs), and
  +FabiusFunction.PaperKFoldThueMorse (3327 jobs), all exit 0; at source commit
  51af7f7e1, git diff --check and git diff --cached --check exited 0, the
  forbidden-token scan found no added sorry/admit/axiom/opaque, exact comparison
  preserved the old public theorem header and absence of attributes, and python
  Analysis/FabiusFunction/scripts/doc_audit.py --baseline
  Analysis/FabiusFunction/docs/doc_audit_baseline.json scanned 189 files and
  3476 public declarations with the unchanged 132 baseline omissions, exit 0;
  two independent hostile source/Mathlib reviews found no mathematical,
  declaration-order, tactic, compatibility, simplifier, or documentation
  blocker; corrected implemented blobs are Generating 2908f1f1652e (SHA-256
  04F8F9AB915928A98FC422C3A5048C53110FD67C29007CE55483A853561A8D9C)
  and Approximation b27b38fbc (SHA-256
  1108CE8C50AAEF02A8C5A7705916D1D70A0AD993005F33AAC27AE83C76E783FE);
  the follow-up collision audit covered all 25 concrete locally fetched origin
  refs, every current registry, and reachable exact-name history: no peer owns
  either path, no source defines a proposed name, and the sole registry
  occurrence is this branch's proposal; git diff --check at merge 5e7ee8309
  exits 0 with no unmerged or dirty path; coordinator source extraction
  62ab80d03 ran serialized LAKE_JOBS=1 builds of
  +FabiusFunction.ThueMorseGenerating (2085 jobs),
  +FabiusFunction.ThueMorseApproximation (3307 jobs),
  +FabiusFunction.ThueMorseExponential (2086 jobs), and
  +FabiusFunction.PaperKFoldThueMorse (3327 jobs), all exit 0, and released both
  finite-jet paths at main checkpoint 682222de1
not yet validated: the active all-order follow-up and finite-Appell claim have
  not been implemented or compiled; no Lean or Lake process is authorized
  because both physical-host tokens remain coordinator-reserved
requested integration or lease: after both active source tranches are
  implemented, reviewed, and frozen, assign the coordinator-held targets
  +FabiusFunction.FabiusQBinomialTaylor,
  +FabiusFunction.ThueMorseGenerating,
  +FabiusFunction.ThueMorseApproximation,
  +FabiusFunction.ThueMorseExponential, and
  +FabiusFunction.PaperKFoldThueMorse at that immutable checkpoint or its exact
  coordinator merge
conflicts / dependencies: no overlap with the active frontier-document lease;
  no AGENTS, README, collaboration, aggregate, TeX, PDF, canonical frontier,
  primary exposition, hot foundational module, or peer registry path requested;
  current main keeps docs/PAPER_COVERAGE.md and docs/AUDIT_FINDINGS.md
  serialized; main checkpoint 682222de1 explicitly accepts and releases the
  finite-jet source paths for the advertised all-order refinement; a
  post-claim scan pinned all 16 locally available Fabius worker tips plus
  origin/main and found no competing claim or proposed declaration under an
  exact or plausible alternate name; the fresh 25-ref review reaches the same
  conclusion; FabiusQBinomialTaylor.lean has no live peer claim,
  none of the four exact Appell names exists in any fetched source, and the
  analogous private dyadic-kernel family is mathematically distinct; no path
  expansion beyond the three active source files and this branch registry is
  requested
next bounded step: push this validation/release correction, fetch and reread
  the board, implement the module-guide corrections and four finite-Appell
  declarations, then implement the all-order approximation tranche; obtain two
  independent read-only reviews and freeze each source checkpoint without
  invoking an unassigned validator
lease refreshed: 2026-08-25 19:38 PDT; registry-only until pushed, then
  FabiusQBinomialTaylor.lean, ThueMorseGenerating.lean, and
  ThueMorseApproximation.lean are active for 30 minutes
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

## Implemented finite-jet design

Coordinator checkpoint `c9eac55c5` accepts and validates the prior source and
documentation tranches and releases the source lease.  Merge `77c15879f`
incorporates current main, and the `SYNC Fabius` block above now advertises the
exact source lease before any theorem edit.

Both convolution theorems belong in the upstream-most module that can state
them, `Lean/FabiusFunction/ThueMorseGenerating.lean`, whose current `HEAD` and
`origin/main` blob is
`a670c07ea215cbf85eb76db0886d2898e20d4f6a` (SHA-256
`784F6C4F389FE0F2FA08616FFAFBFA3917CCC9F6D2C86CE98D3D877B5F0DD14C`).
The polynomial-coefficient strengthening and compatibility wrapper belong in
`Lean/FabiusFunction/ThueMorseApproximation.lean`, whose corresponding blob is
`fb0e20a0e303403df358b925f262f7bead0d03e4` (SHA-256
`045DF230FA224D417D3ED11AFE55F1569F74402833B30BAF008D8D6828A9F47F`).
These were the exact base blobs and matched current `origin/main` before the
source edit.  Fresh searches of all 16 locally available Fabius remote-tracking
tips found
neither an active claim for either path nor any of the proposed names.

Three independent read-only reviews converged on this public API:

```lean
theorem coeff_thueMorseBlockPolynomial_mul_eq_thueMorseSeries_mul
    (f : PowerSeries ℤ) (r m : ℕ) (hm : m < 2 ^ r) :
    PowerSeries.coeff m
        ((thueMorseBlockPolynomial r : PowerSeries ℤ) * f) =
      PowerSeries.coeff m (thueMorseSeries * f)

theorem coeff_thueMorseBlockPolynomial_mul_invOneSubPow_eq_iteratedPrefix
    (r k m : ℕ) (hm : m < 2 ^ r) :
    PowerSeries.coeff m
        ((thueMorseBlockPolynomial r : PowerSeries ℤ) *
          (PowerSeries.invOneSubPow ℤ k).val) =
      iteratedPrefix k m

theorem iteratedPrefix_eq_approximationPolynomial_coeff_all
    (k m : ℕ) (hm : m < 2 ^ k) :
    iteratedPrefix k m =
      ((approximationPolynomial (k - 1)).coeff m : ℤ)
```

The first theorem exposes the actual finite-jet invariant: below the first
omitted dyadic coefficient, right convolution by an arbitrary integer power
series cannot distinguish the finite block from the infinite Thue--Morse
series.  Its proof is exactly the existing private antidiagonal argument with
the formerly conflated block depth and prefix order separated.  The second is
the semantic `invOneSubPow` specialization, using `iteratedPrefixSeries_eq` and
`coeff_iteratedPrefixSeries`.  Neither theorem should be a simp rule.

The all-order approximation theorem adds the real boundary case hidden by the
old positivity hypothesis.  At `k = 0`, its cutoff forces `m = 0`, natural
subtraction makes `k - 1 = 0`, and both sides are one.  The successor proof is
the finite-block specialization followed by
`thueMorseBlock_mul_inv_eq_approximationPolynomialInt`.  The existing public
`iteratedPrefix_eq_approximationPolynomial_coeff` must retain its exact binder
names, order, hypothesis, conclusion, and attributes as a compatibility
wrapper; its sole downstream caller can use the all-order form and drop a
redundant positivity proof.  The narrower private
`coeff_thueMorseSeries_mul_inv_eq_finite` is then deleted.

The cutoff `m < 2^r` is sharp.  At `m = 2^r`, prefix order zero and multiplier
one, the finite block coefficient is zero while the new Thue--Morse coefficient
is `-1`.  No relation between `r` and `k` is needed, and both `r = 0` and
`k = 0` are valid.  This preflight checked every identifier and rewrite
direction against the current project and Mathlib sources; two separate hostile
reviews found no mathematical, API, tactic, dependency, or simplifier blocker.
Commit `51af7f7e1` implements the design with the exact source blobs recorded in
the `SYNC Fabius` block.  Coordinator extraction `62ab80d03` subsequently
compiled all four requested targets successfully and released both source
paths at `682222de1`.

## Claimed finite-Appell calculus

The disjoint one-file follow-up in `FabiusQBinomialTaylor.lean` exposes the
translated Thue--Morse blocks as a finite Appell family.  Writing
`P_(k,d)` for `thueMorseTranslatedPowerSumPolynomial k d`, the exact public
statements are:

```lean
theorem thueMorseTranslatedPowerSumPolynomial_comp_X_add_C
    (c : ℚ) (k d : ℕ) :
    (thueMorseTranslatedPowerSumPolynomial k d).comp
        (Polynomial.X + Polynomial.C c) =
      ∑ j ∈ Finset.range (d + 1),
        Polynomial.C ((d.choose j : ℚ) * c ^ j) *
          thueMorseTranslatedPowerSumPolynomial k (d - j)

theorem thueMorseTranslatedPowerSumPolynomial_hasseDeriv
    (k d j : ℕ) :
    Polynomial.hasseDeriv j
        (thueMorseTranslatedPowerSumPolynomial k d) =
      Polynomial.C (d.choose j : ℚ) *
        thueMorseTranslatedPowerSumPolynomial k (d - j)

theorem thueMorseTranslatedPowerSumPolynomial_derivative
    (k d : ℕ) :
    (thueMorseTranslatedPowerSumPolynomial k d).derivative =
      Polynomial.C (d : ℚ) *
        thueMorseTranslatedPowerSumPolynomial k (d - 1)
```

Writing `P_(k,d)` below is only compact registry prose.  A fourth
successor-indexed wrapper removes natural subtraction for rewriting.  No
theorem receives a `simp` attribute: the composition law expands into a sum,
while the Hasse law is a deliberate semantic bridge.

The composition proof evaluates both sides and applies the ordinary binomial
theorem inside the finite Thue--Morse sum.  The Hasse proof is coefficientwise:
`Polynomial.hasseDeriv_coeff` and the existing exact coefficient theorem reduce
it to `Nat.choose_mul`.  The ordinary derivative is the `j = 1` specialization.
All statements are total: `j > d`, `d = 0`, `d < k`, `d = k`, `k = 0`, and
translation `c = 0` need no separate hypotheses or branches.

The exact names and path were absent from every fetched source and live
registry.  The similarly shaped private dyadic-kernel calculus is a distinct
polynomial family.  The closest human counterparts are the assembled Appell
derivative and addition formulas in the serialized research-frontier document;
the new theorems expose their block-level algebraic mechanism.  This claim does
not request an edit or build of that TeX/PDF pair.
