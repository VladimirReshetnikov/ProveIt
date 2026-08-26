# Workstream registry: `codex/fabius-both-papers`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-both-papers /
  /home/codex/src/Proofs / codexbox
fetched main SHA: c9d20ed14c7572d4f3f1361c7883085eaf5bb0d8
HEAD and dirty paths: 813ea82cf566f409c1ffa42669f32b0556d925f9;
  clean before this ordinary one-source claim
writing (exact paths):
  Lean/FabiusFunction/PeriodicSmooth.lean;
  docs/registry/codex-fabius-both-papers.md
expected declarations or document claims:
  `forwardDerivativeQuotientPolynomial_one`,
  `forwardDerivativeQuotientPolynomial_two`,
  `forwardDerivativeQuotientPolynomial_three`,
  `negativeLaplaceForwardTermDeriv_two`,
  `negativeLaplaceForwardTermDeriv_three`, and
  `negativeLaplaceForwardTermDeriv_four`; these `[simp]` bridges identify the
  first three quotient polynomials and reconcile the unified all-order
  derivative family with the existing explicit second-, third-, and
  fourth-order summands
completed commits: Lower-Lambert source checkpoint `1da2fde2285e3970267b7dc2561bcd0d897be1b4`
  was integrated by coordinator merge `046946a974467e83244fd3a183a3e084e70d3379`;
  registry handoff `225f5338de9ea92489ed6a2c0c371c6edb4f5db9`
  closed that slice and recorded the frozen documentation gaps;
  claim commit `0cb92989d580228917a99293647411ba85d6d452`
  advertised this exact one-source-file tranche; merge
  `f1b33700b6da547acea678791e77a06b2e326521` synchronized it with the first
  fetched main; source checkpoint `34fec97bd4d5ff0b034c305fef6a9e7d26fec2f7`
  implements both declarations and is explicitly unvalidated; merge
  `f546c38e5b6ddde6f68825798ab34c003e5c6930` synchronizes that checkpoint with
  current fetched main `e18f5d0b0`; static-proof correction
  `0095fb161db5e6ef03df7bd391fbf45e96efc792` aligns the odd branch with the
  literal `2 * b + 1` witness; checkpoint
  `c1d681f70dedad3a708a8baa0c06113390bf6a28` matches the coordinator's exact
  directly elaborated module blob; claim expansion
  `5db4ab6f9add0aed692e746da0dc0a7fb9ce23fd` advertises the two exact dyadic
  relocation paths before authoring; source checkpoint
  `09b360531d69a9bc93dba1babc3d5ecc6a396347` moves the theorem upstream
  byte-for-byte and preserves its single public declaration site; registry
  handoff `aaca79f866509b99271ae2c633f81c8162845e16` records the clean relocation
  review; terminology checkpoint
  `45d38dc4147eb7e67a9c6f5cdced1328926b719d` replaces the ambiguous “natural
  knot” shorthand by “nonnegative integer grid point” without changing code;
  exact Gamma--zeta claim `1f40ac305983c01f789642e714d56eef6d48519c`
  precedes source checkpoint `ec23d663f1ff478c8d99719a2dc43aa83afe4d30`,
  and proof/docstring polish `991add419fb7fda185f4a79cb87cae59f3b37205`
  leaves the final five-theorem strict API; clean merge
  `00f0edfe244ad1ceea964cf3855314b9beeb0e71` incorporates validated current main
  `148990f0a`; exact inverse-power bridge claim
  `f858c1bd938932a32c0a73551b5944a3cd3c3a0b` precedes unvalidated source
  checkpoint `9458b1949cfb1b0a0290c0ab533a50d2e8ff908d`, which adds the one-line
  `fabiusAtInverseTwoPow_cast` specialization without changing any existing
  declaration; periodic consolidation claim `896e25742` and exact-domain
  expansion `10717109f` precede unvalidated source checkpoint
  `c7c2321bc6ea7292996b40dd333d4d148f7e75d5`, whose net source delta is 40
  insertions and 58 deletions; clean merge
  `c41a522839850a699f7de8a2f07e15180ae45f7d` incorporates validated current
  main `c9eac55c5`; exact complex-zero claim `446911e31` precedes unvalidated
  source checkpoint `64a95d363cec9647cdd6c93bd63bba1d1d5e11da`, which adds the three
  public iff theorems and one private dyadic-factor bridge; clean merge
  `80c6643abc68213ec1bef60db1e13bf9707c3e00` incorporates current main
  `407da44a6`; exact half-q root-locus claim `301ca2d60` precedes source
  checkpoint `a987b3bb9e983ff771729e2ad20699959a72bfb8`, whose 67 insertions and four
  deletions add the generic rational product-zero criterion, its complete
  `q = 1/2` rational specialization, and both q-binomial transports; exact
  private-only claim `5510369dd` precedes source checkpoint
  `d2df7eaa72ca032ebbf5f7fc731e665edc6087b3`, which factors the two support
  localization proofs and removes redundant/dead helpers for a net reduction
  of 47 lines; clean merge `47d5758467a367eb6962fa0aa11b8834ef10f680`
  incorporates fetched main `c2aa5a25c`; clean merge
  `1064891788f5fd3717fdb45e28f91436daf4fd42` incorporates current fetched main
  `682222de1`; exact non-equivalence claim `9609bee93` precedes source
  checkpoint `45b4816c06f6d9e735df97de80e98ccb2447023c`, which proves that the
  exponential of the literal uncorrected Wikipedia logarithmic expression is
  not asymptotically equivalent to any bounded Fabius solution at the positive
  zero endpoint; clean merge `4694e0d96ed33da24d5dffeb58a4ce510ff18e98`
  incorporates current fetched main `c9d20ed14`
validated (exact command, SHA/state, exit code): coordinator board records
  serialized immutable `lake build +FabiusFunction.LowerLambertW` at
  `4c6bbac41`, exit 0, with its source blob unchanged on current main;
  read-only integer-grid audits at `12e7137a8` and refreshed main found no exact or semantic
  duplicate across all advertised tips and verified the theorem domains,
  edge cases, placement, imports, and public export path; coordinator commit
  `62f4142a9f290c570299e200192a4818dc7529d2` directly ran
  `LAKE_JOBS=1 lake env lean` on the corrected module and exited 0; coordinator
  acceptance `148990f0a` records separate one-job builds of
  `+FabiusFunction.GlobalExtension` (2765 jobs) and
  `+FabiusFunction.Paper06487` (3244 jobs), both exit 0; the current source
  differs from that green proof-bearing blob only in doc-comment words;
  read-only review of `09b360531` confirmed the moved block is byte-identical,
  imports and namespace placement suffice, the downstream theorem resolves
  through its existing direct import, and all static hygiene checks pass
not yet validated: the moved dyadic theorem body was already compiled in its
  downstream home by the green
  aggregate at `9887ea584`, but its new module ownership/import context has not
  been compiled; only read-only source/collision/marker/diff checks are
  currently validated for that relocation; the Gamma--zeta
  sign source checkpoint is implemented and has independent term-level static
  review, but has not been elaborated or built in production; its predecessor
  non-strict `/tmp` proof was green, while the strict logarithmic and large
  kernel upgrades are statically reviewed only; the exact inverse-power bridge
  is implemented at `9458b1949`, and its proof, placement, normalization, and
  public API have two independent static reviews plus a previously green
  `/tmp` prototype, but the production module has not been elaborated or built;
  the periodic consolidation at `c7c2321bc` has two independent complete static
  reviews covering all call sites, theorem hypotheses, import/facade exposure,
  collisions, markers, and diff hygiene, but neither edited module has been
  elaborated or built in this production context; the complex zero-locus
  checkpoint at `64a95d363` has three independent static reviews covering the
  sinc simplification, dyadic cancellation, integer/complex coercions,
  infinite-product nonvanishing API, theorem order, collisions, imports,
  facade exposure, and source hygiene, but has not been elaborated or built;
  the half-q root-locus checkpoint at `a987b3bb9` has three independent
  read-only reviews covering `Finset.prod_eq_zero_iff`, both `sub_eq_zero`
  orientations, half-power cancellation, q-binomial transports, `n = 0`,
  `j = 0`, `q = 0`, `q = 1`, arbitrary rational arguments, API placement,
  rational-only documentation, collisions, forbidden markers, and diff
  hygiene, but no Lean or Lake process has elaborated the production file;
  the private AnalyticMoments checkpoint at `d2df7eaa7` has three independent
  read-only reviews covering the hidden real normed-space requirement, support
  composition and orientation, open/half-open endpoint handling, real and
  complex support coercions, all endpoint replacements, dead-code removal,
  caller preservation, exact public-declaration identity, imports, markers,
  and diff hygiene, but has not been elaborated or built; the Wikipedia
  non-equivalence checkpoint has three independent read-only reviews covering
  the exact asymptotic-equivalence API, ratio/log transfer, eventual
  positivity, corrected-term sign, limit normalization, congruence
  orientations, theorem placement, collision sweep, facade exposure, module
  prose, forbidden markers, and diff hygiene, but has not been elaborated or
  built
requested integration or lease: the dyadic relocation needs serialized
  `+FabiusFunction.GlobalDyadic`
  and `+FabiusFunction.OriginalPaperSupplement` validation; this new ordinary
  source checkpoint needs serialized `+FabiusFunction.DyadicAnalytic`
  validation; the `DyadicAnalytic.lean` writing claim is released by this
  handoff; the Gamma--zeta checkpoint needs serialized
  `+FabiusFunction.BoseFinitePartIntegral` followed by its sole non-facade
  direct importer `+FabiusFunction.PeriodicMean`;
  the periodic checkpoint needs serialized `+FabiusFunction.PeriodicSmooth`,
  which transitively covers its upstream `PeriodicRegularity` dependency; both
  periodic source writing claims are released by this handoff;
  the Fourier zero-locus checkpoint needs serialized
  `+FabiusFunction.FourierProduct`, and its source writing claim is released by
  that handoff; the half-q root-locus checkpoint needs serialized
  `+FabiusFunction.HalfQBinomial` followed by its direct consumer
  `+FabiusFunction.FabiusQBinomialFormula`, and the `HalfQBinomial.lean` source
  writing claim is released by that handoff; the private AnalyticMoments
  checkpoint needs serialized `+FabiusFunction.AnalyticMoments`, and the
  `AnalyticMoments.lean` source writing claim is released by this handoff;
  the Wikipedia non-equivalence checkpoint needs serialized
  `+FabiusFunction.FabiusSharpAsymptotic` followed by
  `+FabiusFunction.PaperFabiusAsymptotic`, and its source writing claim is
  released by this handoff;
  serialized README/primary/walkthrough/coverage paths are deliberately not
  claimed yet
conflicts / dependencies: all advertised Fabius heads and their registries
  were checked; no branch claims GlobalExtension and the only overlap is the
  existing even/odd ingredients and downstream special cases that this API
  packages without modifying; local coordinator candidate merge
  `8d27ea2079ca4146d02ae104dfd48b06f388f49c` contains the pre-correction source
  checkpoint, while follow-up `62f4142a9f290c570299e200192a4818dc7529d2`
  supplies both the literal odd witness and explicit rewrite arguments;
  read-only audit across advertised tips found no competing claim or alternate
  total dyadic-cast bridge on either relocation path; documentation remains
  serialized and unclaimed; a refreshed exact-name, semantic-shape, path, and
  registry sweep across every advertised remote Fabius tip found no existing
  strict Gamma--zeta sign theorem and no competing claim on
  `BoseFinitePartIntegral.lean`; the board explicitly releases old Gamma--zeta
  leases; a fresh post-merge sweep across every advertised tip finds no exact
  or semantic public inverse-power cast bridge, and no active claim on
  `DyadicAnalytic.lean`; existing scalar q-binomial cast theorems have different
  right-hand sides, while the same mathematics occurs only behind private
  wrappers in `DyadicAnalytic`; the periodic helper family is already recorded
  as an unimplemented high-confidence deduplication in `AUDIT_FINDINGS.md`, and
  a fresh sweep of every advertised Fabius tip and registry finds no production
  declaration, alternate public API, or live claim on either periodic module;
  the only registry mention is a closed historical read-only list; a refreshed
  sweep of current main and every advertised remote Fabius tip finds no exact
  name, semantic-equivalent complete complex zero-locus theorem, or registry
  claim on `FourierProduct.lean`; the current file already contains precisely
  the sinc zero criterion, absolute product convergence, and integer-zero facts
  needed by the proposed proof; current main and every advertised remote Fabius
  or Claude tip contain only the dyadic-input q-Pochhammer iff, not an
  arbitrary-rational root classification, and no registry claims
  `HalfQBinomial.lean`; its coefficient-index zero theorem is semantically
  distinct from this polynomial-root locus; a refreshed path/name sweep across
  current main and every advertised Fabius tip finds no active claim on
  `AnalyticMoments.lean` and no alternate private generic localization helper;
  the public endpoint and support lemmas needed for the consolidation already
  live upstream in `Basic.lean`; fetched main `c2aa5a25c` retains the exact
  pre-cleanup AnalyticMoments blob used as the source base; exact-name,
  semantic-shape, path, and registry sweeps across current main and every
  advertised Fabius tip find no implemented uncorrected-Wikipedia
  `not_isEquivalent` theorem and no competing claim on
  `FabiusSharpAsymptotic.lean`; the coordinator explicitly released its prior
  generalizations lease
next bounded step: push this exact ordinary source claim, finish the advertised
  cross-tip collision scan, implement the six bridge theorems without running
  a build, and request serialized `+FabiusFunction.PeriodicSmooth` validation
```

## Coordinator natural-knot integration disposition

The two-declaration source tranche is accepted.  Independent theorem/API
review found the formulas true at every natural knot and derivative order,
including `m = 0`, `m = 1`, and `order = 0`; the placement and imports are
appropriate and no existing public signature changes.  There is no
implemented Lean duplicate.  The exact iff proposition occurs only as a
proposal in `docs/AUDIT_FINDINGS.md`, while the existing even/odd and
power-of-two results are ingredients or special cases.

The coordinator first merged the feature checkpoint at `8d27ea207`, then
fixed three elaboration sites at `62f4142a9`: the odd witness is kept in the
literal `2 * b + 1` form, and both downstream rewrites pass `F` and `hF`
explicitly.  Merge `068fc1be5` reconciles the feature branch's correction and
registry handoff.  At that exact immutable Lean tree, with the sole codexbox
token and `LAKE_JOBS=1`, these separate one-target invocations exited 0:

```text
lake build +FabiusFunction.GlobalExtension       # 2765 jobs
lake build +FabiusFunction.Paper06487             # 3244 jobs
```

The facade build transitively covers `PaperStatements` and
`Paper06487Supplement`.  `git diff --check` exited 0 and the edited source
contains no `sorry`, `admit`, `axiom`, or `opaque`.  This disposition
supersedes the worker snapshot's pre-correction warning and unvalidated state;
the `GlobalExtension.lean` lease is released.

Source-only subagents inspect and prototype in `/tmp`; they do not edit the
leased production paths, run builds, or mutate Git state.

Read-only prototype inventory reported under the coordinator freeze:

- `/tmp/FabiusInversePowerBridgeAudit.lean` compiled before the freeze and
  packages the existing inverse-power identity as
  `fabiusAtInverseTwoPow_cast`; no production edit or integration request.
- `/tmp/FabiusGammaZetaSignAudit.lean` compiled before the freeze and proves
  strict negativity of `gammaZetaConstant` and the corresponding strict upper
  bound for `firstStieltjesConstant`; no production edit or integration
  request.
- `/tmp/FabiusNatDerivativeAudit.lean` compiled before the freeze and proves
  the sharp nonnegative-integer-grid classification
  `iteratedDeriv_extendedFabius_natCast_eq_zero_iff`; no production edit or
  integration request.

Read-only Lower-Lambert documentation handoff for the semantic integrator:

- The source docstrings should call `Ico (-exp (-1)) 0` the natural domain and
  reserve “smooth interior” for `Ioo (-exp (-1)) 0`; several inherited open
  theorem comments still call the latter the natural domain.
- `PAPER_COVERAGE.md` still advertises only the strict equation-(9) domain and
  the three open wrappers.  The README, primary exposition, walkthrough, and
  frontier omit the endpoint value, closed equation/uniqueness/order/range,
  and endpoint-inclusive phase classification.
- The frontier's phase-locked large-branch condition `n + u > 0` must be
  `n + u > 1 / log 2` (eventually), matching the lower branch.
- A future semantic documentation pass must rebuild the primary exposition,
  walkthrough, and canonical-frontier PDFs; no PDF conflict resolution is
  appropriate.
