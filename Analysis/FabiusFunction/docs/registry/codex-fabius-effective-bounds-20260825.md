# Lambert-rate equivalence workstream

Claim prepared on 2026-08-25 after reading the complete local coordination
policy and the live board from fetched `origin/main` `de3033392`.  The source
path is ordinary and unclaimed.  Every subagent remains read-only until this
claim is pushed and the required post-claim collision audit is complete.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: de303339202ef0b7fb99da83003d4b841eef9b80
HEAD and dirty paths: de303339202ef0b7fb99da83003d4b841eef9b80;
  only this new registry file is dirty for the exact-path claim
writing (exact paths): this registry initially; after this claim is pushed and
  the post-claim board/registry/tip audit remains green, only
  Lean/FabiusFunction/FabiusLambertRates.lean and this registry
expected declarations or document claims:
  eventually_le_dyadicLambertPhase, extracting the eventual effective
    inequality t <= dyadicLambertPhase t from the exact fixed-point equation;
  dyadicLambertPhase_isEquivalent_id, packaging the existing sharp ratio
    limit as asymptotic equivalence to the identity coordinate;
  dyadicLambertPhase_inv_isEquivalent_inv, transporting that equivalence to
    reciprocal scales;
  smallArgumentLog_inv_isTheta, recording on an arbitrary filter that the
    reciprocal base-two and natural-logarithmic coordinates differ only by
    the nonzero factor log 2;
  isBigO_lambertScale_iff_smallArgument_log and
    isLittleO_lambertScale_iff_smallArgument_log, upgrading the current
    one-way Lambert-to-endpoint transfer to exact equivalences for arbitrary
    normed codomains;
  preserve every existing declaration header, shorten only compatibility
    proofs through the stronger API, and expand the module guide/doc comments
    with human-readable mathematical statements; no canonical TeX/PDF or
    serialized documentation path is claimed
completed commits: none; this is the registry-first claim
validated (exact command, SHA/state, exit code): read-only source and Mathlib
  API preflight only; current main and every fetched Fabius remote tip have no
  exact proposed name, semantic-equivalent asymptotic-equivalence declaration,
  competing target-path delta, or registry claim; git status was clean before
  this file was created; this is not compiler evidence
not yet validated: all proposed Lean declarations and proof simplifications;
  no Lean, Lake, TeX, PDF, or other cache-mutating process has run because the
  codexbox Lean/Lake token remains coordinator-owned
requested integration or lease: advertise the one ordinary source path and
  six exact declarations above; after a reviewed source checkpoint, request
  one serialized LAKE_JOBS=1 build of +FabiusFunction.FabiusLambertRates and
  one focused downstream target selected by the coordinator; request no
  document or main-write lease
conflicts / dependencies: ProbabilityLaplaceMoments.lean,
  FabiusUniformSpline.lean, Paper06487Supplement.lean,
  FabiusQBinomialTaylor.lean, ThueMorseApproximation.lean, and every canonical
  document/control-plane path are explicitly excluded; only the coordinator
  may advance origin/main
next bounded step: commit and push this registry-only claim without force;
  fetch and reread the live board; inspect every advertised registry/tip again;
  only then edit the single claimed Lean module
```

## Source checkpoint: exact reciprocal-scale equivalences

Source commit `a8421fd7f16b71c7cbd867d0fc71c616c1b274aa` implements the
advertised one-file tranche.  The committed `FabiusLambertRates.lean` blob is
`1c5137f751bb6ac4fc79b8ab6d3af546d4290a6e`, with content SHA-256
`49C26F7C46F465B25513DEF0D4EF02B1B447B04C9348718EB8589C5D22A353BA`.

The six new public declarations are exactly:

- `eventually_le_dyadicLambertPhase`;
- `dyadicLambertPhase_isEquivalent_id`;
- `dyadicLambertPhase_inv_isEquivalent_inv`;
- `smallArgumentLog_inv_isTheta`;
- `isBigO_lambertScale_iff_smallArgument_log`; and
- `isLittleO_lambertScale_iff_smallArgument_log`.

The existing `dyadicLambertPhase_inv_isBigO_inv` and
`isBigO_smallArgument_log_of_lambertScale` headers are unchanged.  Their proofs
now factor through the stronger relation-level API.  The module overview and
each declaration comment state the mathematics in prose; the canonical
walkthrough and exposition remain frozen for their designated document owner,
which should later map the six exact names rather than paraphrasing a stronger
or weaker claim.

One independent hostile review found and resolved a focused-import blocker:
`AsymptoticEquivalent` imports the Theta API privately, so the source now
imports both modules explicitly.  Two independent reviews then accepted the fixed-point
orientation, reciprocal equivalence, arbitrary-filter Theta statement,
Big-O/little-o congruence directions, `[Norm E]` generality, zero-scale and
degenerate-filter cases, public compatibility, names, and documentation.  It
also corrected “effective” to “eventual order” because the public inequality
does not expose a numerical threshold.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: de303339202ef0b7fb99da83003d4b841eef9b80
HEAD and dirty paths: a8421fd7f16b71c7cbd867d0fc71c616c1b274aa;
  claimed Lean source is committed and clean; only this registry report is
  dirty
writing (exact paths): completed source checkpoint writes only
  Lean/FabiusFunction/FabiusLambertRates.lean; this report writes only this
  branch registry
expected declarations or document claims: all six advertised declarations
  are implemented; the two existing compatibility theorem headers remain
  unchanged; no canonical document edit is claimed
completed commits: bc14ab696 (pushed registry-first claim) and a8421fd7f
  (one-file source, proof, simplification, and module-documentation checkpoint)
validated (exact command, SHA/state, exit code): git diff --check exited 0;
  current-main/all-fetched-Fabius-tip path/name/semantic scan was green; an
  independent read-only theorem/API/import/edge-case/doc review found and
  resolved the explicit Theta import issue, and a second independent review
  passed the corrected tree; source contains no sorry, admit, axiom, or
  opaque; this is not compiler evidence
not yet validated: a8421fd7f has not been elaborated; no Lean, Lake, TeX, PDF,
  or other cache-mutating process ran because the codexbox Lean/Lake token is
  coordinator-owned
requested integration or lease: independent coordinator review, then one
  serialized LAKE_JOBS=1 build of +FabiusFunction.FabiusLambertRates and one
  focused downstream target selected from the actual import graph; no document
  or main-write lease
conflicts / dependencies: no target-path or declaration overlap exists on any
  fetched advertised tip; active probability, spline, Thue--Morse, periodic,
  frontier, primary, walkthrough, coverage, audit, root-aggregate, and control-
  plane paths remain excluded; only the coordinator may advance origin/main
next bounded step: commit and push this exact status with the source checkpoint;
  keep FabiusLambertRates.lean frozen for review/validation and advertise a
  separate cold-path effective-bound tranche before any further source edit
```

## Ordinary follow-on claim: expose the eighth-order reference tail

Claim prepared after the branch preserved its first tranche remotely, read the
new complete board at `origin/main` `39ad356c7`, and merged that checkpoint at
`8fad13626`.  The target source is unchanged from main at Git blob
`6d4c8f9a727dfc5616fe405b77453803f61846f6`.  The existing proof derives the
eighth inverse power explicitly and then discards seven powers when constructing
its public Big-O result.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: 39ad356c7a433c1b7dfdaec5bb3e3e4163c9fd35
HEAD and dirty paths: 8fad136269056382417777650976c4b0cad2f34a;
  branch is clean after the conflict-free origin/main merge, then only this
  registry is dirty for the follow-on claim
writing (exact paths): this registry initially; after this claim is pushed and
  the repeated board/registry/tip audit remains green, only
  Lean/FabiusFunction/FabiusSaddleReferenceTail.lean and this registry;
  FabiusLambertRates.lean is frozen at source commit a8421fd7f
expected declarations or document claims:
  exp_neg_sq_centralRadius_div_four, promoting the existing private exact
    identity exp (-(A(b)^2)/4) = b^(-8) at the standard radius;
  integral_norm_gaussian_add_oddCorrection_standardRadius_le_inv_pow_eight,
    exposing the pointwise bound
    tail <= (2 + 2*Clinear + 12*Ccubic) * b^(-8) when exp 1 <= b and the two
    standard coefficient-square hypotheses hold;
  integral_norm_gaussian_add_oddCorrection_standardRadius_isBigO_inv_pow_eight,
    packaging that effective inequality on an arbitrary filter;
  preserve the old integral_norm_gaussian_add_oddCorrection_standardRadius_isBigO
    header as an O(b^(-1)) compatibility wrapper derived from the stronger
    eighth-order theorem;
  revise the module overview and declaration comments so the exact identity,
    effective constant, sharp exported rate, and deliberately weaker wrapper
    are stated in human-readable form; no canonical TeX/PDF, facade, or root
    path is claimed
completed commits: bc14ab696 (first claim), a8421fd7f (first source),
  5473f530d (first report), and 8fad13626 (merge of current main); no follow-on
  source commit exists yet
validated (exact command, SHA/state, exit code): read-only proof audit located
  the complete b^(-8) calculation already inside the old Big-O proof; exact-
  name/semantic/path scans of current main, every fetched Fabius tip, and every
  registry found no public duplicate or competing target edit; the only same-
  name declaration is the private helper being promoted; this is not compiler
  evidence
not yet validated: all three public declarations, the compatibility refactor,
  and documentation changes; no Lean, Lake, TeX, PDF, or cache-mutating process
  ran because neither idle host token is assigned to this branch
requested integration or lease: advertise this one ordinary source path and
  three exact public names; after an immutable reviewed source checkpoint,
  request separate serialized builds of +FabiusFunction.FabiusSaddleReferenceTail
  and its narrow direct consumer +FabiusFunction.GaussianPolynomialTail; no
  document or main-write lease
conflicts / dependencies: the active Differential/Existence claim and all
  released or frozen probability, spline, Thue--Morse, Lambert-rate, canonical-
  document, campaign-wide, and root paths are disjoint and excluded; only the
  coordinator may advance origin/main
next bounded step: commit and push this registry-only follow-on claim; fetch
  and reread the live board; repeat the all-tip collision scan; only then edit
  FabiusSaddleReferenceTail.lean
```

## Source checkpoint: expose the coarse eighth-order reference tail

Source commit `933121538cd4e3294b487edcfdabc6b128a425ef` implements the
approved follow-on in exactly one Lean module.  Its committed
`FabiusSaddleReferenceTail.lean` blob is
`7dc2cd616a259c16eb69fdb412d45e7e9bba75e2`, with content SHA-256
`5000DA5029799F697AC7FC816564349D937F9EF07D59085F4F84996BEA187F86`.

The source promotes the unchanged exact standard-radius identity
`exp_neg_sq_centralRadius_div_four`, adds the effective pointwise bound
`integral_norm_gaussian_add_oddCorrection_standardRadius_le_inv_pow_eight`,
and packages it as the arbitrary-filter result
`integral_norm_gaussian_add_oddCorrection_standardRadius_isBigO_inv_pow_eight`.
The existing
`integral_norm_gaussian_add_oddCorrection_standardRadius_isBigO` declaration
header is unchanged and its proof now factors through the stronger rate by
transitivity.

Following the coordinator correction at `origin/main` `34ca81c94`, the module
consistently calls `b⁻⁸` a **coarse eighth-order algebraic rate**, not a sharp
rate.  Its overview and declaration comments state the exact identity,
threshold, explicit constant `2 + 2 * Clinear + 12 * Ccubic`, arbitrary-filter
transport, discarded `1 / fabiusSaddleCentralRadius b` factor, and compatibility
wrapper in human-readable form.  They also qualify the exact identity by
`1 ≤ b`, which matters because the real square root truncates a negative
radicand.  The canonical TeX/PDF paths remain frozen; their future owner can
map these exact declaration names without guessing at the formal strength.

The private downstream
`Fabius.SaddleExpansion.exp_neg_sq_orderRadius_div_four` in
`GaussianPolynomialTailAllOrders.lean` is a known, nonblocking semantic
overlap: it evaluates the order-dependent radius for arbitrary `N`, while the
new public lemma records the standard-radius identity in the lower-dependency
namespace used here.  No competing public declaration or active edit of the
claimed source path was found on any fetched advertised tip.

Two independent read-only reviews accepted the exact constant arithmetic,
coefficient bounds, denominator signs, `IsBigO.of_bound` packaging, arbitrary
and degenerate filter behavior, rate-comparison orientation, public API,
documentation, and collision status.  The second review identified the
missing `1 ≤ b` prose qualification; it is fixed in the committed source.  The
legacy declaration header was also compared directly with its parent and is
identical.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: 34ca81c9427110e608f7be92c591201739d30fd6
HEAD and dirty paths: 933121538cd4e3294b487edcfdabc6b128a425ef;
  the one-file Lean source checkpoint is committed, clean, and pushed; only
  this registry report is dirty
writing (exact paths): completed source write only
  Lean/FabiusFunction/FabiusSaddleReferenceTail.lean; this report writes only
  this branch registry; FabiusLambertRates.lean remains frozen
expected declarations or document claims: all three advertised public names
  are implemented; the old O(b^(-1)) theorem header remains unchanged; module
  and declaration documentation give human-readable counterparts; no
  canonical document claim
completed commits: f3f9785fe (pushed registry-first follow-on claim) and
  933121538 (pushed one-file coarse eighth-order source checkpoint)
validated (exact command, SHA/state, exit code): git diff --check exited 0;
  exact old-header comparison exited 0; forbidden-placeholder scan was clean;
  current-main/all-fetched-Fabius-tip public-name/path scan found no collision;
  two independent static theorem/API/edge-case/doc reviews passed after the
  prose qualification was fixed; this is not compiler evidence
not yet validated: commit 933121538 has not been elaborated; no Lean, Lake,
  TeX, PDF, or other cache-mutating process ran because neither idle host token
  is assigned to this branch
requested integration or lease: preserve and review exact source commit
  933121538, then assign separate serialized builds of
  +FabiusFunction.FabiusSaddleReferenceTail and its smallest direct importer
  +FabiusFunction.GaussianPolynomialTail; no document or main-write lease
conflicts / dependencies: the private all-orders radius identity above is
  recorded semantic context, not a public duplicate; all active/frozen
  Differential, Lambert, polynomial, canonical-document, facade, root, and
  control-plane paths remain excluded; only the coordinator may advance main
next bounded step: commit and push this exact registry report, merge current
  origin/main into the clean preserved feature branch, resolve only any
  same-branch registry or already-integrated Lambert repair, push the merge,
  and freeze both completed source tranches pending serialized validation
```

## Coordinator integration and validation result

The coordinator integrated exact source commit `933121538` as `f85409a18`.
At that immutable mainline tree, separate serialized builds of
`+FabiusFunction.FabiusSaddleReferenceTail` (3432 jobs) and its smallest direct
importer `+FabiusFunction.GaussianPolynomialTail` (3436 jobs) both exited zero
without warnings.  The old order-one theorem header and both direct consumer
interfaces remained byte-identical.  The earlier Lambert-rate source is also
integrated, repaired only for definitional function shape, and green in its
focused and direct-consumer builds.  Both source leases are released.

This branch merged the validating coordinator checkpoint `b97b7f108` at
`6cf7d1e7b`; the committed `FabiusSaddleReferenceTail.lean` blob is identical
to current main.  No local Lean/Lake process was needed or launched.

## Ordinary follow-on claim: exact normalized `L¹` transfer

Claim prepared on the validated mainline base after three independent
cold-path audits compared disjoint opportunities in Lambert all-order algebra,
unit-interval Laplace moments, and quantitative saddle integration.  This
bounded one-file tranche exposes the exact pointwise inequality already
embedded in the generic Big-O transfer, with the smallest elaboration surface
and immediate simplification payoff.

For `M = sqrt (2 * pi)`, the intended human-readable statement is

```text
‖M⁻¹ ∫ K - M⁻¹ ∫ R‖ ≤ M⁻¹ ∫ ‖K - R‖.
```

When `∫ R = M`, this becomes the corresponding bound on
`‖M⁻¹ ∫ K - 1‖`.  Both statements require only integrability of the two
kernels, plus the displayed mass identity for the second.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: b97b7f108ca3c3c0a20e9958ddf672385c7647ab
HEAD and dirty paths: 6cf7d1e7bf1a8d404faf16684d8bbc57f5ef2538;
  branch is clean and contains current main; only this registry is dirty for
  the registry-first claim
writing (exact paths): this registry initially; after this claim is pushed and
  the repeated board/registry/tip scan remains green, only
  Lean/FabiusFunction/QuantitativeSaddle.lean and this registry
expected declarations or document claims:
  norm_normalized_integral_sub_reference_le_of_L1, exposing the pointwise
    Gaussian-normalized L1 Lipschitz inequality with factor
    (sqrt (2*pi))^(-1);
  norm_normalized_integral_sub_one_le_of_L1, specializing the same inequality
    to an integrable reference whose integral is the Gaussian mass;
  preserve the exact normalized_integral_sub_reference_isBigO_of_L1 header and
    shorten its proof through the new pointwise API; preserve every other
    public header;
  expand the module overview and both declaration comments with the displayed
    mathematics, hypotheses, and relation to the filter-level wrappers; no
    canonical TeX/PDF, walkthrough, facade, root, or campaign-wide document
    path is claimed
completed commits: 933121538 was integrated as f85409a18 and validated as
  recorded above; this is the registry-first claim for the third source tranche
validated (exact command, SHA/state, exit code): current HEAD and origin/main
  share QuantitativeSaddle.lean blob 0fef8b8a0efd3a05ac0728def6e0ef6145cb319c;
  exact-name/semantic/path scans of current main, every fetched Fabius tip, and
  every registry found no public pointwise duplicate or active path claim;
  an independent read-only proof/API/dependency/doc audit derived the exact
  signatures and proof route; this is not compiler evidence for the proposal
not yet validated: the two pointwise declarations and Big-O refactor do not
  exist yet; no Lean, Lake, TeX, PDF, or cache-mutating process is authorized
  or running for this branch
requested integration or lease: advertise the one ordinary source path and
  two exact names above; after an immutable reviewed source checkpoint, request
  separate serialized builds of +FabiusFunction.QuantitativeSaddle and its
  direct API consumer +FabiusFunction.SaddleAllOrders; no document or main-write
  lease
conflicts / dependencies: the inactive AUDIT_FINDINGS proposal to relocate
  norm_standardGaussian into this module is explicitly excluded; no such
  declaration, import change, downstream edit, Lambert algebra, Laplace-moment,
  canonical-document, facade, root, or control-plane path belongs to this claim;
  only the coordinator may advance main
next bounded step: commit and push this registry-only claim without force;
  fetch and reread the board, repeat the all-tip collision scan, then lease the
  single source file to one author while two agents independently audit the
  final proof and documentation; run no build without an explicit host token
```

## Source checkpoint: pointwise normalized `L¹` inequalities

Source commit `24f1eee302bd94a5cc15543cb4b1b6d096baf905` implements the
advertised one-file tranche.  The committed `QuantitativeSaddle.lean` blob is
`378617cc9a68c555442cb8a48c088c17c2af35ec`, with content SHA-256
`E91A83AEE58545499F5CC8C319679959E8CDD857510BBF64EF5A65C2CC172D6B`.

The two new public declarations are exactly:

- `norm_normalized_integral_sub_reference_le_of_L1`; and
- `norm_normalized_integral_sub_one_le_of_L1`.

The first exposes the explicit pointwise inequality with Gaussian-normalizing
factor `(sqrt (2 * pi))⁻¹`; the second rewrites the reference term to `1` under
the standard-mass identity.  Both retain the natural integrability hypotheses,
which cannot simply be dropped because Lean totalizes nonintegrable Bochner
integrals to zero.  The existing
`normalized_integral_sub_reference_isBigO_of_L1` header is byte-identical to
its parent; its proof is now the arbitrary-filter wrapper around the first
pointwise result.  No import, downstream file, `norm_standardGaussian`
declaration, or unrelated API changed.

The module overview and both declaration comments display the whole-line
integral inequalities, distinguish the arbitrary-reference and standard-mass
forms, state their hypotheses, and explain their relationship to the existing
Big-O layer.  They deliberately describe `1 / sqrt (2 * pi)` as the explicit
normalization factor, not as an independently proved optimal constant.

Two independent read-only reviews accept the norm rewrite chain, complex
coercions, positive Gaussian mass, `inv_mul_cancel₀` orientation, arbitrary and
bottom filters, zero rates, Big-O witness multiplication, dependency placement,
consumer choice, exact old header, names, and human-readable documentation.
The focused static checks and all-tip scans are green; no build process was
authorized or launched.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: 2f306d00b477f24457e3fbc1d1de411e8382e51a
HEAD and dirty paths: 24f1eee302bd94a5cc15543cb4b1b6d096baf905;
  the one-file Lean source checkpoint is committed, clean, and pushed; only
  this registry report is dirty
writing (exact paths): completed source checkpoint writes only
  Lean/FabiusFunction/QuantitativeSaddle.lean; this report writes only this
  branch registry
expected declarations or document claims: both advertised pointwise names are
  implemented; normalized_integral_sub_reference_isBigO_of_L1 keeps its exact
  header as a wrapper; module and declaration docs supply human-readable
  counterparts; no canonical document claim
completed commits: 0cf2a0df0 (pushed registry-first claim) and 24f1eee30
  (pushed one-file source/proof/refactor/documentation checkpoint)
validated (exact command, SHA/state, exit code): git diff --check exited 0;
  exact old-header comparison exited 0; forbidden-placeholder scan was clean;
  current-main/all-fetched-Fabius-tip public-name/path scan found no collision;
  two independent static theorem/API/filter/dependency/doc reviews passed;
  this is not compiler evidence
not yet validated: commit 24f1eee30 has not been elaborated; no Lean, Lake,
  TeX, PDF, or other cache-mutating process ran because neither host token is
  assigned to this branch
requested integration or lease: preserve and review exact source commit
  24f1eee30, then assign separate serialized builds of
  +FabiusFunction.QuantitativeSaddle and its direct API consumer
  +FabiusFunction.SaddleAllOrders; no document or main-write lease
conflicts / dependencies: QuantitativeSaddle.lean had the exact current-main
  preimage at claim time; newer normalized-reflection, product-positivity, and
  signed dyadic-reflection paths are disjoint; the inactive
  norm_standardGaussian relocation and all canonical-document/facade/root/
  control-plane paths remain excluded; only the coordinator may advance main
next bounded step: commit and push this exact registry report, merge current
  origin/main into the clean preserved feature branch, verify the source blob
  is unchanged, and freeze the tranche pending serialized validation
```

## Ordinary follow-on claim: quantitative comparison across every tilt

For a measure on `[0,1]`, changing the Laplace tilt from `t` to `s` multiplies
the integrand by `exp ((t - s) * x)`.  Since `0 <= x <= 1`, its endpoint
values give the natural two-sided comparison

```text
exp (min (t - s) 0) * M_k(t) <= M_k(s)
M_k(s) <= exp (max (t - s) 0) * M_k(t).
```

This comparison is valid for every degree and every pair of real tilts.  In
particular, strict positivity at one tilt is equivalent to strict positivity
at every tilt.  Transport through the weighted-sum probability law and the
identity `M_k(0) = halfMoment k > 0` then shows that every Fabius Laplace
moment is strictly positive, with no restriction on its degree or real tilt.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: df3e05c48bd7a4678c6118ba2e26b7d1ec2a6bf2
HEAD and dirty paths: 0463cde5c1911e01966db1e50b92c0860d18be84;
  branch is clean, pushed, and contains current main; only this registry is
  dirty for the registry-first claim
writing (exact paths): this registry initially; after this claim is pushed and
  a repeated board/registry/tip scan remains green, only
  Lean/FabiusFunction/UnitLaplaceMomentBounds.lean and this registry
expected declarations or document claims:
  unitLaplaceMoment_tilt_bounds, giving the displayed min/max exponential
    comparison for any compactly finite measure, natural degree, and real
    tilts;
  unitLaplaceMoment_pos_iff, making strict positivity invariant under a change
    of real tilt;
  fabiusLaplaceMoment_tilt_bounds, transporting the same two-sided estimate to
    every bounded Fabius candidate;
  fabiusLaplaceMoment_pos_all, proving strict positivity for every natural
    degree and every real tilt from the positive zero-tilt half moment;
  expand the module overview and declaration comments with the displayed
    inequalities, hypotheses, and probability-law specialization; preserve
    every existing public header and import; no canonical document, facade,
    root, or campaign-wide path is claimed
completed commits: 24f1eee30 is the frozen normalized-L1 source checkpoint;
  0463cde5c is the pushed merge through current main; this is the registry-first
  claim for a disjoint fourth source tranche
validated (exact command, SHA/state, exit code): current HEAD and origin/main
  share UnitLaplaceMomentBounds.lean blob
  d3d5df6ed130f8d509bb38eec183c6dffdd9a3b2, content SHA-256
  39D1A4E740E22C6F6D29C9ABF6863867160775830F9A4406F97A13AE4969C0C9;
  exact-name, plausible-semantic-name, path, all-fetched-Fabius-tip, and every
  registry scan found no implementation or active claim; two independent
  read-only audits compared this opportunity with the correct but higher-risk
  all-order Lambert degree/leading-coefficient formulas and recommend this
  bounded pointwise-integral route; this is not compiler evidence
not yet validated: none of the four proposed declarations exists yet; no Lean,
  Lake, TeX, PDF, or cache-mutating process is authorized or running here
requested integration or lease: advertise the one ordinary source path and
  four exact names above; after an immutable reviewed source checkpoint,
  request separate serialized builds of
  +FabiusFunction.UnitLaplaceMomentBounds and its smallest direct consumer
  +FabiusFunction.LaplaceMomentBounds; no document or main-write lease
conflicts / dependencies: the frozen QuantitativeSaddle checkpoint is
  disjoint and still awaits coordinator integration; current binary-reduction,
  signed dyadic-reflection, canonical-document, facade, root, and control-plane
  paths remain excluded; the already proved zeroth-degree theorem
  fabiusLaplaceMoment_zero_pos_all is a strict special case, not a duplicate;
  only the coordinator may advance main
next bounded step: commit and push this registry-only claim without force;
  fetch and reread any changed board, repeat the all-tip collision scan, then
  lease the single source file to one author while two agents independently
  audit proof robustness and human-readable parity; run no build without an
  explicit host token
```

## Source checkpoint: all-degree comparison and positivity across tilts

Source commit `d9598f3b6` implements the advertised one-file tranche.  The
committed `UnitLaplaceMomentBounds.lean` blob is
`ac0349d2c96460ddc758a6069fca79fe2359b5c2`, with content SHA-256
`3F609EA6B099602C3503831919F21A0357746618FDE14887C2B9564A36F22ED9`.

The four new public declarations are exactly:

- `unitLaplaceMoment_tilt_bounds`;
- `unitLaplaceMoment_pos_iff`;
- `fabiusLaplaceMoment_tilt_bounds`; and
- `fabiusLaplaceMoment_pos_all`.

Writing `M_k(u) = unitLaplaceMoment μ u k`, the first theorem proves for
arbitrary real `s,t`

```text
exp (min (t - s) 0) * M_k(t) <= M_k(s)
M_k(s) <= exp (max (t - s) 0) * M_k(t).
```

Its proof exposes the pointwise identity
`exp (-s*x) = exp ((t-s)*x) * exp (-t*x)` and integrates the endpoint bounds
for `(t-s)*x` on `[0,1]`.  The second theorem swaps the lower estimate to show
that strict positivity is tilt-independent.  The final two declarations
transport both facts through the weighted-sum probability representation and
use `fabiusLaplaceMoment F k 0 = halfMoment k > 0` to cover every degree and
every real Fabius tilt.

The module overview and all four declaration comments display the formulas,
scope, and hypotheses.  The prose includes the zero/degenerate-measure case
for the generic positivity equivalence and makes no optimality claim.  Existing
imports and every prior declaration header are byte-preserved; no wrapper,
facade, root, or downstream file changed.

Two independent adversarial read-only reviews accept the exponent algebra,
min/max orientations, `IntegrableOn` witnesses, both `integral_mono_ae`
directions, positivity swap, probability-law transport, cast of
`halfMoment_pos`, zero and Dirac measures, every degree, equal and negative
tilts, names, placement, direct consumer, and human-readable parity.  Static
checks are green; no compiler process was authorized or launched.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: 03540bab399836bb87e338ce970b21b4c46f5eaa
HEAD and dirty paths: ebc8b12a8270f8825a3dfab661fcd301a34625df;
  branch is clean, pushed, and contains current main; only this registry report
  is dirty
writing (exact paths): completed source checkpoint writes only
  Lean/FabiusFunction/UnitLaplaceMomentBounds.lean; this report writes only
  this branch registry
expected declarations or document claims: all four advertised declarations
  are implemented with exact formula-bearing module/declaration docs; every
  existing header/import remains unchanged; no canonical document claim
completed commits: 90432f3c6 (registry-first claim), d9598f3b6 (pushed
  one-file source/proof/documentation checkpoint), and ebc8b12a8 (pushed merge
  through current main)
validated (exact command, SHA/state, exit code): git diff --check exited 0;
  added-public-declaration scan found exactly the four claimed names; forbidden
  placeholder scan was clean; exact path/header/import comparison was clean;
  current-main/all-fetched-Fabius-tip public-name/path scan found no collision;
  two independent static theorem/API/measure/edge-case/doc reviews passed;
  this is not compiler evidence
not yet validated: commit d9598f3b6 has not been elaborated; no Lean, Lake,
  TeX, PDF, or other cache-mutating process ran because neither Lean host token
  is assigned to this branch
requested integration or lease: preserve and review exact source commit
  d9598f3b6, then assign separate serialized builds of
  +FabiusFunction.UnitLaplaceMomentBounds and its sole direct source importer
  +FabiusFunction.LaplaceMomentBounds; no document or main-write lease
conflicts / dependencies: the earlier QuantitativeSaddle source checkpoint
  24f1eee30 is disjoint and remains frozen pending its own integration/build;
  the shifted-prefix branch exclusively owns the newly granted canonical
  documentation paths; all document/facade/root/control-plane paths remain
  excluded here; only the coordinator may advance main
next bounded step: commit and push this exact registry report, merge any newer
  origin/main into the clean preserved feature branch after a full board read,
  verify both source blobs remain exact, and freeze both unvalidated source
  checkpoints pending serialized coordinator validation
```

## Coordinator result: normalized `L¹` transfer accepted

The coordinator integrated exact source commit `24f1eee30` as `caed8800e`.
Separate serialized builds of `+FabiusFunction.QuantitativeSaddle` (2782 jobs)
and its direct API consumer `+FabiusFunction.SaddleAllOrders` (2783 jobs) both
exited zero without warnings.  The existing Big-O theorem header and every
other public interface remained unchanged.

Feature merge `3ede563b6` incorporates accepting main checkpoint `0bc0bf551`.
The merged `QuantitativeSaddle.lean` remains byte-identical to the compiled
source: Git blob `378617cc9a68c555442cb8a48c088c17c2af35ec`, content SHA-256
`E91A83AEE58545499F5CC8C319679959E8CDD857510BBF64EF5A65C2CC172D6B`.
That source lease and the coordinator build token are released.  Only the
disjoint Unit-Laplace tilt checkpoint `d9598f3b6` remains unelaborated.

## Coordinator result: all-tilt moment comparison accepted

The coordinator integrated exact source commit `d9598f3b6` as `7b892b41c`.
Separate serialized builds of `+FabiusFunction.UnitLaplaceMomentBounds` (3189
jobs) and its sole direct importer `+FabiusFunction.LaplaceMomentBounds` (3417
jobs) both exited zero.  They reported only the inherited, previously recorded
nonblocking `unnecessarySimpa` linter in `ProbabilityLaplaceMoments.lean`; the
new module emitted no distinct warning.

Feature merge `9507c0ac9` incorporates accepting main checkpoint `4b3ddc7db`.
The merged `UnitLaplaceMomentBounds.lean` is byte-identical to the compiled
source: Git blob `ac0349d2c96460ddc758a6069fca79fe2359b5c2`, content SHA-256
`3F609EA6B099602C3503831919F21A0357746618FDE14887C2B9564A36F22ED9`.
Every source and build lease held by this branch is now released.  No local
Lean/Lake invocation was launched during any tranche.

## Ordinary follow-on claim: exact degree and leading term at every order

The recursive lower-Lambert displacement polynomials currently have explicit
closed forms only through order two.  Their recurrence nevertheless determines
the degree and highest coefficient uniformly: the natural degrees are
`1, 1, 2, 3, ...`, and for every `n : ℕ` the leading coefficient of
`a_(n+1)` is

```text
(-1)^n * (n + 1)^(-1) * (log 2)^(-(n + 2)).
```

Only the `j = 0` convolution summand can reach the new highest degree.  Every
positive-index summand has degree at most the preceding order, so the top
coefficient obeys, for `n >= 1`, the scalar recurrence
`L_(n+1) = -(n / (n + 1)) * (log 2)^(-1) * L_n`.  This gives a short
structural proof rather than expanding individual polynomials.  The exceptional
base step has empty convolution and gives `L_1 = (log 2)^(-2)` directly.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: c5ee98fc72489312e042eb0a4f2280827ee96457
HEAD and dirty paths: b44ddee7c294e579c63ca7cf71db10ffef8c56f7;
  branch is clean, pushed, and contains current main; only this registry is
  dirty for the registry-first claim
writing (exact paths): this registry initially; after this claim is pushed and
  a repeated board/registry/all-tip scan remains green, only
  Lean/FabiusFunction/FabiusLambertAllOrderAlgebra.lean and this registry
expected declarations or document claims:
  dyadicLambertDisplacementPolynomial_natDegree, proving
    (dyadicLambertDisplacementPolynomial n).natDegree = max n 1 for every n;
  dyadicLambertDisplacementPolynomial_leadingCoeff_succ, proving the displayed
    all-order leading-coefficient formula for a_(n+1);
  use documented private degree-bound and top-coefficient helpers to expose
    the unique-highest-summand argument without adding redundant public API;
  expand the module overview and declaration comments with both formulas, the
    degree sequence, and the recurrence insight, and add the missing prose
    comments for the four existing public zero/one/two simp evaluations;
    preserve every old public declaration header; no canonical TeX/PDF,
    walkthrough, facade, root, or campaign-wide document path is claimed
completed commits: d9598f3b6 is accepted on main as 7b892b41c; merge
  b44ddee7c incorporates current main c5ee98fc7 and its accepted shifted-
  Fourier tranche; this is the registry-first claim for a fifth source unit
validated (exact command, SHA/state, exit code): current HEAD and origin/main
  share target blob 5ac6f66612b415ee3524f694e07571e5e887f76f,
  content SHA-256
  244265A906963BAE781FD752792D3AF303506AF87FD44C2C7E75104FEA92FA3B;
  exact-name, plausible-semantic-name, exact-path, every-registry, and all-
  fetched-Fabius-tip scans found no implementation or competing lease; the
  conditional theorem-polish primary reservation concerns a different future
  two-source asymptotic-formula checkpoint and grants no overlapping source;
  read-only Mathlib API inspection confirms the required degree, coefficient,
  finite-sum, and polynomial-product lemmas; this is not compiler evidence
not yet validated: neither proposed public declaration nor its private proof
  helpers exists yet; no Lean, Lake, TeX, PDF, or cache-mutating process is
  authorized or running for this branch
requested integration or lease: advertise this ordinary one-source/two-name
  claim; after an immutable independently reviewed checkpoint, request
  separate serialized builds of
  +FabiusFunction.FabiusLambertAllOrderAlgebra and its sole direct importer
  +FabiusFunction.FabiusLambertFormalLog; request no document or main-write
  lease
conflicts / dependencies: the newly accepted PoissonSummation source and the
  frontier draft additions are disjoint; every canonical document remains
  frozen; the explicit Polynomial.BigOperators import may be added in the
  claimed source for stable API provenance; only the coordinator may advance
  main
next bounded step: commit and push this registry-only claim without force;
  fetch and reread any changed board, repeat all-tip collision checks, then
  edit only the claimed Lean source while three agents independently audit
  proof robustness, alternative cold paths, and human-readable parity
```

## Source checkpoint: all-order degree and leading coefficient

Exact source commit `8f47687e5` implements the complete two-name claim in the
sole leased module.  After merge `14ad82304` incorporated the coordinator's
claim acknowledgment and the disjoint accepted saddle-polynomial
deduplication, the committed `FabiusLambertAllOrderAlgebra.lean` remains Git
blob `08e5a2d9475746a517d8d835b699c00d8c00c0a9`, with content SHA-256
`A0FDC9D0947438D011FD4BE27E25D22F70E3D254881EBCBDF577FFC7A3C52984`.

The two new public declarations are exactly:

- `dyadicLambertDisplacementPolynomial_natDegree`;
- `dyadicLambertDisplacementPolynomial_leadingCoeff_succ`.

The first proves the total formula `natDegree a_n = max n 1`, including the
exceptional degree-one polynomial `a_0`.  The second proves

```text
leadingCoeff a_(n+1) =
  (-1)^n * (n+1)^(-1) * (log 2)^(-(n+2)).
```

A documented private strong-induction helper bounds the degree of every
recursive summand.  A second documented helper proves the top coefficient by
ordinary induction: it handles the empty `n = 0` convolution directly, then
uses `Fin.sum_univ_succ` to split off `j = 0`; the positive-index tail has
degree one below the new coefficient and therefore vanishes there.  The
explicit nonzero closed coefficient upgrades the degree bound to equality,
and `coeff_natDegree` gives the public leading-coefficient corollary.

The module overview now states both formulas and the base exception.  The two
new public theorems and both proof helpers have formula-bearing comments, and
the four formerly undocumented public simp evaluations at indices zero, one,
and two now have human-readable counterparts.  Every old public declaration
header and body remains byte-preserved.  The only import addition is the
explicit `Mathlib.Algebra.Polynomial.BigOperators`, which is the stable source
of the finite-sum degree API.

Three independent read-only reviews audited the live source.  They caught and
resolved the unqualified `n = 0` recurrence prose, polynomial association in
the head coefficient, first-occurrence coefficient rewriting, negation
grouping at the scalar recurrence, the sign-specific `pow_succ` rewrite, and
an unnecessary implicit `gcongr` dependency.  The corrected tree passes all
three static reviews for mathematics, indices, pinned APIs, documentation,
names, imports, simp termination, and compatibility.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: d33c4f44b3d08f14b15c1514d687a32898569475
HEAD and dirty paths: 14ad82304645021f82d63b62d873dd99a24373ea;
  clean after the conflict-free main merge; only this registry is dirty for
  the immutable source handoff
writing (exact paths): completed source checkpoint writes only
  Lean/FabiusFunction/FabiusLambertAllOrderAlgebra.lean; this report writes
  only this branch registry; the Lean source is now frozen
expected declarations or document claims: both advertised public declarations
  are implemented; documented private helpers establish the degree bound and
  exact top coefficient; four missing existing theorem comments are supplied;
  no canonical document, facade, root, or other source claim
completed commits: 96e05f698 (registry-first claim), ca227c69e (base-case
  recurrence correction), 8f47687e5 (one-file source/proof/documentation
  checkpoint), and 14ad82304 (merge through current main d33c4f44b)
validated (exact command, SHA/state, exit code): git diff --check exited 0;
  forbidden-placeholder scan is clean; added-public-declaration scan finds
  exactly the two advertised names; old public headers/bodies are preserved;
  repeat all-registry/all-fetched-tip scans find no competing implementation;
  three independent exact static theorem/API/index/simp/documentation reviews
  pass after all reported hazards were fixed; this is not compiler evidence
not yet validated: source commit 8f47687e5 has not been elaborated; no Lean,
  Lake, TeX, PDF, or cache-mutating process ran because codexbox belongs to the
  coordinator and EVO is assigned to theorem-polish
requested integration or lease: independently review and preserve exact source
  commit 8f47687e5 / blob 08e5a2d94757, then assign separate serialized
  LAKE_JOBS=1 builds of +FabiusFunction.FabiusLambertAllOrderAlgebra and its
  sole direct importer +FabiusFunction.FabiusLambertFormalLog; request no
  document or main-write lease
conflicts / dependencies: the compact Lambert-W obstruction, saddle
  continuous-polynomial deduplication, shifted-prefix, frontier drafts, and
  every canonical document are disjoint; only the coordinator may advance
  main
next bounded step: commit and push this exact immutable report and merge;
  keep the claimed source frozen for coordinator review/validation, and audit
  the already identified disjoint LaplaceMomentBounds strict-monotonicity
  follow-on without editing or claiming it until this handoff is preserved
```

## Ordinary follow-on claim: strict Laplace-moment order structure

The newly integrated all-degree/all-tilt positivity theorem turns the exact
derivative identity

```text
M_k'(s) = -M_(k+1)(s)
```

into a global strict order theorem: every raw Fabius Laplace moment is
strictly decreasing on the whole real line.  The same positivity also shows
that every normalized moment `R_k(s) = M_k(s) / M_0(s)` is strictly positive,
strengthening the existing nonnegativity interfaces without narrowing their
domains.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: 5b053a32b10e758e39f1be23cb2e8d821fba8de6
HEAD and dirty paths: e25f61fda87b529faca9c326ba389316f6d8fa8d;
  clean and pushed after merging current main; only this registry is dirty
  for the registry-first claim
writing (exact paths): this registry initially; after this claim is pushed and
  a repeated board/registry/all-tip scan remains green, only
  Lean/FabiusFunction/LaplaceMomentBounds.lean and this registry
expected declarations or document claims:
  fabiusLaplaceMoment_strictAnti, proving
    StrictAnti (fabiusLaplaceMoment F k) for every natural degree;
  normalizedLaplaceMoment_pos_all, proving
    0 < normalizedLaplaceMoment F k s for every natural degree and real tilt;
  shorten the bodies of normalizedLaplaceMoment_nonneg_all and
    normalizedLaplaceMoment_nonneg through the strict theorem while preserving
    both exact public headers;
  expand the module overview and declaration comments with the derivative,
    strict-order, and strict-positivity formulas; no canonical document,
    facade, root, import, or other source path is claimed
completed commits: the preceding all-order Lambert source is frozen at
  8f47687e5 / blob 08e5a2d94757 and requested for coordinator validation;
  merge e25f61fda incorporates current main 5b053a32b while preserving that
  blob exactly; this is the registry-first claim for a disjoint sixth source
  unit
validated (exact command, SHA/state, exit code): current HEAD and origin/main
  share LaplaceMomentBounds.lean blob
  9b6398320300ff28e21f5deaf59f4b5d6354d468, content SHA-256
  04CB8BCA5E9169A2798A68E19B8D2E548244C71C2539DC3EE30CDEC8693D0F89;
  exact-name, plausible-semantic-name, exact-path, every-registry, and all-
  fetched-Fabius-tip scans found no implementation or competing lease;
  read-only inspection confirms that the existing ExponentialBounds import
  publicly exposes strictAnti_of_hasDerivAt_neg through Log.Deriv/MeanValue;
  three independent mathematical/API/documentation audits recommend the
  bounded two-name tranche; this is not compiler evidence
not yet validated: neither proposed declaration exists yet; no Lean, Lake,
  TeX, PDF, or cache-mutating process is authorized or running for this branch
requested integration or lease: advertise this ordinary one-source/two-name
  claim; after an immutable independently reviewed checkpoint, request a
  serialized build of +FabiusFunction.LaplaceMomentBounds and then its direct
  importer +FabiusFunction.NegativeLaplaceDerivativeBounds; request no
  document or main-write lease
conflicts / dependencies: the previous theorem-polish lease on this file is
  explicitly released; current theorem-polish ownership is only the primary
  TeX/PDF pair; the moving shifted-prefix tip, compact Lambert correction,
  central valuation source, pending all-order Lambert source, and all active
  document paths are disjoint; only the coordinator may advance main
next bounded step: commit and push this registry-only claim without force;
  fetch and reread any changed board, repeat all-tip collision checks, then
  edit only the claimed Lean source while subagents independently inspect the
  live proof, documentation parity, and possible regressions
```

## Source checkpoint: strict raw order and normalized positivity

Exact source commit `caf654097` implements the complete two-name claim in the
sole leased module.  The committed `LaplaceMomentBounds.lean` is Git blob
`007c2ed04697ab56d3fd0654da477d32d360a61b`, with content SHA-256
`66686398FB67A05B4D60ADF737DF5FA99A8FA6773F2EB24AAE9C88D13D7A6084`.

The new theorem `fabiusLaplaceMoment_strictAnti` applies Mathlib's direct
`HasDerivAt` strict-antitonicity principle to the already exact identity

```text
M_k'(s) = -M_(k+1)(s).
```

The imported all-degree/all-tilt positivity theorem makes this derivative
strictly negative for every `s`, so the result covers `k = 0` and every real
tilt without an endpoint or sign exception.  The second theorem,
`normalizedLaplaceMoment_pos_all`, divides the positive `k`th raw moment by
the positive zeroth raw moment and therefore proves `0 < R_k(s)` on the same
full domain.

Both existing nonnegativity declarations retain their exact public kinds,
binders, hypotheses, conclusions, and imports.  Their bodies are now one-line
compatibility consequences of strict positivity.  The deliberately retained
positive-scale hypothesis is documented and enclosed in the same local
unused-variable-linter pattern already used by this module.  The module
overview and all four declaration comments state the strict results and the
compatibility roles in human-readable form.

Three independent read-only reviews accept the live result's mathematics,
strict-order orientation, derivative sign, `k = 0` and negative-tilt cases,
Mathlib API shape, transitive import, exact old headers, declaration kinds,
names, linter scope, direct-import topology, and documentation.  No review
found a source-level blocker after the local linter scope was added.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: 5b053a32b10e758e39f1be23cb2e8d821fba8de6
HEAD and dirty paths: caf65409703d4fa7f5350c2fcfad22e20d2e0059;
  source checkpoint is clean and pushed; only this registry is dirty for the
  immutable handoff
writing (exact paths): completed source checkpoint writes only
  Lean/FabiusFunction/LaplaceMomentBounds.lean; this report writes only this
  branch registry; that Lean source is now frozen
expected declarations or document claims: fabiusLaplaceMoment_strictAnti and
  normalizedLaplaceMoment_pos_all are implemented; both old nonnegativity APIs
  are preserved as compatibility consequences; source-level documentation
  states each new Lean theorem; no canonical document, facade, root, import,
  or other source claim
completed commits: 02c913b2d (registry-first claim) and caf654097 (one-file
  source/proof/documentation checkpoint); preceding all-order Lambert source
  8f47687e5 remains separately frozen and unmodified
validated (exact command, SHA/state, exit code): git diff --check exited 0;
  forbidden-placeholder scan is clean; the added-public-declaration scan
  finds exactly the two advertised names; both old nonnegativity headers and
  all three imports are preserved; three independent exact static reviews
  pass; this is not compiler evidence
not yet validated: source commit caf654097 has not been elaborated; no Lean,
  Lake, TeX, PDF, or cache-mutating process ran because both host Lean/Lake
  tokens remain unassigned/coordinator-controlled for this branch
requested integration or lease: independently review and preserve exact
  source commit caf654097 / blob 007c2ed04697, then assign separate serialized
  LAKE_JOBS=1 builds of +FabiusFunction.LaplaceMomentBounds and its direct
  importer +FabiusFunction.NegativeLaplaceDerivativeBounds; request no
  document or main-write lease
conflicts / dependencies: exact parent preimage is current-main blob
  9b6398320300; the other direct importer is FabiusDyadicSharpCumulant; no
  existing caller uses either new name; all active document work, pending
  all-order Lambert source, compact Lambert source, central valuation source,
  and moving shifted-prefix history are disjoint; only the coordinator may
  advance main
next bounded step: commit and push this exact immutable handoff; keep both
  pending Lean sources frozen for coordinator review/validation, and begin
  only read-only audits of disjoint cold paths until a new registry-first
  claim is justified
```

## Ordinary follow-on claim: the all-real cumulant differential chain

The normalized-moment recurrence is already valid at every real tilt, but its
first three cumulant-polynomial consequences are still stated only for
positive tilts.  Their proofs use no logarithmic-product identity: they are
pure polynomial consequences of

```text
R_k' = -R_(k+1) + R_k R_1.
```

Thus the identities `kappa_1' = kappa_2`, `kappa_2' = kappa_3`, and
`kappa_3' = kappa_4` hold on all of `R`.  Only the separate identification of
these polynomials with successive derivatives of `negativeLaplaceLog` still
requires positive scale.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: 5b053a32b10e758e39f1be23cb2e8d821fba8de6
HEAD and dirty paths: fd53d092874be974217068163129c8f94a332ba5;
  clean and pushed after both preceding immutable source handoffs; only this
  registry is dirty for the registry-first claim
writing (exact paths): this registry initially; after this claim is pushed and
  a repeated board/registry/all-tip scan remains green, only
  Lean/FabiusFunction/NegativeLaplaceDerivatives.lean and this registry
expected declarations or document claims:
  negativeLaplaceLogFirst_hasDerivAt_all, proving the derivative of the first
    normalized cumulant polynomial is the second at every real tilt;
  negativeLaplaceLogSecond_hasDerivAt_all, proving the corresponding second-
    to-third identity globally;
  negativeLaplaceLogThird_hasDerivAt_all, proving the third-to-fourth identity
    globally;
  preserve the exact headers of negativeLaplaceLogFirst_hasDerivAt,
    negativeLaplaceLogSecond_hasDerivAt, and
    negativeLaplaceLogThird_hasDerivAt as positive-scale compatibility
    wrappers, extracting their shared proof bodies into the new global API;
  expand the module overview and declaration comments with the three formulas
    and the precise distinction between globally defined normalized cumulant
    polynomials and the positive-scale logarithmic-product identification;
    no canonical document, facade, root, import, or other source path claimed
completed commits: preceding all-order Lambert source 8f47687e5 and strict
  Laplace-order source caf654097 are separately frozen and requested for
  coordinator validation; this is the registry-first claim for a disjoint
  seventh source unit
validated (exact command, SHA/state, exit code): current HEAD and origin/main
  share NegativeLaplaceDerivatives.lean blob
  7e8c54130ec34a2a97da9637f6fe04ec2f517239, content SHA-256
  B28A6BCF9E4FAB1D179ED72A5D61917FCCBD3BECD4382FFF2620F0B28DEC68F4;
  exact-name, plausible-semantic-name, exact-path, every-registry, and all-
  fetched-Fabius-tip scans found no global cumulant-chain implementation or
  competing lease; the historical theorem-polish lease is explicitly
  released; read-only proof audit verifies that the three existing positive-
  scale bodies become global simply by substituting
  normalizedLaplaceMoment_hasDerivAt_all for the restricted recurrence, with
  no import change; this is not compiler evidence
not yet validated: none of the three proposed declarations exists yet; no
  Lean, Lake, TeX, PDF, or cache-mutating process is authorized or running for
  this branch
requested integration or lease: advertise this ordinary one-source/three-name
  claim; after an immutable independently reviewed checkpoint, request
  separate serialized builds of +FabiusFunction.NegativeLaplaceDerivatives
  and the downstream consumer +FabiusFunction.NegativeLaplaceDerivativeBounds;
  request no document or main-write lease
conflicts / dependencies: negativeLaplaceLog_hasDerivAt genuinely remains
  positive-scale and will not be weakened; existing downstream calls in
  NegativeLaplaceDerivativeBounds and FabiusLambertDerivativeBounds keep the
  old compatibility names; the two pending source handoffs and every active
  document/source claim are disjoint; only the coordinator may advance main
next bounded step: commit and push this registry-only claim without force;
  fetch and reread any changed board, repeat all-tip collision checks, then
  edit only the claimed Lean source while three agents independently review
  proof extraction, exact header preservation, and source-level documentation
```

## Source checkpoint: all-real cumulant-chain derivatives

Exact source commit `d07e8ad3b` implements the complete three-name claim in
the sole leased module.  The committed `NegativeLaplaceDerivatives.lean` is Git
blob `80f3e80c1e9777405499a50da808bef5c71fa372`, with content SHA-256
`47A566FBBC19DCD7713F9BBF17ADE9BB349FE0D9AB6BAB21730A90A9EF8734CC`.

The new declarations are exactly:

- `negativeLaplaceLogFirst_hasDerivAt_all`;
- `negativeLaplaceLogSecond_hasDerivAt_all`;
- `negativeLaplaceLogThird_hasDerivAt_all`.

They prove the global differential chain among the first four normalized
cumulant polynomials by substituting
`normalizedLaplaceMoment_hasDerivAt_all` into the already established
polynomial proofs.  The first theorem negates the `R_1` recurrence, the second
differentiates `R_2 - R_1^2`, and the third differentiates
`-R_3 + 3 R_1 R_2 - 2 R_1^3`.  Its normalized result is exactly
`R_4 - 4 R_1 R_3 - 3 R_2^2 + 12 R_1^2 R_2 - 6 R_1^4`.

All three previous positive-scale declarations preserve their textual public
headers and theorem kinds.  Their bodies are now thin calls to the global
results, with tightly scoped unused-variable linter suppressions explaining
why each compatibility hypothesis remains.  The import is byte-unchanged.
Module and declaration prose explicitly separates the global cumulant
polynomial identities from the still-positive-scale identification with
successive derivatives of `negativeLaplaceLog`.

Two independent hostile reviews accept the live result.  Both checked the
first and second `congr_deriv` algebra, the third theorem's explicit derivative
normalization and `congr_of_eventuallyEq` orientation, every real-tilt edge
case, exact old headers and implicit binders, linter scopes, import sufficiency,
downstream call compatibility, naming, and documentation.  No source-level
blocker remains.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: 5b053a32b10e758e39f1be23cb2e8d821fba8de6
HEAD and dirty paths: d07e8ad3b2b53a4a1b4903b5e3f088bc95c6cb2d;
  source checkpoint is clean and pushed; only this registry is dirty for the
  immutable handoff
writing (exact paths): completed source checkpoint writes only
  Lean/FabiusFunction/NegativeLaplaceDerivatives.lean; this report writes only
  this branch registry; that Lean source is now frozen
expected declarations or document claims: all three advertised `_all`
  declarations are implemented; the three exact old positive-scale headers
  remain as compatibility wrappers; source-level documentation states each
  new Lean theorem and makes no global logarithmic-product claim; no canonical
  document, facade, root, import, or other source claim
completed commits: 7bba02fea (registry-first claim) and d07e8ad3b (one-file
  source/proof/documentation checkpoint); preceding all-order Lambert source
  8f47687e5 and strict Laplace-order source caf654097 remain separately frozen
  and unmodified
validated (exact command, SHA/state, exit code): git diff --check exited 0;
  forbidden-placeholder scan is clean; the added-public-declaration scan
  finds exactly the three advertised names; textual comparison confirms all
  three old headers and the import are unchanged; two independent exact
  static reviews pass after checking the delicate third-order proof; this is
  not compiler evidence
not yet validated: source commit d07e8ad3b has not been elaborated; no Lean,
  Lake, TeX, PDF, or cache-mutating process ran because this branch has no host
  build token
requested integration or lease: independently review and preserve exact
  source commit d07e8ad3b / blob 80f3e80c1e97, then assign separate serialized
  LAKE_JOBS=1 builds of +FabiusFunction.NegativeLaplaceDerivatives and the
  downstream consumer +FabiusFunction.NegativeLaplaceDerivativeBounds;
  request no document or main-write lease
conflicts / dependencies: exact parent preimage is current-main blob
  7e8c54130ec3; existing calls in NegativeLaplaceDerivativeBounds and
  FabiusLambertDerivativeBounds continue through the exact old APIs;
  negativeLaplaceLog_hasDerivAt intentionally remains positive-scale; the two
  other pending source handoffs and all current external branch changes are
  disjoint; only the coordinator may advance main
next bounded step: commit and push this immutable handoff; keep all three
  pending source paths frozen for coordinator review/validation; reserve the
  whole-line strict-convexity and formal Lambert fixed-point follow-ons until
  their current direct dependency gates are integrated and released, and
  continue read-only auditing of other disjoint cold paths
```

## Claim: exact constant-three binary-reduction majorant and regularity deduplication

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: 5b053a32b10e758e39f1be23cb2e8d821fba8de6
HEAD and dirty paths: 295c75b934daac7d34fa98ef86243643064b2b99;
  clean and pushed after the three preceding immutable source handoffs; only
  this registry is dirty for the registry-first claim
writing (exact paths): this registry initially; after this claim is pushed and
  a repeated board/registry/all-tip scan remains green, only
  Lean/FabiusFunction/FabiusBinaryReductionSeries.lean and this registry
expected declarations or document claims:
  norm_globalBinaryReductionSummand_le_three_mul_inv_pow, proving for every
    real x and every 1 <= m the exact telescope-derived majorant
    ‖globalBinaryReductionSummand x m‖ <= 3 * ((2 : R)^(m - 1))⁻¹;
  preserve the exact public headers of
    norm_globalBinaryReductionSummand_le_ge_two and
    norm_globalBinaryReductionSummand_le_of_one_le_all as constant-four
    compatibility corollaries;
  use the new constant-three comparison in
    summable_norm_globalBinaryReductionSummand_all without changing its
    public header;
  add the explicit FabiusFunction.Regularity import, delete the private
    fabiusReal_le_two_mul_of_mem_Icc_half re-proof, and call the existing
    public fabiusReal_le_two_mul theorem at its sole use;
  expand only the source module/declaration documentation with the exact
    constant-three formula, the positive-scale qualification, the retained
    compatibility estimates, and an explicit statement that no optimality is
    claimed; no canonical document, facade, root, or other source path claimed
completed commits: all-order Lambert source 8f47687e5, strict Laplace-order
  source caf654097, and all-real cumulant-chain source d07e8ad3b are separately
  frozen and requested for coordinator validation; this is the registry-first
  claim for a disjoint eighth source unit
validated (exact command, SHA/state, exit code): current HEAD and origin/main
  share FabiusBinaryReductionSeries.lean blob
  9944118b1cfa0791d8b3235586f5856a9f95a166, content SHA-256
  806F8D49B826C3580CDDBe21C34CB6881A73515B22D0CBD4C9530B671FC6BD6C;
  exact-name, plausible-semantic-name, exact-path, every-registry, and all-
  fetched-Fabius-tip scans found no constant-three implementation or competing
  lease; the coordinator explicitly records the prior six-name binary tranche
  as integrated, built, and released, with this Regularity/private-helper
  cleanup excluded; read-only arithmetic audit verifies
  2 * (2^(m-1))⁻¹ + 2 * (2^m)⁻¹ = 3 * (2^(m-1))⁻¹, and the
  public Regularity theorem has exactly the needed nonnegativity hypothesis;
  this is not compiler evidence
not yet validated: the proposed declaration and cleanup do not exist yet; no
  Lean, Lake, TeX, PDF, or cache-mutating process is authorized or running for
  this branch
requested integration or lease: advertise this ordinary one-source/one-name
  claim; after an immutable independently reviewed checkpoint, request
  separate serialized builds of +FabiusFunction.FabiusBinaryReductionSeries
  and its smallest direct consumer +FabiusFunction.FabiusGlobalQBinomialSeries;
  request no document or main-write lease
conflicts / dependencies: retain 1 <= m because the residual-difference
  identity is false at m = 0; retain inverse_two_pow_le_half and
  binaryTail_mem_Icc_half because the restricted residual API still uses
  their interval transport; Regularity imports Differential and creates no
  cycle with the existing TaylorReduction cone; the three pending source
  handoffs and every active external claim are disjoint; only the coordinator
  may advance main
next bounded step: commit and push this registry-only claim without force;
  fetch and reread any changed board, repeat all-tip collision checks, then
  edit only the claimed Lean source while three agents independently review
  proof arithmetic, exact header preservation, imports, and source-level
  documentation
```

## Source checkpoint: constant-three binary-reduction decay

Exact source commit `51b9ad393` implements the advertised one-name theorem,
compatibility refactor, regularity deduplication, and source documentation in
the sole leased module.  The committed `FabiusBinaryReductionSeries.lean` is
Git blob `637e4bb0ad439ecec43cdbef7895237484c8d315`, with content SHA-256
`92FCDB215915F68A2458A42885046B3A31A71CEC03BE34AC5B5A11C9BD0E0626`.

The new public declaration is exactly
`norm_globalBinaryReductionSummand_le_three_mul_inv_pow`.  For every real
input and every `1 ≤ m`, it proves

`‖globalBinaryReductionSummand x m‖ ≤ 3 * ((2 : ℝ) ^ (m - 1))⁻¹`.

Its proof uses the all-real residual telescope, bounds the consecutive
residuals at scales `m - 1` and `m` by the already-totalized estimates, and
keeps the resulting arithmetic as an equality rather than weakening constant
`3` to `4`.  In particular the edge case `m = 1` correctly invokes the total
bound at scale zero.  The existing constant-four declarations
`norm_globalBinaryReductionSummand_le_ge_two` and
`norm_globalBinaryReductionSummand_le_of_one_le_all` retain their exact public
headers as documented compatibility consequences.  The all-real absolute-
summability proof now compares against `3 * (1/2)^j`.

The module explicitly imports `FabiusFunction.Regularity`, deletes only the
private 19-line `fabiusReal_le_two_mul_of_mem_Icc_half` re-proof, and calls the
public `fabiusReal_le_two_mul` theorem at its sole former use.  The interval
transport helpers needed by the restricted remainder API remain in place.
Module and declaration prose states the full all-real positive-scale formula,
the constant-four compatibility bounds, and that no optimality of constant
`3` is claimed.  A complete scan finds an adjacent human-readable comment for
every public definition and theorem in the touched module.

Two independent hostile reviews pass on the exact final bytes.  They checked
the `m = 1` and nonpositive-input cases, residual-bound orientations,
power/inverse arithmetic, summability shift, import acyclicity, exact old
headers, tightly scoped unused-argument linter, deleted-helper callers,
downstream imports, naming, collisions, and source-document parity.  No
source-level blocker remains.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: 741db6b4b777abc3fb4ca9ba6a6f0f098399c1bb
HEAD and dirty paths: 51b9ad3936dbdd51423704e8f50fb8e9c77f9801;
  source checkpoint is clean and pushed; only this registry is dirty for the
  immutable handoff
writing (exact paths): completed source checkpoint writes only
  Lean/FabiusFunction/FabiusBinaryReductionSeries.lean; this report writes
  only this branch registry; that Lean source is now frozen
expected declarations or document claims: the single advertised constant-
  three theorem is implemented; both old constant-four headers remain exact;
  source-level documentation states every changed and new mathematical result;
  no canonical document, facade, root, audit ledger, or other source claim
completed commits: 5e696cc56 (registry-first claim), 736987748 (conflict-
  resolved merge of coordinator main, taking the validated Lambert proof
  repair), and 51b9ad393 (one-file source/proof/documentation checkpoint);
  the preceding Lambert, strict-moment, and cumulant handoffs are now integrated
  and compiler-green on main
validated (exact command, SHA/state, exit code): git diff --check exited 0;
  forbidden-placeholder scan is clean; exact header comparison confirms both
  compatibility APIs; the added-public-declaration scan finds exactly the
  advertised name; exact final blob/hash are recorded above; two independent
  exact-current-byte static reviews pass; this is not compiler evidence
not yet validated: source commit 51b9ad393 has not been elaborated; no Lean,
  Lake, TeX, PDF, or cache-mutating process ran because this branch has no host
  build token
requested integration or lease: independently review and preserve exact source
  commit 51b9ad393 / blob 637e4bb0ad43, then assign separate serialized
  LAKE_JOBS=1 builds of +FabiusFunction.FabiusBinaryReductionSeries and its
  smallest direct consumer +FabiusFunction.FabiusGlobalQBinomialSeries;
  request no document or main-write lease
conflicts / dependencies: exact parent preimage is current-main blob
  9944118b1cfa; `1 ≤ m` remains essential because the telescope step is false
  at `m = 0`; Regularity is acyclic and the old direct importers keep every
  compatibility API; all other active source/document claims are disjoint;
  only the coordinator may advance main
next bounded step: commit and push this immutable handoff; keep the binary
  source frozen for coordinator validation and continue read-only auditing of
  disjoint released paths, reserving strict convexity and the formal Lambert
  fixed point until their now-integrated dependencies are separately claimed
```

## Claim: strict alternating Laplace derivatives and whole-line convexity

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: fc63c39788ab4c31694e4f57efe05b543165675a
HEAD and dirty paths: 880760fc22252c80c497c3818e7fb72cfda13dca;
  clean and pushed after merging the general Kummer cocycle and settled
  primary exposition; only this registry is dirty for the registry-first claim
writing (exact paths): this registry initially; after this claim is pushed and
  a repeated board/registry/all-tip scan remains green, only
  Lean/FabiusFunction/LaplaceMomentBounds.lean and this registry
expected declarations or document claims:
  iteratedDeriv_fabiusLaplaceMoment_alternating_pos, proving for every
    k,n : ℕ and s : ℝ that
    0 < (-1 : ℝ)^n * iteratedDeriv n (fabiusLaplaceMoment F k) s;
  strictConvexOn_fabiusLaplaceMoment, proving
    StrictConvexOn ℝ Set.univ (fabiusLaplaceMoment F k) for every k;
  add the explicit Mathlib.Analysis.Convex.Deriv import required by the
    derivative criterion, preserve every existing public header and import,
    and expand the module/declaration prose with the whole-line alternating-
    derivative identity, its strict sign, and strict convexity; no canonical
    document, facade, root, audit ledger, or other source path claimed
completed commits: the constant-three binary source 51b9ad393 and handoff
  9e7f4df02 remain separately frozen and requested for coordinator validation;
  this is the registry-first claim for a disjoint ninth source unit
validated (exact command, SHA/state, exit code): current HEAD and origin/main
  share LaplaceMomentBounds.lean blob
  007c2ed04697ab56d3fd0654da477d32d360a61b, content SHA-256
  66686398FB67A05B4D60ADF737DF5FA99A8FA6773F2EB24AAE9C88D13D7A6084;
  exact-name, plausible-semantic-name, exact-path, every-registry, and all-
  fetched-Fabius-tip scans found no alternating-sign or whole-line strict-
  convexity implementation or competing lease; the coordinator records this
  module's strict-order predecessor as integrated, built, and released;
  read-only API audit confirms StrictMono.strictConvexOn_univ_of_deriv in the
  pinned Mathlib Convex.Deriv module, and the all-order sign follows directly
  from iteratedDeriv_fabiusLaplaceMoment plus fabiusLaplaceMoment_pos_all;
  this is not compiler evidence
not yet validated: neither proposed declaration exists yet; no Lean, Lake,
  TeX, PDF, or cache-mutating process is authorized or running for this branch
requested integration or lease: advertise this ordinary one-source/two-name
  claim; after an immutable independently reviewed checkpoint, request
  separate serialized builds of +FabiusFunction.LaplaceMomentBounds and the
  direct consumer +FabiusFunction.NegativeLaplaceDerivativeBounds; request no
  document or main-write lease
conflicts / dependencies: the signed theorem covers n = 0 and every real tilt;
  the convexity proof uses M_k' = -M_(k+1) and the already-integrated strict
  decrease of M_(k+1), equivalently M_k'' = M_(k+2) > 0; Mathlib has an
  AbsolutelyMonotoneOn API but no equally direct complete-monotonicity wrapper,
  so no reflected-function abstraction is claimed; the frozen binary source
  and every active external claim are disjoint; only the coordinator may
  advance main
next bounded step: commit and push this registry-only claim without force;
  fetch and reread any changed board, repeat all-tip collision checks, then
  edit only the claimed Lean source while three agents independently review
  signed-power normalization, the derivative criterion, exact header/import
  preservation, and source-level documentation
```

## Source checkpoint: strict alternating derivatives and convexity

Exact source commit `b044a0ec9` implements the complete two-name claim in the
sole leased module.  The committed `LaplaceMomentBounds.lean` is Git blob
`2ffeb693335c3b4baa1a7865e1a3e3e0ea1085f5`, with content SHA-256
`646D942F8D0C442890E4F6BB25699BF0C6C301272178250CD10FA4E59C70DE45`.

The new public declarations are exactly:

- `iteratedDeriv_fabiusLaplaceMoment_alternating_pos`;
- `strictConvexOn_fabiusLaplaceMoment`.

The first proves for every `k,n : ℕ` and `s : ℝ` that

`0 < (-1 : ℝ)^n * iteratedDeriv n (fabiusLaplaceMoment F k) s`.

Rewriting the existing exact iterated-derivative formula leaves two copies of
`(-1)^n`; reassociation, exponent addition, and the evenness of `n+n` cancel
them to one.  The remaining quantity is precisely the already-established
strictly positive moment `M_(k+n)(s)`.  This includes `n = 0` and imposes no
sign or asymptotic condition on `s`.

The second proves `StrictConvexOn ℝ Set.univ (fabiusLaplaceMoment F k)`.  Since
`M_k' = -M_(k+1)` and `M_(k+1)` is strictly decreasing on the whole line, the
derivative of `M_k` is strictly increasing.  Mathlib's whole-line derivative
criterion then yields strict convexity; equivalently, the all-order identity
gives `M_k'' = M_(k+2) > 0` everywhere.

The source directly imports `Mathlib.Analysis.Convex.Deriv`, retains all three
previous import lines in their original order, and places the two results
immediately after the existing strict-antitonicity theorem.  All twenty old
public declaration headers, attributes, and bodies are byte-preserved.  The
module and declaration prose display the alternating derivative identity,
strict sign, unrestricted domain, zero-order case, and strict-convexity
mechanism.  Neither new structural theorem is marked simp.

Two independent hostile reviews pass on the exact final bytes.  They checked
the sign cancellation for zero, odd, and even orders; the strict-order
orientation after negation; exact pinned `StrictMono.strictConvexOn_univ_of_deriv`
arguments; whole-line continuity and differentiability; imports; placement;
names; collisions; direct consumers; exact old source; and human-readable
documentation.  No source-level blocker remains.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: fc63c39788ab4c31694e4f57efe05b543165675a
HEAD and dirty paths: b044a0ec9f3d61788eb0db518cd48db2b085aed7;
  source checkpoint is clean and pushed; only this registry is dirty for the
  immutable handoff
writing (exact paths): completed source checkpoint writes only
  Lean/FabiusFunction/LaplaceMomentBounds.lean; this report writes only this
  branch registry; that Lean source is now frozen
expected declarations or document claims: both advertised declarations are
  implemented; every old public header/body is exact; source-level prose states
  both Lean theorems in human-readable form; no canonical document, facade,
  root, audit ledger, or other source claim
completed commits: a8ae1e7d5 (registry-first claim) and b044a0ec9 (one-file
  source/proof/documentation checkpoint); the disjoint constant-three binary
  source 51b9ad393 and handoff 9e7f4df02 remain separately frozen and pending
  coordinator validation
validated (exact command, SHA/state, exit code): git diff --check exited 0;
  forbidden-placeholder and duplicate-name scans are clean; mechanical diff
  comparison confirms all twenty old public declarations and all old imports;
  exact final blob/hash are recorded above; two independent exact-current-byte
  static reviews pass; this is not compiler evidence
not yet validated: source commit b044a0ec9 has not been elaborated; no Lean,
  Lake, TeX, PDF, or cache-mutating process ran because this branch has no host
  build token
requested integration or lease: independently review and preserve exact source
  commit b044a0ec9 / blob 2ffeb693335c, then assign separate serialized
  LAKE_JOBS=1 builds of +FabiusFunction.LaplaceMomentBounds and the direct
  consumer +FabiusFunction.NegativeLaplaceDerivativeBounds; request no
  document or main-write lease
conflicts / dependencies: exact parent preimage is current-main blob
  007c2ed04697; the all-order sign depends only on already-green derivative and
  positivity APIs; the explicit Convex.Deriv import is acyclic; both direct
  importers retain every old interface; the frozen binary source and every
  active external claim are disjoint; only the coordinator may advance main
next bounded step: commit and push this immutable handoff; keep both pending
  source paths frozen for coordinator validation; reserve the two-file formal
  Lambert fixed-point/dedup tranche as the next ordinary claim while continuing
  read-only audits of other released paths
```

## Claim: full Lambert displacement-series fixed point and downstream deduplication

The next ordinary source tranche is restricted to
`Lean/FabiusFunction/FabiusLambertFormalLog.lean` and
`Lean/FabiusFunction/FabiusLambertAllOrderRemainder.lean`.  It will promote the
downstream private mass-series identity to the formal-log API and package the
existing coefficientwise recurrence as the whole-series fixed-point equation

`A = a₀ + C(C((log 2)⁻¹)) * logSeries(unit)`.

Here `A` is `dyadicLambertDisplacementSeries`, `a₀` is
`dyadicLambertDisplacementPolynomial 0`, and the promoted mass-series identity
states that the unit series is `1 + X * A`.  These are identities of formal
power series; the source prose will explicitly make no convergence claim.

The exact new public, deliberately non-simp declarations are:

- `massSeries_dyadicLambertUnitSeriesCoefficient`;
- `dyadicLambertDisplacementSeries_fixedPoint`.

The first is the exact statement and proof currently hidden privately in
`FabiusLambertAllOrderRemainder`.  The second follows coefficientwise from the
already-integrated theorem
`dyadicLambertDisplacementPolynomial_eq_logCoeff`, with the constant
coefficient isolated explicitly.  Downstream, the private promoted duplicate
and the separate finite-truncation re-proof will be removed; the algebraic
residual proof will consume the public whole-series identity (or its already
proved coefficient consequence) while preserving every public declaration
header.  The FormalLog overview and declaration comments will display both
formal equations and document its three currently undocumented public simp
lemmas.  Only the Remainder module overview changes there; no canonical
document is claimed.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: fc63c39788ab4c31694e4f57efe05b543165675a
HEAD and dirty paths: 3c34416e4; clean before this registry-only claim
writing (exact paths):
  Lean/FabiusFunction/FabiusLambertFormalLog.lean;
  Lean/FabiusFunction/FabiusLambertAllOrderRemainder.lean;
  this branch registry for claim/handoff only
expected declarations or document claims: exactly
  massSeries_dyadicLambertUnitSeriesCoefficient and
  dyadicLambertDisplacementSeries_fixedPoint; promote one exact private
  duplicate, remove the private finite-truncation re-proof, preserve every old
  public declaration header/attribute, and add source-level formal-equation
  prose only
completed commits: all previous source checkpoints and their handoffs are
  clean and pushed; binary source 51b9ad393 / handoff 9e7f4df02 and strict
  Laplace source b044a0ec9 / handoff 3c34416e4 remain separately frozen and
  requested for coordinator validation; this is a disjoint registry-first
  two-file claim
validated (exact command, SHA/state, exit code): current HEAD and origin/main
  share FormalLog blob 4850c483aa1b30b094fcc132ce3979c5beb2336a,
  content SHA-256
  FA0C96CF187781761C6373FE21935518D43AB29FC11A935DCCBB63840E7AF902,
  and AllOrderRemainder blob a34ed0346e28e76c0b96ad2ffdfb080d0aa8d096,
  content SHA-256
  0199EB25D79DD1E9EF4FDA51BDE80E0CC3F8EFFF50748874CD4AE2574FC0E75D;
  all 120 locally visible refs and every registry were scanned: the fixed-point
  name is absent, while the mass-series name occurs only as the intended
  private downstream helper; current-source exact-name and path scans agree;
  this is not compiler evidence
not yet validated: neither public declaration nor the downstream cleanup is
  implemented; no Lean, Lake, TeX, PDF, or cache-mutating process is authorized
  or running for this branch
requested integration or lease: advertise this ordinary two-source claim;
  after an immutable independently reviewed checkpoint, request separate
  serialized builds of +FabiusFunction.FabiusLambertFormalLog,
  +FabiusFunction.FabiusLambertAllOrderRemainder, and the direct consumer
  +FabiusFunction.FabiusLambertAllOrderSmallArgument; request no document or
  main-write lease
conflicts / dependencies: the equations are purely formal and introduce no
  analytic/convergence premise; FormalLog's sole direct importer is the
  claimed Remainder module and Remainder's sole direct importer is
  AllOrderSmallArgument; the frozen binary and Laplace sources and all active
  external claims are disjoint; only the coordinator may advance main
next bounded step: commit and push this registry-only claim without force;
  fetch and reread any changed board, repeat collision checks, then edit only
  the two claimed sources while three agents independently inspect coefficient
  normalization, duplicate removal, exact old-header preservation, consumers,
  and source-level documentation
```

## Source checkpoint: full formal Lambert fixed point

Exact source commit `06ff742b7` completes the two-file claim.  Its result
objects are:

- `FabiusLambertFormalLog.lean`: Git blob
  `198675aab7c2a82f0ea2d7b0739fd80dbc392c7a`, content SHA-256
  `894623584E166F88DA30C50CDD6DC2372CB75D41707DCA5B31C28D3911164C1A`;
- `FabiusLambertAllOrderRemainder.lean`: Git blob
  `cf912c7061bb027ad0309b8c799a35c8ec0d9ff4`, content SHA-256
  `FB1FCA47491B2655D6369CFC39482F5722B793A1C91928E4A8F8A9E8E797D268`.

FormalLog now exposes exactly the two claimed non-simp declarations.  The
promoted mass-series theorem identifies the shifted coefficient sequence with
`1 + X * dyadicLambertDisplacementSeries`.  The fixed-point theorem assembles
the existing coefficient recurrence into

`A = C(a₀) + C(C((log 2)⁻¹)) * logSeries(unit)`.

Its proof is coefficientwise: `PowerSeries.coeff_C` isolates coefficient zero,
where `logCoeff_zero` kills the logarithmic term, and
`PowerSeries.coeff_C_mul` plus `coeff_logSeries` reduces every positive
coefficient to the established polynomial identity.  The module overview and
both declaration comments state the equations and explicitly disclaim
analytic convergence.  The three previously undocumented public simp lemmas
for the unit coefficients and displacement-series coefficients now have
formula-bearing prose.

AllOrderRemainder removes the exact private mass-series duplicate and the
separate forty-line finite-truncation logarithm proof.  Its substitution proof
uses the promoted public mass identity.  The residual divisibility proof now
extracts the truncated displacement coefficient and composed-log coefficient
directly, then closes with the existing public coefficient consequence of the
fixed point.  This shortens the proof, removes its polynomial evaluation and
field cancellation tail, and handles `N = 0`, `m = 0`, and positive
coefficients uniformly.  Every old import and public declaration header is
byte-preserved; the Remainder module prose accurately distinguishes purely
formal identities from the analytic estimates after finite evaluation.

Three independent static audits pass on the exact final bytes.  They checked
the pinned `coeff_C`, `coeff_C_mul`, and `coeff_logSeries` normal forms; zero
and positive coefficient branches; truncation indices; the `N = 0` boundary;
private-declaration removal; exact prior imports and public interfaces;
downstream consumers; names; and human-readable parity.  There is no known
source-level blocker.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: fc63c39788ab4c31694e4f57efe05b543165675a
HEAD and dirty paths: 06ff742b7e6f; source checkpoint is clean and pushed;
  only this registry is dirty for the immutable handoff
writing (exact paths): completed source checkpoint writes only
  Lean/FabiusFunction/FabiusLambertFormalLog.lean and
  Lean/FabiusFunction/FabiusLambertAllOrderRemainder.lean; this report writes
  only this branch registry; both Lean sources are now frozen
expected declarations or document claims: both claimed declarations are
  implemented exactly once and are non-simp; the two private downstream
  duplicates are gone; every old public header/attribute/import is exact;
  source prose states every new Lean theorem in human-readable formal-series
  form; no canonical document, facade, root, or audit-ledger claim
completed commits: a97ca2b8c (registry-first claim) and 06ff742b7 (two-file
  source/proof/documentation checkpoint); binary source 51b9ad393 / handoff
  9e7f4df02 and strict Laplace source b044a0ec9 / handoff 3c34416e4 remain
  separately frozen and pending coordinator validation
validated (exact command, SHA/state, exit code): git diff --check exited 0;
  whitespace, CR, forbidden-placeholder, duplicate-name, simp-registration,
  and declaration scans are clean; exact result blobs/hashes are recorded
  above; three independent exact-current-byte static reviews pass against
  pinned Mathlib APIs; this is not compiler evidence
not yet validated: source commit 06ff742b7 has not been elaborated; no Lean,
  Lake, TeX, PDF, or cache-mutating process ran because this branch has no host
  build token
requested integration or lease: independently review and preserve exact source
  commit 06ff742b7 / blobs 198675aab and cf912c706, then assign separate
  serialized LAKE_JOBS=1 builds of +FabiusFunction.FabiusLambertFormalLog,
  +FabiusFunction.FabiusLambertAllOrderRemainder, and the direct consumer
  +FabiusFunction.FabiusLambertAllOrderSmallArgument; request no document or
  main-write lease
conflicts / dependencies: exact preimages are the current-main blobs recorded
  in the claim; the public mass bridge is the former private downstream proof;
  the fixed point uses only already-integrated coefficient algebra; FormalLog
  and Remainder have a one-way import relation and no cycle; every frozen local
  source and active external claim is disjoint; only the coordinator may
  advance main
next bounded step: commit and push this immutable handoff; keep all three
  pending source tranches frozen for coordinator validation; continue with a
  new registry-first claim on a disjoint released path after a clean fetch and
  coordinator-board refresh
```

## Claim: generic even-subsequence summation and moment-series deduplication

This ordinary two-file tranche is restricted to
`Lean/FabiusFunction/AnalyticMoments.lean` and
`Lean/FabiusFunction/FabiusLegendreSeries.lean`.  It will promote the common
summation principle currently proved privately in the Legendre module:

```lean
theorem hasSum_even_of_odd_eq_zero
    {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    {f : ℕ → E} {a : E}
    (h : HasSum f a) (hodd : ∀ n, f (2 * n + 1) = 0) :
    HasSum (fun n ↦ f (2 * n)) a
```

The theorem needs neither a norm nor completeness: injective reindexing by
`n ↦ 2*n` preserves the sum because every term outside its range is odd and
therefore zero.  Its proof will use Mathlib's
`Function.Injective.hasSum_iff`, whose exact orientation is
`HasSum (f ∘ g) a ↔ HasSum f a`.

In AnalyticMoments, the new result replaces the separate summability,
odd-subseries, even/odd recombination, uniqueness, and tsum-rewrite block in
`rvachevFourier_eq_momentSeries` with one direct application.  In
FabiusLegendreSeries, the more restrictive private normed/complete helper is
deleted; its pointwise and uniform call sites resolve unchanged to the shared
generic result through the existing import cone.  No import or old public
declaration header changes are planned.

While AnalyticMoments is leased, formula-bearing declaration comments will be
added to its five current public prose gaps:
`moment_eq_integral_formula`, `halfMoment_eq_fabius_formula`,
`halfIntegral_eq_rvachev_dyadic_formula`,
`moment_halfIntegral_eq_rvachev_dyadic_formula`, and
`proposition_two_formula`.  The final comment will state the totalized
`complexExpm1Div` identity rather than an invalid unqualified quotient at
`z = 0`.  The module overview will record the reusable zero-odd-subsequence
principle.  No canonical document is claimed.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: fc63c39788ab4c31694e4f57efe05b543165675a
HEAD and dirty paths: bb6e66ad8f9d; clean before this registry-only claim
writing (exact paths): Lean/FabiusFunction/AnalyticMoments.lean;
  Lean/FabiusFunction/FabiusLegendreSeries.lean; this branch registry for
  claim/handoff only
expected declarations or document claims: exactly one new public declaration,
  hasSum_even_of_odd_eq_zero; replace one independent Fourier proof block,
  remove one private Legendre duplicate, preserve every old public
  header/attribute and import, and add source-level formula prose for the new
  theorem plus the five named existing declarations
completed commits: all prior source checkpoints and handoffs are clean and
  pushed; binary, strict-Laplace, and formal-Lambert sources remain separately
  frozen and requested for coordinator validation; this is a disjoint
  registry-first two-file claim
validated (exact command, SHA/state, exit code): current HEAD and origin/main
  share AnalyticMoments blob f0985d5b6e5b20c14683413bff9916e89ebd9932,
  content SHA-256
  EE720F2922A24159F12C78063972E4C484E99BDD4068FFECE2F136A045002D86,
  and FabiusLegendreSeries blob
  77982a661e75d73bf9b3dcc4d276776a855310e0, content SHA-256
  7B752F2647D0377717155038E5164E3AA9D06117205F27D96C7058DD8E4086CB;
  all active fetched Fabius tips share these blobs; exact-name, semantic-name,
  path, and every-registry scans find only the intended private Legendre helper
  and no public implementation or competing lease; the coordinator records
  the earlier AnalyticMoments source unit integrated, compiled, and released;
  two independent pinned-API preflights confirm the minimal typeclasses and
  hasSum_iff orientation; this is not compiler evidence
not yet validated: the public helper, proof contractions, and comments are not
  implemented; no Lean, Lake, TeX, PDF, or cache-mutating process is authorized
  or running for this branch
requested integration or lease: advertise this ordinary two-source claim;
  after an immutable independently reviewed checkpoint, request separate
  serialized builds of +FabiusFunction.AnalyticMoments,
  +FabiusFunction.FabiusLegendreSeries, and one direct Legendre consumer
  (+FabiusFunction.FabiusTranslatedLegendreSeries or
  +FabiusFunction.FabiusLegendreLeastSquares); request no document or
  main-write lease
conflicts / dependencies: the theorem is purely topological/additive and does
  not require summability side conditions beyond HasSum; the two target files
  are in an existing one-way transitive import relation with no reverse edge;
  all frozen local paths and active external claims are disjoint; only the
  coordinator may advance main
next bounded step: commit and push this registry-only claim without force;
  fetch and reread any changed board, repeat collision checks, then edit only
  the two claimed Lean sources while three agents independently audit the
  generic reindexing proof, both consumer families, interface preservation,
  and the five formula comments
```

## Source checkpoint: generic zero-odd subsequence summation

Exact source commit `6818db074` completes the two-file common-lemma tranche.
Its result objects are:

- `AnalyticMoments.lean`: Git blob
  `a5ce5ca3b5bf62d858ef1e8a4eb6818a04a17a8f`, content SHA-256
  `4B893BB0DE22E16E5A48724A0DB48A2713768B12DDEB68BF14EE7EB61E19EE9B`;
- `FabiusLegendreSeries.lean`: Git blob
  `af2423bed82b7c97bfeed5234f0ac31d95ac2614`, content SHA-256
  `4E4A3D1A6059E8862E8A02C223CA54152A23869B53E73E1EF51FD7B2935A619A`.

AnalyticMoments now exposes exactly one documented
`hasSum_even_of_odd_eq_zero` theorem under the minimal assumptions
`[AddCommMonoid E] [TopologicalSpace E]`.  The proof explicitly changes the
goal to composition with the injective map `n ↦ 2*n`, rewrites with
`Function.Injective.hasSum_iff`, and proves that every index outside the range
is odd.  It introduces no norm, completeness, uniqueness, or auxiliary
summability premise.

`rvachevFourier_eq_momentSeries` now obtains its even-indexed series in one
application of the shared result.  This deletes the manual even summability,
zero odd-series, recombination, uniqueness, and tsum rewrite without changing
the theorem header or later moment identification.  FabiusLegendreSeries
removes its private normed/complete copy and the empty section heading; both
its pointwise real and uniform continuous-map calls remain byte-identical and
resolve through the existing import cone.

The five claimed public documentation gaps in AnalyticMoments now display
their exact formulas and hypotheses.  In particular, the half-line statement
records both conjuncts, the inverse-dyadic result records `1 ≤ n`, and the
Proposition 2 comment uses the totalized `complexExpm1Div` factor at `z = 0`.
The overview records the reusable parity-summation principle.  Hosting the
helper in AnalyticMoments, rather than the older `AUDIT_FINDINGS.md` suggestion
of MomentPowerSeries, avoids adding an otherwise unrelated infinite-sum import
to that lower algebra module; the coordinator may close that finding on
integration.

Three independent source/API audits pass on the exact final bytes.  They
verified the pinned `hasSum_iff` orientation and rewrite side-goal order,
`range_two_mul`/odd-index normalization, Fourier unification, both Legendre
codomains, transitive one-way import cone, exact old imports and public
headers, formula prose, names, and current-ref collisions.  No source-level
blocker remains.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: fc63c39788ab4c31694e4f57efe05b543165675a
HEAD and dirty paths: 6818db074; source checkpoint is clean and pushed; only
  this registry is dirty for the immutable handoff
writing (exact paths): completed source checkpoint writes only
  Lean/FabiusFunction/AnalyticMoments.lean and
  Lean/FabiusFunction/FabiusLegendreSeries.lean; this report writes only this
  branch registry; both Lean sources are now frozen
expected declarations or document claims: the one claimed generic theorem is
  implemented exactly once; the private duplicate and manual Fourier proof
  are removed; every old import/public header/attribute is exact; five existing
  theorem comments and the new theorem/module prose state their Lean formulas
  in human-readable form; no canonical document, facade, root, or audit-ledger
  write
completed commits: 94c52a6ae (registry-first claim) and 6818db074 (two-file
  source/proof/documentation checkpoint); four earlier pending source tranches
  remain separately frozen and requested for coordinator validation
validated (exact command, SHA/state, exit code): git diff --check exited 0;
  whitespace, CR, forbidden-placeholder, TODO/FIXME, duplicate-name, stale
  split-helper, import, attribute, and declaration scans are clean; exact
  result blobs/hashes are recorded above; three independent exact-current-byte
  static reviews pass against pinned Mathlib; this is not compiler evidence
not yet validated: source commit 6818db074 has not been elaborated; no Lean,
  Lake, TeX, PDF, or cache-mutating process ran because this branch has no host
  build token
requested integration or lease: independently review and preserve exact source
  commit 6818db074 / blobs a5ce5ca3b and af2423bed, then assign separate
  serialized LAKE_JOBS=1 builds of +FabiusFunction.AnalyticMoments,
  +FabiusFunction.FabiusLegendreSeries, and one direct consumer such as
  +FabiusFunction.FabiusTranslatedLegendreSeries or
  +FabiusFunction.FabiusLegendreLeastSquares; request no document or main-write
  lease
conflicts / dependencies: exact preimages are the current-main blobs recorded
  in the claim; the generic theorem depends only on an established Mathlib
  reindexing equivalence; Legendre already reaches AnalyticMoments transitively
  with no reverse edge; all frozen local paths and active external claims are
  disjoint; only the coordinator may advance main
next bounded step: commit and push this immutable handoff; freeze both sources
  for coordinator validation; continue with the audited private kernel-normal-
  form promotion in two disjoint released modules after a clean registry-first
  claim and fresh collision scan
```

## Claim: public negative-Laplace kernel normal form and Bose deduplication

This very small ordinary tranche is restricted to
`Lean/FabiusFunction/NegativeLaplace.lean` and
`Lean/FabiusFunction/BoseFinitePartIntegral.lean`.  It promotes the existing
private, already-used normal form

```lean
theorem negativeLaplaceKernel_eq_log_sub_log (s : ℝ) (hs : 0 < s) :
    negativeLaplaceKernel s =
      Real.log (1 - Real.exp (-s)) - Real.log s
```

without changing its statement or proof, adds exact positive-domain prose,
and replaces the duplicated logarithm-of-a-quotient argument in
`boseLogKernel_eq_negativeLaplaceKernel_add_log` by one application of the
promoted theorem.  The latter theorem's public header remains exact and its
two downstream Bose consumers remain unchanged.  No adjacent helper, simp
attribute, import, facade, or canonical document is claimed.

The positivity assumption is intentional: it supplies both nonzero arguments
needed by `Real.log_div`.  In particular, this tranche does not state the
split at `s = 0`, where the totalized definitions do not support the displayed
positive-domain factorization.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: fc63c39788ab4c31694e4f57efe05b543165675a
HEAD and dirty paths: 4265436a4; clean before this registry-only claim
writing (exact paths): Lean/FabiusFunction/NegativeLaplace.lean;
  Lean/FabiusFunction/BoseFinitePartIntegral.lean; this branch registry for
  claim/handoff only
expected declarations or document claims: expose exactly the existing
  negativeLaplaceKernel_eq_log_sub_log name as a documented public theorem;
  preserve its statement/proof, preserve every old public header/attribute and
  import, replace only the duplicated Bose proof body, and add no source claim
  beyond the theorem's exact human-readable formula
completed commits: all prior source checkpoints and handoffs are clean and
  pushed; five earlier pending tranches remain separately frozen and requested
  for coordinator validation; this is a disjoint registry-first two-file claim
validated (exact command, SHA/state, exit code): current HEAD and origin/main
  share NegativeLaplace blob b25e7901e46086b2fc31cc1b7d8ed997941c4cb2,
  content SHA-256
  C60FDCDFC68F245D02E3C0DB5682C9889C9216F8E2885FD63D9DC9311ED963FD,
  and BoseFinitePartIntegral blob
  7d7076eb4a68ae65fdbb16b56482ba371f7eca03, content SHA-256
  B48D102245DEE9035521FF0509BA3BBFB6E6CBBB15CE7467C08624E5EAB6AAB5;
  all active fetched Fabius tips share these blobs; exact-name, semantic-name,
  path, and every-registry scans find only the intended private declaration
  and no public implementation or competing lease; coordinator records both
  historical leases compiled and released; two independent proof/import audits
  confirm the Real.log_div conditions and one-way import cone; this is not
  compiler evidence
not yet validated: visibility, documentation, and Bose refactor are not
  implemented; no Lean, Lake, TeX, PDF, or cache-mutating process is authorized
  or running for this branch
requested integration or lease: advertise this ordinary two-source claim;
  after an immutable independently reviewed checkpoint, request separate
  serialized builds of +FabiusFunction.NegativeLaplace,
  +FabiusFunction.BoseFinitePartIntegral, and the direct consumer
  +FabiusFunction.PeriodicMean; request no document or main-write lease
conflicts / dependencies: Bose reaches NegativeLaplace through the existing
  MellinFinitePart/MellinBose/PeriodicCorrection chain, with no reverse edge or
  import cycle; all frozen local paths and active external claims are disjoint;
  only the coordinator may advance main
next bounded step: commit and push this registry-only claim without force;
  fetch and reread any changed board, repeat collision checks, then edit only
  the two claimed sources while three agents independently verify exact proof
  preservation, rewrite orientation, public interfaces, consumers, and prose
```

## Source checkpoint: public negative-Laplace kernel normal form

Exact source commit `ab1d4c35d` completes the two-file visibility and
deduplication claim.  Its result objects are:

- `NegativeLaplace.lean`: Git blob
  `6713f2fd4cdd7b58462eb522d5345d8ef4ee6e9a`, content SHA-256
  `86E0D813192C17D9DF76B642640120C67A4BFB215C2FB5ED6C3CA79B86F75324`;
- `BoseFinitePartIntegral.lean`: Git blob
  `c2d246ecea21c4cf59268a5c2cea3026776ab6ad`, content SHA-256
  `52EAEB9E14C6E01D6B3D47FE62827F852E72FF828C59959477EE012FAADCFB03`.

The NegativeLaplace change is exactly a documented private-to-public
promotion.  The theorem statement and entire existing proof body are
byte-preserved, no simp attribute was added, and adjacent helpers remain
private.  Its source comment states the exact factorization and the strict
positive-domain hypothesis that supplies both nonzero arguments to
`Real.log_div`.

The Bose theorem keeps its public declaration comment and header exactly, but
its duplicated positivity and logarithm-of-a-quotient proof is replaced by the
single deterministic line

`rw [boseLogKernel, negativeLaplaceKernel_eq_log_sub_log x hx, sub_add_cancel]`.

This exposes the numerator logarithm and cancels the scale logarithm literally.
The internal multiplicative-correction consumer in NegativeLaplace and both
finite-part consumers in Bose remain unchanged.  All imports, all other public
headers/bodies, namespaces, and attributes are exact.

Three independent exact-byte reviews pass.  They verified the nonzero
conditions, `Real.log_div` orientation, the final additive normalization,
visibility and name collision, the acyclic transitive import path, every
consumer, and exact interface preservation.  No source-level blocker remains.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: fc63c39788ab4c31694e4f57efe05b543165675a
HEAD and dirty paths: ab1d4c35d; source checkpoint is clean and pushed; only
  this registry is dirty for the immutable handoff
writing (exact paths): completed source checkpoint writes only
  Lean/FabiusFunction/NegativeLaplace.lean and
  Lean/FabiusFunction/BoseFinitePartIntegral.lean; this report writes only this
  branch registry; both Lean sources are now frozen
expected declarations or document claims: the existing kernel normal form is
  now public and documented exactly once; the duplicated Bose body is removed;
  every old import/public header/attribute and every consumer is exact; no
  canonical document, facade, root, or audit-ledger write
completed commits: b7282f4d5 (registry-first claim) and ab1d4c35d (two-file
  source/proof/documentation checkpoint); six earlier pending source tranches
  remain separately frozen and requested for coordinator validation
validated (exact command, SHA/state, exit code): git diff --check exited 0;
  whitespace, CR, forbidden-placeholder, TODO/FIXME, exact-name, simp,
  adjacent-private-helper, import, declaration, and consumer scans are clean;
  exact result blobs/hashes are recorded above; three independent exact-byte
  static reviews pass against pinned Mathlib; this is not compiler evidence
not yet validated: source commit ab1d4c35d has not been elaborated; no Lean,
  Lake, TeX, PDF, or cache-mutating process ran because this branch has no host
  build token
requested integration or lease: independently review and preserve exact source
  commit ab1d4c35d / blobs 6713f2fd4 and c2d246ece, then assign separate
  serialized LAKE_JOBS=1 builds of +FabiusFunction.NegativeLaplace,
  +FabiusFunction.BoseFinitePartIntegral, and direct consumer
  +FabiusFunction.PeriodicMean; request no document or main-write lease
conflicts / dependencies: exact preimages are the current-main blobs recorded
  in the claim; Bose reaches NegativeLaplace through an existing one-way
  transitive import chain and introduces no cycle; the formula is deliberately
  restricted to positive input; all frozen local paths and active external
  claims are disjoint; only the coordinator may advance main
next bounded step: commit and push this immutable handoff; freeze both sources
  for coordinator validation; refresh main and the full ownership board before
  choosing any further ordinary source unit
```

## Claim: repair the Proposition 22 source documentation

Claimed exact source path:

- `Lean/FabiusFunction/PaperStatements.lean`.

This comment-only tranche repairs a materially misattached declaration comment.
The existing prose “Proposition 22: the Bernoulli recurrences for `c_n` and
`d_n`” currently documents `proposition_twenty_two_initial`, whose conclusion
is only `moment 0 = 1 ∧ halfMoment 0 = 1`.  The actual recurrence theorem
`proposition_twenty_two` immediately below it is the module's sole remaining
undocumented public declaration.

The edit changes exactly two adjacent source comments: the first will state the
initial conditions `c₀ = d₀ = 1`, represented by the two zero-index moment
equalities, and the second will define `c_j = moment j`,
`d_j = halfMoment j`, and `B_j = bernoulli j` and display both exact Bernoulli
recurrences under `1 ≤ n`.  No import, namespace, attribute, declaration
header, theorem statement, proof, module overview, facade, audit ledger, or
canonical document is claimed.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: fc63c39788ab4c31694e4f57efe05b543165675a
HEAD and dirty paths: fac753e38; clean before this registry-only claim
writing (exact paths): Lean/FabiusFunction/PaperStatements.lean; this branch
  registry for claim/handoff only
expected declarations or document claims: repair the comment on
  proposition_twenty_two_initial and add the exact formula-bearing comment on
  proposition_twenty_two; alter no Lean term or public interface
completed commits: all prior source checkpoints and handoffs are clean and
  pushed; this is a disjoint registry-first, comment-only claim
validated (exact command, SHA/state, exit code): current HEAD and origin/main
  share PaperStatements blob c72b9022da43d728a649a5e81e5083afeb01385e,
  content SHA-256
  214B6D572A0F6626A2C231C46CE2C731BEC5120905AA7B2FF22DB4CC3D83516B;
  exact-path and registry scans find no competing lease or claim; a complete
  declaration-comment audit identifies proposition_twenty_two as the sole
  public documentation gap in this paper-facing module; this is not compiler
  evidence
not yet validated: the two comments are not implemented; no Lean, Lake, TeX,
  PDF, or cache-mutating process is authorized or running for this branch
requested integration or lease: advertise this ordinary one-source claim;
  after an immutable independently reviewed checkpoint, request the policy
  gates +FabiusFunction.PaperStatements and direct importer
  +FabiusFunction.Paper06487Supplement if the coordinator does not waive them
  for a comment-only diff; request no document or main-write lease
conflicts / dependencies: comments erase and have no API or consumer effect;
  all frozen local paths and active external claims are disjoint; only the
  coordinator may advance main
next bounded step: commit and push this registry-only claim without force;
  repeat post-claim collision checks, then edit only the claimed source while
  independent agents verify exact formula transcription, attachment, and
  byte-preservation of every Lean term and interface
```

## Source checkpoint: Proposition 22 documentation parity

Exact source commit `64e756787` completes the comment-only claim.  The result
object for `PaperStatements.lean` is Git blob
`64684845880bf9e96b5774a4308abf0fdb573349`, with content SHA-256
`E8ED3E148E488693BBF143C16BF9B36A50C74C545CB2AFB972414E8D4F69A316`.

The corrected comment on `proposition_twenty_two_initial` now states precisely
the two initial conditions represented by its conclusion.  The new adjacent
comment on `proposition_twenty_two` defines the `c`, `d`, and Bernoulli
coefficient notation, records `1 ≤ n`, and displays both exact recurrences with
inclusive index ranges.  Every Lean token, import, namespace, attribute,
declaration header, theorem statement, proof body, module comment, and all
unrelated prose are byte-preserved.

Two independent exact-current-byte reviews checked every range, exponent,
factor, binomial and Bernoulli index, moment shift, sign, and denominator
against the formal theorem and passed without qualification.  This closes the
sole remaining undocumented public declaration in the paper-facing module and
repairs the formerly false attachment without changing the compiled program.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: fc63c39788ab4c31694e4f57efe05b543165675a
HEAD and dirty paths: 64e756787; source checkpoint is clean and pushed; only
  this registry is dirty for the immutable handoff
writing (exact paths): completed source checkpoint writes only
  Lean/FabiusFunction/PaperStatements.lean; this report writes only this branch
  registry; the Lean source is now frozen
expected declarations or document claims: initial-condition and recurrence
  comments now attach to their exact Proposition 22 declarations; no Lean term
  or public interface changed
completed commits: 0c3da6303 (registry-first claim) and 64e756787
  (comment-only source checkpoint); all earlier pending source tranches remain
  separately frozen and requested for coordinator validation
validated (exact command, SHA/state, exit code): git diff --check exited 0;
  whitespace, CR, tab, exact-diff, import, declaration-header, theorem-body,
  attachment, and complete formula-transcription scans are clean; exact result
  blob/hash is recorded above; two independent exact-byte static reviews pass;
  this is not compiler evidence
not yet validated: source commit 64e756787 has not been elaborated; no Lean,
  Lake, TeX, PDF, or cache-mutating process ran because this branch has no host
  build token; comments erase, so no elaboration change is expected
requested integration or lease: independently preserve exact source commit
  64e756787 / blob 646848458, then run or explicitly waive the policy gates
  +FabiusFunction.PaperStatements and direct importer
  +FabiusFunction.Paper06487Supplement; request no document or main-write lease
conflicts / dependencies: exact preimage is the current-main blob recorded in
  the claim; the diff is comments only and cannot affect consumers; all frozen
  local paths and active external claims are disjoint; only the coordinator may
  advance main
next bounded step: commit and push this immutable handoff; freeze the source
  for coordinator disposition; refresh main and the full ownership board before
  claiming the next ordinary theorem tranche
```

## Claim: simultaneous-vanishing obstruction for Wikipedia errors

Claimed exact source path:

- `Lean/FabiusFunction/FabiusWikipediaObstruction.lean`.

This tranche extracts the topological core currently hidden inside a
rate-specific Big-O proof.  It adds exactly the public theorem

```lean
theorem fabiusWikipediaElementaryMain_error_not_tendsto_zero_of_corrected
    (q : ℝ → ℝ)
    (hcorrected : Tendsto
      (fun x : ℝ => q x - fabiusExplicitCorrectedWikipediaMain x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    ¬ Tendsto (fun x : ℝ => q x - fabiusWikipediaElementaryMain x)
        (nhdsWithin 0 (Ioi 0)) (nhds 0)
```

and refactors only the proof body of
`fabiusWikipediaElementaryMain_error_not_isBigO_of_corrected_of_tendsto`
through it, preserving that declaration's header exactly.  The new statement
is strictly more general than the existing same-rate obstruction: it assumes
only that the corrected error tends to zero and rules out convergence of the
uncorrected error, with no shared comparison function or Big-O hypothesis.

The source documentation will display that the difference of the two errors is
`negativeLaplacePsi (fabiusLambertPhase x)`, whose non-vanishing limit
obstruction is already proved above.  No import, facade, canonical document,
adjacent theorem header, or additional claim is included.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: fc63c39788ab4c31694e4f57efe05b543165675a
HEAD and dirty paths: e05a177e1; clean before this registry-only claim
writing (exact paths): Lean/FabiusFunction/FabiusWikipediaObstruction.lean;
  this branch registry for claim/handoff only
expected declarations or document claims: add exactly
  fabiusWikipediaElementaryMain_error_not_tendsto_zero_of_corrected; refactor
  only the body of the existing vanishing-rate Big-O theorem through it;
  preserve every old header/attribute/import and document the exact difference
completed commits: all prior source checkpoints and handoffs are clean and
  pushed; this is a disjoint registry-first one-file claim
validated (exact command, SHA/state, exit code): current HEAD and origin/main
  share FabiusWikipediaObstruction blob
  37d11226b0b626889a01f561640dd94222a886f3, content SHA-256
  1E23047ED904DBFE11E0B826EC629FFD92A1C289033343DB987D8BD67E1C5FCE;
  exact-name scans across every visible Lean ref find no implementation;
  registry/path scans find no competing lease; the related historical
  Wikipedia/Lambert tranche is integrated and released; an independent
  proof/API audit verifies the Tendsto subtraction orientation and the existing
  adjacent congruence pattern; this is not compiler evidence
not yet validated: theorem, refactor, and prose are not implemented; no Lean,
  Lake, TeX, PDF, or cache-mutating process is authorized or running for this
  branch
requested integration or lease: advertise this ordinary one-source claim;
  after an immutable independently reviewed checkpoint, request separate
  serialized builds of +FabiusFunction.FabiusWikipediaObstruction and direct
  importer +FabiusFunction.FabiusSharpAsymptotic; request no document or
  main-write lease
conflicts / dependencies: the new proof packages the already-proved periodic
  nonconvergence theorem and the same algebra used by an existing longer proof;
  imports remain exact; all frozen local paths and active external claims are
  disjoint; only the coordinator may advance main
next bounded step: commit and push this registry-only claim without force;
  repeat collision checks, then edit only the claimed source while independent
  agents verify filter orientation, algebraic identity, old-header preservation,
  source documentation, and direct-consumer compatibility
```

## Source checkpoint: simultaneous-vanishing Wikipedia obstruction

Exact source commit `30a02d4a7` completes the one-file strengthening and
refactor.  Its result for `FabiusWikipediaObstruction.lean` is Git blob
`15f1f9afc4df48630cd31b5434627db0dd314827`, with content SHA-256
`9BB093CE27835E7F5551A49BB77F80083D85AEF906E6AE0C21DF9BEC36E3F0AA`.

The new public theorem
`fabiusWikipediaElementaryMain_error_not_tendsto_zero_of_corrected` states the
filter-level obstruction without choosing a rate: if the error relative to the
explicit corrected Wikipedia main term tends to zero at `0⁺`, then the error
relative to the uncorrected main term does not.  Its proof subtracts the two
limits, identifies the difference globally with
`negativeLaplacePsi (fabiusLambertPhase x)`, and invokes the existing intrinsic
nonconvergence theorem.

The old arbitrary-vanishing-scale Big-O theorem keeps its exact public header
and is now a two-line corollary obtained by sending both Big-O estimates to
zero.  All imports and all other old declaration headers/attributes are exact.
Module and declaration prose state the exact errors, exact difference, and the
logical progression from simultaneous convergence to vanishing-scale Big-O
and then the logarithmic scale.

Two independent exact-current-byte hostile reviews pass.  They checked the
subtraction sign, `Tendsto.sub` and `congr'` orientation, the common
`nhdsWithin 0 (Ioi 0)` filter, algebra after unfolding the corrected main term,
both `IsBigO.trans_tendsto` applications, every preserved interface, imports,
consumers, docs, and name collision.  No source-level blocker remains.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: fc63c39788ab4c31694e4f57efe05b543165675a
HEAD and dirty paths: 30a02d4a7; source checkpoint is clean and pushed; only
  this registry is dirty for the immutable handoff
writing (exact paths): completed source checkpoint writes only
  Lean/FabiusFunction/FabiusWikipediaObstruction.lean; this report writes only
  this branch registry; the Lean source is now frozen
expected declarations or document claims: the claimed Tendsto obstruction is
  public and documented exactly once; the old Big-O header is preserved and its
  body factors through the stronger result; imports and all other interfaces
  are exact
completed commits: 7fc020e3b (registry-first claim) and 30a02d4a7 (one-file
  theorem/refactor/documentation checkpoint); earlier pending source tranches
  remain separately frozen and requested for coordinator validation
validated (exact command, SHA/state, exit code): git diff --check exited 0;
  whitespace, CR, tab, placeholder, exact-name, import, declaration-header,
  proof-orientation, algebra, filter, consumer, and documentation scans are
  clean; exact result blob/hash is recorded above; two independent exact-byte
  static reviews pass against pinned APIs and an existing compiled congruence
  pattern; this is not compiler evidence
not yet validated: source commit 30a02d4a7 has not been elaborated; no Lean,
  Lake, TeX, PDF, or cache-mutating process ran because this branch has no host
  build token
requested integration or lease: independently review and preserve exact source
  commit 30a02d4a7 / blob 15f1f9afc, then assign separate serialized builds of
  +FabiusFunction.FabiusWikipediaObstruction and direct importer
  +FabiusFunction.FabiusSharpAsymptotic; request no document or main-write lease
conflicts / dependencies: exact preimage is the current-main blob recorded in
  the claim; no import changed and the proof packages established local facts;
  all frozen local paths and active external claims are disjoint; only the
  coordinator may advance main
next bounded step: commit and push this immutable handoff; freeze the source
  for coordinator validation; refresh main and the full ownership board before
  claiming the next ordinary theorem tranche
```

## Claim: real affine Prouhet identities and uniform-spline deduplication

Claimed exact source paths:

- `Lean/FabiusFunction/ThueMorsePrefix.lean`;
- `Lean/FabiusFunction/FabiusUniformSpline.lean`.

This atomic two-file tranche exports the real affine companions of the public
rational Prouhet API:

```lean
theorem thueMorse_affine_power_sum_eq_zero_real
    (r d : ℕ) (hd : d < r) (x y : ℝ) :
    (∑ h : Fin (2 ^ r), (thueMorseSign h.val : ℝ) *
      (x + y * (h.val : ℝ)) ^ d) = 0

theorem thueMorse_affine_power_sum_self_real
    (r : ℕ) (x y : ℝ) :
    (∑ h : Fin (2 ^ r), (thueMorseSign h.val : ℝ) *
      (x + y * (h.val : ℝ)) ^ r) =
      (-1 : ℝ) ^ r * y ^ r * (2 : ℝ) ^ r.choose 2 * r.factorial
```

The sharp theorem genuinely strengthens the existing downstream private
slope-one result: translation still disappears, while an arbitrary real slope
contributes exactly `y ^ r`.  It covers `r = 0` and `y = 0` under Lean's
`0 ^ 0 = 1` convention.

After adding the two documented public declarations immediately beside their
rational analogues in `ThueMorsePrefix`, the tranche deletes the complete
six-declaration duplicate stack in `FabiusUniformSpline`: the two private real
affine theorems and the private rational power-sum definition, recurrence,
vanishing theorem, and sharp theorem used only to reprove them.  The existing
lower-degree caller resolves to the new public result unchanged; the sharp
caller supplies slope `1`.  `FabiusUniformSpline` adds a direct
`FabiusFunction.ThueMorsePrefix` import while retaining its independently used
`DyadicClosedForm` import.  All old public headers and attributes remain exact.

The claim deliberately excludes the unrelated private `self_le_two_pow` and
`succ_le_two_pow` cleanup in `ThueMorsePrefix`, any unified real conditional
wrapper, canonical prose, facade changes, and downstream refactors beyond the
two existing spline call sites.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: fc63c39788ab4c31694e4f57efe05b543165675a
HEAD and dirty paths: b97519c60; clean before this registry-only claim
writing (exact paths): Lean/FabiusFunction/ThueMorsePrefix.lean;
  Lean/FabiusFunction/FabiusUniformSpline.lean; this branch registry for
  claim/handoff only
expected declarations or document claims: add exactly the two public real
  affine Prouhet theorems above; delete exactly the six redundant private
  declarations downstream; adapt the two existing call sites; update source
  module/declaration prose; preserve all old public headers/attributes
completed commits: all prior source checkpoints and handoffs are clean and
  pushed; this is a disjoint registry-first atomic two-file claim
validated (exact command, SHA/state, exit code): current HEAD and origin/main
  share ThueMorsePrefix blob 88f361d5a724bd08022754308d1d7a962de837f8,
  content SHA-256
  C6B4747FD53DD338B83C5303CC7700743CFAC6E35D466C72B5FA70E52E2322BC,
  and FabiusUniformSpline blob
  fcdd15a3af176d7ff641231e314d58dd89d3db96, content SHA-256
  84FA8B2D6B21131099B5FAB1329EA1861DDAED8351661C455A2A982ECE5940F2;
  scans of 54 visible local/remote refs and every registry find the proposed
  names only as the intended private duplicates and find no public competitor
  or active path/name lease; the historical Prefix lease is explicitly
  released; an independent proof/API audit verifies the formulas, edge cases,
  import graph, callers, and deletion boundary; this is not compiler evidence
not yet validated: public declarations, deduplication, call-site updates, and
  prose are not implemented; no Lean, Lake, TeX, PDF, or cache-mutating process
  is authorized or running for this branch
requested integration or lease: advertise this ordinary atomic two-source
  claim; after an immutable independently reviewed checkpoint, request
  sequential LAKE_JOBS=1 builds of +FabiusFunction.ThueMorsePrefix,
  +FabiusFunction.FabiusUniformSpline, and direct consumers
  +FabiusFunction.FabiusComplexShiftSpline and
  +FabiusFunction.FabiusComputability; request no document or main-write lease
conflicts / dependencies: the Prefix import graph is acyclic and UniformSpline
  already receives it transitively; public promotion and private deletion must
  land atomically to avoid local-name shadowing; all frozen local paths and
  active external claims are disjoint; only the coordinator may advance main
next bounded step: commit and push this registry-only claim without force;
  repeat collision checks, then edit only the two claimed sources while three
  agents independently audit generalized-slope algebra, exact-cast bridges,
  private-stack deletion, imports, call sites, old interfaces, docs, and edge
  cases
```

## Source checkpoint: real affine Prouhet API and spline deduplication

Exact source commit `15c8fbf4f` completes the atomic two-file tranche.  Its
result objects are:

- `ThueMorsePrefix.lean`: Git blob
  `265c7986be9f37dbec0fbbb3504ae305e6b1f537`, content SHA-256
  `624DA63CA30A05297D14E087054409DEF1E10E3C4482A5D19C2C7531549C8932`;
- `FabiusUniformSpline.lean`: Git blob
  `6b3ec4c427e614fca70c99f4241f8cced504aad6`, content SHA-256
  `2498A4BB66C9DB1B2666EDC13A61E45649FAECBFAC4A175AA242B063E377361C`.

`ThueMorsePrefix` now exposes exactly the documented public real theorems
`thueMorse_affine_power_sum_eq_zero_real` and
`thueMorse_affine_power_sum_self_real`.  The first annihilates every affine
power below the block exponent.  The second extracts the sharp real boundary
value with the exact `y ^ r` slope factor.  Its coefficient-zero and positive
tail binomial terms are separated explicitly; the surviving signed power sum
is transported from the established rational result.  The proof includes
`r = 0`, zero slope, and arbitrary negative translations and slopes without a
division or nonzero hypothesis.

`FabiusUniformSpline` retains every old import and adds the direct Prefix import,
deletes exactly the six claimed private declarations, and changes only the two
existing Prouhet call sites.  The lower-degree call resolves to the new public
theorem unchanged; the sharp call supplies slope `1` and simplifies the
result.  Net source effect is 111 insertions and 130 deletions.  No two-power
cleanup, unified wrapper, facade, canonical prose, or unrelated declaration
was touched.

Three independent exact-current-byte hostile reviews pass.  They checked the
`add_pow` indexing, `Finset.sum_eq_single` branches, `y ^ r` factorization,
rational-to-real exact casts, signs and factorial normalization, all edge
cases, exact deletion boundary, import acyclicity, name resolution, both
callers, docs, and byte-preservation of every old public header and attribute.
No source-level blocker remains.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: fc63c39788ab4c31694e4f57efe05b543165675a
HEAD and dirty paths: 15c8fbf4f; source checkpoint is clean and pushed; only
  this registry is dirty for the immutable handoff
writing (exact paths): completed source checkpoint writes only
  Lean/FabiusFunction/ThueMorsePrefix.lean and
  Lean/FabiusFunction/FabiusUniformSpline.lean; this report writes only this
  branch registry; both Lean sources are now frozen
expected declarations or document claims: exactly two public real affine
  Prouhet theorems are present with formula-bearing docs; exactly six private
  duplicates are absent; two existing spline callers use the shared API; every
  old public header/attribute and unrelated source declaration is exact
completed commits: ab31862b7 (registry-first claim) and 15c8fbf4f (atomic
  two-file theorem/dedup/documentation checkpoint); earlier pending source
  tranches remain separately frozen and requested for coordinator validation
validated (exact command, SHA/state, exit code): git diff --check exited 0;
  whitespace, CR, tab, placeholder, exact-name, private-declaration, import,
  declaration-header, sum-index, cast, algebra, edge-case, caller, consumer,
  and documentation scans are clean; exact result blobs/hashes are recorded
  above; three independent exact-byte static reviews pass; this is not compiler
  evidence
not yet validated: source commit 15c8fbf4f has not been elaborated; no Lean,
  Lake, TeX, PDF, or cache-mutating process ran because this branch has no host
  build token
requested integration or lease: independently review and preserve exact source
  commit 15c8fbf4f / blobs 265c7986b and 6b3ec4c42, then assign sequential
  LAKE_JOBS=1 builds of +FabiusFunction.ThueMorsePrefix,
  +FabiusFunction.FabiusUniformSpline, and direct consumers
  +FabiusFunction.FabiusComplexShiftSpline and
  +FabiusFunction.FabiusComputability; request no document or main-write lease
conflicts / dependencies: exact preimages are the current-main blobs recorded
  in the claim; the new direct import is acyclic; public promotion and private
  deletion are atomic in the checkpoint; all frozen local paths and active
  external claims are disjoint; only the coordinator may advance main
next bounded step: commit and push this immutable handoff; freeze both sources
  for coordinator validation; refresh main and reread the full ownership board
  before choosing another ordinary source unit
```

## Synchronization after coordinator checkpoint 948bf3f37

Clean merge commit `9741ac546` incorporates fetched `origin/main`
`948bf3f377472c068f9539e0569d383ddc35f617` after a complete reread of the
1,814-line ownership board.  The merge was automatic and conflict-free.  Its
only source overlap was `FabiusWikipediaObstruction.lean`: the merged result
retains main's newly compiled generic periodic cluster-point engine and this
branch's disjoint simultaneous-vanishing error theorem and Big-O wrapper
refactor.

The coordinator has selectively integrated and compiled the earlier
constant-three binary-reduction checkpoint as main commit `942fd6b68`; that
path is therefore released and no longer appears in this branch's net source
delta.  Main also brought the unrelated inverse-asymptotic stack, exact Lambert
cluster interval, and dead-private-helper deletion; all are preserved without
feature-side edits.

Relative to the merged main, this branch now has exactly eleven frozen Lean
source paths plus this own registry: the alternating/convex Laplace checkpoint,
formal Lambert fixed point and remainder deduplication, generic even-subsequence
summation and Legendre deduplication, negative-Laplace normal-form promotion,
Proposition 22 comments, simultaneous-vanishing Wikipedia obstruction, and
real affine Prouhet/spline deduplication.  No build or document process ran;
all remain immutable pending the validation requests in their individual
handoffs.  Canonical documents, build lanes, and main writes remain unclaimed.

## Claim: generic iterated-`divX` exactness and functoriality

Claimed exact source paths:

- `Lean/FabiusFunction/SaddleExpansionFiniteRemainder.lean`;
- `Lean/FabiusFunction/FabiusSaddleReferenceWeight.lean`.

After clean merge `e358c68c3` of current main `1eadfd565`, this ordinary
two-file tranche promotes and centralizes three pure polynomial facts in
namespace `Fabius.SaddleExpansion`:

```lean
theorem X_pow_mul_iterate_divX_eq_of_coeff_zero
    {S : Type*} [CommRing S] (p : Polynomial S) (L : ℕ)
    (hzero : ∀ k < L, p.coeff k = 0) :
    Polynomial.X ^ L * (Polynomial.divX^[L]) p = p

theorem map_divX
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (p : Polynomial A) :
    p.divX.map f = (p.map f).divX

theorem map_iterate_divX
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (L : ℕ) (p : Polynomial A) :
    ((Polynomial.divX^[L]) p).map f =
      (Polynomial.divX^[L]) (p.map f)
```

The first is the existing private exact-division theorem with an explicit
coefficient-ring binder, so its public interface carries no accidental ambient
`Algebra ℚ` dependency.  The other two move the definitionally identical
private naturality proofs from `FabiusSaddleReferenceWeight` to the upstream
finite-remainder module.  All three existing bodies are retained in substance.

The downstream private `map_divX` and `map_iterate_divX` blocks are deleted
atomically; `map_finiteExpSubstitutionQuotient` remains private and rewrites
through the new public iterated theorem.  Every old public header/attribute and
every import remains exact.  No simp attribute, semiring-level strengthening,
facade/root edit, canonical document, or unrelated finite-remainder abstraction
is claimed.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: 1eadfd565db2e4c49310dbaa68c7b4648cb563b8
HEAD and dirty paths: e358c68c3; clean before this registry-only claim; this
  merge also incorporates coordinator validation of the alternating-sign and
  strict-convex Laplace checkpoint, reducing the prior frozen source delta to
  ten paths
writing (exact paths): Lean/FabiusFunction/SaddleExpansionFiniteRemainder.lean;
  Lean/FabiusFunction/FabiusSaddleReferenceWeight.lean; this branch registry
  for claim/handoff only
expected declarations or document claims: expose exactly the three generic
  polynomial theorems above with formula-bearing comments; delete exactly the
  two downstream private naturality copies; preserve every old public header,
  attribute, import, and consumer
completed commits: all earlier source checkpoints and handoffs are clean and
  pushed; merge e358c68c3 is clean and pushed; this is a disjoint
  registry-first atomic two-file claim
validated (exact command, SHA/state, exit code): current HEAD and origin/main
  share SaddleExpansionFiniteRemainder blob
  65b54f647f520dee1c6853e153d9daa880945887, content SHA-256
  0ED5A1C77BEFCFE1568BB88513F14FB9752897C426642EE20F3ECFAE88D9F820,
  and FabiusSaddleReferenceWeight blob
  bfbef07dbb8e77d34d7cf42fa3db1b477f512904, content SHA-256
  38E255FACEE337B41E697536B78011921347B290D11B94BBE47E4DBC27D1D3C9;
  54-ref exact-name/semantic and every-registry scans find only the three
  intended private declarations and no public competitor or active lease;
  historical ReferenceWeight ownership is integrated and released; all proof
  bodies and import/API shapes have independent static review; this is not
  compiler evidence
not yet validated: promotion, relocation, deletion, and prose are not
  implemented; no Lean, Lake, TeX, PDF, or cache-mutating process is authorized
  or running for this branch
requested integration or lease: advertise this ordinary atomic two-source
  claim; after an immutable independently reviewed checkpoint, request
  sequential LAKE_JOBS=1 builds of
  +FabiusFunction.SaddleExpansionFiniteRemainder,
  +FabiusFunction.FabiusSaddleReferenceWeight, and common direct consumer
  +FabiusFunction.FabiusSaddleCentralAllOrders; request no document or
  main-write lease
conflicts / dependencies: ReferenceWeight already directly imports the
  upstream module and opens its namespace; explicit theorem binders prevent an
  accidental ambient algebra dependency; public promotion and private deletion
  must land atomically; all frozen local paths, the sole primary-document owner,
  and active external claims are disjoint; only the coordinator may advance
  main
next bounded step: commit and push this registry-only claim without force;
  repeat collision checks, then edit only the two claimed sources while three
  agents independently verify exact proof preservation, coefficient indexing,
  iterate/map orientation, ambient assumptions, deletion boundary, consumers,
  imports, interfaces, and docs
```

## Handoff: generic iterated-`divX` exactness and functoriality

Source checkpoint `fc52866e4c81da87b8ab4b5868b7ecd8bef8869a` implements the
complete claimed tranche and is pushed to
`origin/codex/fabius-effective-bounds-20260825`.

In `SaddleExpansionFiniteRemainder.lean`, the private reconstruction fact is
now the public, coefficient-ring-generic theorem
`X_pow_mul_iterate_divX_eq_of_coeff_zero`; the new public theorems `map_divX`
and `map_iterate_divX` state coefficient-map naturality for one and every
finite number of divisions by `X`.  All three declarations have explicit
`CommRing` binders, formula-bearing comments, and no attributes.  Their proof
bodies are the previously established private proofs in substance.

In `FabiusSaddleReferenceWeight.lean`, exactly the two private naturality
copies were deleted.  The surviving private quotient-map theorem now rewrites
explicitly through `SaddleExpansion.map_iterate_divX`.  Every pre-existing
public declaration header and attribute, and every import in both modules,
is byte-preserved.

Exact frozen source artifacts:

- `SaddleExpansionFiniteRemainder.lean`: Git blob
  `91174cc0a22f8e46740b6090b59ad632ca8b7a2d`, content SHA-256
  `8376DCDDCE84EC1B36EBE1F44D79906EC172E40ED7D2658FFFE9A922ABF7A849`;
- `FabiusSaddleReferenceWeight.lean`: Git blob
  `b650c2cb86a31eebc1d9701ac2d726892b4ed6bb`, content SHA-256
  `F6473562DED477EB89193720A96587460563D98DAFA63CE7F50CEBEFB5CDAE7F`.

Three independent exact-current-byte static reviews are green.  They checked
the explicit section-independent interfaces, the `L = 0` case, successor
coefficient shift, multiplication order, ring-map orientation, iteration
orientation, atomic duplicate deletion, qualified downstream name resolution,
import and old-header preservation, documentation, and whitespace.  Local
`git diff --check` and the staged diff check both passed.  No Lean, Lake, TeX,
PDF, cache-mutating process, canonical-document edit, or main write ran.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: 1eadfd565db2e4c49310dbaa68c7b4648cb563b8
HEAD and dirty paths: fc52866e4c81da87b8ab4b5868b7ecd8bef8869a;
  clean after exact-path source commit; checkpoint pushed
writing (exact paths): this branch registry for immutable handoff only; the
  two source paths above are frozen at the stated blobs
expected declarations or document claims: exactly the three public generic
  divX theorems recorded above; no attributes and no facade or canonical-doc
  surface
completed commits: registry-first claim 1d2409e3d; source checkpoint
  fc52866e4; both pushed without force
validated (exact command, SHA/state, exit code): git diff --check and staged
  diff check at the exact frozen bytes exited 0; three independent static
  reviews are green; exact blob/SHA evidence is recorded above
not yet validated: no Lean/Lake target or downstream importer was built on
  this branch; static review is not compiler evidence
requested integration or lease: request serialized LAKE_JOBS=1 builds of
  +FabiusFunction.SaddleExpansionFiniteRemainder,
  +FabiusFunction.FabiusSaddleReferenceWeight, and common direct consumer
  +FabiusFunction.FabiusSaddleCentralAllOrders; request coordinator review
  and selective integration after green gates; request no main-write or
  document lease
conflicts / dependencies: ReferenceWeight already imports the upstream
  finite-remainder module; all local frozen paths, current external claims,
  and the sole primary-document owner are disjoint; only the coordinator may
  advance main
next bounded step: freeze both source blobs, push this handoff, fetch main,
  reread any ownership-board delta, and advertise the disjoint generic
  vector-valued dyadic set-integral tranche before editing it
```

## Claim: vector-valued dyadic set-integral reassembly

Claimed exact source paths:

- `Lean/FabiusFunction/PeriodicMean.lean`;
- `Lean/FabiusFunction/PeriodicFourier.lean`.

This ordinary two-file tranche extracts the countable-additivity argument for
the dyadic partitions from five existing real- and complex-valued special
cases.  It adds exactly three documented public theorems in namespace
`Fabius`:

```lean
theorem hasSum_setIntegral_smallDyadicInterval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : IntegrableOn f (Ioc (0 : ℝ) 1)) :
    HasSum (fun n : ℕ => ∫ x : ℝ in smallDyadicInterval n, f x)
      (∫ x : ℝ in Ioc (0 : ℝ) 1, f x)

theorem hasSum_setIntegral_largeDyadicInterval_Ici
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : IntegrableOn f (Ici (1 : ℝ))) :
    HasSum (fun n : ℕ => ∫ x : ℝ in largeDyadicInterval n, f x)
      (∫ x : ℝ in Ici (1 : ℝ), f x)

theorem hasSum_setIntegral_largeDyadicInterval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : IntegrableOn f (Ioi (1 : ℝ))) :
    HasSum
      (fun n : ℕ => ∫ x : ℝ in Ioc ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1)), f x)
      (∫ x : ℝ in Ioi (1 : ℝ), f x)
```

The first two are the exact `Ioc` and `Ico`/`Ici` partition statements.  The
third isolates all null-endpoint normalization in one reusable corollary.
Mathlib's `hasSum_integral_iUnion` requires only the displayed normed additive
group and real normed-space assumptions; no completeness hypothesis is added.

The exact headers, attributes, and formula comments of the existing
`hasSum_integral_smallDyadicInterval`,
`hasSum_integral_largeDyadicInterval_Ici`,
`hasSum_integral_largeDyadicInterval`,
`hasSum_integral_smallDyadicInterval_fourier`, and
`hasSum_integral_largeDyadicInterval_fourier` declarations are preserved.
Only their proof bodies become applications of the generic API.  The
`PeriodicMean` overview will identify the vector-valued scope.  No import,
consumer, root/facade, canonical document, specialized integrability lemma, or
unrelated periodic analysis is claimed.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: 1eadfd565db2e4c49310dbaa68c7b4648cb563b8
HEAD and dirty paths: 88b44f394d7100f5a97f1afbe9b8b6833b9173c4;
  clean before this registry-only claim; the preceding divX checkpoint and
  immutable handoff are pushed
writing (exact paths): Lean/FabiusFunction/PeriodicMean.lean;
  Lean/FabiusFunction/PeriodicFourier.lean; this branch registry for
  claim/handoff only
expected declarations or document claims: exactly the three generic HasSum
  declarations above with formula-bearing source comments and the one module
  overview expansion; refactor only the five named specialized proof bodies;
  preserve every old header, attribute, import, and consumer
completed commits: all earlier checkpoints and handoffs are clean and pushed;
  this is a disjoint registry-first atomic two-file claim
validated (exact command, SHA/state, exit code): current HEAD and origin/main
  share PeriodicMean blob ca0b5e14ebe69b80f047afc92b08736de40a8aaa,
  content SHA-256
  18499B7EAE5ACA8C6F052EAEDD57BC8A8B6F1DF3DAF49636A8C247025F1A8EEC,
  and PeriodicFourier blob 957d2bb93f344892242acef9f8bf24acd874688d,
  content SHA-256
  2D4731C547FBE3CAE061EBC82EF7E558DC19144DB13D204C17C0076983E93DE3;
  all-visible-ref exact-name and every-registry path/name scans are clear;
  the ownership board has only historical PeriodicMean build records and no
  active claim; exact Mathlib hypotheses and all five wrapper routes have
  independent read-only preflight; this is not compiler evidence
not yet validated: the generic declarations, wrapper contractions, and prose
  are not implemented; no Lean, Lake, TeX, PDF, or cache-mutating process is
  authorized or running on this branch
requested integration or lease: advertise this ordinary atomic two-source
  claim; after an immutable independently reviewed checkpoint, request
  serialized LAKE_JOBS=1 builds of +FabiusFunction.PeriodicMean and
  +FabiusFunction.PeriodicFourier, with optional downstream smoke gates
  +FabiusFunction.FabiusSharpConstant and
  +FabiusFunction.FabiusSharpAsymptotic; request no main-write or document
  lease
conflicts / dependencies: PeriodicFourier already reaches PeriodicMean through
  PeriodicRegularity; the one-way import cone is acyclic; all local frozen
  paths, external claims, and the sole primary-document owner are disjoint;
  only the coordinator may advance main
next bounded step: commit and push this registry-only claim without force;
  repeat the collision scan, then edit only the two claimed sources while the
  other agents independently audit typeclass minimality, endpoint orientation,
  wrapper/header preservation, import topology, docs, and exact current bytes
```

## Handoff: vector-valued dyadic set-integral reassembly

Source checkpoint `57f9f185bf4a070caaccdb94fdc21eb643ce3d52` implements the
complete claimed tranche and is pushed to
`origin/codex/fabius-effective-bounds-20260825`.

`PeriodicMean.lean` now exposes exactly three generic theorems:
`hasSum_setIntegral_smallDyadicInterval`,
`hasSum_setIntegral_largeDyadicInterval_Ici`, and
`hasSum_setIntegral_largeDyadicInterval`.  They reassemble Bochner integrals
with values in an arbitrary `E` carrying only `NormedAddCommGroup E` and
`NormedSpace ℝ E`.  The exact small `Ioc` and large `Ico`/`Ici` partitions use
`hasSum_integral_iUnion`; the third theorem contains all almost-everywhere
endpoint conversion to the ergonomic `Ioc`/`Ioi` form.  The comments state the
precise `IntegrableOn` domains and make no absolute-convergence claim.

The bodies of the three pre-existing real-kernel declarations and the two
pre-existing complex Fourier declarations are now thin applications of the
generic API.  All five old headers, attributes, formula comments, consumer
names, and every import are byte-preserved.  `PeriodicFourier` continues to
obtain the API through its existing `PeriodicRegularity -> PeriodicMean`
import path.  Only the requested `PeriodicMean` dyadic overview bullet changed.

Exact frozen source artifacts:

- `PeriodicMean.lean`: Git blob
  `9a0e290cbd999cd9a3aa3ff92fc23acd2ac8ffdc`, content SHA-256
  `C86816F5DFBE22C4788EAB347C31CE43F6644D9CD5EF5ACD1635CC53EE1DD9BD`;
- `PeriodicFourier.lean`: Git blob
  `21bb543f682d0beb48bf6ea2fc69bc9b9f94c873`, content SHA-256
  `79C6DA04FE4BA5C147E7AA8D0DC4927C19344E20FE3E7D7DA48C6950764C092A`.

Three independent exact-current-byte static reviews are green.  They checked
the pinned Mathlib typeclasses, both union identities, block measurability and
pairwise disjointness, every almost-everywhere equivalence orientation, the
`n = 0` endpoint ownership, all five wrapper unifications, old-header/import
preservation, import acyclicity, consumers, docs, and whitespace.  A prose
review tightened two `IntegrableOn` domain qualifiers before the final hashes;
two reviewers verified that this was the only post-review byte change.  Local
and staged `git diff --check` passed.  No Lean, Lake, TeX, PDF, cache-mutating
process, canonical-document edit, or main write ran.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: 1eadfd565db2e4c49310dbaa68c7b4648cb563b8
HEAD and dirty paths: 57f9f185bf4a070caaccdb94fdc21eb643ce3d52;
  clean after exact-path source commit; checkpoint pushed
writing (exact paths): this branch registry for immutable handoff only; the
  two source paths above are frozen at the stated blobs
expected declarations or document claims: exactly the three public generic
  dyadic HasSum theorems and wrapper/body/doc scope recorded above; no facade,
  import, or canonical-doc surface
completed commits: registry-first claim 0756b03c1; source checkpoint
  57f9f185b; both pushed without force
validated (exact command, SHA/state, exit code): local and staged git diff
  --check exited 0; three independent exact-current-byte static reviews are
  green; exact blob/SHA evidence is recorded above
not yet validated: no Lean/Lake target or downstream importer was built on
  this branch; static review is not compiler evidence
requested integration or lease: request serialized LAKE_JOBS=1 builds of
  +FabiusFunction.PeriodicMean and +FabiusFunction.PeriodicFourier; after
  those pass, optionally smoke +FabiusFunction.FabiusSharpConstant and
  +FabiusFunction.FabiusSharpAsymptotic; request coordinator review and
  selective integration; request no main-write or document lease
conflicts / dependencies: the generic API lives upstream of every wrapper;
  the import cone is already one-way and acyclic; all local frozen paths,
  external claims, and the sole primary-document owner are disjoint; only the
  coordinator may advance main
next bounded step: freeze both source blobs, push this handoff, fetch main,
  reread any ownership-board delta, and reserve the next disjoint low-risk
  generalization before editing it
```

## Claim: reflected endpoint-filter map promotion

Claimed exact source paths:

- `Lean/FabiusFunction/FabiusInverse.lean`;
- `Lean/FabiusFunction/FabiusInverseAsymptotic.lean`.

This small atomic tranche promotes the already-established upstream endpoint
reflection fact and removes its independent downstream reproof:

```lean
theorem tendsto_one_sub_nhdsLT_one_nhdsGT_zero :
    Tendsto (fun y : ℝ => 1 - y)
      (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ))
```

The proof in `FabiusInverse.lean` remains token-for-token in substance; only
its visibility and source documentation change.  Its comment and the inverse
module's right-endpoint overview will state the human formula
`1 - y → 0⁺` as `y → 1⁻`.  The definitionally identical private theorem in
`FabiusInverseAsymptotic.lean` is deleted atomically, and its existing sharp
right-endpoint consumer resolves through the already-direct import of
`FabiusInverse`.  Every old public header/attribute, every import, and every
consumer body otherwise remains exact.

An arbitrary-center affine-filter API and promotion of unrelated inverse
filter helpers are deliberately excluded: they neither remove another copy
nor preserve the zero-risk character of this visibility/deduplication unit.
No facade, canonical document, inverse-asymptotic formula, or diagonal theorem
is claimed.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: 1eadfd565db2e4c49310dbaa68c7b4648cb563b8
HEAD and dirty paths: 12216ae78d2cb0c1d2c36d01cb393a71c2ad98f7;
  clean before this registry-only claim; the dyadic API checkpoint and
  immutable handoff are pushed
writing (exact paths): Lean/FabiusFunction/FabiusInverse.lean;
  Lean/FabiusFunction/FabiusInverseAsymptotic.lean; this branch registry for
  claim/handoff only
expected declarations or document claims: promote exactly the one theorem
  above with the same signature/proof and exact endpoint-limit prose; delete
  exactly the downstream private duplicate; preserve every old public header,
  attribute, import, and consumer
completed commits: all earlier checkpoints and handoffs are clean and pushed;
  this is a disjoint registry-first atomic two-file claim
validated (exact command, SHA/state, exit code): current HEAD and origin/main
  share FabiusInverse blob fac45bf09d9e3b44ceebfeca01f4b396f9500805,
  content SHA-256
  04135170740A10BF1A6EAE7F84A452F3E739A6DB08E3210E0A4D250660CBF604,
  and FabiusInverseAsymptotic blob
  756e7a50ab5c43993be63e6f2bd41efe3c537029, content SHA-256
  9C3E2117F2D17F650FE51C0F79082908DC9101D2FDF9FDB49A63068267AC4C36;
  all-visible-ref scans find this exact name only in the two intended private
  declarations and their consumers; registry scans find no competing claim;
  the ownership board explicitly releases both inverse paths after their
  serialized builds; this is not new compiler evidence
not yet validated: the visibility/doc change and downstream deletion are not
  implemented; no Lean, Lake, TeX, PDF, or cache-mutating process is
  authorized or running on this branch
requested integration or lease: advertise this ordinary atomic two-source
  claim; after an immutable independently reviewed checkpoint, request
  serialized LAKE_JOBS=1 builds of +FabiusFunction.FabiusInverse and
  +FabiusFunction.FabiusInverseAsymptotic, with optional direct aggregate
  +FabiusFunction.PaperFabiusAsymptotic; request no main-write or document
  lease
conflicts / dependencies: FabiusInverseAsymptotic already directly imports
  FabiusInverse; the dependency is one-way and acyclic; both source paths were
  released after main's compiled inverse-diagonal update; all local frozen
  paths, external claims, and the sole primary-document owner are disjoint;
  only the coordinator may advance main
next bounded step: commit and push this registry-only claim without force;
  repeat the collision scan, then edit only the two claimed sources while the
  other agents independently verify proof identity, filter orientation,
  deletion boundary, imported name resolution, interfaces, and docs
```

## Handoff: reflected endpoint-filter map promotion

Source checkpoint `fbdc07445a269da7f1236099a2f3d5f6284bf6d9` implements the
complete claimed tranche and is pushed to
`origin/codex/fabius-effective-bounds-20260825`.

`FabiusInverse.lean` now exposes the public theorem
`tendsto_one_sub_nhdsLT_one_nhdsGT_zero`.  Its signature and proof are the
previously established private declaration unchanged in substance; its
formula comment and Main-results bullet state `1 - y → 0⁺` as `y → 1⁻`.
Exactly the independent private copy in `FabiusInverseAsymptotic.lean` was
deleted.  Its reflected sharp-equivalent consumer is byte-unchanged and now
resolves the theorem through the module's existing direct import of
`FabiusInverse`.

Every import, every pre-existing public header/attribute/body, both upstream
consumers, and the downstream consumer remain exact.  No arbitrary-center
affine API or unrelated inverse helper was promoted.

Exact frozen source artifacts:

- `FabiusInverse.lean`: Git blob
  `38774772f11a2c084d3c2e5189d3f632da941154`, content SHA-256
  `0FC4033016CB998D2D8B6A57293EB56C209555BD52C9539E224323FE39B592D9`;
- `FabiusInverseAsymptotic.lean`: Git blob
  `ab7333c2a7f937b2fb5ff19c57173bf08d886f13`, content SHA-256
  `BB60877D8116F865EBC3C836591D4B9C9A9CC15658651A1F06651845E0895903`.

Three independent exact-current-byte static reviews are green.  They checked
the one-sided-filter direction, continuity and positivity components,
byte-identical promoted proof, public namespace placement, exact deletion
boundary, all three unchanged consumers, direct-import resolution, collision
scan, old-interface/import preservation, documentation, and whitespace.
Local and staged `git diff --check` passed.  No Lean, Lake, TeX, PDF,
cache-mutating process, canonical-document edit, or main write ran.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: 1eadfd565db2e4c49310dbaa68c7b4648cb563b8
HEAD and dirty paths: fbdc07445a269da7f1236099a2f3d5f6284bf6d9;
  clean after exact-path source commit; checkpoint pushed
writing (exact paths): this branch registry for immutable handoff only; the
  two source paths above are frozen at the stated blobs
expected declarations or document claims: exactly the one public endpoint
  filter theorem, exact prose, and downstream duplicate deletion recorded
  above; no facade or canonical-doc surface
completed commits: registry-first claim 826c0b194; source checkpoint
  fbdc07445; both pushed without force
validated (exact command, SHA/state, exit code): local and staged git diff
  --check exited 0; three independent exact-current-byte static reviews are
  green; exact blob/SHA evidence is recorded above
not yet validated: no Lean/Lake target or downstream importer was built on
  this branch; static review is not compiler evidence
requested integration or lease: request serialized LAKE_JOBS=1 builds of
  +FabiusFunction.FabiusInverse and
  +FabiusFunction.FabiusInverseAsymptotic; optionally smoke
  +FabiusFunction.PaperFabiusAsymptotic after both pass; request coordinator
  review and selective integration; request no main-write or document lease
conflicts / dependencies: the downstream module already directly imports the
  upstream theorem's module; both paths were released after compiled inverse
  work on main; all local frozen paths, external claims, and the sole primary-
  document owner are disjoint; only the coordinator may advance main
next bounded step: freeze both source blobs, push this handoff, fetch main,
  reread any ownership-board delta, and choose the next disjoint theorem or
  source-documentation parity tranche before editing it
```

## Synchronization note: inverse-hierarchy integration order

Clean merge `18832d3b3923d3f02786a02ae727a95f775eb766` incorporates
`origin/main` `a949e2efaa485283e66a7d2130fc723168c01efa`.  The incoming main
commit changes only the coordinator registry, but its new 01:51 PDT checkpoint
grants active EVO validation to
`codex/fabius-inverse-asymptotic-20260825` for an additive
`FabiusInverseAsymptotic.lean` hierarchy checkpoint.  That branch's accepted
candidate blob is `fd3b5dac6c3f25332c130967ec4914343b7b506a`, which adds the two
elementary-scale hierarchy theorems and supporting private lemmas while
retaining the same private endpoint-filter duplicate deleted by this branch.

Therefore source checkpoint `fbdc07445` remains frozen and mathematically
compatible, but it must not be selected against the older main preimage in a
way that discards the hierarchy candidate.  The safe integration order is:

1. finish and, if green, selectively integrate the hierarchy candidate;
2. retarget or selectively apply this branch's public promotion, two prose
   edits, and exact 15-line downstream duplicate deletion to that resulting
   blob; and
3. run the already-requested inverse and inverse-asymptotic focused gates on
   the combined source.

No source was changed during this synchronization.  The merge and this note
claim no validation token, main write, document path, or authority over the
active inverse branch.  New ordinary source work will stay disjoint from both
inverse paths until the coordinator resolves that ordering.

## Claim: complete source documentation for periodic C⁴ regularity

Claimed exact source path:

- `Lean/FabiusFunction/PeriodicRegularity.lean`.

This one-file, comment-only source-parity tranche supplies adjacent,
formula-and-hypothesis-bearing human-readable documentation for all 41 public
declarations that the repository audit currently reports as undocumented.  It
also expands the module overview with one structured paragraph describing the
public proof chain from dyadic derivative summability through C⁴ regularity to
periodic bounded first and second derivatives.

The exact declaration inventory is:

```text
summable_two_pow_mul_exp_neg_two_pow
summable_forward_derivative_majorant
negativeLaplaceForwardTermFirst
negativeLaplaceForwardTermSecond
negativeLaplaceForwardTermThird
negativeLaplaceForwardTermFourth
negativeLaplaceForwardTerm_hasDerivAt
negativeLaplaceForwardTermFirst_hasDerivAt
negativeLaplaceForwardTermSecond_hasDerivAt
negativeLaplaceForwardTermThird_hasDerivAt
norm_negativeLaplaceForwardTermFirst_le
norm_negativeLaplaceForwardTermSecond_le
norm_negativeLaplaceForwardTermThird_le
norm_negativeLaplaceForwardTermFourth_le
negativeLaplaceForwardTailFirst
negativeLaplaceForwardTailSecond
negativeLaplaceForwardTailThird
negativeLaplaceForwardTailFourth
summable_negativeLaplaceForwardTermFirst
summable_negativeLaplaceForwardTermSecond
summable_negativeLaplaceForwardTermThird
summable_negativeLaplaceForwardTermFourth
negativeLaplaceForwardTail_hasDerivAt
negativeLaplaceForwardTailFirst_hasDerivAt
negativeLaplaceForwardTailSecond_hasDerivAt
negativeLaplaceForwardTailThird_hasDerivAt
continuousOn_negativeLaplaceForwardTermFourth
continuousAt_negativeLaplaceForwardTailFourth
continuousOn_negativeLaplaceForwardTailFourth
contDiff_fabiusLaplaceMoment_nat
contDiff_negativeLaplaceLog_two_rpow
contDiff_negativeLaplaceForwardTail_two_rpow
negativeLaplacePsi_hasDerivAt
contDiff_deriv_negativeLaplacePsi
negativeLaplacePsi_deriv_hasDerivAt
negativeLaplacePsi_deriv_periodic
negativeLaplacePsi_secondDeriv_periodic
continuous_deriv_negativeLaplacePsi
continuous_secondDeriv_negativeLaplacePsi
isBounded_range_deriv_negativeLaplacePsi
isBounded_range_secondDeriv_negativeLaplacePsi
```

Every new comment will state the exact domain, sign, derivative order,
summability or boundedness hypothesis, and displayed formula represented by
its Lean declaration; definitions will identify the corresponding derivative
term or tail.  The comments will not claim absolute convergence where Lean
only states `Summable`, global regularity where the theorem is restricted to a
half-line, or higher smoothness than the proved order.  All existing comments
remain intact.

No Lean token, proof, declaration header, attribute, import, namespace,
consumer, root/facade, canonical document, or audit/control file is claimed.
This directly reduces the stated public-declaration/source-prose gap without
entering the separately serialized TeX/PDF workflow.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: a949e2efaa485283e66a7d2130fc723168c01efa
HEAD and dirty paths: ac02f61d9 plus clean merge 18832d3b3; clean before this
  registry-only claim; all earlier source checkpoints and handoffs are pushed
writing (exact paths): Lean/FabiusFunction/PeriodicRegularity.lean; this
  branch registry for claim/handoff only
expected declarations or document claims: exact adjacent comments for the 41
  names above plus one structured module-overview paragraph; no Lean-token or
  other-source change
completed commits: all earlier checkpoints, synchronization notes, and
  handoffs are clean and pushed; this is a disjoint registry-first one-file
  source-documentation claim
validated (exact command, SHA/state, exit code): current HEAD and origin/main
  share blob 8eb0647ebbcb5d5d7a274332ab16b5e39da96076,
  content SHA-256
  24DC01CE6E4F45F5A64C7EE7D1E0F2F07267A19710CCC50F3A4B5C89BA11795F;
  repository doc_audit reports exactly 41 missing comments in this module;
  independent declaration inventory matches 56 public declarations total,
  15 already documented, and exactly the 41 names above undocumented;
  all-visible-ref and registry/path scans find no parity implementation or
  active claim; the board records the historical path lease as compiled and
  released; this is not compiler evidence
not yet validated: comment wording, attachment, exact mathematical parity,
  and comment syntax are not implemented; no Lean, Lake, TeX, PDF, or cache-
  mutating process is authorized or running on this branch
requested integration or lease: advertise this ordinary one-source comment-
  only claim; after an immutable independently reviewed checkpoint, request
  one serialized LAKE_JOBS=1 build of +FabiusFunction.PeriodicRegularity and
  optional direct-import smoke target +FabiusFunction.PeriodicSmooth; request
  no main-write or document lease
conflicts / dependencies: this file is disjoint from the active Wikipedia and
  inverse validation targets and from every frozen local source blob; no
  canonical document is touched; only the coordinator may advance main
next bounded step: commit and push this registry-only claim without force;
  repeat the path/name audit, then edit comments only while three agents
  independently verify every attached declaration, formula, hypothesis,
  domain, sign, derivative order, and overclaim boundary
```

## Handoff: complete source documentation for periodic C⁴ regularity

Source checkpoint `e82b55cef1c8dcf581fce41a2cd420c0ba920be6` implements the
complete claimed tranche and is pushed to
`origin/codex/fabius-effective-bounds-20260825`.

`PeriodicRegularity.lean` now has adjacent, formula-and-hypothesis-bearing
comments for all 56 public declarations: the 15 existing comments remain
exact, and the 41 names in the claim are newly documented.  The module guide
now explains the four public layers from superexponential majorants through
explicit derivative terms and uniform bounds, termwise tail differentiation,
and the resulting C⁴/periodic/continuous/bounded-jet API.

The comments record the exact alternating derivative signs, Eulerian
numerators, denominator powers, majorant constants `1, 1, 2, 6`, positive-
scale and half-line hypotheses, tail derivative indices, `C^n`, `C⁴`, and
`C³` orders, period-one statements, and qualitative bounded-range conclusions.
They distinguish totalized definitions from the positive-scale theorems and
do not claim sharpness, analyticity, a least period, or an explicit bound
where Lean proves none.

Exact frozen source artifact:

- `PeriodicRegularity.lean`: Git blob
  `394e2ba61edb76f65c44e90fd722c6f448b56253`, content SHA-256
  `4C961CC50C7312C77CF156449BF57ED9944C431939F69BD29D9A90993A695CD7`.

The exact diff is 120 inserted comment lines and zero deleted baseline lines.
A lexical comparison proves the entire non-comment Lean token stream is
identical to baseline blob `8eb0647ebbcb5d5d7a274332ab16b5e39da96076`.
The official repository audit reports `module_header=True`, 56 public
declarations, and zero missing comments for this file; the corpus-wide missing
count falls by 41.  Three independent exact-current-byte semantic reviews are
green across all formulas, hypotheses, constants, signs, domains, regularity
orders, attachments, overclaim boundaries, imports, headers, and whitespace.
Local and staged `git diff --check` passed.  No Lean, Lake, TeX, PDF, cache-
mutating process, canonical-document edit, or main write ran.

The private proof helper `forward_denominator_le` remains outside the explicit
public-declaration checkpoint; it is recorded as future private-helper prose
debt rather than silently included after the registry-first claim.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: a949e2efaa485283e66a7d2130fc723168c01efa
HEAD and dirty paths: e82b55cef1c8dcf581fce41a2cd420c0ba920be6;
  clean after exact-path source commit; checkpoint pushed
writing (exact paths): this branch registry for immutable handoff only; the
  source path above is frozen at the stated blob
expected declarations or document claims: exact public source-prose parity
  for all 56 declarations and module guide recorded above; no Lean-token,
  facade, import, or canonical-doc surface
completed commits: registry-first claim a4f707fde; source checkpoint
  e82b55cef; both pushed without force
validated (exact command, SHA/state, exit code): repository doc_audit now
  reports 56 public / 0 missing for PeriodicRegularity; local and staged git
  diff --check exited 0; lexical non-comment comparison matches the baseline;
  three independent exact-current-byte semantic reviews are green; exact
  blob/SHA evidence is recorded above
not yet validated: no Lean/Lake target or downstream importer was built on
  this branch; comment-only and static review are not compiler evidence
requested integration or lease: request one serialized LAKE_JOBS=1 build of
  +FabiusFunction.PeriodicRegularity and optional direct-import smoke target
  +FabiusFunction.PeriodicSmooth; request coordinator review and selective
  integration; request no main-write or document lease
conflicts / dependencies: this source remains disjoint from the active
  Wikipedia and inverse validation targets and from all other frozen local
  blobs; only the coordinator may advance main
next bounded step: freeze the source blob, push this handoff, fetch main,
  reread any board delta, and choose another disjoint theorem or source-parity
  tranche; do not expand this checkpoint to its private helper retroactively
```

## Claim: complete source documentation for all-orders periodic smoothness

Claimed exact source path:

- `Lean/FabiusFunction/PeriodicSmooth.lean`.

This one-file, comment-only source-parity tranche supplies adjacent,
formula-and-hypothesis-bearing documentation for all 18 public declarations
that currently lack it, plus one short structured module-overview paragraph.
The official `doc_audit.py` reports only 15 because its column-zero scanner
misses three same-line `@[simp] lemma` declarations; strict lexical inventory
and the existing frozen audit finding both identify the complete count as
18 = 15 + 3.

The exact declaration inventory is:

```text
negativeLaplaceForwardTermDeriv_zero
negativeLaplaceForwardTermDeriv_succ
negativeLaplaceForwardTermDeriv_one
negativeLaplaceForwardTermDeriv_hasDerivAt
exists_bound_abs_forwardDerivativeQuotientPolynomial
exists_norm_negativeLaplaceForwardTermDeriv_succ_le
negativeLaplaceForwardTailDeriv_zero
summable_negativeLaplaceForwardTermDeriv
negativeLaplaceForwardTailDeriv_hasDerivAt
contDiffOn_negativeLaplaceForwardTailDeriv_nat
contDiff_infty_fabiusLaplaceMoment
contDiff_infty_negativeLaplaceLog_two_rpow
contDiff_infty_negativeLaplaceForwardTail_two_rpow
contDiff_infty_deriv
periodic_deriv_of_contDiff_infty
negativeLaplaceBoundedExponentJet_periodic
contDiff_infty_negativeLaplaceBoundedExponentJet
isBounded_range_negativeLaplaceBoundedExponentJet
```

The comments will state the exact recursive derivative formula, base cases,
positive-scale derivative and summability hypotheses, compact polynomial
bound on `z ∈ [0,1]`, existential nonnegative half-line majorant depending on
`a` and `k`, finite-order tail smoothness on `(0,∞)`, whole-line C∞ results,
period-one conclusions, and qualitative bounded-range claims.  They will not
claim analyticity, convergence outside positive scale, a sharp or explicit
existential constant, a least period, or an explicit global bound.

All existing comments remain intact.  No Lean token, proof, declaration
header, attribute, import, namespace, consumer, root/facade, canonical
document, audit script, or control-plane file is claimed.  The separate
lexical-auditor blind spot is recorded but not repaired inside this source-
only tranche.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: a949e2efaa485283e66a7d2130fc723168c01efa
HEAD and dirty paths: 1ae0f9716f8a83033b57762c775073c7169e52dc;
  clean before this registry-only claim; the PeriodicRegularity parity
  checkpoint and immutable handoff are pushed
writing (exact paths): Lean/FabiusFunction/PeriodicSmooth.lean; this branch
  registry for claim/handoff only
expected declarations or document claims: exact adjacent comments for the 18
  names above plus one structured module-overview paragraph; no Lean-token or
  other-source change
completed commits: all earlier checkpoints, merges, synchronization notes,
  and handoffs are clean and pushed; this is a disjoint registry-first one-
  file source-documentation claim
validated (exact command, SHA/state, exit code): current HEAD and origin/main
  share blob 2907aa12ef3e3dfbd7094dc5c39de27b559b4ce8,
  content SHA-256
  DAC9E832627970EAE6975B8C9758C19C5BEB178F624DDBC0E38A1C559B8BD563;
  official doc_audit reports 15 gaps while two independent strict declaration
  inventories and the frozen audit finding identify the exact 18-name scope;
  all-visible-ref and registry/path scans find no parity implementation or
  active claim; the board records historical PeriodicSmooth source work as
  compiled and released; this is not compiler evidence
not yet validated: comment wording, attachment, exact mathematical parity,
  and comment syntax are not implemented; no Lean, Lake, TeX, PDF, or cache-
  mutating process is authorized or running on this branch
requested integration or lease: advertise this ordinary one-source comment-
  only claim; after an immutable independently reviewed checkpoint, request
  one serialized LAKE_JOBS=1 build of +FabiusFunction.PeriodicSmooth and an
  optional direct-import smoke target selected by the coordinator; request no
  main-write or document lease
conflicts / dependencies: this file is disjoint from active Wikipedia and
  inverse validation targets and all frozen local source blobs; no canonical
  document or audit script is touched; only the coordinator may advance main
next bounded step: commit and push this registry-only claim without force;
  repeat the path/name audit, then edit comments only while three agents
  independently verify all 18 attachments, formulas, domains, derivative
  indices, smoothness orders, period/boundedness scope, and token preservation
```

## Handoff: complete source documentation for all-orders periodic smoothness

Source checkpoint `32bc6070ee0819f0a465068219ff9893d1bde1d9` implements the
complete claimed tranche and is pushed to
`origin/codex/fabius-effective-bounds-20260825`.

`PeriodicSmooth.lean` now has adjacent, mathematically precise comments for
all 44 public declarations.  The 18 additions include the three same-line
attributed simp lemmas that the current repository audit does not count.
The module guide now summarizes the public all-orders chain from recursively
generated quotient polynomials and termwise derivative majorants to global
C∞ periodic corrections and bounded exponent jets.

The comments record the exact order-zero and order-one bridges, recursive
`a = 2^n`, `z = exp (-(s*a))` quotient formula, positive-scale derivative and
summability hypotheses, compact `[0,1]` polynomial bound, existential
nonnegative half-line majorant, positive-domain tail smoothness, whole-line
C∞ compositions, derivative-period transport, and qualitative bounded-range
claims.  They do not claim analyticity, convergence at nonpositive scale, a
sharp or explicit existential constant, or a least period.

Exact frozen source artifact:

- `PeriodicSmooth.lean`: Git blob
  `f09e73b35accd3d426fea843eb2122ad5b214df9`, content SHA-256
  `2F5CF5589E74D9AF5051C781BC50537E33E0436CEF431B9E669CF8FD1A10388F`.

The exact diff is 54 inserted comment lines and zero deletions.  Strict
attributed-declaration inventory reports 44 public declarations and 44
adjacent comments; the official audit's narrower 35-declaration view also
reports zero missing and no longer lists this module.  Lexical comparison
shows the non-comment Lean code stream is identical to baseline blob
`2907aa12ef3e3dfbd7094dc5c39de27b559b4ce8`.  Independent hostile semantic
review is green across all 18 comments and the module paragraph; author-side
exact-byte and whitespace checks agree.  Local and staged `git diff --check`
passed.  No Lean, Lake, TeX, PDF, cache-mutating process, canonical-document
edit, or main write ran.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: a949e2efaa485283e66a7d2130fc723168c01efa
HEAD and dirty paths: 32bc6070ee0819f0a465068219ff9893d1bde1d9;
  clean after exact-path source commit; checkpoint pushed
writing (exact paths): this branch registry for immutable handoff only; the
  source path above is frozen at the stated blob
expected declarations or document claims: exact source-prose parity for all
  44 public declarations and module guide recorded above; no Lean-token,
  facade, import, audit-script, or canonical-doc surface
completed commits: registry-first claim 1c6114950; source checkpoint
  32bc6070e; both pushed without force
validated (exact command, SHA/state, exit code): strict scan reports 44 public
  / 0 missing; official doc_audit reports no PeriodicSmooth gap; local and
  staged git diff --check exited 0; lexical non-comment comparison matches the
  baseline; independent semantic and author exact-byte reviews are green;
  exact blob/SHA evidence is recorded above
not yet validated: no Lean/Lake target or downstream importer was built on
  this branch; comment-only and static review are not compiler evidence
requested integration or lease: request one serialized LAKE_JOBS=1 build of
  +FabiusFunction.PeriodicSmooth and optional direct-import smoke target
  selected by the coordinator; request coordinator review and selective
  integration; request no main-write or document lease
conflicts / dependencies: this source remains disjoint from active Wikipedia
  and inverse validation targets and all other frozen local blobs; only the
  coordinator may advance main
next bounded step: freeze the source blob, push this handoff, fetch main,
  reread any board delta, and choose another disjoint theorem or source-parity
  tranche; the audit-script blind spot remains a separately serialized tool
  issue rather than an implicit source expansion
```

## Claim: factorized standardized saddle-tail asymptotics and source parity

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: 4789f05b1a1abc34b5753c166a524be1f62078c3
HEAD and dirty paths: 7dbd08b22; clean before this registry-only claim
writing (exact paths):
  Analysis/FabiusFunction/Lean/FabiusFunction/FabiusSaddleTail.lean
  Analysis/FabiusFunction/docs/registry/codex-fabius-effective-bounds-20260825.md
expected declarations or document claims:
  theorem
  integral_norm_fabius_scaledSaddleKernel_standardRadius_isBigO_minorArcConstant_mul_inv
  with the existing standardized complementary-tail function on the left and
  `negativeLaplaceMinorArcConstant (r i) (2 * m i) * (b i)⁻¹` on the right;
  it assumes only eventual `0 < r i`, `16 ≤ b i`, and
  `b i / 4 ≤ (m i : ℝ)`, and therefore exposes the factorized estimate
  `tail = O(C_i / b_i)` before imposing boundedness of `C_i` or
  `b -> atTop`;
  preserve the exact public header of
  integral_norm_fabius_scaledSaddleKernel_standardRadius_isBigO and refactor
  its proof as the new theorem followed by the existing minor-arc `O(1)`
  hypothesis and the inverse-scale reflexive bound;
  add exact formula/hypothesis-bearing comments to all 17 currently
  undocumented public declarations and one module sentence for the new
  factorization, leaving 30 public declarations / 30 adjacent comments /
  zero missing under a strict declaration scan
completed commits: merged origin/main checkpoint 4789f05b1 as 7dbd08b22 and
  pushed it without force; no source commit exists for this claim yet
validated (exact command, SHA/state, exit code): authoritative all-visible-ref
  `git grep` finds no occurrence of the proposed theorem name; current source
  blob is 5f70fc0e17832fc5e5c0412b7c9369c9ee400a6d and content SHA-256 is
  8348337D5056478A8964B19F8919A1A13CF61A5D75880AD8E303EEA1AD8A2999;
  repository doc_audit reports exactly 17 gaps in this module; historical
  generalization registries record the earlier source lease as integrated and
  released; current board assigns no owner or build token for this path
not yet validated: the claim is not implemented; no Lean, Lake, TeX, PDF, or
  cache-mutating process is authorized or running on this branch
requested integration or lease: advertise this ordinary one-source theorem
  and comment-parity claim; after an immutable independently reviewed source
  checkpoint, request one serialized build of +FabiusFunction.FabiusSaddleTail
  and the smallest direct importer selected by the coordinator; request no
  main-write or canonical-document lease
conflicts / dependencies: the path is disjoint from every active board grant
  and every frozen branch-only source artifact; only the coordinator may
  advance main; the old Big-O theorem remains source-compatible
next bounded step: commit and push this registry-only claim without force;
  repeat the all-ref/name/path scan, then author exactly the new factorized
  theorem, statement-preserving wrapper refactor, module sentence, and 17
  declaration comments while independent agents audit proof orientation,
  constants, filter hypotheses, documentation parity, and exact old-header
  preservation
```

## Handoff: factorized standardized saddle-tail asymptotics and source parity

Source checkpoint `bbaed0ee6` implements the complete one-file claim and is
pushed to `origin/codex/fabius-effective-bounds-20260825`.

The new theorem
`integral_norm_fabius_scaledSaddleKernel_standardRadius_isBigO_minorArcConstant_mul_inv`
states the standardized complementary tail as
`O(negativeLaplaceMinorArcConstant (r i) (2 * m i) * (b i)⁻¹)` under only the
eventual hypotheses `0 < r i`, `16 ≤ b i`, and
`b i / 4 ≤ (m i : ℝ)`.  Thus it exposes the pointwise factorization before
the old theorem additionally assumes `b -> atTop` and a bounded minor-arc
constant.  The old public theorem header is byte-identical and its proof is
now the new estimate composed with `C_i = O(1)` and the reflexive inverse-scale
bound.

All 17 previously undocumented public declarations now have adjacent,
formula- and hypothesis-bearing comments.  Together with the new theorem,
the module has 30 public declarations and 30 adjacent comments.  The prose
covers kernel positivity/evenness/integrability, the exact even-tail and
exponential-tail identities, the scaled Cauchy mass, logarithmic and
two-region bounds, standardized-radius estimates, and the natural square
versus power-of-two inequality without claiming sharpness or unnecessary
asymptotic hypotheses.

Exact frozen artifact:

- `FabiusSaddleTail.lean`: Git blob
  `9712b7a684aa82e21bc0f1a3ff5f533d1eba7fc5`, content SHA-256
  `14914AEF8C600B31E01FF86C5D698D432BFDF8699E9EB013899835562CF24E15`.

The exact diff is 109 insertions and 54 deletions.  Deletions are confined to
the duplicated old final proof and a corrected compatibility comment.  A
header extractor reports the sole new declaration, no removed or changed old
header, and byte-identical imports.  Repository and strict documentation
audits report 30 public / zero missing.  Two independent hostile exact-byte
reviews and the author audit agree on the filter orientation, arbitrary-filter
edge cases, factor `2 * m`, nonnegativity rewrites, constant `16 + 32*pi`,
minor-arc product composition, consumer compatibility, and all comment
formulas.  Local and staged `git diff --check` passed.  No Lean, Lake, TeX,
PDF, cache mutation, canonical-document edit, or main write ran.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: 4789f05b1a1abc34b5753c166a524be1f62078c3
HEAD and dirty paths: bbaed0ee6; clean after exact-path source commit;
  checkpoint pushed
writing (exact paths): this branch registry for immutable handoff only; the
  source path above is frozen at the stated blob
expected declarations or document claims: exact theorem and complete source
  parity described above; no import, facade, audit-script, canonical-doc, or
  old public-header change
completed commits: registry-first claim 0105b4a0b; source checkpoint
  bbaed0ee6; both pushed without force
validated (exact command, SHA/state, exit code): all-visible-ref post-claim
  scan found the proposed name only in this branch registry before authoring;
  repository doc_audit and strict inventory report 30 public / zero missing;
  header/import comparison and local/staged git diff --check exited 0; two
  independent hostile exact-byte reviews and author review are green; exact
  blob/SHA evidence is recorded above
not yet validated: no Lean/Lake target or downstream importer was built on
  this branch; static proof/API review is not compiler evidence
requested integration or lease: request serialized
  +FabiusFunction.FabiusSaddleTail followed by the sole direct old-theorem
  consumer +FabiusFunction.FabiusLambertMinorArc; optionally replay
  +FabiusFunction.FabiusSaddleTailAllOrders; request coordinator review and
  selective integration; request no main-write or document lease
conflicts / dependencies: direct importers remain source-compatible; this
  source is frozen and disjoint from every active board grant; only the
  coordinator may advance main
next bounded step: push this registry handoff, fetch and reread main, then
  continue on a separately advertised cold path; retain SaddleExpansionAlgebra
  coefficient-family congruence and Gaussian contraction deduplication as
  audited future candidates rather than broadening this checkpoint
```

## Claim: positive-index exponential-coefficient extensionality

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-effective-bounds-20260825 /
  /home/codex/.codex/worktrees/d6d3/Proofs / codexbox
fetched main SHA: c7dfc250fe42bf66a241b59e1fa11eb5dd340d0f
HEAD and dirty paths: 0515d3c97; clean before this registry-only claim
writing (exact paths):
  Analysis/FabiusFunction/Lean/FabiusFunction/SaddleExpansionAlgebra.lean
  Analysis/FabiusFunction/Lean/FabiusFunction/SaddleLogExpansionAlgebra.lean
  Analysis/FabiusFunction/docs/registry/codex-fabius-effective-bounds-20260825.md
expected declarations or document claims:
  theorem expCoeff_eq_of_forall_pos {E F : ℕ → R}
    (hEF : ∀ j, 0 < j → E j = F j) : expCoeff E = expCoeff F;
  prove it by function extensionality and the existing finite-index theorem
  expCoeff_congr_of_pos, making explicit that the recursive exponential
  transform ignores index zero as a whole family;
  replace only the repeated five-line `funext` proof of `hexp` inside
  logCoeff_expCoeff_of_pos by the new public theorem, preserving its header;
  add exact adjacent formula comments to the 12 undocumented declarations in
  SaddleExpansionAlgebra and one concise module-guide paragraph for the
  existing locality, map, rescaling, convolution, evaluation, parity,
  partial-sum, eventual-equality, pullback, and linear-map APIs; after the new
  theorem, require strict 46 public declarations / 46 comments / zero missing
completed commits: synchronized main c7dfc250f in merge 0515d3c97 and pushed;
  no source commit exists for this claim yet
validated (exact command, SHA/state, exit code): authoritative all-visible-ref
  `git grep` finds no proposed theorem-name occurrence; current source blobs
  are 80018c6b7af028d4bf3cb4656ec56e7373a4bfbc and
  98b1490cd397e8923488be5b57927b8b3a64f242, with content SHA-256 values
  735798D3452714A9660C49AB236CFD837BF06CD7717CF4C497808DD544278088 and
  99B4A70E001FF09259582C7EFCD0FB36EF6643DB785353AA29C1A6978C798612;
  strict audit reports 45 public / 12 undocumented in the algebra module and
  no attributed-declaration blind spot; current registries show only closed
  historical source work and no active path/name claim
not yet validated: the claim is not implemented; no Lean, Lake, TeX, PDF, or
  cache-mutating process is authorized or running on this branch
requested integration or lease: advertise this ordinary two-source algebra
  and comment-parity claim; after immutable independent review request
  serialized +FabiusFunction.SaddleExpansionAlgebra followed by
  +FabiusFunction.SaddleLogExpansionAlgebra and, if the coordinator chooses,
  the broad consumer +FabiusFunction.PaperFabiusAsymptotic; request no
  main-write or canonical-document lease
conflicts / dependencies: both paths are disjoint from active radial/parity/
  arithmetic and inverse-decay build grants and all frozen local source
  artifacts; the algebra module has a broad import cone, so its source blob is
  frozen immediately after authoring; all old headers/imports remain exact;
  only the coordinator may advance main
next bounded step: commit and push this registry-only claim without force;
  repeat all-ref/path/name scans, then author exactly the one theorem, one
  local proof deduplication, 12 declaration comments, and one module paragraph
  while independent agents audit coefficient-zero semantics, attribute/comment
  placement, old-header preservation, imports, and direct consumer behavior
```
