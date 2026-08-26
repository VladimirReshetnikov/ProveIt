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
