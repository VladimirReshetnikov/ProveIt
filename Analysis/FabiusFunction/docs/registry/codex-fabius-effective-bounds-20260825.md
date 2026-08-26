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
