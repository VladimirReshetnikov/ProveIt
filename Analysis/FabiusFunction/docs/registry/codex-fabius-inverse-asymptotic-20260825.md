# Sharp Fabius inverse-asymptotic workstream

This registry advertises a focused formalization of the sharp inverse
asymptotic already derived in the canonical research-frontier document.  The
workstream is intentionally layered: a filter-polymorphic quadratic inversion
theorem first captures the reusable asymptotic algebra, then a Fabius-specific
module applies it to the exact lower-Lambert phase and derives the logarithmic,
left-endpoint, and reflected right-endpoint inverse formulas.

The canonical human-readable source remains authoritative mathematical input,
not an owned output of this tranche.  In particular, this claim does not edit
or render the frozen frontier, primary exposition, walkthrough, coverage map,
or any matching PDF.  A later documentation owner can promote the relevant
statements from `Derived` to `Formalized` only after the Lean source is
compiled, reviewed, and accepted.

## Registry-first claim: quadratic phase inversion and sharp inverse endpoints

The exact human-readable counterparts are:

- `inverse:lem:lambda-from-T`, which states
  `lambda = sqrt (2 T / L) + B / L + O (log T / sqrt T)` for
  `L = log 2` and `B = 1 + L / 2`;
- `inverse:thm:sharp-inverse-asymptotic`, including the logarithmic formula
  and explicit left-endpoint equivalent; and
- `inverse:eq:right-inverse-asymptotic`, obtained from exact inverse
  reflection.

The generic theorem will retain the full documented Big-O rate.  The
Fabius-facing layer will additionally expose the convergence corollary that
the logarithmic proof actually consumes, rather than repeatedly unpacking a
Big-O estimate downstream.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-inverse-asymptotic-20260825 /
  C:/Users/vresh/.codex/worktrees/c9a3/ProveIt / EVO (Windows)
fetched main SHA: 741db6b4b777abc3fb4ca9ba6a6f0f098399c1bb
fetched main tree: 0f7d86deed0157ff52a4056261e9c4c06653b7ea
HEAD and dirty paths: 741db6b4b777abc3fb4ca9ba6a6f0f098399c1bb;
  tracked worktree and index clean before this registry-only edit; preserved
  untracked reciprocity PDF/text sidecars and tmp/ render tree are unrelated
  and will never be staged by this branch
writing (exact paths): this registry initially; only after this claim is
  committed, pushed, and re-audited:
  Lean/FabiusFunction/QuadraticAsymptoticInversion.lean (new),
  Lean/FabiusFunction/FabiusInverseAsymptotic.lean (new),
  Lean/FabiusFunction/PaperFabiusAsymptotic.lean (one import plus accurate
    source-level module prose), and this registry
expected declarations or document claims:
  quadratic_asymptotic_inversion, a filter-polymorphic theorem proving that
    T = L/2 * lambda^2 - B * lambda + O(log lambda), with L > 0 and
    lambda -> +infinity, implies
    lambda = sqrt(2*T/L) + B/L + O(log T/sqrt T); its proof will first derive
    the intrinsic O(log lambda/lambda) estimate by completing the
    square and rationalizing, then transport the error scale through
    T ~ (L/2) * lambda^2;
  fabiusInverseQuadraticPhaseMain, the exact square-root-plus-affine phase
    main term with L = log 2 and B = 1 + L/2;
  fabiusInverseLogAsymptoticMain, the exact three-term logarithmic inverse
    main at zero;
  fabiusInverseAsymptoticMain, the explicit positive inverse equivalent;
  fabiusLambertPhase_fabiusInv_sub_fabiusInverseQuadraticPhaseMain_isBigO,
    the exact Lean counterpart of inverse:lem:lambda-from-T on nhdsGT 0;
  tendsto_fabiusLambertPhase_fabiusInv_sub_fabiusInverseQuadraticPhaseMain,
    the zero-limit consequence consumed by the logarithmic proof;
  tendsto_log_fabiusInv_sub_fabiusInverseLogAsymptoticMain, the exact Lean
    counterpart of inverse:eq:log-sharp-inverse;
  fabiusInv_isEquivalent_fabiusInverseAsymptoticMain, the explicit sharp
    left-endpoint equivalent;
  one_sub_fabiusInv_isEquivalent_fabiusInverseAsymptoticMain_one_sub, the
    reflected sharp right-endpoint equivalent;
  PaperFabiusAsymptotic.lean will import the new endpoint module and update
    only its Lean module documentation to describe the newly formalized
    inverse results; no canonical TeX/PDF claim is made
completed commits: none; this is the first registry-only claim on the fresh
  branch
validated (exact command, SHA/state, exit code): read-only audit only.  The
  branch was created from origin/main 5b053a32b, then fast-forwarded without
  conflict to exact current main 741db6b4b before this claim.  The current
  PaperFabiusAsymptotic.lean preimage is Git blob
  308315947b4ea359edbe7faaa467303dbcd1c4f6; both new Lean modules and this
  registry are absent on main.  Exact-name, plausible-semantic-name,
  exact-path, every-registry, and advertised-tip scans found no implemented
  sharp inverse asymptotic, quadratic inversion engine, competing path claim,
  or colliding declaration.  Latest fetched both-papers and effective-bounds
  tips advertise disjoint TwoAdic and FabiusBinaryReductionSeries work.  This
  is static/collision evidence, not Lean compiler evidence
not yet validated: neither proposed Lean module exists yet; no Lean, Lake,
  TeX, PDF, cache, or other build process has run.  This branch owns no host
  Lean/Lake token and no document lane
requested integration or lease: advertise this ordinary four-path claim.
  After a frozen source checkpoint and independent review, request separate
  serialized LAKE_JOBS=1 builds, in dependency order, of
  +FabiusFunction.QuadraticAsymptoticInversion,
  +FabiusFunction.FabiusInverseAsymptotic, and
  +FabiusFunction.PaperFabiusAsymptotic.  Request no root-aggregate,
  canonical-document, PDF, or main-write lane now
conflicts / dependencies: the existing FabiusInverse.lean,
  FabiusLambertRates.lean, and PeriodicRegularity.lean APIs remain read-only;
  tiny inverse-filter, Lambert-phase, periodic-boundedness, and reflection
  transports will be private to the new endpoint module.  The root aggregate
  Lean/FabiusFunction.lean is serialized and excluded; it already imports
  PaperFabiusAsymptotic.lean, so the import-only facade change exposes both
  new modules transitively.  The theorem-polish branch owns only the primary
  TeX/PDF pair; all other canonical documents remain frozen.  Only the
  coordinator may advance main; this branch will never force
next bounded step: commit and push only this registry claim; fetch and reread
  the coordinator board, repeat the moving-tip collision scan, then implement
  the generic algebra module before the Fabius-specific module, without
  launching an unassigned validation process
```

## Mathematical boundary

The branch will not infer inverse asymptotics merely by composing the existing
forward `IsEquivalent` theorem with `fabiusInv`; asymptotic equivalence is not
automatically invertible.  Instead it will use the exact identity

```text
log x = log (fabiusLambertPhase x) -
  log 2 * fabiusLambertPhase x
```

together with the corrected sharp logarithmic expansion, boundedness of the
periodic correction, and the explicit quadratic inversion theorem.  The
periodic term is retained in the forward formula and disappears from the
leading inverse equivalent only after its bounded contribution is divided by
the diverging phase.

The related scale-hierarchy corollary in the frontier is a natural follow-on,
but it is not silently folded into this initial declaration claim.  Any public
scale-hierarchy expansion will receive its own registry amendment after the
core inverse endpoint API is implemented and stable.

## Generic inversion source checkpoint

The registry-first claim was committed and pushed as `bdbc63461`.  The first
source milestone is now committed and pushed as `9b7affe68`: the new module
`Lean/FabiusFunction/QuadraticAsymptoticInversion.lean` defines exactly the
advertised public theorem `quadratic_asymptotic_inversion`.  Its immutable Git
blob is `c03608742d1f4c023ffc46ee13e3298395b21320`, and the source SHA-256 is
`A3B54BEC9CDA5D190F664B8924FC55FCE5198E084EF55B2C3166110A8735AF94`.

The generic theorem retains the full documented
`O (log T / sqrt T)` conclusion.  Its proof first isolates the leading
equivalence `T ~ (L / 2) * lambda^2`, proves that the observable rate is
Theta-equivalent to the intrinsic `log lambda / lambda` rate, completes the
square, and rationalizes the positive root.  The sign of the affine correction
is `+ B / L`, and the theorem remains filter-polymorphic without an unnecessary
`NeBot` assumption.

Three independent read-only source reviews have completed:

- a hostile mathematical audit rederived the numerator identity, affine sign,
  denominator asymptotic, positivity obligations, and final rate orientation;
- an API/style/collision audit found no duplicate declaration, path collision,
  import blocker, or reason to expose the private structural helpers; and
- a Mathlib elaboration preflight found three congruence-shape hazards in an
  earlier snapshot.  All three were repaired before commit, and the final
  snapshot received a clean static verdict.

This remains source-review evidence, not compiler evidence.  No Lean, Lake,
TeX, PDF, or cache-mutating process has run in this worktree, because this
branch has no host build or document token.  The tracked tree was clean when
the branch merged current coordinator checkpoint `fc63c3978`; the detailed,
conflict-free merge commit `b7edc7ce2` is pushed.  Existing untracked
reciprocity sidecars and the `tmp/` render tree remain untouched.

The claimed endpoint source and paper facade are now frozen, committed, and
pushed.  No further Lean source edit remains in the current tranche.  The next
bounded step is to publish this registry handoff and request the serialized EVO
Lean/Lake token for the exact immutable Lean tree at `d6464f6c8`.  No root
aggregate, canonical-document, TeX, or PDF lane is requested.

## Sharp endpoint and facade source checkpoints

The endpoint specialization is committed and pushed as
`6ee65a167434fa1b76ab724e195e98dab619c6f3`.  It adds only
`Lean/FabiusFunction/FabiusInverseAsymptotic.lean`.  The immutable source is
429 lines and 17,420 bytes, with Git blob
`bf78aedb8cce1f88c0f8409000dbdd27026e455a` and SHA-256
`2920F950A552FC7AD61DA994948DCA92B99B05181AA1EC7E90B816A2273BB07F`.

The module defines the three advertised main terms and proves all five
advertised endpoint results:

- `fabiusInverseQuadraticPhaseMain`;
- `fabiusInverseLogAsymptoticMain`;
- `fabiusInverseAsymptoticMain`;
- `fabiusLambertPhase_fabiusInv_sub_fabiusInverseQuadraticPhaseMain_isBigO`;
- `tendsto_fabiusLambertPhase_fabiusInv_sub_fabiusInverseQuadraticPhaseMain`;
- `tendsto_log_fabiusInv_sub_fabiusInverseLogAsymptoticMain`;
- `fabiusInv_isEquivalent_fabiusInverseAsymptoticMain`; and
- `one_sub_fabiusInv_isEquivalent_fabiusInverseAsymptoticMain_one_sub`.

The quantitative theorem has exactly the advertised
`O(log (-log y) / sqrt (-log y))` error.  The logarithmic theorem retains the
exact constant `-1 - log (log 2) / 2`, the left theorem gives the explicit
positive equivalent, and the right theorem applies that same main term to
`1 - y`, as required by inverse reflection.

Read-only validation of the immutable endpoint blob is static rather than
compiler evidence.  The preservation commit records a clean targeted cached
diff, zero `sorry`, `admit`, `axiom`, or `opaque` declarations, and no line
over 100 characters.  Independent mathematical and API reviews accepted the
formulas, constants, endpoint domains, filters, and dependency route.  A
Mathlib elaboration preflight found four hazards in earlier snapshots: the
namespace of `isLittleO_log_rpow_atTop`, the explicit real codomain of
`isLittleO_one_left_iff`, the congruence depth needed to expose the square-root
radicand, and the simplifier set needed for the scaled zero limit.  All four
are repaired in blob `bf78aedb8`; the final source/API preflight is clean.
The remaining risk is unexecuted elaboration and compiler validation.

After fetching exact `origin/main`
`fc63c39788ab4c31694e4f57efe05b543165675a`, the requested merge was explicitly
attempted again.  It was a no-op because that commit was already an ancestor
through pushed merge `b7edc7ce2`; there were no conflicts, no tree changes, and
no additional merge commit.

The paper-facade wiring is committed and pushed as
`d6464f6c8482bdb4b771e96b224b0ff1d9c7ec9e`.  It changes only
`Lean/FabiusFunction/PaperFabiusAsymptotic.lean`, adding the
`FabiusInverseAsymptotic` import and nine lines of exact claim-level prose.
The resulting facade is 114 lines and 6,833 bytes, with Git blob
`7259480a72391e59f3d303ed586b67c4d199c1fe` and SHA-256
`24254045EB1C3A45FC2911B99FAFA880AE5658FED8B6EE9B05C187ADBAC398A2`.
Its read-only audit found no declaration collision or dependency cycle;
targeted diff, whitespace, line-length, and forbidden-declaration checks are
clean.  The serialized root aggregate remains untouched: its existing import
of `PaperFabiusAsymptotic` now exposes the generic engine and endpoint API
transitively.

The generic source remains unchanged from commit `9b7affe68`, with blob
`c03608742d1f4c023ffc46ee13e3298395b21320` and SHA-256
`A3B54BEC9CDA5D190F664B8924FC55FCE5198E084EF55B2C3166110A8735AF94`.

No Lean, Lake, TeX, PDF, or cache-mutating command has run in this worktree.
The board at `origin/main` assigns codexbox Lean/Lake to the coordinator and
leaves EVO Lean/Lake idle but unassigned; therefore this branch still has no
authority to compile.  Documentation is unassigned and every canonical
document remains frozen.

### Serialized validation request

Assign the EVO Lean/Lake token to this branch for exact source tip
`d6464f6c8482bdb4b771e96b224b0ff1d9c7ec9e`, or have the current build owner
validate that immutable commit in an isolated worktree.  From the repository
root, run exactly these three separate invocations, in dependency order, with
no overlapping Lean/Lake process:

```text
LAKE_JOBS=1 lake build +FabiusFunction.QuadraticAsymptoticInversion
LAKE_JOBS=1 lake build +FabiusFunction.FabiusInverseAsymptotic
LAKE_JOBS=1 lake build +FabiusFunction.PaperFabiusAsymptotic
```

Record the exact commit, command, exit code, and diagnostics for each
invocation, then release the token.  A failure supplies diagnostic evidence
only and should be repaired on the feature branch before another assigned
serialized run.  Request no `+FabiusFunction` aggregate, root-aggregate edit,
TeX/PDF pass, canonical-document lease, or `main` write at this stage.

## Registry amendment: complete inverse scale hierarchy

The next exact frontier corollary is
`inverse:cor:inverse-scale-hierarchy`.  For every pair of real parameters
`α > 0` and `m > 0`, it places the inverse Fabius function strictly between
all positive algebraic powers and all negative logarithmic powers at zero:

```text
y^α = o(fabiusInv F hF y),
fabiusInv F hF y = o((-log y)^(-m)).
```

The Lean theorem will strengthen the second half: `fabiusInv` is little-o of
`(-log y)^r` for every real `r`, with no sign hypothesis.  The frontier result
is the specialization `r = -m`.  This is a source-only public-surface expansion
on the already claimed inverse module and facade.  It does not widen the path
lease to `FabiusInverse.lean`, the root aggregate, or any canonical document.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-inverse-asymptotic-20260825 /
  C:/Users/vresh/.codex/worktrees/c9a3/ProveIt / EVO (Windows)
fetched main SHA: fc63c39788ab4c31694e4f57efe05b543165675a
HEAD and dirty paths: 85928891fdb6e686ecc916e14fcd57238d7ec0f2;
  tracked worktree and index clean before this registry amendment; unrelated
  reciprocity sidecars and tmp/ remain untracked and untouched
writing (exact paths):
  Lean/FabiusFunction/FabiusInverseAsymptotic.lean, adding exactly two public
    scale-hierarchy theorems;
  Lean/FabiusFunction/PaperFabiusAsymptotic.lean, extending only the existing
    inverse claim-level paragraph with the hierarchy; and
  this registry
expected declarations or document claims:
  rpow_isLittleO_fabiusInv_at_zero_right: for every α > 0,
    (fun y : ℝ => y ^ α) =o[nhdsGT 0] fabiusInv F hF;
  fabiusInv_isLittleO_negLog_rpow_at_zero_right: for every r : ℝ,
    fabiusInv F hF =o[nhdsGT 0] (fun y : ℝ => (-Real.log y) ^ r),
    strictly generalizing the frontier specialization r = -m;
  the facade prose will identify these as the complete elementary scale
    hierarchy and will not claim an unproved quantitative remainder
completed commits: generic engine 9b7affe68; current-main merge b7edc7ce2;
  endpoint source 6ee65a167; facade d6464f6c8; source handoff 85928891f
validated (exact command, SHA/state, exit code): no compiler command.  The
  existing endpoint source has three independent static reviews; current-main,
  exact-name, plausible-name, latest advertised-tip, and exact-path scans find
  only the canonical frontier label and no implemented or claimed hierarchy
  theorem.  The latest effective-bounds, both-papers, theorem-polish, and
  shifted-prefix tips change disjoint Lean paths
not yet validated: neither the existing inverse source nor this hierarchy has
  Lean/Lake evidence.  The coordinator has not answered the serialized build
  request.  No Lean, Lake, TeX, PDF, or cache-mutating command has run here
requested integration or lease: advertise this declaration-level expansion on
  the two already claimed Lean paths.  Retain the earlier request for one
  serialized three-target Lean/Lake sequence, updated to the eventual frozen
  hierarchy source tip.  Request no document, root-aggregate, or main-write
  lane
conflicts / dependencies: the proof will use the explicit inverse equivalent,
  exponential-gap little-o comparison, and IsEquivalent transfer.  The older
  inverse flatness API is read-only; no theorem is inferred by naively
  inverting a forward equivalence.  Canonical TeX/PDF remains frozen
next bounded step: commit and push this registry amendment, finish the two
  independent API/collision reviews, then implement only the two advertised
  theorems and the narrow facade paragraph without launching a build
```

## Post-integration hierarchy source handoff

The coordinator has now selectively integrated, repaired, and serialized-build
validated the generic quadratic engine and the original five endpoint
theorems on `origin/main`.  This branch merged that accepted cumulative source
at `fa632dcee9a7d7811589afd5f64ace6df0a8237e`, whose second parent is exact
`origin/main` commit `948bf3f377472c068f9539e0569d383ddc35f617`.
The merge kept the coordinator's compiler-driven repairs verbatim and retained
only the subsequently advertised scale-hierarchy expansion.

The complete source/facade checkpoint is immutable commit
`29f9b0a2bdc2e67c9a79ff3888fa1da244b7e420`.  Its relevant files are:

- `QuadraticAsymptoticInversion.lean`: unchanged accepted-main blob
  `8017000f51c7c57408963d76f436fb8d9a36137f`, SHA-256
  `32B6B9602FD53C397DE2B46E8C13030E17F48FFAB0CDA00FCEFB164B61DA1B52`,
  263 lines and 9,954 bytes;
- `FabiusInverseAsymptotic.lean`: hierarchy blob
  `fd3b5dac6c3f25332c130967ec4914343b7b506a`, SHA-256
  `D38532CE1E52ADF7E5145916E6F758E9F29A0AF6D2A640813BB55CEABD2EDD7B`,
  624 lines and 24,978 bytes; and
- `PaperFabiusAsymptotic.lean`: facade blob
  `ce830f045e45e291a969f4d97a41294d8f83494a`, SHA-256
  `1367FAF472A6667F02D8C3403CF417B853E0FDEC5B02740583F134211EF96F65`,
  122 lines and 7,250 bytes.

The endpoint module adds exactly the two advertised declarations:

```lean
theorem rpow_isLittleO_fabiusInv_at_zero_right
    (F : BoundedFabius) (hF : IsFabius F)
    {α : ℝ} (hα : 0 < α) :
    (fun y : ℝ => y ^ α) =o[𝓝[>] (0 : ℝ)] fabiusInv F hF

theorem fabiusInv_isLittleO_negLog_rpow_at_zero_right
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    fabiusInv F hF =o[𝓝[>] (0 : ℝ)]
      (fun y : ℝ => (-Real.log y) ^ r)
```

The second theorem strictly strengthens the canonical frontier's `r = -m`,
`m > 0` family.  The facade states both results, explicitly identifies that
specialization, and does not claim a quantitative remainder.

Three independent read-only audits are green on the hierarchy snapshot:

- the mathematical audit rederived both exact exponent gaps, checked every
  sign and constant, confirmed the one-sided filters and equivalence-transfer
  directions, and found the direct exponent-gap architecture shorter and more
  insightful than the available indirect alternatives;
- the hostile elaboration preflight checked every new block against exact
  vendored Mathlib signatures, including constant rescaling, square-root
  rewriting, eventual equalities, real powers, and exponential little-o, and
  found no certain or likely elaboration defect; and
- the facade/provenance audit confirmed exact frontier parity, the stronger
  all-real logarithmic statement, import acyclicity, path ownership, and the
  absence of exact or plausible declaration collisions across fetched remote
  Fabius tips.

Targeted whitespace, line-length, forbidden-declaration, conflict-marker, and
public-name checks pass.  These are source/static results only.  The inherited
main blobs have coordinator-recorded compiler evidence, but the new hierarchy
blob and facade blob do not.

### Superseding serialized validation request

Assign the EVO Lean/Lake token to this branch for exact immutable source tip
`29f9b0a2bdc2e67c9a79ff3888fa1da244b7e420`, or have the coordinator validate
that commit in an isolated worktree.  From the repository root, run these two
separate invocations in order with no overlapping Lean/Lake process:

```text
LAKE_JOBS=1 lake build +FabiusFunction.FabiusInverseAsymptotic
LAKE_JOBS=1 lake build +FabiusFunction.PaperFabiusAsymptotic
```

Record the exact commit, command, exit code, and full diagnostics for each
invocation, then release the token.  A failure is diagnostic evidence only;
repair it on this feature branch and publish a new immutable request before
retrying.  This request supersedes the earlier pre-integration three-target
request: the generic engine now has exact accepted-main compiler evidence and
needs no redundant standalone replay.  Request no root aggregate, canonical
document, TeX/PDF, or `main` write lane.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-inverse-asymptotic-20260825 /
  C:/Users/vresh/.codex/worktrees/c9a3/ProveIt / EVO (Windows)
fetched main SHA: 948bf3f377472c068f9539e0569d383ddc35f617
immutable source/facade tip: 29f9b0a2bdc2e67c9a79ff3888fa1da244b7e420
tracked worktree and index: clean after source/facade push; unrelated
  reciprocity sidecars and tmp/ remain untracked and untouched
writing: this registry only; all three Lean source paths are frozen
validated: exact accepted-main generic and original endpoint/facade blobs have
  coordinator-recorded serialized builds; three independent static audits of
  the new hierarchy/facade snapshot are green
not yet validated: hierarchy blob fd3b5dac6 and facade blob ce830f045 have no
  Lean/Lake evidence; no Lean, Lake, TeX, PDF, or cache-mutating command has
  run in this worktree
requested lease: one serialized EVO Lean/Lake assignment for the exact two
  commands above, or coordinator-side isolated validation of the immutable tip
conflicts / dependencies: no current exact-path or declaration collision;
  canonical documents and the root aggregate remain frozen and untouched
next bounded step: commit and push this registry handoff, notify the
  coordinator, and launch nothing until an explicit host grant appears
```

## Registry amendment: reflected inverse scale hierarchy

The left-endpoint hierarchy has a formal reflection consequence at the right
endpoint.  This follow-on tranche advertises exactly two additional public
corollaries, both obtained by composing the corresponding zero-endpoint
theorem with `y ↦ 1 - y` and rewriting by `fabiusInv_one_sub`:

```lean
theorem one_sub_rpow_isLittleO_one_sub_fabiusInv_at_one_left
    (F : BoundedFabius) (hF : IsFabius F)
    {α : ℝ} (hα : 0 < α) :
    (fun y : ℝ => (1 - y) ^ α) =o[𝓝[<] (1 : ℝ)]
      (fun y : ℝ => 1 - fabiusInv F hF y)

theorem one_sub_fabiusInv_isLittleO_negLog_one_sub_rpow_at_one_left
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    (fun y : ℝ => 1 - fabiusInv F hF y) =o[𝓝[<] (1 : ℝ)]
      (fun y : ℝ => (-Real.log (1 - y)) ^ r)
```

A read-only preflight checked all currently fetched advertised remote Fabius
tips and their registries.  Neither exact name nor a formula-equivalent
all-real reflected hierarchy exists.  The nearest theorem,
`one_sub_isLittleO_one_sub_fabiusInv_pow_at_one_left`, instead compares
`1 - y` with natural powers of the complementary inverse and is not a
duplicate.  The proposed proofs are each a single `comp_tendsto` followed by
`simpa only [Function.comp_def, fabiusInv_one_sub]`.

The existing private reflection-filter helper in
`FabiusInverseAsymptotic.lean` is sufficient.  A private copy of the same
helper also exists in `FabiusInverse.lean`, but
`origin/codex/fabius-both-papers` currently freezes that path for its inverse
diagonal-classification handoff.  This branch will not touch, claim, or
deduplicate `FabiusInverse.lean`; that cleanup can be reconsidered only after
the competing source is integrated and explicitly released.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-inverse-asymptotic-20260825 /
  C:/Users/vresh/.codex/worktrees/c9a3/ProveIt / EVO (Windows)
fetched main SHA: 948bf3f377472c068f9539e0569d383ddc35f617
HEAD before this amendment: 6a2d3fd39566d82647a5796bb3cf0bbae463f6f9;
  tracked worktree and index clean; unrelated reciprocity sidecars and tmp/
  remain untracked and untouched
writing (exact paths after the current frozen build disposition):
  Lean/FabiusFunction/FabiusInverseAsymptotic.lean, adding exactly the two
    public reflected hierarchy corollaries above;
  Lean/FabiusFunction/PaperFabiusAsymptotic.lean, extending only the existing
    inverse hierarchy prose to mention reflection at one; and
  this registry
validated: exact-name, plausible-formula, path-ownership, filter-direction,
  rewrite, and Mathlib API preflight are green; this is source/static evidence
not yet validated: no source for this amendment exists yet; immutable current
  source/facade tip 29f9b0a2b remains under its superseding two-target
  serialized validation request
requested integration or lease: advertise only these two declarations and
  the narrow facade paragraph; do not change the active 29f9b0a2b build request
conflicts / dependencies: do not edit or claim FabiusInverse.lean while the
  both-papers diagonal tranche is frozen; no canonical document, root
  aggregate, TeX/PDF, or main-write lane is requested
next bounded step: push this registry-first amendment, keep all source frozen
  until the current build request is acknowledged, then implement only the
  two one-line corollaries and their exact facade sentence
```

## Current-main validation retarget

`origin/main` advanced to
`1eadfd565db2e4c49310dbaa68c7b4648cb563b8`, integrating and validating the
strict Laplace-sign and forward/inverse diagonal tranches.  This branch merged
that exact tip conflict-free as
`f2b62161ac3d21fac027bc3acfc3e4f44ed18dd5` and pushed it.  The hierarchy blob
remains exactly `fd3b5dac6c3f25332c130967ec4914343b7b506a`, and the facade
blob remains exactly `ce830f045e45e291a969f4d97a41294d8f83494a`.

The pending serialized request is therefore retargeted to immutable cumulative
tree `f2b62161ac3d21fac027bc3acfc3e4f44ed18dd5`.  Run the same two separate
commands, in order, from the repository root:

```text
LAKE_JOBS=1 lake build +FabiusFunction.FabiusInverseAsymptotic
LAKE_JOBS=1 lake build +FabiusFunction.PaperFabiusAsymptotic
```

This retarget supersedes only the older commit coordinate `29f9b0a2b`; it does
not change the source/facade blobs, theorem surface, commands, host-serialization
rules, or evidence status.  No Lean/Lake process has run in this worktree and
no host token has been granted.

The coordinator now explicitly releases `FabiusInverse.lean` after its focused
build.  The duplicate private reflection-filter helper can consequently be
considered for a later registry-first cleanup, but it remains outside the
advertised reflected-hierarchy tranche and is not silently claimed here.

## EVO validation handoff: dependency-cache failure, token released

The coordinator granted the exact two-target hierarchy gate in main commit
`a949e2efaa485283e66a7d2130fc723168c01efa`.  This branch merged that immutable
checkpoint as `eed7fd7defdbe34159375efa0e93e8a130cc6311`.  The merge touched only
the coordinator board and preserved the three audited Lean blobs exactly:

- `FabiusInverseAsymptotic.lean`: `fd3b5dac6c3f25332c130967ec4914343b7b506a`;
- `PaperFabiusAsymptotic.lean`: `ce830f045e45e291a969f4d97a41294d8f83494a`;
  and
- `QuadraticAsymptoticInversion.lean`:
  `8017000f51c7c57408963d76f436fb8d9a36137f`.

With no Lean or Lake process present, the first granted invocation was issued
from the repository root with the requested environment setting:

```text
LAKE_JOBS=1 lake build +FabiusFunction.FabiusInverseAsymptotic
```

Lake scheduled 3,931 jobs and exited `1`.  The failure occurred in unrelated
prerequisites before a successful target gate could be established.  The
complete final failed-target list was:

```text
FabiusFunction.StieltjesConstant
FabiusFunction.GammaSecondOrder
FabiusFunction.GaussianPolynomialContraction
FabiusFunction.DyadicAnalytic
FabiusFunction.FourierAnalytic
FabiusFunction.GlobalExtension
FabiusFunction.Monotonicity
FabiusFunction.SaddleAllOrders
```

The emitted diagnostics were dependency-cache I/O failures, not theorem or
elaboration errors.  Representative exact messages were:

```text
GaussianPolynomialContraction.lean:1:0: failed to read file
  Mathlib/Algebra/Group/Subgroup/Lattice.olean.private
DyadicAnalytic.lean:1:0: failed to read file
  Mathlib/Analysis/Asymptotics/Lemmas.olean.private
FourierAnalytic.lean:1:0: failed to read file
  Mathlib/Analysis/Calculus/FDeriv/Analytic.olean.private
```

A read-only post-exit check found each named private artifact and its ordinary
`.olean` sibling present.  This is consistent with a transient cache-population
or scheduling race; it is not evidence that a retry would pass.  Although the
requested `LAKE_JOBS=1` environment variable was set, Lake 4.32 displayed up
to twelve additional running jobs, and an OS-level observation found one Lake
coordinator with ten Lean children.  Thus the invocation did not behave as a
single-job scheduler on this host.

Per the checkpoint's stop-after-first-failure rule, the second command
`lake build +FabiusFunction.PaperFabiusAsymptotic` was not launched.  No source,
facade, cache, toolchain, dependency, or generated artifact was deliberately
edited or repaired after the failure.  All Lean and Lake processes have exited.
The EVO Lean/Lake token is explicitly released.

This run supplies no compiler validation for either hierarchy target.  A fresh
grant should first specify a host-effective serialization control for Lake
4.32, or move the exact immutable blobs to a known-clean isolated build cache.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-inverse-asymptotic-20260825 /
  C:/Users/vresh/.codex/worktrees/c9a3/ProveIt / EVO (Windows)
fetched main SHA: a949e2efaa485283e66a7d2130fc723168c01efa
validated tree attempt: eed7fd7defdbe34159375efa0e93e8a130cc6311
tracked worktree and index: clean before and after the attempted build;
  unrelated reciprocity sidecars and tmp/ remain untracked and untouched
writing: this registry only; all Lean and facade source remains frozen
validated: merge ancestry, exact source blobs, and all earlier source/static
  audits; no compiler gate completed successfully in this attempt
not yet validated: both requested targets; the first exited 1 on dependency
  cache I/O failures and the second was not run
released: EVO Lean/Lake token; no Lean or Lake process remains
conflicts / dependencies: no source conflict or target-local diagnostic was
  observed; host-effective build serialization and cache health need review
next bounded step: commit and push this failure handoff, notify the coordinator,
  and launch no further Lean/Lake command without a fresh explicit grant
```

## Registry-first claim: stretched-exponential Fabius decay hierarchy

This is a new, disjoint ordinary-source tranche.  It does not modify, retry,
or relax the coordinator's hold on the inverse-hierarchy statements.  The
claim covers exactly:

- `Lean/FabiusFunction/FabiusDecayComparison.lean`; and
- this branch registry.

The mathematical strengthening replaces the proof's fixed dyadic exponential
scale by every positive stretched-exponential scale.  For arbitrary
`c > 0` and `β > 0`, the target conclusion is
`exp (-c / x ^ β) = o(F(x))` as `x → 0⁺`.  The proof first exposes the reusable
fact that the negative-log Fabius profile is little-o of
`2 ^ (β * t)`, then transfers the resulting comparison from the dyadic
logarithmic coordinate back to the original variable.

The exact proposed additive public declarations are:

```lean
theorem fabiusLogProfile_isLittleO_two_rpow_mul
    (F : BoundedFabius) (hF : IsFabius F)
    {β : ℝ} (hβ : 0 < β) :
    fabiusLogProfile F =o[atTop]
      (fun t : ℝ => (2 : ℝ) ^ (β * t))

theorem exp_neg_two_rpow_mul_isLittleO_fabiusLogPhi
    (F : BoundedFabius) (hF : IsFabius F)
    {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    (fun t : ℝ => Real.exp (-c * (2 : ℝ) ^ (β * t))) =o[atTop]
      fabiusLogPhi F

theorem exp_neg_two_rpow_mul_isLittleO_fabius
    {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    (fun t : ℝ => Real.exp (-c * (2 : ℝ) ^ (β * t))) =o[atTop]
      fabiusLogPhi fabius

theorem exp_neg_div_rpow_isLittleO_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F)
    {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    (fun x : ℝ => Real.exp (-c / x ^ β))
      =o[nhdsWithin 0 (Set.Ioi 0)] fabiusReal F

theorem exp_neg_div_rpow_isLittleO_fabius
    {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    (fun x : ℝ => Real.exp (-c / x ^ β))
      =o[nhdsWithin 0 (Set.Ioi 0)] fabiusReal fabius
```

All four existing public `β = 1` declarations remain source-compatible:

- `exp_neg_two_rpow_isLittleO_fabiusLogPhi`;
- `exp_neg_two_rpow_isLittleO_fabius`;
- `exp_neg_div_isLittleO_fabiusReal`; and
- `exp_neg_div_isLittleO_fabius`.

Their current longer proofs will become direct specializations of the new
two-parameter theorems.  The module overview and declaration doc comments will
state the stronger all-positive-`β` result and identify the old declarations
as compatibility specializations.  No canonical TeX/PDF, coverage map,
frontier document, root aggregate, facade, or downstream source is claimed.

A read-only collision audit searched the current source tree, all fetched
registries, and advertised local/remote refs for the exact names, plausible
alternate names, equivalent formulas, and path claims.  No branch claims
`FabiusDecayComparison.lean`, no existing declaration proves this positive
`β` family, and the current coordinator board does not mark the module hot,
frozen, or single-owner.  The only direct downstream importers are
`FabiusQuotientExponentialMismatch.lean` and `PaperKFoldThueMorse.lean`; the
four retained declarations avoid source changes there.

The proposed focused validation, only after an explicit EVO Lean/Lake grant,
is three separate serialized invocations in dependency order:

```text
LEAN_NUM_THREADS=0; LAKE_JOBS=1; lake build +FabiusFunction.FabiusDecayComparison
LEAN_NUM_THREADS=0; LAKE_JOBS=1; lake build +FabiusFunction.FabiusQuotientExponentialMismatch
LEAN_NUM_THREADS=0; LAKE_JOBS=1; lake build +FabiusFunction.PaperKFoldThueMorse
```

The environment notation above describes the required controls, not commands
already run.  No Lean, Lake, TeX, PDF, cache, or generated-artifact process has
been launched for this claim.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-inverse-asymptotic-20260825 /
  C:/Users/vresh/.codex/worktrees/c9a3/ProveIt / EVO (Windows)
fetched main SHA: 447ea43628edf6d4f868aaac596574673412ef3d
HEAD before this claim: 100abb11efbddfeec26a58def5504490fa123b46;
  tracked worktree and index clean; unrelated reciprocity sidecars and tmp/
  remain untracked and untouched
writing after this registry claim is committed and pushed:
  Lean/FabiusFunction/FabiusDecayComparison.lean and this registry only
validated: mathematical reduction, Mathlib API, rpow normalization,
  dependency, exact-name, semantic-collision, and path-ownership preflight
not yet validated: no claimed Lean source has been edited or compiled yet
requested integration or lease: accept the ordinary self-service source claim;
  later grant exactly the three serialized EVO targets above
conflicts / dependencies: inverse hierarchy source/API and its validation stay
  frozen; no build, document, main-write, or serialized path is claimed
next bounded step: commit and push this registry-first claim, reread fetched
  main and advertised registries, then implement only the claimed one-file API
```

## Immutable inverse-power decay source checkpoint and build request

The claimed one-file generalization is source-complete and pushed.  Source
commit `e601015588ad26dd95c860686d5cf1e5ea3bb123` adds the five advertised
positive-`β` declarations and preserves all four existing `β = 1` public
statements as direct specializations.  After that commit, current main
`4789f05b1a1abc34b5753c166a524be1f62078c3` was merged as
`1ab32c423531b90ce07db0482f8ad229b2d01db1`.  The sole merge conflict was the
already-audited inverse hierarchy file; it was resolved exactly to the
coordinator's compiled main blob `b02fd05fae88d0521930281e09c0813daee97650`.
The independent decay source survived at its exact pre-merge blob.

Immutable checkpoint coordinates are:

```text
branch tip: 1ab32c423531b90ce07db0482f8ad229b2d01db1
tree: 766c9e1635360f0718d11d08c0757588fe8283dc
FabiusDecayComparison.lean blob:
  5a407fe366bead3fa2bb8f9d90cac14900fc46bf
FabiusDecayComparison.lean SHA-256:
  50D055DFE92CCB49DB871DC7E0CA0DCCB1A26B8874DDEB4CD0CD413075D8DA9D
FabiusDecayComparison.lean size: 7,895 bytes
```

The earlier claim used “stretched exponential” as an informal umbrella term.
Hostile review correctly noted that the theorem covers every `β > 0`, whereas
that term is conventionally narrower.  The source now uses the precise phrase
“inverse-power exponentials” and states explicitly that the K-fold draft gives
the `β = 1` case while this module proves the stronger all-positive-`β` family.
The registered formulas and ownership boundary were already exact and are
unchanged.

Two independent read-only reviews checked the dirty source against Lean 4.32,
Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, and the exact downstream
call site.  They verified the signs and asymptotic direction, the
`Real.rpow_mul` and `Real.rpow_neg` orientations, the positive-rate `atTop`
composition, the quotient identity, every compatibility simplification, all
nine doc comments, absence of forbidden placeholders/conflict markers, and
preservation of the sole direct theorem application.  `git diff --check` and
the 100-column audit were clean.  This remains source/static evidence only.

The latest coordinator board reports both host Lean/Lake tokens idle and
confirms `LEAN_NUM_THREADS=0` as the effective strict Lake 5.0 serialization
control.  Request the EVO token for exactly these three separate invocations,
in order, stopping and releasing the token after the first failure:

```powershell
$env:LEAN_NUM_THREADS = '0'
$env:LAKE_JOBS = '1'
lake build +FabiusFunction.FabiusDecayComparison
```

```powershell
$env:LEAN_NUM_THREADS = '0'
$env:LAKE_JOBS = '1'
lake build +FabiusFunction.FabiusQuotientExponentialMismatch
```

```powershell
$env:LEAN_NUM_THREADS = '0'
$env:LAKE_JOBS = '1'
lake build +FabiusFunction.PaperKFoldThueMorse
```

No root aggregate, inverse module, facade, fourth target, TeX/PDF command,
cache clean/reconstruction, or parallel process is requested.  The second and
third targets are the complete direct-importer closure and verify that the
retained legacy names remain usable.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-inverse-asymptotic-20260825 /
  C:/Users/vresh/.codex/worktrees/c9a3/ProveIt / EVO (Windows)
fetched and merged main SHA: 4789f05b1a1abc34b5753c166a524be1f62078c3
immutable validation candidate: 1ab32c423531b90ce07db0482f8ad229b2d01db1
writing: this registry only; claimed Lean source is frozen at blob 5a407fe366
validated: exact merge ancestry/blob preservation plus the two independent
  mathematical, API, compatibility, documentation, and static source reviews
not yet validated: no Lean/Lake target has run for the new decay source
requested integration or lease: sole EVO Lean/Lake ownership for exactly the
  three separate commands above, in order, with strict stop-on-failure
conflicts / dependencies: the inverse hierarchy is now integrated, green, and
  released; canonical documents remain with their current sole owner
next bounded step: commit and push this immutable handoff, notify the
  coordinator, and launch no Lean/Lake process before an explicit board grant
```

## EVO validation handoff: target-local normalization failure, token released

Coordinator checkpoint `0f9a6db8313d626c52dc0e4ef31b42158bbd1bb0`
granted exactly three strictly sequential gates.  This branch merged that
checkpoint as validation tree
`2ad7703d374d42a6f451b28a49c3f12c64ced99e`, pushed it, verified no preexisting
Lean/Lake/Elan process, and rechecked the granted source blob and digest:

```text
FabiusDecayComparison.lean blob:
  5a407fe366bead3fa2bb8f9d90cac14900fc46bf
FabiusDecayComparison.lean SHA-256:
  50D055DFE92CCB49DB871DC7E0CA0DCCB1A26B8874DDEB4CD0CD413075D8DA9D
```

The first granted command was then run from the repository root:

```powershell
$env:LEAN_NUM_THREADS = '0'
$env:LAKE_JOBS = '1'
lake build +FabiusFunction.FabiusDecayComparison
```

Lake scheduled 3,312 jobs.  Host snapshots throughout the run showed the
single Elan launcher/toolchain-Lake pair and at most one `lean.exe` child; the
sampled children included `DyadicAnalytic.lean` and `TaylorReduction.lean`.
Thus `LEAN_NUM_THREADS=0` supplied the intended strict serialization.  Twenty
reported rebuilt prerequisites completed successfully, including
`FabiusLogSquaredAsymptotic` and `FabiusSmallArgumentScale`, before the exact
endpoint target ran.

The endpoint target exited `1` after 18 seconds with exactly these two source
diagnostics:

```text
Analysis/FabiusFunction/Lean/FabiusFunction/FabiusDecayComparison.lean:50:10:
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  2 ^ ?y
in the target expression
  (fun x => Real.exp (Real.log 2 * β * x)) t =
    (fun t => 2 ^ (β * t)) t

F : BoundedFabius
hF : IsFabius F
β : ℝ
hβ : 0 < β
t : ℝ
⊢ (fun x => Real.exp (Real.log 2 * β * x)) t =
    (fun t => 2 ^ (β * t)) t
```

```text
Analysis/FabiusFunction/Lean/FabiusFunction/FabiusDecayComparison.lean:64:4:
Type mismatch: After simplification, term
  Tendsto.comp
    (tendsto_rpow_atTop_of_base_gt_one 2 ...)
    (Tendsto.const_mul_atTop hβ tendsto_id)
has type
  @Tendsto ℝ ℝ (fun x => 2 ^ (β * id x)) atTop atTop
but is expected to have type
  @Tendsto ℝ ℝ (fun t => 2 ^ (β * t)) atTop atTop
```

Lean then reported:

```text
error: Lean exited with code 1
Some required targets logged failures:
- FabiusFunction.FabiusDecayComparison
error: build failed
```

These are statement-preserving proof-normalization defects, not mathematical,
API, import, or dependency failures.  The first goal retains unapplied lambda
applications, so the direct `rw [Real.rpow_def_of_pos ...]` cannot see the
right-hand `rpow`.  The second retains `id x` after unfolding composition.
The exact proposed repair is limited to:

```lean
  · exact Filter.Eventually.of_forall fun t => by
      change Real.exp (Real.log 2 * β * t) =
        (2 : ℝ) ^ (β * t)
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
```

and adding `id_eq` to the second normalization:

```lean
    simpa only [Function.comp_def, id_eq] using
      (tendsto_rpow_atTop_of_base_gt_one (2 : ℝ) (by norm_num)).comp
        (tendsto_id.const_mul_atTop hβ)
```

No public statement, name, hypothesis, import, module prose, other proof, or
other path needs to change.  Per the stop-on-first-failure rule,
`+FabiusFunction.FabiusQuotientExponentialMismatch` and
`+FabiusFunction.PaperKFoldThueMorse` were not launched.  No cache clean,
reconstruction, source repair, TeX/PDF command, or fourth target was attempted.
All Lean/Lake/Elan processes exited, tracked files remained clean, the source
blob/digest remained exact, and the EVO Lean/Lake token is explicitly released.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-inverse-asymptotic-20260825 /
  C:/Users/vresh/.codex/worktrees/c9a3/ProveIt / EVO (Windows)
fetched and merged grant SHA: 0f9a6db8313d626c52dc0e4ef31b42158bbd1bb0
failed validation tree: 2ad7703d374d42a6f451b28a49c3f12c64ced99e
writing: this registry only; source remains frozen at blob 5a407fe366
validated: strict host serialization, 3,311 prerequisite jobs, exact target
  reachability, and the two complete target-local elaboration diagnostics
not yet validated: the changed endpoint target and both direct consumers
released: EVO Lean/Lake token; no Lean/Lake/Elan process remains
requested next source action: apply only the two statement-preserving
  normalization repairs displayed above, then publish a new immutable blob
conflicts / dependencies: no mathematical/source-path collision was exposed;
  the effective-bounds inverse-helper handoff remains a separate future lane
next bounded step: commit and push this failure handoff, notify the coordinator,
  and perform no repair or retry until the board records its disposition
```
