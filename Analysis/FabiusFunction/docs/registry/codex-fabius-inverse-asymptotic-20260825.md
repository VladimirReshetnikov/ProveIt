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
