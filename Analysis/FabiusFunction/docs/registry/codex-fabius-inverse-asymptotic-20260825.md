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
    the sharper intrinsic O(log lambda/lambda) estimate by completing the
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
