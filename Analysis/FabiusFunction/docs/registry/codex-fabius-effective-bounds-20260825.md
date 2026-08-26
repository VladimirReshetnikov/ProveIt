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
