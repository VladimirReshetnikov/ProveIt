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
