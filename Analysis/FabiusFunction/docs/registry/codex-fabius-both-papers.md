# Workstream registry: `codex/fabius-both-papers`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-both-papers /
  /home/codex/src/Proofs / codexbox
fetched main SHA: e18f5d0b0e3ec78e2b14e7006af6c7e916b42923
HEAD and dirty paths: 991add419fb7fda185f4a79cb87cae59f3b37205;
  clean before this registry-only source-checkpoint handoff
writing (exact paths):
  Lean/FabiusFunction/BoseFinitePartIntegral.lean;
  docs/registry/codex-fabius-both-papers.md
expected declarations or document claims:
  `boseFinitePartSmallKernel_neg`, `boseLogKernel_neg`, and
  `boseFinitePartLargeKernel_neg`, the strict sign profile of both convergent
  finite-part kernels; `gammaZetaConstant_neg`, strict negativity of the
  Euler--Stieltjes finite-part constant; `firstStieltjesConstant_lt`, the
  resulting strict unconditional upper bound
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
  leaves the final five-theorem strict API
validated (exact command, SHA/state, exit code): coordinator board records
  serialized immutable `lake build +FabiusFunction.LowerLambertW` at
  `4c6bbac41`, exit 0, with its source blob unchanged on current main;
  read-only integer-grid audits at `12e7137a8` and refreshed main found no exact or semantic
  duplicate across all advertised tips and verified the theorem domains,
  edge cases, placement, imports, and public export path; coordinator commit
  `62f4142a9f290c570299e200192a4818dc7529d2` directly ran
  `LAKE_JOBS=1 lake env lean` on the corrected module and exited 0; the current
  source differs from that green proof-bearing blob only in doc-comment words
  read-only review of `09b360531` confirmed the moved block is byte-identical,
  imports and namespace placement suffice, the downstream theorem resolves
  through its existing direct import, and all static hygiene checks pass
not yet validated: no focused Lake target, downstream module, public facade,
  or aggregate build is claimed for the integer-grid checkpoint; the moved
  dyadic theorem body was already compiled in its downstream home by the green
  aggregate at `9887ea584`, but its new module ownership/import context has not
  been compiled; only the exact integer-grid module elaboration plus read-only
  source/collision/marker/diff checks are currently validated; the Gamma--zeta
  sign source checkpoint is implemented and has independent term-level static
  review, but has not been elaborated or built in production; its predecessor
  non-strict `/tmp` proof was green, while the strict logarithmic and large
  kernel upgrades are statically reviewed only
requested integration or lease: the integer-grid and dyadic source checkpoints
  are ready for integration and their ordinary source paths are released;
  request the codexbox token for serialized targets
  `+FabiusFunction.GlobalExtension`, `+FabiusFunction.PaperStatements`,
  `+FabiusFunction.Paper06487Supplement`, and `+FabiusFunction.Paper06487`;
  the dyadic relocation also needs serialized `+FabiusFunction.GlobalDyadic`
  and `+FabiusFunction.OriginalPaperSupplement` validation; this new ordinary
  claim covers only `BoseFinitePartIntegral.lean` and the five advertised
  strict public sign theorems, with only the set-integral strictness lemma kept
  private; request serialized `+FabiusFunction.BoseFinitePartIntegral` followed
  by its sole non-facade direct importer `+FabiusFunction.PeriodicMean`;
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
  leases
next bounded step: push this source-checkpoint handoff and await the focused
  serialized builds; after validation/integration, request the human-document
  lease needed to close the existing audit finding without racing the canonical
  exposition owner
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
