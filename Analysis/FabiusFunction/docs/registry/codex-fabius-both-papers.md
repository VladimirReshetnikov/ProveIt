# Workstream registry: `codex/fabius-both-papers`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-both-papers /
  /home/codex/src/Proofs / codexbox
fetched main SHA: 12e7137a897b8ec99ddf8935f64fff9f35977617
HEAD and dirty paths: 225f5338de9ea92489ed6a2c0c371c6edb4f5db9;
  clean before this registry-only claim
writing (exact paths):
  Lean/FabiusFunction/GlobalExtension.lean;
  docs/registry/codex-fabius-both-papers.md
expected declarations or document claims:
  `extendedFabius_natCast_eq_ite`, the exact all-natural value formula
  (zero at even knots and the Thue--Morse sign indexed by `m / 2` at odd
  knots); `iteratedDeriv_extendedFabius_natCast_eq_zero_iff`, the sharp
  classification by positive derivative order or even knot
completed commits: Lower-Lambert source checkpoint `1da2fde2285e3970267b7dc2561bcd0d897be1b4`
  was integrated by coordinator merge `046946a974467e83244fd3a183a3e084e70d3379`;
  registry handoff `225f5338de9ea92489ed6a2c0c371c6edb4f5db9`
  closed that slice and recorded the frozen documentation gaps
validated (exact command, SHA/state, exit code): coordinator board records
  serialized immutable `lake build +FabiusFunction.LowerLambertW` at
  `4c6bbac41`, exit 0, with its source blob unchanged on current main;
  read-only natural-knot audits at `12e7137a8` found no exact or semantic
  duplicate across all advertised tips and verified the theorem domains,
  edge cases, placement, imports, and public export path
not yet validated: the two natural-knot declarations are not implemented;
  no Lean/Lake/TeX command is authorized or claimed for this new slice
requested integration or lease: this is a nonoverlapping ordinary source
  claim under the 17:10 shared protocol; after an unvalidated source checkpoint
  is pushed, request the codexbox token for serialized targets
  `+FabiusFunction.GlobalExtension`, `+FabiusFunction.PaperStatements`,
  `+FabiusFunction.Paper06487Supplement`, and `+FabiusFunction.Paper06487`;
  serialized README/primary/walkthrough/coverage paths are deliberately not
  claimed yet
conflicts / dependencies: all 16 advertised Fabius heads and their registries
  were checked; no branch claims GlobalExtension and the only overlap is the
  existing even/odd ingredients and downstream special cases that this API
  packages without modifying; current HEAD is a clean ancestor of main
next bounded step: push this claim, reread the board, merge current main into
  the clean feature branch, then edit only GlobalExtension.lean and checkpoint
  the source explicitly as not yet validated
```

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
  the sharp natural-knot classification
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
