# Workstream registry: `codex/fabius-both-papers`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-both-papers /
  /home/codex/src/Proofs / codexbox
fetched main SHA: e18f5d0b0e3ec78e2b14e7006af6c7e916b42923
HEAD and dirty paths: 5db4ab6f9add0aed692e746da0dc0a7fb9ce23fd;
  `Lean/FabiusFunction/GlobalDyadic.lean`,
  `Lean/FabiusFunction/OriginalPaperSupplement.lean`, and this registry are
  dirty for the unvalidated total dyadic-cast relocation checkpoint
writing (exact paths):
  Lean/FabiusFunction/GlobalExtension.lean;
  Lean/FabiusFunction/GlobalDyadic.lean;
  Lean/FabiusFunction/OriginalPaperSupplement.lean;
  docs/registry/codex-fabius-both-papers.md
expected declarations or document claims:
  `extendedFabius_natCast_eq_ite`, the exact all-natural value formula
  (zero at even knots and the Thue--Morse sign indexed by `m / 2` at odd
  knots); `iteratedDeriv_extendedFabius_natCast_eq_zero_iff`, the sharp
  classification by positive derivative order or even knot;
  relocate `rvachevDyadic_cast_global` unchanged from
  `OriginalPaperSupplement.lean` to immediately after the restricted
  `rvachevDyadic_cast` in `GlobalDyadic.lean`, preserving both public names and
  exposing the total theorem to evaluator clients
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
  relocation paths before authoring
validated (exact command, SHA/state, exit code): coordinator board records
  serialized immutable `lake build +FabiusFunction.LowerLambertW` at
  `4c6bbac41`, exit 0, with its source blob unchanged on current main;
  read-only natural-knot audits at `12e7137a8` and refreshed main found no exact or semantic
  duplicate across all advertised tips and verified the theorem domains,
  edge cases, placement, imports, and public export path; coordinator commit
  `62f4142a9f290c570299e200192a4818dc7529d2` directly ran
  `LAKE_JOBS=1 lake env lean` on the exact corrected module and exited 0
not yet validated: no focused Lake target, downstream module, public facade,
  or aggregate build is claimed for the natural-knot checkpoint; the moved
  dyadic theorem body was already compiled in its downstream home by the green
  aggregate at `9887ea584`, but its new module ownership/import context has not
  been compiled; only the exact natural-knot module elaboration plus read-only
  source/collision/marker/diff checks are currently validated
requested integration or lease: natural-knot source is ready for integration;
  request the codexbox token for serialized targets
  `+FabiusFunction.GlobalExtension`, `+FabiusFunction.PaperStatements`,
  `+FabiusFunction.Paper06487Supplement`, and `+FabiusFunction.Paper06487`;
  this claim expands to the ordinary, nonoverlapping paths
  `GlobalDyadic.lean` and `OriginalPaperSupplement.lean`, whose relocation will
  later need serialized `+FabiusFunction.GlobalDyadic` and
  `+FabiusFunction.OriginalPaperSupplement` validation;
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
  serialized and unclaimed
next bounded step: finish the read-only relocation review, checkpoint and push
  the unvalidated source move, then await focused/downstream build tokens and
  the natural-knot documentation lease
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
