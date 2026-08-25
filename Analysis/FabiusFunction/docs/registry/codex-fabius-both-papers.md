# Workstream registry: `codex/fabius-both-papers`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-both-papers /
  /home/codex/src/Proofs / codexbox
fetched main SHA: 4c6bbac41f987e171f8d15a0b1aa842d1e3ee847
HEAD and dirty paths: 07cefff099a348d561ab062fa7f0c4fc6537833e;
  clean before this registry-only refresh
writing (exact paths): this registry only; the Lower-Lambert implementation
  slice is closed because main already contains it byte-for-byte
expected declarations or document claims already integrated on main:
  `lowerLambertW_branchPoint`,
  `lowerLambertW_le_neg_one`, `lowerLambertW_mul_exp_of_mem_Ico`,
  `lowerLambertW_unique_of_mem_Ico`, `lowerLambertW_strictAntiOn_Ico`,
  `lowerLambertW_image_Ico`, `paperLambertN_eq9_of_le`,
  `one_div_log_two_le_paperLambertN`,
  `paperLambertN_eq_one_div_log_two`,
  `paperLambertN_eq_one_div_log_two_iff`, and
  `one_div_log_two_lt_paperLambertN`; existing open-domain names remain
  exact compatibility wrappers
completed commits: `1da2fde2285e3970267b7dc2561bcd0d897be1b4`
  preserves the exact closed lower-Lambert source and the initial coordinator
  reply; `9290aa77955a5ae3bc6b916bf72fb3b1a14a5c5d` records the exact source-lease
  and build-token request; `9906ea69aef27a85561a6fa10f67a5c29483aa4f`
  refreshes the paused coordination state and read-only prototype inventory;
  coordinator merge `046946a974467e83244fd3a183a3e084e70d3379`
  integrated the source; no documentation or aggregate file was changed
validated (exact command, SHA/state, exit code): delegated prototype command
  `lake env lean /tmp/LowerLambertWPrototype.lean` at base 09ae23f63, exit 0;
  all 11 new declarations report exactly `[propext, Classical.choice,
  Quot.sound]`; production source is byte-for-byte identical to that final
  prototype by `diff -q`, and `git diff --check` is clean
  read-only preflight at main `4c6bbac41` found correct endpoint/order/range
  logic, preserved compatibility binders, sufficient imports, and no duplicate
  or alternate implementation across advertised branch tips
not yet validated: no Lean/Lake command has run on the integrated production
  source; no focused, facade, downstream, or aggregate build claim is made
requested integration or lease: source integration is complete and its write
  lease can remain closed; when available, assign the build token at an
  immutable main SHA for `+FabiusFunction.LowerLambertW`; documentation remains
  frozen for the coordinator's semantic integrator
conflicts / dependencies: main and this branch resolve `LowerLambertW.lean` to
  identical blob `6688db017aaf5ab659486efa850e00d02c07ae8c`; all old public
  names and binders remain compatibility wrappers; calculus intentionally
  remains on the open smooth interior
next bounded step: wait for the assigned build token or documentation lease;
  do not merge, edit source/docs, or launch validation while the token remains
  paused
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
