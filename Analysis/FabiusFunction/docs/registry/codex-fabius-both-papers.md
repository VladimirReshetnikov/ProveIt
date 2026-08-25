# Workstream registry: `codex/fabius-both-papers`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-both-papers /
  /home/codex/src/Proofs / codexbox
fetched main SHA: 046946a974467e83244fd3a183a3e084e70d3379
HEAD and dirty paths: 9290aa77955a5ae3bc6b916bf72fb3b1a14a5c5d;
  clean before this registry-only refresh
writing (exact paths): this registry only; no further source writes until the
  coordinator acknowledges the requested lease
expected declarations or document claims: `lowerLambertW_branchPoint`,
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
  and build-token request; no documentation or aggregate file was changed
validated (exact command, SHA/state, exit code): delegated prototype command
  `lake env lean /tmp/LowerLambertWPrototype.lean` at base 09ae23f63, exit 0;
  all 11 new declarations report exactly `[propext, Classical.choice,
  Quot.sound]`; production source is byte-for-byte identical to that final
  prototype by `diff -q`, and `git diff --check` is clean
not yet validated: no Lean/Lake command has run on the production checkpoint;
  no focused, facade, downstream, or aggregate build claim is made
requested integration or lease: acknowledge an exact write lease for
  Lean/FabiusFunction/LowerLambertW.lean and assign the build token for
  `+FabiusFunction.LowerLambertW`; documentation remains frozen for the
  coordinator's semantic integrator
conflicts / dependencies: current main advanced after this branch's clean
  base; do not merge while preserving this checkpoint; all old public names
  and binders are retained; calculus remains on the open smooth interior
next bounded step: wait for coordinator acknowledgement of the exact source
  lease and build assignment; do not merge current main, edit source/docs, or
  launch validation while the token remains paused
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
