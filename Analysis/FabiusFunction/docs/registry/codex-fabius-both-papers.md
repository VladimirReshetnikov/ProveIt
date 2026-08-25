# Workstream registry: `codex/fabius-both-papers`

This file implements the per-branch registry fallback in
[`../COLLABORATION.md`](../COLLABORATION.md).

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-both-papers /
  /home/codex/src/Proofs / codexbox
fetched main SHA: ebe4bd8442507df7b629aa87669fa6bb92e2f19e
HEAD and dirty paths: 09ae23f63217ccf40a67e26b39ed9d9f5fe49d04;
  Lean/FabiusFunction/LowerLambertW.lean and this registry
writing (exact paths): preservation checkpoint already present in
  Lean/FabiusFunction/LowerLambertW.lean; this registry; no further writes
  until the coordinator acknowledges the requested lease
expected declarations or document claims: `lowerLambertW_branchPoint`,
  `lowerLambertW_le_neg_one`, `lowerLambertW_mul_exp_of_mem_Ico`,
  `lowerLambertW_unique_of_mem_Ico`, `lowerLambertW_strictAntiOn_Ico`,
  `lowerLambertW_image_Ico`, `paperLambertN_eq9_of_le`,
  `one_div_log_two_le_paperLambertN`,
  `paperLambertN_eq_one_div_log_two`,
  `paperLambertN_eq_one_div_log_two_iff`, and
  `one_div_log_two_lt_paperLambertN`; existing open-domain names remain
  exact compatibility wrappers
completed commits: none yet; the already-dirty source will be preserved in a
  clearly labelled uncompiled checkpoint commit before this status is pushed
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
next bounded step: checkpoint and push this exact source/status, then wait for
  coordinator acknowledgement and build assignment
```

Source-only subagents inspect and prototype in `/tmp`; they do not edit the
leased production paths, run builds, or mutate Git state.
