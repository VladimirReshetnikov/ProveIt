# Recent-commit intake for the sub-221 search

Inspected 2026-10-20 after 14:23 UTC, pinned to
[`c011e44bc2df6238940bb600833730873b308334`](https://github.com/VladimirReshetnikov/ProveIt/commit/c011e44bc2df6238940bb600833730873b308334).
The review cutoff was 2026-10-20 05:48 UTC. Raw commit responses and file
identities are in `commit_metadata.json`. Prior delivery artifacts were not changed.

## Bottom line

The new K221 archive is byte-identical to our delivery. No newer <=220-state
construction was found. The four newly uploaded K222 reports repeat the known
conditional-G or seed-request-G source, but supply two different literal
continuations that are useful search alternatives. Exact source-subtree
alignment shows that these are **not new decoder allocations**.

## Commits since the cutoff

- `5ca63ffb81c8eaf8c23b23ebcfaa5876c3cac838`, 05:48:34 UTC:
  records a negative bounded rotation/fold search on the seed-G222.
  Counts were 75 / 5,443 / 14,253 tables at three search levels, 1,128
  helper subgoals, and 24 pairs with both read-bit subgoals. None composed
  into a valid fold with final maximum zero run six. This is not a lower
  bound and did not inspect our subsequent K221.
- `c011e44bc2df6238940bb600833730873b308334`, 14:16:31 UTC:
  adds five incoming ZIP packets, with no research-tree code changes.

## Archive and candidate identities

| Incoming archive | ZIP SHA-256 | Candidate canonical SHA-256 |
|---|---|---|
| `K221_Construction_2026-10-20.zip` | `a06c99b775193d9642a2734b7dd5fe7b72736fbdf9d9d8be438321d5e5d57ba4` | `6457dce8c91c5975fb405607567158ca92ad97331f2724503edc0d4ff74cab3c` |
| `K222_Composed_Construction_2026-10-20.zip` | `5f2b1066f7252f05b5012c348f7c0a6e077ddc69534c9a29ac6ba84c55b229f8` | `01fb8d9813824ebf67b0f8b7f420c7719ae83d21217fde16eae7ab6c78ec2e26` |
| `K222_Construction_2026-10-20 (1).zip` | `7d341f01138a1635a61bd14befcca2043caedad73a1f80cf926a8548f3a60bcc` | seed `3bcf4678c9c576ae99a108c32038f035b42204289267d05a34ba2b37b32b6476`; conditional `60e21a040e58e2a2840b0f3d58ad3ee0e6ef4d0d5cdf1372d5a69355f1198ca1` |
| `K222_Construction_2026-10-20 (2).zip` | `ed008b6a349ae913e140bd260d48a2efc31f28db349ad7f3bd547e1497b0be5d` | same seed and conditional hashes as preceding row |
| `ZFC_K222_Construction_2026-10-20.zip` | `bce505a51868372f04e889cf6b04f49870c44eb5a39c947c08ea8ea46fb9a866` | conditional `60e21a040e58e2a2840b0f3d58ad3ee0e6ef4d0d5cdf1372d5a69355f1198ca1` |

All archives are retained and extracted beneath `archives/`. The K221 archive
hash was compared directly with the prior delivery ZIP, not just its README.

## The two usable continuation differences

Both new seed-G222 variants have the exact source SHA-256
`cc1fbb3a16dd446af9c7cdb678317d31060082e6794b9c7074ce02b46584a75e`.
Matching each physical decoder state's complete set of represented subtrees
gives a unique bijection to our K222. Every one of the 173 decoder groups
matches exactly, and the 49 engine labels are fixed.

After this bijection, the ordinary seed222 has only:

```
native 103/read1: (0,L,162) -> (0,L,142)
```

The composed222 has that difference and:

```
native 157/read1: (1,L,148) -> (1,L,187)
```

Run `python3 -B research_sub221/intake/compare_incoming.py` from the workspace
to regenerate the maps, aligned tables and `incoming_comparison.json`.

The three corresponding K221 exploratory variants are:

- `k221_row103.native.tm`
- `k221_row157.native.tm`
- `k221_both.native.tm`

Their identities and exact edits are in `alternate_k221_rows.json`. All three
preserve K221's exact compound-source decoder binding under the existing
literal prefix checker. In addition, `verify_alternate_rows.py` independently
proves all three halting-equivalent to the delivered K221 on every initial
binary tape from state0, using positive macro diamonds. The checked receipt
is `alternate_rows_proof.json`. They are equivalent 221-state search inputs,
not smaller constructions.

The row103 change has a simple local explanation: the inductive invariant
at old state 103 forces offset -1 to contain 1. Old and new first steps
therefore enter states 162 and 142 scanning 1; both next rows are `(0,L,27)`.
The two paths converge with identical tape and head after two steps.
The row157 change does not require an invariant. If the left bit is zero,
old148/read0 and new187/read0 are both `(0,R,186)`, so two steps agree.
If the left bit is one, the new path through187 and76 returns to148 at the
old head position with unchanged tape: new187/read1 is `(1,R,76)`, and the
preserved current one makes76/read1 `(1,L,148)`. Thus three new steps equal
one old step. Unknown cells are untouched. The verifier rederives and
independently checks the old 535 constant-bit invariant facts for the
row103 case and checks exact complete-tape convergence for both diamonds.

## Validation and limits

The composed packet's full offline driver finished with
`FULL_K222_REPLAY_PASS` in `composed222_replay/replay.json`. All 15 executed
phases passed, including fresh manifest, pinned parent extraction, emitter,
numerical formula audit, deterministic compilation, artifact identity,
finite logic, and all 6,167 unbounded runtime cases. The runtime used
1,488,930 symbolic rule applications, covered all 444 rows, and checked the
exact 409,835-step blank initialization. Regenerated case bytes match the
frozen certificate at SHA-256
`ff650d645ee2ccc5e07f2b1437944b45037c241c863022633f02a79fe25bb7fd`.
Elapsed driver time was 1,087.4 seconds on this shared execution environment.
Exact fresh receipts and identities are retained in `replay_summary.json`.

The incoming packets report ordinary mathematical consistency calibration
formalizable in ZFC, plus executable universal runtime certificates. None
claims a newly compiled Rocq or Lean endpoint for these exact tables.
No negative search here establishes minimality.

For reaching <=220, the only new machine-level leads from this intake are
the alternate continuation rows. The source counts and tag-sharing counts
are unchanged. Broader source rotations, additional contextual aliases,
simultaneous reductions, or a changed calibrated logical emitter remain
necessary research directions rather than a completed new construction.
