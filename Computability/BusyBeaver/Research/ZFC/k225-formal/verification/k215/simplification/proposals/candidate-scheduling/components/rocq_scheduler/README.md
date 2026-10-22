# Constructive scheduler core: checked Rocq component

## Result and scope

`CandidateScheduler.v` proves a calculus-independent fairness theorem for a
partial deterministic step function, then a local completion theorem. The
concrete `L1_CompPerm.v` and `SeedPerm.v` instantiate it using the maintained
`EnumPerm.enum_step` and `step_pl`, preserving every old scheduler helper and
all four existing enumerator/seed endpoint statements.

The source baseline is ProveIt commit
`57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.
The numeric calculus, source program, seed state, command compiler and machine
transition tables are unchanged. The generic `run enum_step` is definitionally
equal to the maintained `EnumPerm.run`; no conversion induction is needed.

## Exact mathematical interface

For a state `s`, let `pending s` be its remaining-candidate rank and `index s`
its next candidate index. Every successful step must satisfy:

* At `pending s = 0`, the index increments by exactly one.
* At `pending s <> 0`, the index is unchanged and pending rank strictly decreases.

There is **no upper bound on pending rank after a refill**.

`seek target s` proves, constructively, that `index s <= target` implies either
halting from `s`, or a finite successful run to a boundary whose index is exactly
`target`. The proof is a nested strong induction, equivalently lexicographic
induction on `(target - index, pending)`; the implementation uses the equivalent
nonnegative offset to avoid subtraction in the induction invariant.

`complete_at target s` requires one target at least `index s` and a proof that
all boundary states at that target reachable from `s` halt. It concludes that
`s` halts. The adequacy contract is deliberately local to reachable payloads.
The stronger `cofinal_complete` corollary accepts a cofinal set of indices each
of which works for every boundary payload.

The order of quantifiers matters: a different killing candidate for each fixed
payload does not suffice if the scheduler changes payload while searching. The
companion report supplies a concrete checked counterexample. K215's actual
`program_halts Y L` has the stronger correct order: a fixed compiled word works
for every register tuple.

## Concrete instantiation

`step_pl` supplies `scheduler_advance` and `scheduler_descend`. All compatibility
wrappers (`drain`, `reach`, `reach_from`, `run_add`, and halting transport) reuse
the generic theorems instead of repeating candidate-drainage or reachability
inductions.

For a refutation, the unchanged compiler gives a word `L` with `blk 1 L`.
Set `Y = np seed` and

    N = P 3 (P Y (P 1 (enc_tail (L ++ SUFFIX)))).

The inherited Cantor inequalities prove `np seed <= N`. The existing
`program_halts Y L` and `run_first` discharge `complete_at` at this one index,
giving `enum_complete_from : forall seed, thm222 1 -> halts_from seed`.
Soundness still requires `Inv seed`. No unconditional equivalence for arbitrary
initial formula/cache values is asserted.

## Verification

The `checked/receipt.json` record binds every source and compatibility copy to
its SHA256. Eleven component modules plus a typed interface client were freshly
compiled with Coq 8.18.0 / OCaml 4.14.1. The only compatibility preprocessing is
`From Stdlib` to `From Coq` in build copies; the source originals are retained.
The client checks the four existing interfaces and two generalized interfaces;
six assumption reports are closed under the global context. A separate recursive
`coqchk` passes for the scheduler, `K215F.SeedPerm`, and the typed client.

This is a component check against the maintained K215 calculus/enumerator
sources. The complete physical-machine-to-ZFC closure has **not** been rebuilt,
and the pinned production lane uses Rocq 9.1.0 / rocq-stdlib 9.0.0. This packet
claims neither an internal PA proof nor an unconditional nonhalting theorem.

`integration.patch` passes `git apply --check` at the pinned commit. It updates
the three generated proof sources, their `rocqperm` producer templates,
`regenerate215.py`, and the extension manifest's hashes/compile order. Its exact
changed paths and hashes are in `patch_manifest.json`. It does not update old
historical verification receipts or claim they certify the refactored sources.

Reproduce from a checkout of the pinned repository, with Coq available:

```sh
python3 check_component.py --repo /path/to/ProveIt --out /tmp/fresh-scheduler-check
```

`--coqc` and `--coqchk` select explicit compiler/checker executables. The output
directory must be empty or absent. Dependencies are taken from the pinned
repository's production lane; its two retained K230 arithmetic dependencies
are read from the checked-transport packet already stored in that repository.
No precompiled project objects are reused.

## Source size, counted honestly

The old two concrete modules contain 410 lines / 18,100 bytes. The new clients
contain 386 lines / 17,009 bytes. The shared core adds 125 lines / 4,616 bytes,
so this single-lane compatibility-preserving prototype totals 511 lines /
21,625 bytes: an increase of 101 lines / 3,525 bytes. This is a proof-sharing
and interface improvement, **not a single-lane byte reduction**. It is most
useful when shared across several enumerators, as in the four Lean clients,
or combined with retiring unneeded helper wrappers after a consumer audit.
The older concrete numerical-rank proof remains the smaller option for a
standalone K215-only target when its stronger refill bound is acceptable.

## Relationship to earlier proposals

The `further-interface` report proposed extracting scheduling once; this packet
implements and checks that architecture. The `checked-transport/rocq_seed_rank`
packet already established a concrete rank argument and arbitrary-state
completeness. Those are credited as prior work. This contribution is the
reusable proof with weaker refill assumptions, the reachable-payload
`complete_at` interface, a current-source instantiation, compatibility wrappers,
and a synchronized reviewable patch. It does not claim a new ranking method.
