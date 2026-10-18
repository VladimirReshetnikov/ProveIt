# Further state elimination after the register permutation

The register permutation turns the earlier runtime-only 252-state fold into a
machine with a complete clean blank bootstrap. Three subsequent diagnostic
families tested whether another state could be removed from that exact table.
None produced a runtime survivor.

| Family | Complete tested recipes | Candidate affine checks | Result |
| --- | ---: | ---: | --- |
| Uniform replacement | 55,471 | 127,868 | No survivor |
| Separate incoming-path replacement | 23,092 individual assignments, then 30 joint deletions | 83,018 individual checks, then 30 joint checks | No survivor |
| Mixed read-0/read-1 merge | 49,462 | 717,306 | No survivor |

Each run first independently checked all 8,391 original conditional cases
under the new physical register map and replayed all 82,552 blank-tape moves.
The complete endpoint tape was compared, including every spare block. All
candidate families preserve the 55 rows supporting the register-box proofs.
No modified table reached the required full runtime pass, so no modified table
was given a blank-tape run. These are bounded diagnostics, not proofs that a
251-state machine is impossible.

The [uniform fold](permutation252_fold_search.md) replaces every incoming
reference to a deleted state with one existing state. The
[incoming-path experiment](permutation252_context_search.md) lets two incoming
rows choose different continuations. Its domains require each replacement to
work separately while the old state remains, so jointly compensating changes
are outside that experiment.

The third family combines the read-0 action of one state with the read-1
action of another. If states `q` and `r` merge into `r`, every target `q` is
redirected to `r`, one row of `r` is replaced by the corresponding original
row of `q`, and both rows of `q` are deleted. This includes the redirect in the
copied row itself. It differs from either uniform replacement, which retains
both rows of one state. Read-0 and read-1 contexts can potentially permit such
a merge even when neither wholesale replacement works.

The search excludes deletion of the dispatcher or a protected row's source
or target. It also excludes modifying a protected row or copying an action
into the dispatcher. The dispatch state keeps its label, but its outgoing
targets undergo the same redirection as other rows when old110 or old111 is
deleted. Symmetric label choices are represented once when both states are
eligible for deletion. A mixed row identical to the retained row is skipped:
it is already a uniform-fold recipe. Affected cases include both rows of the
deleted state and the modified retained row. Any survivor must then pass all
8,391 cases before a literal blank run. The complete family took 109.59 seconds
with a 1,000-rule affine bound and had no survivors. The earlier source-25
mixed-merge experiment used the public253 table; its negative results were
not assumed to transfer to arbitrary mutated continuations of this table.

Reproduce the mixed-row diagnostic from the repository root:

```sh
uv run --no-project python -B \
  Computability/BusyBeaver/Research/ZFC/permutation252_mixed_merge_search.py \
  --output /tmp/permutation252-mixed-merge.json --seconds 180
```

The saved [record](results/permutation252-mixed-merge-search.json) includes
every recipe and its first failing case, bounds and source identities. A fuel
exhaustion or unsupported symbolic rule is a failure of this diagnostic;
it is not a proof that the altered machine computes a different function.
The symbolic register-box contracts remain explicit. These experiments do not
add a kernel proof for any altered table.

Attribution is inherited from the frozen candidate: Mira-Cult's original
machine, Jeff's verification, Wade's compiler and mira-emmy's public253
reduction. The diagnostic executor is from attributed closure-kernel source
27. The new searches operate on the separately frozen ProveIt permutation
candidate and do not modify it.

Two further experiments broaden the boundary. The [lazy incoming-target
search](permutation252_lazy_context_search.md) permits compensating reroutes
and records an explicit unfinished frontier; its entire branch/prune partition
was independently replayed. The [spare-suffix box experiment](permutation252_spare_fold_search.md)
tests7,279 previously excluded folds with arbitrary valid spare values in
finite literal box samples; no candidate survives its subsequent conditional
instruction screen. Neither experiment changes the frozen candidate.

The later [phase and incoming-action follow-up](phase-entry/README.md) combines
the six excluded source guards with source50's complete one-incoming-action
ledger. Only three recipes need another check. One changes the movement
direction and was outside the earlier target-only follow-up; a literal finite
trace shows that it reaches the same wrong continuation in two extra steps.
None passes the retained guard screen. The result narrows this particular
combination of searches without proving a global lower bound.

