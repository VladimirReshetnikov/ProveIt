This bounded experiment checks context-dependent state deletion in the frozen
permutation252 table. The table and its full original frontend are unchanged.
The source is attributed to Mira-Cult, Jeff, Wade and mira-emmy's public253
reduction; this experiment uses the independently found physical permutation
`[0,3,4,5,8,1,6,2,7]`. The old-label table SHA256 is
`939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713`.

All55 register-box support rows, old dispatch96 and blank start64 are fixed.
Among eligible deletions,46 states have exactly two incoming rows from other
states. States with only one external incoming row add no new independent
incoming assignment to the preceding uniform-fold family. Higher incoming
degrees are outside this experiment. The previous public253 context experiment only tried
old107 with its two incoming continuations; it did not use this frozen table.

The baseline passed all8391 strict affine cases, with the actual new logical
to physical map `[6,2,0,4,3,7,8,5,1]`, and the exact82552-step blank run reached
the whole frozen target frame: old96, head2, emptyPC, gap40, nine zero primary
registers and65 spares, of which only index8 is1. Every cell of the77-one tape
was compared. The four symbolic register-box summaries remain mathematical
diagnostic contracts; no modified table is given a Lean proof by this search.

For each of the92 incoming rows, the driver retained the old state and tried
each of251 other existing working states as the new target. Baseline literal
table accesses identify the affected cases. Cases that never read the changed
row retain the same deterministic symbolic trace; unchanged box interiors are
covered by the55 fixed rows. Targets passing the affected cases form that
row's diagnostic domain. The driver then combines the two domains, removes
the deleted state's rows, and checks the joint candidate. A joint survivor
must pass all8391 cases before any literal blank run begins.

The completed run screened23092 individual assignments in83018 affine checks.
Six of92 incoming rows had a nonempty domain, containing18 accepted target
choices in total. Only old42 had two nonempty domains:

| Incoming row | Passing targets with old42 retained |
| --- | --- |
| old30/read0 |39,70,72,93,169,201 |
| old57/read0 |21,25,49,53,173 |

All30 joint deletions failed their first affected affine case by exhausting
the1000-rule limit. There were no full-recheck survivors and no candidate
blank runs. Total elapsed time was34.96seconds. The detailed journal is
2394307bytes with SHA256
`328b0080df466d47bc2cdd983fe9c3f4afb301e8c72471a8bb52651fba1db4d8`;
the permanent JSON retains every domain and every first-failure case in
destination order.

This is a sufficient-domain family. It excludes jointly compensating
assignments that fail when made separately, all deletions with more than two
external incoming rows, write/move edits and protected register-box changes.
Fuel or unsupported symbolic rules are finite diagnostic rejections; they
do not prove nonhalting, impossibility of deletion, or minimality.

Reproduce offline from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/permutation252_context_search.py \
  --output Computability/BusyBeaver/Research/ZFC/results/permutation252-context-search.json \
  --scratch /tmp/zfc-permutation252-context-search --seconds 120
```

The run uses no Lean or Coq build, network access, or changes to the frozen
machine.
