The actual public 253-state machine has no single-state deletion certified by
`audit_tm.py` at radius 4 or radius 5 with at most 64 steps on each side. Each run
checks all 253×252=63,756 ordered pairs. This is a finite negative search result,
not a lower bound on equivalent machines.

The input is mira-emmy's public PR20 reduction, derived from the Mira-Cult
machine and Jeff's verification using Wade's TMBuilder framework, at commit
`0d544f2a2e3c18f12278441a74b7879f31cbe856`. Its literal table is
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/04-machine-machines-zfc_253.tm`,
SHA-256
`84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`.
It has 253 working states, 506 rows, blank symbol 0, start 0 and separate terminal 253
on a bi-infinite tape. The exact table identity was checked. The auditor source
was unchanged; no external executor, register-box summary, manifest audit,
Coq build or Lean build was used.

| Radius | Known cells | Abstract configurations, including terminal | Ordered pairs | Maximum steps per side | Certificates | Elapsed seconds |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 4 | 9 | 31,909 | 63,756 | 64 | 0 | 0.690 |
| 5 | 11 | 102,061 | 63,756 | 64 | 0 | 1.319 |

Both abstractions include all 253 working states and both read symbols at every
working state. Thus neither run can discard an entire transition row as
abstractly unreachable. The auditor's 11 regression tests passed with the
radius 4 run. Its other checks also give 253 graph-reachable working states,
253 exact-step equivalence classes after 13 refinement rounds, and no startup
reuse certificate. Those Python checks supply no new Lean theorem.

The radius 5 followup was selected after computing its reachable windows,
before running its pair search. Projecting each 11-bit window to its central
9 bits removes 447 radius 4 patterns across 26 states. The projection is
`(pattern >> 1) & 511`. It therefore supplies tighter information
than merely adding two arbitrary exterior bits. Compact state 0, formerly
old 5, has 128 radius 4 windows and 384 radius 5 windows; compact 32, formerly old 84,
has 79 and 175. The complete setup counts and removed patterns are retained in
the evidence. No radius 6 run or larger parameter grid was performed.

For each ordered pair p≠q, the candidate removes p and redirects every target
p to q, including the start when p=0. The abstract graph starts from the blank
window. Every shift admits both values for the newly exposed exterior cell,
so it overapproximates actual blank-run windows. For every abstract window
possible at p, the auditor locally runs the original from p and the candidate
from q. Each side must take a strictly positive number of steps, at most 64,
and may not read outside the original known window. A nonterminal match
requires the same control after mapping p to q, the same relative head and the
same entire known window. All writes remain within that window, leaving the
unknown exterior unchanged. Two terminal configurations may match without
matching their final tape or head, since the property being preserved is
halting. The positive-step requirement prevents an infinite run from being
matched by zero progress. The mathematical argument for this sufficient
criterion is documented in the auditor; the Python implementation has not
been verified in Lean.

This search differs from the affine instruction-contract searches in
`public253_fold_search.md` and the source 04/source 25 bundles. It uses literal
local transitions and matching blocks rather than the 6,459-row register
program, protected box summaries, or the complete 312,975-step bootstrap
frame. It also differs from the radius 4 audit of the original 254-state table,
the exact-step quotient obstructions for literal 254 and 253, and the changed
decoder 255/256 fold families. All ordered pairs here include removal of the
public start 0 and old 84/compact 32.

A failed local certificate can arise from an abstract window that the actual
machine never reaches, a need to inspect farther exterior cells, or a match
requiring more than 64 steps. These runs do not refute an arbitrary deletion's
halting equivalence and do not exclude any other 252-state construction.
They supply neither a new machine nor a new ZFC consistency calibration.

Reproduce from the repository root, changing 4 to 5 for the second run:

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/audit_tm.py \
  SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/04-machine-machines-zfc_253.tm \
  --expected-sha256 84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95 \
  --expected-states 253 --expected-halt 253 \
  --source-commit 0d544f2a2e3c18f12278441a74b7879f31cbe856 \
  --source-url https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/machine/zfc_253.tm \
  --window-radius 4 --macro-steps 64 --self-test \
  --output /tmp/public253-radius4.json
```

`results/public253-macro-search.json` retains both complete auditor outputs,
the exact commands, timings, source identity and the radius 5 setup snapshot.
The snapshot's `radius5_merge_search_run: false` records its status before the
authorized followup; the surrounding completed-run evidence records that the
followup subsequently finished. Original logs are retained under
`/tmp/zfc-public253-macro-6uctpk7a`.
