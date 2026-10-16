The bounded fold search on the actual public 253-state machine found no new
blank-start candidate. All 504 folds of old states 5 and 84 preserve the 55
protected register-box rows. Exactly one passes all 8,391 affine instruction
cases: the already known fold 5→64. Its mapped blank start fails to reach the
complete public bootstrap frame through 2,000,000 steps. This is a finite search
result, with no global minimality or consistency-equivalence claim.

The machine is mira-emmy's attributed PR20 reduction at
`0d544f2a2e3c18f12278441a74b7879f31cbe856`, derived from Mira-Cult's original
machine and Jeff's verification, using Wade's TMBuilder framework. The public
literal table is retained as
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/04-machine-machines-zfc_253.tm`;
its SHA-256 is
`84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`.
The search uses the original labels to preserve the published affine checker
interfaces. It checks the exact table identity against the four-edit
reconstruction of the original 254 machine. Old start 5 is compact state 0;
old dispatch 96 is compact state 33.

The earlier experiments cover different tables or different contracts:

| Earlier experiment | Actual input and result | Relevant boundary |
| --- | --- | --- |
| Project `baseline-254-audit.json` | Original 254 table; all 254 graph-reachable; singleton step quotient; 64,262 ordered radius-4/64-step macro pairs, no merge | Its local-window search was not run on public 253. The separate Lean `NoQuotient254` theorem also concerns literal 254 only. |
| Source 04 `engineering/context_search.py` | Actual public 253 reconstructed in old labels; 223 removed states ×252 destinations =56,196 folds; no affine survivor | Lines 138–141 exclude old 5 and84, plus box/interface states and dispatch. Lines 149–155 redirect all incoming edges, filter affected cases, then recheck all cases. No per-fold successful boot follows from zero runtime survivors. |
| Source 04 `runtime252_audit.py` and `bootstrap_search.py` | Known fold 5→64 of public253; 8,391 runtime cases pass, but all252 blank starts fail the advertised bounded initialization checks | A prepared/runtime-only body. The current search repeats this one known fold as a regression. |
| Source 09 decoder search | Decoder256, 57,375 folds; no affine survivor; separate C++ bootstrap searches and eleven successful folds of decoder267 down to256 | Uses a changed decoder and its original 264,982-step bootstrap, not the public253 bootstrap. |
| Source 20 `reproduce_decoder255_folds.py` | Decoder255 with the public initializer-sharing idea; 57,150 folds, no affine survivor; fixed table has a separately checked 606,702-step full boot | Its decoder has202 nodes and gap≥41. These results cannot be read as folds of public253. |

Source04's protected source-state list differs from the later conservative
box boundary: it excludes84 but allows4. This does not create a successful
candidate in that negative search. A positive result using unchanged box
summaries must instead preserve every protected row after all incoming-target
rewrites. The present search enforces exact equality of all55 pairs from the
source09/source20 `BOX_PAIRS` convention, including both rows of state4 and
excluding only3/read0. Neither5 nor84 is a box state, and no protected row
targets either; all504 new-family folds therefore meet this stronger boundary.
Of these,503 were not covered by source04's search or its separately known
5→64 experiment.

The driver reuses source04's attributed `program_sites`, `cases` and `executor`
helpers, copying the helper modules to a new scratch directory before import.
The underlying affine executor is the unchanged attributed upstream
`symexec.py`. It uses existing register-box summaries; this Python search
supplies no new soundness proof for those summaries or for the executor.
No manifest checks, network fetch, Coq or Lean build is performed.

For each deleted state p∈{5,84} and each other working state q, the candidate
removes p's two rows and redirects every target p to q. If p is the start, the
start is also mapped to q. The candidate has252 working states,504 rows and
the original separate halt label254. The original labels need not form a
contiguous range. The driver checks target closure and the 55 protected rows
for every candidate and records its exact rewritten rows and start mapping.

The baseline first passes all8,391 cases for the literal6,459-row public RM
program, both decrement branches, at arbitrary affine gap≥40. It independently
reproduces the literal public blank bootstrap in312,975 binary steps. For the
candidate filter, only baseline cases whose explicit table execution visits p
need rechecking: the other cases retain the same transitions and unchanged
box summaries. Every survivor then receives a full8,391-case recheck. The
recorded baseline affected-case counts are744 for p=5 and8,390 for p=84.
The default limit is1,000 affine executor iterations per case.

Only an affine survivor receives the independent literal blank-tape run.
Success requires old dispatch96, absolute head−17 and equality of the entire
finite set of178 one-cell positions, with all other integer cells blank.
This is the complete `Boot253.bootTarget253` frame: the nine primary physical
values are `[0,2,0,0,0,0,5,0,0]`, followed by158 spare blocks, whose indices2
and8 have value1. The marker is at−18 and the header at23. The check neither
ignores spare data nor compares only a finite prefix of the tape.

The initial candidate boot limit is313,000 steps. An affine survivor still
running at that limit receives an extended2,000,000-step run, matching the
older source04 diagnostic cap: redirecting paths can change startup duration.
The target may be reached at any time within the limit; its time is not forced
to312,975. No first-dispatch-arrival claim is made. Optional small-configuration
cycle detection only excludes this target when the entire observed cycle
prefix has fewer than178 ones, so a translated repeat cannot conceal a later
translation into the target frame. No such cycle certificate arose here.

The default replay passed in about7.3seconds:

| Outcome | Count |
| --- | ---: |
| Baseline affine cases passed | 8,391 |
| Candidate row-protection checks passed | 504 |
| Candidates rejected by the affine checker | 503 |
| Of those, affine fuel exhausted | 303 |
| Full affine survivors | 1 (5→64) |
| Exact blank bootstrap survivors | 0 |

The sole survivor remains active at313,000 steps in old state10, head30,
with243 ones. At2,000,000 steps it is in old state95, head750, with646 ones.
This is a bounded failure to match the target, not a translation-cycle proof
or a proof that no later compatible frame exists. Likewise, affine fuel
exhaustion does not refute a candidate's semantic correctness. The other
checker errors are failures of the advertised affine contract, not a lower
bound on arbitrary equivalent machines.

Run from any working directory with the repository available:

```sh
python /path/to/Proofs/Computability/BusyBeaver/Research/ZFC/public253_fold_search.py \
  --output /tmp/public253-fold-results.json
```

`public253-fold-results.json` records all504 candidates, every first failing
case and reason, start mappings, row-protection checks, source pins, limits,
baseline results and both finite survivor runs. The driver rejects optimized
Python because its checked contracts use assertions. Its source hash is
recorded for reproducibility; the literal table/program pin checks are
functional input-identity checks rather than bulk manifest verification.

A different experiment, unrun when this fold search was recorded, applies `audit_tm.py`'s conservative
local-window macro certificate to public253. Read-only radius4 setup reaches
31,909 abstract configurations, including all253 working states, giving
63,756 ordered state pairs. Old5/compact0 has128 possible windows and
old84/compact32 has79. That check admits contextual positive-length matching
blocks on both sides, rather than demanding the exact RM dispatch contract.
It could therefore test a different sufficient condition on candidates
rejected here. Any survivor would still need an independently checked
certificate and a Lean proof connecting the certificate algorithm to the
actual blank machine. A larger search, mutation of box contracts, or repair
of the initializer has not been run as part of this result.

The subsequent [local-window macro search](public253_macro_search.md) completed
all 63,756 pairs at both radius 4 and radius 5, with 64 steps per side and no
certificates. Radius 5 removed 447 projected radius 4 windows across 26 states.
Its negative result has the same limited scope: it does not establish a lower
bound for machines preserving blank-start halting behavior.

Batch151 source25 now supplies an independently replayed complementary
symbol-wise fusion family: 148,368 candidates, 55 protected rows, zero passing
affine contracts at fuel1000. Its 132,389 fuel and 15,336 abstraction-limit
outcomes remain unresolved; 643 candidates halt unexpectedly. The complete
ledger matches. Its inherited 56,196 direct-fold family was also rerun and
still excludes old5/84. Thus it does not contradict this experiment's known
5→64 runtime survivor. Source24 separately gives a complete finite exact-step
quotient obstruction for literal253, not a blank-equivalence lower bound.
See the host's `intake-151-source-25-machine.md` and `intake-151-source-24.md`.


## Batch 152 independent extensions

The host's sources 26–34 (arrival `da6dabcd89`) reproduce larger bounded
families of direct folds, mixed fusions, incoming-edge rewrites, row mutations,
grammar rotations and initializer reuse. Their different 53/55 protected-row
interfaces and finite-fuel contracts are retained in their dossiers. A runtime
survivor is not a blank-start certificate; fuel and abstraction failures remain
unresolved. The searches do not establish global minimality.

Source 27 supplies a four-row 253-state variant with the same complete
bootstrap tape at 312,935 steps instead of 312,975. Its ordinary same-halting
argument and independent 2,981-pair register certificate are useful controls,
but do not remove a state or supply a new Lean runtime theorem. Source 34's
shared-initializer quotients save states on larger clean layouts, with best
309 among its listed controls; their differences cannot be subtracted from
public253. A full replay of source 33's broader final protected-basis search
finds 268, matching the prior complete-word control. The table and recipe are
preserved separately as `data/intake-152-source-33-protected268-*` in the host.
