# Rechecking incoming actions under the phase invariant

No smaller machine was found. This bounded follow-up combines two existing
results that were not previously combined in this form: source50's complete
one-incoming-**action** ledger and the six excluded source guards from the
independent phase analysis. The previously completed ledger selects exactly three recipes for this
follow-up. The frozen table is unchanged.

The [continued-mutant follow-up](continuation/README.md) now records literal
100-million-move blank controls, complete startup-frame scans, and prepared
examples that retain data in shifted fields and spares. It also identifies the
stronger original-source relation `TW=p1+s1` at case8390. The original residual
obstruction below concerns that original program, while the changed tables
still need a new global interpretation and startup argument.

## Exact baseline and previous coverage

The actual checked permutation252 old-label table has SHA256
`939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713`;
canonical start0 table SHA256 is
`8dae0c2359aa8bf87d32543b9e53e1f87fe4716c016a4e2fd174bfe09e520797`.
The experiment uses old start64, dispatch96, halt254 and physical map
`[6,2,0,4,3,7,8,5,1]`. Source identities are recorded in `results.json`.
Mira-Cult's original program, Jeff's verification, Wade's backend,
mira-emmy's public253 reduction, the ProveIt permutation candidate and the
source27/source48/source50 diagnostic work retain their attribution.

Prior uniform, incoming-target, mixed-row and spare-suffix searches are documented
in [permutation252_minimization.md](../permutation252_minimization.md) and its linked notes. Source48/source50 already
completed all132,048 one-incoming action assignments, including writes, movement
and halt targets, with zero strict-checker survivors. Source50 is a reproduction
of that same family, not extra coverage. Its132,179-row compressed ledger includes
every recipe and first failed case. The two-incoming family remains partial.

The source-program mask analysis excludes guards
`8202,8203,8204,8358,8359,8360` from zeroRoot by an ordinary monotone invariant.
The existing503-recipe follow-up only revisited **target-only uniform folds**
first stopped at those cases. It did not cover movement-changing entry actions
under the restricted guard set. The mask invariant is not yet a Lean premise
for the altered machine: preservation would have to follow from a new simulation.
Untracked interior-frame probes were read as bounded scratch evidence only.
Their accelerations retain explicit box contracts and do not establish new
blank-start endpoints.

## Exactly three recipes need rechecking

`filter_journal.py` scans only the previously reproduced complete degree1 ledger.
Of132,048 recipes, just three have an excluded guard as their first failure.
Each deletes old204 and changes its sole external incoming row `(172,1)`:

| Replacement action | Archived first failure | Overlap with target-only family |
|---|---:|---|
| write1, **L**, target229 |8360| Direction-changing; absent from the503 target-only follow-up |
| write1, R, target77 |8360| Already target-only |
| write1, R, target252 |8360| Already target-only |

All other archived first failures are retained guards. Because every case is
started independently from its specified prepared source, removing six other
cases does not affect such an earlier retained failure. Thus these three are the
complete newly unlocked degree1 ledger slice for this exact guard-filter change,
conditional on the previously independently reproduced ledger. This is a new
**contract combination**, not three previously untested table recipes.

`probe.py` freshly checks the full8,391 baseline conditional affine cases and
replays all82,552 blank transitions with exact whole-tape comparison. It then
tries the three502-row/251-state mutants, preserving all55 box-support rows and
the blank start. Each passes two retained cases and stops at case8390,
path `1111111111`, source `CC 2`: the L229/R252 variants exhaust1,000 symbolic
rules, while R77 reaches a missing-row checker stop. None reaches a full8,385-case
pass, so none gets a candidate blank simulation. The whole control takes3.16s.
Fuel and missing-rule stops are not mathematical proofs of nonequivalence.

## The new direction-changing candidate returns the old wrong continuation

`literal_probe.py` executes twelve actual mutant prefixes: three actions, each
with `(n,k)` in`(1,0),(1,1),(2,0),(2,1)`, prepared source PC`1111111111`, gap40,
spares`[0,1,0]`, and logical registers`[0,0,0,0,n,0,k,0,0]`. These satisfy the
recorded source masks`[7,7,7,1,6,1,7,1,7]` but are not proved reachable from blank.

L229 reaches a complete clean dispatch frame after36 moves. R252 does so after34.
Both retain the entire primary file, spare suffix, exterior, head0 and gap40,
but return PC`1111110111` instead of the expected`11111111`. R77 actually halts
after6 moves on all four prepared inputs; its earlier symbolic missing-row stop
was therefore not merely a reason to increase fuel in this local comparison.
This says nothing about blank reachability of those prepared inputs.

`window.py` provides a stronger local observation independent of the sampled
register values. The L229 and R252 paths inspect only`[-11,6]`; from state96/head0
with window ones`{-1,0,1,2,3,4,5,6}`, they both return state96/head0 and make the
sole net tape change cell6:1→0, in36 and34 steps respectively. Every inspected
row/read/write is saved in `window-results.json`. Induction on that finite trace
extends the equal endpoint effect to **arbitrary exterior tape**. No box oracle
is used. This is an ordinary finite certificate, not a Lean theorem. The new
movement-changing recipe is a two-step detour into the already studied wrong-PC
continuation at this boundary.

The source50 obstruction is therefore still the concrete issue for the proposed
identity/finite-label original-residual interpretation. Its expected original
residual is`F(t,n,k)=(t,n+k,0)` while the returned-PC original residual is
`G(t,n,k)=(t+n,n+k,0)`, for n>0. Equal F-fibers have arbitrarily many G-values;
a fixed finite phase label cannot recover the lost initial n. One unbounded
saved natural would suffice. Those formulas describe **original register
residuals** and are not a claim about continued execution of these mutated
binary tables.

A different attempt here needs a changed continuation representation
with retained unbounded information, a stronger reachable relation, or altered
later execution that restores the semantic formula field. Merely skipping the
six impossible guards or allowing this incoming move flip does not supply it.
The experiment leaves global behavior of the mutants open and establishes no
state lower bound or new ZFC/PA endpoint.

## Reproduction

Run these maintained scripts in order from the repository root. Results are
written outside the checkout; the [publication record](../results/phase-entry-verification.json)
contains the saved outputs, source identities and finite traces:

```sh
uv run --no-project python -B Computability/BusyBeaver/Research/ZFC/phase-entry/filter_journal.py --repo /path/to/Proofs --output /outside/phase-entry
uv run --no-project python -B Computability/BusyBeaver/Research/ZFC/phase-entry/probe.py --repo /path/to/Proofs --output /outside/phase-entry
uv run --no-project python -B Computability/BusyBeaver/Research/ZFC/phase-entry/literal_probe.py --repo /path/to/Proofs --output /outside/phase-entry
uv run --no-project python -B Computability/BusyBeaver/Research/ZFC/phase-entry/window.py --repo /path/to/Proofs --output /outside/phase-entry
```

The scripts retain the baseline table identity checks and record their source
dependencies. Reproduction uses only Python and the checked-in data.
