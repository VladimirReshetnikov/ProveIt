# Machine engineering findings at the pinned ProveIt source

Input repository: `VladimirReshetnikov/ProveIt`, commit
`de047657e193ec605e930eaf149a44a38031820b`.

This work establishes no new sub-253-state consistency machine. It contributes
a measured comparison of the new exact fixed-point schema with EPSC, and a
broader diagnostic state-fusion search around the existing 253-state machine.

## 1. The existing 253-state benchmark

The attributed machine is Mira-Cult's 254-state design, reduced by mira-emmy
in the open upstream PR <https://github.com/jeff87654/busy-beaver/pull/20>, head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`. Its exact 253-state literal table
has SHA-256
`84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`.

The upstream result concerns external equivalence of blank-tape halting and
finite classical refutation in its stated ZF/ZFC presentations. The README and
PR explicitly refrain from claiming a formalized internalization. A claim that
ZFC proves the arithmetized target equivalence needs an additional metatheoretic
argument or proof translation. Closed Coq assumptions alone do not supply that
translation.

The new finite checks reproduce the 253-state machine in the baseline's old
labels: delete state 8 and change exactly `(3,0)`, `(5,0)`, `(5,1)`, `(49,1)` as
in the upstream generator. The exact blank bootstrap at time 312,975 reaches
old dispatcher 96 at head -17 with 178 one cells, agreeing with the cited
upstream bootstrap endpoint. This is prior work reproduced, not a new machine.

## 2. New symbol-wise fusion experiment

The earlier repository search considered direct redirection of a deleted state
to an existing state with that existing state's rows unchanged. The present
family additionally allows the retained state's read-0 and read-1 transitions
to be selected independently from the two original states. Incoming references
to the deleted state are then redirected to the retained state. Choices that
are unchanged direct redirections are omitted. Some remaining choices are
equivalent, after renaming, to earlier direct redirections; the candidate count
must not be presented as that many entirely new semantic transformations.

All 55 conservative register-box transition pairs must remain byte-identical.
Deleting any protected source or protected successor is prohibited, and the
dispatcher remains available. This leaves 222 eligible source labels. The
same pinned affine executor passes all 8,391 baseline instruction cases.
Candidates are screened on affected cases, with 1,000 units of affine-executor
fuel per case. A survivor would be checked on every case and then on the exact
finite blank bootstrap.

| Recorded outcome | Count |
|---|---:|
| Deduplicated candidates actually checked | 148,368 |
| Additional choices excluded by protected-row preservation | 18,405 |
| First failed check: fuel exhausted | 132,389 |
| First failed check: unsupported symbolic operation | 15,336 |
| First failed check: unexpected halt in a nonhalting instruction case | 643 |
| Candidates accepted by all affine obligations | 0 |

The fuel failures and symbolic-abstraction failures are **unresolved candidates
under this procedure**, not proofs of semantic inequivalence. Even an unexpected
halt in an arbitrary instruction configuration disproves that universal
instruction contract; it does not by itself disprove equivalence from the blank
tape. No minimality claim follows. The experiment mainly identifies why this
specific extension of the existing checker supplies no new positive certificate.

`fusion/rejection_ledger.csv.gz` records every tested candidate's deleted and
retained labels, branch choices, first failing case index, reason and detail.
`fusion/fusion_results.json` contains the full census and source pins.
`fusion/pair_usage.json` is the baseline affine transition-usage inventory.

Reproduce, with a checkout at the pinned commit and ordinary Python 3:

```sh
python3 lab/fuse_states.py --repo /path/to/ProveIt --out /tmp/zfc-fusion-replay
```

Elapsed time and gzip metadata can differ on reproduction. The search's logical
result, source labels, fuel bound and first-failure census are the relevant
outputs. The two copied support modules in `lab/` retain their original source
headers and are attributed to the repository's source-04 engineering report.

## 3. Exact fixed-point normal form: actual compilation costs

The new schema is EFPC, with all auxiliary variables fresh in ordinary syntax:

\[
\begin{split}
\operatorname{LB}(\rho)&:=\forall x\exists b\forall y\left(
 \rho(x,y)\to\forall z(z\in y\to z\in b)\right),\\
\operatorname{EFPC}(\rho)&:=\operatorname{LB}(\rho)\to\exists c\forall y\left[
 y\in c\leftrightarrow\exists x\bigl(\rho(x,y)\land
 (\operatorname{Empty}(x)\lor x\in c)\bigr)\right].
\end{split}
\]

The code uses the existing distinguished input/output labels 0 and 1, and
the current matrix code as the auxiliary binder label. Its exact syntax is in
`measure_fixedpoint.py`, function `formula`. This comparison retains GEN, all
eight original logical rows, both atomic vacuity rows, all equality constructors,
base-four coding, proof enumeration, and the original cleanup/freshness tail.
Only the theory expression and the bracketing/sharing of closed emission words
are varied. Retention of these components is not a proof that the new emitted
code calculus has the desired calibration.

The finite experiment used eight logical-row orders, two bundle associations,
two Re-Pair weight exponents (4 and 8), and seeds 0 through 63: 2,048 candidates
for each formula presentation. There are two EPSC presentations and eight EFPC
presentations (the three binary choices exchange the disjunction arguments,
the conjunction arguments, and the biconditional arguments). Every candidate
was compiled and ranked by its **actual generated working-state count**.

| Presentation | Theory emission macros | Full AX macros | Best measured working states |
|---|---:|---:|---:|
| EPSC, support first | 49 | 162 | 270 |
| EPSC, closure first | 49 | 162 | 270 |
| EFPC 000 | 57 | 170 | 272 |
| EFPC 001 | 57 | 170 | 272 |
| EFPC 010 | 57 | 170 | 271 |
| EFPC 011 | 57 | 170 | 272 |
| EFPC 100 | 61 | 174 | 274 |
| EFPC 101 | 61 | 174 | 274 |
| EFPC 110 | 61 | 174 | 273 |
| EFPC 111 | 61 | 174 | 273 |

The support-first EPSC control reproduces the previously supplied 270-state
table exactly, SHA-256
`54d631fa31f36b02dd41634de8cadeb2cc8fcfae4bc75fea8812af0794b2a136`.
The winning EFPC expression is the formula displayed above. Its table has
271 working states, 542 transitions, start state 0, blank symbol 0, and
uncounted terminal state 271. Its SHA-256 is
`f00ae2f3fda5b191793d4a7542bcb3a4a4ee7d5ec1113fdff96f859ed52dfbea`.
The winning recipe keeps logical rows in order 1 through 8, takes the bundle
`And(And(EFPC, equality_vacuity), membership_vacuity)`, and uses Re-Pair alpha 4,
seed 39. It has 209 decision states and 62 framework states.

An independent repository checker validates its 4,028-pair finite operation
bisimulation: 2,310 increment sites, 1,717 decrement sites and one halt site,
with 5,744 successor comparisons. The source is the naive 274-node emission
program for the **same EFPC formula word**, and the target is the 209-node
compressed program. This certificate proves no equivalence to the original
SIR theory and no binary compiler or initializer theorem. Independent literal
parsing confirms all ten emitted winners are total, transition-closed, and have
every counted state graph-reachable.

The useful quantitative finding is that this stronger mathematical normal form
costs one state more than the best EPSC control in the selected family. Its
repeated subexpressions recover most of the eight extra emission macros, but
there is currently no state saving to advertise.

The framework cost across the 20,480 compiled candidates ranges from 61 to 66
states. It must not be replaced by a presumed constant of 62. This is why the
final search measures literal tables rather than ranking only formula trees or
decoder DAGs. These are finite-family minima, not lower bounds on compilers or
machines.

Reproduce all 20,480 candidates:

```sh
python3 measure_fixedpoint.py --repo /path/to/ProveIt --out /tmp/efpc-replay --seeds 64
```

`fixedpoint/results.json` includes every distribution and winning recipe.
The ten subdirectories include full literal tables, named tables, source and
target DAGs, grammar words, state labels and operation certificates. The main
report need only package the `EPSC_s` and `EFPC_010` winners plus the aggregate
results if archive size matters.

## 4. Remaining route to the user's target

For the new schema, the outstanding work is the emitted-code soundness and
completeness interface (including exceptional codes and parameter gates), a
literal compiler/initializer simulation, and internal ZFC proof of the resulting
arithmetized halting equivalence. The ordinary low-code cases 0 and 1 can be
checked for EFPC plus irreflexivity, but that does not supply these broader
interfaces. The 271-state artifact is therefore an engineering control for the
theorem-level proposal, not a newly verified consistency machine.

For beating 253, the measured alternatives require either substantially better
backend sharing, a new complete small logical kernel, or a successful invariant
certificate for a stronger machine transformation. Reducing a theory's displayed
axiom count alone does not justify a machine-state prediction.

## Attribution and licenses

The compiler is Andrew James Wade's 2025 MIT No Attribution implementation,
distributed by the pinned ProveIt snapshot. Grammar compression, the full-equality
EPSC frontend and operation checkers are retained prior work in the repository's
source-08 and source-14 reports. The existing 253-state machine and its proofs
are attributed above; no authorship of that machine is claimed here.
`LICENSE.ProveIt` and `LICENSE.wade` accompany these experiments. No new blanket
license supersedes third-party rights or notices.
