# CM215: conditional origin markers and ZFC consistency

**Result: an explicit, newly verified 215-working-state binary Turing machine.**
The packet also supplies a new two-head transfer calculus and compiler, plus
precise negative results for two tempting implementation shortcuts. It does
not claim a verified 214-state machine.

The principal ordinary mathematical theorem is

```
ZFC proves: not Halt(CM215, blank) <-> Con(ZFC).
```

The proof transfers the pinned accepted K215 calibration through a new exact
whole-tape simulation. The main new theorem holds on **every initial binary
tape, starting in control state 0**, not merely on the calibrated blank run.
It does not assert equivalence for arbitrary initial controls inside the
modified fragment. No new Lean or Rocq kernel-compiled endpoint is claimed.

Read **`report.pdf`** for the complete contribution, ordinary proofs, evidence
boundaries, and follow-up problems. **`report.tex`** and **`sections/`** contain
all of its editable LaTeX sources.

## The exact machine

The model has one two-way infinite tape, alphabet `{0,1}`, blank symbol 0,
initial head position 0, and only L/R moves. The count includes initialization
and excludes the separate halt. Each `.tm` row is

```
state  read-symbol  write-symbol  direction  next-state
```

The header `#! start 0` identifies the initial state.

| File | Working labels | Start | Dispatcher | Halt |
|---|---|---:|---:|---:|
| `machine/marker215.native.tm` | Preserved native labels | 0 | 84 | 254 |
| `machine/marker215.tm` | 0 through 214 | 0 | 83 | 215 |

There are exactly **215 working states and 430 transition rows**. The two
files are related by the complete bijection in
`machine/canonicalization.json`. All working states are reachable in the
finite transition graph; this does not claim all occur on the blank run.

| Artifact | SHA-256 |
|---|---|
| Native CM215 | `e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252` |
| Dense CM215 | `1f4f084f7293e2b042d5746039f793ff72ed429083b504970c939a5515e666cf` |
| Unchanged source | `17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba` |

## The new decoder transformation

Old decoder roles 52 and 176 have the same read-one transition but different
read-zero destinations. Their origin can be recovered from the bit to the
left **when the current cell is zero**. The otherwise troublesome incoming
path `189/1 -> 156/1 -> 176` necessarily reads a one at 176: its first edge
writes one into the cell to which its second edge returns.

Consequently the two old roles can share new state 52. Physical label 176 is
reused as a predecessor-marker selector, with existing providers 185 and 129
implementing the two continuations. The following six native rows change:

| State/read | Parent | CM215 |
|---|---|---|
| 52/0 | 0 R 154 | 0 L 176 |
| 156/1 | 1 R 176 | 1 R 52 |
| 165/0 | 0 R 176 | 0 R 52 |
| 176/0 | 0 R 168 | 0 R 185 |
| 176/1 | 1 R 150 | 1 R 129 |
| 193/0 | 0 R 176 | 0 R 52 |

All other native rows are unchanged. With `phi(176)=52`, every old step is
simulated by one or three new steps, with identical complete tape and head
at each simulation boundary. If `z` of the first `t` old transitions use
52/0 or 176/0, their exact new duration is `t + 2*z`.

This is a state-neutral role merger, giving a concrete possible next target:
share the new selector with an existing compatible role to save a state.
The present table retains 215 states. It is not a renaming of the parent:
its L/R row counts are 83/347 instead of 82/348. A reproducible rooted graph
comparison, also allowing global tape reflection, finds no match among the
77 distinct literal 215-state tables retained in the comparison corpus.

## Verification and its scope

The fresh complete symbolic runtime run on the exact new table establishes:

| Quantity | Result |
|---|---:|
| Primitive source occurrences | 4,751 |
| Distinct source subtrees | 202 |
| Guarded primitive cases | 6,176 / 6,176 passed |
| Symbolic proof rules | 1,701,542 |
| Transition row coverage | 430 / 430 |
| Minimum duration constant | 6 |
| Complete blank startup | 95,714 transitions |

The primitive contracts quantify arbitrary natural primary-register values,
an arbitrary natural gap, a nonempty arbitrary finite spare list, and the
whole tape with blank exterior. Unary scan and list inductions justify the
unbounded contracts. This is an ordinary mathematical checker, not a
proof-assistant kernel.

An independent audit replays the entire blank trace in both numberings and
parses the complete terminal tape: native dispatcher 84, head -8, header 57,
gap 1, logical registers `[4,0,0,0,0,0,0,0,0]`, forty unit spares, and 95
one-cells. It also audits the ordered saved case inventory and every covered
row. Relative to the accepted parent, 5,632 durations are unchanged, 128
increase by 2, and 416 increase by 6; all variable coefficients and motions
agree. Thus 544 quantified cases actually use the changed mechanism.

The independent saved-record audit is not a second universal induction
implementation. The new whole-tape theorem, the fresh universal runtime, and
the finite audits are separate, explicitly stated evidence layers.

## Reproduce from a clean extraction

Python 3.10 or newer and the standard library suffice. Keep assertions enabled.
From the unpacked packet root:

```sh
python3 -B verify.py
```

This verifies every root-manifest hash, rebuilds both exact tables in a
temporary directory, checks all finite hypotheses of the marker simulation,
audits the saved runtime and independent blank replay, repeats the 77-table
comparison, rebuilds the two-head source variants, runs their finite compiler
corroborations, and independently reproduces both negative examples. It
does not modify the shipped machine or evidence, run an optimizer, or need
network access. The completed packaging run is recorded in
`evidence/reproduction.json`.

To also rederive all 6,176 quantified runtime cases, use a new or empty path:

```sh
python3 -B verify.py --runtime /absolute/path/to/fresh-runtime
```

Allow several minutes. The driver checks the final report's status, case
counts, failure list, input hashes, and checker hashes; process exit alone is
not treated as proof success. The initial fresh run and its complete
compressed case/startup records are already included in `machine/runtime/`.

To compile the report:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

## Formalism contribution: two-head transfer

`research/stride2/` develops a three-command numerical proof-search language.
It retains MP and the dominated AX emitter but replaces transfer with a
command having successful return

```
(t, [x,y;S], d, h) -> (h, S, d, y).
```

Its composite implementation is `DROP;NIP;NIP;NIP`, which halts exactly when
`h=1`, `t=1`, or `x=1`. The direct implementation clears top, copies cache
into top, and executes `NIP;NIP`; it has the same successful return and only
the `h=1` or `x=1` guards. Their command bodies contain 104 and 61 primitive
occurrences respectively. Neither source is presented as an allocated
215- or 214-state binary machine.

The ordinary proof supplies total PUSH and DISCARD macros, all row selectors,
generalization, modus ponens, and a strong compiler preserving an arbitrary
raw underlying stack. Deliberate successful `MP(0)` operations supply parity
padding; the zero implication alias is treated explicitly. A separate
all-natural diagonal proof establishes a conservative deficit of at most
two stack heads for the increasing scheduler. Ten theorem heads above an
arbitrary tail therefore leave permanent margin eight. These facts establish
refutation-equivalence with the inherited calculus at a matched source
interface.

Five composite and five direct source associations are supplied, each with
202 distinct source subtrees. Their complete control-flow graphs are checked
by two independent resolvers. The finite interface and credit scripts
corroborate the written infinite proofs; they do not replace them.

## Negative results worth retaining

1. **Deleting return-scanner state 50 is invalid for the inherited frame
   contract.** The proposed 214-state table fails 72 guarded cases at 37
   addresses ending in six zeros. A concrete valid all-zero-register frame
   at source ordinal 26 reaches the expected dispatcher after 588 baseline
   steps, but after 662 shortened-machine steps has the address one at cell
   12 instead of 14. Complete replayable traces are under
   `research/rejected-return214/`. This does not make a separate assertion
   about the rejected machine's blank-run consistency equivalence.

2. **The archived scratch-biased short-transfer experiment has a wrong
   backward jump.** Its `CC3` at address `100111` returns to ordinal 23 rather
   than 0. From its actual post-AX conditions it manufactures cache value 1
   and reaches CH after 15 further nonhalting source transitions. The proof
   of eventual blank halting uses the inherited terminating AX and complete
   runtime theorem; a full huge binary halting trace is not claimed.
   Changing the leaf to `CC4` fixes the target but changes the source DAG
   count from 201 to 203. Exact hashes, source, table, blank-prefix evidence,
   and an independent checker are under `evidence/audit/`. The accepted
   composite-transfer table in the same incoming archive is unaffected.

`research/source-packing/` records bounded reassociation and protected-row
allocation attempts. Search scores and source DAG counts are not physical
state counts, and infeasibility of those restricted models is not a lower
bound. The optional adjacent-success theorem in `evidence/audit/` concerns a
future correctly implemented scheduler, not the erroneous archived table.

## Artifact map and attribution

| Path | Purpose |
|---|---|
| `report.tex`, `report.pdf`, `sections/` | Complete main paper and editable source |
| `machine/` | Accepted new table, source, construction, canonicalization, runtime evidence |
| `code/` | Deterministic construction, local proof checks, complete runtime checker |
| `evidence/audit/` | Independent audits, 77 prior tables, scratch-return correction |
| `research/stride2/` | New language, compiler, source variants, exact generators and finite corroborations |
| `research/rejected-return214/` | Rejected table and full concrete counterexample |
| `research/source-packing/` | Bounded search receipts, selected sources and optional search tools |
| `reference/` | Exact parent inputs and relevant inherited proof expositions |
| `licenses/`, `NOTICE.md` | Retained licenses and contribution attribution |
| `manifest.json` | SHA-256 and size of each shipped file other than the manifest itself |

The inspected repository is pinned at
`75716498437bfc7291d5900cab2983a11fd54bac`. The inherited numerical calculus,
ZFC calibration, source/compiler architecture, previous marker folds, and
symbolic runtime checker remain contributions of the ProveIt authors and
the upstream authors identified in the retained notices. This packet adds
the conditional 52/176 marker fold and proof, exact new verified table,
independent audits, two-head compiler and credit theorem, and the explicit
return-path correction. The complete inherited development is available at
the pinned repository; copied expositions are reference excerpts, not a
claim to have re-proved that development from first principles.
