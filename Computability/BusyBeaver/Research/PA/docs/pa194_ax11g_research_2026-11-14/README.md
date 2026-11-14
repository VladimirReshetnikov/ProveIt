# PA194AX11G: comparison, construction, and relative iPRA preservation

**Result:** a new 194-state binary Turing machine, PA194AX11G. No verified
machine with fewer than 194 states was obtained. The machine combines the
explicit generalization binder of PA194G with the eleven-entry,
four-operand AX protocol, Q-oriented distribution, no-push MP, and the
original sum-one Shift. Its source command, proof compiler, and literal
transition graph differ from every recognized 194-state design in the
requested pinned corpus.

**Proof qualification:** the report gives an ordinary computer-assisted
proof of relative preservation:

    iPRA ⊢ Halt(PA194AX11G) ↔ Halt(primary PA194).

Thus an iPRA proof of the primary machine's nonhalting equivalence to
Con(PA) transfers to this exact new table. The primary machine's absolute
iPRA calibration is a separate inherited obligation, explicitly open in
the [pinned PA README](https://github.com/VladimirReshetnikov/ProveIt/blob/32d0d8b7d93a63ad4106c18cdb29b37927acdad2/Computability/BusyBeaver/Research/PA/README.md).
This package does **not** claim to complete that calibration or a new
end-to-end Lean or Rocq proof. The distinction concerns the strength and
scope of the available mathematical argument, not just whether Lean has
been run.

## Read first

- **`report/main.pdf`**: full mathematical report, comparison, attempted
  reductions, proof scope, the complete transition table, all 94 historical
  graph classes, and all 82 delivery packets.
- **`report/main.tex`** and **`proof/ax11g.tex`**: editable LaTeX sources.
- **`machine/machine.tm`**: the exact new dense transition table.
- **`verify_all.py`**: an offline aggregate replay of the positive
  construction and finite certificates.

## Literal machine

The machine has a two-way infinite tape, alphabet `{0,1}`, blank symbol 0,
head initially at coordinate 0, working states 0 through 193, initial state
0, and a terminal halt label 194 with no outgoing rows. Each of its 388
rows writes a bit and moves one square left or right. All working states
are graph-reachable. The count is **134 fixed controls + 67 raw AX readers
− 7 simultaneous context-dependent folds = 194**.

The exact dense-table SHA-256 is:

```text
7e1c6442816e5df05e961f2057719252a1976c9a195a786978bf1e2d3c8e466d
```

`machine/FORMAT.txt` explains the native labels, direction convention,
label correspondence, and related table files. No prewritten input,
larger alphabet, stationary head move, or alternate state-count convention
is used.

## What changes in the source

PA194G's final AX jump is replaced by its existing Push macro. This changes
one primitive jump into a 19-site interval. All other primitive instructions
and control-flow successors are identical under the checked relocation.
The inserted Push falls through the **complete** MP operand reader, so AX
now consumes a fourth field. The saved generalization remains `U(c,h)`,
with the explicit first AX operand `c` as binder.

With a store `(t,w,d,h)`, the command has the effect

```text
AX(c,x,y,z):
  (t,w,d,h) ↦ (0,[g, Γ, h6Q, h5, h4, h3, h2, h1, ρ, U(c,h), t ; w],z,0)
```

The report gives every head's exact arithmetic definition. With
`A0 = AX(0,0,0,0)`, it proves total identities for

```text
Push = A0 ; S^10 ; MP(0)
Pop  = A0 ; S^12
Gen(i) = Push ; S ; AX(i,0,0,0) ; S^11
```

The generalization word requires no offset-setting command. The complete
proof compiler handles arbitrary incoming stores and all Cantor-stack
zero aliases. Its iPRA induction is an explicit bounded Boolean invariant,
not an induction assumption with an unbounded universal store quantifier.

The Q/primary premise-exchange bridge is supplied as a flat certificate
with **18,897 lines: 8,986 restricted-rho instances and 9,911 MP steps**.
Its 29,932-node term DAG has no K/S axiom, hypothesis, or tautology oracle.
Two separate checkers replay all numerical dominance certificates.

## What was verified

| Check | Result |
|---|---:|
| Working controls / transition rows | 194 / 388 |
| Primitive source sites | 3,672 |
| Branch-sensitive source outcomes | 4,779 |
| Local simultaneous fold cases | 28 |
| Construction-checker symbolic operations | 1,483,363 |
| Independent literal-checker symbolic operations | 1,083,079 |
| Literal checker maximum operations per outcome | 379 |
| Generic list lemmas derived from literal rows | 4 |
| Complete blank initialization | 58,154 transitions |
| Exact matches to the 94 historical graph classes | 0 |

The independent tape checker imports no constructor and uses no
arithmetic-box oracle. It checks arbitrary natural register values, both
decrement branches, an arbitrary nonempty spare list, and an affine
nonnegative header gap. The complete startup tape, not just a local
window, is checked. Symbolic-operation counts are checker costs, not
bounds on physical execution for arbitrary register values.

The delivered table, source data, and native proof certificate rebuild
byte for byte in a separate directory without the original repository or
network access. Every freshly replayed literal symbolic contract matches
its retained losslessly compressed counterpart byte for byte.

## Complete comparison

The snapshot is ProveIt revision
`32d0d8b7d93a63ad4106c18cdb29b37927acdad2` (14 November 2026).
The inventory covers all **675 tracked PA `.tm` files** and all **five
current incoming ZIPs**; all 680 source payloads matched their Git blob
identities. The delivery ledger has **77 filed packets + 5 incoming
archives = 82 packets**.

The 194-state slice has **528 literal-table occurrences**, **139
normalized labeled tables**, and **94 spanning graph classes**. Their
attributed categories are 51 principal constructions, 7 supplementary
constructions, 25 research auxiliaries, 4 research seeds, and 7 rejected
or diagnostic classes. Four nonspanning diagnostic occurrences are
recorded separately. The scan recognizes literal table files; it does not
claim to evaluate every arbitrary program that could generate another
table.

Every class has a bundled representative and a full CSV/JSON ledger row.
The novelty replay compares complete canonical tuples after allowing all
spanning initial controls, arbitrary state names, reflection, global
symbol exchange, and ignored writes/moves on entry to halt. The symbol
exchange is a deliberately stronger structural novelty screen; it is not
assumed to preserve the all-zero initial tape. No old class matches
AX11G. This establishes novelty within the pinned recognized corpus,
not a worldwide priority claim.

## Efforts below 194 states

The report distinguishes new experiments from attributed prior results.

- **All inherited physical 193-state graphs:** fresh replay of 52 tables
  at every working-state start gives 10,036 cases: 106 finite halts and
  9,930 exact outward-ray certificates, all within 117 steps. There are no
  fuel-cutoff cases. The separate coefficient-three logical proposal has
  an attributed prior refutation, not a fresh replay here.
- **Control sharing:** new radius-four coupled screens include arithmetic
  controls as well as decoder controls. Their exact inputs, limits,
  zero-hit receipts, and C++ replay are in `research/physical/`.
- **Terminal grammar allocation:** two new 300-second searches made
  4,638,201 and 5,197,642 mutation attempts; both ended at best penalized reader
  score 60, with no score-59, zero-penalty nomination. Seeds, exact inputs,
  logs, sources, and finite pricing screens are in `research/grammar/`.
- **More substantial source changes:** deleting the saved-old-top copy
  breaks total cleanup; the concrete coefficient-six parity integration
  has 205 raw states and an optimistic folded price of 198. Neither is
  reported as a successful smaller machine.

These are finite, explicitly scoped research results. They imply no lower
bound on arbitrary 193-state consistency machines or on unexplored
initializers and tape representations.

## Offline replay

Use Python 3.10+ with assertions enabled:

```sh
python3 -B verify_all.py
```

It checks file integrity, pinned construction/proof inputs, the full
constructor, the independent literal contracts and startup, command words,
source relocation, both native-propositional checkers, exact certificate
re-export, the 94-class comparison, and all 10,036 rejected starts. On the
preparation machine this completed in about 71 seconds; elapsed time is
not part of the theorem. No third-party Python package, Lean installation,
original checkout, or network is required.

To retain separate fresh outputs:

```sh
python3 -B verify_all.py --output /tmp/pa194-ax11g-replay
```

The default aggregate does not rerun exploratory allocation searches.
Their own READMEs give the optional C++17 commands. Those searches are not
dependencies of the positive machine or proof replay.

To rebuild the PDF with an ordinary LaTeX installation:

```sh
cd report
python3 -B generate.py
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The generated appendices are also included. The two LaTeX passes resolve
the table of contents, citations, and internal references.

## Attribution and scope

The historical machines, arithmetic engines, and source-calculus results
remain attributed to their original ProveIt research packets and authors.
The minimal inherited source files are pinned in the provenance manifests,
and upstream license notices are preserved under `construction/licenses/`
and the independent verifier's reference directory. The new contribution
is the combined AX11G source/table and compiler, its independent checks,
the current-corpus reconciliation, expanded finite exchange certificate,
and the fresh searches identified in the report.

The absolute machine-specific iPRA equivalence to Con(PA) remains a
separate obligation. Finite replay success and an ordinary relative
preservation proof must not be relabeled as its completion.
