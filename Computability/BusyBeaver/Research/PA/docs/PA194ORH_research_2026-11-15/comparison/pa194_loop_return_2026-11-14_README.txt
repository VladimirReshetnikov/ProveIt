# Two 194-state PA consistency machines with shortened loop continuations

Research report for Vladimir Reshetnikov, 14 November 2026.

**No verified machine below 194 working states was obtained.** This package
constructs two materially different 194-state alternatives, **PA194LCG** and
**PA194LCGS**, and gives a written relative iPRA proof connecting each to its
specified AX11GH/GHS parent. Their Con(PA) calibration follows by composition
with the identified revised AX11H written calibration and GH/GHS command
equivalences. That arithmetic calibration is an explicitly imported
mathematical dependency. This package does not claim a new completed
end-to-end Lean or Rocq proof.

Read `report/report.pdf` for the full comparison, construction, proof,
evidence boundaries, and complete printed transition tables. All of its
LaTeX source files are included in `report/`.

## Exact machines

Both machines use a single two-way infinite tape, binary alphabet, blank
symbol zero, one head, and only left/right moves. The entire initial tape
is zero. Dense working states are 0 through 193; start is 0; halt is 194,
excluded from the working-state count. Native start and halt labels are
74 and 254. Native label 194 is a working state.

| Property | PA194LCG | PA194LCGS |
|---|---:|---:|
| Working states | 194 | 194 |
| Transition rows | 388 | 388 |
| Unfolded controls | 201 | 202 |
| Contextual folds | 7 | 8 |
| Primitive source sites | 3,671 | 3,668 |
| Independently checked source outcomes | 4,778 | 4,774 |
| Changed primitive addresses | 305 | 305 |
| Exact blank initialization steps | 57,870 | 57,712 |

The definitive tables are `machines/PA194LCG/machine.tm` and
`machines/PA194LCGS/machine.tm`. Each line is `state read write direction next`.
Their exact SHA-256 values are:

```text
PA194LCG
5d8e4f5e03c72a8737b898c00a5fbd6e62476cc34a483613ed046d0dc113e84c

PA194LCGS
ff084fd560d1b2792cda1c443ef522fe4953b1ff0677ad71100fb5e82d19b90b
```

### What changes

The existing loop reassociation is applied to the AX11GH/GHS parents,
preserving every resolved primitive instruction and successor. It changes
five source addresses at each of 61 occurrences. Two existing physical
shortcuts are retained. A new third shortcut uses the unique incoming edge
of native control 190 to prove that its left neighbor is one:

```text
190 reading 1:  1 L 73; 1 R 83; 0 L 42
replaced by:   0 L 42
```

The three old steps and one new step have exactly the same complete tape,
head and control at their endpoint. The new relative proof gives both
halting-witness implications with

```text
Theta(t) = 60000 + 13*(t+1)^2 + 1147*(t+1)
         = 13*t^2 + 1173*t + 61160.
```

The proof uses primitive recursion and quantifier-free induction. It
explicitly handles physical halting between source-frame boundaries and
does not invoke Markov's principle. The local shortcut proof also gives
an exact expanded clock between each accelerated table and its intermediate
loop parent, with `t <= sigma(t) <= 3*t`.

Neither table is a state renaming of a prior table. The supplied exact
indegree/self-loop/successor-equality histograms give a differing
multiplicity against every one of the 232 prior normalized labeled tables.
The two new tables also differ from each other under that invariant.
This novelty check is separate from the correctness proof.

## Reproduce the construction and checks

Python 3.10 or later and its standard library suffice for the main package.
Run without `-O`: assertions are part of the checkers.

```sh
python3 -B reproduce.py --out replay
python3 -B reproduce.py --full --out full-replay
```

The first command checks the release manifest, reconstructs both machines,
checks source equality, all fold and shortcut premises, and the entire
blank initialization. It also checks the saved independent literal
certificates against the actual tables, verifies complete frame closure
and the polynomial duration envelope, and replays every exact novelty
comparison. It does not merely run a long blank-tape simulation.

The second command additionally regenerates all 9,552 independent literal
source outcomes from the transition tables. It reconstructs four generic
list-sweep lemmas from literal rows and uses an independent pair of source
resolvers. It imports neither the construction compiler nor an arithmetic
box oracle. This replay takes several minutes. The completed receipts and
contracts are already included under `verification/results/`.

The literal contracts quantify over nine arbitrary natural registers,
both decrement branches, an arbitrary nonempty finite spare list, and an
arbitrary nonnegative header gap. The verifier's symbolic step counts
measure proof execution, not a bound on the machine's actual running time.

Optional research replay:

```sh
python3 -B research/replay_shortcuts.py shortcut-replay
python3 -B research/literal_contexts/reproduce_context_research.py --help
```

The literal-context supplement also needs a C++17 compiler for its bounded
reduction searches. Its own README documents full envelope regeneration
and the faster replay using the included hash-checked envelope. No network
access or repository checkout is needed for these new-machine checks.
Rebuilding the historical corpus census does require the pinned Git tree.

## Comparison scope and negative results

All source claims are tied to ProveIt commit
`8d31445d858761a8f6150c2e5012adae8895e932`:

<https://github.com/VladimirReshetnikov/ProveIt/tree/8d31445d858761a8f6150c2e5012adae8895e932>

The comparison reconciles 87 filed packets and six current incoming
archives: 93 deliveries, 74 named principal/supplementary constructions,
and 26 mechanism families. The literal/explicit-JSON/recursive-ZIP census
recognizes 1,988 physical 194-state occurrences, 232 normalized labeled
tables, 139 spanning action-graph classes and two nonspanning diagnostic
encodings. All 110 classes in the older official 194-state census are
recovered. Auxiliary and rejected tables are retained with their status;
they are not counted as independently proved consistency theorems.

The new literal arithmetic-context envelope reduces the radius-six
contexts at 23 arithmetic controls from 119,150 to 18,570. On that envelope,
all 18,721 state pairs were checked in each of two bounded quotient
families, and all 193 non-start states were checked for a bounded
incoming-edge deletion. None yielded a candidate. Additional shortcut,
marker and targeted return-fold searches are included. Their negative
results exclude only the specified transformations under the stated
bounds and context requirements. They establish no global state lower
bound.

## Artifact map

| Location | Contents |
|---|---|
| `report/` | Compiled report, full LaTeX source, generated family/named-design tables and complete transition-table appendices |
| `machines/` | Both final dense and native tables, source arrays, label maps, folds, intermediate loop tables, construction receipts |
| `inputs/` | Exact frozen AX11GH/GHS parents and supplied independent literal certificates |
| `construction/` | Attributed compiler and construction-side symbolic checker |
| `verification/` | Independent literal checker, full contracts, frame/clock audits and inherited-calibration review |
| `comparison/` | Delivery ledger, all named designs/families, all recognized frontier classes, prior tables and exact novelty witnesses |
| `research/` | New finite searches, arithmetic-context envelope, scripts, receipts, proof notes and search limitations |
| `references/` | Identified inherited mathematical proof sources and their original status statements |
| `licenses/` | Upstream licenses and attribution notices |
| `PROVENANCE.json` | Source revision, archive identity, copied-input bindings and adaptation notes |
| `MANIFEST.sha256.json` | SHA-256 values for every release file other than the manifest itself |

## Compile the report

With a standard TeX Live or MiKTeX installation:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The report uses Latin Modern, microtype, AMS packages, geometry, booktabs,
longtable, array, enumitem, xcolor, xurl, hyperref and fancyhdr. No bibliography
processor is required. Regenerate data appendices with
`python3 -B report/generate_tables.py` from the package root before compiling
if the comparison data or transition tables have intentionally changed.

## Attribution and evidence boundary

The arithmetic controller, inherited calibration, source compiler,
independent symbolic engine and many design ingredients come from the
supplied ProveIt research material. Preserve the included ProveIt, James
Chang and Wade notices. The new work consists of the additional
continuation shortcut, the two combined literal tables, the direct
relative proof and coefficient audit, the current comparison and exact
novelty certificates, and the documented new reduction experiments.

The absolute consistency corollary imports the revised
`pa194_ax11h_research_2026-11-14_2` written mathematical calibration and the
specified GH/GHS source-protocol equivalences. The review binds and examines
those dependencies; it does not rebuild every inherited proof constructor
or complete the repository's Lean project. That distinction applies to
every result and receipt in this package.
