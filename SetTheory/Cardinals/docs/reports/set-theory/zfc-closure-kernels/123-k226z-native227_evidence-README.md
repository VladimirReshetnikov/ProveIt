# Native construction and evidence for K227

The selected binary machine has **227 working states**, with start state 0,
dispatcher 83 and halt state 227. Its public table is
`selected/k227.tm`, SHA-256:

```
ce179dae58b737c508c6a3b360cad0fb4ff722165a34aa9e903a8877c0e89d34
```

It is built from [K230 at commit 3142e4dd980f0be12f4abb636c4ae2528afc17eb](https://github.com/elliotglazer/k230-rocq/tree/3142e4dd980f0be12f4abb636c4ae2528afc17eb), whose pinned input is `reference/k230.tm`, SHA-256
`e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8`.

The public numbering preserves the ascending original K230 labels after deleting
79, 140 and 175. The complete bijections are in `selected/numbering.json`.
`selected/k227_k230labels.tm` keeps the gaps in those original labels;
`selected/k227_native.tm` uses inherited native labels, start 95, dispatcher 96
and halt 254, so that the pre-existing exact symbolic engine can be replayed.
All three representations are literally isomorphic.

## Result and scope

The full selected-table proof in `evidence/runtime227/verification.json` passed:

- all 5,121 source leaves and all 6,656 guarded instruction cases;
- 1,605,915 symbolic execution rules, with positive durations and a minimum of 13 literal steps;
- all four exact-table finite-list induction schemas;
- every natural primary register value, arbitrary natural gap, arbitrary first spare and finite spare tail;
- the entire tape, exact successor head position, and zero exterior;
- exact blank startup in 409,835 steps, including an independent dense canonical replay;
- all 454 transition rows, with no unused row assumption.

The source still requires its independently supplied calibration: four closed
increment/drain loop replacements preserve the K230 source computation, and the
remaining tree rotations preserve its complete guarded control graph. This
packet includes an independent checker for the four loop contexts and the full
final-to-H source graph comparison. The accompanying source packet gives the
construction, loop induction, and compact role-fold certificate. The ZFC
calibration ultimately comes from the pinned K230 theorem. These Python proofs
are executable ordinary mathematical proofs; they are not described here as a
fresh proof-assistant check of the complete selected 227-state endpoint.

The runtime checker's `canonical_sha256` names an additional, inherited-label
sorting of the machine. That auxiliary numbering is different from the public
K230-preserving numbering above; `build.py` checks their exact relationship via
the common inherited table.

## The three savings

1. **The H loop and native 79→63 fold.** Replace each of four closed loops that
   computes `(R5,R6)=(a,b) → (a+b+1,0)` by an equivalent form with one fewer leaf.
   Its selector contexts allow two native controls to share state 63. The
   all-tape finite proof rechecks all 460 old rows and uses four exceptional
   positive blocks of lengths 9, 3, 3 and 3.
2. **Delayed erasure, 140→71.** Retain a marker for a few more native steps and
   share its erasure with the existing arithmetic path. The finite proof uses
   four exceptional blocks of lengths 5, 3, 5 and 9. A separately quantified
   runtime proof checks the one required right-neighbor guard in all 6,656 H
   source cases and throughout exact startup. All 28 symbolic guard visits and
   all six startup visits are retained.
3. **Rehome two roles of native 175.** A source rotation makes the old `PP`
   decoder at 150 uniformly enter with predecessor bit 0. Its unused bit-1
   context then hosts the `PI` role of 175. The remaining `ZI` role goes to a
   large decoder at 152 in the opposite predecessor context. Five closed
   rotations establish the contexts and repair the tape encoding. This removes
   state 175 without introducing a replacement state.

The original K230 table already incorporates the older 243→241 native folds.
The two transferable arithmetic savings and the new role reassignment account
for the reduction 230→227. The source programs' leaf counts are 5,125→5,121;
working-state count and source leaf count are different quantities.

## Reproduction

Python 3 and a C++17 compiler (`g++`) suffice for this packet. No third-party
Python package or network access is required. Run with Python assertions enabled.

```
python reproduce.py --output /path/to/fresh-replay
```

This reconstructs all eight selected/control tables byte for byte; replays the
H and delayed-erasure finite block certificates; independently checks all H
replacement contexts; replays the rejected scanner witness; checks the 26,624
finite instruction fixtures plus exact startup; and checks the selected source
graph and complete blank startup.

To freshly reprove all selected native instruction frames and every delayed erasure guard as well:

```
python reproduce.py --full --output /path/to/fresh-full-replay
```

The full option runs two symbolic proofs. Their induction is over arbitrary
natural unary lengths and arbitrary finite spare lists. Proof-construction fuel
is not a bound on the eventual machine execution.

`build.py --output DIR` reconstructs the selected 227 and five inherited-label
control tables independently of the source builder. `selected/recipe.json`
contains the 36 retained-row changes, their required old values, and the three
deletions. `SHA256SUMS` pins every distributed file.

## Evidence layout

- `selected/`: only the chosen 227-state machine, exact source leaves, recipe and bijections.
- `reference/`: frozen K230, normalization and exact startup data, and the H source.
- `controls/`: the unchanged-source 229 and the H-based 230/229/228 transfer chain.
- `evidence/`: full selected runtime and startup receipts, finite block proofs,
  and every case/visit/block/used-row record for the H delayed-erasure guard.
- `verification/`, `engine/`, `runtime_dependency/`: portable checker sources,
  preserving the exact engine bytes used for each proof. The guard engine and
  selected runtime engine are independently pinned versions of the same method.
- `rejected/`: a complete finite counterexample to an intermediate seven-zero
  address layout. Its 227-state count alone did not imply correctness.
- `discovery/`: bounded negative local search results; these do not assert minimality.

The rejected layout fails at source leaf 1042, address
`11101001001110010000000`, on a zero-valued `CD2`. It reaches a clean dispatcher
after 1,708 steps with four wrong tape cells. Two later source rotations remove
the seven-zero run while retaining all three state savings. The selected source
has maximum depth 40 and maximum zero run 6.

The last bounded search tried every 25,651 state pair and 46,377,008 replacement
row choices, with 585,927,699 one/two-helper checks, over the stated radius-5
finite discovery profile and local blocks of at most 65 steps. It found no
additional fold in that search scope. It is neither an exhaustive TM search nor
a proof that 227 is optimal.

## Attribution

The frozen 230-state construction and consistency calibration are due to the
K230 project, building on the ProveIt and Wade busy-beaver constructions.
The inherited native fold and symbolic-checker sources are copied from the
pinned ProveIt research artifacts. Their notices are retained under `licenses/`.
The final role reassignment, source repairs, independent construction checks,
and integration evidence are the new work in this research package.
