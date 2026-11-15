# Physical reduction investigation

Scope: pinned ProveIt commit `7c0bb454cf73c29ca1c385f9fec856ddd236a7cb`, with the six incoming archives extracted by the census agent. No remote files were changed.

## Positive contribution: expose the gate's two closed tests

The primary gate macro is `node150 = (node146,node149)`. Its native control is 221 and its children are 196 and 217. The 30-leaf gate consists of a first comparison/clear loop and a second copy-and-compare loop. Both subroutines are closed at the source CFG level. Exposing them allows the adjoining AX suffix to be reassociated without altering any primitive source instruction or jump destination.

The first attempted balanced association helped the shortened scanner but had an increment-path problem at other addresses. The parent agent found the working regular-scanner reassociation

`(A, ((node146,node149), Push)) -> (A, (node146,(node149,Push)))`.

Native control 221 becomes unreachable; the new reader replaces its role in associating the second test with Push. This is not a control renaming. The parent built `gate_split_work/candidate` with 194 states, 133 fixed plus 68 reader states minus seven folds. My independent reconstruction in `reduction_work/validation_h_seed0` returned exactly the same dense SHA-256:

`64ac4ba569b770688a39a1545d5536ad631d15dbb756a0584a8956a83943b3a8`.

Both reconstructors report 3,671 source sites; exactly 49 addresses changed; 4,778 symbolic outcomes passed; the complete blank startup reaches the seed in 57,922 literal transitions. These executable facts do not independently establish the absolute Con(PA) calibration. The new relative implementation argument uses the same source, universal frame contracts, and primitive-recursive witness transport.

## Shortened return scanner: why the apparent 193 machine is rejected

An existing incoming experiment removes scanner state 34 by changing native `(23,0)` to `0 L 75`. The shortened detector requires a smaller bound on zero runs in source addresses. I investigated exposing the gate to make that bound achievable while avoiding an extra gate reader.

A constrained interval DP on the standalone 30-leaf gate found minimum leading-zero depth five, even if integer break/continue counts are adjusted to preserve the exact CFG. The first part has forced nested boundaries: `dec` at local instruction 0 exits at 4; the break at 3 exits at 5; `dec` at 4 exits at 10; the break at 9 exits at 12. A full standalone gate then contains a further enclosing branch. This is a restriction on this structured representation of this CFG, not a lower bound on all gates or all machines. Exposing the gate and associating a preceding closed AX routine can interrupt the run with a right branch.

The first explicit new nominee in `reduction_work/scanner_initial` has 193 controls, exact equality of all 3,673 primitive instructions, and all local fold checks. It fails the physical source checker at site 50, zero branch on physical register 2, after 70 completed outcomes. Its path is `101101001000000`. A literal replay from a complete frame with all nine registers zero and one spare of value 1 reaches control 84 at head 9 after 91 transitions; the required next frame is at head 0. `failed_symbolic_trace.json` records the exact rejected symbolic trace, and `failed_literal_trace.json` records a 10,000-step diagnostic run. The diagnostic run is bounded; its failure to reach the expected target is not asserted as an infinite nonreachability proof.

There do exist longer 5-zero-bounded reencodings of this exposed-gate source: the 250-state balanced specimen in `scanner_balanced_check` passes all 4,780 symbolic source outcomes. Its inherited exact blank-seed test fails, and a further bounded million-step inspection found no required seed. Thus neither source-CFG equality nor the smaller runtime state's count solves blank initialization. No shortened-scanner candidate is promoted as a consistency machine.

Several annealing runs explored global reassociation, including a feasible zero-bounded balanced seed instead of only the node72 ancestry rotations in the prior report. They did not produce a calibrated sub-194 machine. In particular, the scores of failed or larger runtime variants must not be presented as machine bounds for Con(PA).

## Fresh table-level acceleration and quotient screen

`reduction_work/shortcuts.cpp` is a standalone C++17 search. Starting from the designated blank state 74, it computes an inductively closed finite abstraction of radius-K tape windows, admitting both values of newly exposed boundary cells. For each state/read pair it intersects all old future configurations, through a specified step fuel, that can be represented by one legal TM transition with no changes outside the scanned cell. It then tests:

* deleting one or two controls by choosing certified row shortcuts whose targets avoid them;
* merging two controls when both bit actions have a common shortcut after the control identification.

It searches sufficient local conditions and is not a global minimizer. On all nine incoming top-level native machines at radius 7 and fuel 129 it found no deletion or merge. The only additional row shortcuts are the already-known `(26,1)->1 R 91` and `(101,0)->0 R 17` on unaccelerated parents. Every state/read case has nonempty abstract context coverage.

| Machine | Radius-7 contexts |
|---|---:|
| H5XS | 945146 |
| JH5XS | 931849 |
| GDH_SF | 901793 |
| GD_SF | 903057 |
| GDHS_SF | 916193 |
| H5X_MF | 930186 |
| JH5X_MF | 917561 |
| ORH | 895911 |
| OR | 898753 |

The new gate-split candidate was also screened at radius 9 and fuel 257: 10,650,383 contexts, the same two available accelerations, and no one/two-state deletion or merge. ORH at radius 9 had 10,601,743 contexts and likewise no contraction.

## Regular-scanner gate family: historical and corrected searches

This is the strongest follow-up to the positive 194 construction. The fixed part has 133 controls, so effective reader cost at most 60 would give at most 193 states. Frozen literal seeds, leaf attributes, standalone C++ scorers, logs and generated grammars are in `reduction_work/gate_search`, `gate_search_gdh`, and `gate_permutations`.

The ordinary scorer follows the inherited shared-DAG annealer. I also extended it to consider folds involving fixed controls, whose incoming contexts can change after 221 disappears, rather than only newly allocated AX readers. The extended scorer considers every non-start control whose entire incoming edge set writes a uniformly zero or one preceding cell and moves right. Simultaneous two-cell fold traces are checked in the scorer; actual nominees still require a complete independent source/physical/startup validation.

H and GDH source families are searched separately. An additional pair of searches reparameterizes each of six universally quantified axiom heads by permutations of A/D/H, with all increments expanded before assigning word intervals. Such a hit would require the explicit schema-reparameterization argument as well as physical validation. No source-graph equality to the unpermuted parent would be claimed.

The seven historical principal runs generated 13,446,433 proposals, and seven additional-family compositions generated 12,633,111 proposals. These are historical nominal effort counts. A later audit found that the inherited expanded-copy search bound `node69` to native 30 instead of the correct copyH remainder entry 179, and recognized `(19,30)` as a free copyH pair. Five principal runs and all additional-family runs included this incorrect model. Their scores must not be used as physical negative evidence. The two head-permutation runs did not expose copyH, so this particular binding error was dormant there.

The correction also charges only syntactically reachable controls: expanded copies may eliminate fixed controls 12 and 166. All 900 saved legacy grammars were repriced using the corrected binding, graph reachability, and simultaneous compatible folds. Every one prices at 194; none survives as a 193-state nominee. Three apparent 193 tables obtained with the old binding are explicitly retained as rejected examples. Two fail at site 389 after 513 scalar outcomes, and one fails at site 95 after 129. A literal H example returns to dispatch after 120 transitions with the wrong code tape. This is a failure of the implementation contract, not an absolute halting conclusion.

Four fresh corrected H/GDH runs generated **7,663,786 proposals**, with **zero strict-reduction hits** and best effective cost 61, or 194 controls. Their exact counts are 3,140,743; 3,010,987; 773,749; 738,307, using seeds 18112200 through 18112203. The first two use 300-second budgets; the warmer variants use 120 seconds. The standalone tail generator was also replayed and its 3,238 templates repriced with the corrected model, again giving best effective cost 62, or 195 controls.

A historical deep-gate experiment generated 1,807,142 proposals but is also an invalid/partial price screen: besides the copyH error, it omitted the incoming-one conditions for exposed node145/native122 and node147/native130. No physical result is claimed from it.

The validated positive 194 construction does not expose copyH and is unaffected. Final portable sources, frozen inputs, corrected receipts, audit patches, and rejected witnesses are in the package's `research/gate_search`; standalone finite-window screens are in `research/physical_shortcuts`. Exact final totals are in `reduction_work/search_summary.json`. None of the scoped negative outcomes is a general lower bound.

## Reproduction and provenance

For the standalone physical screen:

```sh
g++ -O3 -std=c++17 shortcuts.cpp -o shortcuts
./shortcuts path/to/machine.native.tm output_prefix 9 257
```

For each frozen annealer folder, compile its `search.cpp` or `search_all.cpp` and pass `seeds.txt`, `leaf_attrs.txt`, output prefix, time limit, random seed, and maximum proposal count. Runtime-limited searches are not bit-for-bit reproducible across processors; frozen logs give actual proposal totals. The source transformation and positive checks should be reproduced by the parent's final deterministic build/check scripts.

The search framework and compiler utilities derive from the attributed ORH packet and its retained prior dependencies. They must retain the packet's license/notice files if redistributed. `shortcuts.cpp`, the exposed-gate experiments, and the broadened all-control fold scorer are new modifications; no authorship of the inherited numerical calculus, machine, or compiler is claimed.
