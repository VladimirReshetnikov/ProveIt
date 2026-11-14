# NEG18: a new arithmetic macro and its 197-state implementation

This package supplies an explicit **197-state**, two-symbol, single-tape machine implementing a new 18-site negation macro. It does **not** achieve the requested threshold of fewer than 196 states. The smaller source program is a useful optimization, but its compiled decoder currently needs one state more than the existing 196-state designs.

The dense machine has working labels `0..196`, start state `0`, and a separate halt label `197`. Its tape is two-way infinite and initially all zero. Each table row is `state read write direction next`, with direction `L` or `R`. The halt label has no rows and is excluded from the count. All 197 working states are graph reachable.

## The arithmetic idea

Write

\[
 p(a,b)=\frac{(a+b)(a+b+1)}2+b,
 \qquad N(t)=4p(t,1).
\]

The identity `p(t,1) = p(0,t) + 2` allows the existing pairing core to compute negation without pushing and popping the formula stack. The fixed `node64` core has the more general contract

\[
 (T,X,Y)=(t,x,y)\longmapsto(4(y+p(x,t)),0,0).
\]

Starting with scratch registers `X=register6=0` and `Y=register7=0`, execute

```
INC register7
INC register7
node64
```

The result is `T = 4(2+p(0,t)) = 4p(t,1)`, the scratch registers return to zero, and every other register, including the encoded formula stack, is preserved. Both building blocks already exist in the fixed physical kernel: `INC7` enters at native state 82, and `node64` enters at native state 106. The new block has 18 primitive source sites. The previous direct negation uses 20; the original stack-based block uses 47.

The independent checker in `macro_proof/` binds the exact primitive CFG, checks the affine drain-loop effects and the triangular outer invariant with rational-polynomial arithmetic, and verifies termination through decreasing natural counters. It also checks direct entry-state bindings at all upstream occurrences. Finite numerical examples are controls in addition to this universal loop argument. The exact source-step count of NEG18 at clean scratch is `13*t*(t+1)/2 + 8*t + 17`. The previous 20-site block takes `13*t*(t+1)/2 + 14*t + 26` source steps: its move drain costs `3*t+1`, its increment costs `1`, and its core is entered at `(T,X,Y)=(1,t,0)`. Thus NEG18 saves exactly `6*t+9` source steps. These are register-program transition counts, not physical TM-step counts.

The scratch hypothesis matters. None of these claims treats an arbitrary dirty scratch store as a clean macro input. The implemented whole program has an independently computed zero/positive invariant that forces **both** scratch registers to zero at all eight replacement entries. The higher-level clean-store interpretation also appears explicitly in the inherited `AXMacro.registers` definition and its macro realization lemmas.

## Exact construction

The input `inputs/separate196.grammar.json` is the existing 190-token separate-equality-vacuity AX emitter. Each of its eight token triples

```
node49 ; INC register1 ; node65
```

is replaced by

```
INC register7 ; INC register7 ; node64
```

The original binary association is retained. Five explicit simultaneous contextual folds are applied to the 68 generated AX readers. Together with the fixed 134-state kernel, this gives `134 + 68 - 5 = 197` states. The saved fold recipe is literal data; verification does not rerun an optimizer.

The resulting source has 3,441 sites, versus 3,673 for the input emitter and 3,457 for combining that emitter with the older 20-site negation. The reconstruction checks each 47-to-18 block replacement against the independently resolved local CFG, checks that no outside edge enters a changed block halfway through, and compares every unaffected source row with its relocated successor labels. Two additional CFG resolvers check the complete new source.

## Reproduce

Python 3.10 or later is sufficient; all code uses the standard library. Run without `-O` because inherited parsers use assertions.

```
python3 verify.py --check
python3 macro_proof/verify.py
```

The first command checks the supplied artifacts byte-for-byte. Running `python3 verify.py` without `--check` regenerates the same seven output files and reruns all checks. No network, Git checkout, package installation, Lean installation, or workspace-specific path is needed.

The whole-program checks establish:

- 197 graph-reachable working states and 394 total binary transitions;
- exact dense/native relabeling and unchanged inherited register-engine rows;
- all 4,468 positive-length symbolic primitive contracts under the inherited register-block interfaces and clean-frame assumptions;
- the entire blank-tape startup, including every nonzero tape cell, after exactly 58,154 steps;
- the source seed at site 25, native root 84, header gap 48, logical register `R0=2` (the enumeration candidate), other logical registers zero, and 26 spare blocks of value 1;
- an inductively closed joint zero/positive abstraction with 245,112 `(site, mask)` pairs, forcing registers 6 and 7 to zero at every replacement entry;
- the universal local NEG18 arithmetic identity and its exact binding to the eight changed source intervals.

The symbolic runtime is an executable checker using inherited register-block summaries. It is not a new Lean kernel proof. This package does not claim a newly formalized PA-internal biconditional between nonhalting and `Con(PA)`. In particular, the imported PA196 publication states the internal direction `Nonhalting -> Con(PA)` and metatheoretic soundness; the converse internal proof remains a separate obligation. Halting-preserving local optimizations do not discharge that logical obligation.

## Files

| File | Purpose |
| --- | --- |
| `machine.tm` | Dense 197-state transition table, start 0, halt 197 |
| `machine.native.tm` | Native labels, start 74, frame root 84, halt 254 |
| `labels.json` | Dense-to-native relabeling, including the halt label |
| `source.json` | Every primitive site, path, operation, operand, and resolved instruction |
| `grammar.json` | Exact new AX grammar |
| `folds.json` | Five simultaneous fold recipes |
| `verification.json` | Deterministic complete-machine verification receipt |
| `verify.py` | Portable reconstruction and verification driver |
| `macro_proof/verify.py` | Independent CFG and polynomial-loop certificate |
| `negation_identity.tex` | Mathematical explanation of the direct negation variants |
| `code/` | Inherited compiler, symbolic checker, independent CFG utilities, and source references |
| `inputs/` | Pinned input grammar and explicit fold recipe |
| `licenses/` | Preserved ProveIt and James Chang notices |

Dense table SHA-256:

```
15f8b3e96d6adae76236ab0960d288b9537e39294ef1ab65f8fdd2e16dc2a9b6
```

Native table SHA-256:

```
06f0d712e0933e80c2a0e82c765dbf82b4a9645a4fb6556eb50f8fc79550519d
```

## Provenance

Inputs were taken from ProveIt commit `906367250a7f96c923147b10df392294bced7be5`, principally `docs/incoming/pa_consistency_comparison_and_new196_2026-11-13.zip` and `Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196`. The independent CFG utility comes from the existing PA allocator screen. The local negation identity, preloading construction, integration, and independent source-loop certificate were developed during this investigation. Original licenses and authorship remain unchanged.
