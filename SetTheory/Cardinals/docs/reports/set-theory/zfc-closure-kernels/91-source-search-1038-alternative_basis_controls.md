# A priced three-parameter implicational basis

## Question and measured result

The original Łukasiewicz axiom row uses four independent formula parameters. Its fourth parameter `u` requires a destructive proof-stream read in the AX constructor. Could a complete three-parameter basis remove that read and reduce the whole machine?

We replaced that one row by K, S and Peirce, retaining the original seven other logical rows, GEN, the complete SIR bundle, arithmetic formula constructors and gate. The replacement is logically complete, and the destructive `u` read disappears from the actual generated source. On the matched Wade compiler/grammar backend, the best resulting complete transition table had **272 working states**, compared with **268** for the matched original-basis control. Removing one read was outweighed by the cost of constructing two additional logical rows.

This is a measured negative control, not a lower-bound claim or a count against the routed 245-state framework. The matched compiler has a different decomposition and boot path. No 272-state blank-start consistency theorem is claimed; its complete table and exact source-edge reextraction were checked, while its new proof-stream encoding and initializer would require their own semantic composition.

## Exact basis and the two proof translations

Use the same numerical implication operation `I`, with the same truth and falsity aliases as the original code calculus. The new axiom schemas are

\[
K(a,b)=a\to(b\to a),
\]
\[
S(a,b,c)=(a\to(b\to c))\to((a\to b)\to(a\to c)),
\]
\[
P(a,b)=((a\to b)\to a)\to a.
\]

All instances use the existing AX parameters `a,b,c`. The independent fourth parameter no longer appears. The remaining original schemas `rho1` through `rho7`, including rho6, are retained exactly, as is the original gated bundle.

The original Łukasiewicz row derives K, S and Peirce. The existing `Lukasiewicz.lean` proves this for any theorem predicate and any implication operation, without a freeness or injectivity assumption. Hence every new axiom is an original theorem.

Conversely the K/S/Peirce basis derives the original row

\[
((c\to u)\to a)\to((a\to c)\to(b\to c)).
\]

Here is a direct deduction-theorem derivation. Assume `H=(c→u)→a` and `J=a→c`. Under the temporary assumption `c→u`, MP with H gives a, and MP with J gives c. Discharge that temporary assumption to obtain `(c→u)→c`. Peirce with parameters c,u yields c. K then yields b→c. Discharge J and H. The deduction theorem used here follows from K and S alone, so this is a uniform finite proof in the proposed basis and permits arbitrary numerical substitutions, including the original alias 0.

Replacing axiom leaves by these finite derivations proves equality of theorem sets for the two numerical calculi. No set-theory weakening is involved, and the exact native CP/GIC/IR comparison therefore transfers at the logical level.

## The compiler experiment

The attributed backend is the same one used by the prior `specialized_axiom_compiler.py` investigations. Its matched source layout uses the prior 268-state optimized C/G conjunction arrangement. We held that arrangement, all constructor implementations and all retained logical rows fixed.

For each ordering of the K/S/Peirce rows, we searched 100 grammar seeds and exponents 2, 4 and 8. There are six orderings, hence 1,800 trials. Every proposed grammar was expanded and compared with its requested source token word. A complete table was generated for each needed framework/depth configuration, and the final table was reextracted to verify every source edge.

| Control | Working states | Decision states | Dispatch depth | AX macro calls | Logical rows | Destructive `u` reads | Grammar trials |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Original Łukasiewicz | 268 | 206 | 7 | 186 | 8 | 1 | 300 |
| K/S/Peirce | 272 | 210 | 7 | 196 | 10 | 0 | 1,800 |

The best K/S/Peirce push order was K, Peirce, S; the selected seed was 3 and exponent 8. The two tables have identical 62-state framework costs in this particular backend. The measured difference is four decision states. No inference that a routed 245-state machine would become 249 is justified without actually compiling and auditing that different backend.

Artifact identities:

* `basis_results/lukasiewicz/candidate.tm`: SHA-256 `169d97ddf7a1a722b3686aa414bd24a7bcf49c433b5c7b9e50fc1f20f356bed7`.
* `basis_results/K_S_Peirce/candidate.tm`: SHA-256 `9d865bb27cb57f69e175227497a0182b6505ea06df9c979b2c8cfd11cda72985`.
* `basis_results/results.json` contains the complete measured ledger.
* `basis_experiment.py` reproduces the measurements from the attributed pinned local compiler fixtures.

Two additional exploratory controls were emitted: K/Syllogism/Peirce at 271 states and K/S without Peirce at 269 states. This artifact supplies no independent completeness proof for those two systems and does not classify either as a consistency machine. They should not be used to improve the proved comparison in the table.

## The exact operational difference matters

Adding two rows changes the top-first AX list length from nine entries (eight logical rows and GEN) to eleven. The old eight-row proof-selector schedules cannot be reused literally. The generic block proof adapts by increasing the associated NIP counts by two: discard and bundle extraction use 12, GEN extraction uses 11, and a selected logical row at position j uses j pops followed by DROP and `13−j` pops. This does not itself add source instructions; these are finite command lists enumerated on the tape.

Deleting the embedded read of u also changes the proof-command encoding. The new AX command consumes selector c and additive fields x,y; it does not consume the old fourth field. A correct new abstract enumerator must match that layout. It would be wrong to leave the old command encoder unchanged merely because the resulting circuit has fewer macros.

Cofinal proof enumeration remains possible even without a spare u field. Use a leading reset command AX with selector 0, first additive field `v+1`, and second additive field 1. Its candidate code grows without bound as v grows. It resets d=h=0, and the contradiction block's contract quantifies over the resulting arbitrary current formula and stack. Thus the old padding idea has a straightforward new field choice, but a complete machine proof must implement the new command codec and prove its read contract.

## Separate fixed-bundle DNE control

The same older macro-level backend was also used to examine all 256 double-negation masks of its prior rearranged C/G layout, which has eight redexes. Each mask received 300 grammar trials, for **76,800 trials** in total. The minimum remained the unchanged 268-state control, with 206 decision states and dispatch depth 7. The complete ledger is `double_negation_results/results.json`; the sweep took about 521 seconds in this environment.

This does not rule out the original-layout six-redex fine-terminal optimization. The latter changes the grammar's available boundaries and keeps the routed 117-state framework; it is the separate experiment described in `dne_calculus_transfer.md`. In particular, DNE can shorten a primitive word while increasing its coarse macro count, so the two compression levels need not agree.

## Provenance

The compact original calculus is attributed to Mira-Cult, its upstream verification to Jeff Ketchersid, and the compiler to Andrew James Wade. Existing C/G regrouping and the specialized compiler are attributed incoming ProveIt work. The new measured experiment is the explicit K/S/Peirce replacement and search, together with the fixed-bundle DNE sweeps; it does not claim the standard K/S/Peirce basis or the prior 268-state layout as new.

Source basis: ProveIt `6446ff5668307a2ac6aee1896037f0b792090389`; original upstream specification and backend fixture hashes are recorded by the neighboring source audit and snapshot. The central primary mathematical reference for the old-to-new implication direction is the pinned repository's `Lukasiewicz.lean`; the short new-to-old derivation is given explicitly above.
