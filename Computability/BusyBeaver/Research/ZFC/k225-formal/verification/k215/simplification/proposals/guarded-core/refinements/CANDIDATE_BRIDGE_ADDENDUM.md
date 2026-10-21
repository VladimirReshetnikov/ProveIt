# Candidate comparison: reuse the existing Core bridge

Source-inspection addendum, 2026-10-21. No compiler was run and no large formalization was started.

## The reusable bridge already exists

The source-bound, previously compiled Lean module
`k215-simplification-2/formal_cm215/CoreNativeBridge.lean` is not specific to CM215's invariant. Its `blank_iff` theorem is generic in:

- a repository `Machine (n+1)` D;
- a native `MarkerTransfer.TM` M, with `Q = Fin 303`;
- the dense-to-native labeling `ex` and native halt label;
- `Compatible D M ex halt`, namely every dense transition has exactly the native write, direction, and mapped target;
- absent native halt rows for both symbols; and
- `ex 0 = 0`.

It embeds the repository's finite-support tape by `Tape.read`, proves write/step/run correspondence, and identifies blank halting. It does **not** inspect the three-clause CM215 invariant. It does not require a separately supplied generic injectivity/bijection theorem for ex: the row and halt equations are enough for this synchronous embedding. Do not propose another general tape/renaming bridge.

`CM215Core.lean` already instantiates this interface with finite all-row `decide` proofs, exact primary `KDense215.machine215`, literal alternative rows, and the existing label list. I rechecked the two source hashes against their successful Lean 4.32 receipts. The older `k215-transport/formal/CM215CoreBridge.lean` likewise offers a reusable `Commutes`/`blank_iff` interface, although its state types are fixed to the 215-state dense presentation and its semantics are partial. The newer direct native bridge is the natural fit for these three native tables.

The 215 `CM215Core.nativeLabels` are exactly the sorted working labels of the current K215 native table. They also exactly equal the inverse dense labeling in the incoming M125 canonicalization. M124 and FM215 preserve this same working-state set. Thus the existing `ex` labeling can be reused for all three, rather than reproving a novel renaming scheme. One still must kernel-check the new literal row-compatibility equations.

## What actually remains for M124, FM215, and M125

The new marker theorem is in **Coq**, whereas this existing Core adapter is in **Lean**. Source equality and successful Coq checking do not let a Lean theorem import that proof.

This does **not** mean each candidate lacks a native Lean theorem. Earlier packets already contain these interfaces:

- `Marker124.all_tapes` proves old/new halting equivalence for every tape at state0. Its `Config` has a `Nat` state and a head-centered `Int -> Bool` tape, and its total step freezes at designated halt254. Its `Active` invariant and `old_reachable_states`/`new_reachable_states` constrain reachable labels. The packet README reports successful Lean 4.32 checking with `propext`, `Classical.choice`, and `Quot.sound`.
- `FM215.all_tapes_halts_iff h t` proves old/new halting equivalence for every absolute head and tape at state0. Its states are `Fin 512`, actions are triples, and `step` is partial, returning `Option Config`; it uses `PositiveSimulation.Halts`. The supplied Lean 4.32 receipt reports exit0 for the simulation, data, and theorem modules, with `propext` and `Quot.sound` for the theorem. This review inspected the native interfaces; it did not rerun either compiler.

Neither interface is definitionally identical to the newer `CoreNativeBridge`'s `Fin 303`, row-structure, totalized-step model. Reuse requires a semantic identification, not a new invariant proof. For M124 this includes centering an absolute tape by `center(h,t)(i) = t(h+i)`, identifying bounded active native labels, and identifying designated-label halting with missing-row halting on the reachable image. For FM215 the tape/head convention already agrees; the remaining adapters identify `Fin 512` versus native labels, triple actions versus row structures, and partial halting versus totalized iteration with a missing-row predicate. The older partial `Commutes` bridge offers an alternative starting point, but its fixed state types still need matching or generalizing. A generic cross-kernel transfer of the new Coq checker is a separate optional development, not a prerequisite for reusing these existing Lean instances.

For the Lean endpoint route:

1. Reuse the existing M124 or FM215 native Lean theorem after proving the relevant semantic identification above. For M125, identify a matching existing native theorem or instantiate/generalize the two-marker proof at provider125; this review has not established an existing M125 Lean instance. Porting the shared Coq checker is another option, not a requirement for the two existing instances. Preserve the distinction between designated-label, partial, and missing-row halting.
2. Instantiate literal native and dense tables, using the existing native labels and row interpretation. Discharge `Compatible`, both absent halt rows, and start-label equality. The old K215 side can reuse its exact existing binding after the literal data identification.
3. Apply `CoreNativeBridge.blank_iff` on both sides, compose with the new native transfer, and then use the same existing `KEndpoint215` transitivity adapter.
4. Compile the affected full endpoint closure and retain assumption reports. This last full-ZFC replay is also not claimed by the existing standalone CM215 packet.

This route directly reaches the repository's Core `Machine`/`BlankHalts` interface. It does not require a new proof through zipper tape semantics. A Rocq-only route would instead need compatible Rocq endpoint semantics; the Lean adapter cannot be assumed to provide a cross-kernel bridge.

## Qualified recommendation

M124/FM215/M125 have the **simplest new local invariant**: two strict predecessor-marker clauses, with no exceptional incoming case. CM215 needs a third auxiliary clause at state156 to justify the exceptional incoming route into176.

CM215 currently has the **shortest demonstrated route to the repository's exact dense-machine interface**, because that concrete bridge and primary-machine equivalence are already compiled. Its full ZFC transitivity adapter still awaits the full closure replay identified by its own receipt. The three strict-marker candidates can reuse the generic bridge; for M124 and FM215 the remaining gap is interface matching and finite exact-table instances, not absence of native Lean proofs or new general tape theory. For M125 the native proof instance remains to be established or located.

There is no global winner: distinguish local invariant simplicity, proof-assistant compatibility, completed exact-table integration, and full endpoint replay. Primary K215 remains the least disruptive baseline for simplifying the maintained complete proof.

## Source pins

- [Generic Core-native bridge](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification-2/formal_cm215/CoreNativeBridge.lean), Git blob `88c8a25edcfd8dab49ebdde6fda01349df35b358`.
- [Compiled exact dense instance](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-simplification-2/formal_cm215/CM215Core.lean), Git blob `b3123d427fc00b08c77fba9fdd7d5299edf7d180`.
- [Earlier reusable partial bridge](https://github.com/VladimirReshetnikov/ProveIt/blob/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-transport/formal/CM215CoreBridge.lean), Git blob `e80a240181f5d0d993947fe465720b9172d84555`.
- [Existing M124 native Lean theorem](https://github.com/VladimirReshetnikov/ProveIt/blob/aa66d0a33f1f8237a348899eb8095b045a502832/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/zfc215-simplification/m124_lean/Marker124.lean), Git blob `2ed7994fe8703e34b55ac07f31666956ce87196b`.
- [Existing FM215 native Lean theorem](https://github.com/VladimirReshetnikov/ProveIt/blob/aa66d0a33f1f8237a348899eb8095b045a502832/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/fm215-compression/formal/FM215.lean), Git blob `7e43154c63622cf88d8940707ac0c9ca0e1c2528`, and [its supplied kernel receipt](https://github.com/VladimirReshetnikov/ProveIt/blob/aa66d0a33f1f8237a348899eb8095b045a502832/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/fm215-compression/formal/fm215-kernel-receipt.json), Git blob `74531a908f01a7721ca1ddd987ac4d5390993764`.

The supplied earlier snapshots and receipt audit establish these statements at the displayed pins; this addendum does not claim a newly compiled instance or fresh full endpoint run.
