# Audit and completed formal contribution

## Pinned state

The requested commits were inspected using the GitHub plugin. This audit fixes
ProveIt at `4747142d5d15213eb711bdadfa3cc7e769fcb7a7` (16 October 2026).

* `6d8bc7f1ba02c83e54757366f019f61b966ed0b7` reconciles the nine-source
  closure-kernel collection. Its main path is
  `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md`.
  It carefully distinguishes the public attributed 253 table, the initializer
  deleted 252 runtime body, the separate prepared-tape 252 core, and the
  uncalibrated reduced-logic 252 experiment.
* `63c83cf79986f8a92bb75460848a1d4f863b7b15` updates project catalogues and
  pointers; it introduces no new machine equivalence theorem.
* `0301aa64e0676bed17402a63de46996631252a51` checks all 312,975 steps of the
  public 253 machine's blank bootstrap in Lean. It specifies the complete
  terminal frame, state 33 and head -17; it does not prove arbitrary runtime,
  proof search, or consistency calibration.
* At the later pinned state, nineteen source reports are reconciled. The best
  complete-logic Wade compiler control is 268 working states. Its grammar
  certificate compares the revised 217-node source word with 206 decision
  nodes; 62 framework states give 268. It is separate from the public
  Mira-Cult/mira-emmy 253 construction.
* The most recent correction at the pin withdraws a false histogram concern:
  the price is decision nodes + 55 + dispatcher depth. Compiling all 1,024
  source18 PSC controls reproduces the delivered histogram with five 283-state
  winners. The previously claimed six-versus-five discrepancy was an intake
  review error, not an error in the delivered experiment.

## The exact gap closed here

Commit `04d4900ac9d228054a8b3580141841636d9f693e` adds
`BusyBeaver/ZFC/TarskiComplete.lean`. The theorem `completeness` explicitly
assumes two `Kalmar.Classical` records, for the target theory and the empty
theory. At the pinned state, the referenced local `Lukasiewicz.lean` was absent.
The theorem itself is correctly conditional. Some introductory comments
overstate its status and, more specifically, say that primitive-falsity
classicality follows from the pure implicational row alone.

We now supply the missing reconstruction rather than merely report the gap.
The three new repository-ready files are:

1. `lean/BusyBeaver/ZFC/Lukasiewicz.lean`: a generic, explicit proof from
   the sole axiom `CCCpqrCCrpCsp` and modus ponens of K, S, and Peirce. It
   transcribes thirteen primary Metamath derivations (202 displayed proof
   rows, including 95 MP rows), attributed to Larry Lesyna and Jeffrey P.
   Machado and based on Lukasiewicz's original argument. Its interface allows
   an arbitrary carrier, arbitrary implication operation and arbitrary theorem
   predicate. It assumes neither syntactic injectivity nor a semantic model.
2. `lean/BusyBeaver/ZFC/TarskiClassicalBridge.lean`: instantiates that proof
   with the exact repository `Thm Ax` constructors, derives ex falso from K,
   S and the existing rho6, and exports `classical_from_rows`. It also formally
   proves that rho8+MP+GEN alone cannot give ex falso for primitive Bottom.
3. `lean/BusyBeaver/ZFC/TarskiCompleteClosed.lean`: supplies both missing
   classicality records and proves `completeness_closed` and
   `theorem_iff_semantic_consequence` with no propositional hypotheses.

The new endpoint is, for every `Ax : NF -> Prop` and every named formula f,

    Thm Ax f iff for every set-sized membership structure and assignment,
                   validity of every Ax formula under every assignment
                   implies validity of f.

The domain is nonempty whenever an assignment exists; the model produced in
the completeness argument is inhabited. Equality is interpreted as identity,
Bottom as false. This is full first-order consequence for the specified
calculus. It does not calibrate numerical aliases, theory emission, register
execution, a binary compiler, or a literal Turing machine.

Every new propositional reconstruction/bridge root is free of axioms. The
two unconditional completeness roots have exactly the standard Lean
dependencies `[propext, Classical.choice, Quot.sound]`, inherited from the
existing Henkin argument. There is no `sorry`, `sorryAx`, custom axiom,
`native_decide`, or semantic shortcut replacing the syntactic derivation.

All ten modules were rebuilt serially from source in a fresh temporary
directory with Lean 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`. The seven borrowed dependency files
match their pinned Git blob identities exactly. All compilation exit codes
are zero. The old `TarskiComplete.lean` emits six unused-variable lints;
the new modules emit no warnings. The reproducible record is
`lean-bridge-verification.json`, with 17 audited theorem roots.

The transcribed proof is classical prior mathematics. The contribution is
the checked implementation closing this specific ProveIt interface, not a
claim to have discovered a new implicational basis or a smaller machine.

## The falsity derivation, in full

Fix an arbitrary formula A and variable i, and put

    Q = forall i (forall i A -> Bottom).

The existing rho6 row is `(Q -> Bottom) -> A`. K gives
`Bottom -> (Q -> Bottom)`. Their composition gives `Bottom -> A`.
To expand the composition using only K and S, use these seven proof lines:

1. `(Q -> Bottom) -> A`                         (rho6)
2. `((Q -> Bottom) -> A) ->
      (Bottom -> ((Q -> Bottom) -> A))`          (K)
3. `Bottom -> ((Q -> Bottom) -> A)`              (MP 1,2)
4. `(Bottom -> ((Q -> Bottom) -> A)) ->
      ((Bottom -> (Q -> Bottom)) ->
         (Bottom -> A))`                       (S)
5. `(Bottom -> (Q -> Bottom)) -> (Bottom -> A)`  (MP 3,4)
6. `Bottom -> (Q -> Bottom)`                    (K)
7. `Bottom -> A`                               (MP 6,5)

No generalization, substitution, semantic falsehood axiom, or additional
machine row is used. This keeps the relative-falsity issue visible: if rho6
is removed or replaced, its ex-falso contribution must be recovered.

To see why rho8 alone is insufficient, interpret Bottom as true, each relation
and equality atom as false, every quantifier as identity, and implication as
material implication. Every rho8 instance is true; MP and GEN preserve truth;
`Bottom -> Rel(0,0)` is false. The file formalizes this induction as
`efq_not_from_rho8`, with no axioms.

## Reproduction and integration

Run `python reproduce_lean.py --lean /path/to/lean --output verification.json`.
This builds all sources offline into a fresh temporary directory, verifies the
seven pinned inputs, rejects any admitted theorem or unexpected axiom, and
records the logs. `generate_lukasiewicz.py` regenerates the explicit proof file
from `metamath-proof-steps.json` without network access; exact regeneration was
verified. The generator is outside the trusted proof boundary.

Copy the three new Lean modules into the matching repository directory. The
separate `tarski-documentation-correction.patch` only corrects two comments;
it does not change any old theorem. Import `TarskiCompleteClosed` wherever the
unconditional result is required. No existing repository file was modified or
pushed during this task.

Primary proof pages:

* https://us.metamath.org/mpeuni/impsingle-ax1.html
* https://us.metamath.org/mpeuni/impsingle-imim1.html
* https://us.metamath.org/mpeuni/impsingle-peirce.html
* https://us.metamath.org/mpeuni/tarski-bernays-ax2.html

The archived JSON lists every intermediate page and its formal proof rows.
