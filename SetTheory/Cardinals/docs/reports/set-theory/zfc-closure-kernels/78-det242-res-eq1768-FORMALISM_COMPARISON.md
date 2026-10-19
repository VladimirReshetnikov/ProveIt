# Formalism and encoding comparison

This investigation distinguishes changes to the theory, its proof calculus,
and its binary implementation. The **242-state result** keeps the current
calibrated numerical proof search and changes its literal implementation. The
separate **1,768-bit result** changes a finite equational target whose ordinary
consistency calibration is inherited. It has no compiled binary state bound.
All repository references below are pinned to
`e58338db7545909907e07a7603e8eb88625c527a`.

| Route | Established calibration and retained obligations | Concrete encoding assessment |
| --- | --- | --- |
| **Numerical C254 proof search** | The maintained Combined243 report supports the ordinary statement `ZFC ⊢ (nonhalting ↔ Con(ZFC))`. Its relative Lean machine comparison is distinct from a complete 243-state Lean consistency endpoint, which remains open. Our positive-block transfer preserves the same blank behavior. [1] | This route already has a complete binary table, initialization and runtime evidence. Removing inherited state 27 gives the actual **242-state** improvement. The numerical source and its theory remain unchanged. |
| **Direct first-order closure schemas** | The repository's closure axiomatization proves deductive equivalence with ZF while retaining Extensionality, Regularity, Separation and Power Set. Other reviewed seeded/positive/exact-fiber kernels have their own interpretation arguments. These require unrestricted formula instances and appropriate parameters. [2] | A short displayed schema still requires a complete first-order proof engine and instance generation. The reviewed raw numerical C/G shortcut has a finite-sort countermodel; the ordinary closure-theory results do not validate that shortcut. No state saving is inferred from schema length. |
| **Finite assignment/class clause kernel** | FC13B packages the formula apparatus into class incidence, evaluation, coordinate update and witness operations. The source-70 input includes explicit equality completion: **23 clauses and 57 literals**. Its ordinary ZFC calibration is inherited from the finite-kernel work, rather than supplied by our packet transformations. [3] | The retained clause payload is **1,499 bits** under its own format. A search must handle instantiated terms, genuine equality/congruence, collisions, fair enumeration and blank initialization. The clause-payload figure and a complete equational packet have different boundaries. |
| **Equational ground rewriting** | Source 70 turns the equality-free completed clauses into a nontrivial-model problem. Ground contextual rewriting connects designated Boolean zero and one exactly when the equational theory collapses. The Boolean basis is McCune et al.'s proved Sheffer axiom, not merely its finite truth-table test. [3,4] | Our exact transformations reduce the complete packet from **2,324 to 1,768 bits**. The final target has **22 equations, 420 term nodes and 44 rewrite orientations**. A complete ideal certificate enumerator exists, but its binary codecs, substitution, replacement and initializer still need implementation and state accounting. |
| **NBG-style finite class axioms** | The retained cyclic-algebra study uses a specific finite NBG-style source and published validity translations. Its audit records a repaired tagged Capture-to-Collection inference; the repair has a stated scope and does not automatically validate every informal NBG variant. [5] | Source 41 emits **14 intended source sentences**, but not its final translated ZFC-specific ground query or a binary backend. A finite axiom list therefore supplies a different candidate input, without an established smaller complete encoding. |
| **ZF and removal of Choice/Foundation** | These are calibration transformations that permit simpler source theories. The maintained Choice adapter builds an inhabited constructible model from a ZF model and compares finite refutations; it changes no machine row. Its external Lean theorem is separate from internal PA proof-code translation. Foundation-free closure arguments have their own stated hypotheses. [2,6] | This can remove axioms from a proof-search source when the consistency comparison is established. The current lineage already uses these reductions; merely citing equiconsistency provides no additional measured reduction here. |

## Why the selected alternative yields a measured improvement

The class kernel already contains enough assignment machinery to define its
membership predicate by incidence at two distinct fixed coordinates. Eliminating
that predicate removes its separate congruence equation. A powerset
embedding/retraction argument then permits fusion of the auxiliary Boolean
truth constant with the existing source constant. These changes reduce the
alphabet enough to cross from five-bit to four-bit opcodes.

Finally, an explicit alias for the repeated ground term `I(d,d)` saves term
occurrences. Replacing ternary congruence by two interderivable clauses lowers
variable capacity so that the alias fits within the same four-bit alphabet.
The complete packet saving is **556 bits, or 23.92%**; all syntax, headers and
endpoints are counted. [NOTES.md](NOTES.md) gives the ordinary model arguments
and the exact relative reachability theorem. The supplied executable checks
verify the packet and finite proof certificates; they do not establish a new
binary bound or upgrade inherited formalization status.

## References

1. [Combined243 README](https://github.com/VladimirReshetnikov/ProveIt/blob/e58338db7545909907e07a7603e8eb88625c527a/Computability/BusyBeaver/Research/ZFC/candidate-combined243/README.md).
2. [Closure axiomatization README](https://github.com/VladimirReshetnikov/ProveIt/blob/e58338db7545909907e07a7603e8eb88625c527a/SetTheory/ClosureAxiomatization/README.md) and [closure-kernels reconciliation](https://github.com/VladimirReshetnikov/ProveIt/blob/e58338db7545909907e07a7603e8eb88625c527a/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md).
3. [Source-70 intake, equational branch](https://github.com/VladimirReshetnikov/ProveIt/blob/e58338db7545909907e07a7603e8eb88625c527a/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-166.md).
4. McCune et al., [*Short Single Axioms for Boolean Algebra*](https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf), Theorem 2.
5. [Batch154, finite payload and cyclic algebraic alternatives](https://github.com/VladimirReshetnikov/ProveIt/blob/e58338db7545909907e07a7603e8eb88625c527a/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md#batch-154-finite-fusion-unary-union-and-algebraicassignment-kernels).
6. [Standard-ZFC Choice calibration](https://github.com/VladimirReshetnikov/ProveIt/blob/e58338db7545909907e07a7603e8eb88625c527a/Computability/BusyBeaver/Research/ZFC/choice_calibration254.md).
