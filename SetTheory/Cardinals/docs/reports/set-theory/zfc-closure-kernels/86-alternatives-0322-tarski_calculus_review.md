# Conditional completeness of the substitution-free Tarski calculus

Independent review, 16 October 2026, of the six modules at upstream commit
`04d4900ac9d228054a8b3580141841636d9f693e`: `Kalmar`, `TarskiCalculus`,
`TarskiDerived`, `TarskiLeibniz`, `TarskiClean`, and `TarskiComplete`.

Subsequent work on the same date closes the propositional gap identified
below: [the attributed Lean certificate port](lukasiewicz_basis.md) constructs
`Tarski.classical` and proves `Tarski.complete` without supplied `hC`/`hC0`.
The original review remains a record of the imported six-module state.
Numerical syntax, runtime falsity, theory and machine bridges remain open.

The new result is a kernel-checked **conditional first-order completeness
proof** for the named-variable calculus `Tarski.Thm`. Its formulas have
membership, genuine equality, a primitive falsity constant, implication and
universal quantification. The rules are all eight original logical rows,
both gated atomic vacuity families, modus ponens and unrestricted
generalization of theorems. Theory axioms must hold under every assignment.
This is the full equality-bearing calculus; it does not repair the reduced
fixed-slot systems refuted by the earlier countermodels.

`Tarski.soundness` interprets equality as identity and falsity as false.
`Tarski.completeness` concludes `Thm Ax f` from validity of `f` under every
assignment in every model of `Ax`, **given** both
`Kalmar.Classical imp bot (Thm Ax)` and the corresponding empty-theory
structure. `Classical` includes K, S, Peirce, ex falso and modus ponens.
Those structures are explicit theorem parameters, not axioms added to Lean;
these six files do not construct them from `rho8`. The empty-theory
structure already implies the structure for arbitrary `Ax` by `Thm.mono`.
The independent scratch caller checked this monotonicity consequence.

The mathematical proof has the needed capture protections. `rn` replaces
free occurrences and stops at a binder of the renamed label; its semantic
lemma and Leibniz/specialization lemmas require that the source and target
labels are not bound in the matrix. Fresh alpha-renaming produces a clean
form before the truth lemma. The Lindenbaum chain revisits every formula
infinitely often, adds fresh counterexample labels above any requested
bound, and hence gives every equality class arbitrarily large
representatives. The quotient term model is nonempty. Universal closures
of theory axioms ensure that the model satisfies each axiom under every
assignment, including theories with infinitely many formulas and parameters.
I found no gap in these conditional arguments.

Two source comments overstate the present repository state:
`TarskiDerived.lean` and `TarskiComplete.lean` refer to
`Lukasiewicz.lean` / `Tarski.classical` as discharging the assumptions, but
neither declaration/file is present at the reviewed commit. Moreover,
**rho8 alone cannot supply ex falso for an arbitrary primitive `bot`**:
pure implication semantics may interpret that symbol as true. This is not
an obstacle once the pure implication basis has been obtained: the
independent scratch caller formally proves ex falso from K/S and `rho6`,
with no axioms. Thus the actionable next calculus task is to provide the
actual K/S/Peirce certificates and assemble the required `Classical`
structure, rather than describe that task as completed.

This result does not yet connect named formulas to the numerical runtime
syntax, a machine's relative falsity alias, its literal theory bundle,
proof enumeration, compiled register program or binary transition table.
It proves no new state bound or end-to-end equivalence with consistency of
ZFC. A future unconditional logical-calculus theorem and those adapters
remain separate obligations.

All six modules were rebuilt serially with pinned Lean 4.32.0 (compiler
commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`) against the previously
source-verified 38-module dependency cache. An additional caller printed
the two principal signatures and audited 21 theorems. Every check passed;
no `sorryAx` or custom axiom appeared. Completeness uses only `propext`,
`Classical.choice`, and `Quot.sound`. Dependencies, including the expensive
`Boot253` certificate, were reused rather than rebuilt in this scoped run.
The exact build/audit outputs and module blob IDs are preserved in
[results/tarski-verification.json](results/tarski-verification.json).

