# Independent audit of full-normal completeness

Audited `/research_notes/calculus_reduction.md`, specifically the single-introduction recovery, transfer through the stable seven-rule calculus N7, and inheritance of the ordinary iPRA bridge.

## Conclusion

I find no circularity in the displayed completeness argument, provided the normalization facts are proved in the already established **raw** native calculus and N7's substitutions are consistently hereditary-normalizing substitutions. No full-formula transport or arbitrary numerical substitution theorem for the new six-rule calculus is needed before the equivalence is established.

## Dependency order that makes the argument valid

1. Establish weakening, injective renaming, and cut directly for the six-rule calculus. Proof replacement changes neither the witness term nor the root of a matrix, so it preserves the DI guard. Under an eigenvariable binder, shift the inserted proof by injective renaming. This is substitution of proofs for assumptions, not the problematic substitution of numerical terms for variables.
2. Obtain atomic two-sided transport from the two applications of crossed Tr given in the notes. The normalization-substitution composition law makes these template instances literal equalities of normal syntax.
3. Derive the zero-witness packet and, inside its DE scope, the equality `b=0`. Recover atomic DI-case at witness zero using atomic transport and cut only. The proof does not assume full formula transport; the omitted mode occurs only for a literal equation.
4. Recover direct QI-progress from DI-progress at witness zero with a dummy existential variable, then DE. Its minor proof is the Q hypothesis itself. Conversely, recover witnessed progress from QI and ordinary case introduction by QE. Thus Six and N7 have exactly the same derivable normal sequents.
5. Translate raw NPrf proofs forward into N7 by induction. Normalize all term data, including the term template in Tr. The normalization-substitution law handles Tr, QE, DI-case, and QI-progress. Injective renaming handles DE and fresh-variable context shifts. Both computation axioms become Refl. No substitution theorem about Six is used.
6. Translate N7 proofs backward into raw NPrf. Here, and only here, use the **previously established raw** equality and Q/D congruences, raw cut, raw formula transport, and raw equation induction. These supply equivalences between each raw substituted formula and its normal form. Use the raw kernel's original case/QI rules after converting the premises, then convert the conclusion back.
7. Extend the backward result from normal sequents to an arbitrary original raw sequent using the raw interderivabilities `A <-> N(A)` for assumptions and conclusion. Compose with the baseline's existing native/iPRA translations and round-trip theorems.

## Two details that should be explicit in the final report

**The normalization equality lemma includes iterator bodies.** It should state that for every raw term `t`, with any free numerical variables, the raw theory proves `t=N(t)` with no logical assumptions. A reduction in an iterator body is not justified merely by first-order argument congruence of a ternary function: the body is bound syntax. Use pointwise body equality in a fresh accumulator and the raw theory's equation-induction proof of iterator-body congruence. This is permissible because the raw arithmetic bridge and induction theorem precede the new construction. The notes currently acknowledge this correctly.

**The ordinary reading of QI is precisely quantifier-free induction.** Given `Gamma,E(z) |- E(Sz)` with `z` fresh for `Gamma`, the ordinary iPRA interpretation derives `forall z (E(z) -> E(Sz))`. Because `E` is a literal equation of iterator terms, its translated formula is an equation between primitive-recursive terms. iPRA's quantifier-free induction gives `E(0) -> forall y E(y)`, which is exactly the ordinary Q-reading. No induction on an arbitrary Q/D formula is introduced. The ordinary case rule uses the baseline's coverage theorem together with ordinary intuitionistic logic.

## Round trips and scope

On normal syntax, normalizing after inclusion is syntactic identity. On raw syntax, inclusion after normalization is provably the identity by the raw normalization equality and formula-congruence lemmas. All numerical variables remain the same variables and actual equality is retained, so the model-level round-trip graph is `x=y`. This is the right route for inheriting the baseline's ordinary bi-interpretability claim; a theorem-set equivalence alone would not suffice.

This audit does not add a proof-assistant verification or a checker-size claim. It also leaves the separately reported uniform-normalization/primitive-recursion qualification unchanged.
