# Peano arithmetic is not finitely axiomatizable

This project gives a kernel-checked model-theoretic proof that first-order
Peano arithmetic has no finite axiomatization in its original language.  A
finite axiomatization means a finite list of arithmetic sentences with exactly
the same sentence consequences as the usual PA axiom schema.

The Lean development proves the unconditional headline theorem
`ProgramTrace.pa_not_finitely_axiomatizable`.  The independent Coq development
proves
`PATraceContractRealization.peano_arithmetic_not_finitely_axiomatizable`.
Both proofs reach the finite-basis conclusion without assuming fragment
strictness, trace totality, or trace functionality as hypotheses.

The compactness construction also yields an independently audited corollary:
first-order PA has at least two non-isomorphic models.  The Lean theorem is
`TwoNonisomorphicModels.peano_arithmetic_has_two_nonisomorphic_models`; its Coq
counterpart is
`PATwoNonisomorphicModels.peano_arithmetic_has_two_nonisomorphic_models`.
Both compare the standard model, whose elements are all values of standard
numerals, with a compactness model containing an element above every standard
numeral.  They use raw first-order structures satisfying the PA schema, not
the stronger meta-level `PA.Model` interface whose induction field ranges over
all host-language predicates.

## Proof architecture

The proof formalizes the Ryll-Nardzewski finite-Skolem-hull argument.  Its
central point is that the hull constructed below is deliberately only a raw
arithmetic structure.  Full PA is used in the ambient nonstandard model, never
silently assumed for the hull whose induction axiom will fail.

1. **Cofinal finite fragments.**  `PARankFragment n` contains the six
   non-induction PA axioms and every sealed induction instance whose source
   formula has structural rank at most `n`.  Rank-bounded syntax is explicitly
   enumerated, and every finite list of PA axioms is contained in one such
   fragment.
2. **A nonstandard ambient PA model.**  Compactness is applied to a
   relativized hereditary-finite-set theory with a named ordinal above every
   standard numeral.  The PA-in-HF interpretation turns the resulting model
   into a raw PA algebra satisfying every sealed PA axiom, with a distinguished
   nonstandard element `star`.
3. **A bounded-rank canonical Skolem hull.**  For the requested fragment rank,
   the construction closes `star` under arithmetic and canonical least/default
   witnesses for bounded-rank formulas.  Bounded-rank formulas are elementary
   between this hull and the ambient model, so the hull satisfies the requested
   rank fragment.  Every hull element is denoted by a standard finite `Program`.
4. **An arithmetized program trace.**  Programs have injective polynomial
   natural-number codes.  Closure-preserving finite beta coding supplies table
   parameters which are themselves denoted by programs and hence remain in the
   hull.  One fixed first-order formula checks all program rows through a target
   code.  Its default row is guarded by the assertion that no genuine output
   exists, so a valid nonzero row cannot coexist with a spurious zero row.
5. **Totality and functionality at standard codes.**  An external total
   decoder provides a canonical row at every natural-number code and agrees
   with every genuine program.  Strong induction on standard codes proves that
   any two valid trace tables—even tables with unrelated beta parameters—have
   the same output.  Thus standard codes name every hull element and the
   evaluator is functional at each standard code.
6. **The definable standard cut.**  A bound *covers* the hull when every element
   has an evaluator code below it.  Standard bounds do not cover, by a finite
   pigeonhole argument; every element above all standard numerals does cover.
   The formula saying “not covered” therefore defines exactly the standard
   elements of the hull.  It contains zero and is successor-closed, while
   `star` lies outside it, so its sealed PA induction instance is false.
7. **Finite-basis reduction.**  The hull satisfies `PARankFragment n` but
   falsifies a genuine PA axiom.  First-order soundness separates every rank
   fragment from PA.  Cofinality of the hierarchy then rules out any finite
   list of sentences with all PA sentence consequences.

The compactness construction and all semantic bridges use the repository's
own first-order calculus.  The final Lean kernel audit reports only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound` assumptions.  The Coq
realization is accepted by both `coqc` and `coqchk`.  Neither development uses
a project-local axiom or admission, a native decision procedure, or a
generated proof oracle in the argument.

## Lean modules

The main layers under `Lean/PAFiniteBasisReduction/` are:

- `Reduction.lean`, `Hierarchy.lean`, and `FiniteRankSyntax.lean`: finite-basis
  reduction, cofinal rank hierarchy, and finite syntax enumeration;
- `NonstandardHFFin.lean`: compactness model with a named nonstandard ordinal;
- `TwoNonisomorphicModels.lean`: the standard/nonstandard model comparison and
  the isomorphism-invariant numeral-generation argument;
- `FiniteSkolemCut.lean` and `CanonicalSelectors.lean`: the bounded-rank hull,
  elementarity, and PA-definable canonical selectors;
- `FiniteBetaCoding.lean`, `ProgramBetaCoding.lean`, and
  `HullTraceTransport.lean`: beta tables and rank-bounded transport without
  assuming PA in the hull;
- `ProgramTrace.lean`, `TotalProgramRows.lean`, and `TotalRowCases.lean`: the
  fixed trace formula and exhaustive total decoder;
- `StandardRowFunctionality.lean` and `StandardTraceFunctionality.lean`:
  semantic inversion and cross-table strong-induction functionality;
- `TotalTraceEvaluator.lean`: evaluator totality on all hull elements;
- `EvaluatorCutContract.lean`: the evaluator-independent definable-cut and
  pigeonhole argument;
- `TraceContractAssembly.lean` and `TraceContractRealization.lean`: assembly of
  the uniform countermodels and the unconditional headline theorem.

`PAFiniteBasisReduction/Audit.lean` checks the public theorem surface and
prints the kernel assumptions of the critical results.

## Verification

Lean, from the repository root:

```powershell
Push-Location Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Lean
lake build
lake env lean PAFiniteBasisReduction/Audit.lean
Pop-Location
```

The repository-wide Coq project can be rebuilt in dependency order:

```powershell
coq_makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
```

The exact focused `coqc` and `coqchk` commands for the final Coq realization
are recorded in [`Coq/README.md`](Coq/README.md).

## Why simpler arguments do not suffice

PA having an infinite axiom schema does not by itself preclude an equivalent
finite set of different sentences.  Likewise, the absence of finite PA models
is irrelevant: a single first-order sentence can force all of its models to be
infinite.  The construction above instead produces, for every finite fragment,
a model of that fragment which refutes a further genuine PA induction axiom.

## Related research report

[`SetTheory/Cardinals/docs/reports/ordinals-and-order-types/random-bits-arithmetic-cuts`](../../../SetTheory/Cardinals/docs/reports/ordinals-and-order-types/random-bits-arithmetic-cuts/)
(batch 114; AI-assisted, unrefereed, not formalized) studies the coding cut
of a random predicate `P` on a countable model of PA: the initial segment of
those `a` for which `P ∩ [0, a)` has an internal binary code. It claims the
almost-sure value of that cut for every independent bias law, the
realization of every cut and of every inclusion-monotone system of
conjunction cuts, and a three-regime classification of `IΔ₀(P, E)` and
`IΣ₁(P)` in the expansion `(M, P)`. It cites this README and two of its Lean
files, and describes them correctly. Three declarations are ingredients
only: `finite_list_beta_code` and `finite_vector_beta_code`
(`FiniteBetaCoding.lean`; externally finite lists in a raw PA structure)
cover the coding step of its Lemma 6.5 for lists of standard length, not
its Lemma 6.1 (internal sequences of nonstandard length) or its binary
`Bit` relation; `not_sat_inductionForm` (`EvaluatorCutContract.lean`, with
`sat_cutAt_iff_isStandard`) is the induction-failure pattern of its
Corollary 6.2 and Lemma 6.5, for a different formula and without a
predicate `P`. `raw_above_of_nonstandard` is used implicitly in the same
lemma. Its Section 11 proposes a formalization route built on this
project's raw first-order semantics; none of its modules exists, and
nothing in this project depends on the report.

## References

- C. Ryll-Nardzewski,
  [*The Role of the Axiom of Induction in the Elementary Arithmetic*](https://eudml.org/doc/213266),
  *Fundamenta Mathematicae* 39 (1952).
- A. Mostowski,
  [*On Models of Axiomatic Systems*](https://eudml.org/doc/213259),
  *Fundamenta Mathematicae* 39 (1952), 133–158.
- S. Berdugo Parada,
  [*Non-finite axiomatizability of first-order Peano Arithmetic*](https://diposit.ub.edu/bitstreams/0bda6e0f-6638-4222-b333-707b84556551/download).
