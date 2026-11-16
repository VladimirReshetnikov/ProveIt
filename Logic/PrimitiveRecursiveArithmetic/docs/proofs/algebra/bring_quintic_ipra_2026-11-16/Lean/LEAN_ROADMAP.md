# Lean completion roadmap

## Status boundary

`BringQuinticBlueprint.lean` is an uncompiled specification and dependency map. It deliberately contains no `sorry`, `admit`, or declared axiom, and it does not supply an inhabitant of `FormalizationObligations`. The existing ProveIt theorems imported by the final implementation—especially the quadratic, Cardano, and Ferrari factorization identities—are the only pieces currently claimed to be kernel-checked.

## Pinned repository

- Repository: `VladimirReshetnikov/ProveIt`
- Inspected head: `b73ff58ad10e9c446fa997777c5f502844249929`
- Primary roots:
  - `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA`
  - `Logic/PrimitiveRecursiveArithmetic/Derivations`
  - `Logic/PrimitiveRecursiveArithmetic/docs/proofs/algebra/lagrange_inversion_ipra`
  - `Logic/PrimitiveRecursiveArithmetic/docs/proofs/algebra/ipra_polynomial_formulas_abel_ruffini`

## Completion order

1. **Polynomial identities.** Add object-theory signed-integer terms for the SOS identity, Bring difference identity, scaling, depression, explicit factors, trinomial resultant, and the numerator of the differential resolvent. Close them with `ZT.derive`, `ipra_ring`, or the repository’s equivalent exact tactic.
2. **Rational codes and bisection.** Compile numerator/denominator arithmetic, exact order, midpoint, `bisectStep`, and the Boolean-folded bracket/width invariant. Define the fixed PR approximation symbol and prove regularity, residual, Lipschitz, oddness, and asymptotic bounds.
3. **Truncated series.** Implement vectors, Cauchy product, composition, Laurent residue, and the finite Lagrange theorem. Export the Bring coefficient theorem as a closed equality of finite vectors, not as a completed infinite series object.
4. **Cyclotomic algebra.** Implement the quotient by `1+W+...+W^4`, the root-of-unity filter, de Moivre product, four-resolvent product, and explicit examples.
5. **Finite groups.** Encode `S5`, `A5`, and `AGL(1,5)`; prove the two commutator identities and the minimal-normal-subgroup classification. Retain the 156-subgroup enumeration as a regression check, not the only proof.
6. **Finite fields and Frobenius.** Check the literal factor/remainder/Bézout vectors modulo `2`, `3`, and `7`, then prove the decomposition-group bridge from square-free factor degrees to Galois cycle types.
7. **Radical towers.** Encode finite extension and automorphism tables, Kummer kernels, normal series, and Lagrange-resolvent reconstruction. Connect to the checked degree `2–4` factorization theorems.
8. **Generic theorem.** Formalize the fixed field of the `S5` action through a terminating symmetric-polynomial normalizer. Combine it with radical-tower solvability and `A5` perfectness.
9. **Analytic lifting.** Reuse or complete ProveIt’s effective Cauchy/Taylor infrastructure for named complex disks, ratio-tail moduli, Puiseux branches, and the Cockle–Harley ODE.
10. **Global special functions.** Only after the preceding core is checked: theta constants, modular equations, icosahedral continuation, and certified Doyle–McMullen trapping regions.

## Required audit

A completed branch should add the exported theorems to the repository’s axiom-audit file and verify:

- `lake build` succeeds;
- no `sorry`, `admit`, or new object-theory axiom occurs;
- each final arithmetic theorem has a closed `Prf PRAAx` type (or is explicitly a metatheoretic compiler lemma);
- generated certificate files and the Python JSON reproduce byte-for-byte;
- every upgraded item in `STATEMENT_AUDIT.md` cites its final Lean theorem name.
