# Mathematical and computational review notes

The manuscript is unrefereed. This note records the main proof checks and the
remaining distinctions reviewers should preserve.

## Proof-chain audit

1. **Mixed degree lowering.** The operator inverse for U(D) is a finite integer
   polynomial in D on the nilpotent translation module. It commutes with every
   other difference operator. This establishes the mixed-difference degree
   bound, not merely a repeated-direction test.
2. **Normalization.** Subtract P(0) before identifying its values with residues
   modulo p^(a+1). A residue r means P=r/p^(a+1) in the circle; multiplication
   by p^(a+1) as a circle-group operation would instead annihilate P.
3. **Degree budget.** The digit lift has degree exactly 1+a(p-1). The step
   correction has degree at most a(p-1). Subtracting it from Q therefore does
   not increase the original critical degree.
4. **Signs.** The atomic vectors are omega^(-1_{t<j}), whereas their correlation
   scores use the conjugate. Thus the prefix formula is S+(omega-1)B_j. The
   Laurent identity is checked before numerical root evaluation.
5. **Root geometry.** Competitor products give one root from each residue class
   modulo p and hence p distinct roots. Consecutive roots attain the general
   distinct-root maximum; their different block positions have different sum
   arguments. These facts control both the maximum and equality classification.
6. **Uniform versus weighted conclusions.** Transfer is pointwise and works
   for arbitrary probability measures. The uniform sharpness and equality
   classification use the equal sizes of the fibres of a nonzero linear map.
   They are not asserted unchanged for every fixed nonuniform measure.
7. **List quantifiers.** The dictionary is fixed before f. Cyclotomic
   independence excludes fewer than p candidates in that quantifier order.
   It does not prohibit returning one adaptively selected phase.
8. **Stability object.** The exact frame controls the conditional twisted
   function on the top-residue coordinate. It does not control the component
   of f with zero average on every fibre.
9. **Simultaneous theorem.** One index preserves aggregate squared energy.
   The explicit dual-basis example rules out an unrestricted componentwise
   guarantee for the same dictionary.
10. **Noniteration.** A reduction keeps degree d_a but lowers depth. It is not
    at the next depth's critical degree, so the linear-top-residue hypothesis
    needed for another application is unavailable.

## Computational checks

The archived run uses seed 20261007. Exact modular tests cover digit and step
degrees in 15 pairs (p,a), plus 48 multivariate examples and their candidates.
The cyclotomic checks were executed with SymPy 1.14.0 in Python 3.13.5.

The numerical part covers 600 random cyclic vectors, 150 weighted inputs, and
509,732 normalized finite root patterns. These are diagnostics, not rigorous
certificates of inequalities over real or complex variables. The analytic
proofs of sharpness and stability do not depend on their outcome.

All programs are independent of the repository's Lean files. No Lean compiler
was invoked. No formalization status should be inferred from the JSON's
`status: passed` field.

## Editorial corrections made during review

The residue-input notation was made explicit as P=r/p^(a+1) modulo 1.
The correlation envelopes are called norms only for degree at least one.
The next-degree research question explicitly imposes depth at most a, which
matters in characteristic two. The finite-abelian-p-group question does not
assume an exponent-p translation identity in higher-order directions.

The compiled PDF has no unresolved references or overfull boxes. Page-layout
inspection is recorded in the build validation file. The source has its own
bibliography and does not depend on external images or font files.
