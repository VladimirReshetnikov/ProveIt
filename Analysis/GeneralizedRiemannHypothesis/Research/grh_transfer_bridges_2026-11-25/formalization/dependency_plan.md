# Lean formalization plan

This is a dependency map, not executable Lean and not a claim of kernel verification.
There are no placeholder proofs packaged as completed results.

## 1. Finite character extension

Model finite abelian p-groups additively. First prove extension of a homomorphism
from a subgroup into the p-primary torsion subgroup of Q/Z. Then prove:

- A character on A extends with values killed by p^N and vanishes on D exactly
  when it vanishes on A ∩ (D + p^N B).
- If p^a kills B/A, every compatible character on A killed by p^N extends to a
  character killed by p^(N+a).
- Count the restriction image using annihilator duality.

These are independent of the automorphic proof. Keep D in the primary statement,
because forgetting decomposition-group conditions changes the arithmetic result.

## 2. Confluent independence

Work with a finite free commutative algebra over the localization Z_(p).

1. Divided differences of integer polynomials at integer nodes are integers.
2. The divided difference of binom(T,i) of order j has denominator dividing i!,
   vanishes for i<j, and equals 1/j! at i=j.
3. For j<p^s-1 and i>j, Legendre's digit-sum formula gives
   s(i-j) > v_p(i!/j!).
4. Transform the power columns by an invertible triangular matrix over Q.
5. Prove that a modular rank certificate implies Q-linear independence.
6. Check the two small exact matrices.

The scalar congruences can be checked in polynomial quotient rings by a finite
normalizer. The small rank certificates do not establish that the input integer
polynomials are the Hilbert/ring class polynomials: that separate CM identity must
be formalized or supplied by a formally verified interval method.

## 3. CM ray class interface

Required foundations:

- the ideal-theoretic ray class exact sequence;
- finite p-primary projection and the odd-p minus idempotent;
- CM unit quotient u/conj(u) is a root of unity;
- class-field reciprocity and tame conductor exponents;
- explicit decomposition/Frobenius interpretation.

The root-unit subgroup W must be retained. The p=2 case needs a different theorem.
The exact -23 calculation then uses the three reduced forms, the norm-27 element
beta, and the finite residue table already supplied.

## 4. Source covolume theorem

Import the existing New.TwistedLattice.covolume_add_index_nonneg and prove the
ordered-field rearrangement with the short-covolume and volume-height hypotheses.
The new statement can retain negative excess completion cost.

Source-specific weakening of integral_forms_long should be stated using its
same auxiliary forms, twist family, and height bounds, replacing only the rank
assumption by the completion budget proved in the report.

## 5. Unresolved interfaces

No formalization plan may mark these as supplied:

- a nonabelian target's Frobenius-sensitive arithmetic divisibility;
- a new automorphic lattice and its spanning/completion estimates;
- survival of Selmer witness bounds on the compatible character subgroup;
- identification of the custom odd-cocycle module with conventional strict
  Selmer cohomology;
- a complete residue cover for six-term equations of unpowered singular moduli.
