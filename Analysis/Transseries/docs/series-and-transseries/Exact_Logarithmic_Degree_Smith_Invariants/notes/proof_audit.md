# Proof audit and boundaries

## Domain

- The coefficient field is the real Hahn field in x, log(x), ..., log_n(x), n >= 1.
- Exponent supports are reverse well-ordered in lexicographic order.
- The derivative is the strong, coefficientwise extension of monomial differentiation.
- Every perturbing coefficient lowers the outer x exponent by a common epsilon > 0.
- The forcing belongs to the base field and is independent of the added logarithm T.
- Solutions classified are in H_n[T], with finitely many nonnegative integer T powers.
- Real indicial roots contribute; nonreal roots are not treated as oscillatory monomials.

## Proof chain

1. Normalized integration is constructed recursively through logarithmic depth.
   Nonresonant blocks use a strong geometric derivative inverse. The unique omitted
   lower monomial is sigma = 1/(L ell_2 ... ell_n).
2. Integration by parts yields exactly m moments for the image of delta^m.
3. These moments construct the normalized kernel/cokernel splitting of P(E).
4. A central derivative parameter z replaces the full Euler operator by E+sigma z.
   The powers are noncommutative operator compositions, not binomial expansions.
5. A formal inverse exists by an outer-small constant-term inverse and a z-adic
   inverse. In a word of fixed z degree, preserving letters consume z degree and
   lowering letters consume outer exponent. This proves strong summability.
6. Projection to finitely many root levels gives the exact word bound Q+k.
7. The root crossing has an antidiagonal residue matrix, with determinant equal
   to a nonzero root-factor power times the squared factorial product.
8. Root triangularity implies determinant valuation r and inverse pole order <= s.
9. Classical Smith reduction and its degree-preserving action on polynomial
   vectors give the exact degree classification. The Toeplitz systems are the
   literal coefficient equations in divided powers.
10. For the exact-pencil subclass, A maps the negative-L subspace down by one;
    normalized G preserves that subspace after A. Pure resonant sigma terms are
    removed by GJ=0. Hence all correction words have zero residue.
11. Rational interpolation gives the universal scalar realization; nilpotent
    matrix powers prove the explicit cancellation and minimality assertions.

## Points that must not be silently strengthened

- n >= 1 is essential for the multiplicity-independent distinct-root bound.
- The normalized primitive of an arbitrary L^-1 block may involve lower logs;
  the pencil proof removes specifically the pure sigma monomial, not all such blocks.
- Finite word depth is not synonymous with effective arbitrary Hahn arithmetic.
- Classification through M_(s-1) and explicit reconstruction at degree s are
  different tasks: the latter can need M_s.
- The degree-zero matrix's nilpotency is not the logarithmic index. The scalar
  example explicitly reverses that proposed inference.
- Formal support truncation is not a numerical remainder bound.
- A solution's residue coordinate polynomial is not itself the full scalar solution;
  the normalized lift includes lower blocks and derivative corrections.
- Positive logarithmic indices correspond to Jordan blocks; the full r-tuple also
  contains zero Smith exponents.

## Verification scope

The primary exact suite has 1,383 passing assertions. Its general polynomial
matrix examples are finite representatives used to test Smith/Toeplitz algebra,
not a claim to realize every such matrix by a scalar differential operator.
The independent scalar operator suite has 192 passing exact column checks for
a = -1 and +1. It handles noncommuting derivative terms explicitly and uses a
lower guard cutoff at L exponent -10. Its output is a finite regression check.

No new Lean or other proof-assistant checking was performed. No independent
peer review or exhaustive literature priority search is claimed. Established
Smith-form, Toeplitz/Jordan-chain, and generalized-series methods are credited.
