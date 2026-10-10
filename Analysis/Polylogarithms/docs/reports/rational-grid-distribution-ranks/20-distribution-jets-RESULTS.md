# Result map

The labels below are stable LaTeX labels in `article/distribution_jets.tex`.

| Result | Label | Proof/certificate |
|---|---|---|
| Universal polynomial-weight quotient is free of rank phi(q) | `thm:universal` | Complete Fourier decomposition of the relation map; monic conductor normal form |
| Endpoint-anchored rank q-phi(q) | `cor:anchored` | Principal conductor coordinate is the endpoint |
| Even/odd formal quotient dimensions | `cor:parity` | Reflection diagonalized by character parity |
| Arbitrary finite-jet ranks | `thm:jet-rank` | Base change of an explicit split polynomial-module decomposition |
| Primitive-grid determinant factorization | `thm:determinant` | Conductor counts and exact multiplicities of character values |
| Local primitive-grid jet defects | `thm:smith` | Explicit powers of the local parameter in each character block |
| Noncentral resonances involve only one prime | `cor:central` | Rational independence of logarithms of two distinct primes |
| Smooth-number/finite residue normal forms | `thm:primitive`, `thm:finite-C` | Exact distribution rows and geometric residue sums |
| Exact support, signs, monotonicity, and denominators | `cor:support`, `cor:monotone`, `prop:denominator` | Finite subgroup support and rational operator inverse |
| Derived and underived Stieltjes reductions | `thm:derived-stieltjes`, `thm:underived` | Taylor/Laurent multiplication, with the explicit pole correction |
| Conductor-lifted cyclotomic trace | `thm:trace` | Polynomial normal form plus primitive Gauss sums |
| Exact trace zeros and leading derivatives | `thm:trace-zero`, `thm:principal` | Euler-factor vanishing and principal-pole cancellation |
| S4 cannot be obtained from the declared row vocabulary alone | `thm:S4-obstruction` | Eight-entry integer annihilator; 96 exact row checks; pairing 768 |
| Mixed diagonal antisymmetry need not vanish | `prop:mixed-diagonal` | Strictly positive integral for Im(Li22(-1,i)-Li22(i,-1)) |
| Cubic log-gamma formula, correctly attributed | `eq:cubic-known` | Published BBB formula, independently rederived by Fourier coefficients |

## The primitive-grid determinant

For p^e exactly dividing q, write M_p=q/p^e and h_p=ord_{M_p}(p), with order 1 modulo 1. In the specified Fourier and conductor bases,

    Delta_q(A) = product_{p^e || q}
      A_p^[phi(M_p)(p^(e-1)-1)] * (A_p^h_p-1)^[phi(M_p)/h_p].

Its vanishing describes failure of the primitive-grid basis, NOT a rank jump of the complete quotient.

## Remaining conjecture

The existing weight-five S4 formula is retained as Conjecture `conj:S4`. A fresh independent integral residual at 55-digit working precision is approximately 7.17e-57, but this is not a proof of equality. The exact finite row-space obstruction narrows what an eventual proof must add to this particular presentation.

## Further research

Section 11 develops eight directions: proving S4 with additional laws; integral/modular weighted modules; multivariate jet defects; sparse and interval-certified algorithms; higher-depth distribution modules; arithmetic reduction of trace jets; further Tornheim-derivative reductions; and proof-assistant formalization.
