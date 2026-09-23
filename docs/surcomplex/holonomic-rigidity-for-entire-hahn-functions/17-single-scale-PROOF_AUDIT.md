# Proof audit

Date: 23 September 2026.
Scope: a written-argument audit by the same assistant that prepared the draft,
plus exact finite regression checks. This is not independent peer review,
formal proof checking, or certification of novelty.

## Core mechanism

1. **Top total degree, not highest derivative.** A proposed equation is cleared
   of q,z denominators and its maximal total jet degree D is chosen. A target
   has exactly D high indices. This prevents a competitor of degree <=D from
   matching all high indices while adding low ones.
2. **Largest differing index.** At the largest differing k, the leading height
   contribution is at least b_k; the lower contributions are at most
   2 D b_(k-1). For factorial heights N >= max(3,4D) and N!/2 > H suffice,
   where H is the q-degree of the cleared equation. This argument works
   against every competing multiset, not just competitors in a finite window.
3. **Polarization is nonzero.** Distinct jet monomials give disjoint symmetric
   monomial orbits of derivative-weight tuples. Characteristic zero prevents
   the positive integer multiplicities from vanishing.
4. **Repeated indices are avoided.** Each private index set is partitioned into
   finitely many disjoint infinite subsets, one per slot. This makes all
   selected indices distinct and makes the polarized coefficient exactly the
   coefficient of the target multiset. No repeated-index normalization is
   hidden in the proof.
5. **Mixed weights really are dense.** Rapid ratios imply b_n dominates every
   power of n. Thus every nonzero rational polynomial at (n,b_n) is eventually
   nonzero, by dominance of its highest b_n power. General characteristic-zero
   coefficients reduce to finitely many rational polynomials by choosing a
   basis of their finite-dimensional Q-span.
6. **The z-shift is fixed.** In the mixed proof, after selecting the target
   multiset T, the coefficient z^M with M=j_0+sum(T) forces the chosen
   coefficient power j_0. Height separation excludes all other multisets.
   This handles polynomials in z in the equation, not just autonomous ones.

## Exact relation ideals

7. A finite family of 0/1 streams has only finitely many membership patterns.
   The union of finite nonzero pattern classes is finite. Its contribution
   must be retained as an affine polynomial correction.
8. The infinite pattern classes are disjoint. Their series satisfy the joint
   independence theorem. A full-row-rank constant matrix maps their free jet
   variables to free coordinates; a right inverse proves injectivity on
   polynomial rings. The remaining coordinates are zero. Transforming back
   gives the entire differential kernel, not just its dimension.
9. The same matrix acts on each jet block. This proves the exact rectangular
   mixed-jet degree (r+1)(s+1)d, and the ordinary-jet degree (r+1)d.
10. The finite-alphabet extension keeps coefficients in the constant field.
    It does not cover arbitrary infinite alphabets. The stream (1,n) gives
    the obstruction F_2=Theta(F_1).

## Base fields and interpretation

11. Pure external differentiation extends constants by an invertible finite
    coefficient minor. This is not a general assertion that arbitrary
    algebraic independence survives adjoining arbitrary ambient elements.
12. q remains transcendental over the prime field in each Hahn application,
    because a monomial of positive valuation has distinct integral powers.
13. The external derivative D_z fixes every scalar in the Hahn field. The
    intrinsic BM derivative does not fix q: BM(q)=-q^2. Their theorems are
    separate. The identity BM^j=(-1)^j q^j delta(delta+1)...(delta+j-1)
    supplies the intrinsic numerical transfer.
14. Bounded-support descent is attributed to the repository and reproved.
    In each coset of the cofinal integer lattice, a bounded Hahn coefficient
    has finite support. Projection reduces a putative relation to Laurent
    polynomial coefficients. Cofinality is a real hypothesis.
15. The mixed differential theorem is over k(q,z). It is not automatically a
    theorem over an arbitrary differential extension of the Hahn scalar field.
16. All numerical transcendence claims specify a base. The witnesses themselves
    lie in R((q)); they are not transcendental over R((q)) or all of No.

## Strong summation and omnific results

17. The entire proof uses the cofinal lower bound (b_n-mn) eta. Entire-ring
    closure under products uses lower bounds for both weighted coefficient
    sequences and the fact that one convolution index must be in a tail.
18. Full-class summation does not follow merely from an ordinary limit of
    valuations. For z=c t^gamma(1+u), the proof separately uses eventual
    increase of b_n+n gamma, the positive support monoid of u, and Hahn
    finiteness of representations. This is strong summation, not fine-topology
    convergence in the full class.
19. If gamma is negative infinite, the leading valuations strictly decrease
    along every infinite index set. This makes the original family
    nonsummable. Hypothetical cancellation cannot define an inadmissible sum.
20. The faithfulness argument is for finite polynomial expressions in the
    given generators. Their coefficients have a common valuation lower bound.
    A sufficiently small positive monomial argument isolates the first nonzero
    Taylor coefficient. Regrouping is justified by finite products of the
    already summable generating families.
21. For the coding scale M=omega^Lambda, Lambda is positive infinite. Distinct
    powers M^j have disjoint real-exponent support cosets. Thus M is
    transcendental over the full real-exponent Hahn field, which already
    contains the bounded-support fraction base and all the numerical witnesses.
22. The code exponents Lambda-b_n are all positive, and the constant coefficient
    is zero. This proves membership in Oz. Algebraic independence of codes
    does not prove their intrinsic differential independence, irreducibility,
    or primality.
23. The floor retains exactly the terms with an-n! >=0. The remaining sum is a
    positive infinitesimal. A positive nonzero omnific integer is >=1, so this
    identifies the actual omnific floor. a is an ordinary nonnegative real.

## Imported foundations

Conway normal forms and their Hahn interpretation; standard Hahn support and
Neumann summability facts; the normalized BM derivation with real constants,
strong additivity, product rule, and BM(omega)=1; and the normal-form definition
of the omnific integers. These foundations are cited, not rebuilt or formally
verified in this package.

## Verification boundary

Recorded result: 8,608 finite checks passed on Python 3.13.5, SymPy 1.14.0.
The count includes related examples and many checks of the same lemma. It is
not a count of independently proved theorems. No test quantifies over all
supports, all differential equations, or a continuum family.

The universal order-unit rigidity question remains unresolved here. Classical
single-series gap differential transcendence is explicitly not claimed new.
