# Integration and formalization plan

This is a statement/proof-boundary plan, not a Lean implementation. No theorem
names below are represented as existing Mathlib APIs, and no formal verification
is claimed. The intended interface is `proposition_8_1` in
`Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections08_09.lean` at commit
`6a6d7961c3c261da7dc18def13fff30b12dd5c04`.

## 1. Normalize once

Use a nonempty finite abelian group G and its additive character group. Fix
`E_x = (1/|G|) sum_x`; define the normalized Fourier transform using negative
character sign, and inverse transform as the unnormalized sum over characters.

Distinguish these objects explicitly:

- `A(h) = E_x u(x+h) conjugate(v(x)) e(-eta(x))`;
- `Ew = sum_h w(h) |A(h)|^2`, without a second normalization;
- global `Eeta = E_h |A(h)|^2`;
- original Gowers `D_h(r) = sum_x f(x) conjugate(f(x-h)) e(-r x/N)`.

For a cyclic quadratic untwist, `|D_h(lambda h+mu)| = N |A(h)|`.
Losing this factor of N, or normalizing the dual sum twice, changes the theorem.

## 2. Minimal common-frequency layer

For arbitrary complex functions u,v and nonnegative real weights w, prove the
Fourier coefficient product identity

    a_xi = uhat(xi) conjugate(vhat(xi-eta)),
    A(h) = sum_xi a_xi e(xi(h)).

Next define

    W_xi(s) = sum_h w(h) u(s+h) e(-xi(h)),
    K_xi = E_s conjugate(v(s)) e(-eta(s)) W_xi(s),
    L_xi = E_s |v(s)| |W_xi(s)|,
    D = sum_xi |a_xi|.

Prove the exact identity `Ew = sum_xi conjugate(a_xi) K_xi` as a complex
identity whose right-hand side is a nonnegative real. Then derive

    Ew <= sum_xi |a_xi| L_xi <= D max_xi L_xi,
    D <= ||u||_2 ||v||_2.

The maximizer is selected only after the average over s. Selecting separately
for each s would fail to prove the intended common-frequency conclusion.

Prefer the denominator-free inequality as the core formal statement. Derive the
quotient form only under `D > 0`. If D=0, the coefficient identity gives A=0 and
Ew=0. The core statement is also valid for zero weights and zero functions.

## 3. Recover the original proposition, including degenerate cases

For odd N, set `q(x) = (lambda * inverse(2)) x^2 / N` as a circle-valued phase
and `g=f e(-q)`. With the backward derivative convention in the existing file,
prove the exact phase identity

    D_h(lambda h+mu)/N = e(-q(h)-mu h/N) A_mu(g)(h).

Apply the extraction layer with u=v=g and w the indicator of P. The output phase
is `psi(z) = inverse(2) lambda z^2 + r z`. Translation of the sum contributes only
a scalar phase of modulus one. For f the balanced function of A, prove

    sigma = E |f|^2 = delta(1-delta),
    B = max(delta,1-delta) for 0<delta<1,
    ||f||_1 = 2 sigma,
    B sigma <= 4/27.

The numerator in the original input is at least `beta N^2 |P|`, so the weighted
sum over translates is at least `beta N |P| / sigma` and the unweighted sum is
at least `beta N |P| / (B sigma)`.

For the implication to the existing `proposition_8_1`, handle first:

1. P empty: both lower-bound factors vanish, so any polynomial works.
2. beta nonpositive: nonnegativity of the conclusion suffices.
3. A empty or universal: f=0; with P nonempty the positive-beta premise is
   impossible.
4. The remaining case has positive beta, T, sigma, B, and spectral overlap;
   the quotient statement is safe. Put every existing `psi s` equal to the
   same psi and weaken the coefficient to `1/sqrt(2)`.

Do not silently change `ModAP` properness or membership definitions. The new
mathematical theorem requires only its carrier set. The old polynomial predicate
must still be discharged in the repository's exact representation.

## 4. Optional all-group quadratic-refinement API

This layer is independent of the odd cyclic specialization. Define a symmetric
biadditive map b into the circle group and a refinement q with q(0)=0 and
`q(x+y)-q(x)-q(y)=b(x,y)`. Then untwisting is a finite algebraic calculation.

Existence uses a decomposition of finite abelian groups into cyclic factors and
surjectivity of multiplication by a positive integer on the circle group. The
coordinate formula in Proposition 4.2 includes its full periodicity proof. Two
refinements differ by a character; therefore the extracted phase family does
not depend on the coordinate construction.

Even cyclic groups require circle-valued quadratic phases. In particular,
`q(x)=lambda x^2/(2N)` is periodic for even N. Do not model it as a ZMod N-valued
polynomial when lambda is odd: Example 4.3 rules out that target phase class.

## 5. Offset extremizers and stability

Prove the global power identity by Parseval in h. Translation by eta partitions
the finite dual group into cycles of length ord(eta). The order-two case counts
each undirected edge twice; all cycle lengths at least three count each once.
Order one is a loop/sum-of-squares case, not a simple graph case.

The graph core can be formulated independently of Fourier analysis. For a simple
triangle-free graph, probabilities p, neighbor sums d, and edge sum F, prove

    F - 4 F^2
      = sum_edges p_u p_v (1-d_u-d_v)
        + (sum_v p_v d_v^2 - (2F)^2).

The first term is nonnegative by disjoint adjacent neighborhoods; the second is
variance. An edge with positive product captures all but at most `1-4F` mass.
For cycle lengths >=5 its neighborhood union induces a four-vertex path. This
geometric fact is false for length four, whose neighborhood union is a cycle;
the split is essential to both equality and stability proofs.

For the long-cycle repair retain the two quantitative errors `ad` and `(U-V)^2`.
Delete the smaller endpoint, move the center mass to 1/2, and rescale the two
leaves to total 1/2. The proof gives an explicit L1 estimate and never uses an
unspecified compactness constant. Short-cycle repair has separate elementary
formulas given in Theorem 6.5.

The final Fourier lift preserves arguments and replaces magnitudes by square
roots of the repaired powers. Prove the squared-distance identity by Parseval.
The lift preserves L2 norm but not additional amplitude, reality, or indicator
conditions. Do not add those conclusions to the formal theorem.

## 6. Validation boundaries

The Python suite is executable numerical/exact regression support, not a proof
certificate checked by Lean. The exact integer graph identities can serve as
small-case tests after formalization. The general proof must use the symbolic
identity and graph geometry, not finite enumeration.

No changes to `gowers-proof-status.json` or `FORMALIZATION_STATUS.txt` should be
made until the proposed new modules build in the repository's own environment.
The existing Proposition 8.1 is already marked as proved in the inspected search
result; the proposed work is a strengthening, not a completion of an open proof.
