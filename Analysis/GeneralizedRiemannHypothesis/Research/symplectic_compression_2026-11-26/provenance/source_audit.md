# Source audit: lsernau/grh-lean

Prepared for the current research task, 26 November 2026 (client date).

## 1. Version and inspection scope

The live GitHub API returned commit **72fead102f663d5c7a407964a13dc0cf9d977207**, authored 2026-11-25T20:38:07Z, with tree **5eb1240f03e791edd3fc7aa84a3a7d8dc3997b7f**. The commit message is “Lean proof of GRH.” Source URLs below are pinned to this commit.

I fetched the readable edition's `GUIDE.md`, `README.md`, `Statements.lean`, `Main.lean`, `New/Main.lean`, the main inequality, the zero criterion, the positive-type lemma, the few-translates argument, the unfolding moment file, the height calculus, and the twisted-lattice determinant comparison. The full build and independent kernel replays were **not** rerun during this audit. The README reports successful compilation without `sorry` in `src`, the axiom dependencies `propext`, `Classical.choice`, `Quot.sound`, and independent checks by nanoda, con-leche and con-ron. Those are repository-reported checks, not fresh checks performed here.

The pinned toolchain is Lean v4.35.0, with Mathlib commit **56a005855ea17e0b0958f73ec801ae140b0a1679**. The README gives a full-build estimate of one to two hours on twelve cores and 24 GB RAM, plus a Mathlib build if caches are unavailable.

## 2. Exact public theorem scope

`grh/src/Statements.lean` imports only Mathlib and fixes the public statements. Its Git blob is **1cd1bce93344065936b2b392b23306254e0785ef**. The five exported theorems in `grh/src/Main.lean` (blob **1adf4187a938510363cdb0dde0a6d628ff39c600**) are:

1. `riemannHypothesis : RiemannHypothesis`, with Mathlib's standard type.
2. `riemannZeta_eq_zero_re : RiemannZetaZerosOnLine`.
3. `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`.
4. `LFunction_eq_zero_re : DirichletLZerosOnLine`.
5. `LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine`.

The third statement is, exactly in mathematical notation: for every positive modulus N, every complex Dirichlet character χ modulo N, and every s with Re(s)>1/2, L(s,χ)≠0 provided χ is nonprincipal or s≠1. The fourth puts every zero in 0<Re(s)<1 on Re(s)=1/2, for imprimitive as well as primitive characters.

This is **GRH for Dirichlet L-functions**. It does not assert GRH for every automorphic L-function, every Artin L-function, or arbitrary number fields. Abelian special cases may follow by standard factorizations, but the exported theorem should not be silently broadened.

Sources:

- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Statements.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Main.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/README.md

## 3. The actual proof architecture

The guide identifies three principal inputs:

- **A, short integral forms:** many source vectors have small archimedean sizes after a normalized Poincare map, and their images have controlled local indices.
- **B, enough forms:** second-moment estimates show that relatively few translates of those images span almost the entire target.
- **C, integral forms are long:** a twisted-lattice determinant comparison supplies a lower bound on the covolume of a sufficiently large independent integral family.

The central comparison is schematically

    mainAmount <= (V + 2 delta)/dim
               <= mainAmount - (n/dim) m rem + errors.

The common main amount cancels. `New.star_inequality` states the exact conclusion

    D.m * D.totalRemainder <= D.f * D.a * D.logB^5.

Here the independent family has n>=dim/2. The losses arise from archimedean size, local index, and determinant lower bounds, each much smaller than the canceled main term at the chosen scales.

The number-theoretic observable is

    R_(d,q)(x) = sum_(n<=x, n=1 mod q)
                 Lambda(n) (1-(n/d)) (1/n-1/x)
                 - log(x)/phi(q) - c_(d,q).

The resulting one-sided theorem says: if q is a positive multiple of 18480 and d is prime with d=q/2-1 modulo q, then for every epsilon>0,

    R_(d,q)(x) <= x^(-1/2+epsilon)

eventually. The criterion in `New/Reduction/Zeros/Criterion.lean` converts this into a zero-free half-plane. It chooses a quadratic twist with no zeros in a bounded rectangle, makes the real residues nonnegative, and applies the Landau argument to the meromorphic Laplace transform. The final functional-equation symmetry turns half-plane nonvanishing into critical-line zeros.

Sources:

- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/GUIDE.md
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/MainInequality.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/OneSidedBound.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Zeros/Criterion.lean

## 4. Transferable finite-field positivity lemma

`New/Spanning/SecondMoment/PositiveType.lean` (blob **2832d7465ef520ca8c216616ff2ca4e25c746e1c**) is a clean, finite, independently reusable component.

Let G be a finite group, pi:G->GL_n(F_q), and A_0,A_1 be n-by-m matrices. Let Theta:G->R be nonnegative and of positive type, meaning

    Theta(a^(-1)b) = <u_a,u_b>

for vectors in a complex Hilbert space. Suppose that, for every nonzero v in F_q^m, each of the two weighted stabilizer masses

    sum_(g: pi(g) A_0 v=A_0 v) Theta(g),
    sum_(g: pi(g)^(-T) A_1 v=A_1 v) Theta(g)

is at most Y>=0. Then `card_mul_sum_det_eq_zero_le` proves

    q sum_(g: det(A_1^T pi(g) A_0)=0) Theta(g)
      <= 2 sum_g Theta(g) + q^m sqrt(q^n) Y.

Its core is `re_sum_addChar_dotProduct_mul_le`: a bilinear additive-character sum is at most sqrt(q^n)Y. The proof realizes the sum as a Hilbert-space inner product of two orbit sums, whose squared norms are the two stabilizer masses times |G|. Character orthogonality then counts vectors in the kernel of the compression.

One can retain two distinct stabilizer bounds Y_0,Y_1 and use their geometric mean in the Cauchy-Schwarz step. That observation alone is a routine sharpening, not a substantial novelty claim. Likewise, merely replacing the singular indicator by a nonzero-kernel count or tracking the two coordinate axes exactly would be a small improvement.

Source:

- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Spanning/SecondMoment/PositiveType.lean

## 5. Transferable second-moment spanning lemma

`New/Spanning/SecondMoment/FewTranslates.lean` (blob **82f674740e21326fb1e22c6600035ce0addb9d62**) treats a unitary representation rho of a finite group on a target T, an invariant orthogonal projection P_0 onto a d-dimensional subspace, and a map B:S->T with source dimension s.

The near-isometry hypothesis is the lower mean-square condition

    dim U - epsilon s <= ||P_0 B P_U||_HS^2

for every source subspace U. The moment hypothesis is

    d sum_g ||B* rho(g) B||_HS^2 <= |G|(1+epsilon)s^2.

`isSpread_of_second_moment` then proves that, for every target subspace W of dimension alpha d, some translated map has preimage of dimension at most

    (1+alpha+3epsilon)s/2.

A greedy argument gives a set of at most ell translates whose image span has codimension at most

    max(16epsilon, exp(-2 ell s/(5d))) d.

The file explicitly cites **Welch (1974)** for rank bounds from second moments and **Wolsey (1982)** for greedy submodular covering. Therefore a generic effective-rank or greedy-cover bound should not be advertised as a fundamentally new theorem without a material additional feature and a literature comparison.

Source:

- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Spanning/SecondMoment/FewTranslates.lean

## 6. A distinctive transferable determinant principle

`New/Reduction/Lattices/Heights.lean` (blob **d5fac063830b3b0136829bf94b89f91f77273ea7**) and `TwistedLattice.lean` (blob **c6eacd876cd9b12bf9ded06150eedbdda966435b**) allow a **different auxiliary twist at each finite place**, while preserving a common global multiplier.

For a family y_iota indexed by pairs iota consisting of a rational prime ell and an isomorphism C~=Qbar_ell, `HeightLe c y` means that there exist H!=0, alpha, and h_ell>=0 such that all archimedean conjugates of H are bounded by exp(alpha), each |iota(H y_iota)|_ell is bounded by ell^(h_ell), and alpha+sum h_ell log ell<=c. The same H is essential; arbitrary unrelated local multipliers do not give a product-formula argument.

For injective twisted maps Theta_xi, put Z(xi)=det(Theta_xi*Theta_xi). Suppose y_1,...,y_n,z_1,...,z_n' is a basis. The family y has log squared-covolume at most c and local index loss at most delta. For each finite place choose an allowed twist xi_iota. Suppose auxiliary vectors z become integral after multiplication by gamma(xi), and have squared size at most exp(b_short) at the untwisted archimedean conjugates. If the families |gamma(xi_iota)|^(-2) and Z(1)/Z(xi_iota) have heights at most b_denom and b_volume, respectively, then

    0 <= c + 2delta + n' (b_short+b_denom) + b_volume.

This is `TwistedLattice.covolume_add_index_nonneg`. It combines a Gram-determinant factorization, uniform local integrality of the same original vectors under all allowed twists, and the product formula. It is directly relevant to any proposed extension that glues optimized local certificates into one global bound.

The files identify the general determinant size-versus-divisibility method as established, citing Bost, Laurent, Gaudron, and Bombieri-Gubler. The precise primewise-twist implementation is the useful technical feature to preserve.

Sources:

- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Lattices/Heights.lean
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Lattices/TwistedLattice.lean

## 7. Novelty and transfer boundaries

The guide explicitly says the `Lib`/`New` folder split is a working classification and the `New` namespace makes no novelty claim. A new theorem should be distinguished from extracting a pre-existing lemma or giving a standard consequence of Dirichlet GRH.

The strongest clean transfer possibilities are: a genuinely richer finite-field orbit statistic controlled by stabilizer masses; a spectral spanning theorem with a feature not implied by standard frame/covering inequalities; or a global determinant theorem permitting quantitatively optimized local auxiliary data while retaining one honest global product-formula certificate. Any proposed arithmetic extension beyond Dirichlet L-functions must separately verify all its replacement automorphic, twisting, and local integrality inputs.

No conclusion about the novelty of a new theorem follows from this source audit alone.
