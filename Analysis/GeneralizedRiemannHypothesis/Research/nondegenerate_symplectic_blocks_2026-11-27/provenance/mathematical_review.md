# Independent review: critical nondegenerate symplectic blocks

Reviewed on 27 November 2026 against the mathematical draft, subsequently assembled as `paper.tex`. This is an adversarial mathematical review and targeted primary-literature comparison, not a machine-checked formalization or external peer review.

## Verdict

The exact likelihood, sign separation, optimal detector, exact total-variation identity, exponential rank-universality estimate, limiting positive distance, and supplementary defect-rank universality theorem in the mathematical draft all check. I found no unresolved mathematical gap in the supplied proof. Characteristic two is included correctly because every matrix called alternating has zero diagonal, not merely skew symmetry.

The main theorem is substantive in the growing-dimensional critical regime. Its novelty should be formulated as a candidate new combination of a complete likelihood test, persistent full-matrix separation, and exponentially vanishing rank-only separation for nondegenerate half-blocks. Neither raw symplectic frame counts nor exact alternating-pencil/subspace intersection counts should be claimed as new.

## Independent checks of the fibre calculation

For the initial review, use the draft notation (translated to the final paper notation in the addendum below): `N=2m`, `b_j=prod_(i=1)^j(1-q^(-2i))`, `a_j=prod_(i=1)^j(1-q^(-i))`, `S_j=|Sp_(2j)(q)|`, and `alpha_m=b_m^2/b_(2m)`.

The first N columns of a uniform symplectic matrix for `diag(J,J)` form a uniform isometric embedding of an N-dimensional nondegenerate source. There are `S_(2m)/S_m` such frames. This follows from transitivity on nondegenerate embeddings and the pointwise stabilizer `Sp_N` on the orthogonal complement. For fixed upper block M, the lower block B satisfies exactly

`B^T J B = D(M) = J-M^T J M`.

If `D(M)` has radical dimension `2k`, its nondegenerate quotient has dimension `N-2k`. A fixed splitting into a nondegenerate part and the radical gives `S_m/S_k` choices for the first part of B. The radical maps into the remaining `2k`-dimensional symplectic complement, with totally isotropic image. For image dimension d, the count is

`[2k choose d]_q prod_(i=0)^(d-1)(q^(2k-i)-q^i)`.

Choosing a kernel followed by an injective isotropic quotient frame gives that count; it is equally obtained by choosing the isotropic image and then a surjection onto it. Therefore the stated `F_k` and likelihood follow without needing any generic-position assumption or dividing by a vanishing form determinant.

The normalization can be checked by dimensions:

`q^(N^2) S_m^2/S_(2m) = b_m^2/b_(2m)`.

## The sign argument and exact optimality

The d=k summand alone gives

`F_k >= q^(-k(k+1)/2) [2k choose k]_q >= q^(k(k-1)/2)`.

For k=1 direct arithmetic gives `F_1=1+q/(q^2-1)`. The elementary infinite-product estimate gives

`b_infty >= (q^2-2)/(q^2-1)`.

Thus `b_infty F_1>1`, because the numerator of the difference is

`q^3-q^2-2q+1 = q(q-2)(q+1)+1 > 0`.

For k>=2, `b_infty F_k >= q b_infty>1`. Also `b_infty<alpha_m<1` for m>=1. Consequently **every** singular-defect matrix has likelihood strictly greater than one, and every nonsingular-defect matrix has likelihood `alpha_m<1`. The entire negative discrepancy is one explicitly computable event, which proves optimality rather than merely furnishing a lower bound.

The supplementary exact identity

`TV(A,U)=(alpha_m^(-1)-1) P_A(A invertible)`

is valid. Under the actual frame law, `D(A)=B^TJB`, which is invertible exactly when B is invertible. The matrix exchanging the two ambient nondegenerate halves preserves `diag(J,J)`, including in characteristic two. Hence A and B have the same law. This identity is especially useful because the main limiting separation follows from rank universality alone.

## Embedding count and uniform estimates

For a fixed alternating form on a j-dimensional space of rank `2s`, let `t=j-2s`. The injective realization count in a nondegenerate D-dimensional space is

`E(D,j,s)=q^(Dj-j(j-1)/2) Phi(D,j,s)`,

where

`Phi(D,j,s)=prod_(i=D/2-j+s+1)^(D/2)(1-q^(-2i))`

when `j-s<=D/2`, and zero otherwise. The product simplifies exactly: the factors from the nondegenerate embedding and the subsequent isotropic t-frame are adjacent segments of the same symplectic product. This confirms the exponent and all endpoints.

The bounds

`1-Phi(N,j,s)<=q^(-N+2j)/(q^2-1)`

and

`1-Phi(2N,j,s)<=q^(-2N+2j)/(q^2-1)`

hold wherever used. Infeasible first embeddings are harmless: their upper bound is already larger than one. Types belonging to an actual source subspace are feasible in N, and all types of dimension at most N embed in the 2N-dimensional ambient space.

The denominator in the subspace count is also correct:

`|Isom(H)|=|Sp_(2s)| |GL_t| q^(2st)`.

An isometry preserves the radical and has block form `[[P,0],[R,T]]`; R is arbitrary.

## Rank-universality proof

For a fixed j-subspace K of type 2s, the exact probability of `K subset ker A` is `E(N,j,s)/E(2N,j,s)`. This follows from transitivity on embeddings of K and Witt extension; no independence between its columns is assumed.

The Gaussian-moment difference estimate (1), power-moment conversion (2), and Lagrange coefficient bound (3) in the draft are valid. In particular:

- The Gaussian coefficient bound `[N choose j]_q q^(-Nj)<=q^(-j^2)/a_infty` holds uniformly in j.
- The expansion of `q^(iz)` by the image dimension of a linear map `F_q^i -> F_q^z` has coefficient `prod_(h<j)(q^i-q^h)`, with no missing `|GL_j|` factor.
- The constant coefficient of the exact Lagrange indicator at node `q^r` is `(-1)^r q^(-r(r+1)/2)/(a_r a_(N-r))`.
- The elementary symmetric coefficients are bounded by `q^(-i(i-1)/2)/a_i`.
- The resulting exponent is `-i^2/4+3i/2+1`, so the coefficient/moment sum is summable uniformly in N and r.

Thus the proof does not rely on an unproved moment-determinacy claim. It obtains a uniform point-mass estimate and then sums it to get total variation.

If an explicit constant is desired, define

`Theta_q=sum_(z in Z)q^(-z^2/4)`,

`V_q=sum_(i>=0)q^(-i^2/4+3i/2+1)`,

`W_q=sum_(r>=0)q^(-r(r+1)/2)`.

Keeping the draft's factor 2 in its Gaussian-moment bound, one valid choice is

`C_rank(q)=Theta_q V_q W_q/[a_infty^4 b_infty (q^2-1)]`,

so that `TV(nullity A,nullity U)<=C_rank(q) q^(-N)`. This constant is conservative and need not be advertised as sharp.

The limit then follows from `P(U invertible)=a_N=a_infty+O_q(q^(-N))` and `alpha_m=b_infty+O_q(q^(-N))`. The claimed constant

`Delta_q=(a_infty/b_infty)(1-b_infty)`

is correct and positive.

## Supplementary defect-universality proof

The key inclusion count is valid but warrants the explanation present in the draft. If

`K subset ker(J-U^TJU)`,

then `U|K` is injective: `Uv=0` would force `J(v,w)=0` for every w, hence v=0. Its restricted Gram form must match the form on K. Once those j columns are fixed, every remaining column obeys j independent affine pairing conditions, giving exactly `q^((N-j)^2)` possibilities. Pairings between two complementary columns remain unrestricted.

This proves the exact inclusion probability and Gaussian moments. For the power-moment estimate the exponent at summation index j is

`f(j)=-j(j-1)/2+(i+2)j`.

It satisfies `f(j+1)-f(j)=i+2-j>=3` for j<i. Therefore the final-term bound with factor `(1-q^(-3))^(-1)` is valid. Even parity allows interpolation on `1,q^2,...,q^(2m)`. The surviving exponent is `-i^2/2+7i/2`, summable uniformly. The claimed full defect-nullity TV bound follows.

**A pitfall that the proof correctly avoids:** `U^TJU` itself is not asymptotically uniform over alternating matrices in full total variation; its likelihood relative to a uniform alternating form is `b_m F_k`, depending on corank 2k. The theorem concerns the rank of the shifted defect, not full matrix equidistribution of the Gram matrix.

## Primary-literature comparison

### Pott, Schmidt, and Zhou (2016)

Alexander Pott, Kai-Uwe Schmidt, and Yue Zhou, *Pairs of Quadratic Forms over Finite Fields*, Electronic Journal of Combinatorics 23(2), P2.8, DOI `10.37236/4072`.

- Publisher: https://www.combinatorics.org/ojs/index.php/eljc/article/view/v23i2p8
- Author-hosted full text: https://math.uni-paderborn.de/fileadmin-eim/mathematik/AG-Diskrete_Mathematik/Publications-schmidt/quad_pairs.pdf

Their Theorem 5 gives exact counts of alternating pairs with specified ranks of B, C, and B+C over every finite field. It uses eigenvalues and intersection numbers of the alternating-matrix association scheme; Theorem 1 specializes to all three forms nonsingular. Consequently, the defect distribution here can also be expressed by weighting known intersection counts with Gram-fibre counts. Exact alternating-pencil rank enumeration is therefore prior art. The passages checked do not state the present symplectic-block likelihood test or quantitative rank-blindness conclusion.

### De Boeck and Van de Voorde (2024)

Maarten De Boeck and Geertrui Van de Voorde, *Anzahl theorems for trivially intersecting subspaces generating a non-singular subspace I: symplectic and hermitian forms*, Linear Algebra and its Applications 699 (2024), 367–402, DOI `10.1016/j.laa.2024.07.004`.

- Full text: https://arxiv.org/html/2407.07486v3
- Institutional record: https://biblio.ugent.be/publication/01J52VTRF3S2T2P565VFDEF23F

They count nondegenerate subspaces disjoint from a fixed subspace of arbitrary type and generating a nondegenerate sum; Theorem 4.7 is the symplectic case. In the present model, `P_A(A invertible)` is the proportion of nondegenerate N-subspaces complementary to the fixed bottom N-space. That probability thus has a direct antecedent in exact subspace counting. Their work should be cited when discussing the invertibility component, not merely general background.

### Glasby, Niemeyer, and Praeger (2022)

S. P. Glasby, Alice C. Niemeyer, and Cheryl E. Praeger, *Random generation of direct sums of finite non-degenerate subspaces*, Linear Algebra and its Applications 649 (2022), 408–432, DOI `10.1016/j.laa.2022.05.016`.

- Primary full-paper landing page: https://arxiv.org/abs/2111.02198

This earlier work bounds proportions of disjoint nondegenerate subspaces with nondegenerate sum and explains applications to recognizing finite classical groups. It supplies context for the exact-count work above.

### Fulman and Goldstein (2015)

Jason Fulman and Larry Goldstein, *Stein's method and the rank distribution of random matrices over finite fields*, Annals of Probability 43 (2015), 1274–1314, DOI `10.1214/13-AOP889`.

- Author-hosted paper: https://dornsife.usc.edu/jason-fulman/wp-content/uploads/sites/224/2023/06/AOP889.pdf

This treats standard iid and alternating rank laws and quantitative approximation. Those limiting laws are classical, rather than a new component of the present theorem.

## Recommended novelty language

The literature search establishes close antecedents and does not establish worldwide priority. A defensible formulation is:

> We prove a quantitative separation for growing nondegenerate half-blocks of finite symplectic matrices: the complete rank distribution approaches the iid rank distribution exponentially, whereas an explicit determinant test achieves a positive limiting full-matrix total-variation distance. We derive a complete likelihood formula and prove that this test is exactly optimal. The elementary counting inputs and nearby exact finite-geometry enumerations are credited; publication priority for this combined statement remains provisional.

This also preserves the distinction from the previous ProveIt Lagrangian-output result. The likelihood formula can be viewed as a specialization of a general finite symplectic-compression count; the new work lies in the critical-dimensional estimates, the likelihood sign theorem, and the resulting optimal-test/rank-universality separation.

## Additional review: sharp first-order expansions

The sharp first-order additions and Sections 5--6 of the final assembled `paper.tex` received a separate review. The current assembled text was checked again after correction of its outside-grid exponents and insertion of the corollary "First correction to the full-matrix distance." The paper now uses `c_j` for the product over all exponents, `e_j` for the even product, and `o_j` for the odd product. With this notation, both signed expansions and their `O_q(q^(-2n))` remainders are valid. This review covers mathematical content; PDF compilation and visual inspection are separate checks.

### Uniform moment identities and Taylor bounds

For `tau=q^(-n)` and a uniform alternating j-dimensional form H of rank 2s, the identities

`mu_block(j)=u_j E[Phi_n^2/Phi_(2n)]`,

`mu_iid(j)=u_j E[Phi_n]`,

`nu_defect(j)=v_j E[Phi_n^2]`,

`nu_alt(j)=v_j E[Phi_n]`

are exact, where `u_j=q^(-j^2)/c_j` and `v_j=q^(-j(j-1)/2)/c_j`. The uniform-H type weight is `|GL_j|/(q^(j(j-1)/2) |Isom(H)|)`; substitution reproduces the earlier subspace counts with all powers of q correct.

Write `W=(q^(2(j-s))-1)/(q^2-1)`, `P=Phi_n`, and `Q=Phi_(2n)`. For all types, including infeasible first embeddings,

`0<=1-P<=tau W`,

`0<=P-1+tau W<=tau^2 W^2`,

`0<=1-Q<=tau^2 W`, and `Q>=e_infty`.

For infeasible first embeddings P=0 and tau W>=1, so these inequalities still hold. If `d=1-P` and `r=tau W-d`, then

`P^2/Q-P+tau W=P^2(1-Q)/Q+r+d^2`.

This remainder is nonnegative and at most `(2+e_infty^(-1))tau^2 W^2` for j>0, with the j=0 case identically zero. The defect version omits the first term. Thus the second-order Gaussian-moment bounds are genuinely uniform over all j<=n, rather than fixed-j asymptotic statements.

The elementary calculation `E q^(nullity H)=q+1-q^(1-j)` gives `E W=(q^j-1)/(q-1)`, including j=0 by direct inspection.

### The signed corrections

Let

`pi(a)=c_infty q^(-a^2)/c_a^2`,

`eta(2a)=o_infty q^(-a(2a-1))/c_(2a)`, with eta zero on odd integers.

The corrections

`delta(a)=(2-q^a)pi(a)/(q-1)`

and

`epsilon(a)=(q+1-q^a)eta(a)/(q^2-1)`

have exactly the required Gaussian moments. This follows from

`(q^a-q^j)[a choose j]_q=q^j(q^(j+1)-1)[a choose j+1]_q`,

and the ratios `(q^(j+1)-1)u_(j+1)=q^(-j)u_j` and `(q^(j+1)-1)v_(j+1)=q v_j`. In particular their total masses are zero. Only the zero-nullity coordinate has positive mass; delta(1)=0 when q=2.

### Inversion and the infinite signed tails

The rank remainder's power moment is bounded by `C_q tau^2 q^((i+4)^2/4)`. Interpolation coefficients leave the summable exponent `-i^2/4+5i/2+4`. The defect counterpart is `C_q tau^2 q^(i(i+9)/2)`, and even-grid coefficients leave `-i^2/2+11i/2`. These are correct.

The signed target measures have infinite support. Their contributions outside the interpolation grid have been included correctly after the following exponent correction, now applied in the assembled paper:

`|L_(a,n)(q^b)|<=c_infty^(-2) q^(nb-n(n+1)/2-a(a-1)/2)` for b>n,

and

`|L^even_(a,m)(q^(2k))|<=e_infty^(-2) q^(2mk-m(m+1)-a(a-1))` for k>m.

The exponent uses `a(a-1)`, not `a(a+1)`, in these outside-grid bounds. Summing the rank tail, then multiplying by tau, gives `O_q(q^(-n(n+3)/2))`, which is `O_q(q^(-2n))`. The defect tail gives `O_q(q^(-n-n^2/4+1))`; it is `O_q(q^(-2n))` for sufficiently large even n, and n=2,4 are absorbed by enlarging the q-dependent constant. The un-interpolated omitted masses are smaller. No missing tail term remains.

Consequently the claimed sharp total-variation formulas are justified:

`TV(rank(A),rank(U))=c_infty/(q-1) q^(-n)+O_q(q^(-2n))`,

`TV(nullity D(U),nullity T)=q o_infty/(q^2-1) q^(-n)+O_q(q^(-2n))`.

### Optional full-matrix correction

The optional expansion also checks independently. The elementary product tails give

`alpha_n=e_infty(1+2tau/(q^2-1)+O_q(tau^2))`,

`P(A invertible)=c_infty(1+2tau/(q-1)+O_q(tau^2))`.

Substitution into the exact TV identity yields

`TV(P_n,Q_n)=Delta_q + [2o_infty/(q^2-1)] [q-(q+1)e_infty] q^(-n) + O_q(q^(-2n))`.

The correction coefficient is strictly negative: `e_infty>q/(q+1)`, using the elementary product bound, with strictness in the binary case supplied by at least two positive product factors. This establishes eventual approach from below; it is not a proof of monotonicity in n.

The independent joint-law calculation in the computation section also checks: after fixing an isometric injection on a kernel subspace K and applying Witt extension, the residual constrained matrix is triangular with two identity blocks and an independent uniform square middle block of dimension `n-2j+2s`.
