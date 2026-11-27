# Exact laws and a dimension threshold for several symplectic frames

Independent derivation and proof audit, 27 November 2026.

## Setting

Let V be a symplectic space of dimension 2n over F_q, in every characteristic. Let k >= 2 and E = direct sum E_i, dim E_i = d_i. Fix alternating forms H_i of rank 2s_i on E_i, satisfying d_i-s_i <= n. Independently sample isometric injections X_i:E_i -> V uniformly. Equivalently take independent uniform symplectic translates of prescribed frames. One frame may be held fixed, by simultaneous symplectic invariance. Observe every cross pairing M_ij=X_i^T J X_j (i<j).

Write D=sum d_i. Their full Gram matrix Gamma has diagonal blocks H_i and cross blocks M_ij, -M_ij^T. Put rank Gamma=2s, R=rad Gamma, r=dim R=D-2s, R_i=R intersect E_i, t_i=dim R_i. Because the E_i are direct summands, the R_i also have a direct sum.

Define the isometric injection count

    Emb_n(d,s) = q^(2nd-binomial(d,2)) product_{j=n-d+s+1}^n (1-q^(-2j))

when 0<=2s<=d and d-s<=n, and zero otherwise. Empty products are one.

## The exact law

For 0<=ell<=r let T_ell be the number of ell-dimensional subspaces L of R meeting every R_i trivially. Its explicit formula is

    T_ell = sum_{0<=j_i<=t_i} (-1)^J q^(sum_i binomial(j_i,2))
            product_i [t_i choose j_i]_q [r-J choose ell-J]_q,
    J = sum_i j_i.

Gaussian coefficients outside their permitted range are zero. Then

    P(Gamma) = sum_{ell=0}^r T_ell Emb_n(D-ell,s)
               / product_i Emb_n(d_i,s_i).

The ell summand is also the joint probability of this Gamma and dim ker(X_1,...,X_k)=ell.

### Proof of T_ell

For a subspace U of dimension j, the subspace-lattice Mobius value is (-1)^j q^(j(j-1)/2). Thus the indicator of L intersect R_i =0 is the sum of these Mobius values over U_i<=L intersect R_i. Multiply over i and sum over L. Choose U_i independently in R_i. Their sum is direct and has dimension J, so the number of ell-subspaces L containing that sum is [r-J choose ell-J]_q. This proves the formula.

### Proof of the law

Each tuple of frames corresponds to a linear map F:E->V, whose restriction to each E_i is injective and whose pulled-back form is Gamma. Its kernel L is contained in R, and injectivity is equivalent to L intersect R_i=0 for all i. Conversely such an L and any isometric injection E/L -> V give exactly one tuple. The induced quotient form has dimension D-ell and rank 2s, so the displayed numerator counts tuples. The denominator counts all independent tuples.

The count Emb follows by writing a formed space as a nondegenerate 2s-space plus a radical of dimension h=d-2s. Embed the former in |Sp(2n,q)|/|Sp(2(n-s),q)| ways and then choose an independent isotropic h-frame in its orthogonal complement, in product_{j=0}^{h-1}(q^(2(n-s)-j)-q^j) ways. Witt extension shows that uniform symplectic translates give uniform injections.

## Sharp support and minimum ambient dimension

The observation Gamma is realizable if and only if

    s + max_i t_i <= n.

In particular its minimum symplectic ambient dimension is 2(s+max_i t_i), with no assumption that the individual forms were already realized.

### Proof

If ell=dim L, avoiding R_i implies ell<=r-t_i for each i, so ell<=r-max t_i. The quotient embeds precisely when D-ell-s<=n. These inequalities are compatible exactly when s+max t_i<=n.

For constructive sufficiency let t=max t_i, choose injections f_i:R_i->F_q^t and extend their direct sum to a linear map f:R->F_q^t by setting it to zero on a complement of direct sum R_i. At least one f_i is onto, so f is onto. Its kernel L has dimension r-t and avoids all R_i. The quotient E/L has radical dimension t and nondegenerate rank 2s, hence embeds in dimension 2(s+t) by adding t hyperbolic partners to its radical.

## Specialize to isotropic frames

Take H_i=0 and d_i<=n. Let mu be the joint cross-block law and U the law in which every entry of every M_ij (i<j) is independent and uniform. There are q^B such observations, where B=sum_{i<j}d_i d_j=binomial(D,2)-sum_i binomial(d_i,2).

Set eta_j=product_{a=1}^j(1-q^(-2a)), eta_0=1, and eta_infinity=product_{a>=1}(1-q^(-2a))>0. Define

    A(q;d_1,...,d_k)
      = E_U q^(dim ker Gamma)
      = q+1-q^(1-D)
        + q^(-D) sum_i (q^(d_i)-1)(q^(d_i)-q).

The exact expectation is valid when all d_i>=1. Zero-dimensional blocks may simply be removed. In particular

    A <= q+1+sum_i q^(2d_i-D),

and if max d_i <= D/2, then A <= q+1+k.

### Proof of the expectation

Sum P_U(Gamma v=0) over vectors v in E. The zero vector contributes one. If v is supported in the single block E_i, the linear map from the independent cross entries to Gamma v has rank D-d_i: the i output block is identically zero and every other output block is an independent unrestricted vector. Hence its zero probability is q^(-(D-d_i)).

If v has at least two nonzero blocks, this map has rank D-1. To check this exactly, use the standard nondegenerate coordinate pairing. Its cokernel consists of w with

    w_i v_j^T - v_i w_j^T = 0 for every i<j.

Choose two nonzero v blocks. Equality of nonzero rank-one outer products forces w_i=lambda v_i, w_j=lambda v_j with the same scalar; this assertion also includes either w block being zero, which forces both zero. Pairing either chosen block with every other block then forces w=lambda v globally. Thus the cokernel is precisely the line spanned by v, in characteristic two as well. The zero probability is q^(-(D-1)). There are q^(d_i)-1 single-block nonzero vectors of type i and q^D-1-sum_i(q^(d_i)-1) other nonzero vectors. Summing and simplifying gives A.

## Quantitative subcritical bound

If c=2n-D>=0, then

    TV(mu,U) <= min(1, A q^(-c)/(q^2-1)).

### Proof

Keep only tuples for which F=(X_1,...,X_k) is injective. This is a subprobability mu_inj<=mu, with density relative to U, at a Gamma of radical dimension r,

    f_inj(Gamma) = 1_{r<=c}
        (product_i eta_(n-d_i)) / (eta_n^(k-1) eta_((c-r)/2)).

Here r and c have the same parity. The formula follows directly from the ell=0 term of the exact law after cancelling q powers. Let Ctilde=(product_i eta_(n-d_i))/eta_n^(k-1). Because eta_j decreases in j and n-d_i<=n, Ctilde>=eta_n>=eta_infinity.

When r<=c, put m=(c-r)/2. Then

    f_inj >= eta_infinity/eta_m
           = product_{a=m+1}^infinity (1-q^(-2a))
           >= 1-q^(-2m)/(q^2-1)
           = 1-q^(r-c)/(q^2-1).

When r>c, parity gives r-c>=2, and q^(r-c)/(q^2-1)>=1. Thus in every case (1-f_inj)_+<=q^(r-c)/(q^2-1). If f is the actual density of mu, f>=f_inj, so

    TV(mu,U)=E_U(1-f)_+ <= E_U(1-f_inj)_+
            <= q^(-c) E_U q^r/(q^2-1).

This proof uses no approximation, no bound on the probability of dependent combined frames, and no extra separation between any d_i and n.

## Quantitative supercritical bound

If w=D-2n>0, then

    TV(mu,U) >= max(0, 1-(A-1)/(q^w-1)).

### Proof

Under the actual law, rank Gamma<=2n, hence nullity r>=w. Under U, Markov's inequality applied to q^r-1 gives

    P_U(r>=w) <= (A-1)/(q^w-1).

The test rank Gamma<=2n accepts the actual law with probability one. Its difference in acceptance probabilities proves the lower bound.

## Consequences: a threshold and hidden high-order dependence

Fix q and k, with max d_i<=D/2. For all legal isotropic frame dimensions, the preceding bounds give a transition on the scale D=2n+O(1): if 2n-D tends to infinity, TV tends to zero; if D-2n tends to infinity, TV tends to one. More quantitatively the two tails are O_{q,k}(q^(-|D-2n|)). This describes a bounded-width transition, but does not claim an exact critical-window limit.

For every fixed k>=3 choose alpha with 2/k<alpha<2/(k-1) and put d_i=floor(alpha n). All these dimensions are legal for large n. Every proper subset of j>=2 frames has jd_i<= (k-1)d_i<2n by a linear margin and is balanced, so its complete joint cross-block observation has distance O_{q,k,alpha}(q^(-epsilon n)) from independent uniform entries. A one-frame observation is empty and exactly uniform. Yet all k frames together have total dimension kd_i>2n by a linear margin and their joint cross-block law has distance 1-O_{q,k,alpha}(q^(-epsilon n)) from independent uniform entries.

Therefore this constructs, for arbitrarily large k, joint observations whose every proper frame marginal is exponentially close to independence, while the full observation is exponentially close to perfectly distinguishable from independence. It is an information-theoretic statement; the full-law test is efficient Gaussian elimination on Gamma.

For the particularly simple three-frame example, take n=5m and d_1=d_2=d_3=4m. The ambient dimension is 10m. Each pair uses 8m dimensions and has TV at most (q+3)/(q^2-1) q^(-2m). The triple uses 12m dimensions; its TV is at least 1-(q+3)/(q^(2m)-1). The pair bound uses k=2 and the triple bound uses A-1<=q+3.

## Comparison with inspected source

## Further strengthening: forest edges are exactly independent

For any forest F on the frame index set, the matrix-valued edge observations M_ij on its edges are mutually independent, each having its ordinary two-frame marginal law. This holds for arbitrary fixed individual Gram forms H_i and at every finite dimension.

Proof: remove an isolated vertex or choose a leaf i adjacent to j. Conditional on every frame except X_i, the law of M_ij depends only on the prescribed Gram matrix of the fixed neighbor X_j: any two neighbor frames are related by a symplectic transformation, and applying its inverse to the uniform leaf frame does not change its law. Therefore the conditional law of M_ij is constant, so M_ij is independent of all other frames and in particular every other edge observation. Induct on the number of edges.

In the explicit three-frame example, any pair of the three observed matrices is therefore exactly independent. Nevertheless their three-way joint distribution has distance tending exponentially to one from the product of their own marginals: use the product-TV inequality and the bounds against independent uniform matrices to subtract at most three pair marginal errors. Precisely, for n=5m and d_i=4m,

    TV(Law(M12,M13,M23), Law(M12) tensor Law(M13) tensor Law(M23))
      >= 1 - (q+3)/(q^(2m)-1)
           - 3(q+3)/(q^2-1) q^(-2m).

All three marginal laws are the same after compatible orientation conventions, but equality of their distributions is not needed for this inequality.

## Further strengthening: threshold bounds for arbitrary individual forms

The exact-law and support theorem already allow arbitrary prescribed forms H_i, of rank 2s_i. The threshold estimates also hold without isotropy after replacing A by

    A = 1 + (q^D-1-sum_i(q^(d_i)-1)) q^(1-D)
          + sum_i (q^(d_i-2s_i)-1) q^(d_i-D).

For a nonzero vector supported in a single block i, Gamma v=0 requires H_i v_i=0, so only q^(d_i-2s_i)-1 of those vectors contribute, with probability q^(-(D-d_i)). For a vector with at least two nonzero blocks, the random off-block linear map still has image v-perp, and the fixed diagonal-block contribution lies in v-perp because every H_i is alternating. Thus its zero probability remains q^(-(D-1)). This proves the displayed expectation.

The injection density is now

    1_{r<=c} product_i eta_(n-d_i+s_i)
                 / (eta_n^(k-1) eta_((c-r)/2)),

whose numerator ratio is again at least eta_infinity. Thus the same TV upper and lower bounds follow. One has

    A <= q+1+sum_i q^(2(d_i-s_i)-D).

In particular the bounded-width threshold holds whenever d_i-s_i<=D/2 for every i. This condition is automatic if all H_i are nondegenerate. It also holds for every equal-size isotropic collection with at least two blocks.

## Source comparison (continued)

The pinned article contains the exact two-frame law in spn:thm:complete-law, random alternating Gram Fourier law in spn:lem:alt-gram, and exact finite complement discrepancy in spn:eq:complement-discrepancy. The incoming uniform_symplectic_blocks, rectangular_symplectic_blocks, and grh-two-open-questions/symplectic reports concern two nondegenerate frames and sharper two-frame profiles. None of the inspected theorem statements gives the joint law for an arbitrary number of frames or the all-proper-marginals-versus-full-law separation above. Worldwide priority is not established by this inspection.

The upstream theorem premise has current primary support: https://math.mit.edu/~drew/shortgrh/, updated 2026-11-27 17:27 UTC, reports successful checks of the pinned lsernau/grh-lean revision 72fead102f663d5c7a407964a13dc0cf9d977207. We did not rerun the upstream kernel checks. The result in this note is unconditional and uses only finite linear algebra.
