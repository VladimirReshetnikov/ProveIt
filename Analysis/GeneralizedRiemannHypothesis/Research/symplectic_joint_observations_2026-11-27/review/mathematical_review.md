# Independent mathematical review: multi-frame symplectic Gram law

Reviewer: analytic-extension agent. Date: 2026-11-27.
Repository baseline: VladimirReshetnikov/ProveIt at
`6d284fcf75bc3a91bb2e79ba7636f94724bff62c`.

## Scope and conclusion

I independently checked the exact kernel first moment, the injection-density
formula, both total-variation inequalities, their prescribed-Gram extension,
the support criterion, and the forest independence argument. No mathematical
error was found. The proofs work over every finite field, including
characteristic two. The asymptotic result locates a dimension threshold with
exponentially small errors on either side; it does not determine the limiting
distribution in the bounded critical window.

## General setup

Let V be symplectic of dimension 2n over F_q. For i=1,...,k, let H_i be an
alternating d_i by d_i matrix of rank 2s_i, with d_i-s_i <= n. Choose
independently and uniformly injective maps X_i with X_i^t J X_i=H_i.
Put D=sum d_i. The observed alternating Gram matrix G has diagonal blocks
H_i and off-diagonal blocks X_i^t J X_j. U denotes independent uniform
off-diagonal blocks with those same fixed diagonals. Let r=nullity(G).

## Exact first moment under U

For each nonzero v, consider the linear map from the free cross-block
coordinates to the off-diagonal part of Gv. Its annihilator comprises w with

    w_i v_j^t - v_i w_j^t = 0  for all i<j.

If v is supported on exactly one block i, the annihilator has dimension d_i
and the image consists of vectors whose i-th block is zero. Consequently
Gv=0 is possible precisely when H_i v_i=0 and then has probability
q^{-(D-d_i)}.

If v has at least two nonzero blocks, the displayed equations force
w=lambda v: an edge between two active blocks forces the same proportionality
constant, and all other blocks are then forced. The image is therefore the
hyperplane v-perpendicular for the coordinate dot product. The fixed shift
(H_i v_i)_i lies in this hyperplane because v^t diag(H_i)v=0. Hence Gv=0
has probability q^{-(D-1)}. These arguments use alternating forms and remain
valid in characteristic two.

It follows exactly that

    M := E_U q^r
       = 1 + [q^D - 1 - sum_i(q^{d_i}-1)] q^{1-D}
           + sum_i(q^{d_i-2s_i}-1) q^{d_i-D}.

In particular,

    M <= 1+q+sum_i q^{2(d_i-s_i)-D}.

For isotropic blocks, the equivalent formula is

    E_U(q^r-1)
       = q-q^{1-D} + q^{-D} sum_i(q^{d_i}-1)(q^{d_i}-q).

## Exact injection density and upper bound

Write eta_m=product_{j=1}^m(1-q^{-2j}), and c=2n-D. Let f_0 be the U-density
of the subprobability consisting of frame tuples whose concatenated map is
injective. For c>=0,

    f_0(G)=1_{r<=c}
      [product_i eta_{n-d_i+s_i} / eta_n^{k-1}]
      /eta_{(c-r)/2}.

The parity r=c mod 2 follows from even rank of an alternating matrix. Each
eta_{n-d_i+s_i} >= eta_n, so the numerator is at least eta_n >= eta_infinity.
For r<=c the product-tail inequality gives

    (1-f_0)_+ <= q^{r-c}/(q^2-1).

For r>c the same inequality holds because parity gives r>=c+2, making its
right side larger than one. Since the full density f is at least f_0,

    TV(P,U)=E_U(1-f)_+ <= M q^{D-2n}/(q^2-1).

A convenient version without a balance assumption is

    TV(P,U) <= [(q+1)q^{D-2n}
                 +sum_i q^{-2(n-d_i+s_i)}]/(q^2-1).

Under max_i(d_i-s_i)<=D/2 this becomes

    TV(P,U) <= (q+1+k)q^{D-2n}/(q^2-1).

## Lower bound and automatic balance above threshold

Actual Gram matrices have rank at most 2n. If D>2n, Markov applied to q^r
gives TV(P,U)>=1-M q^{2n-D}. One can instead use q^r-1 to obtain the sharper
bound 1-(M-1)/(q^{D-2n}-1).

Above the threshold, feasibility d_i-s_i<=n already implies
max_i(d_i-s_i)<D/2. Thus

    TV(P,U) >= 1-(q+1+k)q^{2n-D}

needs no additional balance assumption when D>2n.

## Exact law and support

For a prescribed G, put R=rad(G), rank(G)=2s and t_i=dim(R intersect E_i),
where E is the direct sum of the coordinate blocks E_i. A linear realization
with individual block maps injective has kernel L<=R satisfying
L intersect E_i=0 for every i. Quotienting by L then gives an isometric
injection E/L -> V. This proves the kernel-sum law using the repository's
single-form embedding count.

The maximum possible dimension of an allowed L is dim(R)-max_i t_i.
For sufficiency choose a surjection R -> F_q^{max_i t_i} whose restriction
to each R intersect E_i is injective: these subspaces form a direct sum, so
their maps can be chosen independently. The kernel has the required
dimension. Necessity follows by dimensions against any individual subspace.
Consequently the exact support criterion is

    s + max_i t_i <= n.

The number of l-dimensional allowed kernels is

    sum_{j_1,...,j_k} (-1)^{sum j_i} q^{sum binom(j_i,2)}
       product_i [t_i choose j_i]_q
       [dim(R)-sum j_i choose l-sum j_i]_q,

with out-of-range Gaussian binomials zero. This follows by the ordinary
subspace-lattice Mobius inversion on each of the independent coordinate
radicals; no additional relative-position invariant is needed.

## Exact forest independence and high-order dependence

The symplectic group acts transitively on embeddings of each fixed H_i.
For any parent frame, the distribution of its cross Gram block with an
independent leaf frame is therefore the same. Removing leaves proves that
the Gram blocks indexed by any forest are exactly independent, with their
individual two-frame marginal laws. In particular all three blocks from
three independent frames are pairwise independent.

For k>=3 equal isotropic frame dimensions d=floor(alpha n), with
2/k<alpha<2/(k-1), all proper vertex-induced collections approach independent
uniform blocks, while the full collection has TV distance tending to one.
For k=3 and d=floor(4n/5), every pair of blocks is exactly independent and
each marginal approaches uniform exponentially, while the triple is
asymptotically singular against the product uniform model.

## Primary literature and limits on novelty claims

The following are adjacent primary sources located in targeted searches.
None of the inspected statements was the exact multi-frame prescribed-Gram
law plus the stated total-dimension TV bounds and forest/high-order
dependence corollary. This is not an exhaustive priority determination.

1. Tiange Li, Yinan Li, Youming Qiao, Dacheng Tao, Yingjie Wang,
   *On the average-case complexity landscape for Tensor-Isomorphism-complete
   problems over finite fields*, arXiv:2604.00591v2 (2026), Proposition 5.2.
   https://arxiv.org/abs/2604.00591v2
   https://arxiv.org/pdf/2604.00591v2
   This gives a rank-enumerator/chi-square expansion and uniformity estimate
   for symmetric random Gram matrices MM^t over odd finite fields. It is a
   substantial precedent for random-Gram-to-uniform dimension comparisons.
   The new application uses alternating forms, arbitrary fixed diagonal
   Gram blocks, and individually injective frames.

2. Tom Farshi, Daniele Toniolo, Carlos E. Gonzalez-Guillen, Alvaro M.
   Alhambra, Lluis Masanes, *Mixing and localization in random time-periodic
   quantum circuits of Clifford unitaries*, J. Math. Phys. 63, 032201 (2022),
   DOI 10.1063/5.0054863.
   https://discovery.ucl.ac.uk/id/eprint/10146567/1/5.0054863.pdf
   Institutional metadata: https://discovery.ucl.ac.uk/id/eprint/10146567/
   Author manuscript: https://arxiv.org/abs/2007.03339
   Studies uniform outputs and submatrix/product rank bounds for finite
   binary symplectic matrices. This supplies finite-symplectic probabilistic
   context, not the simultaneous cross-Gram model addressed here.

3. Jimmy He, *Random walk on the symplectic forms over a finite field*,
   arXiv:1910.10823v2 (2020), Algebraic Combinatorics,
   DOI 10.5802/alco.131.
   https://arxiv.org/abs/1910.10823v2
   https://arxiv.org/pdf/1910.10823v2
   Establishes cutoff for a transvection walk on GL_{2n}/Sp_{2n}, the space
   of nondegenerate symplectic forms. The state space and mechanism differ
   from independent frames and their full cross-pairing matrix. Do not claim
   the general occurrence of a finite-symplectic threshold is new.

4. OpenAI, *A counterexample to Sidorenko's conjecture*, September 23, 2026,
   Section 5, Proposition 5.3.
   https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/A-counterexample-to-Sidorenkos-conjecture-September-23-2026/paper.pdf
   Studies ordered triples of independent Lagrangian subspaces, intersection
   profiles and orbit/completion probabilities as the field size grows.
   It is relevant prior art on multi-Lagrangian statistics, though its
   observable and asymptotic regime differ from the full framed Gram law.

5. Jason Fulman and Larry Goldstein, *Stein's method and the rank distribution
   of random matrices over finite fields*, Ann. Probab. (2015),
   DOI 10.1214/13-AOP889.
   https://doi.org/10.1214/13-AOP889
   Relevant background for ranks of uniform alternating matrices. The
   present first moment also handles fixed diagonal blocks and needs no
   existing full rank-distribution formula.

Recommended wording: 'The theorem is a new extension of the pinned
repository's two-frame results. A targeted literature comparison located
related finite-field Gram and symplectic results, but not this precise
combination of statements; worldwide priority is not asserted.'

### Source-coverage limitation

The pinned incoming archive
`Analysis/GeneralizedRiemannHypothesis/docs/incoming/grh_uniform_extensions_2026-11-27.zip`
was identified with Git blob SHA `fcddc0beadb909de6850ca2ba3bab403095f7239`
but was not inspected. The GitHub contents tool returned an empty base64
payload for this archive (larger than one MiB); the blob tool attempted UTF-8
decoding and failed, and generic fetch rejected non-UTF-8 content. Any
novelty comparison must disclose that this incoming packet is outside the
reviewed source coverage. This does not affect the independent proofs.
