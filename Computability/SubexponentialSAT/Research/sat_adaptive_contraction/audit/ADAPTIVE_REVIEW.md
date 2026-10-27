# Independent review of the adaptive three-block argument

Reviewed `theory_work/adaptive_proof.md`, `adaptive_blocks.py`, and the
corresponding exact-weight/cache arguments of the earlier joint-Cauchy
packet, together with the asymmetric packing theorem and schedule.
No substantive gap was found in the new composition, subject to the stated
imported contraction, packing, and integral-mode lemmas. This is a
mathematical review, not a proof-assistant certificate.

## Local counting and adaptive choice

For nine groups there are 72 directed pair indices. A group is incident
with 16; a triple is incident with 42 and has 36 boundary indices. These
counts give, from the uniform subset-entropy bound, coefficients 4/9,
sqrt(42)/9, and 2/3. A uniformly selected partition into three triples
separates each fixed ordered pair with probability 6/8=3/4. Therefore
minimizing the exact crossing-domain product gives crossing entropy at most
(3/4) times total entropy, bounded by K/sqrt(2). Since
1/sqrt(2)<sqrt(42)/9, block construction dominates the final crossing sum.

All 280 products involve a fixed number of polynomial-bit integers. The
selection is polynomial time and needs no approximate logarithms. Zero
exact-weight list sizes must be skipped before selection, as the supplied
algorithm does. The uniform entropy error covers adaptive subset choice:
there are only finitely many pair subsets at fixed r=9.

## Cache order and bit access

Choose the partition before constructing group caches. For each selected
block, order its boundary axes according to one global crossing-axis
order, followed by its internal axes. Order each of its group caches by
the restriction of that axis order. Cache entries are values of the same
group functions regardless of the chosen order or outer partition.

Here is a direct amortization of sequential cache access. A lexicographic
scan of A assignments to k axes projects onto any fixed subset of axes.
When a counter at position j advances, its suffix resets. The projected
cache head travels at most a constant multiple of the product of the
selected suffix dimensions. The number of such counter advances is at
most A divided by the product of all suffix dimensions. Thus the head
movement charged to one counter is O(A), and all counters cost O(kA).
Repeated projected records require no movement. Here k<=72, and record
lengths are polynomial. This pays for the group-cache accesses during
block construction and for the boundary-table accesses in the final
crossing scan without assuming constant-cost random access to exponential
tables. Each block's internal sum can be accumulated and its resulting
boundary entry written sequentially.

## Recursive costs and space

The partition affects the order of finite summation only. It does not
alter the group factors, their incident mode indices, their child-network
topology, immutable creation precision, or the side-degree invariant.
Different exact-weight arrays, and different recursive calls, can therefore
choose different partitions. Reusing caches across those choices is not
needed; the polynomial number of arrays is already charged.

With a=4/9, beta=sqrt(42)/9, and gamma=2sqrt(2)/9, recurrence expansion
produces a coefficient

    a(1-gamma^d)/(1-gamma) + beta gamma^d.

It never exceeds beta because a/(1-gamma)=4/(9-2sqrt(2))<2/3<beta.
Depth-first child evaluation stores only ancestor partial caches plus the
current child's data; their sizes add, rather than multiply. Boundary
tables are built after that call's group-cache evaluations are complete.
The largest space coefficient is therefore 2/3. Exact-weight arrays are
processed one at a time.

## Schedule and presentation details

The integer schedule with

    B_lambda=max{b : 9^(20b)<=2^lambda},
    U=B_lambda-ceil(sqrt(lambda)),
    u_d=floor(U/2^d)

has the required slack. Using the boundary expression without the
subtracted sqrt(lambda) would fail the root and retained-row packing
conditions after adding buffers. In the supplied schedule the
Theta(sqrt(lambda)) gap dominates the O((log lambda)^2) cumulative
buffers, while preserving the limiting leading coefficient.

Two useful clarifications for the final proof are:

1. The packing error is O(1/lambda) plus terms exponentially small in
   sqrt(lambda), using h=ceil(log2 s). Its product over O(log lambda)
   levels is 1+o(1), justifying the uniform geometric bound on K_d.
   Alternatively retain gamma_s=gamma+o(1) throughout the recurrence and
   take the limit in its convergent geometric series.
2. The number of recursive children and exact-weight arrays is bounded
   by poly(s), independent of the original description length. Local
   entry-reading and arithmetic overhead can carry a common fixed
   poly(s+description_length) factor. State the recurrence this way to
   avoid accidentally suggesting that a description-length polynomial
   is multiplied afresh at every depth.

The resulting constants 36.7503125238... for time and 34.0241780075...
for space follow from kappa=pi*sqrt(40log2(9))/ln(2). They describe a
normalized contraction certificate with subexponential space. They are
not universal coefficients on the original SAT variable count, and the
argument does not improve the logarithmic order of the inherited SAT bound.
