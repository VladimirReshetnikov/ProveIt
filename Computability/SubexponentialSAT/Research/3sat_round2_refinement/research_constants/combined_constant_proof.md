# A combined explicit contraction certificate below 85

## Scope and headline

Relative to the unchanged deformation, integrality, recovery, and recursive factorization identities in OpenAI's pinned quantitative contraction appendix, the supplied improvements can be combined with two further packing/precision refinements and a two-stage grouping schedule to prove

\[
T(s,\mathcal L)\le(s+\mathcal L)^{O(1)}
 2^{(84.0662714943\ldots+o(1))s/\sqrt{\lceil\log_2s\rceil}}
\]

with polynomial space, on **the same normalized interface** used for the supplied 648.4411 certificate: at most s edges, maximum degree at most ceil(s^.9), P0 and ell at most s, and initial entry cost poly(s+L) 2^{A s^.9} for fixed A. The coefficient may be replaced by 85 for sufficiently large s. This is not a smaller logarithmic order, a full independent proof of the ETH claim, a measured speedup, a numerical coefficient directly in SAT variable count, or a formally verified theorem. Exceptional sizes and parameter failures are handled by direct summation, as in the source; the crossover can be enormous.

The principal additional contributions here are: (1) deterministic near-balanced collision packing using edge-color matchings; (2) a thin additive precision gap instead of doubling every taper increment; (3) exact counting of crossing rather than all padded packets; (4) a larger root grouping alphabet than the tail alphabet. Exact taper, sharp precision, and factorial-Cauchy modes are reused from the supplied reports, not claimed as new.

## 1. Deterministic packing for multigraphs

Let an active bipartite multigraph have M edges and maximum degree Delta. Let q=r^a be the number of labels on each side and Darr=q^2. Greedy edge coloring uses K<=2 Delta-1 colors; every color class E_j is a matching, including when the graph has parallel edges. Put m_j=|E_j|. Assign independent uniform labels in [q] to vertices. For a pair gamma of labels let X_{j,gamma} be the number of edges of E_j receiving gamma.

Set lambda=ceil(log2 s)>=2, z=1+1/lambda, and

\[
 t_j=\left\lceil (1+1/\lambda)m_j/D_{arr}+10\lambda^2\right\rceil,
 \qquad \Phi=\sum_{j,\gamma}z^{X_{j,\gamma}-t_j}.
\]

For each fixed matching, the indicators for its different edges are independent. There is **no assumption of independence between matchings**. Consequently,

\[
\mathbb E\Phi
 =\sum_{j,\gamma}z^{-t_j}(1+1/(\lambda D_{arr}))^{m_j}
 \le K D_{arr} e^{-5\lambda}<1
\]

for all sufficiently large s in the schedules below. Indeed ln(1+1/lambda)>=1/(2lambda) and (1+1/lambda)ln(1+1/lambda)>=1/lambda; applying these to t_j and using ln(1+x)<=x gives e^{-5lambda} per summand. Our schedules have Darr<=s and K<=4s, so the last strict inequality is elementary for sufficiently large s.

This existence proof is algorithmic. Conditional on any partial vertex labeling, distinct matching edges remain independent, and an edge's conditional probability of receiving gamma belongs to {0,1/q^2,1/q,1}. Thus the conditional expectation of every summand is exactly

\[
 z^{-t_j}\prod_{e\in E_j}(1+p_e/\lambda).
\]

All factors are rational. At the next vertex, try each of the q labels and take one minimizing the conditional expectation. Its average is the current expectation, so the invariant Phi_conditional<1 persists. At the end every X_{j,gamma}<t_j, since otherwise one positive summand would be at least one. Summing and using ceil(x)-1<x gives

\[
 X_\gamma < (1+1/\lambda)M/D_{arr}+10K\lambda^2
 \le (1+1/\lambda)M/D_{arr}+20\Delta\lambda^2.
\]

The number of tested labels, terms, and edges is polynomial in s+description length. Products and powers have polynomial bit length: exponents t_j are O(s+lambda^2), denominators are powers of polynomial-size integers, and K Darr and q are polynomial. Exact rational conditional expectation therefore gives a deterministic polynomial-time and polynomial-space construction; efficiency constants are not claimed practical.

Pad every pair-label class to the same multiple Hpad of L=2^a. Then

\[
B:=H_{pad}D_{arr}
 \le (1+1/\lambda)M+20D_{arr}\Delta\lambda^2+LD_{arr}.
\]

If Darr Delta polylog(s)=o(M) and L Darr=o(M), then B=(1+o(1))M. This replaces the source's sufficient Darr^2 Delta=o(M) condition, while retaining exactly its subsequent packet arrangement. In particular, there are B/L packets and every coordinate-symbol class has at most B/r real ports on each side. A child has at most 2B/r=(2/r)(1+o(1))M edges. New packet vertices still have degree at most 2L and retained vertices retain their old degrees.

The scale of this improved padding condition is essentially sharp for this architecture. Take t vertex-disjoint pairs, each joined by Delta parallel edges, so M=t Delta. Every nonzero label-cell load is a multiple of Delta, and some cell has load at least Delta. Equal padding therefore has B=Hpad Darr>=Delta Darr. Near-unit total padding B=(1+o(1))M is impossible if Darr Delta/M diverges, regardless of labeling. This is only a limitation of equal-padded collision packing, not a contraction or SAT runtime lower bound.

For a fixed coordinate, exactly a fraction 1-1/r of the padded pair labels have unequal symbols. Every packet fixes that unordered pair, so exactly (1-1/r)B/L packets can contribute crossing modes in that coordinate. At a retained node with valuation i and Dt=2^{a-i}, there are therefore at most

\[
c\le 2(1-1/r)B/D_t=(2(1-1/r)+o(1))M/D_t
\]

column-tile families. Empty or local-only tiles can only reduce this count.

## 2. The thin-gap precision schedule

Write g(lambda)=ceil(log2 lambda)^2. For any positive taper sequence u_d, use

\[
 a_d=\sum_{j=0}^d u_j+(d+1)g(\lambda),\qquad a_{-1}=0.
\]

The source needs the cumulative packet exponent to dominate inherited precision, not literally a_d=2 sum u_j. At retained i<u_d,

\[
 D_t=2^{a_d-i}\ge2^{a_{d-1}+g+1}.
\]

Use the complete linear taper

\[
 h=\left\lceil\frac{M(2L-1)+1}{L(2u-2+2^{1-u})}\right\rceil,
 \quad q_i=h(u-i),\quad 0\le i<u,
\]

and zero thereafter. The supplied exact precision formula is

\[
 p_t=p+B_i+(q_i-1)(a+1-i),\quad
 B_i=D_t\sum_{j=1}^{a-i}j2^{-j}(q_i-q_{i+j})\le6hD_t.
\]

The multiplicities provide more conditions than the deformation degree. They are nonincreasing, the precision increments are positive, and the source's immutable creation-precision lifting convention is preserved.

Along a path, increments are at most s lambda^{O(1)}2^{a_d}; thus inherited p<=s lambda^{O(1)}2^{a_{d-1}}. With leaf cutoff H=ceil(s/lambda), active M>s/lambda and u<=O(lambda), the inherited precision divided by M Dt/u is at most lambda^{O(1)}2^{-g}=o(1). The evaluation loss is negligible by the same bound. If u grows as a positive power of lambda uniformly at active depths, then h=(1+o(1))M/u, and

\[
 p_t\le(6+o(1))MD_t/u
\]

uniformly. The gap consumes only O((log lambda)^3)=o(lambda) label coordinates over O(log lambda) recursion levels. No extra root precision is assumed.

## 3. Compatibility with factorial Cauchy modes and bit complexity

Use the supplied Cauchy report's exact separated features with weights

\[
 w_b=1+b+2v_2(b!)=3b+1-2s_2(b),\quad 0\le b<D_t/2.
\]

The needed congruence of actual row parameters to the prime subring holds at every interpolation value: z_x/2 differs from the rational 2-integral 2^i/d0 by an element divisible by 2^{a+1-i}. Since b<D_t/2=2^{a-i-1}, the factorial-divisibility proof applies. There is no factorial division in a residue ring: the binomial feature is computed as an ordinary integer, while b! is multiplied into the target coefficient. All denominators introduced by these features are units. Changing the taper, packing bound, or r at different calls changes none of these local facts.

The standard generating product for these weights has

\[
\log N(p,c)\le(\pi\sqrt{2}/3+o(1))\sqrt{cp}.
\]

Apply this upper bound using the precision envelope P=(6+o(1))M Dt/u and family envelope Cfam=(2(1-1/r)+o(1))M/Dt, rather than asserting that actual p or the number of nonempty families attains these bounds. The ratio P/Cfam has scale Dt^2/u and Dt>=2^g, so the small-saddle regime and its error bounds hold uniformly. Finite tile truncation or empty families only decreases the count. Combining the bounds above yields the local natural-log coefficient

\[
 \log N\le\left[2\pi\sqrt{\tfrac23(1-1/r)}+o(1)\right]M/\sqrt u.
\]

The exact local kernel, creation-time representatives, and recursive child tensor definitions are otherwise unchanged. Source packet-entry enumeration costs exp(O(L log s)); the supplied streamed finite-difference replacement can instead give poly(s+description length) 2^L with at most L extra internal precision bits. Either routine is lower order in the schedule below. If using finite differences, compute the numerator modulo 2^{p_creation+v2(product beta!)} and only then divide its canonical coordinates by that explicit power of two. Temporary extra precision does not change tensor creation precision.

The field extension remains degree 4lambda, since deformation degrees are M(2L-1)<s^4 eventually. All precisions, rational recovery operands, field coordinates, and descriptions have polynomial bit length. Ell<=s is still allowed; the scalar parity improvement may set ell=1 in its application but is unnecessary for this normalized contraction theorem. The original entry allowance 2^{A s^.9} is lower order. Entry routines are not recursively composed; old descriptions are immutable.

## 4. An explicit two-stage schedule

Use the following exact rational choices:

\[
 r_0=37,\quad u_0=\lfloor (10/1043)\lambda\rfloor,
\]

\[
 r_d=8,\quad u_d=\left\lfloor\frac{\lambda}{236(5/2)^{d-1}}\right\rfloor\quad(d\ge1).
\]

Use the thin-gap a_d above and H=ceil(s/lambda). To avoid a circular depth estimate, first consider the candidate depths d<=N=ceil(log_3 lambda)+3. For these depths (d+1)g=O((log lambda)^3)=o(lambda) without assuming anything about the actual recursion. At the root a0/lambda<=10/1043+o(1), while through these candidate tail depths

\[
 a_d/\lambda\le A+o(1),\qquad
 A=10/1043+5/708=0.016649874601188\ldots.
\]

Packing exponents are strictly below one:

\[
 .9+2(10/1043)\log_2 37=0.999893640759903\ldots<1,
\]

\[
 .9+2A\log_2 8=.9+6A=0.999899247607131\ldots<1.
\]

The first strict inequality can be verified by the exact integer inequality 37^{200}<2^{1043}. The second is rational. Consequently Darr Delta lambda^3/s=o(1), uniformly. Also L Darr lambda/s=o(1), since L Darr has root exponent (10/1043)(1+2log2 37) and tail exponent 7A, both below one. Finally 2L<=Delta eventually. The construction checks these finite inequalities at runtime and directly sums the finite exceptional range.

These estimates bootstrap the actual depth bound. For every candidate tail call with M>H they imply B/M<=4/3 eventually, and hence each tail child has at most M/3 edges. Starting with M<=s, no active call reaches depth N. Thus all real active calls lie in the candidate range, closing the induction rather than presupposing the depth. This coarse bound already ensures u_d grows as a positive power of lambda, since 5/2<3.

In fact B/M=1+O(1/lambda)+o(1/lambda), so the overhead accumulated over O(log lambda) depths is 1+o(1). At depth d>=1,

\[
 M_d\le(1+o(1))s(2/37)4^{-(d-1)}.
\]

An active tail depth is at most log_4 lambda+O(1); therefore

\[
 u_d=\Omega(\lambda^{\eta+o(1)}),\qquad
 \eta=1-\log(5/2)/\log4>0.
\]

This closes the induction, justifies uniform floors, and verifies the precision regime.

Define

\[
 K(r)=\frac{2\pi}{\ln2}\sqrt{\frac23(1-1/r)}.
\]

Summing branching logarithms along a path gives the base-two coefficient

\[
 C=\frac{K(37)}{\sqrt{10/1043}}+
 \frac{(2/37)K(8)}{\sqrt{1/236}(1-\sqrt{5/2}/4)}
 =84.06627149423657\ldots<85.
\]

For an elementary exact check of the rounded certificate, use pi<22/7, ln2>69/100, sqrt(12516/185)<8226/1000, sqrt(413/3)<11734/1000, and sqrt(5/2)<1582/1000. They imply C<9128012476/108030195=84.49501064...<85 without relying on floating-point evaluation.

Polynomial branching over O(log lambda) levels contributes O(lambda log lambda), and leaf work has exponent O(s/lambda). Both are lower order. Depth-first accumulation preserves polynomial space. The dependency on description length stays a fixed polynomial because branching counts depend only on s, not that length.

## 5. Comparisons, provenance, and limits

* Supplied contraction report: C=648.4410666487 on this same interface, using geometric modes, r=256, 3-padding, doubled cumulative taper, and six-bit precision.
* Simply adding factorial weights to that certificate yields C/sqrt(3)=374.3776..., but requires the compatibility checks above.
* Keeping the source's collision packing but taking its asymptotically sharp padding and thin gaps already gives a conservative coefficient about 134.
* The new matching packing plus constant r=46, b=8, epsilon=10/1263 gives C=93.8049738133 (<94).
* The two-stage schedule above gives C=84.0662714943 (<85).

These are comparable explicit certificates for declared constructions, not lower bounds or runtime measurements. The general-density SAT wire budget remains O_k(n log log n), and the fixed-density budget O_{k,D}(n), so the supplied logarithmic orders do not change. The scalar parity improvement and density refinement affect that reduction separately and must not be multiplied blindly into the normalized s coefficient. The coefficient cannot be placed directly before n without explicit reduction constants.

Exact optimal taper profiles improve finite precision but have the same leading six-bit loss, so they are optional here. The current schedule is not claimed globally optimal, even among depth-varying grouping schedules. A smaller logarithmic order would require a different summation/representation idea; none is established by this note.

### Source anchors (local snapshots)

* OpenAI source `eth_3sat_improvement_20261027/source/build/quantitative-reduction.tex`, lines 15–18: multigraph interface. `quantitative-contraction.tex`, lines 11–72: arithmetic and canonical creation precision; 114–171: packing and packet arrangement; 183–241: deformation/integrality; 274–323: Hermite identity and valuation loss; 385–451: groups and column tiles; 485–554: factorization, child degree, entry descriptions; 558–619: time/space induction.
* Supplied contraction report, `eth_contraction_improvements/eth_contraction_improvements/report.tex`: labels `lem:taper`, `lem:precision`, `thm:packet`, `thm:main`.
* Supplied Cauchy report, `cauchy_mode_improvement_2026-10-26/cauchy_mode_improvement/report.tex`: labels `lem:identity`, `lem:factorial`, `lem:actual-domain`, `thm:weights`, `prop:recursion`, `lem:entropy`.
* Supplied precision report, `3sat_precision_refinement_2026-10-26/3sat_precision_refinement/report.tex`: labels `thm:precision`, `thm:optimal`.

This note was independently derived from the source and supplied proofs. Numerical/finite regression checks accompany it; finite checks do not replace its asymptotic proof.
