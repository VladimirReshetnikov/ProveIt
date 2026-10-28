# A cached asymmetric contraction certificate below 38

## Result and scope

Combining the supplied asymmetric two-stage packet balancing and full crossing-block Cauchy factorization, and changing the grouping/taper schedule and block sizes, gives the normalized contraction bound

\[
T(s,\mathcal L)\le(s+\mathcal L)^{O(1)}
2^{(37.93010908288456\ldots+o(1))s/\sqrt{\lceil\log_2s\rceil}},
\]
\[
S(s,\mathcal L)\le(s+\mathcal L)^{O(1)}
2^{(33.62304092165775\ldots+o(1))s/\sqrt{\lceil\log_2s\rceil}}.
\]
Thus eventual coefficients 38 for time and 34 for space are valid. This is **not a polynomial-space bound**. It is conditional on the unchanged source contraction identities and on the supplied full crossing-block factorization, not an end-to-end independent certification of the SAT claim. It retains the normalized maximum-degree bound ceil(s^.9), P0,ell<=s, and polynomial-description entry-oracle interface. The coefficient is not directly on SAT variable count n. No logarithmic-order improvement is established.

The new work here is the r=7 root/r=9 tail schedule and its cost analysis, not the imported cache factorization, Strassen identity, asymmetric balancing, or slope-four modes. A numerical search in the two-stage schedule family suggests an infimum near 37.89056; no global optimality is claimed. The rounded 38 certificate below is proved independently of numerical optimization.

## 1. Uniform entropy per ordered group pair

Write lambda=ceil(log2 s), P=(1+o(1))M for padded mass, D=2^(a-i), and u for the retained taper range. Equal pair-label padding and the orientation arrangement give at most

\[
c_{gh}\le(2+o(1))M/(r^2D), \qquad g\ne h,
\]

full crossing orientation families on each ordered group pair. The supplied joint Cauchy factorization gives weights a+1-i+4q-2s2(q), whose generating entropy has leading pi^2/(24 theta). The inherited sharp precision upper envelope is p_t<=(6+o(1))MD/u. The same common-parameter weighted generating-function proof as in the supplied joint report therefore gives, for fixed nonnegative pair weights w_e,

\[
\sum_e w_e h_e\le
 (\sqrt{\sum_e w_e^2/r^2}+o(1))K(M,u),
\qquad K(M,u)=\frac{\pi\sqrt2}{\ln2}\frac M{\sqrt u}.
\]

Here h_e is the binary index length of the exact-weight mode list on pair e. The polynomial number of exact per-pair weight allocations is enumerated, with empty lists discarded, exactly as in the supplied report. No exponentially cheap group oracle is assumed: group functions are recursively computed and cached explicitly.

## 2. Three-block constants for arbitrary fixed r

Partition r groups into three blocks k1,k2,k3. Each group is incident with 2(r-1) ordered pairs, so the cache-recursion coefficient is

\[
\alpha_r=\sqrt{2(r-1)}/r.
\]

For a block of size k, enumeration of all its incident pair indices builds its boundary table with coefficient sqrt(2rk-k^2-k)/r; storage is sqrt(2k(r-k))/r. Put

\[
 A_r=\max_j\sqrt{2rk_j-k_j^2-k_j}/r,
\quad J_r=\max_j\sqrt{2k_j(r-k_j)}/r.
\]

Let v12=2k1k2, v13=2k1k3, v23=2k2k3 and tau=log2(7)-2. Rectangular Strassen multiplication of the three boundary tables has coefficient

\[
 B_r=\frac1r\sqrt{v12+v13+v23-(1-\tau^2)\min(v12,v13,v23)}.
\]

Set beta_r=max(A_r,B_r). These statements follow directly from the weighted entropy inequality. Strassen's seven-product formula uses no division, so works over the source quotient ring. Sequential record access, reblocking, and sorting can be implemented as in the supplied report; only fixed constants and block dimensions change.

The recurrence, suppressing polynomial factors, is

\[
T_d\le 2^{(\alpha_{r_d}+o(1))K_d}r_dT_{d+1}
     +2^{(\beta_{r_d}+o(1))K_d}.
\]

Critically, block-building counts do not multiply a fresh child contraction: they read already computed group caches.

At r=7 choose blocks (3,2,2). Then

\[
\alpha_7=\sqrt{12}/7,\qquad
\beta_7=\sqrt{30}/7,\qquad J_7=\sqrt{24}/7.
\]

Indeed the matrix term is sqrt(24+8tau^2)/7<sqrt(30)/7. At r=9 choose blocks (3,3,3). Then

\[
\alpha_9=4/9,\qquad
\beta_9=\sqrt{36+18\tau^2}/9,\qquad J_9=2/3.
\]

The matrix term exceeds the build term sqrt(42)/9.

## 3. An entirely rational schedule

Take

\[
r_0=7,\quad u_0=\lfloor89\lambda/5000\rfloor,
\]
\[
r_d=9,\quad
u_d=\left\lfloor\frac{1233}{125000}
       \left(\frac7{25}\right)^{d-1}\lambda\right\rfloor
\quad(d\ge1).
\]
 Use the standard additive guard b=ceil(log2 lambda)^2 and a_d=sum_{j<=d}(u_j+b). The total leading budget is

\[
\frac{89}{5000}+
\frac{1233/125000}{1-7/25}=\frac{63}{2000}.
\]

Use leaf threshold H=ceil(s/lambda). At the root, the symmetric matching or two-stage packing conditions hold because

\[
.9+2(89/5000)\log_2 7<1,
\]

witnessed exactly by 7^89<2^250. Below the root, the child side-degree invariant gives R_d<=ceil(s^.9), C_d<=2L_{d-1}. Hence

\[
\frac{Q_dR_d}{M}=o(1)
\]

because .9+(63/2000)log2 9<1, witnessed exactly by 9^63<2^200. The other padding terms satisfy

\[
Q_d^2C_d,\;L_dQ_d^2
 \le s^{(63/2000)(1+2\log_2 9)+o(1)}
 <s^{.232+o(1)},
\]

so they are lower order uniformly for M>s/lambda. All new degrees remain below s^.9. Root rounding is smaller still.

For a noncircular bootstrap, consider candidate depths d<=ceil(log_4 lambda)+3. The additive gaps sum to O((log lambda)^3)=o(lambda). All strict power gaps above hold uniformly there, so padding has P/M=1+O(1/lambda)+o(1/lambda) and tail children eventually have at most M/4 edges. Thus actual active paths cannot exceed the candidate range. Since 7/25>1/4, each active u_d grows at least as lambda raised to a fixed positive power; floors are uniformly negligible. The sharp shrinkage is

\[
M_d\le(1+o(1))s(2/7)(2/9)^{d-1},\quad d\ge1.
\]

Since 2^b dominates every fixed polynomial in lambda, the additive precision guard therefore gives the same uniform p_t<=(6+o(1))MD/u. All labels, precisions, deformation degrees and recovery integers have polynomial bit length. Entry computation, direct leaves, and polynomial branching contribute only o(s/sqrt(lambda)) in the exponent. Immutable creation-time representatives are unchanged.

## 4. Solving time and storage

Let kappa=pi sqrt2/ln2 and

\[
K_0=\kappa/\sqrt{89/5000},\quad
K_1=\frac{(2/7)\kappa}{\sqrt{1233/125000}},\quad
\gamma=\frac{2/9}{\sqrt{7/25}}=\frac{10}{9\sqrt7}.
\]

These denote the coefficients on s/sqrt(lambda). The tail local coefficient at depth d>=1 is K1 gamma^(d-1). Its recurrence has total coefficient

\[
K_1\max\{\beta_9,\alpha_9/(1-\gamma)\}.
\]

Numerically alpha9/(1-gamma)=.76623137568005...<beta9=.76765472130967..., so the tail matrix term dominates. Equivalently, the work stopped at tail depth j has coefficient alpha9 K1(1-gamma^j)/(1-gamma)+beta9 K1 gamma^j, a convex interpolation of the two endpoints. Including the root gives

\[
C_T=\max\{\beta_7K_0,
                 \alpha_7K_0+\beta_9K_1\}
=37.93010908288456\ldots.
\]

The tail remains below its first storage cost because gamma<1; ancestor records add rather than multiply their spaces. Thus

\[
C_S=\max\{J_7K_0,J_9K_1\}
=33.62304092165775\ldots.
\]

The first max entry for time is 37.59170255554196..., and the second is the stated result. A reader may retain the max involving alpha9/(1-gamma) rather than use the numerical domination; it gives the same rounded certificate and avoids needing that strict comparison.

## 5. Exact checks and provenance

`check_certificate.py` is original standard-library code. It checks the rational budget identity, integer capacity witnesses, tail bootstrap margin, mode/block constants, and a rational upper bound using pi<22/7, a six-term positive series lower bound for ln2, log2 7<281/100 (checked by 7^100<2^281), and integer-square-root enclosures. It does not load or execute supplied research code. Its certified time upper bound is 37.95679951304334...<38 and space upper bound33.63657935944941...<34. Floating point is used only to display the sharper formulas, not to establish the rounded bounds.

`search.py` is an original exploratory numerical search of two-stage schedules; its output is not a proof of optimality. The theorem is established by the displayed schedule and symbolic inequalities, not the search or finite tests.

Imported sources:

* `eth_joint_cauchy_2026-10-26/.../report.tex`, sections on exact-weight allocations, weighted entropy, three-block group caching, rectangular multiplication, and the full recursive time/space cost (local source lines 680--878).
* `eth_asymmetric_packet_balancing_2026-10-26/.../report.tex`, Theorem pair-balance, padding corollary, side-degree invariant, additive guard and sharp precision.
* The unchanged OpenAI deformation, recovery, child construction and creation-precision conventions cited by those reports.

The prior asymmetric report with joint slope-four modes has a polynomial-space coefficient about66.605; it is a separate space class. The present comparison is to the combination of those same mechanisms **with the already supplied caching/Strassen method**, and improves that time certificate by rechoosing the alphabet, taper, and finite block sizes. It does not count the act of combining imported mechanisms as a new theorem.

## 6. A lower-degree cached certificate below 14.3

Suppose additionally that the root maximum degree is at most ceil(s^(1/12)). **Do not require this degree bound to remain invariant**: it is enough to track the packet degrees. Retained tensors never gain ports. At depth d>=1 both side degrees are at most

\[
\max\{\lceil s^{1/12}\rceil,2L_{d-1}\}.
\]

Use symmetric matching packing (or the asymmetric lemma with the same upper bound on both sides). For nondecreasing a_d with a_0/lambda>1/12, it suffices that a_d(1+2log2 r_d)<lambda with strict power slack. This follows because Q_d^2 times the previous maximum degree is at most 2^(2a_d log2r_d+a_{d-1}+O(1)), and rounding costs at most 2^(a_d(1+2log2r_d)). The original high-degree parameter s^.9 need not be retained when smaller degree information is known.

Take

\[
r_0=12,\qquad u_0=\lfloor239\lambda/2000\rfloor,
\]
\[
r_d=7,\qquad
u_d=\left\lfloor\frac{567}{32000}
       \left(\frac7{16}\right)^{d-1}\lambda\right\rfloor
\quad(d\ge1).
\]
 Use the same additive guard and leaf threshold. The total leading packet budget is

\[
\frac{239}{2000}+
\frac{567/32000}{1-7/16}=\frac{151}{1000}.
\]

At the root, the rounding and packing conditions follow from

\[
(239/2000)(1+2\log_2 12)<1,
\]

certified exactly by 12^478<2^1761. The degree term is smaller because 239/2000>1/12. In the tail,

\[
(151/1000)(1+2\log_2 7)<1,
\]

certified by 7^302<2^849. This also bounds the previous-degree term since a_{d-1}<=a_d. The maximum created degree remains s^{.151+o(1)}<s^.9, so all unchanged oracle and arithmetic bounds remain valid.

Tail children have sharp ratio 2/7 and eventual coarse ratio 1/3. The candidate-depth bootstrap uses ceil(log_3 lambda)+3; since 7/16>1/3, the retained taper grows uniformly as a positive power of lambda. All precision, entropy, floor, and bit-complexity arguments from Sections 1--4 carry over.

At the root use blocks (4,4,4), giving

\[
\alpha_{12}=\sqrt{22}/12,\quad
\beta_{12}=\sqrt{2(2+\tau^2)}/3,\quad J_{12}=2/3.
\]

The tail uses the previously computed r7 constants. Define

\[
K_0=\frac\kappa{\sqrt{239/2000}},\qquad
K_1=\frac{\kappa/6}{\sqrt{567/32000}},\qquad
\gamma=\frac{2/7}{\sqrt{7/16}}=\frac8{7\sqrt7}.
\]

The coefficients are

\[
C_T^{\rm low}
=\max\left\{\beta_{12}K_0,
\alpha_{12}K_0+K_1\max\left(\beta_7,
            \frac{\alpha_7}{1-\gamma}\right)\right\}
=14.23918819443970\ldots,
\]
\[
C_S^{\rm low}=\max\{(2/3)K_0,J_7K_1\}
=12.36130145759395\ldots.
\]

Thus eventual coefficients 14.3 for time and 12.4 for space hold on this additional low-degree interface. Integer coefficients 15 and 13 are looser alternatives. Root matrix work contributes 14.23381713818120..., while the infinite cache-chain endpoint in the tail gives the slightly larger total. Original entries may still have the source allowance exp(O(s^.9)); that is lower order on this scale.

`check_lowdegree.py` independently checks the exact capacities, budget identity, coarse-shrink margin and rational coefficient envelopes. It certifies time<14.25102972375682<14.3 and space<12.36627877987977<12.4. Normal and `python -O` runs agree because failures use explicit exceptions, not removable assertions.

For comparison, substituting the joint modes and existing caching scheme into the supplied low-degree r48 schedule gives time 18.41065978423048 and space 15.98866371660825. The supplied generic r16 asymmetric schedule similarly gives cached time 44.53757185496245 and space 39.49594953369977. These are compatible combined baselines, not the individual proposal headline constants. Further, the independent audit examines all fixed-r three-block coefficient schedules and finds that the generic 38 certificate beats that entire stated family; this is a lower bound on those certificate expressions, **not an algorithmic runtime lower bound**.

### Finite block constants and denominator audit

The normalization is **r²**, because each ordered pair has the same family envelope 2P/(r²D); the absent diagonal pairs reduce the number of summands, not the denominator. Replacing this denominator by r(r−1) would incorrectly redistribute absent families onto the off-diagonal pairs.

| Alphabet / blocks | Incident pairs per group | Maximum block incident pairs | Directed block-pair class sizes | Maximum boundary pairs |
|---|---:|---:|---|---:|
|7 /3,2,2|12|30|12,12,8|24|
|9 /3,3,3|16|42|18,18,18|36|
|12 /4,4,4|22|76|32,32,32|64|

Consequently the squared build factors are 30/49,42/81,76/144; the squared rectangular factors are (24+8tau²)/49,(36+18tau²)/81,(64+32tau²)/144. Their maxima give exactly the beta constants used above. In particular the generic root r7 is **table-construction dominated**, not matrix-multiplication dominated. This distinction is material to the coefficient.

`replay_checks.py` runs both exact checkers normally and with `-O`, requires byte-identical stdout, and reruns modified too-strong thresholds as negative controls. All four positive runs pass and all four negative controls fail by explicit RuntimeError. `verification_runs.json` records these results. No supplied script is imported or executed.
