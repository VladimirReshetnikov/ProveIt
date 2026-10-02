# Independent audit: second-order coefficient lower construction

Audit date: 2 October 2026. This audit is independent of the author of `../a202061-second-order-research/coefficient-lower-second-order.md`. Frozen foundation files are not changed.

## Verdict

The construction proves, for all sufficiently large integer n,

D_n <= C F + (7C/3) F loglog(n)/log(n) + O(F/log(n)),

where F=n^(1/3)(log n)^(2/3), A=2 pi^2 alpha^2/v, and C=(3A/4)^(1/3).

This is a one-sided bound. It establishes neither a matching lower bound on D_n nor an asymptotic expansion by itself. I found no gap in the balanced-path conditioning, Jensen step, or O(M) accumulated error argument. One harmless rounding error in the original prose is recorded below.

## The imported foundation

The inputs used are the exact positive height-walk expansion and its local positive kernel lower bound, already stated and independently reviewed in the frozen sharp-deficit release. The required local bound is only

sum over a fixed-width shifted q-window of rho^ell t^d B(ell,q,q+d-1)
 >= c ell^(-2) exp(-d^2/(2v ell)-epsilon_n),

uniformly for ell>=c(log n)^7 and |d|<=C sqrt(ell log n), with epsilon_n=o(1). The stronger full local equivalent in the kernel note is unnecessary. Its conditional q center may be displaced by O(sqrt(ell log n)); the audited construction accounts for the displacement.

## 1. Scale and endpoint checks

Write L=log n and M=round((6An/L)^(1/3)). With J=ceil(L^3), the deterministic profile obeys

n/M^3=Theta(L), h_j=Theta((n/M) sin^2(pi j/M)),
ell_j=Theta((n/M) sin^2(pi j/M)).

For j between J and M/2, both h_j and ell_j are Theta(L j^2). The analogous statement uses M-j on the right half. Thus the minimum is Theta(L^7), while h0=O(L^7)=o(M). Every proposed length and height perturbation remains in the local-kernel range uniformly, including both ends.

The strict margin alpha ell_j <= (1-4/L)h_j+O(1) follows from n'/n<1 and integer rounding. Since ell_j~h_j/alpha,

sqrt(ell_j L)/(h_j/L)=O(L^(3/2)/sqrt(h_j))=O(L^-2)

at worst. Therefore the q-window displacement is negligible relative to the reserved h_j/L margin.

## 2. Exact balancing and good paths

A convolution of centered integer-interval indicators is symmetric and unimodal. One direct proof writes an arbitrary symmetric unimodal sequence as a nonnegative linear combination of centered interval indicators; convolution of two centered intervals is symmetric unimodal. Consequently the central coefficient is at least the average over its support. This gives probability at least 1/(2 sum b_j+1) of sum V_j=0 and the analogous bound for sum U_j=0. Because b_j<=ell_j and w_j<=ell_j for large n, both denominators are at most 2n+1.

For k<=M/2, variance sum <=C L k^3, maximal increment <=C sqrt(L) k, and the forbidden bridge excursion threshold h_k/L >=c k^2. Bernstein therefore gives

P(|sum_{j<k} V_j|>h_k/L) <=2 exp(-c k/L).

Since k>=J~L^3, this is at most 2 exp(-c L^2). For k>M/2, use the independent suffix in the unconditional calculation and only then use that it equals the negative prefix on the bridge event. Dividing by the polynomial lower bound for the bridge probability and union-bounding all boundaries yields at most C nM exp(-cL^2), which tends to zero exponentially in L^2.

This argument never assumes that the increments stay independent after conditioning. Simultaneous sign reversal preserves the bridge condition and every good-path constraint, so every coordinate of the uniform good bridge still has mean zero. Its second moment is at most b_j^2<=ell_j. The length bridge also has zero coordinate means, and the two complete vectors can be sampled independently.

The resulting number of rectangles is at least

prod_j (2w_j+1)(2b_j+1) / [2(2n+1)^2].

Every one is legal: its starting height is at least h_j-h_j/L, whereas every retained q is at most h_j-2h_j/L for all sufficiently large n. Intermediate macro heights are positive, and q<=height is precisely the legality condition in the exact positive expansion. The saddle lies in the positive factorial interior, so the positive r and auxiliary parameters cause no hidden constraint.

## 3. Jensen and the averaged energy

Under the uniform distribution on the retained Cartesian product, U and V are independent as complete vectors. Coordinatewise independence within either vector is neither true nor used. Thus

E[(g_j+V_j)^2/(ell_j+U_j)]
 =(g_j^2+E[V_j^2]) E[1/(ell_j+U_j)].

The identity (1+x)^(-1)=1-x+x^2/(1+x), the exact centering E U_j=0, and |U_j|/ell_j<=1/L imply

E[1/(ell_j+U_j)] <= ell_j^(-1)(1+O(L^-2)).

It follows that the increment fluctuations cost O(M), and the length fluctuations cost O(L^-2 sum g_j^2/ell_j)=O(M/L). Concavity gives E log(ell_j+U_j)<=log ell_j. The convexity inequality E e^(-X)>=e^(-E X) has the favorable direction required for the positive sum. There is no lost O(M sqrt L) linear fluctuation term.

The volume gains are log ell_j-log L+O(1) and (1/2)log ell_j+O(1), against the kernel loss 2log ell_j. This leaves exactly

(1/2)sum log ell_j + m log L.

The local epsilon_n errors total o(M). All fixed per-block prefactors total O(M), and the two balancing denominators cost O(L)=o(M).

## 4. Exact degree, seeds, and absence of interpolation

The ascent seed, final descent, and first letter together have degree 2h0+1. There are m leading x factors in the large blocks and sum actual ell_j=n-m-2h0-1. Hence every retained object has degree exactly n. The macro increments return to h0 and the two seeds return the full walk to 1, so all height tilts cancel. The seed degree tilt costs O(h0)=O(L^7)=o(M). The terminal series may contribute its constant term. The argument therefore applies to every sufficiently large integer n directly.

## 5. Deterministic error budget

Before rounding,

sum (s_{j+1}-s_j)^2/s_j
 =2pi^2/M+O((J+log M)/M^2).

The exact displayed trigonometric decomposition in the author's note is correct. Its main square error is O(J/M^2), the cross term is O(log M/M^2), and the final square is O(1/(M^2J)). Multiplication by H0^2 S/n'=Theta(n/M) converts the total error into O(L(J+L))=O(L^4)=o(M).

The profile inflation factor (1-4/L)^(-2) differs from 1 by O(1/L). Multiplying the leading kinetic energy Theta(ML) gives O(M), as required. The omitted seed and macro degree correction n-n'=O(M+L^7) creates a smaller error.

Height rounding contributes at most a constant times

sum |unrounded g_j|/ell_j + sum 1/ell_j = O(log M)=O(L).

This follows near the left endpoint from |unrounded g_j|/ell_j=O(1/j), and on the right from O(1/(M-j)). Length rounding contributes at most

C sum g_j^2/ell_j^2 <= C (min ell_j)^(-1) sum g_j^2/ell_j
 =O(ML/L^7)=o(M).

Thus sum g_j^2/ell_j=4pi^2 alpha^2 n/M^2+O(M).

For the entropy sum, the sine product and deletion of 2J endpoint terms give

sum log s_j=-2M log 2+O(J log M+log M).

The deleted endpoint logarithms cost O(L^4)=o(M). Also sum 1/ell_j=O(1/(LJ))=o(1), so integer rounding is negligible even in absolute logarithmic error. Replacing m by M in m log(n/M) costs O(JL)=o(M), and replacing m log L by M log L costs O(J log L)=o(M). Therefore

(1/2)sum log ell_j=(M/2)log(n/M)+O(M).

## 6. Final expansion and required textual correction

The intermediate bound is rigorously

D_n <= A n/M^2+(M/2)log(n/M)+M log L+O(M).

For real x=(6An/L)^(1/3), xL/2=CF exactly. With integer M=round(x), it is generally false that A n/M^2=ML/6+o(1), or that ML/2=CF+o(1). The valid separate errors are O(L), harmless since L=o(M). The sum A n/M^2+ML/3 is stationary at x, so its combined rounding error is even O(L/M).

Using log(n/M)=(2/3)L+(1/3)log L-(1/3)log(6A)+O(1/M),

the leading cost is CF and the next displayed term is (7/6)M log L=(7C/3)F log L/L+o(F/L). Every remaining cost is O(M)=O(F/L). This establishes the stated one-sided refinement.
