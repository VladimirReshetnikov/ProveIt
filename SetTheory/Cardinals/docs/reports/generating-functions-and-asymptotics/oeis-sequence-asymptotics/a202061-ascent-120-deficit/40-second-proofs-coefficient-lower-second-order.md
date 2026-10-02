# Second-order coefficient lower bound: a rigorous balanced-rectangle refinement

Research result, 2 October 2026. This note is separate from the frozen audited release. It uses only the release's audited local positive kernel lower bound and exact positive representation. Its new probabilistic counting argument should receive independent review.

## Result

Put L=log n, F=n^(1/3)L^(2/3), and use the release's constants

A=2 pi^2 alpha^2/v, C=(3 pi^2 alpha^2/(2v))^(1/3).

Then the exact-length construction proves

D_n := n log(mu)-log a_n
 <= C F + (7C/3) F (log L)/L + O(F/L).                 (T)

This is a one-sided refinement. It does not by itself prove the coefficient 7/3 in an asymptotic expansion.

More explicitly, with M=round[(6A n/L)^(1/3)] the intermediate bound is

D_n <= A n/M^2 + (M/2)log(n/M) + M log L + O(M).       (B)

Here 6A=12 pi^2 alpha^2/v, so A n/M^2=ML/6+O(L), and ML/2=C F+O(L). Expanding log(n/M) gives (T).

## 1. Deterministic construction

Set J=ceil(L^3), eta=4/L, m=M-2J, and, for J<=j<=M-J,

s_j=sin^2(pi j/M), S=sum_{j=J}^{M-J-1}s_j,
H0=alpha n/[(1-eta)S], h_j=floor(H0 s_j),
h0=h_J=h_{M-J}, n'=n-m-2h0-1.

Choose positive integer ell_j, J<=j<M-J, satisfying

sum ell_j=n', ell_j=(n'/S)s_j+O(1),

by flooring and distributing the bounded rounding residual, as in the audited construction. Put g_j=h_{j+1}-h_j. Uniformly,

h_j asymp (n/M)s_j,
ell_j asymp (n/M)s_j,
min h_j, min ell_j asymp L J^2 asymp L^7,
|g_j|<=C sqrt(ell_j L),
alpha ell_j <=(1-4/L)h_j+O(1).

The last bound holds because n'/n<1 and replacing H0 s_j by its floor changes only O(1). All implicit constants here and below are independent of n and j.

For each j choose integer deviations

|u_j|<=w_j=floor(ell_j/L),
|v_j|<=b_j=floor(sqrt(ell_j)),

and impose separately sum u_j=0 and sum v_j=0. The actual kernel arguments are ell_j+u_j and d_j=g_j+v_j.

## 2. A large set of legal balanced increment bridges

First take independent V_j uniform on [-b_j,b_j] intersect Z. The centered integer interval convolutions are symmetric and unimodal, so

P(sum V_j=0)>=1/(2sum b_j+1)>=1/(2n+1).               (1)

For an interior boundary k, let E_k=sum_{j=J}^{k-1}V_j. Define the symmetric good event G by

|E_k|<=h_k/L for every J<=k<=M-J.                    (2)

We claim P(G | sum V_j=0)>=1/2 for all sufficiently large n. In fact the failure probability is at most exp(-cL^2).

For J<=k<=M/2, sine estimates give

sum_{j=J}^{k-1} b_j^2 <=C(n/M^3)k^3<=C L k^3,
max_{J<=j<k} b_j <=C sqrt(L)k,
h_k/L >=c k^2.

Bernstein's inequality for bounded independent centered variables therefore gives

P(|E_k|>h_k/L)
 <=2 exp[-c k^4/(Lk^3+sqrt(L)k^3)]
 <=2 exp(-c k/L)
 <=2 exp(-c L^2).                                  (3)

For k>M/2 use the complementary suffix, which equals -E_k when sum V_j=0. Its corresponding unconditional Bernstein estimate has the same bound, with M-k in place of k. Dividing these unconditional bounds by (1) and taking a union bound over at most M boundaries yields

P(G^c | sum V_j=0)
 <= C nM exp(-c L^2) <=exp(-c' L^2).                (4)

At the two endpoints E=0 automatically. This proves the claim. The argument never asserts independence after conditioning.

Because G is preserved by the simultaneous sign reversal V_j -> -V_j, the uniform measure on good balanced increment vectors satisfies

E[V_j]=0, E[V_j^2]<=b_j^2<=ell_j.                    (5)

Independently, choose the length vector uniformly among the balanced vectors in the u-boxes. This distribution also has E[U_j]=0 and |U_j|<=ell_j/L. The length vector and the good balanced increment vector are independent.

Every resulting walk is legal. Its actual starting height in block j is h_j+E_j>=h_j-h_j/L, whereas, throughout the shifted q-window of the audited local kernel estimate,

q<=alpha(ell_j+u_j)+C sqrt(ell_j L)
 <=(1-4/L)(1+1/L)h_j+O(1)+C sqrt(ell_j L)
 <=h_j-2h_j/L

for all sufficiently large n. The final inequality uses h_j>=cL^7, so sqrt(ell_j L)=o(h_j/L). Therefore q<=h_j+E_j. Every intermediate macro-boundary height is positive. Also |d_j|<=C sqrt((ell_j+u_j)L), uniformly, as required by the kernel estimate.

The balanced rectangle set R thus has cardinality

|R| >= [prod_j(2w_j+1)(2b_j+1)]/[2(2n+1)^2].        (6)

All terms counted are admissible and have the exact prescribed total degree.

## 3. Jensen cancels the large linear energy variations

The audited local kernel bound, summed over its legal shifted q-window, supplies at least

c (ell_j+u_j)^(-2)
 exp[-(g_j+v_j)^2/(2v(ell_j+u_j))-epsilon_n]

per block after the critical tilts, with epsilon_n=o(1) uniformly. Fixed multiplicative constants and the leading x factors cost O(M) in the logarithm.

Let expectation be the product of the two uniform balanced-vector measures just constructed. Each actual rectangle choice has equal probability. Define

X=sum_j [(g_j+V_j)^2/(2v(ell_j+U_j))+2log(ell_j+U_j)].

Independence of the two complete vectors, together with E[U_j]=E[V_j]=0, gives

E[(g_j+V_j)^2/(ell_j+U_j)]
 =(g_j^2+E[V_j^2]) E[1/(ell_j+U_j)].                 (7)

Using the exact identity 1/(1+x)=1-x+x^2/(1+x),

E[1/(ell_j+U_j)]
 <=(1/ell_j)(1+C/L^2).                              (8)

Consequently

E sum_j (g_j+V_j)^2/(ell_j+U_j)
 <=sum_j g_j^2/ell_j + O(M)
   +O(L^(-2) sum_j g_j^2/ell_j)
 <=sum_j g_j^2/ell_j+O(M),                          (9)

because the deterministic sum is O(ML). Concavity gives

E log(ell_j+U_j)<=log ell_j.                         (10)

Jensen's inequality in the favorable direction is

sum_{R} exp(-X)=|R| E exp(-X)>=|R| exp(-E X).         (11)

Thus variation of increments and lengths costs only O(M); it does not cost O(M sqrt L), and no asymmetric restriction has spoiled the centered cancellation.

Combining (6), (9)-(11), the seed construction from the audited proof, and

log(2w_j+1)>=log ell_j-log L+O(1),
log(2b_j+1)>=0.5log ell_j+O(1),

we obtain

D_n<=sum_j g_j^2/(2v ell_j)
     +0.5sum_j log ell_j + m log L
     +O(M+L+h0).                                   (12)

The seed from 1 to h0 has degree 2h0-1, the final descent has degree 1, and the initial letter has degree 1. The m large-block leading x factors and sum ell_j=n' make the total degree exactly n. Seed tilts cancel because the entire walk returns to 1; their finite multiplicities and critical degree cost O(h0)=O(L^7)=o(M).

## 4. Deterministic sums with O(M), rather than relative-o(1), precision

We have S=M/2+O(J^3/M^2+1) and n'=n-O(M+L^7). Removing the endpoints changes the relevant trigonometric sums by at most logarithmic-polynomial amounts after their physical scalings.

For the kinetic term one has

sum_j (s_{j+1}-s_j)^2/s_j
 =2pi^2/M+O((J+log M)/M^2).                         (13)

For example, put delta=pi/M and expand exactly

(s_{j+1}-s_j)/sqrt(s_j)
 =sin(delta)[2cos(pi j/M)cos(delta)
            +(cos(2pi j/M)/sin(pi j/M))sin(delta)].

The main square sums to 2pi^2/M+O(J/M^2). The cross term is bounded by C(log M)/M^2 using sum 1/sin(pi j/M)=O(M log M). The last square is O(1/(M^2 J)), using sum_{j=J}^{M-J}1/sin^2(pi j/M)=O(M^2/J).

Before integer rounding, the kinetic sum equals H0^2 S/n' times the left side of (13). The factors n/n'=1+o(1/L) and (1-4/L)^(-2)=1+O(1/L) give

sum_j g_j^2/ell_j
 =4pi^2 alpha^2 n/M^2+O(M).                         (14)

Here the trigonometric error costs O((J+L)L)=O(L^4)=o(M). Height-rounding error costs at most C sum_j(|g_j|/ell_j+1/ell_j)=O(L), and length-rounding error is bounded by C sum_j g_j^2/ell_j^2=O(ML/L^7)=o(M). These estimates also verify (9)'s deterministic O(ML) bound.

Finally the exact sine product

prod_{j=1}^{M-1}sin(pi j/M)=M/2^(M-1)

gives

sum_{j=J}^{M-J-1}log s_j=-2M log 2+O(J log M+log M).

Rounding changes sum log ell_j by O(sum 1/ell_j)=o(1). Hence

0.5sum_j log ell_j=(M/2)log(n/M)+O(M).               (15)

Replacing m by M in m log L costs O(J log L)=o(M). Inserting (14)-(15) into (12) proves (B), and then (T).

## Scope

The coefficient 7/3 is not taken from a numerical fit: it arises as twice the per-block loglog coefficient 7/6. Its two sources are (1/6)loglog n from the optimal block scale n/M and loglog n from the usable length-window width ell/log n. The proof establishes it only in a rigorous upper bound on D_n. A matching lower bound requires a quantitatively sharp global calibration; the leading audited calibration's sequential fixed-parameter limits do not establish that refinement.
