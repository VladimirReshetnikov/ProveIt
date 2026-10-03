# Matching stretched-exponential order, including the logarithm

Research proof draft, 1 October 2026. This is a refinement of the frozen operator/lower-bound notes and of upper_scale_proof.md. It requires their independent audit and a separate audit of the refinements below.

## Proposed strengthened theorem

There exist constants c,C>0 such that, for all sufficiently large n,

mu^n exp[-C n^(1/3)(log n)^(2/3)]
 <= a_n <=
C mu^n exp[-c n^(1/3)(log n)^(2/3)].                             (R)

Equivalently,

n log mu-log a_n = Theta(n^(1/3)(log n)^(2/3)).

This determines the order of the logarithmic deficit, not a leading constant, asymptotic equivalent, or transseries. It in particular excludes both a pure negative n^(3/8) stretch and a pure negative constant-times-n^(1/3) stretch.

All notation is as in the preceding notes.

## 1. Critical fixed-tilt jump tail

Fix x=rho and t=t_*. The discriminant of the jump quadratic, as a polynomial in z, has leading and constant coefficients

d_2=(b+rho t_*)^2,
d_0=(b^2-rho^2 t_*)^2.

One root is z_*. The other is

z_2=d_0/(d_2 z_*)=0.8817230195... .

The exact field identities and rational interval certificate show

0<z_*<z_2<1,
s=b^2-rho^2 t_*>0.

Thus

Delta(z)=s^2(1-z/z_*)(1-z/z_2),

and the formal root with Q(0)=0 is

Q(rho;z,t_*)=
 [s-(b-rho t_*)z-s sqrt(1-z/z_*)sqrt(1-z/z_2)]
 /[2rho t_*(1-z)].                                               (20)

The nonsingular part is analytic for |z|<1, while the multiplier of sqrt(1-z/z_*) is analytic for |z|<z_2. Consequently

0<=Q_q(rho,t_*)z_*^q<=C_0 q^(-3/2),  q>=1.                       (21)

An elementary proof of the bound, avoiding a transfer theorem, is to use the exact coefficients of sqrt(1-w), bounded by C(m+1)^(-3/2), and convolve them with an analytic multiplier whose coefficients are O(R^(-m)) for fixed z_*<R<z_2. Split the convolution at m=q/2. The analytic nonsingular part is exponentially smaller. This proves (21) uniformly after enlarging C_0 for finitely many q.

## 2. Improve the finite-height radius shift

Keep the fixed-t_* derivative bound (16) from upper_scale_proof.md. Put

delta_H=epsilon log(H+1)/(H+1),
x_H=rho+delta_H.

For sufficiently small fixed epsilon>0 and large H, this lies in the same fixed analytic x interval. Let A_q=Q_q(rho,t_*)z_*^q. The weighted row sum of the height-H cutoff is bounded by

c(x_H)t_* exp(C_1 delta_H)
 *sum_{q<=H} A_q exp(C_1 q delta_H).

The undisturbed infinite sum has mass m_*<1. By (21), the extra tail satisfies

sum_{q<=H} A_q [exp(C_1 q delta_H)-1] ->0.                         (22)

To verify (22), split at q=1/delta_H. The lower part is O(sqrt(delta_H)), using exp(C_1 q delta_H)-1=O(q delta_H) there. The upper part is at most

C exp(C_1 H delta_H) sqrt(delta_H)
 =O(H^(C_1 epsilon-1/2) sqrt(log H)),

which tends to zero if C_1 epsilon<1/2. The harmless prefactor tends to its critical value. Therefore the cutoff row mass stays uniformly below 1, and its generating function at x_H stays uniformly bounded as before. It follows that

a_n^[<=H] <= C mu^n exp[-c n log(H+1)/(H+1)].                    (23)

## 3. Optimize with the unchanged height-hit bound

The first-hit bound (19) remains

a_n^[>H] <= C mu^n exp(-c H^2/n)

for H=o(n). Take

H=floor(n^(2/3)(log n)^(1/3)).

Both exponents in (23) and the first-hit bound are then bounded below by a positive constant times n^(1/3)(log n)^(2/3). Their sum proves the upper half of (R).

## 4. A logarithmically accelerated staircase

The block entropy argument also has the following immediate uniform variant of (14). For fixed D, if

|q-alpha ell|<=2, |k-kappa ell|<=1,
|r-q|<=D sqrt(ell log ell),

then for all large ell,

B(ell,q,r)>=c ell^(-C_D) mu^ell z_*^(r-q).                        (24)

Indeed, Taylor's quadratic remainder is now O_D(log ell), while all normalized factorial arguments remain in the same positive compact set. Uniform Stirling therefore yields (24).

Replace the square heights in the all-length lower construction by

h_j=floor(j^2 log j),
q_j=floor(h_j/2),
ell_j=floor(q_j/alpha),
k_j=nearest integer to kappa ell_j,

for all j above a sufficiently large fixed J. For an ascent choose

r_j^+=q_j-1+(h_{j+1}-h_j),

and for a descent choose

r_j^-=q_j-1+(h_{j-1}-h_j).

These formulas preserve the exact height increment 1-q+r. Since

h_{j+1}-h_j=O(j log j),
ell_j=Theta(j^2 log j),

we have |r-q|=O(sqrt(ell_j log ell_j)), and (24) applies. Every q_j is at most its starting height; all endpoints are positive. The fixed seeds now go from 1 to h_J and back, costing fixed length 2h_J.

The length of the ascent to h_K and descent back, including the leading 0 and seeds, is

L_K=2h_J+1
 +sum_{j=J}^{K-1}(ell_j+1)+sum_{j=J+1}^{K}(ell_j+1)
 =K^3 log K/(3alpha)+O(K^3).                                    (25)

The residual gap obeys

L_{K+1}-L_K=ell_K+ell_{K+1}+2=Theta(h_K).

The same two self-loop repair covers every large integer length exactly. Specifically, for residual R less than this gap, split R into two almost-equal large loop lengths if it is not bounded. Each loop with ell=m-1, q nearest alpha ell, r=q-1 has

q<=alpha R/2+O(1)
 <=(h_K+h_{K+1})/4+O(1)<h_K

for large K, so its boundary constraint remains valid. Bounded residuals are absorbed by the terminating 1/(1-x).

The up-and-down part has zero total height increment, hence sum(r-q) equals minus the number of its blocks. Its tilt factors still cancel up to a constant factor per block. There are O(K) blocks and each ell<=O(K^2 log K). Multiplying (24) therefore gives

log a_n >= n log mu-O(K log K).

From (25), K=Theta((n/log n)^(1/3)), so

K log K=Theta(n^(1/3)(log n)^(2/3)).

This proves the lower half of (R). No conjectured local limit theorem, spectral asymptotic, or numerical fit is used.
