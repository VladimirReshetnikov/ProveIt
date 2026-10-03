# Independent leading-amplitude verdict

Date: 2026-10-02. Reviewed candidate SHA-256: `f6390a57af247219c50cf67b276a412001018e5985bc0880f726632cc4d2a965` (`amplitude-proof-candidate.md`, snapshot read at 04:44 UTC).

## Verdict and exact scope

The leading relaxed-ternary amplitude argument is valid after making the ordinary analytic estimates explicit as below and in `singular-airy-audit.md`. I found no remaining fatal gap in Claims S and R or the tracking argument. This is an independent analytic audit, not a conclusion drawn from the numerical scripts. The theorem certified by this review is existence of a finite positive constant C_R in

R_n ∼ C_R (n!)² (27/4)^n exp(3·3^(1/3) a_1 n^(1/3)) n^(5/3),

for the exact relaxed-tree recurrence initialized by d_(0,0)=1 and the exact conversion R_n=(2n)!d_(3n,0)/16^n. The proof also yields a relative error O(n^−1/6), without claiming that this is sharp.

This verdict does not certify an all-orders expansion, any explicit value or convergent numerical evaluation of C_R, a compacted-tree amplitude, or a DFA/relaxed ratio limit. Those are genuinely separate assertions. Start the profiles and tracking at an arbitrary sufficiently large fixed I; their undefined small-i cutoff conventions are then irrelevant and only alter the finite scalar constant.

## 1. Forward expansion and time dilation

Write ε=i^−1/3, x=ε(j+1), and H_ε=f+εg. On its effective support,

U_i(j)=2−3xε²+9ε³+O(ε⁴(1+x²)).

The previous-time argument at an input shifted by d∈{−1,2} is

ε_(i−1)(j+1+d)=x+dε+(x/3)ε³+O(ε⁴(1+x)).

The two critical shifts have weights 2,1, first moment zero, second Taylor coefficient 3, and third Taylor coefficient 1. Thus

T_i F_(i−1)=3f+3εg+3ε²(f″−xf)
 +ε³[f‴+4xf′+9f+3(g″−xg)]+O(ε⁴ W(x)),

where W can be taken to be an integrable polynomially weighted Airy envelope, with integrable square independent of i. In particular, the extra time dilation contributes xf′, so dropping it would give an incorrect polynomial power.

For p=−5x²/12−a x/6 and g=pf,

3[g″−(x+a)g]=3p″f+6p′f′=−(5/2)f−(5x+a)f′.

Using f‴=f+(x+a)f′ gives the scalar 15f/2, exactly t_i=3(1+aε²+(5/2)ε³). The bottom row is covered by the same Taylor formula because its absent input is at h=0 and f(0)=g(0)=0 exactly. There is no extrapolated negative value to estimate in the forward equation.

Squaring the envelope and summing on the mesh costs O(ε^−1). Since N_i is of order ε^−1/2, the unnormalized residual O(ε⁴N_i) becomes the claimed normalized O(ε⁴).

## 2. Cutoffs

Choose an explicit nonnegative smooth cutoff χ(x/log i), equal to one below 1 and zero above 2. On its support, ε|p(x)|→0, so the profile is nonnegative for large i. Every cutoff mismatch, including adjacent times and shifted arguments, occurs where x is at least a constant times log i. Airy decay there is exp(−c(log i)^(3/2)), multiplied by at most fixed polynomial powers of x and i. Such errors are smaller than any prescribed power of i. Polynomial Airy-envelope estimates, rather than a supremum over the support, avoid unnecessary logarithmic losses in the bulk remainder.

The cutoff support has height O(i^(1/3)log i), far below the finite moving top. Thus top truncation does not add a boundary residual.

## 3. Weighted adjoint, including the bottom

Let T be the critical infinite-phase map, and D=T†−T applied to the common smooth profile on all nonnegative sites. At sites t≥2 put h=t+1, A=ω(t+1)/ω(t), B=ω(t−2)/ω(t). Then

D F(t)=2A F(t+1)+B F(t−2)−2F(t−1)−F(t+2).

Its Taylor moments satisfy

M_0=2A+B−3=O(h^−3),
M_1=2A−2B=O(h^−2),
M_2=2A+4B−6=O(h^−2),

and all needed higher moments are bounded. The geometrically decaying part of ω satisfies these inverse-power bounds too, with enlarged absolute constants. Crucially, exact weighted harmonicity gives D h=0, equivalently h M_0+M_1=0. This must be retained rather than estimating the two weighted shift errors separately.

Let c=f′(0), and R(h)=H_ε(εh)−cεh. For 1≤h≤ε^−1+O(1), analyticity, f(0)=f″(0)=0, and g(x)=O(x²) give

|R|≤Cε³(h³+h²),
|R′|≤Cε³(h²+h),
|R″|≤Cε³(h+1),
|R‴|≤Cε³.

Here the derivatives are with respect to h. The moment bounds therefore give |D R|≤Cε³. At t=0,1, simply use the finitely many exact matrix coefficients and D h=0: every remaining profile value is O(ε³). No nonexistent negative coordinate is used.

For h≥ε^−1, Taylor's theorem and Airy derivative bounds give |D H_ε(εh)|≤Cε³W(εh), again with square-integrable polynomial Airy envelope. Combining regions yields ||D F_i||_ω=O(ε³N_i).

The inhomogeneous adjoint up coefficient obeys

v_i(t+1)=3xε²+O(ε³(1+x²)),

and its ω ratio and shifted profile replace its leading term only by O(ε³W). Consequently T_i†F_i=3(1+aε²)F_i+O(ε³N_i). The difference F_(i−1)−F_i, the ε³ term in t_i, and the normalization ratio below each have this same admissible O(ε³N_i) size. This proves the normalized backward estimate O(i^−1). Its coefficient need not match the higher-accuracy forward correction.

## 4. Adjacent-phase norms

A bare Riemann-sum estimate N_i²=A/ε+O(1) would not establish N_i/N_(i−1)=1+O(ε³). The stronger phase-uniform expansion is required and is available:

N_(r,ε)²=C_(−1)ε^−1+C_0+C_1ε+O(ε²),

with the first three coefficients independent of r∈{0,1,2}. To see this, put H=(f+εg)² and use

ω(h−1)=1+1/(3h)+[(-1/2)^(h−1)]/(6h).

The ordinary mesh sum of H has phase-dependent endpoint corrections only at absolute order ε² because H(0)=H′(0)=0. The algebraic weight contribution is (ε/3) times the mesh sum of H(x)/x; this quotient is smooth at zero and vanishes there, so its first phase-dependent correction is again absolute order ε². The geometric contribution is O(ε²), since H(εh)=O(ε²h²) for bounded h and the exponential tail is summable. Cutoff errors are negligible.

In particular C_(−1)=(1/3)∫f²>0. Since ε_(i−1)−ε_i=O(ε_i⁴), the phase-independent leading terms change by O(ε²), and the phase remainders also differ by O(ε²). Relative to N_i² of order ε^−1 this is O(ε³). Thus the claimed adjacent normalized ratio follows. At residue zero, f(ε)=cε+O(ε³), εg(ε)=O(ε³), and N_i≍ε^−1/2, so ψ_i(0)≍ε^(3/2)=i^−1/2.

## 5. Tracking and endpoint extraction

Claims S and R give the block inequalities in the candidate. The compressed singular bound is justified in the previous singular audit and does not identify an evolving profile with a frozen eigenvector.

Let A_i=|a_i|, Z_i=||z_i||, and w_i=K i^−1/3. Their inequalities imply

A_i+w_i Z_i ≤ (1+C i^−4/3)(A_(i−1)+w_(i−1)Z_(i−1))

for fixed K sufficiently large: the negative term −Kc i^−1 Z absorbs the O(i^−1)Z coupling, and w_i≤w_(i−1). Thus both A_i and the indicated Lyapunov quantity remain bounded. This does not by itself uniformly bound Z_i, but the stable second recurrence with bounded A_i then yields Z_i=O(i^−2/3) by the stretched-exponential convolution estimate. Substitution gives summable increments of a_i and a_i=a_∞+O(i^−1/3).

At residue-zero endpoints, bounded ω(0) gives |z_i(0)|≤C Z_i. Dividing by ψ_i(0)≍i^−1/2 yields O(i^−1/6). Therefore the normalized endpoint has limit a_∞, with the stated error, even though the global remainder estimate is only in Hilbert norm.

The scalar product satisfies

∏_(m=I+1)^i t_m=C_I 3^i exp(3a i^(1/3)) i^(5/2)(1+O(i^−1/3)).

This follows by expanding log(1+a m^−2/3+(5/2)m^−1); all nonlinear terms are summable, and their tails are O(i^−1/3). The N_i/N_(i−1) factors telescope exactly, leaving F_i(0), of order i^−1/3. Hence d_(3n,0) has the asserted scale n^(13/6), and the factorial conversion decreases the power by 1/2, giving 5/3.

## 6. Positivity and primary-source check

I independently opened https://arxiv.org/html/2404.08415v1 . Theorem 1 states the relaxed-tree Theta estimate for every k≥2; setting k=3 gives the same factorial, exponential, stretched-exponential and n^(5/3) factors as above. Equations (3)–(5) give the candidate's recurrence and R_n=(2n)!d_(3n,0)/16^n. Thus the published lower bound applies to precisely this initialized sequence, not a distinct normalization or DFA sequence.

The tracking argument gives existence and finiteness of its normalized endpoint limit. The positive published lower bound forces that limit to be strictly positive. No positivity of a nonnormal spectral projection, and no unproved ratio limit, is needed.

The only source facts used here are the published recurrence/conversion and its Theta bound. The improvement from Theta to a positive asymptotic amplitude is the additional argument audited here.
