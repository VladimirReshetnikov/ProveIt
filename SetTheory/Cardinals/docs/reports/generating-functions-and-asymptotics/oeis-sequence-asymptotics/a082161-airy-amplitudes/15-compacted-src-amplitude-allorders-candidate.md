# A254789: candidate amplitude and all-orders proof by a small signed-delay perturbation

Prepared 2 October 2026. **Candidate proof awaiting independent audit.** The nonnegative finite-state encoding is independently useful, but the analytic argument below does not require a new nonselfadjoint spectral theorem. It treats the exact signed recurrence as a small bounded delay of the relaxed Jacobi evolution. All claims must remain provisional until its estimates and formal algebra have been audited.

## 1. Statement and known input

Let c_n=c_(n,n), with c_(n,0)=1, c_(n,m)=0 for m>n, and

\[
c_{n,m}=c_{n,m-1}+(m+1)c_{n-1,m}-(m-1)c_{n-2,m-1}.
\]

Write z=-2.338107410459767... for the largest real Airy zero, a=2^(-1/3)z, and F(x)=Ai(z+2^(1/3)x). Proposed theorem: a constant gamma_c>0 exists such that, for every finite M,

\[
c_n=\gamma_c n!4^n e^{3zn^{1/3}}n^{3/4}
\left(1+\sum_{k=1}^M c_k n^{-k/3}+O_M(n^{-(M+1)/3})\right).
\tag{1}
\]

All c_k lie in Q[z]. This is a Poincare expansion, not a transseries or a canonical continuous interpolation. No numerical enclosure or elementary evaluation of gamma_c is asserted.

Primary source: Elvey Price–Fang–Wallner, *Compacted binary trees admit a stretched exponential*, https://arxiv.org/pdf/1908.11181, Proposition 2.11, Definition 2.12, Theorem 1.1 and Section 3.4. The source proves the theta estimate in (1), without an amplitude limit. Its fitted gamma_c is approximately 173.12670485. The present argument uses the established positive lower bound only at the final positivity step. It also uses the elementary domination c_(n,m) <= r_(n,m) by relaxed counts, immediate from the H-decorated path interpretation.

## 2. Relaxed Jacobi input, stated precisely

The following ingredients are proved independently for the relaxed recurrence in the neighboring relaxed-DAG proof. They concern explicitly defined matrices, not the asymptotic conclusion for relaxed counts, so there is no assumption that a relaxed amplitude theorem automatically extends to compacted counts.

For physical time N and height j, define

\[
D_N(j)^2=\frac{\Gamma(N+2)\Gamma(N+1)}{\Gamma(N-j+2)\Gamma(N+j+1)},\quad D_N(0)=1.
\]

Let S_N be the symmetric Jacobi matrix on j=0,...,N+1 with edge b_(N,j)=sqrt((N-j+2)/(N+j)) for j=1,...,N+1, zero-padded to l2(N_0). Let Q_N(j)=sqrt(1-j(j-1)/(N(N+1))) on that support and zero elsewhere. Let lambda_N be the largest eigenvalue and psi_N its positive unit vector. On occupied parity N set g_N=sqrt(2) E_(N mod 2) psi_N; on opposite parity set h_N=sqrt(2) E_((N-1) mod 2) psi_N. Define

\[
P_N=\prod_{i=1}^N\lambda_i,\qquad M_N=S_NQ_N/\lambda_N.
\]

The complete proofs of these shared lemmas are included in `shared-jacobi-lemmas.md`, copied from the approved source and pinned there by SHA-256. The needed estimates, for large N, are

\[
\begin{split}
&\|M_N\|\le1,\quad
\|\Pi_N M_N y\|\le(1-cN^{-2/3})\|y\|,\\
&\|M_Ng_{N-1}-g_N\|=O(N^{-1}),\\
&t_N:=\langle g_N,M_Ng_{N-1}\rangle=1+O(N^{-4/3}),\\
&\|M_N^*g_N-g_{N-1}\|=O(N^{-1}),\\
&\lambda_N=2+2aN^{-2/3}+3N^{-1}+O(N^{-4/3}),\\
&P_N=\kappa 2^N e^{3aN^{1/3}}N^{3/2}(1+O(N^{-1/3})),\quad\kappa>0.
\end{split}\tag{2}
\]

Here Pi_N is projection perpendicular to g_N on occupied parity, and y is on the preceding parity. The singular-value statement removes the negative top eigenvalue by parity restriction. In particular it is not a claim about an ordinary second spectral radius.

For clarity, a sufficient quantitative Airy input is that psi_N differs in l2 by O(N^(-4/3)) from the normalization of cutoff samples of

\[
F(x)+N^{-2/3}\left[\frac{2(-a+2x)}{15}F(x)+\frac{x(2a+x)}{15}F'(x)\right]
+N^{-1}\frac{F(x)-xF'(x)}3,\quad x=(j+1)N^{-1/3},
\tag{3}
\]

with cutoff chi(j/N^(1/2)). The normalized cutoff samples have time derivative O(N^(-1)) in l2 and one-site shift difference O(N^(-1/3)). Their polynomial moments on the Airy scale are bounded. These facts prove all profile comparisons below. The coarse Airy limit, gap, residual calculation and contraction behind (2)–(3) are in Sections 2–5 of the independently audited relaxed proof, and can be copied as shared lemmas into a standalone article.

## 3. Exact compacted gauge recurrence and a global delay bound

Set e_(N,j)=c_((N+j)/2,(N-j)/2)/(((N+j)/2)!) on the physical support, and zero otherwise; v_N(j)=e_(N,j)/D_N(j). For N sufficiently large, the exact recurrence is

\[
v_N=S_NQ_Nv_{N-1}-L_Nv_{N-3},\quad
(L_N f)(j)=\ell_{N,j}f(j-1),
\tag{4}
\]

where j>=1 and the coefficient is used only for valid input support 0<=j-1<=N-3,

\[
\ell_{N,j}=\frac{2(N-j-2)}{(N+j)(N+j-2)}\frac{D_{N-3}(j-1)}{D_N(j)}.
\tag{5}
\]

The coefficient vanishes outside this support. At j=0 the entire delayed term is zero. At j=N-2 its coefficient is zero; thus it is nonnegative on its physical support. This convention also handles the upper boundary, where the formal rational expression by itself need not describe the recurrence.

The factorial identity

\[
\left(\frac{D_{N-3}(j-1)}{D_N(j)}\right)^2
=\frac{(N-j+1)(N-j)(N+j)(N+j-1)(N+j-2)(N+j-3)}{(N+1)N^2(N-1)^2(N-2)}
\tag{6}
\]

proves that the ratio is uniformly bounded for N>=6 and 1<=j<=N-2. The rational factor in (5) is O(1/N) uniformly there. Consequently

\[
\|L_N\|\le C/N.\tag{7}
\]

This is a global operator estimate; it is not restricted to the Airy window.

On j<=2N^(1/2), expansion of (5)–(6) gives

\[
\ell_{N,j}=2/N+O((j+1)/N^2).\tag{8}
\]

Let U be the unilateral upward shift, (Uf)(0)=0 and (Uf)(j)=f(j-1). Equations (3), (7), (8), and Airy moment bounds give

\[
\|L_Ng_{N-3}-(2/N)Ug_{N-3}\|=O(N^{-5/3}),\quad
\|Ug_{N-3}-g_N\|=O(N^{-1/3}).\tag{9}
\]

For the first estimate apply (8) to the cutoff samples, whose typical j is O(N^(1/3)), and apply (7) to their O(N^(-4/3)) approximation errors. The cutoff tails are exponentially small. The second estimate follows from the sample shift and O(N^(-1)) time change in (3). The parity of Ug_(N-3) equals that of g_N, as required.

## 4. Remove the nonsummable scalar drift

For N>=1 set R_N=P_N N^(-1/4), and u_N=v_N/R_N. Beginning the recurrence at any fixed large N avoids irrelevant small-time conventions. Then

\[
u_N=\eta_N M_Nu_{N-1}-B_Nu_{N-3},\quad
\eta_N=(N/(N-1))^{1/4},\quad B_N=(R_{N-3}/R_N)L_N.
\tag{10}
\]

Here

\[
\begin{split}
&\eta_N=1+(4N)^{-1}+O(N^{-2}),\quad\|B_N\|=O(N^{-1}),\\
&\|B_Ng_{N-3}-(4N)^{-1}g_N\|=O(N^{-4/3}),\\
&b_N:=\langle g_N,B_Ng_{N-3}\rangle=(4N)^{-1}+O(N^{-4/3}),\\
&\eta_Nt_N-1-b_N=O(N^{-4/3}).
\end{split}\tag{11}
\]

Indeed R_(N-3)/R_N=1/8+O(N^(-2/3)), so (9) gives the second line. This is the exact cancellation responsible for the additional N^(-1/4) factor.

## 5. A finite-memory tracking lemma

We use two elementary estimates; neither assumes positivity of the delayed evolution.

(a) If nonnegative x_N satisfy, eventually,

\[
x_N\le(1-cN^{-2/3})x_{N-1}+CN^{-1}x_{N-3}+CN^{-r},\tag{12}
\]

then x_N=O(N^(2/3-r)). To prove this, take the barrier K N^(2/3-r). The difference of consecutive power values is O(K N^(2/3-r-1)); the delayed term is of the same smaller order; the contraction supplies cK N^(-r). For sufficiently large starting N and then sufficiently large K, induction gives the claim. A sum of power forcings gives the sum of the corresponding bounds.

(b) If delta_N is polynomially bounded and

\[
|\delta_N|\le CN^{-1}(|\delta_{N-1}|+|\delta_{N-2}|)+O(N^{-r}),\tag{13}
\]

then delta_N=O(N^(-r)). Repeated substitution a fixed number of times lowers any initial polynomial exponent by one per substitution until the O(N^(-r)) forcing dominates. Alternatively the barrier K N^(-r) gives a direct eventual induction. Both arguments use only that C/N tends to zero.

## 6. Initial domination makes the scalar amplitude converge

The compacted paths are a subset of relaxed decorated paths. In the common positive diagonal gauge, compacted v_N is bounded entrywise by relaxed v_N. The relaxed normalized evolution has norm at most one, so

\[
\|u_N\|\le N^{1/4}.\tag{14}
\]

Write u_N=A_Ng_N+w_N, with w_N perpendicular to g_N. From (2), (10), (11), and (14),

\[
\|w_N\|\le(1-c'N^{-2/3})\|w_{N-1}\|+O(N^{-3/4}),
\]

for large N. The standard geometric-sum estimate for the variable gap, or the power barrier in (12), yields

\[
\|w_N\|=O(N^{-1/12}).\tag{15}
\]

In this first estimate the delayed whole vector can simply be bounded by (14); no cancellation is used for transverse control.

Projecting (10) gives

\[
A_N=\eta_Nt_N A_{N-1}-b_N A_{N-3}+\xi_N,
\quad |\xi_N|\le CN^{-1}(\|w_{N-1}\|+\|w_{N-3}\|).
\tag{16}
\]

The first cross term uses \|M_N^*g_N-g_(N-1)\|=O(N^(-1)) and orthogonality; the second only uses \|B_N\|=O(N^(-1)). Set delta_N=A_N-A_(N-1). Then

\[
\delta_N=b_N(\delta_{N-1}+\delta_{N-2})
+(\eta_Nt_N-1-b_N)A_{N-1}+\xi_N.
\tag{17}
\]

Equations (11), (14), (15) give (13) with r=13/12. Thus delta_N=O(N^(-13/12)), a summable sequence. A_N has a finite limit A_infinity. Since e_N and g_N are nonnegative, A_infinity>=0.

Now A_N is bounded, while w_N tends to zero by (15), so u_N is bounded. Repeating the transverse estimate gives w_N=O(N^(-1/3)); (17) and (13) then give delta_N=O(N^(-4/3)). Therefore

\[
A_N=A_\infty+O(N^{-1/3}),\quad \|w_N\|=O(N^{-1/3}),\quad \|u_N\|=O(1).
\tag{18}
\]

No endpoint conclusion is yet drawn from (18), because the ground endpoint itself is of order N^(-1/2).

## 7. Formal compacted profiles exist at every order

Use epsilon=N^(-1/3), x=(j+1)epsilon, and seek

\[
Z_{N,j}=H_N\Phi_N(x),\quad \Phi_N(x)=\sum_{k=0}^K\epsilon^kG_k(x),\quad G_0=F,
\]

with G_k(0)=G_k'(0)=0 for k>=1 and

\[
H_N/H_{N-1}\sim2\left(1+\sum_{m\ge2}s_m\epsilon^m\right).
\tag{19}
\]

The two one-step arguments are (x±epsilon)(1-epsilon^3)^(-1/3); the delayed argument is (x-epsilon)(1-3epsilon^3)^(-1/3). The horizontal coefficient and delayed coefficient are respectively

\[
A(x,\epsilon)=\frac{1-x\epsilon^2+3\epsilon^3}{1+x\epsilon^2-\epsilon^3},\quad
\beta(x,\epsilon)=\frac{2\epsilon^3(1-x\epsilon^2-\epsilon^3)}{(1+x\epsilon^2-\epsilon^3)(1+x\epsilon^2-3\epsilon^3)}.
\tag{20}
\]

After dividing the original recurrence by H_(N-1), the delayed term is multiplied by H_(N-3)/H_(N-1)=1/[(H_(N-1)/H_(N-2))(H_(N-2)/H_(N-3))]. The latter is a formal series with leading constant 1/4. Since beta starts at degree three, it does not change the leading Airy operator or how the new unknown profile and scalar enter at each order. At degree m the equation has the form

\[
\mathcal L G_{m-2}-2s_m F+R_m(x)F+S_m(x)F'=0,
\quad \mathcal L=\partial_x^2-2(x+a),
\tag{21}
\]

where R_m,S_m are already determined polynomials over Q[a]. In particular s_2=a.

For G=PF+QF',

\[
\mathcal L G=(P''+4(x+a)Q'+2Q)F+(2P'+Q'')F'.
\]

Eliminating P reduces the polynomial equation to

\[
-\tfrac12Q'''+4(x+a)Q'+2Q=R-\tfrac12S'.\tag{22}
\]

On degree <=d polynomials this has triangular nonzero diagonal 4j+2, so it is invertible over Q[a]. Changing the new scalar s_m adds s_m to the constant term of Q. It can therefore be chosen uniquely so Q(0)=0. The integration constant of P then enforces P(0)+Q'(0)=0. This proves existence and uniqueness of the entire formal recursion.

The finite exact symbolic calculation in formal_compacted.py gives s_3=13/12. Thus the genuine finite logarithmic amplitude can be chosen as

\[
\log H_N=N\log2+3aN^{1/3}+\frac{13}{12}\log N+
\sum_{k=1}^J h_kN^{-k/3}.\tag{23}
\]

At degree k+3 in the one-step ratio the coefficient of new h_k is -k/3, so any finite number of scalar ratio coefficients can be matched uniquely. The leading multiplicative constant in H_N is fixed to one for every truncation.

## 8. Uniform norm residuals, with no endpoint smoothing assumption

Fix p>1. Choose sufficiently many terms in (19) and (23), use cutoff chi(j/N^(1/2)), restrict to occupied parity, and define

\[
z_N=D_N^{-1}Z_N/R_N.
\]

Then

\[
\|z_N\|=O(1),\quad
r_N:=z_N-\eta_NM_Nz_{N-1}+B_Nz_{N-3}=O(N^{-p})\quad\text{in }\ell^2,
\tag{24}
\]

and

\[
\langle g_N,z_N\rangle\longrightarrow q_0=\kappa^{-1}\sqrt{I/2}>0,
\quad I=\int_0^\infty F(x)^2dx.
\tag{25}
\]

Here are the global justifications. On j<=2N^(1/2), the factorial product for D_N gives D_N^(-1)<=C uniformly. Taylor remainders in (20), the time dilations and the finite ratios are bounded by an arbitrarily prescribed power of N^(-1/3) times a fixed polynomial–Airy envelope. Cutoff derivative errors are exponentially small in N^(1/4), and multiplication by the bounded gauge does not change that. The one- and three-step shifted cutoff supports differ only in the same exponentially small region. At the left boundary all fictitious samples vanish exactly because every G_k(0)=0. At the upper moving boundary the cutoff is identically zero for large N. Finally H_N/R_N~kappa^(-1)N^(-1/6), while a parity-restricted Airy sample has norm ~N^(1/6)sqrt(I/2). The residual and projection statements follow by summation of these square-integrable envelopes.

## 9. Zero-limit projection bootstrap for the delayed recurrence

Set C=A_infinity/q_0 and E_N=u_N-Cz_N. Its ground projection alpha_N tends to zero by (18), (25). Write E_N=alpha_Ng_N+W_N. The inhomogeneous recurrence is

\[
E_N=\eta_NM_NE_{N-1}-B_NE_{N-3}-Cr_N.
\tag{26}
\]

Exactly as above, for sufficiently large N,

\[
\begin{split}
\|W_N\|&\le(1-cN^{-2/3})\|W_{N-1}\|+CN^{-1}\|W_{N-3}\|\\
&\qquad+CN^{-1}(|\alpha_{N-1}|+|\alpha_{N-3}|)+CN^{-p},\\
|\delta_N|&\le CN^{-1}(|\delta_{N-1}|+|\delta_{N-2}|)
+CN^{-4/3}|\alpha_{N-1}|\\
&\qquad+CN^{-1}(\|W_{N-1}\|+\|W_{N-3}\|)+CN^{-p},
\end{split}\tag{27}
\]

where delta_N=alpha_N-alpha_(N-1). Suppose alpha_N=O(N^(-q)) for q>=0. The finite-memory lemma gives

\[
\|W_N\|=O(N^{-q-1/3}+N^{2/3-p}).\tag{28}
\]

The scalar difference lemma then gives delta_N=O(N^(-q-4/3)+N^(-p)). This is summable. Using alpha_infinity=0 and summing the differences to infinity yields

\[
\alpha_N=O(N^{-q-1/3}+N^{1-p}).\tag{29}
\]

Starting at q=0, which holds because u_N and z_N are bounded, and iterating finitely many times gives

\[
\|E_N\|=O(N^{1-p}).\tag{30}
\]

This proof does not need the delayed evolution itself to be positive or contractive. Positivity was used only for initial domination and the sign of the scalar limit. It does not need a one-step singular gap for a lifted finite-state kernel.

## 10. Endpoint, strict positivity, and the common amplitude

Point evaluation is a bounded functional on l2, so |E_N(0)|<=\|E_N\|=O(N^(1-p)). The leading normalized approximate endpoint is of order N^(-1/2), since H_N/R_N~kappa^(-1)N^(-1/6) and Phi_N(epsilon)~F'(0)epsilon. We may choose p arbitrarily large. Thus (30) gives every requested finite relative algebraic accuracy at the endpoint, at the price of a harmless N^(1/2) loss. No signed-kernel heat bound has been assumed.

If A_infinity were zero, then C=0 and (30), for p>3/2, would imply u_N(0)=o(N^(-1/2)). But the published compacted lower bound, divided by R_(2n), says u_(2n)(0)>=cN^(-1/2) for large even N. This contradiction proves A_infinity>0.

Using F'(0)/sqrt(I)=sqrt(2), conversion N=2n gives

\[
\gamma_c=2^{3/4}CF'(0)=2^{7/4}\kappa A_\infty>0.\tag{31}
\]

All truncations share the same q_0 and the same fixed leading normalization of H_N. Hence C and gamma_c are independent of truncation order. This proves the proposed expansion (1), subject to independent audit of the candidate argument.

## 11. Explicit coefficients and coefficient field

An independent direct linear-system calculation confirms the first logarithmic corrections

\[
\log\frac{c_n}{\gamma_c n!4^n e^{3zn^{1/3}}n^{3/4}}
=\frac{53z^2}{90}n^{-1/3}+\frac{271z}{216}n^{-2/3}
+\left(\frac{393}{1120}-\frac{1304z^3}{42525}\right)n^{-1}+O(n^{-4/3}).
\]

The corresponding relative coefficients are

\[
c_1=53z^2/90,\quad c_2=z(2809z^3+20325)/16200,\quad
c_3=(2084278z^6+43365690z^3+21487275)/61236000.
\]

The scalar ratio coefficients are s_4=29a^2/270, s_5=-11a/324, and s_6=(2054835-140528a^3)/1360800. The first finite logarithmic amplitude coefficients are h_1=53a^2/45, h_2=235a/108, and h_3=-641/1680-5216a^3/42525. The normalized endpoint factor is 1+(a/3)epsilon^2+(13/12)epsilon^3+O(epsilon^4).


Every formal coefficient is in Q[a]. To see that conversion to n puts the final coefficients in Q[z], let omega be a primitive cube root of unity. For general a, define phi_a as the unique entire initial-value solution phi_a''=2(x+a)phi_a, phi_a(0)=0, phi_a'(0)=1. At the physical Airy-root parameter it equals F/F'(0); at other a it need not be a decaying Airy solution. Uniqueness of this initial-value problem gives phi_(omega a)(omega x)=omega phi_a(x). The full formal recurrence (19)–(20), including the delayed time dilation and the two previous ratios, is invariant under (a,epsilon,x)->(omega a,omega epsilon,omega x). Uniqueness of (21)–(22) therefore gives s_m(omega a)=omega^(-m)s_m(a). The finite-logarithm coefficients and normalized endpoint coefficients inherit the same grading: every monomial a^r in the order-k correction has r+k divisible by three. Consequently a^r N^(-k/3)=2^(-(r+k)/3)z^r n^(-k/3), with a rational power of two. Thus all c_k lie in Q[z].

## 12. Audit targets and limits

Required checks: the exact global gauge identity (6); the physical upper-support convention; the cancellation (11); the initial N^(1/4) domination; finite-memory power barriers for arbitrary exponents; the order-by-order delayed formal recursion; the global residual after cutoff and changing parity; and the zero-limit tail direction in (29).

No existence claim should be released without an independent analytic audit. Exact finite-state counts and high-precision recurrence fits are supporting checks only. Current bounded searches of primary literature and ProveIt found no prior amplitude resolution, which is not an exhaustive novelty guarantee.
