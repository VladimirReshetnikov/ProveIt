# Independent audit: A331120 signed-delay extension

Date: 2 October 2026.

## Verdict and scope

The DFA-specific extension passes this audit, conditional on the quantitative relaxed-Jacobi lemmas already isolated and audited for the compacted-tree argument. The extension needs no new signed-kernel smoothing or spectral theorem. The finite-memory convergence and zero-limit bootstrap apply with stronger initial exponents than in the compacted case. The result is a proposed proof, not a claim of publication or independently established novelty.

The boundary convention is essential: the delayed term at m=1 is **nonzero**, whereas the compacted analogue vanished there. Keep all physical inputs 1 <= j <= N-2. The upper boundary m=0 has no delayed term.

## Published input and normalization

Primary source: Elvey Price–Fang–Wallner, *Asymptotics of Minimal Deterministic Finite Automata Recognizing a Finite Binary Language*, AofA 2020, DOI https://doi.org/10.4230/LIPIcs.AofA.2020.11 . PDF: https://drops.dagstuhl.de/storage/00lipics/lipics-vol159-aofa2020/LIPIcs.AofA.2020.11/LIPIcs.AofA.2020.11.pdf .

Proposition 5 gives the stated recurrence, including b(n,0)=1 for n>=-1, and identifies b(n,n) with the counted automata and OEIS A331120. Theorem 1 gives the two-sided Theta estimate at scale n!8^n exp(3z n^(1/3)) n^(7/8), with z the largest negative Airy zero. Only its positive lower bound is needed for strict positivity below.

Use c(n,m)=b(n,m)/2^m for **every** m>=0. Then

    c(n,m)=c(n,m-1)+(m+1)c(n-1,m)-(m/2)c(n-2,m-1).

At m=1 this gives c(n,1)=1/2+2c(n-1,1), including n=1 because c(-1,0)=1 and c(0,1)=0. Thus c(n,1)=2^(n-1)-1/2. At m=0 keep c(n,0)=1 as a boundary value. This verifies the exceptional first strip directly. The paper instead scales by 2^(m-1) for m>=1 while leaving m=0 unchanged; its subsequent displayed normalized recurrence must not be copied across that strip without checking. The present uniform normalization eliminates the mismatch.

## Exact gauge and physical support

Set N=n+m, j=n-m and e(N,j)=c(n,m)/n! on physical nonnegative indices and occupied parity. For N>=6 its exact recurrence is

    e(N,j)=e(N-1,j+1)+(N-j+2)/(N+j)e(N-1,j-1)
            -(N-j)/((N+j)(N+j-2)) e(N-3,j-1).

At j=0, fictitious sources with j=-1 are zero. At j=N the delayed term is omitted, and the surviving one-step term yields e(N,N)=1/N!. At j=N-2 the delay is retained and reproduces the first-strip computation above. Starting at N>=6 avoids any use of a factorial at n=-1; that exceptional initial datum is already absorbed in the initial physical vectors.

With the same positive gauge D_N as the compacted proof, v_N=D_N^(-1)e_N obeys

    v_N=S_N Q_N v_(N-1)-L_N v_(N-3),
    (L_N f)(j)=ell(N,j)f(j-1),
    ell(N,j)=(N-j)/((N+j)(N+j-2)) D_(N-3)(j-1)/D_N(j),

for 1<=j<=N-2 and zero outside valid source support. The unchanged factorial identity is

    [D_(N-3)(j-1)/D_N(j)]^2
      =(N-j+1)(N-j)(N+j)(N+j-1)(N+j-2)(N+j-3)
        /[(N+1)N^2(N-1)^2(N-2)].

It implies a global bound ||L_N||<=C/N, including the m=1 strip. For j<=2sqrt(N),

    ell(N,j)=1/N+O((j+1)/N^2).

The quantitative Airy samples therefore give

    ||L_N g_(N-3)-N^(-1)U g_(N-3)||=O(N^(-5/3)),
    ||U g_(N-3)-g_N||=O(N^(-1/3)).

These are norm estimates with controlled tails, not merely pointwise formal expansions.

## Initial domination

Let r(n,m) be the relaxed recurrence with the same m=0 boundary and no subtraction. Nonnegativity of b is supplied by its counting interpretation. Induction on N, using the nonnegative subtraction coefficient, proves 0<=c(n,m)<=r(n,m). For the exceptional first input, c(1,1)=1/2<=r(1,1)=1; alternatively use the explicit first-strip formulas. The positive gauge preserves the comparison. This proof is safer than asserting a literal subset relation after fractional normalization.

The relaxed norm contraction then gives ||v_N/P_N||<=C. With

    R_N=P_N N^(-1/8), u_N=v_N/R_N,

we obtain ||u_N||=O(N^(1/8)).

## Drift cancellation and existence of a scalar limit

The exact normalized recurrence is

    u_N=eta_N M_N u_(N-1)-B_N u_(N-3),
    eta_N=(N/(N-1))^(1/8), B_N=(R_(N-3)/R_N)L_N.

As R_(N-3)/R_N=1/8+O(N^(-2/3)),

    eta_N=1+1/(8N)+O(N^-2), ||B_N||=O(N^-1),
    B_N g_(N-3)=(1/(8N))g_N+O_l2(N^(-4/3)),
    eta_N t_N-1-b_N=O(N^(-4/3)),

where b_N=<g_N,B_Ng_(N-3)> and t_N=<g_N,M_Ng_(N-1)>.

Write u_N=A_N g_N+w_N with w_N perpendicular to g_N. The initial transverse forcing is O(N^(-7/8)); division by the N^(-2/3) gap gives

    ||w_N||=O(N^(-5/24)).

The scalar increments delta_N=A_N-A_(N-1) satisfy the exact identity

    delta_N=b_N(delta_(N-1)+delta_(N-2))
        +(eta_N t_N-1-b_N)A_(N-1)+xi_N,
    |xi_N|<=C N^-1 (||w_(N-1)||+||w_(N-3)||).

Both forcing terms are O(N^(-29/24)), since 4/3-1/8=29/24 and 1+5/24=29/24. The elementary finite-memory increment lemma gives delta_N=O(N^(-29/24)), which is summable. Hence A_N tends to a finite nonnegative A_infinity. Now u_N is bounded; repeating the estimates yields

    ||w_N||=O(N^(-1/3)), A_N-A_infinity=O(N^(-1/3)).

No conclusion about the endpoint is extracted from this coarse norm bound.

## Formal profiles and arbitrary residual order

With epsilon=N^(-1/3), x=(j+1)epsilon, the one-step rational coefficient stays

    A=(1-x epsilon^2+3epsilon^3)/(1+x epsilon^2-epsilon^3),

and the delay coefficient becomes

    beta=epsilon^3(1-x epsilon^2+epsilon^3)
         /[(1+x epsilon^2-epsilon^3)(1+x epsilon^2-3epsilon^3)].

The delayed argument remains (x-epsilon)(1-3epsilon^3)^(-1/3), and its scalar multiplier is the inverse product of the two previous amplitude ratios. Its leading degree is three, so the same triangular polynomial-Airy recursion applies at all orders. The Airy operator and its invertible polynomial reduction are unchanged. Boundary conditions G_k(0)=G_k'(0)=0 fix every new scalar and profile uniquely.

At degree three, relative to the compacted case the leading delayed forcing changes from -F/2 to -F/4. In the equation containing -2s_3 F this increases s_3 by 1/8. Therefore

    rho=s_3=13/12+1/8=29/24.

Choose any finite logarithmic amplitude

    log H_N=N log 2+3aN^(1/3)+(29/24)log N+sum h_k N^(-k/3),

with leading multiplicative constant one. Since R_N~kappa 2^N exp(3aN^(1/3))N^(11/8), H_N/R_N~kappa^(-1)N^(-1/6), exactly as required for a bounded normalized Airy sample. Cutoff at j/sqrt(N), parity restriction, bounded inverse gauge on the cutoff support, polynomial-Airy envelopes, and vanishing fictitious left samples give a residual O_l2(N^-p) for every prescribed p>1. The nonzero m=1 delay causes no new residual because this moving upper strip is outside the cutoff support for all sufficiently large N.

The projection limit of each such profile is the same q_0=kappa^(-1)sqrt(I/2)>0, where I=int_0^infinity F(x)^2 dx.

## Bootstrap, endpoint and strict positivity

Let C=A_infinity/q_0, and E_N=u_N-Cz_N. Its ground projection alpha_N tends to zero. The same finite-memory inequalities as in the compacted proof give, from alpha_N=O(N^-q),

    ||W_N||=O(N^(-q-1/3)+N^(2/3-p)),
    |alpha_N-alpha_(N-1)|=O(N^(-q-4/3)+N^-p),
    alpha_N=O(N^(-q-1/3)+N^(1-p)).

The last line follows by summing the increments toward the known zero limit. Starting at q=0 and iterating finitely many times gives ||E_N||=O(N^(1-p)). The finite-memory power barriers work for arbitrary real exponents because their gap term dominates the N^-1 delayed term by a factor N^(1/3).

Point evaluation has norm one on l2. Its normalized leading endpoint is of order N^-1/2, so arbitrary p yields every finite relative endpoint order. This is the complete substitute for smoothing; no smoothing theorem is being presumed.

If A_infinity=0, C=0 and the bootstrap gives u_N(0)=O(N^(1-p)). Choosing p>3/2 contradicts Theorem 1's positive lower bound on even N, which is u_(2n)(0)>=c N^-1/2 after division by 2^n n! R_(2n). Therefore A_infinity>0.

Consequently there is a common gamma>0 such that, for every finite M,

    b(n,n)=gamma n!8^n exp(3z n^(1/3)) n^(7/8)
       [1+sum_(k=1)^M d_k n^(-k/3)+O_M(n^(-(M+1)/3))].

The normalization conversion is

    gamma=2^(7/8) C F'(0)=2^(15/8) kappa A_infinity.

All truncations have the same leading H_N normalization and q_0, hence the same gamma. The coefficient-field grading proof carries over unchanged, provided the general complex-parameter Airy function is defined by its normalized initial-value problem rather than by an unjustified decaying-Ai formula. It gives d_k in Q[z].

## Independent coefficient calculation

The independent direct-linear-system script `independent_coefficient_audit.py` was adapted from the independent compacted audit, changing the DFA delay coefficient. It does not import or use `formal_dfa.py`. It completed successfully and its exact results are in `independent-coefficient-audit.json`. They agree with the separate formal calculation:

    s_2=a, s_3=29/24, s_4=29a^2/270,
    s_5=-103a/648,
    s_6=(5341815-562112a^3)/5443200.

The normalized endpoint is 1+(a/3)epsilon^2+(29/24)epsilon^3+O(epsilon^4). The first logarithmic correction coefficients in n are

    53z^2/90,
    623z/432,
    3497/4480-1304z^3/42525.

These are checks on the explicit coefficients; the preceding convergence and residual argument supplies the analytic justification.

## Final proof addendum: renewal and selected inverse

I inspected the final `proof.md` sections on exact positive renewal and the selected smooth inverse. Both pass, with the inverse error interpretation clarified below.

For m>=1, set A(n,m)=b(n,m)-(m+1)b(n-1,m) on n>=m and A(n,m)=0 otherwise. The first row satisfies A(n,1)=1. On the next physical row,

    A(n,m+1)=2b(n,m)-(m+1)b(n-2,m), n>=m+1.

Substitute b(n,m)=sum_(k=0)^(n-m)(m+1)^k A(n-k,m). The resulting run kernel is exactly

    W_m(t)=[2-(m+1)t^2]/[1-(m+1)t],

whose coefficients are 2, 2(m+1), and [2(m+1)^2-(m+1)](m+1)^(k-2) for k>=2. All are positive. The triangular cutoff A(n,m)=0 for n<m must remain part of the definition: at a newly added altitude one discards coefficients below its diagonal, rather than applying an unrestricted row-generating-function product. With that stated cutoff, the renewal system and signed recurrence are algebraically equivalent. An independent exact computation checked all 465 physical entries with 1<=m<=n<=30.

For the inverse, write L=log(8X)=1+w and

    h(X)=3zX^(1/3)+(11/8)log X+log(gamma sqrt(2pi)).

Stirling gives F_M(X)=X log(8X/e)+h(X)+O_M(X^(-1/3)). Let delta=-h(X)/L=O(X^(1/3)/L). Since the first term equals Y, Taylor expansion at X gives residual at X+delta of size O_M(X^(-1/3)); more explicitly the h' delta contribution is O(X^(-1/3)/L), and the base-function quadratic term is O(X^(-1/3)/L^2). Dividing by F_M'~L proves

    x_M(Y)=X-h(X)/L+O_M(X^(-1/3)/log X).

Thus the stated remainder is valid, including M=0. In inverse-index units, the two Newton effects are respectively O(X^(-1/3)/L^2) and O(X^(-1/3)/L^3), below the displayed error.

The all-orders mean-value estimate should be read, and preferably stated explicitly, as

    x_M(log b_n)-n=O_M(n^(-(M+1)/3)/log n).

Indeed F_M(n)-log b_n has the numerator order and F_M' is uniformly comparable with log n in the intervening interval. This is an inverse estimate at the actual discrete sample values. It does not claim that an integer first-crossing function for arbitrary y has a vanishing index error without bracketing or rounding. The proof's separate caveat about discrete thresholds correctly handles that distinction. Recursive Newton reversion produces arbitrary asymptotic accuracy for each chosen smooth model; accuracy relative to b_n remains limited by the retained forward truncation unless M is increased.
