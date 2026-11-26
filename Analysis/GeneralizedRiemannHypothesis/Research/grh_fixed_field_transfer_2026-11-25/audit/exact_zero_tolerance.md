# Exact zero-tolerance torsion selection over a fixed p-adic coefficient field

## Verdict

The proposed threshold is correct for finite packets of integral one-variable polynomials over an arbitrary finite extension K/Q_p. The proof below handles separate witnessing points, cancellation, residue classes, and repeated roots. It also shows sharpness at equality. No Lean compilation or literature-novelty claim is made here.

## Statement

Normalize the valuation v by v(p)=1. Let K/Q_p be finite, with absolute ramification index e, and put s=v_p(e). Fix a finite nonempty set S of positive integers and a real rho>0 such that

    rho >= max_{h in S} r_h,
    N_h=(p-1)p^(h-1),  r_h=1/N_h.

Let g_i in O_K[T], for i in a finite set I, have witnessing points x_i in the algebraic closure (or its completion) satisfying v(x_i)>=rho. Suppose

    t_i=v(g_i(x_i))<infinity,
    sum_i t_i <= B.

The shell h consists of the points z=zeta-1 for primitive p^h-th roots of unity zeta. Call it blocked if for every point z in that shell there is an i with v(g_i(z))>t_i. Equivalently, every z has strictly positive total positive excess sum_i max(0,v(g_i(z))-t_i).

Define

    a_h = p^(-min(s,h-1)),
    C_K(S) = sum_{h in S} a_h.

**Exact threshold theorem.** If every shell in S is blocked, then B>=C_K(S). Conversely, there is a packet over K, with all witnesses x_i=0, whose total witness valuation is exactly C_K(S), and which blocks every shell in S. In fact the polynomial assigned to h has positive excess on shell h and no positive excess on any other shell.

Consequently, if B<C_K(S), some h in S and some primitive p^h-th root zeta satisfy

    v(g_i(zeta-1)) <= v(g_i(x_i))  for every i simultaneously.

The strict inequality B<C_K(S) is optimal. For consecutive shells h_0,...,H, this is exactly the proposed sum threshold.

## 1. Gauss valuation and root accounting

For a nonzero polynomial g(T)=sum_j a_j T^j and r>=0 write

    G_r(g)=min_j (v(a_j)+jr).

For v(x)>=rho, the ultrametric inequality gives G_rho(g)<=v(g(x)). Every polynomial here is nonzero because its witnessing valuation is finite.

Factor g over the algebraic closure, with multiplicities:

    g(T)=a_D product_{j=1}^D (T-alpha_j).

Multiplicativity of Gauss valuation gives

    G_r(g)=v(a_D)+sum_j min(r,v(alpha_j)).

One can also prove this identity directly by scaling T by an element of valuation r and reducing the resulting integral factors. The convention v(0)=infinity handles zero roots.

Because g has integral coefficients, G_0(g)>=0. Therefore

    G_rho(g)-G_0(g)
      = sum_{v(alpha_j)>0} min(rho,v(alpha_j)).

Let M_h(g) be the number of roots of g of valuation exactly r_h, with multiplicity. The radii r_h are distinct and all at most rho. Hence

    v(g(x)) >= G_rho(g) >= sum_{h in S} r_h M_h(g).       (1)

This inequality is the accounting mechanism that prevents the same witness budget from being reused independently at multiple shells.

## 2. The initial polynomial at a torsion radius

Fix a shell h and put N=N_h, r=1/N. Choose one primitive p^h-th root zeta_0 and set z_0=zeta_0-1, so v(z_0)=r. For each g choose a nonzero b of valuation G_r(g), for example b=a_j z_0^j at an index attaining the minimum. Then

    F_g(Y)=reduction( g(z_0 Y)/b )

is a nonzero polynomial over the algebraic closure of the residue field. Its nonzero coefficients are precisely at the exponents attaining G_r(g).

If j and k are two such exponents, then

    (j-k)/N = v(a_k)-v(a_j) belongs to (1/e) Z.

It follows that j-k is divisible by

    D_h=N/gcd(e,N).

Its p-part is

    P_h=p^max(h-1-s,0).

Thus every exponent of F_g is congruent to the smallest exponent modulo P_h. After factoring out its lowest monomial, F_g is a polynomial in Y^P_h. The residue field is algebraically closed and has characteristic p, so that remaining polynomial is a P_h-th power. Every nonzero root of F_g consequently has multiplicity at least P_h.

There is an exact interpretation of the nonzero-root degree. Scale each linear factor T-alpha_j as follows:

* If v(alpha_j)<r, its reduction after division by -alpha_j is a nonzero constant.
* If v(alpha_j)>r, its reduction after division by z_0 is Y.
* If v(alpha_j)=r, its reduction after division by z_0 is Y-reduction(alpha_j/z_0), with a nonzero root.

The product of those scale factors has valuation G_r(g). Hence, up to a nonzero scalar,

    F_g(Y) = Y^u product_{v(alpha_j)=r}(Y-reduction(alpha_j/z_0)).

In particular, the number of its nonzero roots counted with multiplicity is exactly M_h(g). If F_g vanishes on c distinct members of the prime-field set F_p^*, then

    M_h(g) >= c P_h.                                    (2)

This argument explicitly handles all cancellation in g at the radius r.

## 3. Blocking a shell consumes at least a_h

For each a=1,...,p-1 choose

    z_a=zeta_0^a-1=(1+z_0)^a-1.

Every zeta_0^a is primitive of order p^h, and the binomial expansion gives

    reduction(z_a/z_0)=a in F_p^*.

If shell h is blocked, each z_a has an index i for which

    v(g_i(z_a))>t_i>=G_rho(g_i)>=G_r(g_i).

Therefore F_{g_i}(a)=0. The sets of prime-field nonzero roots of the F_{g_i} cover all p-1 elements of F_p^*. By (2),

    sum_i M_h(g_i) >= (p-1) P_h.

Multiplying by r_h gives the shell cost

    r_h sum_i M_h(g_i)
       >= (p-1)p^max(h-1-s,0)/[(p-1)p^(h-1)]
       = p^(-min(s,h-1))
       = a_h.                                           (3)

It is enough to inspect the p-1 representatives z_a for this lower bound; blocking all torsion points is a stronger hypothesis.

Sum (1) over i, then sum (3) over h. The result is

    B >= sum_i t_i
      >= sum_{h in S} r_h sum_i M_h(g_i)
      >= sum_{h in S} a_h.

This proves the lower bound.

## 4. Sharp construction over every finite K

For each h in S put

    k=min(s,h-1),  P=p^k,
    d=N_h/P=(p-1)p^max(h-1-s,0).

Since P divides e, choose a uniformizer pi of K and let c_0=pi^(e/P). Then v(c_0)=1/P and u=c_0^P/(-p) is a unit. The finite residue field of K is perfect, so there is a residue unit w with w^P=reduction(u)^(-1). Lift w to a unit w_0 in O_K and set c=c_0 w_0. Thus

    v(c)=1/P=a_h,
    reduction(c^P/(-p))=1.

Use the polynomial

    g_h(T)=T^d-c

and witness x_h=0. Its baseline valuation is t_h=v(c)=a_h.

For z=zeta-1 in shell h, the shifted cyclotomic polynomial Phi_{p^h}(1+T) is monic of degree N_h, has constant term p, and all its other nonleading coefficients are divisible by p. Evaluating at z, every middle term has valuation strictly greater than 1. Therefore

    reduction(z^N_h/(-p))=1.

It follows that z^d/c is a unit whose P-th power has residue 1. In characteristic p the only P-th root of 1 is 1, because X^P-1=(X-1)^P. Thus

    reduction(z^d/c)=1,
    v(z^d-c)>v(c)=a_h.

The polynomial g_h blocks every point of shell h.

For a different shell j, unequal valuations prevent cancellation:

* If j<h then r_j>r_h, so v(z_j^d)>a_h and v(g_h(z_j))=a_h.
* If j>h then r_j<r_h, so v(z_j^d)<a_h and v(g_h(z_j))=d r_j<a_h.

Hence g_h has no positive excess on any other shell. The packet (g_h)_{h in S} has total witness cost sum_h a_h and attains the lower bound exactly.

## 5. Consequences and cautions

### Extension to integral formal power series

The exact theorem, including its optimal threshold, holds for finite packets g_i in O_K[[T]], evaluated at points of strictly positive valuation in the completed algebraic closure. Choose an integer D with

    (D+1) min_{h in S} r_h > B.

Truncate every series after degree D. The tails have valuation greater than B at every shell point and at every witness, because all their coefficients are integral and every such point has valuation at least min_{h in S} r_h. Since t_i<=B, the truncation preserves t_i and preserves every comparison of the form v(g_i(z))>t_i or v(g_i(z))<=t_i. The polynomial theorem applies. Its sharp polynomial examples already belong to the formal-series class.

### The p-part of ramification is the only relevant field invariant

The tame part of e affects which individual initial-polynomial exponents can occur, but it cancels from the total minimum cost of covering the p-1 prime-field residue classes. The exact answer depends only on s=v_p(e).

### Simple eventual formula

Once h>=s+1, each new shell costs exactly p^(-s). Thus sufficiently far out, L consecutive blocked shells require budget at least L p^(-s). If the first allowed shell h_0>=s+1, then H=h_0+floor(p^s B) always supplies a simultaneous zero-loss point; the range contains floor(p^s B)+1 shells, and this endpoint is sharp.

For arbitrary h_0, the optimal endpoint is the smallest H>=h_0 for which

    sum_{h=h_0}^H p^(-min(s,h-1)) > B.

If e is prime to p, every shell costs 1; the sharp endpoint is H=h_0+floor(B).

### No coefficient-field-independent bound at every budget

If K is allowed to vary, s can be at least H-1 and the cost over h_0,...,H becomes sum_h p^(1-h). Its infinite sum is p^(2-h_0)/(p-1). Consequently there is no field-independent finite endpoint for budgets at least that limit. Every finite range can be blocked over some sufficiently ramified finite K within such a budget.

### Packets must remain packets

The sharp construction uses one polynomial per shell. Multiplying them into one polynomial can introduce valuation deficits from other shells that cancel a desired excess. Thus the result should not silently be restated as the same sharp extremal theorem for a single polynomial.

### Zero tolerance is exact but qualitative

The construction guarantees strictly positive excess; it does not claim a uniform positive lower bound for that excess as h or K varies. A positive-tolerance extremal problem needs additional analysis.

### This is not a solution of nonabelian GRH

The result sharpens a reusable local torsion-selection ingredient. It supplies no new global arithmetic lattice, prime-sensitive divisibility estimate, or determinant lower bound. Whether it has already appeared elsewhere in the literature is a separate question.
