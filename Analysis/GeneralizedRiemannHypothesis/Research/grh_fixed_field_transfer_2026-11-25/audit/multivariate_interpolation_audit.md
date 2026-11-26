# Independent audit of the multivariate finite-slope theorem

Reviewed proof: `/workspace/scratch/ea6784599d00/agent_transfer/result/non_tower_specialization.md`.

## Verdict

The finite-slope interpolation lemma and its multivariable iteration are valid. The endpoint stated below works for arbitrary rho>0 and any chosen first shell h_0 with r_(h_0)<=rho. It uses the independently proved sharp fixed-field scalar theorem, improving the older eB term to p^(v_p(e))B. Integral formal power series are covered by a separate, rigorous truncation argument.

This is an independent mathematical audit, not a machine-checked Lean verification or a claim of historical priority.

## Corrected complete theorem

Let K/Q_p be a finite extension, e its absolute ramification index, and w=v_p(e). Normalize v(p)=1. Let d>=1, rho>0, and h_0>=1 with

    r_(h_0) = 1/((p-1)p^(h_0-1)) <= rho.

Let F_i be a finite packet of nonzero integral polynomials over K in d variables. Put A_i=G_rho(F_i) and assume sum_i A_i<=B<infinity. Then there are p-power roots of unity zeta_1,...,zeta_d such that each has exact order p^(h_j), with h_0<=h_j<=H, and

    v(F_i(zeta_1-1,...,zeta_d-1)) <= A_i  for every i,

where the following endpoint suffices:

    H = h_0
      + ceil((3^(d-1)-1) log_p(1+B/rho))
      + floor(p^w B).

The statement also holds for F_i in O_K[[T_1,...,T_d]]. No claim that this multivariate endpoint is sharp is justified. The one-variable shell-cost theorem is sharp.

## 1. Checked finite-slope argument

Set b_n(X)=(1+X)^n-1, M=floor(B/rho)+1, and r=rho/M^2. For a polynomial F with A=G_rho(F), call n bad if

    G_(r,rho,...,rho)(F(X,b_n(X),Z)) > A.

Let k=floor(A/rho)+1; integrality gives A>=0, and the total budget gives k<=M. Suppose k distinct slopes J are bad.

### Integral monic division

The polynomial Q_J=product_(n in J)(Y-b_n(X)) is monic in Y over O_K[X,Z]. Division therefore produces quotient and remainder in the same integral polynomial ring; there is no hidden coefficient-field extension and no denominator in this division.

Each factor has Gauss valuation exactly rho, because the Y coefficient is 1 and every term of b_n has degree at least 1 and integral coefficient. Thus G_rho(Q_J S)>=k rho>A, and the remainder R satisfies G_rho(R)=A and deg_Y R<k.

### Constant-minimizer case

If a monomial of R attaining A has X,Y degree zero, then the Z-Gauss valuation of R(0,0,Z) is at most A. Since Q_J(0,0)=0, this polynomial equals F(0,0,Z). Every restriction F(X,b_n(X),Z) has that same constant term as a polynomial in X. Therefore every slope is good. This resolves the otherwise delicate additional-variable case.

### Positive-degree minimizer case

Otherwise choose a minimizing monomial with X,Y degree q>=1. Lowering only those two weights to r gives

    G_(r,r,rho,...,rho)(R)
      <= A-q(rho-r)
      <= A-rho+r.                                      (1)

For M=1 the right side is A. The proof still works because the subsequent lower inequality is strict.

### Lagrange interpolation and denominator bound

The b_n are distinct polynomials in characteristic zero. Lagrange interpolation in Y is therefore valid over K(X,Z). At the valuation with X,Y weights r and Z weights rho, its n-th summand is

    F(X,b_n(X),Z)
    product_(m!=n)(Y-b_m(X)) / product_(m!=n)(b_n(X)-b_m(X)).

The numerator product has valuation (k-1)r. For a positive integer a, the coefficient of X^(p^(v_p(a))) in b_a is a p-adic unit. Since b_n-b_m is a sign times (1+X)^min(n,m) b_|n-m|, and the first factor has Gauss valuation zero,

    G_r(b_n-b_m) <= r p^(v_p(|n-m|)).

Define

    C_J=max_(n in J) sum_(m in J,m!=n)(p^(v_p(|n-m|))-1).

Badness and the finite-sum ultrametric inequality now give

    G_(r,r,rho,...)(R) > A-r C_J.                       (2)

For M>=2, each summand in C_J is at most M-2 and there are k-1<=M-1 of them. Thus C_J<=(M-1)(M-2); for M=1, C_J=0. In every case C_J+1<=M^2, so r C_J<=rho-r. This makes (1) and (2) contradictory.

Hence F_i has at most floor(A_i/rho) bad slopes. The sum of these counts is at most floor(B/rho)=M-1, and a common good slope exists.

## 2. Iteration keeps K fixed

Let rho_0=rho and recursively set

    M_j=floor(B/rho_j)+1,
    rho_(j+1)=rho_j/M_j^2     (0<=j<=d-2).

At each step use the current actual Gauss baselines. They are no greater than the original A_i, so their sum remains at most B. After taking the common good slope, lowering all remaining variable weights to rho_(j+1) can only decrease their Gauss valuations.

Use T_1 as the master variable throughout. The final polynomials are

    P_i(T)=F_i((1+T)^(a_1)-1,...,(1+T)^(a_d)-1),

with a_1=1 and each new a_j among its step's slope range. The earlier exponents can remain unchanged. In particular, if

    P=product_(j=0)^(d-2) M_j,

then 1<=a_j<=P for every coordinate and rho_(d-1)=rho/P^2. Every coefficient is still in O_K. The Lagrange denominators were used only in the proof of a bound; they are not coefficients of the actual substitutions.

## 3. Scalar baselines and order control

The sharp scalar theorem needs only a threshold t_i>=G_r(P_i), not an actual witnessing point. Its root-counting proof uses exactly this inequality. Thus it applies with t_i=A_i and r=rho/P^2.

Choose

    hbar=h_0+ceil(2 log_p P).

Then

    r_hbar <= r_(h_0)/P^2 <= rho/P^2.

Each scalar shell costs at least p^(-w). Therefore among the floor(p^w B)+1 shells starting at hbar, at least one provides a primitive p^h-th root zeta with v(P_i(zeta-1))<=A_i for all i.

Put zeta_j=zeta^(a_j). Its exact order exponent is h-v_p(a_j). Since a_j<=P,

    v_p(a_j)<=log_p P<=ceil(2 log_p P),

so

    h-v_p(a_j)>=h_0>=1.

All coordinates are nontrivial and belong to the permitted range. This order check is stronger than merely bounding v(zeta_j-1)<=rho. No replacement of rho by min(rho,1/(p-1)) is needed.

## 4. Closed endpoint

Let u_j=1+B/rho_j. Then M_j<=u_j and

    u_(j+1)=1+(u_j-1)M_j^2<=u_j^3.

Hence

    2 log_p P
      <= (3^(d-1)-1) log_p(1+B/rho).

Taking ceilings and adding the scalar shell count gives the stated H.

The dimension-one case uses an empty product P=1 and no slope reduction. The logarithmic term vanishes. If B=0, every M_j=1, P=1, and H=h_0; all inequalities remain valid. There is no division by B or by log(1+B/rho).

## 5. Formal-power-series extension

For nonzero F_i in O_K[[T_1,...,T_d]], their Gauss minimum at rho>0 is attained: only finitely many multi-indices can have rho-weight below any fixed finite bound.

The endpoint H above depends only on K,d,rho,B,h_0, and not on degrees. Choose an integer D such that

    (D+1)r_H > B.

Truncate each series by retaining total degree at most D. Since rho>=r_(h_0)>=r_H, its tail has initial Gauss valuation >B, so the truncation has exactly the same baseline A_i.

Apply the polynomial theorem to the truncations. Every resulting coordinate has valuation at least r_H, because its order exponent is at most H. Thus every discarded monomial has valuation at least (D+1)r_H>B at the resulting tuple. The series converges there, and the tail has valuation >B>=A_i. Since the truncated value has valuation <=A_i, adding the tail preserves that value's valuation. The full series satisfies the same bounds.

This truncation is noncircular: H is fixed before D is chosen, and the polynomial theorem is uniform in D.

## 6. Limits of the result

* It is a uniform exact specialization theorem for a fixed finite coefficient field, independent of degrees and packet cardinality.
* The multivariable bound is valid, not shown optimal.
* The finite slope ranges and final endpoint are chosen from numerical parameters; the actual slope choices and torsion point may depend on the polynomial packet.
* Applying it inside the upstream arithmetic argument still requires a coefficient-field ramification bound before torsion orders are chosen. The source's existing degree-free selector has a different quantifier order and cannot be replaced without checking that issue.
* It supplies neither a new global nonabelian lattice nor an L-function prime-sum estimate.
