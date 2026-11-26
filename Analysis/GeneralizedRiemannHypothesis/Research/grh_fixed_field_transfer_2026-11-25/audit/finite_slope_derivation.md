# Exact simultaneous multivariate specialization without a conductor tower

## Status

A new deduction in this session, with a complete elementary proof below. It answers the explicit multivariate bound question in the prior `grh-torsion-and-prime-sampling.zip`, `sections/field.tex`. No claim of historical priority or resolution of a named global arithmetic conjecture is made. The initial ingredient is the prior fixed-coefficient-field scalar zero-loss selector; the new ingredient is finite-slope interpolation that keeps the coefficient field fixed while removing variables.

## Definitions

Fix a prime p and write v(p)=1. Let O be any valuation ring containing Z_p. For an integral polynomial F in s variables and rho>0 define

G_rho(F) = min_alpha(v(c_alpha) + rho |alpha|).

The Gauss valuation is multiplicative, satisfies G(F+H)>=min(G(F),G(H)), and extends to a valuation on the rational function field. All results use nonzero polynomials and finite baselines. Unequal coordinate weights have the identical properties. Put

b_n(T)=(1+T)^n-1  (n>=1).

## Finite-slope lemma (arbitrary integral coefficients)

Let F_1,...,F_t in O[X,Y,Z_1,...,Z_q] be nonzero. Give all variables weight rho>0 and set A_i=G_rho(F_i), with sum A_i<=B. Set

M = floor(B/rho)+1,  r = rho/M^2.

There is n in {1,...,M} such that, for every i,

G_{r,rho,...,rho}( F_i(T,b_n(T),Z) ) <= A_i.

The first displayed weight applies to T and all the others to Z. Consequently the uniform-radius r Gauss valuation is also <=A_i. In particular none of these restrictions is the zero polynomial. No degree, packet-cardinality, or coefficient-field bound is required.

### Proof by counting bad slopes

For one F with A=G_rho(F), let k=floor(A/rho)+1. Thus k rho>A. Suppose k distinct slopes J subset {1,...,M} are all bad, meaning their restricted Gauss valuations are >A (infinity is permitted).

Divide F, as a polynomial in Y, by the monic polynomial

Q_J(X,Y)=product_{n in J}(Y-b_n(X)).

The quotient S and remainder R are integral polynomials, and deg_Y R<k. Each factor has Gauss valuation exactly rho: its Y coefficient is 1 and b_n has zero constant term and integral coefficients. Thus G_rho(Q_J S)>=k rho>A. From F=Q_J S+R we conclude G_rho(R)=A.

Choose a monomial of R attaining A. If its degree in X,Y is zero, the coefficient polynomial R(0,0,Z) has Gauss valuation at most A in Z. Since Q_J(0,0)=0, it equals F(0,0,Z). Every restricted polynomial has this same constant term in T, and so all slopes are good, a contradiction.

Otherwise its X,Y degree d is at least 1. Lowering the weights of X,Y from rho to r gives

G_{r,r,rho,...,rho}(R) <= A-d(rho-r) <= A-(rho-r). (1)

Lagrange interpolation in Y gives, as an identity over the rational-function field,

R(X,Y,Z) = sum_{n in J} F(X,b_n(X),Z)
                  product_{m in J, m!=n}(Y-b_m(X)) / D_n(X),
D_n(X) = product_{m in J,m!=n}(b_n(X)-b_m(X)).

The numerator product has Gauss valuation (k-1)r. For positive integers d, the coefficient of T^{p^{v_p(d)}} in (1+T)^d-1 is a p-adic unit, since reduction mod p gives (1+T^{p^{v_p(d)}})^{d/p^{v_p(d)}}-1. Hence

G_r(b_n-b_m) <= p^{v_p(|n-m|)} r.

Set C_J=max_{n in J} sum_{m!=n}(p^{v_p(|n-m|)}-1). The triangle inequality for the Gauss valuation and badness of all k slopes give

G_{r,r,rho,...}(R)>A-r C_J. (2)

As 1<=|n-m|<=M-1, we have C_J<=(k-1)(M-2) when M>=2; when M=1, C_J=0. In every case C_J+1<=M^2. Thus r C_J<=rho-r, and (1),(2) contradict each other.

Therefore F_i has at most floor(A_i/rho) bad slopes. The total number of slopes bad for at least one polynomial is at most

sum_i floor(A_i/rho)<=floor(B/rho)=M-1.

One of the M slopes works for the whole packet. This proves the lemma.

## Multivariate theorem over a fixed coefficient field

Let K/Q_p be finite with absolute ramification index e, and let nonzero F_i lie in O_K[T_1,...,T_s], s>=1. Fix rho>0 and A_i=G_rho(F_i), with sum_i A_i<=B.

Put rho_0=rho and define recursively for j=0,...,s-2

M_j=floor(B/rho_j)+1,
rho_{j+1}=rho_j/M_j^2.

Repeated finite-slope reduction yields positive integers a_1,...,a_s, with a_1=1, and polynomials

P_i(T)=F_i((1+T)^{a_1}-1,...,(1+T)^{a_s}-1)

still over O_K, such that G_{rho_{s-1}}(P_i)<=A_i for every i. Specifically a_{j+2} can be chosen in {1,...,M_j}; earlier exponents are unchanged. These choices may depend on the packet, whereas the finite slope ranges and all final bounds are fixed beforehand.

Define h_*(r)=min{h>=1: r_h<=r}, where r_h=1/phi(p^h). Put h0=h_*(rho), P=product_j M_j (empty product 1), and hbar=h0+ceil(2 log_p P). Then r_hbar<=rho/P^2=rho_{s-1}. The scalar fixed-field zero-loss theorem, started at hbar, gives a primitive p^h-th root zeta with

hbar <= h <= hbar+floor(eB),
v(P_i(zeta-1))<=A_i  for every i.

Indeed at most floor(eB) admissible shells contain a root of any P_i of matching valuation: each nonempty matching-root multiset is Galois-stable over K and its product has positive valuation in e^{-1} Z, hence costs at least 1/e of the total Gauss budget. On a shell with no matching root, strict ultrametric equality gives v(P_i(zeta-1))=G_{r_h}(P_i)<=G_{rho_{s-1}}(P_i).

Set zeta_j=zeta^{a_j}. Each zeta_j has order exponent at least h0 and satisfies v(zeta_j-1)<=rho. Indeed 1<=a_j<=P, so v_p(a_j)<=floor(log_p P). Thus

h-v_p(a_j)>=h0+ceil(2 log_p P)-floor(log_p P)>=h0.

It follows that zeta_j is nontrivial and has the required radius. This argument works for arbitrary rho>0 and requires no normalization rho<=1/(p-1).

### Closed form upper bound

Let u_j=1+B/rho_j. Then M_j<=u_j and

u_{j+1}=1+(u_j-1)M_j^2<=u_j^3.

Therefore u_j<=u_0^{3^j}, and

log_p(product_{j=0}^{s-2} M_j) <= ((3^{s-1}-1)/2) log_p(1+B/rho_0).

Since hbar=h_*(rho)+ceil(2 log_p P), a sufficient final exponent is

H = h_*(rho)
    + ceil((3^{s-1}-1) log_p(1+B/rho))
    + floor(eB).

If the independently proved wild-ramification scalar selector is available, its improved charge 1/p^{v_p(e)} replaces floor(eB) by floor(p^{v_p(e)}B) throughout. The multivariate proof itself does not require that refinement.

For s=1 the logarithmic term is zero. If B=0, M_j=1 and the proof still works. For fixed dimension, H is linear in eB and logarithmic in 1+B/rho_0, instead of the previous iterated cyclotomic-ramification recurrence. The dimension dependence 3^{s-1} is not claimed sharp.

## Why a single predetermined curve fails

For a primitive positive slope (a,b), the curve (T_1,T_2)=((1+T)^a-1,(1+T)^b-1) is annihilated by

H_{a,b}=(1+T_1)^b-(1+T_2)^a.

It has Gauss valuation exactly rho: constant term zero, integral coefficients, and at least one of the linear coefficients a,b is a p-adic unit. Thus even arbitrarily high conductor on one prescribed curve cannot be a universal selector for budget rho. The finite list and union-bound argument in the lemma are essential.

For M distinct primitive positive slopes, the minimum Gauss budget of a nonzero integral polynomial vanishing identically on every curve is exactly M rho. The binomials H_{a,b} are irreducible and pairwise nonassociate over K, so their product divides any such polynomial. Each is monic in one variable, and Gauss multiplicativity (or Gauss content) ensures the integral quotient has nonnegative Gauss valuation. Their product attains M rho. This explains the threshold M>B/rho for simultaneous nonvanishing, while interpolation supplies the additional valuation control.

## Relationship to arithmetic transfers

This improves the local multivariate exact specialization interface when one fixed coefficient field K is controlled before the packet is supplied. It can replace the tower recurrence in the prior report's polynomial/matrix-minor applications. It does not remove source `GeneralTheorem.lean` hypotheses: the arithmetic construction chooses coefficient rings after the order exponent, and can allow their ramification to grow. One may not replace its selector by this fixed-K theorem unless that quantifier order is verified. It also does not prove global L-value nonvanishing without integral interpolation polynomials and nonzero witnesses.

## Source anchors

- Upstream: `grh/src/New/Congruences/Selmer/RootsOfUnity.lean`, `exists_rootOfUnity_eval_le_gaussVal_add`, `exists_rootsOfUnity_ellVal_eval_le_add`, commit 72fead102f663d5c7a407964a13dc0cf9d977207.
- Prior question: `grh-torsion-and-prime-sampling.zip`, `sections/field.tex`, several-variable recurrence and closing research question.
- Prior scalar proof: same ZIP, `sections/ramification_intro.tex` and `sections/cyclotomic.tex`; also `grh-torsion-and-zero-data.zip`, `torsion.tex`, bounded-ramification section.
- New ingredient: finite slope counting by monic division and Gauss-valued Lagrange interpolation, proved above; this is a deduction, not an imported theorem or claimed historical novelty.
