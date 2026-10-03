# Independent audit of the all-orders inverse-logarithmic hierarchy

1 October 2026. Outcome: APPROVED. Source ALL_LOG_ORDERS.md is pinned in log_hierarchy_approval.json. This is an ordinary asymptotic proof at every fixed truncation order, with constructive exact formal coefficients; it does not assert convergence or exponentially small sectors.

## Inverse derivatives and uniform expansion

At fixed t, the inverse branch of tx-log x=v obeys d/dv=[x/(tx-1)]d/dx. Applied to x R_r(tx), this gives precisely

R_(r+1)(s)=[R_r(s)+s R_r'(s)]/(s-1).

R1=(s-1)^(-1), R2=-(s-1)^(-3), R3=(2s+1)/(s-1)^5. From r=2 onward the recurrence gives R_r(s)=O_r(s^(-r-1)); this bound remains uniform in the stated central range, where x is comparable to M and tx is comparable to log M. The exceptional R1 order is correctly separated.

To make the Taylor remainder explicit, expand the amplitude x'(v) through degree 2J+1, rather than stopping immediately after the last retained even degree. All odd terms integrate to zero on the symmetric central interval. The remainder is bounded by C_J M L^(-2J-4) |v|^(2J+2). The soft-cutoff kernel has finite moments of every order, and its even moment of order 2j is 2(2j)! eta(2j+2). This proves the stated expansion, including its error, since the tails, the small-size region and sum-integral error are smaller than every prescribed M/L^A.

No infinite series is interchanged with an integral. For each requested precision one chooses a fixed finite Taylor degree. Only finitely many inverse derivatives can contribute to a specified Laurent coefficient.

## Rigorous minimization

The displayed Q(rho,h) is exactly (f_hard(M)+nt(M))/m plus the thermal Laurent approximation, with M=m rho, n=m^2/2 and h=1/log m. Differentiation gives the displayed equation (4). Its normalized derivative with respect to rho at (rho,h)=(1,0) equals one, so formal implicit inversion is uniquely triangular and starts at order h^2.

Here is the precise uniform-minimum justification. Fix a small compact interval around rho=1. The exact saddle lies in this interval, and in fact within 1+O(h^2), by the already approved thermal localization. For a sufficiently accurate finite thermal truncation, the explicitly truncated objective has second rho derivative comparable to 1/h near one and has its unique local minimum there. Its normalized critical equation is analytic near h=0 and rho=1. The ordinary implicit-function theorem therefore gives an actual local analytic solution with the computed Taylor coefficients.

The uniform value error between the exact and truncated objectives bounds the difference of their minimum values on that compact interval by the same error. This step requires no derivative bound on an unspecified remainder. The exact global saddle is in the interval, and the truncated minimum is its internal critical point. Taking sufficiently many thermal terms gives any requested inverse-logarithmic precision. The logarithm of the exact-saddle Gaussian prefactor is O(log m), smaller than m/log^A m for every fixed A. These facts prove equation (1) to every fixed order.

## Inversion

Equation (5) follows by writing the new m as m_* tau and using the exact identity s=m_*(log m_*-1). After multiplication by h it is analytic near (tau,h)=(1,0), with derivative one in tau. Its formal solution is unique and begins at h^2. Entropy error O(m/L^(K+1)) divided by derivative asymptotic to L gives relative m error O(L^(-K-2)). Squaring preserves the claimed order. Strict monotonicity of a_n supplies the integer brackets; the relative cost of rounding n is O(m_*^(-2)), negligible compared with every fixed inverse-logarithmic power. Thus the upper index K+1 and error K+2 in equation (2) are correct.

## Exact coefficients and independent checker

The independent standard-library program check_log_hierarchy.py performs truncated arithmetic in Q[P][h], with P=pi^2. It reconstructs R3 and R5 using the recurrence, forms the even-kernel series using its rational even-zeta constants, and solves both normalized implicit equations coefficient by coefficient. It does not import or execute the producer's SymPy generator.

The printed coefficients check exactly:

d1=P/6, d2=P/6, d3=P/6-P^2/72, d4=P/6+P^2/40;

b2=-P/3, b3=-P/3, b4=P(P-3)/9, b5=P(P-10)/30.

The checker also reproduces the supplied six-order output:

d5=P/6+41P^2/180+P^3/432,
d6=P/6+3P^2/4+1973P^3/45360;

b6=-P/3-77P^2/180-P^3/27,
b7=-P/3-19P^2/12-167P^3/2835.

All saddle-ratio coefficients through order seven agree as well. The checker rejects -O. These exact finite identities corroborate the coefficients; the uniform analytic argument above is the proof of arbitrary-order validity.

A minor generator-interface issue was reported separately: its unconditional first-three-coefficient assertions require order>=3, although its parser originally allowed smaller values. The default order-six execution and all approved mathematics are unaffected. The independent checker here has a fixed documented order and no such interface ambiguity.
