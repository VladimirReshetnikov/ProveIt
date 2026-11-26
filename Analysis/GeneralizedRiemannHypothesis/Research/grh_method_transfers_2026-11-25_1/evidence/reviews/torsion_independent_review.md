# Independent mathematical review of the torsion transfer

Reviewed `notes/torsion_transfer.tex` and
`output/grh_method_transfers_2026-11-25/code/torsion_checks.py`.

## Findings

No mathematical flaw found in the stated finite polynomial and bounded
power-series selection theorems. The following details are essential and
are correctly preserved in the text:

1. For the one-coordinate lemma, integrality gives v_0(g)>=0; roots of
   distinct selected radii consume disjoint portions of v_rho(g). The
   truncated-distance average uses the coefficient of Y in
   (Y+1+alpha)^(p^h)-1, which has valuation h because 1+alpha is a unit.
   Delta<1 permits removal of every minimum with 1.
2. At each coordinate replacement, the frozen coordinates remain integral
   even though previously replaced coordinates can have smaller valuation
   than rho. The not-yet-replaced coordinate still has depth at least rho.
   This gives a_i>=b_i and c_i>=b_i for the product argument. The total
   positive excess, not merely the total signed increase, is then bounded.
3. Uniform total-degree truncation works on all witnesses and the finite
   torsion grid because every coordinate has valuation at least r_H>0.
   The tails have valuations >=(N+1)r_H>M, including in several variables.
4. Algebraic approximations can be chosen integral. Precision >M>rho
   preserves the witness depth, and the 1-Lipschitz property of integral
   polynomials preserves valuations exactly below M. This spends no extra
   error from the epsilon budget.
5. For an arbitrary index set, all finite-subfamily constraints have the
   same finite grid. Positive excess is nonnegative, so the constraint for
   a union implies every individual finite-subfamily constraint. The
   finite intersection property proves simultaneous selection.
6. Finite coefficient fields yield a positive lower valuation for a
   nonunit constant coefficient; hence finite total budget allows only
   finitely many nontrivial constraints there. Allowing O_Cp coefficients
   with unbounded ramification makes the infinite-family extension useful.
7. Smith normal form applies only once evaluations lie in a finite
   extension L. As epsilon varies, L and its ramification can vary; small
   normalized length cannot be promoted to vanishing without additional
   uniform discreteness. The text explicitly prevents that overclaim.

## Maximal-order example: precise conclusion

For a primitive zeta of order p^m, m>=2, let

    P_m(T)=product_(a=1,...,p-1) (T-(zeta^a-1)).

At the witness zero, t=v(P_m(0))=p^(1-m). For a primitive exponent b,
exactly one a in {1,...,p-1} satisfies a=b mod p. Its factor has
valuation at least p*r_m, or is zero; the other p-2 factors have
valuation r_m. Thus every nonzero primitive-shell evaluation has
valuation at least 2t. This agrees with the exact code.

This refutes **no increase** at prescribed maximal order, and refutes
an additive-loss bound if epsilon<t. Because t tends to zero with m,
this example alone does not refute a uniform approximate exact-order
selection theorem with H chosen in advance from fixed epsilon.

The separate polynomial Phi_(p^H)(1+T), whose witness valuation is 1,
vanishes on the entire shell of exact order p^H. It is the appropriate
counterexample to arbitrary prescribed exact-order selection when the
permitted budget B is at least 1. The distinction has been sent to root.

## Genus extension cross-check

The field F in `genus_transfer.tex` is a subfield of the multiquadratic
genus field G/Q, hence abelian over Q. Dirichlet GRH suffices for its
Dedekind RH. The discriminant is exactly x^(n/2) because F/K is
unramified, not merely bounded by it. Ramification of every prime of D
persists in F/Q since F contains K. Thus the split prime from
Bach--Sorenson avoids the ramified representative J.

All four endpoint inequalities and the demonstration discriminant have
been checked with exact rational arithmetic, including trial-division
primality for both large factors. The field construction, norm argument
and ramified-class independence/parity lemma were independently reviewed
by the source-audit agent, who found no flaw.
