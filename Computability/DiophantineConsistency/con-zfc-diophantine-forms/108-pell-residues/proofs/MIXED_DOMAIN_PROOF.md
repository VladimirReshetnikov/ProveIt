# Mixed domains for the modular C222 arithmetic source

This note records the exact semantic interface used by `build_mixed.py`.
It applies to the literal 655-coordinate modular source supplied by
`modular_binomial.py`, not to an arbitrary equation that happens to use the
same variable names. The source hash, domain ledger, all sign inferences,
and all projection steps are included in each endpoint packet.

The signed auxiliary Pell theorem is inherited from
`ConZFC_Shared_Pell_1873.zip`,
`con_zfc_batched_pell/proofs/SIGNED_INDEX_THEOREM.md`; it is not a new
theorem of this contribution. Normalizing the sign of the shared U is
also already justified in `ConZFC_Direct_Quartics_3776_3671_2026-10-23.zip`,
`conzfc_signed_quartic/guard_minimization/PROOF.md`. Exact copies and
archive/file SHA-256 pins are retained under `inherited/integer_domain/`.
This component combines those existing signed-certificate results with
the newly supplied modular-numerator graph and the newer small C222 source.

## The retained natural domain

There are 655 original coordinates. The compiler leaves 147 coordinates
temporarily unrestricted and proves that every other original coordinate
is nonnegative. The 147 coordinates consist of:

* 58 divisibility-quotient witnesses;
* the 58 multiplication-gate outputs directly containing those quotients;
* 30 auxiliary Pell coordinates `index*.S`, `index*.R`;
* the shared Pell coordinate `shared_index.U`.

The other 508 source coordinates are certified nonnegative using 96
independent ternary guards and 507 literal lower-bound inferences. Every guard
has the form

    v = a*a + b*b + c*(c+1).

The usual three-square theorem makes this equivalent to `v >= 0` over
integers. The sign inferences are exact original rows `A*v = B`, where
the coefficient A is a polynomial proved strictly positive from earlier
bounds. They strengthen certified lower bounds through the values 0,1,2.
All polynomial inequalities are certified by expanding the substitutions
`x=t+L`, where the already established lower bound L is 0,1,or2 and t>=0.
The resulting coefficients must be nonnegative, and every variable
occurring to an odd exponent must have a known nonnegative sign. A
positive constant term certifies strict positivity. An explicitly
expanded affine square also certifies nonnegativity.

If A>0 and B>=0, then v>=0. If A>0 and B>0, integrality gives v>=1.
If A>0 and B-A>0, then v>1, and integrality gives v>=2. These implications
are sound over integers without dividing by an unproved nonzero value.
The check reconstructs A and B from the literal source residual, ensures
v occurs only to the first power, verifies every lower-bound antecedent,
and accepts no rule that refers to a future inference. Compared with the
initial constant-coefficient sign closure, these rules eliminate two
more guards, for `factorial0.output` and `index_addition.D`. The general
positive-divisor implication method is inherited from the prior guard
minimization proof, not claimed as new here.

No assumption about a still-signed factor is used. In particular all
main Pell coordinates X,Y, the common coordinate V, all actual power
bases, exact-power exponents and outputs, radix and remainder data,
bounded-proof-code parameters, and every genuine inequality slack stay
natural. The lower Pell parameter L and the offset A-L stay natural.

## Which signs are deliberately unnecessary

The source's common and local auxiliary congruences are

    U^2 - (A^2-1)*V^2 = 1,
    b = 1 + 4*V*(b0+1),
    b = A + U*b1,
    S_i^2 - (b^2-1)*R_i^2 = 1,
    S_i = X_i + U*s_i,
    R_i = k_i + 4*Y_i*r_i.

The signed indexed-Pell theorem supplied in the main report permits
U,S_i,R_i,b1,s_i,r_i to be integers. The other hypotheses remain unchanged:
A>=2, V>0, main X_i,Y_i>=0, 1<=k_i<=Y_i, and Y_i^2 divides V.
Taking abs(U), abs(S_i), abs(R_i) identifies ordinary Pell indices.
The two possible signs yield index congruences i = +/- k_i modulo 2Y_i;
the interval 1<=i,k_i<=Y_i forces i=k_i even in the negative case.
Thus all main pairs still equal the requested indexed Pell pairs.
No auxiliary sign guard is needed, and no unsigned quotient theorem is
silently applied to a signed auxiliary pair.

The 58 quotient roles divide into the following groups:

| Group | Count | Role |
| --- | ---: | --- |
| Auxiliary S/R congruences | 30 | Signed indexed-Pell theorem |
| Exact powers | 12 | Residues modulo positive T_n |
| Modular binomial extraction | 11 | Residues modulo q*D or B*D |
| Common modular root | 1 | Divisibility of 2*A*b-b^2-1 by q^(H+1) |
| Shared b congruence | 1 | b congruent to A modulo abs(U) |
| Initial endpoint | 1 | Euclidean quotient automatically nonnegative |
| Product remainder | 1 | Euclidean quotient automatically nonnegative |
| Local CRT evaluation | 1 | Nonnegative evaluation divided by positive B |

For the power and modular groups, integer quotients express exactly the
same congruences that enter the arithmetic proof. Their associated gate
outputs are signed because products involving these witnesses can be
signed. None of those outputs appears in the natural frame bound or in a
semantic input to another arithmetic request; their only uses are the
listed congruence identities.

## Exact powers

Write T_n=2*A*n-n^2-1 and
R_k=X_k(A)+(n-A)*Y_k(A). Once the indexed pair is recovered,

    R_k - n^k = T_n * sum_(j=0)^(k-1) n^(k-1-j)*Y_j(A).

The growth-frame proof still gives 0<=m<T_n and 0<n^k<T_n.
Consequently R_k=m+T_n*q with integer q implies m=n^k by congruence
and interval uniqueness. In fact q is then the displayed nonnegative
sum. The soundness proof never needed to assume q>=0 in advance.

## Modular extraction

Put b=q+1 and write R_n=X_n(A)+(b-A)*Y_n(A). The common modular-root
equation, with an integer quotient, gives

    2*A*b-b^2-1 = q^(H+1)*h.

This is the divisibility needed for R_n congruent to b^n modulo every
requested digit modulus. The modular extraction rows are ordinary
Euclidean residue equations

    R_n = r + D*c + q*D*h_i       (exact digit),
    R_n = r + B*D*h_i            (residue-only range test),

where 0<=r<D and 0<=c<q are still explicit natural bounds, B divides q,
and D is the appropriate q-power. Allowing h_i to be an integer does
not change these residue conditions. The source's lower-digit bounds
therefore recover exactly the same binomial coefficient or divisibility
statement as before. The modular source proof supplies simultaneous
completeness for the common parameter A; no separate existential frames
are identified without that theorem.

If desired, each modular h_i can also be shown nonnegative after index
recovery: R_n>0 for b>=1, since X_n>(A-1)Y_n when n>0, and R_0=1.
Its bounded residue lies in [0,qD) or [0,BD), respectively. The common
root quotient is positive because the frame bounds imply A>=b>=2 and
2*A*b-b^2-1>0. These later inequalities are explanatory; the soundness
argument needs only the congruences.

## Three elementary quotient restorations

These require no Pell theorem.

1. Let u be `endpoint.u0`. The retained final endpoint and natural
   `endpoint.ut` give x>=1. The initial endpoint is
   x=(M0+2)+(y+1)u, and y=M0+2+r0 with r0>=0. Thus
   0<=M0+2<y+1. If u<=-1 then x<0, a contradiction.
2. Let u be `moduli_product.quotient`. Its two source rows state
   N=B+D*u and D=B+s+1. The numerator N is a product of natural
   arithmetic values; B,s>=0. Thus D>=1 and 0<=B<D. Again u<0
   would imply N<0. This does not presuppose that B is already the
   intended product of CRT moduli.
3. Let u be `crt.nonnegative_quotient`. Its rows state L=B*u,
   where L is the sum of a product of squared residuals and two
   difference squares. Thus L>=0. The canonical-index row gives
   B=1+T*(C+1)>=1. Therefore u>=0.

## End-to-end logical implication

An integer zero of the guarded system gives the 508 natural semantic
coordinates by the finite sign certificate. The signed indexed-Pell
theorem fixes all main indices. Exact power and modular residue proofs
then recover the intended finite arithmetic. The three elementary
restorations justify all remaining natural quotient roles. The existing
CRT decoding, bounded local rule proof, and flow argument therefore
produce a C222 derivation of 1. The pinned calculus calibration gives a
finite ZFC refutation.

Conversely, a finite ZFC refutation supplies the original modular source's
entirely natural witness tuple by its completeness theorem. In particular
it supplies a zero of the mixed-domain system. Every retained natural
coordinate has a ternary guard representation, so the integer guarded
system has a zero. These implications are ordinary mathematics
formalizable in ZFC; they do not assume either consistency or
inconsistency.

Finally each integral monic substitution v=f is an exact existential
equivalence over integers. Reverse substitution uniquely restores every
deleted coordinate. All 280 substitutions preserve quadratic residuals,
so the sum of their 397 squares is an ordinary quartic in 663 integers.
The full collected polynomial has 7,268 nonzero monomials. A companion
with smaller restoration support uses 256 substitutions and gives 421
residuals in 687 integer variables, with 5,602 collected monomials and
coefficient height 63,906,013. The primary coefficient height is
2,445,790,974,704. The independent
checker verifies all finite identities and coefficient collection; it is
not itself an unbounded proof of the signed Pell theorem or calibration.
