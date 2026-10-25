# Audit: one Pell cap with six exact powers and modular binomial numerators

Comparison source: ProveIt commit `f4d8db99e060339f3306a04d507c35bc1d0d68c5`.
This is an independent mathematical compatibility audit, not a new formal
proof-assistant certificate. No upstream files were modified.

## Sources actually read

1. Incoming `ConZFC_Shared_Pell_Bound_261_2026-10-24.zip`, especially
   `portable/CAP_THEOREM.md` and `portable/source/custom/capped_pell.py`.
2. Incoming `ConZFC_Shared_Binomial_Certificates_2026-10-24.zip`, especially
   `direct/PROOF.md`, `direct/build_modular_factorial.py`, and the literal
   `direct/equation319/raw/raw_audit_input.json` and `SUMMARY.json`.
3. Incoming `ConZFC_Residue_Compiler_2026-10-24.zip`, whose dominant-denominator
   idea is credited below.
4. The retained immediate C222/ZF/ZFC calibration interfaces in the cap
   package. Their transitive Lean import closure was not rebuilt.

The 319-variable source has six exact powers, eleven modular binomial
requests, fifteen independent seed indices, no additive-index derivations,
and one derived denominator. Its original frame deliberately omitted the
eleven modular upper indices. Copying that frame unchanged into the capped
architecture would invalidate the cap proof.

## 1. General cap lemma, including zero requested indices

For an integer A >= 2 define X_j(A),Y_j(A) by

    X_0=1, Y_0=0,
    X_(j+1)=A X_j+(A^2-1)Y_j,
    Y_(j+1)=X_j+A Y_j.

Let r be fixed, let W >= r+2 and W >= 3, assume A-1 > W^3, and let
0 <= k_i < W for i=1,...,r. Suppose the natural-valued variables obey

    V = Y_W(A),
    x_i^2-(A^2-1)y_i^2=1,
    V = W+1+s+sum_i y_i,
    sum_i (y_i-k_i)^2 = (A-1)q.

Then every pair is exactly (X_(k_i)(A),Y_(k_i)(A)). Conversely the
canonical pairs admit natural s,q. Zero requested indices cause no problem.

Proof. Pell classification yields y_i=Y_(j_i)(A), j_i>=0. The aggregate
row gives y_i<V, whence j_i<W by monotonicity. Modulo A-1, the recurrence
gives X_j=1 and Y_j=j. Consequently A-1 divides

    E=sum_i(j_i-k_i)^2.

But 0<=E<=r(W-1)^2< W^3 < A-1. Thus E=0, and j_i=k_i. For completeness
the true y_i have y_i-k_i divisible by A-1, so the displayed q is a
nonnegative integer. Also y_i<=Y_(W-1)(A) and

    Y_W(A) > (2A-1)Y_(W-1)(A).

Since r<=W-2 and A>W+1, the difference V-sum_i y_i exceeds W, making
s=V-W-1-sum_i y_i nonnegative.

The one anchor V=Y_W(A) must retain the full inherited indexed-Pell
certificate. Its hypothesis W<=V follows from the aggregate row. Do not
replace this anchor with a principal Pell norm alone.

## 2. The enlarged frame and the split lower scale

Let S be the finite union of the distinct atoms appearing as base, exponent,
or output of an exact-power request, together with every modular-numerator
upper index. Use

    W = r+2+sum_(a in S) a.

All atoms are natural-valued polynomials in the semantic data. Every seed
index occurs among S, so k_i<W; independently, W>=r+2. The fixed offset
avoids relying on positivity of modular indices. In the actual 319 source
these indices are positive anyway: encoded representatives are shifted by
one, the factorial top is F^2+t>=16, and the derived label range contains
a positive constant.

Keep the modular source's split scale:

    L^2-((W+1)^2-1)(W Z)^2=1,  Z>=1,
    A=L+sigma,  sigma>=0.

Pell classification gives L=X_e(W+1), WZ=Y_e(W+1), with e>0. Reducing the
ordinate modulo W yields e=0 modulo W, so e>=W. Hence

    A>=L>=X_W(W+1)>=(W+1)^W,
    A-1>W^3.

This establishes the cap's size hypothesis before decoding any exact power.
The upper indices J(encoded labels), C, and all encoded column values may be
extremely large. This is harmless: they are chosen before L and A, and only
affect the size of the existential Pell witnesses, not polynomial degree.

Crucially, do not require A itself to satisfy the lower-scale Pell equation.
The free nonnegative sigma lets A range cofinally in the residue class needed
for the common modular numerator. The cap index and all private Pell
witnesses are excluded from S, preventing a circular frame definition.

## 3. Six exact powers are recovered without factorial semantics

With all seed indices now proved correct, use the unchanged positive-power
rows

    T_n=2An-n^2-1,
    X_k(A)+(n-A)Y_k(A)=m+T_n h, h>=0.

Here each semantic n,k,m is less than W. The modulus row forces n>=1;
the literal exponents are positive. Since A>=(W+1)^W, T_n exceeds both
m and n^k. The standard Pell congruence therefore gives m=n^k.

The six retained requests are

    V_0=(F^2+1)^t,
    N=B^K,
    q=N^K,
    D_t=q^t,
    D_y=q^(y+1),
    D_x=q^(x+1),

with B=b_0+2, R=2+t+x+y+F, K=2R, and t>=16. The extra denominator
D_(t+1)=q D_t is ordinary multiplication. None of these formulae is a
variable-exponent expression in the final polynomial: all six use the
finite polynomial Pell representation just described.

## 4. A smaller common modulus is compatible

Credit: the incoming Residue Compiler packet introduced the dominant
denominator method. It composes with the merged factorial and shared-cap
construction.

The raw ceiling rows imply V_0+s=BF. Since V_0>=1 after the exact powers
are decoded and B>=2, they force F>=1. The source endpoints include

    x=F+1+(y+1)u_0,
    y=F+1+r_0,
    x=1+(1+(t+1)y)u_t.

If u_t=0 then x=1, contradicting x>=F+1>=2. Thus u_t>=1 and

    x>=2+(t+1)y,  y>=2.

In particular x>y+1 and x>t+1. This argument uses no factorial semantics
and can precede decoding the exact binomial.

Consequently one may use

    M=N D_x=N q^(x+1)

instead of the original product q D_(t+1) D_x D_y. For every divisibility
digit denominator d in {D_t,D_(t+1),D_x,D_y}, Nd divides M. For the single
exact binomial, q D_t=q^(t+1) also divides M. These are precisely the
moduli used by the digit rows.

The common-root equation is

    2A(q+1)=(q+1)^2+1+M h_0, h_0>=0.

Because N divides q, gcd(q+1,M)=1. Thus gcd(2(q+1),M) is either 1 or 2.
In the second case q+1 is odd and the right-hand constant is even. The
linear congruence for A is therefore always soluble. Its positive
solutions are cofinal. After all semantic data and L have been chosen,
choose A in this congruence class, above L and large enough that h_0>=0.

## 5. Modular numerators, signs, and natural quotients

Put b=q+1 and R_n=X_n(A)+(b-A)Y_n(A). The common-root row gives
(b-A)^2=A^2-1 modulo M, and hence R_n=b^n modulo M. For n>0,

    X_n(A)>(A-1)Y_n(A),
    R_n>qY_n(A)>0.

For n=0, R_0=1>0. Thus modular numerator representatives are always
positive, despite the signed-looking coefficient b-A.

Each true exact-digit residue r+dB lies in [0,qd), and each true
divisibility residue r lies in [0,Nd). Since R_n is nonnegative and
congruent to that least residue, the required quotient is nonnegative.
This verifies completeness over naturals, not only over integers.

The independent pre-factorial radix bound is unchanged:

    q=B^(4R^2)>=2^(4R^2),
    binom(F^2+t,j)<q for 0<=j<=t.

It proves B=binom(F^2+t,t) before invoking the squared-radius factorial
fixed-point lemma. The ceiling rows then yield F=t!. The inherited range
digit bounds, strengthened prime-power CRT construction, bounded C222
source, Horn-flow argument, and the identified ZF/ZFC calibration follow.

## 6. Soundness order and completeness order

Soundness must be presented in this order:

1. Read the raw natural frame and split-scale equations.
2. Obtain A-1>W^3 and the single genuine indexed cap at W.
3. Identify every principal seed pair using the pooled squared errors.
4. Decode the six exact powers.
5. Infer F>=1, derive the endpoint bounds, and justify dominant M.
6. Decode the exact factorial/CRT binomial using the independent radix bound.
7. Prove F=t!, then decode all remaining range binomials.
8. Apply strengthened prime-power CRT, derived label bounds, and Horn flow.
9. Invoke the inherited C222-to-ZF and ZF-to-ZFC refutation equivalences.

Completeness chooses the finite proof and a padded horizon first; then the
bounded source data, F,B,R,K,N,q, and the CRT representatives; then every
semantic exact-power output and modular index; then the enlarged W and lower
scale L; then a sufficiently large A in the common-root class; then the
single anchor certificate, canonical seed pairs, pooled slack and quotient,
digit witnesses, and all arithmetic gates. There is no backward dependence
from a semantic index to a private Pell witness.

## 7. Release obligations

The mathematical composition is sound under the stated conditions. A final
artifact must additionally bind the proof to its emitted syntax:

- Verify the actual W atom set, offset, and all seed registrations.
- Verify the lower scale uses L and A=L+sigma.
- Verify every exact and modular request uses a registered canonical pair.
- Verify all pooled rows and the full anchor rows literally.
- If using dominant M, verify it is exactly N D_x and retain the endpoint
  rows needed above.
- Check every affine and natural-domain contraction and all expanded
  coefficients independently.

Finite checks establish these algebraic and source-binding claims. They do
not replace any of the unbounded number-theoretic proofs above.
