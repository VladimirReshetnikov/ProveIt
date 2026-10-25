# Linear orientation in one Pell pool: an explicit quartic in 306 integers

## Result and provenance

This construction transforms the literal, centered 324-integer quartic in
ProveIt package 131 (`131-shared-pell-caps-round16/direct/integer324/`) at
commit `1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`. Its parent ordinary proof
is retained as `parent/PROOF_324.md`; the complete parent equation and its
centering certificate are retained alongside it. No coefficient port is an
unknown or an unspecified fixed parameter.

The new equation is

    P306(z0,...,z305) = sum_{j=0}^{205} r_j(z)^2 = 0,

where every coordinate independently ranges over all of Z. The 206 literal
quadratic residuals are in `integer306/equation.json` and `residuals.txt`;
the complete collected polynomial is in `expanded_polynomial.json`.

The exact metrics are 306 variables, 206 residuals, degree four, 6,259
collected monomials, coefficient height 128,446, and residual height 256.
The parent has 324 variables, 208 residuals, 5,808 monomials, and the same
degree and heights. Thus this is a variable/row reduction at a support cost,
not simultaneous dominance in every measure. It is not a global minimum.

The ordinary theorem proved below is

    (exists z in Z^306: P306(z)=0)
        iff (exists w in Z^324: P324(w)=0).

Composing with the retained parent C222/ZF/ZFC calibration gives the
ZFC-provable equivalence between the nonexistence of a Z^306 zero and
Con(ZFC). This does not prove either consistency or inconsistency. The new
proof is ordinary unbounded mathematics formalizable in ZFC; the exact
finite checker does not claim an end-to-end Lean/Rocq or object-ZFC proof.

## 1. The finite-alphabet orientation lemma

For A>=2 write X_j(A),Y_j(A) for the canonical Pell sequences,

    X_0=1, Y_0=0,
    X_(j+1)=A X_j+(A^2-1)Y_j,
    Y_(j+1)=X_j+A Y_j.

The parent anchor and square frame provide all the following facts BEFORE
using any sign on an encoded CRT representative:

* W>=258, A>W^W, and A-1>4W^3;
* there are 15 principal Pell norms
  `x_i^2-(A^2-1)y_i^2=1`;
* their absolute indices j_i obey 0<=j_i<W;
* their proposed integer indices k_i obey |k_i|<W;
* every requested base n and output m has |n|<W and |m|<W;
* the pool quotient is an unrestricted private integer.

These facts follow from the unchanged square frame, the full anchor at W,
and its unchanged ordinate cap. In particular none requires k_i>=0. The
parent proof's sections "One fully certified anchor" and "Bounded signed
principal indices" give the unbounded anchor argument. We retain A's
nonnegative graph, the anchor common-multiplier graph, and the cap graph.

Pell classification gives signs sigma_i,epsilon_i in {+1,-1} such that

    x_i=sigma_i X_(j_i)(A), y_i=epsilon_i Y_(j_i)(A).

The sign of y_i when j_i=0 is immaterial. Modulo A-1, the recurrence gives
`X_j=1` and `Y_j=j`. Let I be any nine of the 15 indices and replace the
old pooled row by

    sum_{i=1}^{15}(y_i-k_i)^2 + sum_{i in I}(1-x_i) = (A-1)q0.       (L)

Reduction modulo A-1 shows that A-1 divides the integer

    E = sum_{i=1}^{15}(epsilon_i j_i-k_i)^2
          + sum_{i in I}(1-sigma_i).

Each term in the second sum is either zero or two, so E is nonnegative.
Moreover

    E <= 60(W-1)^2+18 < 4W^3 < A-1.

The strict middle inequality holds already for W>=16: its difference is
`4W^3-60(W-1)^2-18`, which is positive there. We only use W>=258.
It follows that E=0. Consequently

    epsilon_i j_i=k_i for all 15 i,
    sigma_i=+1 for all nine selected i.

Thus all ordinates are certified at their signed intended indices, and the
selected abscissas have their positive orientation. No assertion that the
actual left side of (L) is small or nonnegative has been made. Only its
finite signed-index representative E is small. The private quotient q0
may have either sign; restricting its sign would require a different proof.

This uses a linear orientation term, not a squared abscissa discrepancy.
The nonnegative residue alphabet `{0,2}` is sufficient. The inherited
conservative `cap_both` construction used `(x_i-1)^2`; the present linear
choice and its composition with scalar-guard removal are the new step here.

Eight-factor scalar-guard compression was already proved in the repository's
`research/signed-pell-cap-refined-scalar-product/PROOF.md`, using a different
residue-one chart. The present construction keeps package 131's raw remainder
chart and obtains the required nonnegative indices directly from the linear
orientation pool. Positive-product reasoning and the ternary nonnegativity
representation themselves are not claimed as new.

## 2. Power requests with a signed intended index

Fix a positive base 2<=n<W, an integer k with |k|<W, and a candidate
integer output |m|<W. Write `T=2An-n^2-1`. The unchanged request is

    x+(n-A)y = m+Tz,                                            (R)

for an unrestricted integer z. Suppose the pool supplies y=Y_k(A), with
`Y_-j=-Y_j`, and x is either sign of X_|k|(A).

For j>=0 define

    H_j=X_j+(n-A)Y_j, J_j=X_j-(n-A)Y_j.

The identities

    H_j J_j = 1+T Y_j^2,
    H_(j+1)=n H_j+T Y_j

imply `H_j=n^j (mod T)`. From A>W^W and 2<=n<W we have
`T>W^W`. For 1<=j<W, all differences used below have absolute value less
than W^W; for example

    |m*n^j-1| <= (W-1)^W+1 < W^W.

If k=-j<0 and x=+X_j, (R) gives `m*n^j=1 (mod T)` and hence
`m*n^j=1` as an exact integer equality. This is impossible because n^j>=2.
If k=j>0 and x=-X_j, the same reasoning gives `m*n^j=-1`, also impossible.
For k>0 the positive-abscissa branch gives the exact equality m=n^k. At
k=0 with x=+1, (R) and the size bounds give m=1.

In particular, when the new pool forces x positive, it forces k>=0 and
gives m=n^k, including the zero-index value m=1. Zero indices are not
discarded by this lemma. The proof does not use a sign assumption on m.

For the t pair, which is not one of the nine newly oriented pairs, its
already positive intended index t and a genuine q-base request eliminate
the negative-abscissa branch by the same argument.

## 3. The early bootstrap uses none of the nine deleted graphs

Use the parent semantic notation. The retained rows and graphs give

    t=16+h0^2>=16,
    B=r+s+1>=1,
    q=B+o+1>=2,
    rho=F^2.

Here F is initially signed, while r,s,o have retained nonnegative graphs.
The pool gives the signed intended indices before any encoded-column sign
is used. Apply the positive-index power argument to the genuine q^t
request: its pair is positively oriented and its output equals q^t.
The SAME pair supplies `V0=(F^2+1)^t`, including the possible base-one case.
The literal ceiling rows give

    F B = V0+s > 0.

Therefore F>=1. Put b=F^2+1. Since b>F and b^(t-1)>F,

    F B >= b^t > F b,
    so B>F^2+1.                                              (B)

The cofinal beta row supplies `y=V0(V0-1)`, so y>F and y>=0. The x graph
is also retained. These facts recover positive K and the other requested
indices exactly when the parent proof needs them; none was used to prove
the new pool lemma. For the nine selected requests we already know their
base q+1 is at least three and lies in the square frame, so the preceding
signed-index lemma applies immediately, even before any CRT decoding.

Let k_a,...,k_vq,k_index be their nine intended indices. All are
nonnegative after the new pool and signed-power lemma.
The retained reciprocal-index rows say

    B*index_quotient = F^2+k_index+1.

If k_index=0, the right side is strictly between zero and B by (B), which
no integer multiple of positive B can equal. Thus k_index>=1. The other
eight indices may still be zero; they are handled next.

## 4. One strict product replaces the eight remaining signs

Introduce six unrestricted product coordinates P2,...,P7, with monic
quadratic rows

    P2=k_a*k_b,
    P3=P2*k_c,
    P4=P3*k_d,
    P5=P4*k_S,
    P6=P5*k_Sp,
    P7=P6*k_u.

Introduce three further unrestricted integers a,b,c and impose

    P7*k_vq - 1 = a^2+b^2+c(c+1).                            (P)

The right side is nonnegative for every integer triple. All eight factors
were proved nonnegative independently of (P), so their product being at
least one implies that each factor is at least one. Together with the
reciprocal argument, this recovers all nine old encoded-coordinate signs.

Conversely any eight positive integer factors give a product at least
one. Every nonnegative integer n has a representation
`n=a^2+b^2+c(c+1)`: apply Legendre's three-square theorem to 4n+1, which
is not of the forbidden form `4^u(8v+7)`. Exactly one of its three square
terms is odd; writing it as `(2c+1)^2` and the others as `(2a)^2,(2b)^2`
gives the claimed representation. This supplies (P).

There is no separate P8 coordinate. Fusing the last multiplication with
the nonnegativity row preserves quadratic residuals and saves one variable
and one row compared with an unfused product chain.

## 5. Exact charts and the two witness maps

In the pinned centered parent, the nine encoded requested indices are

| Requested index | Parent chart expression | Selected abscissa coordinate |
|---|---|---:|
| k_a | z10-1 | 174 |
| k_b | z11 | 180 |
| k_c | z12 | 184 |
| k_d | z13 | 188 |
| k_S | z14 | 192 |
| k_Sp | z15 | 200 |
| k_u | z16 | 204 |
| k_vq | z17 | 212 |
| k_index | z18 | 216 |

The parent translation certificate, the exact nine old graph rows, and the
zero shifts of all nine abscissas establish this table. The old nonnegative
quantities are k_i-1. The deleted parent rows are 184,...,192, labeled
`domain_guard.3`,...,`domain_guard.11`. Their 27 private witness coordinates
are 252,...,278 and occur nowhere else.

The only modified retained parent row is row 180, labeled
`cap.pooled_index_residue`. Add exactly

    9-z174-z180-z184-z188-z192-z200-z204-z212-z216.

Its quotient is parent coordinate 242, `cap.pooled_quotient`, occurring
only in that row. The actual main Pell center is `A=z151+1`, so the pool
divisor is `A-1=z151`, positive at every solution proved above.

From a new zero, the pool and bootstrap prove all nine omitted signs.
Let `T0=sum_selected(1-X_i)`. Each selected X_i is canonical and hence
`X_i=1 (mod A-1)`, so T0/(A-1) is an integer. Replace the private pool
quotient by

    q_old = q_new - T0/(A-1).

Choose fresh ternary Legendre triples for all nine recovered old scalar
graphs. Keep every other parent coordinate unchanged. All parent rows now
hold, giving a literal P324 zero. This is the first point at which the
complete parent consistency calibration is invoked.

Conversely start with a P324 zero. Its ordinary signed-power proof gives
positive canonical abscissas at all nine positive encoded indices. Thus
T0/(A-1) is integral. Set

    q_new = q_old + T0/(A-1),

forget the 27 old private guard witnesses, calculate P2,...,P7, and choose
a fresh triple for (P). All new rows hold. The native front and every
retained parent coordinate except the private pool quotient stay fixed.
The Legendre triples are not unique; no unique extension or bijection of
individual full zero tuples is asserted.

The parent-to-source algebraic projection was performed before this work.
Its nine scalar guard rows survived projection and centering unchanged
except for the certified affine coordinate shifts. Deleting only their
private triples therefore does not invalidate the restoration of any
body coordinate. The parent quotient's privacy similarly permits its
change without affecting a frame, anchor, power request, or native port.

## 6. Literal counts and checking boundary

Keep 324-27=297 old coordinates and append six product coordinates and
three ternary witnesses: 306 in total. Keep 208-9=199 old rows, modify
the one pool row in place, and append six product equations and one fused
strict-product row: 206 in total. Every residual remains quadratic.
The collected polynomial has a nonzero degree-four coefficient, so its
degree is exactly four, not merely at most four.

`build.py` emits the complete polynomial and its transformation certificate.
`verify.py` independently checks every retained and modified row, all
deleted witness occurrence sets, the private quotient occurrence set,
the exact affine requested-index chart, all six monic products, the fused
guard, the complete quartic expansion and exact metrics. Its deliberate
corruption controls check actual semantic entries and collected coefficients.
It imports no producer code. Finite verification establishes these finite
identities, not the universal number theory by sampling.

The mathematical dependency boundary is explicit: the unchanged parent
frame/anchor lemmas, ordinary Pell classification, Legendre's theorem,
and the parent C222 calibration are inherited. The finite residue argument,
signed-index composition, exact guard replacement, and its two witness
maps are proved here. New material was prepared with AI assistance and
claims novelty only relative to the inspected repository material.
