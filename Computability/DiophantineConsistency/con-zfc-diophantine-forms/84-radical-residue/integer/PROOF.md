# A scaled two-root merger after a transport pivot

## 1. Completed output and scope

The principal equation is `forms/norm17_degree112.json`. It is a sum of five
squares of ordinary integer polynomials in **17 unrestricted integer
unknowns**, of exact total degree **112**. Its six fixed coefficient ports
are the authentic source-34 tuple beta, K0, MC, MF and the two calibrated
determinant scales cone_A=2^1113, cone_B=2^666104. The complete actual
integer bytes are in `coefficients/`; MF is already shifted by beta.

The new step combines two root witnesses using a scale which prevents their
radicands from coinciding modulo a known integer. A rational-root recovery
argument and adjacent-coefficient Pell descent prove that the recovered
witnesses are integers. This is an existential equivalence on each fixed
tuple of the other coordinates, not a claim that an arbitrary resultant
preserves integer solutions.

The following companion points are also supplied:

| Equation | Integer unknowns | Exact degree | Residuals |
|---|---:|---:|---:|
| pivot21_degree16 | 21 | 16 | 9 |
| pivot20_degree20 | 20 | 20 | 8 |
| pivot19_degree32 | 19 | 32 | 7 |
| pivot18_degree88 | 18 | 88 | 6 |
| center18_degree80 | 18 | 80 | 6 before its product finalizer |
| norm17_degree112 | 17 | 112 | 5 |
| norm17_degree110 | 17 | 110 | 5 |

The first four are exact polynomial coordinate projections of the incoming
Joint Guards equations. The last two use new arithmetic arguments given
below. They retain exactly the same inherited compiler, Pell, native
tableau, and ZFC-refutation calibration dependencies. This package proves
new reductions in ordinary arithmetic formalizable in ZFC. It does not
supply a new end-to-end proof-assistant certificate, prove consistency, or
claim a globally smallest polynomial.

## 2. Source identity and the transport pivot

The parent is the incoming archive
`docs/incoming/ZFC_Diophantine_Joint_Guards_2026-10-24.zip` at ProveIt commit
`c1a102936aca437e9999530a0111e6ddab56dc6d`. Exact SHA-256 identities for the
archive and imported inert JSON packets are in `SOURCE_PINS.json`.

In each parent write

    J = 3 J3 + 1,  q = beta J + 1,  W = 4(3 w3 + 1).

The parent has C=q-F-alpha as an abbreviation, and contains the row

    (K0+W) C - F - z(q-1) = 0.

Replace alpha by the new coordinate C, then eliminate F by the monic
transport equation:

    F = (K0+W) C - z(q-1),   alpha = q-F-C.            (TP)

These are integer polynomial substitutions. On the original zero set the
inverse sends (F,alpha) to C=q-F-alpha. Thus projection and restoration are
inverse on zero sets; no divisibility or positivity premise is needed.
Delete the one transport row and the coordinate F. The source counts
22/16, 21/20, 20/32, 19/88 become 21/16, 20/20, 19/32, 18/88.

The packing expression can be kept short using the exact identity

    ((q-1)(q-F)+alpha) = q(q-F)-C.

The four new exact-degree certificates are inherited from parent monomials
which involve neither F nor alpha and are untouched by this substitution.
The independent homogeneous-component check also confirms that the new
guard and packing terms do not raise those four total degrees.

## 3. A compact six-row integer interface

The 18-variable pivoted parent has coordinates

    J3, C, z, f, h, r, v_scale, w3, tau, y,
    gamma, o, j, c, pair_root, pair_pos1, pair_pos2, pair_pos3.

All the following are polynomial abbreviations, not further unknowns:

    J = 3J3+1,                 q = beta J+1,
    W = 4(3w3+1),              X = qW,
    Y = (2v_scale+1) q^3,       E = XY,
    a = (X+1)Y,                H = 4a+3,
    Delta = a^2+H,
    V = fo-c,                  k = 1-V+jc+hE,
    eta = c-Yk,                u = EYk,
    A = u(u+k)+1,
    F = (K0+W)C-z(q-1),        alpha = q-F-C,
    I = (2r+1)c^2,             Q = I^2,
    R = (q(q-F)-C)(q^2-1)+(MC+q MF)J,
    d = (cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2,
    T = eta(k-eta),
    Pos = 1+pair_pos1^2+pair_pos2^2+pair_pos3(pair_pos3+1),
    G = dT-(pair_root^2-d-T+1)^2-Pos.

Its six rows are

    tau^2-A,
    (X+ac+gamma H)^2-Delta c^2-1,
    cj-V-R,
    Q-Delta(f^2-1),
    Q(V^2-y^2)+y^2-1,
    G.                                                     (18)

The supplied verifier checks this complete display against the literal
18-variable packet. In particular u=E(c-eta)=EYk, and the original
auxiliary row is QV^2-(Q-1)y^2-1. The two root coordinates tau and y occur
in only their own displayed rows.

## 4. Positivity needed by the new merger

For integers p1,p2,p3, the value 1+p1^2+p2^2+p3(p3+1) is positive.
Therefore G=0 implies

    dT > (pair_root^2-d-T+1)^2 >= 0.

Thus d and T have the same nonzero sign. If both were negative, putting
d=-b, T=-e with b,e positive would give

    (pair_root^2+b+e+1)^2 >= (b+e+1)^2 > be=dT,

a contradiction. Hence d>0 and T>0.

The second inequality says eta and k-eta have the same nonzero sign.
Consequently k is nonzero, |k|>=2, and 0<|eta|<|k|. Since eta=c-Yk,

    |c| >= |Y||k|-|eta| > (|Y|-1)|k|.             (C)

The authentic beta exceeds 17. As J=3J3+1 cannot vanish,
|q|=|beta J+1|>=beta-1>=16. Also 3w3+1 is nonzero and |W|>=4, while
2v_scale+1 is odd and nonzero, so |Y|>=|q|^3. It follows from (C) that
|c|>1. Therefore I=(2r+1)c^2 is nonzero and Q=I^2>1.

These deductions use only the literal joint guard, the odd scales, and
ordinary integer arithmetic. They do not use the first or auxiliary Pell
root equations which are about to be eliminated, or the unbounded native
calibration theorem.

Finally, putting b=XY^2 gives u=bk and

    A = b(b+1)k^2+1 >= 1,

because b(b+1)>=0 for every integer b. Thus QA is positive.

## 5. Adjacent-coefficient Pell descent

**Lemma.** If Q>1 and V are integers and y is rational with

    QV^2-(Q-1)y^2=1,

then y is an integer.

**Proof.** Take absolute values, and write y=a/m in lowest terms with
m>0. Then m^2 divides Q-1. The equation excludes V=0 and y=0. If |V|=1,
then |y|=1 and m=1.

For V>1, y>0, define

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV.

The new V' is an integer because m divides Q-1. Direct expansion preserves
the same equation. We have y>V and QV>(Q-1)y: the latter follows by squaring
and using

    Q^2 V^2-(Q-1)^2 y^2=Q V^2+Q-1>0.

These two strict inequalities give -V<V'<V. The norm excludes V'=0.
Moreover 2Q-1 is 1 modulo m, so y' has exactly the same reduced denominator
m. Taking absolute values and inducting on |V| reaches |V|=1 without
changing m. Therefore m=1. QED.

This is the adjacent-coefficient descent already proved in source 69 and
used in the incoming denominator-free constructions. It is reproduced to
make the new recovery argument self-contained. A generic quadratic norm
with unrelated coefficients would not justify this integrality step.

## 6. The scaled two-root merger

Keep the last four rows of (18) other than the two root rows, and replace
tau,y by the single unrestricted integer coordinate `root_sum`, denoted xi
in this section. Put

    delta = Q-1,
    Bnum = QV^2-1,
    L = xi^2+2I(2u+k)xi+Q(k^2-4),
    D = delta L-4Bnum,
    N = D^2-64 delta Q A Bnum.                         (N)

The new five-row system is

    (X+ac+gamma H)^2-Delta c^2-1 = 0,
    cj-V-R = 0,
    Q-Delta(f^2-1) = 0,
    G = 0,
    N = 0.                                            (17)

Its single ordinary polynomial is the sum of these five squares.

### Completeness

Given an integer zero of (18), set

    xi = 2(I tau+y)-I(2u+k).

All retained coordinates and four retained rows stay fixed. With
s=I tau+y, tau^2=A, and B=y^2=Bnum/delta, the standard two-root identity

    (s^2-QA-B)^2-4QA B=0

holds. Since

    [I(2u+k)+xi]^2-4QA
       = xi^2+2I(2u+k)xi+Q(k^2-4)=L,

clearing the factors 4 and delta yields N=0. Thus the new point is an
integer zero of (17).

### Soundness

Let an unrestricted integer tuple solve (17). Section 4 gives Q>1,
I nonzero and A>0. Set, only in the proof,

    s=[I(2u+k)+xi]/2,     B=Bnum/delta.

The centered identity above gives

    N = 16 delta^2 [(s^2-QA-B)^2-4QA B].              (ID)

If B were negative, the bracket would be strictly positive, because QA is
positive. B=0 would give QV^2=1, impossible for Q>1 and integral V.
Therefore B>0.

The two radicands QA and B cannot coincide. If they did, multiplying by
delta would give

    Q[(Q-1)A-V^2]=-1,

which is impossible for the integer Q>1. This is the purpose of scaling
the first root by I. Unscaled radicands need not be distinct.

For a concrete negative control, take I=2, Q=4, V=2 and A=5. The auxiliary
radicand is B=(16-1)/3=5. The unscaled sum of roots can vanish as
sqrt(5)-sqrt(5)=0, so its resultant accepts an integer sum even though
neither required square root is an integer. Scaling gives QA=20 and
B=5, and the same sum-zero input is rejected: the cleared uncentered norm
has value 2025. This counterexample is included in the executable checks.

If s=0, equation (ID) would give (QA-B)^2=0, also impossible. Hence s is
a nonzero rational number. Define rational numbers

    x=(s^2+QA-B)/(2s),    y=(s^2-QA+B)/(2s).

Expansion using (ID) gives x^2=QA, y^2=B, and x+y=s. Put tau=x/I.
Then tau is rational and tau^2=A is an integer. Writing tau in lowest
terms shows that its denominator is 1, so tau is an integer. The rational
y satisfies QV^2-(Q-1)y^2=1, and the lemma in Section 5 makes y an integer.
The two discarded root rows of (18) are now restored, with all other
coordinates unchanged.

No parity assumption on xi was required. Although s may initially be a
half-integer, the two independent integrality arguments imply a posteriori
that s=I tau+y is an integer. There is no division in the actual polynomial
N. Every fraction in this section belongs only to the proof.

This proves the claimed existence equivalence on each fixed tuple of the
other sixteen coordinates.

## 7. Exact degree 112

Fixed ports have witness degree zero. The important register degrees are

| Register | q,W | X | Y | E,a | V | k | eta | u | A | I | Q,delta | d | T | G | Bnum | L | D | N |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Degree | 1 | 2 | 4 | 6 | 2 | 7 | 11 | 17 | 34 | 3 | 6 | 4 | 22 | 44 | 10 | 21 | 27 | 56 |

The other three arithmetic rows have degrees at most 14,5,14. In N, D^2
has degree at most 54, whereas -64 delta Q A Bnum has degree 56. For
leading forms, write

    X0=36 beta J3 w3,       Y0=54 beta^3 J3^3 v_scale,
    I0=2r c^2,             Q0=4r^2 c^4,
    u0=h X0^2 Y0^3,        A0=u0^2.

The top form of N is the single monomial

    -64 Q0^3 A0 f^2 o^2
      = -2^26 3^26 beta^22
          r^6 c^12 h^2 f^2 o^2 J3^22 w3^4 v_scale^6.

No other row reaches degree 56. Consequently the degree-112 coefficient at

    r^12 c^24 h^4 f^4 o^4 J3^44 w3^8 v_scale^12

in the sum of five squares is exactly 2^52 3^52 beta^44, which is nonzero
for the authenticated numeral beta. This proves exact degree after actual
coefficient specialization, not just a generic symbolic upper bound.

## 8. A separate 18-variable equation of degree 80

The first root row admits a useful midpoint change. Replace tau by an
unrestricted coordinate t and use

    M = t^2+2(2u+k)t+k^2-4.

The exact identity under t=2tau-2u-k is M=4(tau^2-A). Conversely M=0
reduces modulo 4 to (t+k)^2=0 modulo 4, so t+k is even and
tau=(t+2u+k)/2 is an integer restoring the original norm. This replacement
therefore preserves integer solvability without a parity witness.

Let S be the sum of squares of the first five rows of (18), with M used
for the first row. Keep G as the last unsquared row. The one equation is

    (1+G)(1+S)-1=0.

Since S is a nonnegative integer, 1+S is a positive integer. A product of
integers equal to 1 forces 1+S=1 and 1+G=1. Thus this equation is equivalent
to all six rows vanishing. M has degree 18; the other rows have degree at
most 14. Hence S has degree 36 and G has degree 44, giving total degree 80.
Its exact leading coefficient at

    h^6 w3^8 v_scale^14 J3^50 t^2

is -2^34 3^58 beta^50. This is a separate variable/degree tradeoff, not a
claim that the 17-variable degree-112 equation dominates it on every metric.

## 9. Logical conclusion and reproducibility boundary

### A secondary degree-110 companion

For a further, separately counted tradeoff, change the final root coordinate
by xi_old=xi_new+2V. Let xi denote the new coordinate and retain the
definition of L from Section 6 with this xi. Put

    Jtail = delta(L+4V xi)-4(V^2-1),
    Htail = 4 delta I(2u+k)V,
    N110 = Jtail^2+2 Jtail Htail
             +64 delta Q A(1-V^2)+16 delta^2 Q(k^2-4)V^2.

Using (2u+k)^2=4A+k^2-4 and delta=Q-1 proves the exact polynomial identity

    N110(xi)=N(xi+2V).

Thus the coordinate shear is an integer-polynomial bijection of the zero
sets. The four other rows are unchanged. The degrees of Jtail and Htail
are 27 and 28; the product 2 Jtail Htail is the unique degree-55 contribution
to N110. Its top form is 64 Q0^3 u0^2 V0 xi, with V0=fo. Squaring gives
the nonzero coefficient 2^52 3^52 beta^44 at

    r^12 c^24 h^4 f^2 o^2 xi^2 J3^44 w3^8 v_scale^12,

which has total degree 110. This packet uses 140 live binary operations
in the supplied DAG, compared with 124 for the degree-112 packet. Both
are retained; the lower operation count is the reason degree 112 remains
the primary display. These are counts of supplied circuits, not minima.

### Consistency statement

The parent source theorem identifies an integer zero of its named packet
with a finite syntactic ZFC refutation. Compose that theorem with the
explicit transport isomorphism and the new two-root argument. ZFC can
formalize every step, including rational arithmetic, strong integer
induction in the descent, and the elementary real argument used to reject
B<0. Thus, for the supplied actual fixed coefficients,

    ZFC proves: (norm17_degree112 has no integer zero) iff Con(ZFC).

This is a theorem of ordinary mathematics relative to the cited parent's
unbounded compiler/calibration proof. The present finite checker does not
discharge that inherited proof-assistant obligation. The contribution is
the new complete local reduction, explicit literal equation, degree
certificate, and reproducible coefficient/identity checks.

Run `python3 build.py`, then `python3 verify.py` and `python3 -O verify.py`.
Run `python3 circuit.py` between building and verifying to reproduce the
three literal circuit packets and their operation counts.
The builder is standard-library only; the verifier's exact small ring
checks use SymPy 1.14.0 as listed in `requirements.txt`. Independently written
audit receipts, when present, are separate from these checks. Finite signed
or modular samples are explicitly diagnostics; no finite run is presented
as proof of the universal equivalence.
