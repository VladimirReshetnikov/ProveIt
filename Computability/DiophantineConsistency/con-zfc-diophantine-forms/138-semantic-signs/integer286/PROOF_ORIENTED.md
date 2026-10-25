# Semantic signs and cofinal bounds: the 286-integer quartic

## Statement and exact artifact

Let P be the sum of the squares of the 196 quadratic integer residuals,
in their displayed order, in `principal/centered/equation.json`. Its 286
coordinates all range independently over the unrestricted integers.
The adjacent `expanded_polynomial.json` is the exact collected polynomial:
degree 4, 6,607 monomials, and maximum absolute coefficient 128,446.

ZFC proves

    (there is no z in Z^286 with P(z)=0) <-> Con(ZFC).

This is an ordinary mathematical equivalence proof formalizable in ZFC;
no new complete proof-assistant derivation is claimed. Its logical
calibration is the retained C222/ZF/ZFC interface, specified below.

The comparator is package 131's centered integer324 equation at ProveIt
commit `1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`: 324 unrestricted
integers, 208 quadratic rows, 5,808 monomials, degree 4, height 128,446.
The new equation saves 38 variables and 12 residuals at the same degree
and height, while adding 799 monomials. The separate 319-variable parity
companion has 5,779 monomials and 207 rows, and improves all varying size
metrics of that comparator. Neither result is a global simplicity optimum.

## 1. Retained arithmetic and notation

The complete parent ordinary proof is `input/INHERITED_PROOF.md`, copied
from package 131's `direct/PROOF.md`. Its literal raw quadratic source
and transformation metadata are `input/source.json` and
`input/transform_certificate.json`. The following explanatory powers
and binomials are compiled by the retained Pell and digit equations;
none is a variable-exponent primitive in the final polynomial.

The front has t=16+h0^2; a proposed factorial F; V=(F^2+1)^t; a
proposed binomial B; R=2+t+x+y+F; K=2R; N=B^K; and common radix q.
The raw ceiling rows are

    B=r+s+1,       FB=V+s,       r>=0, s>=0.                   (1)

The retained beta endpoint includes

    x-1 = (1+(t+1)y) u_t,                                    (2)

with u_t initially an unrestricted integer. The other endpoint and all
CRT/local-rule residuals remain unchanged.

There are nine independent actual CRT representatives, denoted
a_a,a_b,a_c,a_d,a_S,a_Sp,a_u,a_vq,c. Their stored coordinates are each
one less than these values. The old proof required the actual values
positive by guarding those stored coordinates. Here the actual values
are eventually recovered as nonnegative; their stored coordinates may
equal -1. This extension is justified in Section 7, rather than silently
identified with the older positive-coordinate interface.

## 2. All changes, and only the remaining guards

Use the even square frame and odd common-ordinate construction proved in
`PROOF.md`:

    W=2+2 sum(atom^2),
    A^2-W^3(W+2)(2z+1)^2=1,     A=2a^2-1,
    J=2C^2(2e+1).                                            (3)

The atoms are exactly the parent's distinct actual power bases, indices
and outputs, with their full affine restorations. The common anchor cap
is still

    C=W+1+sum(y_i^2)+u^2+v^2+w(w+1).                         (4)

There are fifteen principal Pell pairs (x_i,y_i) with requested signed
indices k_i. Replace their one pooled congruence by

    sum_i ((y_i-k_i)^2+(x_i-1)^2)=(A-1)q0.                   (5)

No new variable is introduced by adding the abscissa terms. All principal
norms and power congruences are retained.

Change the cofinal beta modulus and the self-sized radix to

    y=V-1,             H0=3+2(a_a+...+a_vq+c),
    q=(B H0)^K,        q=(2v_q+1)^2,                          (6)

where v_q is one new unrestricted integer. The last equation replaces the
ternary guard q-B-1>=0; its old affine slack remains only as an eliminable
coordinate. The H0 choice makes its canonical value odd, and also leaves
a margin for the derived-label coefficient bound when some representatives
are zero.

Remove the nine stored-representative nonnegativity guards and the guard
x>=0. Their signs follow from the equations themselves, as proved below.
Together with (3), the removed guards are exactly those on A, e, the nine
stored representatives, x, and the binomial output slack q-B-1.

Fourteen semantic guards remain: r>=0 and s>=0 in (1); eleven products of
paired digit remainders; and the single shared cap (4). Each is encoded by
one row G=u^2+v^2+w(w+1), using three unrestricted auxiliary integers.
The full list and the exact coordinate indices are recorded in
`principal/transform_certificate.json`.

## 3. Frame and principal signs before front arithmetic

The even-frame proof in `PROOF.md` gives A>=2, A odd,
A>W^W, and A-1>4W^3, without any premise about the unknown front signs.
It proves the anchor has C=Y_W(A), even when the common ordinate J is
negative. Here X_j,Y_j are the standard Pell sequences at center A.

Every principal norm has

    x_i=sigma_i X_(j_i)(A), y_i=epsilon_i Y_(j_i)(A),

where j_i>=0 and the signs are independent. The cap gives |y_i|<C and
hence j_i<W. The square frame gives |k_i|<W. Reduction modulo A-1 gives
X_j=1 and Y_j=j. Therefore A-1 divides the nonnegative integer

    E=sum_i ((epsilon_i j_i-k_i)^2+(sigma_i-1)^2).

Because j_i and |k_i| are at most W-1, each summand is at most
4(W-1)^2+4<4W^2. There are fifteen pairs and W>=514. Thus

    0<=E<4*15*W^2<4W^3<A-1.

Consequently E=0. Every abscissa is positive, and every ordinate has its
exact signed index:

    x_i=X_(|k_i|)(A),       y_i=Y_(k_i)(A).                  (7)

When j_i=0, the sign epsilon_i is immaterial and the ordinate is zero;
sigma_i=1 is still forced by its square. This argument bounds residues,
not the huge raw abscissas, and uses no cap on x_i itself.

## 4. An integral output rules out a negative exponent

For a power request with integer base n>=2, signed index k, and candidate
integer output m, the raw frame guarantees n<W, |k|<W and |m|<W. Put

    T=2An-n^2-1.

Since A>W^W and 1<=n<W, T>W^W+W. The positive-abscissa Pell congruence
from (7) has the following consequences.

If k>=0, the elementary recurrence identity gives m=n^k modulo T.
Both values have difference of absolute value less than T, so m=n^k.
For k=0 this says m=1.

If k=-h<0, the norm identity gives

    (X_h-(A-n)Y_h)(X_h+(A-n)Y_h)=1+T Y_h^2.

The first factor is n^h modulo T and the second is the requested m.
Thus m n^h=1 modulo T. But

    |m n^h-1| <= (W-1)^W+1 < W^W < T.

It follows that m n^h=1 as integers, impossible for n>=2,h>=1.
Hence k>=0 and m=n^k. No assumption on the sign of m is used.

For base n=1 and an already nonnegative k, the first half of the argument
still gives m=1. This special case will be used before F is known positive.

## 5. Complete acyclic sign and power recovery

The order below is essential; it proves that the relaxed guards cannot
create roots with negative CRT arguments or a degenerate radix.

1. From (6), q=(2v_q+1)^2>=1. Independently, the genuine horizon t=16+h0^2
   is at least sixteen. Applying the positive-index part of Section 4 to
   the retained request with base F^2+1>=1 gives V=(F^2+1)^t>=1.
   From (1), B>=1 and FB=V+s>0, hence F>=1. Since V>F^2,
   B>F>=1, so B>=2. The new cofinal equation gives
   y=(F^2+1)^t-1>=F+1: for F>=2 use F^2>=F+1; for F=1 use t>=16.

2. Each of the nine actual independent representatives is the exponent of
   a retained power with base q+1>=2. Section 4 therefore proves each is
   nonnegative, without any prior CRT or factorial interpretation. The
   exact zero-based source call ledger is:

   | Actual exponent | Source coordinate plus one | Power call |
   |---|---|---:|
   | a_a | crt.encoded.a | 5 |
   | a_b | crt.encoded.b | 7 |
   | a_c | crt.encoded.c | 8 |
   | a_d | crt.encoded.d | 9 |
   | a_S | crt.encoded.S | 10 |
   | a_Sp | crt.encoded.Sp | 12 |
   | a_u | crt.encoded.u | 13 |
   | a_vq | crt.encoded.vq | 15 |
   | c | crt.encoded_index_minus_one | 16 |

   Every listed base is exactly q+1. These literal claims are checked by
   `verify.py` against the retained source metadata. It now follows that
   H0=3+2 sum a_i is odd and at least three.

3. The retained request B^K has B>=2 and a positive abscissa. Section 4
   proves K>=0. Because K=2(2+t+x+y+F), it is even. Suppose K=0. Then
   x=-2-t-y-F, and (2) says the integer L=1+(t+1)y divides x-1. But

       0<|x-1|=3+t+y+F<L,

   because L-(3+t+y+F)=t(y-1)-F-2 >= (t-1)F-2>0. This is impossible.
   Thus K>=2. The same power lemma at positive base BH0>=6 gives

       N=B^K,      q=(BH0)^K>=36.

   This step uses the power graph as an exact small-residue certificate,
   not a premise about the meaning of q.

4. Power call 14 has base q and exponent x+1. Since q>=36, Section 4
   gives x+1>=0, hence x>=-1. If x=-1, (2) would make L>2 divide -2,
   impossible. Therefore x>=0. All front signs required by the original
   arithmetic, except the deliberately relaxed stored representatives,
   have now been recovered. In particular q>B and its removed output
   slack q-B-1 is nonnegative.

5. The derived constructor exponent is positive on these nonnegative
   actual representatives. The indices t+F^2, y+1, x+1 and t+1 are
   positive. All remaining principal power graphs now recover their
   intended outputs. The t+1 graph follows by the unchanged one-step
   Pell addition from the oriented t pair. Thus every one of the eighteen
   power requests has its intended ordinary meaning.

6. For each paired remainder constraint, its denominator L_i is now a
   positive power of q. The unchanged row is r_i+s_i=L_i-1>=0, and the
   retained guard is r_i s_i>=0. These two facts force both remainders
   nonnegative. The unchanged positive-numerator division rows then
   recover the high/range quotient signs. Both beta endpoint quotients
   are nonnegative by x>=0 and 0<1+F<1+y. No deleted sign was used
   earlier in the argument.

## 6. Exact binomial, factorial, and modulus recovery

The ceiling bootstrap already gives V<=BF<B^2. Since K>=2 and H0>=3,
q=(BH0)^K>=B^2>V. The parent's uniform coefficient lemma
binom(F^2+t,j)<=(F^2+1)^t for 0<=j<=t therefore makes the sole exact
digit graph return B=binom(F^2+t,t). Its padded square-output fixed-point
argument then proves F=t!. This is exactly the proof in inherited
`UNIFIED_PRODUCT_PROOF.md`, Sections 2-4; it does not require the
representatives to be positive.

The same B is product_(i=1)^t(1+F^2/i), and these factors are pairwise
coprime. Hence N=B^K is the original amplified CRT modulus and N divides q.
The removed aggregate bound is still unnecessary, since all actual
representatives a_i satisfy 0<=a_i<H0. For a lower digit index 1<=k<R,
every coefficient of order j<=k fits q: the j=0 coefficient is one,
and for j>=1 either j>a_i gives zero or

    binom(a_i,j)<=a_i^k<H0^K<=q.

For the derived label put n=max(1,a_a,a_b,a_c,a_d). The retained positive
constructor ledger bounds its polynomial Jlabel by (n+1)^ell, where
ell=4194304. Our H0 choice gives n+1<=H0 even if all four arguments
are zero. The old factorial inequality ell(t+1)<2F<K then gives every
needed derived-label coefficient strictly below H0^K<=q. Thus the
derived range digit is also exact.

The ordinary local majorant is unchanged: after x,y,F,t are natural,
its bounded decoded local values satisfy L<R^8388608<2^R<2^K.

## 7. Why zero representatives cause no gap

The representatives enter the CRT proof only as actual integer arguments
of binomial coefficients and as arguments of the local constructor
polynomials. The range lemma says, for a>=0 and k>=1,

    p^e | binom(a,k)  implies  a modulo p^e < k.

For a<k, including a=0, this is immediate because the residue is a if
p^e>=k; in its application p^e>=2^K>k. For a>=k the parent's valuation
proof applies unchanged. Equivalently, the lemma can be stated without
that application inequality: if a<k and p^e<k, the residue is automatically
less than p^e<k. In every case the conclusion holds.

Apply this to each actual a_i and to the nonnegative derived constructor.
The old prime-power CRT proof decodes natural local tuples in their
bounded intervals. Its index congruence, local polynomial divisibility,
and derived label bound do not require a_i>0. They yield a zero of the
same numerical C222 local-rule polynomial for each row. The beta endpoints
and the retained Horn-flow argument therefore yield a finite C222
refutation. No claim identifies a stored value -1 with an old natural
coordinate; it is the recovered actual value zero that enters the proof.

In the converse direction we may still choose all CRT representatives
strictly positive exactly as the parent construction did. Permitting
zero only enlarges the representational choices and never changes which
decoded finite refutations exist.

## 8. Cofinal completeness with y=V-1

Start from a finite C222 refutation, expand its derivation DAG into a
tree, and choose t=16+h0^2 large enough to dominate the step count,
all finite schema parameters, and every complete constructor label.
Truth padding fills the remaining rows. Every label is at most t and
every pending multiset has at most t+1 members, counting multiplicity.

Put F=t!, V=(F^2+1)^t, y=V-1. Each weight is at most 1+tF<=(t+1)F.
For t>=16, F>(t+1)^2, as follows from the base case and multiplication
by t+1. Therefore every accumulator is at most

    ((t+1)F)^(t+1) < F^(2t) <= (F^2+1)^t-1 = y.

For the strict inequality, divide by F^(t+1), then use
F^(t-1)>(t+1)^(2t-2)>=(t+1)^(t+1), since t>=3.
The final weak inequality follows by expanding (F^2+1)^t.

Also F divides y and y>=F+1. Thus the moduli 1+(i+1)y are pairwise
coprime, and beta CRT gives a nonnegative x and the intended endpoint
quotients. This is exactly the role of the older larger y=V(V-1), now
proved for the smaller linear expression. The stronger accumulator
estimate was derived independently in the parallel natural-number branch
of this iteration; it is shared here with that attribution.

Fix B,R,K,N and choose positive independent representatives by the old
precision-2K CRT. Only then set H0=3+2 sum a_i and q=(BH0)^K. The bounds
in Section 6 give all exact digit witnesses without circular dependence.
Each factor 1+F^2/i is odd, since i|F and F is even. Thus B and H0 are
odd, K=2R is even, and

    v_q=((BH0)^R-1)/2

is an integer satisfying q=(2v_q+1)^2. Construct the private even frame,
the canonical principal pairs, and the odd anchor quotient as in
`PROOF.md`. Each term in (5) is divisible by A-1, since the canonical
Pell coordinates satisfy X_k=1 and Y_k=k modulo A-1; hence the pooled
quotient exists. All retained guards have their ordinary ternary
representations. This constructs a zero of the new equation.

## 9. Calibration and polynomial compilation

The two unchanged logical interfaces are

    SetTheory.BusyBeaver.ZFC.KEndpoint.c222_iff_zf_refutation
    SetTheory.BusyBeaver.ZFC.ConstructibleChoice.zf_refutation_iff_zfc_refutation.

The first identifies the numerical calculus's derivation of falsity with
a finite ZF refutation. The second transports finite refutations between
ZF and ZFC using the constructible-universe consistency theorem. No
simulation of K215, Jones universal polynomial, or Sun reduction occurs
in this direct polynomial branch.

The preceding ordinary proof is a proof within ZFC of existence of an
integer zero if and only if existence of a finite ZFC refutation. Negation
is exactly the stated consistency equivalence. Neither consistency nor
inconsistency is assumed. Finite executable checks below do not establish
the unbounded theorem by sampling.

Every final residual is literally quadratic. The compiler first performs
the retained exact Horn factorization, then monic integral elimination
only when the substitution keeps all residuals quadratic. Its inverse
certificate restores the eliminated coordinates over the integers.
Coordinate centering is an integral translation, hence a bijection.
Squaring and summing gives the supplied polynomial without cancellation
ambiguity: over the integers it vanishes exactly when all residuals do.

The variable reduction from 324 is accounted for as follows:

| Change | Variables saved | Rows saved |
|---|---:|---:|
| Even frame, doubled A and odd anchor quotient | 5 | 1 |
| Semantic recovery of nine stored-representative guards | 27 | 9 |
| Semantic recovery of x>=0 | 3 | 1 |
| Odd square radix replaces a ternary output-bound guard | 2 | 0 |
| Linear cofinal y=V-1 | 1 | 1 |
| Total | 38 | 12 |

## 10. Reproduction and limits

Run `python3 -B verify.py --rebuild` from this component directory.
It checks exact source transformations, the nine-call ledger, guard list,
factorization, monic projection, both translations, and the full collected
polynomial. It also rebuilds the selected artifacts in a temporary
directory and requires exact equality. The report distinguishes these
finite checks from the unbounded sign, Pell, factorial, CRT, and
calibration arguments.

The important new mechanism is to prove the signs of front coordinates
from their already-required integer power certificates after orienting
the principal Pell abscissas. The smaller cofinal modulus and the parity
choices supply compatible further savings. The result is a concrete
smaller direct quartic, not a proof that no simpler Diophantine encoding
can exist.
