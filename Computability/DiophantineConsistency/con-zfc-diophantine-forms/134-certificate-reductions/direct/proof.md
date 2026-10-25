# A deterministic comparison center and a semantic anchor

## The precise result

Let `r_0,...,r_203` be the literal quadratic residuals in `equation.json`,
in that file's order on its 314 independently quantified integer coordinates.
Define the ordinary polynomial

    P(z_0,...,z_313) = sum_{j=0}^{203} r_j(z)^2.

The complete expanded polynomial is in `expanded_polynomial.json`. It has
exact degree 4, 5,721 nonzero monomials and coefficient height 128,446.
The maximum residual coefficient is 256. The ordinary theorem proved here,
using the explicitly cited existing C222 calibration, is

    ZFC proves: [there exists z in Z^314 with P(z)=0]
                iff [there exists a finite syntactic ZFC refutation].

Negation gives the requested equivalence with Con(ZFC). Neither direction
asserts consistency or produces a solution. This is not a new end-to-end
proof-assistant derivation and not a claim of a globally smallest quartic.

The accepted signed parent is package 131's 324-integer construction,
at ProveIt commit `1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`.
Its exact factored quadratic source and interface certificate are retained
in `baseline/`. The parent theorem and complete chronological arithmetic
proof are retained as `proofs/parent131.md`. Its actual 324-variable endpoint
is also supplied and independently recollected for comparison. The new
endpoint saves 10 variables, 4 residuals and 87 expanded monomials, at
unchanged degree and coefficient height.

The proof below concerns the complete new semantic source. Projection,
coordinate changes and coefficient collection are finite exact identities
independently replayed by `code/check.py`; they are not substitutes for
the unbounded arguments.

## 1. Inherited arithmetic interface and what changes

The parent encodes the numerical proof calculus C222 directly, rather than
simulating K215 or instantiating Jones's universal polynomial. Its front
has 18 power requests, sharing 15 independent Pell pairs. The requested
indices include the horizon t, K, F^2+t, the nine encoded CRT representatives,
x+1, y+1, and the derived syntax-label polynomial

    h = J(A_a,A_b,A_c,A_d).

The exact source includes all its arithmetic gates. In the retained
interface, this is seed 14, `index15.X,index15.Y`, with intended index
`1+add.380`. Thus a definition of h adds no new unknown.

For the numerical constructors

    I(a,b)=2(a+b)(a+b+1)+4b,

J is a fixed sum of the nine axiom-conclusion polynomials, a,b,I(a,b),
the universal quantification constructor, and 1. All coefficients in its original
natural circuit are nonnegative. The four actual encoded inputs are at
least 1 under retained guards. Consequently h>=16 and J>=2 A_a^2,
before interpreting any encoded proof or Pell power.

The parent uses an additional fully indexed cap at index W. We instead
use the already required pair (U,C) at h as this cap. Its ordinary
principal norm is retained, and the old separate cap norm and product
wire are deleted. The squared-index-error pool still includes all 15
principal pairs, including (U,C).

Three other modifications are made:

1. The square frame is doubled: W=2(2+sum a^2), over exactly the parent's
   actual base, index and output atoms, including h. Its atom list is
   retained literally, and all affine restorations are included.
2. The common auxiliary ordinate is J_c=C^2(2e+1), with e unrestricted.
   The old e>=0 guard and its three private witnesses are removed.
3. Instead of freely choosing a comparison center by CRT, define

       D = A+(1-A)H^2,

   where H^2-(A^2-1)J_c^2=1. One new wire T=H^2 makes this definition
   quadratic. The former private comparison parameters d and f disappear.

Finally we permit either sign of the main scale A. Its old nonnegative
guard is removed, and the cap is the single nonnegative predicate

    C^2-W^2-1-sum_{i != anchor} y_i^2 >= 0.             (1)

It is represented by the exact ternary form a^2+b^2+c(c+1). This form
is always nonnegative on Z and represents every nonnegative integer by
Legendre's three-square theorem applied to 4n+1.

All other front guards, power requests, remainder bounds and semantic
source rows remain unchanged. In particular the positive encoded-column
guards are retained. No conjectured product compression is used.

## 2. The even frame supplies an odd large signed scale

The doubled frame is even, W>=516, and it gives |a|<W for every actual
semantic atom a. Every proposed index k_i satisfies |k_i|<W, including h.
The old frame norm and its odd ordinate parameter remain

    A^2-W^3(W+2)(2z+1)^2=1.                           (2)

Since W is even, A is odd. Set a=|A|. Pell classification at center W+1
applied to (a,|W(2z+1)|) gives a positive index n. Reduction of Y_n(W+1)
modulo W gives n=0 modulo W; the ordinate is nonzero, so n>=W. Therefore

    a >= X_W(W+1) > W^W,
    |A-1| >= a-1 > 4W^3.                             (3)

No sign of A, any unvalidated output, or any unvalidated requested index
is used. Here and below X_n(b),Y_n(b) are the integer Pell polynomials
defined by X_0=1,Y_0=0 and

    X_{n+1}=b X_n+(b^2-1)Y_n,
    Y_{n+1}=X_n+b Y_n.

For negative bases, X_n(-b)=(-1)^n X_n(b) and
Y_n(-b)=(-1)^(n-1)Y_n(b) for n>=1. Negative indices use X_{-n}=X_n
and Y_{-n}=-Y_n. These formulas are elementary recurrence identities.

## 3. A polynomial comparison center replaces CRT

The retained anchor and common norms are

    U^2-(A^2-1)C^2=1,
    H^2-(A^2-1)J_c^2=1,
    J_c=C^2(2e+1).

Equation (1) gives |C|>W. Thus C and J_c are nonzero. Define

    D=A+(1-A)H^2=1-(A-1)(A^2-1)J_c^2.                (4)

Because A is odd, 4 divides (A-1)(A^2-1). Since C^2 divides J_c,
the identities in (4) give

    D=A modulo H,      D=1 modulo 4C,      |D|>1.      (5)

For A>=3 the second expression in (4) is less than -1. For A<=-3 it
is greater than 1. No order condition on D, H or J_c is required.

Retain the comparison norm and two congruences

    S^2-(D^2-1)Q^2=1,
    S=U+Hg,              Q=h+4Cq.                    (6)

We prove that |C|=Y_h(a). Classify the first two norms at a to write

    |U|=X_i(a), |C|=Y_i(a), |H|=X_l(a), |J_c|=Y_l(a),

with i,l>0. Since C^2 divides J_c and |C|>1, i<l. The standard
squared-ordinate divisor lemma gives |C| divides l. For completeness,
its proof first obtains i|l from Y_i|Y_l using the addition law; putting
l=ik and expanding the unit power modulo Y_i^2 gives

    Y_l/Y_i = k X_i^(k-1) modulo Y_i.

The norm gives gcd(X_i,Y_i)=1, hence Y_i divides k and therefore l.

Classify the comparison pair at |D|, and absorb signs of A,D and the
abscissas using the signed-base recurrence identities. Polynomial base
transfer through D=A modulo H and S=U modulo H implies that its index j
satisfies j=+/-i modulo 2l. This is the same abscissa-residue lemma used
by the parent: reduce the Pell unit exponent modulo 2l, reflect about l,
and use strict growth to separate the remaining absolute traces.
The other congruence in (5) gives Y_j(D)=j modulo 4C; hence (6) implies
j=+/-h modulo 4C. As |C| divides l, it follows that

    i=+/-h modulo 2|C|.

But 1<=i<=|C|, since Y_i(a)>=i, and 1<=h<W<|C|. The only possibility
is i=h. This establishes the exact absolute cap index. It does not yet
assert the sign of C; that is recovered by the pooled equation.

The fixed polynomial center (4) is the new local simplification. The
underlying signed index criterion, Pell recurrences and CRT method it
replaces are inherited. No claim of literature-wide priority is made.

## 4. The square cap identifies all signed indices

Each retained principal norm gives independent signs in

    x_i=+/-X_{j_i}(A),    y_i=epsilon_i Y_{j_i}(A),

where j_i>=0. For non-anchor seeds, (1) implies |y_i|<|C|, so j_i<h.
For the anchor, j_i=h. Thus every j_i is less than W.

The unchanged pooled row is

    sum_i (y_i-k_i)^2=(A-1)q_0,                       (7)

with q_0 unrestricted. For every signed integer A, the polynomial
recurrence gives X_j(A)=1 and Y_j(A)=j modulo A-1. Therefore |A-1|
divides the nonnegative integer

    E=sum_i (epsilon_i j_i-k_i)^2.

There are 15 indices, 15<W, and both |k_i| and j_i are less than W.
Hence 0<=E<4*15*W^2<4W^3<|A-1|. Divisibility forces E=0. We obtain

    y_i=Y_{k_i}(A),       x_i=+/-X_{k_i}(A)            (8)

for every seed, even if a proposed index is zero or negative. At the
semantic anchor the target is h>0, so C=Y_h(A) with the correct signed
base convention. The large actual sum in (7) is not asserted to be
small; only its finite index-error representative E is bounded.

Allowing signed A is an explicitly credited extension already justified
in the repository's unoriented-cap work, retained as
`proofs/signed_scale.md`. We have rebound it to this complete source;
we do not invoke an old positive-A result after removing its hypotheses.

## 5. Recover the actual powers before using arithmetic semantics

Let k>0, 2<=n<W, |m|<W and k<W. Put T_n=2An-n^2-1. For canonical
signed-base values define

    L_k=X_k(A)+(n-A)Y_k(A),
    R_k=X_k(A)-(n-A)Y_k(A).

The polynomial identities

    L_k R_k=1+T_n Y_k(A)^2,
    L_{k+1}=n L_k+T_n Y_k(A),      L_0=1

hold for either sign of A. Thus L_k=n^k modulo T_n. Equations (3)
and the frame give |T_n|>W^W and strict bounds for |m-n^k| and
|m n^k+1| below |T_n|. On the canonical x branch the actual request
therefore gives m=n^k. On the opposite branch it would give
m n^k=-1, impossible in integers. This selects the canonical signed-base
abscissa, which need not be positive when A<0.

The source's sign chronology is unchanged. Initially its retained guards
and rows give B=r+s+1>=1, q=B+o+1>=2, x>=0 and t=16+h_0^2>=16.
The genuine q^t request first orients the t pair. The request using
the same pair at base F^2+1 then gives V_0=(F^2+1)^t, including the
possible base-one endpoint. The ceiling F B=V_0+s>0 yields F>=1.
Consequently B>F>=1 and q>=3. The cofinal row y=V_0(V_0-1) gives
y>=F+1. All independent representatives are positive by their retained
guards, so K=2(2+t+x+y+F) and all requested indices are now positive.

The B^K request orients the K pair and gives N=B^K. Its shared request
gives q=(BH_0)^K, H_0=1+sum of the nine positive representatives.
Every remaining principal pair has a genuine request at q or q+1, and
the signed polynomial recurrence supplies the derived t+1 pair. Thus all
18 power interfaces have their ordinary meaning.

Each retained interval-product guard says r_i s_i>=0, while its power
bound gives r_i+s_i=L_i-1>=0. Hence r_i,s_i>=0. Positive numerators
and Euclidean remainder bounds then restore the needed quotient signs.
These sign conclusions occur after power decoding and are never used
circularly to prove it.

## 6. The unchanged factorial, CRT and C222 calibration

For precision, the following imported portion is the parent's proved
arithmetic theorem, not an experimental conjecture. Its full argument
is retained in `proofs/parent131.md` with its stated predecessor sources.
The relevant front, requested powers and range predicates are unchanged.

The ceiling gives V_0<=BF<B^2. Since q=(BH_0)^K>=B^2, the first digit
is carry-free and B=binom(F^2+t,t). The parent fixed-point theorem at
t>=16 then gives F=t!. The same B equals the product of the pairwise
coprime integers d_i=1+F^2/i, 1<=i<=t. Thus N=B^K is the amplified
CRT modulus. The self-sized radix N H_0^K is chosen after the actual
representatives; its bounds cover ordinary binomial coefficients and
the derived label using J<=H_0^(2^22) and (2^22)(t+1)<K.

Prime-power range extraction recovers every bounded local rule and label.
The finite Horn-flow argument uses pairwise coprime weights 1+jF and
exact multiplicity balance to recover a C222 refutation, including in the
presence of cycles in a supplied rule multiset. Finally the inherited
logical endpoints are

    KEndpoint.c222_iff_zf_refutation,
    ConstructibleChoice.zf_refutation_iff_zfc_refutation.

Together these establish that any new-source zero yields a finite ZFC
refutation. No K215 transition table or universal polynomial is required.
The package retains exact source pins, ordinary parent proofs and named
logical interfaces. It does not recompile the full older formal development.
That distinction is part of the release's proof scope, not an extra
consistency assumption in the mathematical theorem.

## 7. Completeness: choose a dominating semantic anchor first

Start with a finite C222 refutation. Use the parent's cofinal construction:
choose t=16+h_0^2 above the finite proof data and pad with truth steps;
set F=t!, V_0=(F^2+1)^t, y=V_0(V_0-1), and choose the beta CRT code x.
Fix R_0,K,B,N. Choose the nine positive encoded representatives with the
parent's stronger residues modulo d_i^(2K). Their common period is N^2.

Now increase only A_a by a sufficiently large multiple of N^2. This
preserves every local polynomial congruence, including the derived-label
range condition, at every required prime-power precision. It also makes

    h=J(A_a,A_b,A_c,A_d) >= 2 max_{i != anchor} k_i + 1,             (9)

because J>=2 A_a^2 and every other index depending on the changed
coordinate is only A_a itself; all other requested indices were already
fixed. There is no aggregate upper bound on these representatives in
the self-sized-radix parent.

After this lift compute H_0, q=(BH_0)^K, every genuine power output,
and all digit witnesses. The parent's uniform bound J<=H_0^(2^22)
still applies; it does not assume representatives smaller than N^2.
Only now compute the doubled frame W. This ordering avoids a circular
choice of q, h, W or the CRT precision.

Set A=X_W(W+1)>0. Since W is even, A is odd. The recurrence gives
Y_W(W+1)=W modulo 2W, so z=(Y_W(W+1)/W-1)/2 is an integer satisfying
the retained odd frame (2). Choose every principal pair canonically,
in particular U=X_h(A), C=Y_h(A).

Let k_* be the largest other requested index. Pell doubling and growth
give Y_{2k_*+1}(A)>(4A-2)Y_{k_*}(A)^2. In view of (9), W>15, and
A>W^W, this implies C>W+sum_{i != anchor}Y_{k_i}(A)^2. Hence the
nonnegative slack in (1) exists. Choose its ternary representation.
The pooled quotient exists because Y_{k_i}(A)=k_i modulo A-1.

To construct the auxiliary pair with an odd quotient, take l=hC and

    H=X_l(A),       J_c=Y_l(A)=C Y_C(U).

The binomial expansion of the Pell unit gives an integer T with

    Y_C(U)=C U^(C-1)+(U^2-1)T,
    J_c/C^2=U^(C-1)+(A^2-1)C T.

The quotient is a positive odd integer: A and U are odd, while A^2-1
is even. Thus e=(J_c/C^2-1)/2 is an integer. This supplies the new
odd auxiliary equation for every anchor h, with no even-h assumption.
The older package 132 used even cap indices; the even frame here makes
the unrestricted semantic-index application valid.

Finally define D by (4), and set S=X_h(D), Q=Y_h(D). These are signed
integers satisfying the comparison norm. Polynomial base transfer and
(5) give both congruences in (6), so their unrestricted quotient witnesses
exist. No CRT choice of a comparison center remains. Fill the genuine
power quotients, unchanged front guards and ordinary gate values.
This is a zero of the new source.

Thus a finite refutation gives a new-source zero, and Sections 2-6 prove
the reverse implication. The construction may replace all private old
Pell witnesses; it does not claim a bijection fixing those old witnesses.

## 8. Exact finite compilation and reproducibility

The rebuild starts at the literal accepted factored parent source. Its
Horn factoring is already part of that input's calibration; no new Horn
factorization is performed. `source_change.json` enumerates all removed,
modified and appended rows. The independent checker reconstructs the
whole transformation from the frozen input and named interfaces.

Then integral monic projection removes only a row z-Q=0 with an integer
polynomial restoration and substitutions that leave every row quadratic.
Every one of the 216 eliminated coordinates is restored in the checked
certificate. All 94 omitted unconstrained coordinates are verified absent
from the remaining rows and may be restored arbitrarily. The retained
coordinate order is checked exactly. Final integer translations are
bijections old=new+constant, independently substituted into every row.

The checker independently expands all 204 squared residuals, compares
every collected integer coefficient, measures the whole endpoint and
the literal 324-variable parent, and rejects deliberate corruptions of
the source change, projection and final coefficient list. It imports no
producer, optimizer or translation helper. The rebuild command additionally
regenerates the final mathematical files in a fresh directory and compares
their bytes; it does not overwrite the released endpoint.

All these are finite checks. Classification of Pell solutions, growth,
the ternary representation theorem, unbounded digit decoding and the
syntactic logical calibration are supplied by ordinary mathematical
proofs. Finite checking is not advertised as deciding Con(ZFC).
