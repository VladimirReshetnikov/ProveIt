# A single bounded-error Pell row

Research note for the ProveIt construction at commit
`f4d8db99e060339f3306a04d507c35bc1d0d68c5`. This is a new ordinary arithmetic
lemma, not a new calculus calibration or a claim of global optimality.

## Stronger version: the same row also orients every abscissa

Under all hypotheses below, use instead

    V = W + sum_i [(X_i-1)^2 + (Y_i-e_i)^2] + (A-1)Q,
    Q >= 0.                                                   (R+)

Then the conclusion strengthens to the complete canonical pair

    X_i=chi_A(e_i)>0,  Y_i=psi_A(e_i)>0.

The soundness proof below first applies unchanged: dropping the
nonnegative abscissa-error squares gives the same bound j_i<=B.
Write X_i=sigma_i chi_A(j_i), sigma_i in {+1,-1}. Reduction modulo
A-1 uses chi_A(j)=1 modulo A-1 and gives

    A-1 divides E_plus = sum_i [(sigma_i-1)^2
                               +(epsilon_i j_i-e_i)^2].

Its complete bound is

    0<=E_plus<=m[4+(W-1)^2]
                <=(W-2)[4+(W-1)^2] < W^3 < A-1.

The strict middle inequality follows from

    W^3-(W-2)[4+(W-1)^2] = 4W^2-9W+10 > 0.

Consequently E_plus=0, which simultaneously forces sigma_i=1 and
epsilon_i j_i=e_i>0. Thus both signs are oriented without a separate
guard for any principal seed coordinate.

For completeness put z=psi_A(B-1)>=1. The actual error sum satisfies

    E_actual_plus <= m[chi_A(B-1)^2+psi_A(B-1)^2]
                    <=m(A^2+1)z^2.

Since psi_A(B)>A z and chi_A(B)>(A-1)psi_A(B),

    V=psi_A(2B)>2(A-1)A^2 z^2.

Therefore

    V-E_actual_plus > { [2(A-1)-m]A^2-m }z^2 > W,

using A>W+1 and m<=W-2. Each chi_A(e_i)-1 and psi_A(e_i)-e_i
is divisible by A-1, and V-W is too. Hence

    Q=(V-W-E_actual_plus)/(A-1)

is a positive integer, furnishing explicit complete witnesses for (R+).

### Consequence for signed power outputs

After (R+) has oriented a true principal pair at exponent e, the
standard power congruence with a syntactically positive base n gives

    m = n^e modulo T_n,  T_n=2An-n^2-1.

Suppose the square frame already gives |m|<W, 1<=n<W, and 1<=e<W.
Then n^e<=W^(W-1) and

    |m-n^e| < W+W^(W-1) < W^W < T_n.

Thus the congruence forces m=n^e>0 even if the raw output m was signed.
This removes the need for selectively doubled exponents and squared
outputs at THIS interface. It does not remove the source sign
hypotheses needed to show the actual bases and exponents positive in the
first place, and it does not by itself alter the other arithmetic-source
constraints. The complete original power request list must be restored
and audited under whichever compiler uses this consequence.

All terms in (R+) remain quadratic in the actual stored coordinates
when the requested e_i are affine. There is no multiplication by an
unknown weight inside an error before squaring.

## Exact theorem

For an integer A >= 2 write

    (A + sqrt(A^2-1))^j = chi_A(j) + psi_A(j) sqrt(A^2-1).

Let W=2B >= 4, A-1 > W^3, m <= W-2, and let the requested indices
e_1,...,e_m satisfy 1 <= e_i < B. Retain one complete indexed-Pell
certificate at index W, with principal pair (U,V), and retain every
hypothesis of that certificate except its separate inequality V>=W.
In particular, the private certificate witnesses must obey their actual
inherited domain conditions. The following assertion does not authorize
making those private witnesses signed.

For each i retain only the principal norm

    X_i^2 - (A^2-1)Y_i^2 = 1,

where X_i,Y_i may be arbitrary integers. Replace both a separate shared
upper-bound row and a separate pooled congruence row by the single row

    V = W + sum_i (Y_i-e_i)^2 + (A-1)Q,        Q >= 0.       (R)

Then every solution satisfies

    V = psi_A(W),
    Y_i = psi_A(e_i) > 0,
    X_i = +/- chi_A(e_i).

Conversely every collection of these principal pairs extends, by fresh
anchor witnesses and a nonnegative Q, to a solution. The converse holds
under the stated assumptions; it only uses A>W+1 for its size estimate,
which follows from A-1>W^3.

Thus the one row certifies both the true positive ordinates and their
indices. It deliberately leaves each abscissa sign unresolved. Any later
power graph must orient that sign using its own proved argument.

## Soundness

Because A-1>0 and Q>=0, (R) first gives V>=W. The retained indexed-Pell
criterion can therefore be applied without circularity and yields
V=psi_A(W). Principal Pell classification gives, for each i,

    |X_i|=chi_A(j_i),  Y_i=epsilon_i psi_A(j_i),  j_i>=0,

where epsilon_i is either sign (the sign is immaterial if j_i=0).

Put y=psi_A(B) and x=chi_A(B). We have y>=B, x<=Ay, and
x>(A-1)y. The first inequality follows from Pell growth; the second
follows by squaring from x^2=(A^2-1)y^2+1<=A^2y^2; the last follows
from sqrt(A^2-1)>A-1. Consequently

    psi_A(B+1)=Ay+x>(2A-1)y,
    V=psi_A(2B)=2xy<=2Ay^2.

If j_i>=B+1, then, for either sign of Y_i and e_i<=B-1<=y-1,

    |Y_i-e_i| >= psi_A(B+1)-e_i > (2A-2)y+1.

For A>=2, (2A-2)^2>=2A, including equality when A=2. Hence

    (Y_i-e_i)^2 > 2Ay^2 >= V.

But (R) implies sum_i(Y_i-e_i)^2<=V-W<V. This contradiction proves
0<=j_i<=B.

The Pell recurrence reduced modulo A-1 gives psi_A(j)=j mod A-1.
Reducing (R), and using V=psi_A(W)=W mod A-1, proves

    A-1 divides E := sum_i(epsilon_i j_i-e_i)^2.

Since j_i<=B and 1<=e_i<=B-1, every absolute error is <=2B-1=W-1.
Therefore

    0 <= E <= m(W-1)^2 <= (W-2)(W-1)^2 < W^3 < A-1.

Thus E=0 and each epsilon_i j_i=e_i>0. It follows that the actual
ordinate has positive sign and exactly the requested index.

No individual ordinate sign, index lower bound, or individual index
quotient was used. No bounds on the huge ordinates modulo A-1 were
assumed: the bounded quantities are their recovered signed indices.

## Constructive completeness

Choose the true principal ordinates Y_i=psi_A(e_i), either sign of
X_i=chi_A(e_i), and the true anchor at W. Let z=psi_A(B-1)>=1.
Because e_i<=B-1 and psi_A(e_i)>=e_i,

    E_actual := sum_i(psi_A(e_i)-e_i)^2 <= m z^2.

Also

    psi_A(2B)=2chi_A(B)psi_A(B)
              >2(A-1)psi_A(B)^2 >2(A-1)z^2.

Consequently

    V-E_actual > [2(A-1)-m]z^2 > W.

The last inequality uses A>W+1 and m<=W-2. The numerator
V-W-E_actual is a positive integer divisible by A-1, because
psi_A(W)=W mod A-1 and every psi_A(e_i)-e_i is divisible by A-1.
Thus

    Q = (V-W-E_actual)/(A-1)

is a positive integer and satisfies (R). The inherited completeness
theorem supplies fresh private anchor witnesses. They are not identified
with witnesses from another coefficient specialization.

## Why the actual square frame supplies the half-index interval

The Round15 signed architecture defines

    W = 2 * (2 + sum_{a in atom set} a^2).

For every integer atom k,

    W - 4|k| >= 4+2k^2-4|k|
                = 2(|k|-1)^2+2 > 0.

Therefore every selectively doubled target e=2k, k>=1, satisfies
2e<W. An undoubled positive target e=k does too. These conclusions are
syntactic and precede the interpretation of every power request. Each
target must be traced to its actual atom; an arbitrary expression not
occurring in the frame cannot silently use the bound.

For a natural-domain architecture with the original frame
W0=2+sum(atoms), use W=2W0 instead. Every positive seed atom e then
satisfies e<W/2. This only changes the affine frame equation. Its
large-A certificate must of course use this new W everywhere.

The usual frame norm

    A^2 - ((W+1)^2-1)(W Z)^2 = 1,  A>=0, Z>=1,

supplies A>=chi_(W+1)(W)>=(W+1)^W, and hence A-1>W^3 for W>=4,
before any power-output semantics. This statement is inherited from the
shared-power frame, with the complete frame restored before use.

## Polynomial realization and counting boundary

(R) is quadratic in actual stored coordinates when each e_i is affine
in a stored coordinate, as for e_i=k_i or 2k_i. Over unrestricted
integers one may impose Q>=0 through the ordinary Legendre identity

    Q = a^2+b^2+c(c+1),  a,b,c in Z.

Keep Q as a wire if necessary so that (A-1)Q remains quadratic. Direct
substitution of the quadratic expression for Q into that product would
make the row cubic and must not be called a quartic SOS construction.

Relative to a two-row signed cap using a nonnegative gap and a free
pooled quotient, the new construction has one aggregate row and one
nonnegative quotient. Exact variable/support/height gains depend on the
whole compiler and must be measured from its actual emitted equations.
No count is claimed in this note.

## Scope and dependence

Only the preceding arithmetic reduction is new here. Application to
Con(ZFC) still requires the full inherited finite-power, arithmetic-source,
and numerical C222/ZFC-refutation calibration. A finite checker of the
emitted polynomial verifies syntax and identities, not this unbounded
semantic proof by itself.
