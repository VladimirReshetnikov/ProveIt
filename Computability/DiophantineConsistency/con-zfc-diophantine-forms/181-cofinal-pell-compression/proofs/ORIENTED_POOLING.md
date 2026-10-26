# Oriented reciprocal pooling with dormant zero bases

## Result and exact boundary

This note gives a new ordinary arithmetic lemma and a literal specialization
of package 173's direct C222 consistency polynomial. It uses the parent at
ProveIt commit `02a78a08603cbae248c19c23a75907c6c6bd6443`, path
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/173-crt-index-anchor-215/source/anchor221/equation.json`.
The parent has 221 unrestricted integer coordinates and 160 quadratic rows.
Only its ten private power-certificate coordinates and their ten rows are
replaced. Every other source polynomial, index, range, parity, CRT endpoint,
frame, and Pell orientation condition is unchanged.

The five-block construction replaces those ten coordinates by one. Five
inherited common-radical projections and one affine consequence give a
literal polynomial in **206 unrestricted integers**, exact degree **24**,
written as 144 quadratic residual squares and one degree-12 residual square.
The more practical split construction uses two certificates and yields
**207 unrestricted integers**, exact degree **16**, with 144 quadratic
residuals, one degree-8 residual and one degree-5 residual.

All coefficients are given literally by the generated JSON residual lists.
These are size tradeoffs, not quartic records or global variable minima.
The repository already has much smaller variable counts at other degrees
and coefficient regimes. The new unbounded lemma is distinct from the
parent's exact finite algebra; no new Lean/Rocq compilation is claimed.

## 1. General lemma

Let W>=258 be an integer, A an integer with |A|>W^W, and let at most five
integer bases n_j be given. Each block contains requests (m_i,k_i) with
canonical signed Pell coordinates (X_i,Y_i) at parameter A and signed
index k_i. Assume every actual base, output and index satisfies

    n_j^2 < W, m_i^2 < W, k_i^2 < W,

and that the total number of requests r is at most 64. A block is allowed
to have base zero. Set

    T_j = 2*A*n_j - n_j^2 - 1,
    D_i = X_i-A*Y_i,
    S_j = sum_i ((m_i-D_i)^2-Y_i^2),
    H_j = sum_i Y_i*(m_i-X_i),
    E_j = S_j-2*n_j*H_j.

Every T_j is nonzero. If n_j=0 it is -1; otherwise

    |T_j| >= 2*|A|-W > W^W,
    sign(n_j/T_j) = sign(A).

Then

    sum_j n_j*E_j/T_j is an integer                         (1)

if and only if every request in every NONZERO base block has the exact
integer value m_i=n_j^k_i (interpreted first in Q for signed k_i).
For |n_j|>=2 this additionally implies k_i>=0. No assertion about a zero
base block's values is needed or made. Zero base blocks contribute zero
to (1); their elimination is handled by a later bootstrap.

### Proof

Write delta_i=m_i-X_i+(A-n_j)*Y_i. Direct expansion gives

    E_j = sum_i delta_i^2 + T_j*sum_i Y_i^2.                 (2)

Thus (1) is equivalent to integrality of sum_j n_j sum_i delta_i^2/T_j.
Let b=floor(sqrt(W-1)), so b>=16, b^2<W, and every relevant absolute
base/output/index is at most b. Let J be the set of nonzero-base blocks,
s=|J|<=5, and set C=product_(j in J) n_j^b (empty product one). The number
C is nonzero; it is used only in the proof, not as an extra polynomial
variable. For a request in a nonzero block define the integer

    d_i=C*m_i-(C/n_j^b)*n_j^(b+k_i).

Both displayed exponents are nonnegative. The standard signed Pell
congruence

    X_i+(n_j-A)*Y_i == n_j^k_i (mod T_j)

is legitimate also for negative indices, since T_j=-1 mod n_j makes n_j
invertible modulo T_j. Here is the exact recurrence proof, including those
indices. Write U_k=X_k(A)+(n_j-A)Y_k(A). The Pell addition law gives
U_(k+1)=n_j U_k modulo T_j, because (n_j-A)^2=A^2-1 modulo T_j.
Equivalently one can evaluate the unit A+s of
Z[s]/(s^2-(A^2-1)) at s=n_j-A modulo T_j. Its inverse A-s evaluates
to 2A-n_j, and n_j(2A-n_j)=1 modulo T_j. Thus this evaluation respects
every integer power, not merely nonnegative powers, and U_k=n_j^k
in the residue ring. The absolute-value bounds in the preceding paragraph
ensure T_j is nonzero; a modulus of either sign is harmless.

It follows that C*delta_i == d_i mod T_j. Consequently

    L=sum_(j in J) n_j*sum_i d_i^2/T_j

is an integer: by (2), Q=sum_j n_j sum_i delta_i^2/T_j is an integer.
For each active request, T_j divides (C*delta_i)^2-d_i^2. Multiplying
each corresponding quotient by the integer n_j and summing proves
that C^2 Q-L is an integer. Since C^2 Q is an integer, so is L. This
argument uses separate divisibility at each denominator; no pairwise
coprimality of the T_j is assumed.

Now |C|<=b^(s*b), |C/n_j^b|<=b^((s-1)*b), and

    |d_i| <= b^(s*b+1)+b^((s+1)*b) <= 2*b^((s+1)*b).

Hence

    sum_(j in J) |n_j|*sum_i d_i^2
      <=4*r*b^(2*(s+1)*b+1)
      <=4*r*b^(12*b+1)
      <W^(6*b+2) <= W^W.

The strict inequality uses 4*r<=256<W and b^2<W. The last one follows
from 6*b+2<=b^2+1<=W for b>=16. Therefore |L|<1. Every nonzero summand
has the same sign, sign(A), since n_j/T_j has that sign. The integer L
is zero, and each d_i=0. Dividing by C gives m_i=n_j^k_i in Q. If
|n_j|>=2 and k_i<0, the resulting integer equality
m_i*n_j^(-k_i)=1 is impossible. This proves the forward direction.

Conversely, exact powers give T_j|delta_i in every nonzero block.
Equation (2) makes E_j/T_j integral there. Each zero-base term in (1)
vanishes. Thus (1) holds. QED.

## 2. One explicit polynomial certificate

Introduce one integer z and put

    R = sum_j n_j*E_j*product_(h!=j) T_h
        -z*product_h T_h.                                  (3)

All denominators are nonzero under the retained frame. Thus R=0 is
equivalent to (1). No divisibility primitive or variable exponent occurs
in this polynomial. Existing AY multiplication wires make each E_j at
most cubic, each T_j quadratic, and (3) degree at most twelve for five
blocks. Its square has degree at most 24. The emitted residual has exact
degree twelve, verified from its complete collected coefficients.

For the first three singleton blocks, the literal definition is

    E_j=(m_j-D_j)^2-Y_j^2
          -2*n_j*Y_j*(m_j-D_j-Z_j),  Z_j=A*Y_j.

For the two existing fixed-base pools, the two old quadratic rows are

    K_j-2*H_j-(2*A-n_j)*L_j=0,
    S_j-n_j*K_j+L_j=0.

The combination second+n_j*first is E_j-T_j*L_j. The producer checks this
identity exactly and constructs E_j by setting the private K_j,L_j to
zero in that combination. This avoids trusting manual transcription of
the ten-member and three-member request lists.

## 3. The parity bootstrap that makes all five blocks active

The source's five bases, in order, are

    t, B, B*H, q, q+1,

with respectively 1,1,1,3,10 requests, total r=16. Its retained rows give

    t=128+4*h^2, K=t^4, F is the requested t^K,
    C=2*c, B*mu=C+F+1,
    H=2+4*sum(actual CRT representatives),
    q is the requested (B*H)^x.

The source frame and canonical Pell orientation proof are independent of
the deleted power-certificate rows. Thus the new lemma applies with no
initial premise that every base is nonzero.

1. t>=128 is nonzero, so the t-block yields F=t^K. Since t is even and
   K=t^4>0, F is even.
2. C is even by its literal coordinate convention. Therefore C+F+1 is
   odd and nonzero. B*mu=C+F+1 forces B nonzero (indeed odd), without
   any assumption on C's sign.
3. H is 2 modulo four, hence is nonzero and |H|>=2. Therefore B*H is
   nonzero and has absolute value at least two. The active-block
   conclusion yields x>=0 and q=(B*H)^x.
4. If x=0, q=1. If x>=1, q is nonzero and even. In either case q is
   neither zero nor minus one, so both q and q+1 are nonzero.

All five blocks are now active. Every old power congruence follows,
including unit-base boundary cases, without assuming any later positive
radix or range conclusion. All deleted singleton quotients can be restored
as -delta/T; every deleted modulus as its explicit T; and each fixed-base
pool restores L_j=E_j/T_j and K_j=2*H_j+(2*A-n_j)*L_j. These are integers.
Thus an arbitrary new zero restores an old zero with EVERY shared
coordinate unchanged.

Conversely an old zero supplies the new quotient by a polynomial map,
without even invoking the inherited exact-power theorem. For each old
singleton certificate delta_j=-T_j*Q_j, identity (2) gives
E_j/T_j=T_j*Q_j^2+Y_j^2. For the two old pools it gives E_j/T_j=L_j.
Thus choose

    z=sum_(j=0..2) n_j*(T_j*Q_j^2+Y_j^2)
      +q*L_q+(q+1)*L_(q+1).

This expression is an integer polynomial in the old coordinates and
annuls (3) on every old zero. The change is therefore
pointwise existential equivalence over the retained coordinates, not merely
a reconstruction from a canonical refutation witness. No CRT choices,
radix congruences, logical calculus or coefficient tuple are changed.

## 4. A smaller-degree two-certificate companion

Apply oriented pooling only to the first three bases t,B,BH, using z0.
The same parity bootstrap proves q,q+1 nonzero and of the same sign:
two nonzero consecutive integers always have the same sign. Their T_q,
T_(q+1) therefore have the same sign. Use a second integer z1 and the
unweighted reciprocal polynomial

    R1=E_q*T_(q+1)+E_(q+1)*T_q-z1*T_q*T_(q+1).             (4)

The standard two-base proof uses C=(q*(q+1))^b and
|d_i|<=2*b^(3*b); its unweighted numerator is at most
4*13*b^(6*b)<W^(3*b+1)<=W^W. Integrality and a common denominator sign
force every requested error to vanish. This is the consecutive-base lemma
already proved in package168, now composed with the new oriented
three-base certificate. No novel claim is made for that two-base lemma.

The first residual has exact degree eight and the second exact degree five.
Both are added to the unchanged 144 projected quadratic residuals. This
gives a single polynomial of exact degree sixteen in 207 integer variables.
The old-to-new map here is z0=sum_(j=0..2)n_j*(T_j*Q_j^2+Y_j^2)
and z1=L_q+L_(q+1), again polynomial on the old coordinate space.

## 5. Exact finite construction and count

In the literal parent chart, delete only coordinates

    145,146,147,148,149,150,215,216,217,218

and rows

    102,103,104,105,106,107,153,154,155,156.

The producer checks that none of those coordinates occurs in a retained
row. The five block bases and E_j,T_j polynomials are preserved in the
construction certificate. The one-certificate source has 212 coordinates
and 151 rows; the two-certificate source has 213 and 152.

The five inherited radical directions concern syntax coordinates below64.
Every new pooling expression is independent of those coordinates. Each
directional derivative is checked to be a constant in every residual;
the pivot slope is +-1; and its exact restoration polynomial matches the
inherited certificate. The integer shear and its restoration are therefore
inverse on zero sets. The sixth, affine consequence is checked as an exact
integer combination of two retained rows; its pivot coefficient is one.
After substitution the omitted row equals the retained partner row.

The final coordinates all remain unrestricted integers. Squaring and
summing the residuals preserves their simultaneous zero set. A sum of
real polynomial squares cannot cancel its maximum even total degree,
so the exact residual degrees certify the exact degrees of the final
single polynomials without relying on a huge full expansion.

## 6. Calibration and novelty boundaries

The exact source replacement and projections prove the new zero sets
equivalent to the pinned direct C222 polynomial. Composing with the
parent's ordinary Pell, CRT, C222/ZF and ZF/ZFC calibration therefore gives

    ZFC proves: no integer zero iff Con(ZFC).

The same inherited calibration boundaries apply. In particular finite
coefficient verification does not prove an unbounded Pell theorem or
newly compile the full transitive formal logical development. The result
does not decide consistency. The new lemma is the signed orientation of
distinct reciprocal denominators together with dormant zero-base blocks;
the source application uses parity to activate them without circularity.
Package168 had noted a possible multi-base extension but did not compile
it. No claim of worldwide novelty or global optimality is made.
