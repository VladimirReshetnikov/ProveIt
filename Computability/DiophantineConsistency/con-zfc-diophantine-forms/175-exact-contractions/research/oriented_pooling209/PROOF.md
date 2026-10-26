# A completed five-base reciprocal certificate

This contribution completes a direction explicitly suggested at the end of
the incoming *Reciprocal pooling* report. That report already observed that
weights `n_j` orient distinct signed bases. The new work here is the uniform
five-block height calculation, treatment of temporarily zero bases, the
acyclic bootstrap allowing deletion of the three formerly protected singleton
certificates, and an actual finite polynomial specialization.

No worldwide novelty or global minimum is asserted. The 209-variable equation
is a degree/arity tradeoff, and must be compared with the other new sextics in
the containing submission rather than presented as an undominated record.

## 1. Exact arithmetic theorem

Let W>=258, A be an integer with |A|>W^W, and b=floor(sqrt(W-1)). Consider
at most five integer bases n_j, and at most seventeen requests in total.
Each request has integer proposed output m_i, integer index k_i, and a canonical
signed Pell pair (X_i,Y_i) for parameter A and signed index k_i. Assume

    n_j^2 < W,    m_i^2 < W,    k_i^2 < W.

Thus all absolute values are <=b and b>=16. For a block I_j put

    T_j = 2*A*n_j - n_j^2 - 1,
    H_j = sum_{i in I_j} Y_i*(m_i-X_i),
    S_j = sum_{i in I_j} ((m_i-X_i+A*Y_i)^2-Y_i^2),
    E_j = S_j-2*n_j*H_j.

The products A*Y_i in these expressions are represented by already constrained
coordinates in the literal compiler. Accordingly H_j,S_j are quadratic and
E_j is cubic in the emitted coordinate system. The displayed mathematical
definitions are equal on the retained A*Y_i gates.

Define the ordinary polynomial residual

    R = sum_j n_j*E_j*product_{l!=j} T_l - z*product_l T_l.

No denominator occurs in R. For every nonzero base, sign(T_j)=sign(A*n_j),
since

    |T_j| >= 2|A||n_j|-n_j^2-1 >= 2|A|-W > W^W.

For a zero base, T_j=-1. Thus none of the T_j vanishes. An integer z satisfying
R=0 exists if and only if every request at every nonzero base is the exact
power m_i=n_j^{k_i}. At a unit base negative indices mean the usual integer
unit powers. At a nonunit nonzero base the equality forces k_i>=0. Requests
at a zero base are deliberately left unconstrained by this local theorem.

### Proof of soundness

Let delta_i=m_i-X_i+(A-n_j)Y_i. Direct expansion gives

    sum_{i in I_j} delta_i^2 = E_j-T_j*sum_{i in I_j}Y_i^2.

Consequently R=0 says that sum_j n_j*sum_i delta_i^2/T_j is an integer.
Zero bases contribute exactly zero and may be omitted. Put

    C = product_{n_j!=0} n_j^b,
    d_i = C*m_i - (C/n_j^b)*n_j^{b+k_i}.

The empty product is one; C is nonzero. Each d_i is an integer, because
b+k_i>=0 and C/n_j^b is an integer. The canonical Pell congruence is

    X_i+(n_j-A)Y_i == n_j^{k_i} modulo T_j.

For a negative index the right hand side uses the inverse of n_j modulo T_j;
this inverse exists since T_j=-1 modulo n_j. Multiplying by C gives
C*delta_i == d_i modulo T_j. Hence

    J = sum_{n_j!=0} sum_{i in I_j} n_j*d_i^2/T_j

differs by an integer from C^2*sum_j n_j*sum_i delta_i^2/T_j. Thus J is an
integer. This argument uses no pairwise coprimality of the moduli.

There are at most five nonzero bases. The uniform estimates

    |C| <= b^{5b},
    |C/n_j^b| <= b^{4b},
    |n_j^{b+k_i}| <= b^{2b}

give |d_i|<=b^{5b+1}+b^{6b}<=2b^{6b}. Therefore

    sum |n_j|*d_i^2 <= 68*b^{12b+1} < W^{6b+2} <= W^W.

For the strict middle inequality, b^{12b}<W^{6b}, and
68b<W^2 for b>=16 and W>=b^2+1. For the final inequality use
6b+2<=b^2+1<=W, valid at b=16 and increasing thereafter. Since every
denominator of a nonzero-base term has absolute value greater than W^W,
we obtain |J|<1.

Crucially, n_j/T_j always has the common sign of A. Every nonzero summand
of J therefore has that same sign. Since J is an integer of absolute value
less than one, it is zero, and every d_i is zero individually. Division in Q
by C yields m_i=n_j^{k_i}. If |n_j|>=2 and k_i<0, this would imply the
impossible integer equation m_i*n_j^{-k_i}=1. Thus k_i>=0 at nonunit bases.

### Proof of completeness

For an exact integer power at a nonzero base, the Pell congruence implies
T_j divides delta_i. The square identity gives T_j divides E_j. Therefore
z=sum_j n_j*E_j/T_j is an integer, with zero-base terms equal to zero,
and satisfies R=0. The argument is uniform in all signed-index branches.

## 2. The five blocks of the inherited calculus compiler

The fixed instance has the following bases and numbers of requests:

| Block | Actual base | Requests |
|---|---|---:|
| initial growth | F^2+1 | 1 |
| initial B | B | 1 |
| initial BH | BH | 1 |
| radix | q | 3 |
| radix plus one | q+1 | 11 |

The first three requests are V=(F^2+1)^t, N=B^x, and q=(BH)^x.
The strict horizon t=16+u^2 is retained. The square-frame and signed-Pell
orientation interfaces of package 158 give W=2+sum of the 36 actual affine
atom squares, W>=258, |A|>W^W, and the canonical signed pairs before the
power certificates are interpreted. All seventeen base/index/output triples
belong to that frame. The new compiler deletes no frame, Pell-norm, cap, or
orientation row. This order is essential: the proof does not assume the
positivity of the arithmetic outputs in order to orient their powers.

The local theorem tolerates zero bases, so it can be applied before the
bootstrap knows that q and q+1 are nonzero. Its conditional conclusion will
be used as those bases become known to be nonzero.

## 3. An acyclic nonzero bootstrap

The unchanged common remainder norm has the form

    M^2 = 1+4*(sum of squares)+(a^2+b^2+c(c+1)),

with c an arbitrary integer. Since c(c+1)>=0, it implies M!=0. The retained
ceiling ratio B*r=M implies B!=0. The self-radix multiplier H is an odd
integer, so H!=0 and BH!=0. The base F^2+1 is positive without using any
arithmetic interpretation. Thus the conditional theorem already recovers
all three initial requests.

The normalized ceiling identity and strict common remainder bound give

    |F*B-V| < |B|/2.

Write h=|B|. If h=1 the left side is an integer of absolute value less
than one half, so F*B=V and |F|=V. This contradicts
V=(F^2+1)^t>|F| for t>=16. Thus h>=2. The usual stronger bootstrap bounds
|F|<h and V<h^2 also follow: if |F|>=h, then

    V >= (F^2+1)^2 > F^2+|F|/2 >= |F|h+h/2,

contrary to the displayed ceiling bound; then
V<(|F|+1/2)h< h^2.

Because |B|>=2, the recovered initial request N=B^x forces x>=0. The
recovered request q=(BH)^x implies q!=0. The conditional theorem can now
be used on every q-block request, in particular M=q^x. If x=0, then
M=1, contradicting B*r=M and |B|>=2. Hence x>=1 and |q|>=2, so q+1!=0.
The local theorem now recovers the final block as well.

The retained normalization ratio q^t*v=M=q^x implies x>=t. Thus
|q|>=|B|^x>=2^16, and |q+1|>=2. All nonunit-index sign conclusions required
by the old digit and range decoding are now licensed. The remainder of the
parent's rounded-factorial, CRT, Horn-flow, and finite C222 refutation proof
applies with the same arithmetic equalities as before.

This proof does not use q!=0 or positivity of its representatives to establish
the initial power requests. The initial nonzero facts are purely retained
integer equations and parity. That is what permits deletion of the three
formerly protected singleton power certificates.

## 4. Exact literal compiler and coordinate count

The input is the parent's 218-variable affine projection stage. It still
contains the three singleton modulus and quotient pairs and the two pooled
K,L pairs as private coordinates: ten coordinates and ten residual rows.
The compiler deletes those ten coordinates and rows, then adds z and R.
The result has 209 variables and 146 residuals: 145 retained quadratic
residuals and one residual of exact degree twelve.

The ordinary polynomial is exactly the sum of the 146 residual squares.
The group ports in equation.json are finite sparse ordinary polynomials;
their multiplication in the displayed fixed five-block expression introduces
no additional quantified variables. In particular the reciprocal notation
is only used in the proof, never as an operation of the final polynomial.

The input uses A=stored_shared_A+1. The initial bases are respectively
stored_mul_1+1, stored_choose_0, and stored_BH; the radix is
stored_pow_2-1. These offsets are checked against the actual inherited
modulus and congruence rows. The two pool bases and A are recovered directly
from the coefficients of the original four pool rows, then checked against
the same anchor.

The code additionally retains an explicitly recorded subsequence of integer
row additions from the incoming residual-basis certificate. Both the source
and target of every retained addition avoid the ten private rows. These row
operations are invertible over Z and preserve the common zero set. Skipping
the other additions affects support and coefficient height but not semantics.

The exact total degree is 24. Every base is affine, every modulus quadratic,
and every E_j cubic; hence R has degree at most twelve. On setting every
independent coordinate to an indeterminate t, its degree-twelve coefficient
is 34. Therefore the final sum of squares has degree-twenty-four coefficient
34^2=1156 on this line. The other residuals have degree at most two and cannot
cancel that coefficient. The full expanded support and coefficient height
are not claimed; the factored finite expression completely specifies them.

## 5. Forward and reverse witnesses

On an old zero, each singleton satisfies delta_i=-T_j*q_i. Its contribution
to z can be chosen as n_j*(T_j*q_i^2+Y_i^2). The two old pooled contributions
are n_j*L_j. Thus the forward z is a polynomial in the old witnesses.

On a new zero, the theorem and bootstrap give every true power and therefore
T_j|delta_i. Restore each singleton modulus by its displayed polynomial and
restore its quotient by -delta_i/T_j. Restore each old pool by
L_j=E_j/T_j and K_j=2H_j+(2A-n_j)L_j. These values are integers on the
solution set. The retained equations then give a zero of the old system.
The reverse restoration is not claimed to be a polynomial automorphism on
arbitrary integer tuples; its integrality is a conclusion of the theorem.

## 6. Logical scope

The new arithmetic theorem and finite compiler compose with the named
inherited canonical-Pell/C222/ZF/ZFC calibration. The result is the ordinary
mathematical theorem, formalizable in ZFC, that the literal polynomial has
an integer zero exactly when a finite syntactic ZFC refutation exists.
Negating yields the requested equivalence with Con(ZFC). This supplies no
proof or disproof of consistency and no new end-to-end Lean/Rocq compilation.
Exact finite coefficient tests authenticate the artifact; they do not replace
this unbounded arithmetic proof or the inherited logical calibration.
