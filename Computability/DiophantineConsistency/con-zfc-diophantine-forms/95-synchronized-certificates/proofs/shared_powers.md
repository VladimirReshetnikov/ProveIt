# Simultaneous positive-power certificates

## Scope and interfaces

The construction concerns a finite acyclic circuit of natural addition,
multiplication, positive exponentiation, and the previously proved arithmetic
macros built from them. At every intended power call the base `n` and exponent
`k` are at least one. In soundness, exponent positivity is a separate static
fact about the actual arithmetic syntax. Base positivity follows directly
from its defining equation 2An=T_n+n^2+1: a zero base makes its right side
positive and left side zero. Thus a factorial output used as a power base
does not require prior semantic verification of the factorial. All power
graphs can be proved correct simultaneously, before proving binomial and
factorial correctness, provided the exponents are syntactically positive.
The specialized graph does not represent zero-base powers or exponent zero.

The inherited Pell-index theorem is
`DiophantineConsistency.PellRepresentation.criterion_iff_pell`. The proof
below also uses the standard classification of nonnegative solutions to
X^2-(a^2-1)Y^2=1 by Pell powers at the fundamental solution (a,1).
The full inherited exponentiation theorem is not required: the synchronized
frame supplies its own exponential bound. No universal Diophantine
polynomial is used.

Let X_k(a),Y_k(a) be defined by X_0=1,Y_0=0 and

    X_{k+1}=a X_k+(a^2-1)Y_k,
    Y_{k+1}=X_k+a Y_k.

For a>=2 these are natural and satisfy X_k^2-(a^2-1)Y_k^2=1.

## One dominating Pell frame

For the finite set of distinct semantic atoms occurring as a base, exponent,
or output of a power call, impose

    W = 2 + sum(atoms),    Z=z+1,
    A^2 - W^3(W+2) Z^2 = 1.                         (F)

All variables are nonnegative integers. Consequently W>=2, Z>=1, and
A^2>W^4. Thus A>W^2 and, for every power call,

    1 <= n,k <= W,    0 <= m <= W,    A>=2.

For each distinct base n define a natural T_n by

    2 A n = T_n+n^2+1.

Then T_n>m. Indeed n>=1, n<=W and A>W^2 imply
T_n>=2A-W^2-1>W^2-1>=W when W>=2 (the last inequality
holds at W=2 and above). Thus the local output-gap and upper-bound witnesses
of the old power graph can all be restored as natural differences.

The norm in (F) is exactly

    A^2 - ((W+1)^2-1)(W Z)^2 = 1.

For soundness we need the stronger exponential bound. The classification of
Pell solutions writes A=X_j(W+1), WZ=Y_j(W+1). Reduction of the recurrence
modulo W gives X_j(W+1)=1 mod W and Y_j(W+1)=j mod W. Thus W divides j.
Since WZ>0, j>0, and therefore j>=W. The first recurrence gives
X_{j+1}(W+1)>=(W+1)X_j(W+1), hence

    A >= (W+1)^j >= (W+1)^W > W^W >= n^k.

Because 1<=n<=W<A, the quadratic 2An-n^2-1 is increasing over this
integer interval, and

    T_n >= 2A-2 > W^W >= n^k.                       (B)

Thus both the proposed output m and the true value n^k lie in [0,T_n).

Completeness is simultaneous, not a collection of unrelated local existence
claims. First evaluate the intended finite semantic circuit, and then set W
to its displayed finite sum. At Pell base b=W+1, the recurrence gives
Y_j(b)=j modulo W: reduce the recurrence modulo W and induct from (1,0).
Choose A=X_W(W+1) and Z=Y_W(W+1)/W. The latter is a positive integer.
The norm holds, and hence all required inequalities follow as above. The
apparent references to power outputs in W introduce no semantic circularity:
the circuit's intended outputs are chosen before the auxiliary Pell frame.

## One index certificate per distinct exponent

At each exponent k choose X,Y,U,V,S,R and q>=0, and put

    B = 1+4Y(q+1).

Impose

    Y=k+e,
    X^2-(A^2-1)Y^2=1,
    U^2-(A^2-1)V^2=1,
    S^2-(B^2-1)R^2=1,
    V=Y^2(v+1),
    B=A+U b,
    S=X+U s,
    R=k+4Y r,                                      (I)

with all additional variables natural. Since k>=1, Y>=1 and B>=5.
Forgetting the nonnegative quotient orientations gives exactly the original
Matiyasevich index certificate. It follows that X=X_k(A), Y=Y_k(A).

Conversely, suppose these are the true Pell coordinates. The existing index
completeness theorem supplies U,V and a B in the simultaneous residue classes
B=A mod U and B=1 mod 4Y, with V>0 and Y^2|V. Raise B by a sufficiently large
multiple of 4YU to arrange B>=A and B>1. Replace S,R by X_k(B),Y_k(B).
The coordinate recurrence is polynomial in the base, so S=X mod U. Also
Y_k(1)=k, so R=k mod 4Y. The Pell recurrences have nonnegative coefficients
in a and a^2-1 when evaluated for a>=1; induction gives monotonicity in the
base. Hence S>=X, and Y_k(B)>=k. These facts supply natural b,s,r.
Finally B>1 and B=1 mod 4Y imply (B-1)/(4Y)>=1, yielding q.

Only the exponent k determines this certificate after A is fixed, so its
entire witness family is shared among all power calls with that exponent.

## One-sided power quotients

For each call m=n^k, with the already shared T_n, X_k(A),Y_k(A), impose

    X_k(A)+nY_k(A) = A Y_k(A)+m+T_n h,    h>=0.     (P)

For soundness, the index graph has already identified X=X_k(A),Y=Y_k(A).
The recurrence identity below shows X-(A-n)Y=n^k modulo T_n. Equation (P)
therefore gives m=n^k modulo T_n. Both numbers are nonnegative and strictly
less than T_n by (F) and (B), so m=n^k as ordinary integers.

For completeness define H_j=X_j(A)-(A-n)Y_j(A). Direct substitution into
the two Pell recurrences gives the exact identity

    H_0=1,    H_{j+1}=n H_j+T_n Y_j(A).

Therefore

    H_k-n^k = T_n sum_{j=0}^{k-1} n^(k-1-j)Y_j(A).

The sum is a nonnegative integer, and it is precisely the witness h in (P).
No signed quotient or offset is needed for any power/index congruence.

## Remaining general congruences

For any remaining finite family L_i=R_i mod M_i, use one shared natural
offset C and one natural q_i per congruence:

    L_i+M_i q_i = R_i+M_i C.

If M_i>0, write delta_i=(R_i-L_i)/M_i and choose
C>=max(0,-delta_1,...,-delta_s), q_i=C+delta_i. If M_i=0, the congruence
means L_i=R_i and any natural q_i is admissible. This proves exact
equivalence. The offset is applied only to general outer congruences;
the oriented power/index equations above are smaller.

## Polynomial materialization and internal provability

Every expression above is built from natural additions and multiplications.
One quadratic residual enforces each multiplication gate and each displayed
equality, with square gates for Pell norms. Taking the sum of the residual
squares produces an ordinary quartic. The inherited exporter may eliminate
a monic affine gate only when its restoring affine expression has
nonnegative integer coefficients; such substitution preserves natural
solutions and quadratic residual degrees.

All arguments use finite recurrences, natural induction, finite maxima,
polynomial identities, divisibility, the established Pell-index theorem and
standard Pell-solution classification. They can be carried out in ZFC's internal natural numbers, without
assuming consistency or arithmetic soundness of ZFC. They are ordinary
mathematical proofs; no new checked Lean derivation or sealed object-ZFC
proof object is claimed.
