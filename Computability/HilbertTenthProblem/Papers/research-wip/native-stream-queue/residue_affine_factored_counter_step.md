# Factored residue-affine steps with paid counter zero tests

A positive complementary residue witness improves the generic scalar
residue-affine graph from **6b+1 to 4b+3 operations**. It also improves the
standalone shortcut-Collatz graph from eight to **seven operations**.

A separate construction compiles a fixed counter program directly into a
one-number residue-affine map. Its complete one-step graph costs
**10B+8=(5B+1)M+(5B+7)A**, where B counts instruction branches, with
**six positive witnesses and five equations**. This avoids enumerating the
much larger combined residue modulus. It certifies the selected control
state, decrement guard, zero guard, and numerical update together.

These are scalar components. The constructed computational substrate is
universal on an explicit prime-power input code; its connection to the
ordinary queried input and its finite iteration are still unpaid. No
complete universal bound below75 follows.

## 1. A positive slack replaces the selector-root product

For a fixed b>=2 let

    f(n)=a_r floor(n/b)+d_r, r=n mod b,

be a map from positive integers to positive integers. The coefficients may
be nonunit slopes, and translations may be signed. As in the
[earlier scalar graph](residue_affine_ancestor_pumping.md), interpolate
integer polynomials P,G of degree at most b-1 after clearing denominators
by one positive fixed integer L:

    P(r+1)=L*a_r, G(r+1)=L*(d_r-a_r).

Supply positive q,s,v and impose

    n+b+1=bq+s,
    s+v=b+1,
    Ly=P(s)q+G(s).                                      (1)

The second equation gives1<=s<=b. The first then gives uniquely
q=floor(n/b)+1 and s=1+(n mod b), including n<b. The last equation is
exactly y=f(n). Conversely those q,s and v=b+1-s are all positive and
satisfy(1). Thus the finite selector range requires one addition and an
additional positive witness; no degree-b root polynomial is needed.

Two padded Horner evaluations cost(2b-2)M+(2b-2)A. Input decomposition
costs1M+2A, the complementary slack1A, and the output equation2M+1A.
The literal graph total is

    4b+3=(2b+1)M+(2b+2)A.                               (2)

All numerator multiplications, including fixed coefficients, are charged.
Signed intermediates are permitted, while all supplied coordinates remain
positive. Summing the squares of the three residuals adds3M+5A, giving a
single polynomial in **4b+11 operations**, with the same three witnesses.

The archived
[shortcut primitive](legacy-untracked/current/1980/EXPLORATION_TWO_BRANCH_COLLATZ_PRIMITIVE.md)
uses

    n+3=2q+s, y+1=(2q)s-q, s in {1,2}.

Replace its two-operation isolated selector test by s+v=3 with v>0.
Computing2q=q+q and sharing it gives **7=1M+6A** for the complete graph
of n/2 on even n and(3n+1)/2 on odd n. Its single sum-of-squares polynomial
costs15=4M+11A. No universality of this shortcut map is asserted.

## 2. A precise universal substrate and its encoded input

Consider a deterministic counter program whose instructions are

    INC(i,j): increment counter i and go to j;
    DEC(i,j,k): if counter i>0, decrement it and go to j;
                otherwise leave it zero and go to k.

There are finitely many nonnegative counters. First normalize acceptance:
replace the intended accepting halt by successive decrement loops emptying
every counter, followed by a fresh terminal state h. Other undefined
instructions, if present, become nonaccepting loops. This finite change
preserves whether an original run reaches the intended accepting halt.

Choose distinct register primes p_i. Choose K greater than the number of
control states and coprime to every p_i; for example use a sufficiently
large prime. Relabel the states inside{1,...,K}. Fill unused labels by an
increment instruction looping at that label. After acceptance, let h also
increment some fixed register and remain at h. We test reaching h before
that subsequent update; this makes the numerical map total.

Encode the configuration with counters c_i and state j as

    P=product_i p_i^c_i, N=K(P-1)+j.                     (3)

This is positive even when every counter is zero. Every positive integer
N has a unique decomposition(3) with integer P>=1 and1<=j<=K, although
its P need not be supported on the designated primes. Define the map on
all such P by the same multiplication/divisibility rules. An increment
multiplies P by p_i; a successful decrement divides it by p_i; a zero
branch leaves it unchanged when p_i does not divide P. All successors
remain positive.

This is a total residue-affine map with modulus

    m=K*product_i p_i.                                  (4)

A residue modulo m determines j and every divisibility guard on P. On a
selected branch the update has rational slope p_i,1/p_i, or1. Thus it
has the form a_r floor(N/m)+d_r, with positive integer a_r. In particular
K divides every a_r, so these are nonunit numerator slopes modulo m.
The coprime-slope ancestor-pumping theorem does not apply.

The universality claim uses a primary source with a precise contract:
[Korec, *Small universal register machines* (1996), Main Theorem(a2) and
Definition2.3](https://www.cs.cmu.edu/~cdm/resources/Korec1996-small-universal-RM.pdf)
provides a fixed strongly universal machine with22 increment/conditional-
decrement instructions. Its program code occupies one input register and
the ordinary argument occupies a second, without recoding that argument
at the register-machine interface. Fix that machine, perform the finite
normalization above, and assign primes2 and3 to its two input registers.
For the fixed code e of a simulated program, the resulting one-number map
starts at

    N_e(x)=K*(2^e*3^x-1)+j_start.                        (5)

It reaches the fixed integer h if and only if that program accepts x:
entering h after cleanup has P=1, hence N=h; conversely N=h has exactly
that state and payload. This statement follows from the explicit
simulation(3), not from a claim about all starting values of a generalized
Collatz map. The code e may be the effective code supplied by Korec's
strong-universality definition.

Equation(5) has a variable exponent. A source proving strong universality
for counter registers does not eliminate this cost after prime encoding.
Our executable fixture below tests the compiler on a small nonuniversal
program; it is not a transcription or execution audit of Korec's full table.

## 3. Factoring the control table instead of enumerating m residues

Split each INC into one branch and each DEC into its positive and zero
branches. Let B be the resulting number of branches after normalization
and filling the K labels. For each branch z=1,...,B record its source I_z,
target O_z, active prime p_z and multipliers A_z,D_z:

| Branch | A_z | D_z | Condition |
|---|---:|---:|---|
| Increment | p_z | 1 | always |
| Decrement | 1 | p_z | p_z divides P |
| Zero | 1 | 1 | p_z does not divide P |

Precompute the fixed offset

    E_z=A_z*(K-I_z)-D_z*(K-O_z).                         (6)

Then the numerical update is simply D_z*y=A_z*n+E_z.
The source control state still has to match I_z, and the zero branch still
needs its divisibility complement. Neither test is omitted.

Interpolate the five columns I,A,D,E,p at1,...,B, and clear all their
coefficient denominators with one positive fixed numeral L. Denote the
resulting integer polynomials by boldface in prose, or by the following
capitalized register names in the equations:

    IT(z)=L*I_z, AT(z)=L*A_z, DT(z)=L*D_z,
    ET(z)=L*E_z, PT(z)=L*p_z.                            (7)

Each is evaluated with a padded degree-(B-1) Horner schedule. All values
outside the selector range may be signed; no condition on them is needed.

Supply exactly six positive existential integers z,v,P,Q,U,V. Define
computed registers

    S=AT(z)+DT(z), H=PT(z)+L-S.

The complete graph consists of five equations:

    z+v=B+1,
    L*n+L*K=L*K*P+IT(z),
    DT(z)*y=AT(z)*n+ET(z),
    H*P+S+PT(z)-2L=PT(z)*Q+U,
    U+V=PT(z).                                         (8)

Here n,y are the positive arguments of the graph. Equality comparisons
and fixed numerals cost no operations. Multiplying by L or LK is paid.

## 4. Full scalar proof, including both guards and positivity

The first equation forces a genuine branch z. Divide the second equation
by L in the mathematical proof. It gives n=K(P-1)+I_z, so the unique source
state and its positive payload are correct. The update equation similarly
reduces to D_z*y=A_z*n+E_z.

Write A,D,p for the unscaled selected table entries, and put

    h=p+1-A-D, Z=hP+A+D-2.

The final two equations of(8) say

    L*(Z+p)=Lp*Q+U, U+V=Lp.                            (9)

They force L|U and hence L|V; no separate scaled-divisibility witness or
multiplication is needed. Since U,V>0, the integer R=U/L satisfies
1<=R<=p-1. Thus(9) is exactly

    Z=p*(Q-1)+R, 1<=R<p.                               (10)

For an increment or decrement branch, A+D=p+1, so h=0 and Z=p-1. Its
guard is always satisfied with Q=1,U=L(p-1),V=L. For a zero branch,
A=D=1, so Z=(p-1)P; since p is prime, p does not divide Z exactly when
p does not divide P. This proves the complete zero test.

For a selected decrement branch, the update equation gives

    p*(y+K-O_z)=K*P.

Because gcd(p,K)=1, integrality forces p|P. Thus a false decrement cannot
pass merely by supplying another y. The next payload P/p is positive,
and the equation gives precisely y=K(P/p-1)+O_z. For an increment, it
gives y=K(pP-1)+O_z. On the zero branch it gives y=K(P-1)+O_z. These
are positive in every case. Exactly one branch is possible at a source
state: INC has one branch, while DEC's two guards are complementary.

Conversely take any genuine one-step update of this numerical map.
Choose its branch z, set v=B+1-z, and use its actual positive payload P.
The first three equations follow. The selected Z is positive: it is either
p-1 or(p-1)P. For each legal branch, Z is not divisible by p. On a
decrement branch its legality is enforced separately by the update equation.
Set

    Q=floor(Z/p)+1,
    U=L*(Z mod p), V=L*(p-(Z mod p)).                    (11)

All six supplied coordinates are strictly positive, and the last two
equations follow. Therefore(8) has exactly the claimed graph, including
small payload P=1 and all states with zero counters. No primality or
prime-support test on a variable integer is assumed.

The coprimality condition on K is essential. Without it, integrality of
the decrement update can be supplied by K even when p does not divide P.
The compiler chooses K to satisfy it, as an ordinary fixed constant.

## 5. Literal arithmetic count

Five degree-(B-1) Horner evaluations cost5(B-1)M+5(B-1)A. The remainder
of(8) has the following literal schedule:

| Block | M | A |
|---|---:|---:|
| Positive selector complement | 0 | 1 |
| Input/control decomposition | 2 | 2 |
| Output update | 2 | 1 |
| S and H, guard division, complementary remainder | 2 | 8 |
| Total after interpolation | 6 | 12 |

Thus the exact padded source costs

    10B+8=(5B+1)M+(5B+7)A.                              (12)

There are five equations and six positive witnesses. Converting these
five equalities to their sum of squared residuals adds5M+9A, for
**10B+22=(5B+6)M+(5B+16)A**. This single polynomial is zero exactly on
the same positive graph. Coefficient-specific simplifications can lower
these literal counts; no optimality is claimed.

For the concrete checker fixture, K=11 and the register primes are2,3,5.
There are B=14 branches, so the factored graph costs **148=71M+77A**, or
162 as one polynomial. Its combined residue modulus is330; applying the
new generic4b+3 graph after fully expanding that table would cost1323.
The comparison is between the stated generic constructions, not a lower
bound on every implementation of this particular fixture.

## 6. Nonunit slopes really escape the previous finite-language bound

A simple independent example shows that the old unit-slope restriction
cannot just be dropped. Take

    f(2q)=q, f(2q+1)=4q+3.

The even branch is pure division, but the odd numerator slope is4 in the
radix2 convention, sharing a factor with that radix. Use the same affine
loader n=2x+1 and target tau=2^h-1, h>=3. Every loaded value is odd, and
all subsequent values satisfy

    f^t(n)=2^t*(n+1)-1.

Consequently the accepted positive input language is exactly

    {2^j-1 : 1<=j<h}.                                  (13)

These finite languages have unbounded cardinality h-1. In particular
h=3 gives{1,3}, whereas the earlier unit-slope theorem permits at most one
finite accepted input for this loader and odd target. The exact formula
proves termination of the membership calculation here; no cutoff is used
to declare unknown trajectories nonhalting. This example is not universal.

## 7. What is still unpaid, and exact evidence

The ordinary positive input x has not been equated to the coded numerical
state in(5) by a counted exponentiation certificate. If a positive value
T=3^x were already certified, the remaining fixed affine loader would use
one multiplication and one addition; that does not certify T=3^x.

Likewise(8) verifies one step. Evaluating its interpolants on a packed
selector integer creates cross products between times. A finite-history
certificate still needs aligned coefficientwise table lookup and products,
positive bounded digit fields, carries, a common finite endpoint, the
initial loader and final point target. Multiplying(12) by an existential
number of steps is not a fixed Diophantine polynomial. No controller or
history cost is hidden in the scalar count.

The [checker](residue_affine_factored_counter_step.py) expands all five
source identities and the single-polynomial identity symbolically. It
checks generated and independently supplied false witnesses for(1),
exhausts selected branch/output alternatives for(8), perturbs each positive
coordinate, and separately simulates counter vectors against the numerical
map. It also verifies affine behavior on every residue class of the fixture
and the exact nonunit finite languages. The fixed fixture is explicitly
nonuniversal; the universal construction is the parametric proof above.
The [receipt](residue_affine_factored_counter_step.json) is checked afresh
by default. From the repository root with the pinned verification dependencies:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_factored_counter_step.py

Independent proof/source review and default replay passed. A separate audit
checked12,360 guard/update cases across K=1,7,11,13 and active primes2,3,5,7,
and verified the cited Korec universality and input definitions. No
proof-assistant formalization or complete universal arithmetic improvement
is claimed.
