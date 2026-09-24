# A conditional tag-halting verifier with eleven Boolean fields

The joint marker construction gives an exact finite-history interface for
the binary productions `0 -> 0` and `1 -> u`, with a fixed positive
deletion number beta and a nonempty fixed word u. The interface below
uses **33 operations, 14M+19A, and eleven Boolean fields**. This count
includes the transition arithmetic and three boundary inequalities.
It excludes the implementation of the Boolean masks, power geometry,
strictly positive adapters for zero fields, and conversion of an ordinary
numerical query into an initial tag word. It is therefore a conditional
history component, not a new universal certificate or a replacement for
the established 90-operation construction.

Unlike a list of local transition identities, the theorem proves that
the packed equations describe one common history with the specified
initial word and a terminal short queue. An apparent suffix after the
first real halt may be discarded.

## 1. Fixed coefficients and supplied geometry

Let a be the length of u and U its little-endian ternary value: symbols
are zero or one, and the first symbol is the least significant digit.
Define fixed numerals

    K=3^beta, Khalf=K/3, B=3^(a-1), c=(Khalf-1)/2.

Here the name Khalf is only a label for the fixed quotient by three.
None of these definitions involves a variable exponent or an uncharged
operation on a witness. Choose a fixed power C of three satisfying

    C > K^2+U+B+1.

Assume the supplied geometry is `R=3^m`, `q=R^t`, with t>=1, and
`H=(q-1)/(R-1)`. Supply positive A and pay for `C*A=R`. This implies
that A is a power of three. The independent realization of q,R,H is
outside the component count.

The initial parameters Ninit,Linit describe one specified binary word:
Linit=3^ell, Ninit is Boolean ternary and below Linit, and ell>=beta.
In particular the initial queue is long enough to take a step. This
encoded-word input contract is not a free conversion of an arbitrary x.

## 2. The fields and equations

Use the joint marker component from `EXPLORATION_JOINT_ROW_MARKER_SELECTION.md`:

    S0+S1=H,
    2Q0+S0=M0, 2Q1+S1=M1,
    G=Q0+Q1+A*H,
    M0+M1=L, Qsum=Q0+Q1, C*A=R.

G and Qsum are computed registers. Mask exactly these eleven words
as nonnegative Boolean ternary integers below q:

    Q0,Q1,S0,S1,M0,M1,G,N,Nbar,E,Ebar.

Add

    N+Nbar=Qsum,
    E+Ebar=c*H, d=3E+S1,                              (1)
    R(N-d+U*M1)=K(N-Ninit+q*Nfinal),                 (2)
    R(M0+B*M1)=Khalf(L-Linit+q*Lfinal).              (3)

Nfinal is nonnegative, Lfinal is positive, and three positive slacks
give the paid boundary conditions

    Linit+alphaI=A,
    Lfinal+alphaH=K,
    Nfinal+alphaN=Lfinal.                            (4)

All other supplied words in this component may be zero. There is no
unspoken positive-domain restriction on them.

The joint lemma gives a length marker L_j=3^ell_j<=A in each row,
one head bit S1_j, and M1_j=S1_j*L_j. It also gives
Qsum_j=(L_j-1)/2. The first equation in (1), with its two Boolean
words, therefore says that N_j is precisely a binary word of length
ell_j, allowing leading high zero symbols. The second equation makes
E a subset of the fixed beta-1 lower positions in each row. Consequently
d_j=3E_j+S1_j is Boolean, below K, and has first digit S1_j.

## 3. Recovering one history without row carries

To decode (2), use its equivalent equation with nonnegative terms:

    R(N+U*M1)+K*Ninit = K*N+R*d+K*q*Nfinal.          (5)

The joint masks give N_j<A/2, M1_j<=A and d_j<K/2. The initial bound
gives Ninit<Linit<A, and the terminal bounds give Nfinal<Lfinal<K.
Since A>=1 and C>K^2+U+B+1, every coefficient on either side of (5)
is below R:

    N_j+U*M1_j < (U+1)A < R,
    K*N_j+d_(j-1) < K(A+1)/2 <= K*A < R,
    d_(t-1)+K*Nfinal < K^2 < R,
    K*Ninit < K*A < R.

At the lowest row this proves N_0=Ninit. At all higher rows it proves
exactly

    K*N_(j+1)=N_j-d_j+U*M1_j,

with N_t=Nfinal. No quotient word or separate successor array is
assumed. The two appearances of N come from the same packed integer.

Similarly rewrite (3) as

    R(M0+B*M1)+Khalf*Linit = Khalf*L+Khalf*q*Lfinal.

Every coefficient is below R: M0_j+B*M1_j<=B*A<R because exactly one
marker channel is active, Khalf*L_j<=Khalf*A<R, and the initial and
terminal terms meet the bounds above. Thus L_0=Linit and

    Khalf*L_(j+1)=M0_j+B*M1_j,

with L_t=Lfinal. Equivalently,

    K*L_(j+1)=3L_j+(3^a-3)M1_j.                    (6)

Dividing by the fixed factor three before forming (3) saves one
multiplication compared with the undivided length equation.

## 4. Exact eventual-halting equivalence

The terminal bound L_t<K gives a least j<=t with L_j<K. The initial
contract ensures j>=1. For every i<j, the queue length exponent is at
least beta, so L_i and M1_i are divisible by K. The recovered content
equation implies d_i=N_i modulo K. Since 0<=d_i<K, this is exactly
the deleted beta-symbol prefix, and S1_i is the actual first symbol.

Equations (2) and (6) now give the ordinary tag successor: remove that
prefix and append zero, or append u, according to S1_i. Induction
therefore identifies the first j transitions with the real run.
L_j<K means its resulting queue is short, so the actual system halts.
No interpretation of later rows is needed.

Conversely, suppose the actual system halts after t>=1 steps from the
given initial word. Choose A, and hence R=C*A, large enough to exceed
every length marker in the run and Linit. Form the marker fields from
the genuine source lengths and read bits, take N to be the source
content words and Nbar=Qsum-N, and set E_j=(d_j-S1_j)/3 from the actual
deleted prefixes. All eleven fields are Boolean and nonnegative.
Use the actual last content and length for Nfinal,Lfinal. The final
queue is short and Nfinal<Lfinal, so all three slacks in (4) are
positive. The local equations telescope to (2)-(3), proving existence.

Thus, for every valid initial word of length at least beta, halting is
equivalent to the existence of the stated geometry and eleven-field
witness. The general first-short-queue reasoning also explains why
some admissible witnesses can extend past the actual halting time.

## 5. Arithmetic and evidence boundary

The shared marker schedule costs ten operations. The content partition
costs one addition. The deleted-prefix interface costs four operations:
cH, E+Ebar, 3E, and d=3E+S1. Equation (2) costs eight operations by
factoring both sides as displayed; equation (3) costs seven. Finally
(4) costs three additions. The total is

    10+1+4+8+7+3 = 33 = 14M+19A.

There are twelve free source comparisons. The companion
`../verification/explore_tag_queue_history.py` expands all twelve
residuals against a fresh symbolic source, checks all eleven fields on
actual halting histories, and compares with direct word rewriting.
It also materializes a three-row witness for `00 -> 0` that continues
formally through an empty queue and back to a short queue; the real
halt occurs after its first transition. This is an intentional check
of the eventual-halting contract, not an exact-duration claim.

Finite step cutoffs in the regression leave longer runs unclassified.
Neither those tests nor the proved conditional history interface establish
a raw-input universal family. The Boolean predicate, noncircular packed
bounds, geometry and positive adapters must still be composed and counted.
