# A single projector and increasing length flow for tag halting

Status: **verified conditional component**, with **32 operations =
14 multiplications + 18 additions/subtractions**, ten Boolean ternary fields,
and eleven equality comparisons. Omitting the three explicitly counted boundary
sums leaves **29 operations = 14 multiplications + 15 additions/subtractions**.
The author, root, and independent affine reviewer each completed a full proof
and source review and a fresh complete verification run without findings.
This improves the separate 33-operation / eleven-field interface in
`EXPLORATION_TAG_QUEUE_HISTORY.md`. That predecessor is unchanged.

The theorem here concerns an already encoded binary input word. Boolean-mask
realization, power geometry, conversion of nonnegative words to strictly positive
unknowns, and conversion of a raw numerical input into the encoded word are
external obligations. In particular, 32 is not a universal Diophantine bound.
The proof accepts certificates containing an arbitrary suffix after a real
halt; it does not assert that every encoded row is a legal tag step.

## 1. Interface and exact arithmetic

Fix a deletion number beta >= 1 and a nonempty binary word u of length a.
The tag rules are 0 -> 0 and 1 -> u. First symbols occupy the least significant
ternary positions. Compile the fixed integer numerals

    K = 3^beta,  Khalf = K/3,  Af = 3^a,  B = Af/3,
    U = sum(u_i 3^i),  c = (Khalf-1)/2.

Choose a fixed power of three C satisfying

    C > max(K, Af, 2U+3).                                      (1)

These powers and quotients are fixed program numerals, not variable operations.
Assume the external power geometry

    R = 3^m,  q = R^t,  H = (q-1)/(R-1),  t >= 1.

The input parameters encode a specified binary word w of length ell >= beta:

    Linit = 3^ell,  Ninit = sum(w_i 3^i).

The ten masked, nonnegative, length-mt Boolean ternary words are

    Q, S0, S1, M0, M1, G, N, Nbar, E, Ebar.                    (2)

Each is less than q and has only digits 0 and 1. All may be zero. G is a
computed register to which a mask condition is applied. The variables A and
Lfinal are positive; Nfinal is nonnegative. The three boundary slack variables
are positive. L is an unmasked coordinate defined by M0+M1; neither L nor the
terminal Lfinal is assumed to be a marker word.

The projector and length-sum equations are

    CA = R,  G = Q+AH,  S0+S1 = H,
    2Q+S1 = M1,  M0+M1 = L.                                  (3)

The word containment and deleted-prefix equations are

    2(N+Nbar)+H = L,
    E+Ebar = cH,  d = 3E+S1.                                  (4)

The two packed transitions and boundary equations are

    R(N-d+U M1) = K(N-Ninit+q Nfinal),                         (5)
    R(M0+B M1) = Khalf(L-Linit+q Lfinal),                      (6)
    Linit+alphaI = A,
    Lfinal+alphaH = K,
    Nfinal+alphaN = Lfinal.                                   (7)

Here d is computed and unmasked. Equations (7) pay for Linit<A,
0<Lfinal<K, and 0<=Nfinal<Lfinal. The last two are conditions on ordinary
integers; no terminal digit condition is silently supplied.

The exact schedule is in `explore_single_projector_tag_history.py` and its JSON
receipt. Its operation groups are:

| Group | Multiplications | Additions/subtractions | Total |
|---|---:|---:|---:|
| Projector, guard, and L in (3) | 3 | 4 | 7 |
| Containment in (4) | 1 | 2 | 3 |
| Prefix in (4) | 2 | 2 | 4 |
| Content transition (5) | 4 | 4 | 8 |
| Length transition (6) | 4 | 3 | 7 |
| Three boundaries (7) | 0 | 3 | 3 |
| **Total** | **14** | **18** | **32** |

G=Q+AH and d=3E+S1 are computed directly, so there are eleven supplied-coordinate
equality comparisons. In particular, the division of the ordinary length
transition by the fixed numeral 3 in (6) is exact and uses no variable division.
The complete symbolic source check covers every comparison and the length-flow
identity used below.

## 2. The single projector

Adding two Boolean ternary words cannot create a ternary carry. Thus
S0+S1=H makes them complementary subsets of row heads. Write s_i for the unit
digit of S1 in row i.

The same observation applied to G=Q+AH implies that Q has a zero at every
row's A-position. Recall that A=R/C is a power of three. Consider 2Q+S1=M1
from the low end of a row, with incoming carry zero. With incoming carry zero,
a Q digit 1 would produce the forbidden M1 digit 2. With incoming carry one,
a Q digit 1 gives output zero and retains carry one, whereas a Q digit zero
gives output one and ends the carry. Therefore:

* if s_i=0, Q_i=M1_i=0;
* if s_i=1, Q_i=(3^j-1)/2 and M1_i=3^j for some 0<=j<=log_3 A.

The forced zero at the A-position ends any carry before the row boundary.
Induction gives this conclusion for every row, including the last one. In
particular M1_i is either zero or a single marker at most A. This argument puts
no bound of that kind on M0_i and does not assume L_i is a marker.

The prefix equation likewise has no ternary carries. It confines E and Ebar
to the lowest beta-1 positions of each row, numbered 0 through beta-2 starting
at its head. Thus 3E occupies positions 1 through beta-1, disjoint from S1.
Hence every d_i is a Boolean prefix with

    0 <= d_i <= (K-1)/2 < K,  d_i mod 3 = s_i.                 (8)

For beta=1, c=0 and both E and Ebar are identically zero; their nonnegative
domain explicitly allows this case.

## 3. The global length equation is a single increasing unit flow

Let T0=R/Khalf and T1=B T0, used only in the proof. Both are positive powers
of three strictly greater than one. Substituting L=M0+M1 into (6) gives

    M0+M1+q Lfinal = Linit+T0 M0+T1 M1.                      (9)

Equation (9) is a literal equality of ternary coefficients, not merely an
equality after normalization. On the left, M0 and M1 have coefficients at most
one and positions below q; q Lfinal has positions at or above q, with ordinary
ternary coefficients at most two. On the right, each shifted word has
coefficients at most one. Their lowest possible position is T0, whereas
Linit<A<T0 by (1). Thus every coefficient on both sides is at most two.

Regard a bit of M0 at exponent e as a directed edge from e to
e+log_3 T0, and a bit of M1 as an edge from e to e+log_3 T1. The initial marker
is the unique unit source, and the digits of q Lfinal are sinks. All edges
strictly increase the exponent. Coefficient equality is flow conservation.

Induction through the exponents shows that there is exactly one unbranched
path. A vertex with no incoming unit and no initial source has no outgoing
edge and no sink; a vertex with one incoming unit must pass it along one edge
or absorb it in one unit sink. It cannot branch or acquire a second unit.
All M0 and M1 bits belong to this path. Since Lfinal>0, it ends in exactly one
sink of coefficient one. Consequently Lfinal is a power of three, and M0 and
M1 have no common occupied position. This proves the terminal marker property
from an arbitrary integer 0<Lfinal<K.

The path need not place exactly one marker in each R-row after a short marker.
No such conclusion is used.

## 4. The prefix before the first short marker is causal

For a path node in row i, let its marker be L_i=3^ell_i. The initial node has
ell_0=ell>=beta. As long as ell_i>=beta, a zero-channel edge advances to row
i+1 and changes the exponent to ell_i+1-beta. A one-channel edge changes it to
ell_i+a-beta. Both new exponents are nonnegative (in fact at least one).

There is also no overflow past the next row. The stronger invariant

    K L_i < R                                                (10)

holds initially because Linit<A and C>K. A zero-channel step gives
K L_(i+1)=3L_i<=K L_i. A one-channel step has L_i<=A by the projector and
gives K L_(i+1)=Af L_i<=Af A<R by (1). Thus every step before a short node
advances exactly one row. The global path is increasing, so later nodes
cannot add another marker to any of these earlier rows.

Let j be the first path node whose within-row length exponent is less than
beta. Such a node exists: if none occurred earlier, the path would reach its
terminal node in row t, where Lfinal<K. Therefore j>=1, and each source row
i<j has exactly the marker L_i, with

    M1_i=s_i L_i,  M0_i=(1-s_i)L_i.                           (11)

At row j itself there may be additional later path nodes in that same row.
The proof does not identify the full encoded L-row or N-row there with the
first short marker or with an actual halted word.

## 5. Containment and actual content on the causal prefix

N and Nbar are Boolean words, so N+Nbar has literal ternary coefficients at
most two and no carries between rows. Write b_i=N_i+Nbar_i<=R-1. In a row
i<j with zero incoming carry, containment says

    2b_i+1 = L_i + R epsilon,  epsilon in {0,1}.

Both 2b_i+1 and L_i are odd and R is odd; hence epsilon=0. Starting at row
zero proves, throughout the causal prefix,

    N_i+Nbar_i=(L_i-1)/2,  0<=N_i<= (L_i-1)/2.                (12)

This proves that N_i is the value of a binary word of length ell_i, including
leading zero symbols. In particular K N_i<R/2 by (10).

Reducing (5) modulo R first yields
K(N_0-Ninit)=0 mod R. Since L_0=Linit<A<R/K and both values satisfy (12),
N_0=Ninit.

Now proceed through rows i<j. After the preceding coefficient equalities have
been removed, (5) implies

    N_i-d_i+U M1_i = K N_(i+1)  (mod R),                     (13)

where the final N_(i+1) can denote the supplied Nfinal if i+1=t. At this stage
it is enough to reduce (13) modulo K. R is divisible by K, and the current
marker L_i is divisible by K; thus (8) and (11) imply

    d_i=N_i mod K.                                           (14)

In particular s_i is the actual first symbol. Equation (14) is established
before treating the trimmed content as nonnegative; a possible signed borrow
has not been assumed away.

For i<j-1, both content rows have (12). After (14), the two nonnegative sides
of (13) are strictly below R:

    K N_(i+1)<R/2,
    0<=N_i-d_i+U M1_i <= N_i+U A < R/(2K)+U R/C < R.

Consequently (13) is the exact scalar tag-content transition. This inductively
identifies all N_i for i<j with the actual computation from w.

For the final genuine source i=j-1, equation (14) still holds without any
bound or decoding assumption on the following encoded content row. It fixes
the actual symbol and deletion prefix. The corresponding length edge already
produces a length below beta, so this real step halts. No identification with
the possibly noncausal encoded row j is required. This proves soundness for
eventual halting, including certificates with later self-supported rows.

## 6. Every actual halt has a certificate

Take any actual halting run from the specified word w, stopping at its first
halt, with t>=1 steps. Choose a power of three A strictly larger than every
source length marker and Linit; set R=CA and q=R^t. In each source row use its
actual first symbol s and marker L_i, and set

    M1_i=s L_i,  M0_i=(1-s)L_i,
    Q_i=s(L_i-1)/2,
    Nbar_i=(L_i-1)/2-N_i,
    E_i=(d_i-s)/3,  Ebar_i=c-E_i.

S0 and S1 are the complementary heads. Q has no A-position, so G=Q+AH is
Boolean. All ten words are nonnegative Boolean words below q. The actual
scalar transitions telescope to (5) and (6), and the three slacks in (7) are
strictly positive. This proves the converse and the exact conditional
equivalence to eventual halting.

No parity constraint for a later Pell kernel is part of this component.
Nor is the cost of realizing the assumed powers R and q included.

## 7. Verification and evidence boundary

The companion checker independently expands all eleven source residuals,
checks the complete 32-instruction schedule, and verifies the exact flow
identity. It constructs all ten masks and all equations for 944 directly
observed halting runs, containing 2,318 source rows. The other 428 runs reach
the stated 20-step test cutoff and are left unclassified.

The maintained noncausal example uses beta=2, u=100, initial word 00, formal
source words 00, 0, and the empty word, then final word 0. Its three formal
rows satisfy this new interface, although the actual computation halts after
one step. This checks that the theorem has the intended first-halt scope.

The finite adversarial test exhausts Q words satisfying their Boolean guard,
all complementary head choices, all admitted initial length markers, and
**every integer** 1<=Lfinal<K, at seven specified width/height/appendant
configurations. M0 is solved uniquely from the exact length equation; all
accepted length words are independently decoded as increasing unit paths.
For each accepted length word it further enumerates every Boolean splitting
of (L-H)/2, all deleted-prefix words, and all possible valid encoded inputs
through the unique modulo-R/K residue. It solves Nfinal from the exact content
equation and checks every remaining comparison and mask. These bounded checks
corroborate the general proof; they are not a substitute for it. The JSON
receipt contains per-configuration counts and the complete operation list.
The aggregate gate checks 385,024 guarded-Q/head candidates, 3,328 endpoint
trials (including 2,496 nonmarker terminals), 28 accepted length words, and
2,688 full-content candidates. The 30 accepted complete certificates all have
a genuine halting prefix; 18 include rows after that halt.
