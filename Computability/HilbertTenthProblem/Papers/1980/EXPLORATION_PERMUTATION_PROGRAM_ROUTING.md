# A 66-operation fixed permutation routing component

The complete fixed-table path verifier in
`EXPLORATION_FIXED_PROGRAM_ROUTING.md` costs 70 operations for an arbitrary
deterministic finite successor map. For a permutation, a more widely spaced
constant table allows one mask field to be omitted. Absorbing a fixed
complement into a numeral saves two more operations. The resulting complete
relation uses **66 operations: 37 multiplications and 29 additions or
subtractions**, with one positive parameter q, 23 positive unknowns, and
16 equations. Numerals and equality comparisons are free. The same
fixed-complement absorption reduces the general routing component to
**68 operations: 38 multiplications and 30 additions/subtractions**.

The precise relation is q=W^t and f^t(i0)=i1 for some t>=1, where f, W,
i0 and i1 are fixed. It is a decidable finite permutation path relation.
It is not a universal counter-machine verifier. The possible value for
a larger compiler is a smaller interface for routing reversible control
ports; counter tests, chosen ports and raw input still need equations.

The full source checker is
`../verification/explore_permutation_program_routing.py`. The 70-operation
predecessor remains unchanged.

## 1. Fixed constants and the exact normalized target property

Let f be a fixed permutation of an odd number m>=3 of states, with no
fixed points. Fix initial and final states i0,i1. These hypotheses are
restrictions of this component, not conclusions inferred from its equations.
Any finite permutation can be phase-split into (i,epsilon) with transition
(f(i),1-epsilon), eliminating fixed points. Adjoining a disjoint three-cycle
makes the state count odd without changing paths in the original component.
The doubled phase still has to match the chosen endpoint; no uncharged
existential choice of endpoint phase is assumed here.

Choose a positive integer l with 3^l>m+1 and set

    a_i=l*3^i, d=max_i a_i,
    S=sum_i 3^(a_i), g=3^d,
    K=sum_i 3^(d+a_f(i)-a_i),
    I=3^(a_i0), F=3^(a_i1).

All these values are fixed numerals. The a_i form a Sidon set: equality
of two sums of two a_i determines the same unordered pair. The exponents
of K are nonnegative and distinct. If two differences a_f(i)-a_i and
a_f(j)-a_j agreed for distinct i,j, the Sidon alternatives would require
two fixed points, which are excluded.

Choose a fixed even B and W=3^B such that

    W>max((K+g)*S, 2S+1).                         (1)

The stronger sum bound, rather than separate bounds on KS and gS, will
exclude carries between rows in a sum used below. Increasing these fixed
numerals costs no arithmetic instructions.

For any source subset U, let c_U=sum_(i in U) 3^(a_i). Before radix-three
normalization the coefficient of K(T)c_U(T) at d+a_j is exactly

    1 if f^(-1)(j) belongs to U, and 0 otherwise.  (2)

Indeed a term lands there precisely when a_i+a_f(k)=a_j+a_k. The Sidon
alternatives give k=i and f(i)=j, or i=j and f(k)=k; the second is
excluded. The permutation hypothesis then ensures at most one contribution.

Every exponent in the whole product is a multiple of l. Every coefficient
is at most m, since each of the m monomials of K can contribute at most
once to an exponent. After adding gS, every coefficient is at most m+1.
Writing the products in radix 3^l, these coefficients are already digits,
because m+1<3^l. Consequently no coefficient carries into the next
multiple of l. In ordinary ternary notation, the normalized digit at each
target d+a_j is therefore still (2), and in Kc_U+gS it is one plus (2).
This remains true for malformed rows containing several selected states.
It is stronger than the single-monomial target fact used by the predecessor.

## 2. All positive source equations and their count

Supply positive H, C, V, TestC, TestV, alpha and the seventeen
positive variables of `EXPLORATION_BASE_THREE_PELL_KERNEL.md`. The sole
parameter q is an arbitrary positive integer. Impose

    q=(W-1)H+1,
    TestC=C+[((W-1)/2)-S]H,
    V+(gS)H=TestV,
    (WK-g)C+gI=(gF)q+WV,
    TestC+TestV+alpha=q.                          (3)

The coefficients ((W-1)/2)-S, WK-g, gS, gI and gF are fixed integer
numerals, with the first strictly positive by (1). These five equations
take thirteen arithmetic instructions: two for geometry, four for support
comparisons, five for routing, and two for the shared bound.

In the predecessor, the source support used the supplied Rep and the
equations Rep=((W-1)/2)H and C+Rep=SH+TestC. Eliminating Rep and combining
the fixed coefficients removes one product and one addition. Every new
positive tuple has exactly one positive extension to the old equations,
namely Rep=((W-1)/2)H=(q-1)/2. Conversely every old tuple yields (3) by
forgetting Rep. Thus this absorption is an exact witness bijection. Below,
Rep always denotes that mathematical value and is not a supplied variable
or an uncounted register. The source checker verifies the elimination
identity as well as the new direct source comparisons.

The new packing is only

    P0=C+q TestC+q^2 TestV.                       (4)

It requires two multiplications and two additions in Horner form. V is
still a positive supplied variable and participates in (3); its Boolean
mask is the one being removed. Append the existing 49-operation mask
and Pell component with

    L=q^4, D0=9L, r=D0-3P0-1.                    (5)

The fourth q-chunk in (5) is the constant zero, requiring no packing
operation or extra supplied variable. The component tests Boolean digits,
so this zero chunk is allowed. Its eleven equations and full positive
Pell construction are unchanged. The total is 13+4+49=66, and the exact
primitive histogram is 37M+29A. All sixteen fresh source residuals are
checked, including the inherited acyclic Pell norm correction.

## 3. Bounds and support before using routing

Positivity and (1),(3) give q>=W and Rep=(q-1)/2. Also SH<Rep because
2S<W-1. Thus

    0<C<TestC<q, 0<V<TestV<q.                     (6)

These are consequences of counted equations, before decoding powers or
digits. In particular (4) gives 0<P0<q^3<q^4, so the existing mask's
range hypotheses are paid. Its soundness implication, which does not
require parity, proves that q is a power of three and C,TestC,TestV are
ternary Boolean words below q.

Since W=3^B and W-1 divides q-1, q=W^t for some t>=1. Hence H is the
base-W repunit of length t and Rep is the full ternary repunit below q.
The equality TestC=C+(Rep-SH) is then a carry-free sum of Boolean words.
It proves that C is supported on SH. Each C row is a subset of the fixed
source positions, bounded by S. No Booleanity of V or one-hot condition
has been assumed.

## 4. Recover the initial row and the mathematical successor word

Reduce the routing equation modulo W. Since q is divisible by W and g
divides W, the first row c0 of C satisfies c0=I modulo W/g. By (1),
both c0 and I are at most S<W/g; therefore c0=I as integers.

Define, for the proof only,

    Next=(C-I+qF)/W.

This is a positive integer consisting of the later rows of C followed
by the singleton final row F. It is Boolean, supported on SH and below q.
Substitution into (3) gives exactly

    KC=g Next+V,
    TestV+g Next=KC+(gS)H.                       (7)

There is no reversal of an unjustified cancellation modulo g. The
division in the displayed definition is a mathematical deduction from
the established first row and is not a certificate instruction.

Both summands on the left of the second equation in (7) are Boolean,
so their ternary sum has digits at most two and no carry. Every row
of the right side has value at most (K+g)S<W by (1), so it has no carry
between time rows. Within a row, Section 1 gives the exact normalized
target digits even for a source row with several states.

Let U_j be the subset encoded by row j of C and U_(j+1) the corresponding
Next row, with U_0={i0} and U_t={i1}. At the target for state k, equation
(7) now reads

    bit_k(TestV)+1_(k in U_(j+1))
      =1+1_(f^(-1)(k) in U_j).                   (8)

Since the TestV bit is zero or one, (8) implies

    f(U_j) is a subset of U_(j+1).

The permutation preserves cardinality. Therefore the sequence |U_j|
is nondecreasing, starts at one and ends at one. Every row has exactly
one state and every inclusion is equality. This proves f^t(i0)=i1.
Only after this conclusion does KC become a rowwise shift of the Boolean
numeral K, and V is inferred to be its Boolean junk part. That inference
explains why its original mask was redundant in this restricted setting.

For a noninjective successor function, different current states could
merge and offset a falsely added head. The cardinality proof would fail.
The claim in this note is explicitly limited to permutations.

## 5. Every positive witness and the three-field parity

Conversely assume q=W^t with t>=1 and f^t(i0)=i1. Put the actual singleton
state rows into C and their successors into Next, and set

    V=KC-g Next,
    TestC=C+Rep-SH, TestV=V+(gS)H,
    alpha=q-TestC-TestV.

As in the predecessor, each row of KC has exactly m distinct one digits
and exactly one lies at a tested target. Thus V has m-1 nonzero junk
digits per row, is Boolean and is positive. Both Test fields are Boolean
and positive. Each is at most Rep, so alpha>=1. All other outer variables
are positive and every equation (3) holds.

Because m is odd and powers of three are odd, V has parity
(m-1)t=0 modulo two. Also Rep=((W-1)/2)H is even since B is even. From
the two support equations,

    C+TestC+TestV=2C+V+Rep+(g-1)SH,

so the sum of the three fields is even. With q odd, P0 is even, and
r=9q^4-3P0-1 is even. Thus the existing positive Pell converse applies
without an extra parity field or equation. It supplies all seventeen
Pell variables, completing all twenty-three positive unknowns.

The proof uses the mask's unchanged hypotheses q>=3 and 0<=P0<q^4,
all already established in (6). The unused highest q-chunk creates no
exception to its Boolean theorem or its central-binomial valuation.

## 6. Verification boundary and compiler use

The checker independently compares all fresh source polynomials with the
66 acyclic primitives. It checks normalized target digits on every subset
for every fixed-point-free permutation of three or five states, including
rows with no head or several heads. Its canonical histories check all
outer equations, positive slacks, parity and the factorial valuation of
the complete mask. Its adversarial two-row enumeration omits the V mask
and imposes no one-hot test during acceptance; it checks that the complete
remaining mask rejects every false path in the tested set. The fresh
regression covers 46 permutation tables, 7,088 normalized subset-target
checks, 904 canonical histories, and 52,352 adversarial subset histories,
with exactly sixteen accepted paths.

These finite checks supplement the general proof. No huge Pell tuple is
materialized; its existence follows from the retained positive converse.
The relation is a finite permutation path predicate and is decidable.
It does not improve the 90-operation universal bound.

If the frame radix W is replaced by a variable counter-frame radix R,
the two operations constructing RK-g must be counted and the enlarged
bound R>(K+g)S must be derived from equations. The coefficient
((R-1)/2)-S also stops being fixed. With a counter history's existing
repunit J, the support equation becomes C+J=SH+TestC and costs three
operations rather than two. Geometry may be shared, but the fixed-frame
count cannot be transferred merely by adding the two routing operations.
Moreover, chosen control
ports must be linked to the actual counter tests. The smaller mask
interface is a possible component of that larger construction, not a
claim that those tasks have been completed.

## 7. The same absorption gives general routing in 68 operations

For an arbitrary fixed deterministic graph, keep the four original fields
C,V,TestC,TestV and the original no-fixed-point phase construction of
`EXPLORATION_FIXED_PROGRAM_ROUTING.md`. Keep all its constants and proof
hypotheses. Replace only its first support equation and supplied Rep by
the exact elimination in Section 2. The resulting count is

    13 outer operations+6 packing operations+49 kernel operations
      =68=38M+30A.

It has the same one parameter q, twenty-three positive unknowns and
sixteen equations as the permutation variant, but the mask still includes
V. Its endpoint relation is exactly the predecessor's relation by the
positive witness bijection. It needs neither the permutation hypothesis
nor the spaced-exponent modification. Its four-field parity argument
continues to use Rep=(q-1)/2 as a proof abbreviation.

The same checker verifies a separate complete 68-operation schedule and
all sixteen fresh polynomials for this variant. It reruns the predecessor's
1,036 target-coefficient checks, 96 canonical histories and 16,384
adversarial source-subset histories. No new representation theorem is
inferred merely by replacing the number 70 with 68; the witness elimination
proves the exact equality of their positive solution relations.
