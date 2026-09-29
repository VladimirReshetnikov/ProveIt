# Merged state and junk masks: a modular repetition obstruction

The complete 102 construction has four program fields. Replacing them
by one combined Boolean word and its complement has a plausible
99-operation ledger, but the proposed independent program-typing
implication is **false**. Section4 constructs an infinite positive
counterfamily for the merged program equations, even with fixed union
support and a separated low-copy band. The small exhaustive checks in
Section3 find no alias at their tested heights; modular repetition
explains why those finite results cannot prove the general implication.
The complete 101 doubled successor is a separate, independently audited
result.

## 1. Candidate interface and its precise missing implication

Retain positive C and V and compute F=C+V in one addition. Shift the
fixed ROM coefficient and g together by a sufficiently large power of
three. This leaves the represented finite graph unchanged and puts all
correct product junk above every state position. Include the state
positions in the forbidden-junk set.

One possible support word is the fixed numeral

    U = union over all legal single-row transitions of
        support(Crow+Vrow).

It contains the state positions and every legitimate junk position.
All are on the fixed exponent grid. Enlarge the paid fixed-width
threshold to put U, KS, gS and the other fixed row products below R.
Supply the same positive width slack as before. The proposed program
pair is

    UH-F, F.

The original route, with its already typed sign and nozero words, is

    (RK-g)C = gI(q-1)+R(V+hs*Kplus+hz*D).

Equivalently, after using F=C+V,

    [R(K+1)-g]C = gI(q-1)+R(F+hs*Kplus+hz*D).                 (1)

Here K+1 is a fixed numeral, so the equivalent form changes no route
operation count. Keeping positive V is significant: a cap on F gives
C<F and V<F before either word is separately typed.

If the combined mask yields Boolean F supported in UH, the missing
conclusion is that C is itself Boolean and supported on SH, and that
V=F-C is the correct Boolean junk. Positivity and C<F do not establish
digitwise containment. A large integer can be smaller than F while
occupying positions where F has zero digits.

With the new pair in positions eight and nine, the prospective packed
expression is

    X=Kminus+q²[D+q²(A0+q²(A1+q²F))],
    P=(q-1)X+(1+q²)(H+q^4 t)+q^8 UH.

Four Horner steps replace five; the high offset loses one product and
one addition, while computing F adds one addition. The net saving is
two products and one addition. The power chain q²,q^4,q^8,q^10 still
costs four products. This gives the proposed ledger99=52M+47A from102.
It is an arithmetic ledger, not a complete source or universality
certificate. The independent support implication above is refuted
below. This note does not give a false solution of all raw-counter
equations, so it does not claim to exclude every stronger argument
using the complete proposed system.

## 2. What the low copy does and does not currently prove

Choose the shift so that every coefficient of K is divisible by
Qcopy=3^b, where Qcopy exceeds all fixed state words, and the only
allowed F positions below b are the state positions. In an exact
single-row identity, reduction modulo Qcopy would expose the low copy
of C. This blocks the simplest wrong-next-state substitution into a
cross-junk position below the correct junk band.

The eliminated integer equation does not initially give exact row
identities. Its initial congruence gives only

    C = I mod(R/g),

provided R and g are powers of three. An initial R-block may still
contain a high alias at a multiple of R/g. Multiplication by K can
move such an alias into later rows. A proof must exclude these complete
chains, rather than assuming that global C<F implies a bound on each
row of C.

For example, writing the base-R multiplication carries explicitly
gives a lower carry bound, but the backwards coefficient equation
also contains the next carry multiplied by R. Discarding that term
does not justify a uniform small bound on all C rows. No such
backwards bound is claimed here.

## 3. Exact bounded controller checks

The companion `../verification/explore_merged_program_word.py` tests
controller-only versions of (1), with no sign or zero channels. It
uses positive C,V=F-C and the exact fixed union support U. For every
legal edge i to j it constructs

    Frow=(K+1)3^(a_i)-g3^(a_j),

checks that this is Boolean, and takes the union of its positions.
The state exponents are separated Sidon sets on a spacing-two grid;
the count block has enough capacity for each tested graph. All junk
lies strictly above the state positions, and R exceeds the fixed
row-product bounds.

For a fixed height u, q=R^u, put M=R/g and

    A=M(K+1)-1.

Since gcd(M,A)=1 and M(K+1)=1 mod A, existence of an integer C in (1)
is exactly the congruence

    F = -(K+1)I(q-1) mod A.                                (2)

Every Boolean support word F is a subset sum of known powers of three.
The checker enumerates both halves, indexes their residues modulo A,
and matches (2). It then reconstructs C by exact division, checks the
original route and 0<C<F<q, and tests the initial residue and complete
state support. Thus the finite conclusions are exhaustive; they are
not based on a search cutoff.

| Fixed graph | Height | Allowed words | Exact solutions |
|---|---:|---:|---:|
| Two-state directed cycle | 2 | 16,384 | 1 |
| Two-state directed cycle | 4 | 268,435,456 | 1 |
| Three-state directed cycle | 2 | 4,294,967,296 | 0 |

Both accepted solutions are the expected supported state histories.
The final case correctly has no cyclic return after two steps. The
total is 4,563,419,136 support words, represented by 164,096 enumerated
half sums. These cases do not include raw counters, variable height,
arbitrary compiled graphs, or the Pell coordinates.

Earlier bounded SMT attempts with broader free grid support returned
`unknown` at their time limit. They provide no nonexistence evidence
and are excluded from the positive verification receipt.

## 4. An infinite positive program-level counterfamily

Use the maintained six-state program of102, with its eight legal edges,
and shift K,g,hs,hz together by3^456. The least exponent in the shifted
K is548, above all state exponents. Let U be exactly the union of the
correct merged row words for the eight legal edges. It has111 positions.
This is the strongest fixed allowed set compatible with all those
correct rows: no extra globally safe forbidden position removes a word
used below.

Write c_i=3^(a_i) and I=c_0. Form a six-row block whose source states
are0,1,2,3,4,5. In each row use the correct merged row word, but choose
virtual successors

    1,2,3,4,5,3.

The last virtual edge5 to3 is legal. It does not match the next copy's
first source0. Its sign flags are+++---; its true-zero flags are011000,
and its nozero flags are100111. All four global flag words are positive
and typed when this block is repeated. Each individual merged row is
canonical, so it and its complement in U are Boolean.

Choose any sufficiently large grid-aligned R=3^m; width1960 is the
checker example. In particular require R>2U, RI>c_5, and R divisible
by g. For this one block define

    Cseed=sum_(j=0)^5 c_j R^j,
    Fseed=sum_(j=0)^5 f_j R^j,
    Oseed=hs*Kplus_seed+hz*Dseed,
    T=R/g,  d=(K+1)T-1,  Delta=R^6(c_3-I).

Every f_j is its correct combined row word. In particular
Fseed>Cseed>0. Exact elimination of the single wrong wrap gives

    Nseed := T(Fseed+Oseed)+I(R^6-1)
           = d*Cseed-Delta.                                 (3)

Here c_3>I, so Delta>0. Also Nseed>0 directly from its positive
definition. Thus

    0<Nseed<d*Cseed<d*Fseed.                                 (4)

The checker verifies(3) and(4) at the actual shifted fixed constants;
they are identities and positivity statements, not search results.

The integer d is coprime to R. Let ell0 be the multiplicative order
of R^6 modulo d, and choose

    k=2d*ell0,
    q=R^(6k),
    G=1+R^6+...+R^(6(k-1)).

Since R^(6ell0)=1 mod d, the geometric sum consists of2d blocks
with the same residue modulo d. Hence d divides G. Also q-1=(R^6-1)G
is divisible by d. These are finite effectively constructible integers;
their astronomical size is not treated as an uncharged arithmetic
instruction or as a numerically instantiated witness.

Repeat Fseed and the four typed flag blocks by G, and set

    F=Fseed*G,
    C=Nseed*(G/d),
    V=F-C.

Equation(4) proves positive integral C,V. Equation(3) proves exactly

    dC=T(F+hs*Kplus+hz*D)+I(q-1),

which is the divided form of the proposed merged route(1). The words
F and UH-F remain Boolean. The flag pairs sum to the same row-head
repunit H, and every fixed row-width and F<q bound holds. Taking an
even repetition count also avoids an odd-duration escape.

Yet the separate state/junk interpretation cannot hold. If C were a
Boolean state word and V a Boolean junk word avoiding state positions,
the low-copy band of each F row would force

    C=Cseed*G.

The actual value is strictly smaller:

    C=Cseed*G-Delta*(G/d).

Thus at least one of the required separate typing properties fails.
This is not merely a bad initial residue: Delta is divisible by R^6,
so the first six R-blocks of C are unchanged. The defect occurs later,
through the inter-row arithmetic that a local low-copy argument omits.

The exact checker records the six-state/eight-edge row construction,
all111 allowed positions, positive typed flags, identity(3), strict
inequality(4), and696 finite coprime base/modulus checks of the geometric
repetition lemma. The general order argument supplies the unmaterialized
repetition. The complete raw-counter time equation is outside this
counterfamily; in particular, no full99-operation universal false
positive is asserted.
