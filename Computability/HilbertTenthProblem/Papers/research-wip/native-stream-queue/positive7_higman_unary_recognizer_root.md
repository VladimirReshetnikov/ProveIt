# A finite Higman expression for the universal unary index set

This note supplies a finite Higman-operation expression for a concrete
universal unary set U. It fixes the program enumeration, gives a literal
counter-machine loader for n=2^e(2x+1), and constructs accepting histories
using finite-support block conditions. Substitution into the frozen
commutator-pattern construction therefore supplies its previously missing
E_U input. No general recursively-enumerable-set-to-H-expression existence
theorem is needed for this step.

The finite benign pair, named finite presentation, actual universal relator
count and positive7 matrix list remain to be constructed. An H-expression
is not a Diophantine arithmetic circuit, so this note claims no numerical
equation bound. The strong universality of the retained Korec table is an
imported foundation, with the precise source/interface scope below.

## 1. Primitive conventions and completely finite notation

E is the integer-valued functions on Z with finite support. A k-tuple is
supported at indices 0,...,k-1, with zeros elsewhere. The bases are
Z={(0)} and S={(a,a+1):a in Z}. Union and intersection are binary operations.
The unary primitives are

    rho:   f(i)=g(-i);           sigma: f(i)=g(i-1);
    tau:   exchange 0 and 1;     theta: f(i)=g(2i);
    zeta:  agree with g except at 0;
    pi:    agree with g at every i<=0;
    omega_k: every aligned k-block of f, read as a k-tuple, lies in A.

For rho,sigma,tau,theta,zeta,pi, g is one witness in the input set A. In omega_k,
each block may have its own witness. Every output remains in E. These are
the actual definitions in [Mikaelian, Sections 2.2--2.3](https://arxiv.org/pdf/2002.09728v6).
In particular rho reflects indices, not values; omega_k is a single allowed
operation for each fixed positive k.

Composition acts right to left. Use only these derived macros:

    sigma^-1 = rho sigma rho;
    zeta_i = sigma^i zeta sigma^-i;
    T_i = sigma^i tau sigma^-i;
    Left = rho pi rho;
    Right_j = sigma^j pi sigma^-j;
    Box_F = zeta_F Z,       Box_d = Box_{0,...,d-1};
    Block_d(A) = Right_(d-1) Left A intersect Box_d.       (1)

Fixed powers and finite unions/intersections mean literal finite iteration.
zeta_F is a finite product; its factors commute. Left frees negative sites,
Right_j frees sites >j, and T_i swaps adjacent sites i,i+1. Hence Block_d
extracts exactly the first d coordinates from a *single* witness in A.
For the converse, patch that witness outside the block in two stages; both
patches have finite support. This proves the macro even when A itself has
no uniform support bound.

For a tuple set A supported inside a fixed finite F and nonempty I subset F,
define

    Keep_(F,I)(A) = zeta_(F minus I) A intersect Box_I.   (2)

This existentially forgets the other coordinates and replaces them by zero.
It does not require their original values to have been zero.

Only unary and binary relation cylinders are required. For a unary set A
and a binary set B, put F={0,...,d-1} and define, for 0<=i<j<d,

    Unary_d(A;i) = zeta_(F minus {i}) sigma^i A;
    Pair_d(B;i,j)
      = zeta_(F minus {i,j}) T_(j-1)...T_(i+1) sigma^i B. (3)

The swap product is empty when j=i+1. Its rightmost swap acts first, so
it moves B's second coordinate from i+1 to j while keeping the first at i.
For reversed arguments use Pair_d(tau B;j,i). These formulas impose exactly
the indicated relation and free all remaining sites of the d-window.
Every atom below has distinct argument sites. A conjunction/disjunction
means finite intersection/union of (3); no arbitrary relation, coordinate
copy, unbounded union or extra logical closure is added to H.

## 2. Equality, nonnegativity and fixed constants

The following short equality relation was supplied independently by
Aristotle during this construction:

    Eq = theta (zeta_2 S intersect zeta sigma tau S).     (4)

The intersection consists of (a,a+1,a); theta keeps sites 0 and 2, so
Eq={(a,a):a in Z}. A similarly direct finite-chain construction gives the
nonnegative integers without assuming an order primitive:

    V = omega_2 (zeta_1 Z union tau S);
    N = Block_1(V intersect sigma^-1 V).                 (5)

For every adjacent pair in a witness h, either h(i)=0 or
h(i+1)=h(i)-1. A negative entry would force a forever negative decreasing
tail, contradicting finite support. Conversely the finite string
n,n-1,...,1, followed and preceded by zeros, realizes every n>=0; n=0 is
the all-zero string. Thus N={(n):n>=0} exactly.

Set

    Next(A) = theta (tau S intersect zeta sigma A);
    C_0=Z,  C_(k+1)=Next(C_k) for k=0,...,30;
    Pos=Next(N).                                        (6)

The intersection is (a+1,a) with (a) in A. Consequently C_k={(k)} and
Pos={(n):n>0}. Recursion in (6) stops at the displayed fixed numeral 31;
it is finite abbreviation expansion, not a variable-length computation.
The relations used later are only C_k, N, Pos, Eq and S.

## 3. A fixed enumeration and a literal unary loader

Let K be the following retained U21 table, with eight nonnegative registers
R0,...,R7. I r t increments Rr and goes to t. D r t z decrements a positive
Rr and goes to t; when Rr=0 it leaves it unchanged and goes to z.
T r t z branches on the same condition without changing any register.
State 0 is the start; state 21 is the sole halt.

| q | Instruction | q | Instruction |
|---:|:---|---:|:---|
| 0 | D 1 1 2 | 11 | D 5 13 14 |
| 1 | I 7 0 | 12 | D 2 17 18 |
| 2 | I 6 3 | 13 | D 5 15 16 |
| 3 | D 5 2 4 | 14 | D 3 17 19 |
| 4 | D 6 5 3 | 15 | I 4 10 |
| 5 | I 5 6 | 16 | I 2 20 |
| 6 | D 7 7 8 | 17 | D 4 0 21 |
| 7 | I 1 4 | 18 | D 0 0 17 |
| 8 | T 6 9 0 | 19 | I 0 0 |
| 9 | D 4 0 10 | 20 | I 3 17 |
| 10 | D 5 11 12 | 21 | halt |

This is the literal table in `korec_packed_counter_units.md`, Section 1.
Define the enumeration, including all its possibly redundant indices, by

    S_e={x>=1: K started at 0 with (0,e,x,0,...,0) halts},
    U={2^e(2x+1):e>=0 and x in S_e}.                     (7)

Each S_e is c.e., uniformly in e, and every c.e. set of positive integers
occurs by the inherited strong-universality theorem. In particular the
program coordinate in (7) is the literal nonnegative register R1, not an
unspecified alternative enumeration or the shifted positive parameter E.
The primary strong-universality convention uses a recursive program-code
map and leaves the varying input unchanged. [Korec, printed pages 267--268,
Definition 2.3 and Section 7](https://www.cs.cmu.edu/~cdm/resources/Korec1996-small-universal-RM.pdf).

Adjoin the following nine states to K, changing none of its instructions:

| q | Instruction | Meaning |
|---:|:---|:---|
| 22 | T 0 23 30 | require a positive current dividend |
| 23 | D 0 24 26 | consume the first unit of a pair, or finish even division |
| 24 | D 0 25 29 | consume the second unit, or finish odd division |
| 25 | I 2 23 | increment the quotient |
| 26 | I 1 27 | count one extracted factor of two |
| 27 | D 2 28 22 | transfer the quotient back to R0 |
| 28 | I 0 27 | complete one transfer unit |
| 29 | T 2 0 30 | enter K only with positive ordinary input |
| 30 | I 3 30 | reject forever |

Call the resulting machine M. Its start is 22 and its sole halt remains 21.
For its unary input n put R0=n and all other registers zero.

At each entrance to 22, the registers are (N,e,0,0,...), N>0. The loop
23--25 removes pairs from N and records their number in R2. For even N,
it reaches 26 with (0,e,N/2,0,...), increments e, and the loop 27--28
returns to 22 with (N/2,e+1,0,...). Both inner loops terminate by their
decreasing source counter. An even positive N is at least 2, so every
such return strictly decreases the current dividend.

For odd N, state 24 detects the final unpaired unit after it has been
removed. State 29 therefore sees (0,e,(N-1)/2,0,...). If that quotient is
positive, M enters K in exactly the required configuration; if it is zero,
M rejects forever. Consequently powers of two are rejected, as required
by x>=1. For all other n>0, the unique factorization n=2^e(2x+1), x>=1,
gives exactly the entry (0,e,x,0,...). No K edge targets a loader state.
It follows, in both directions, that

    M halts on n  iff  n in U.                           (8)

This is a proof of the literal loader for every n, not a bounded simulation.

## 4. The fully specified H transition expression

A live configuration is the nine-tuple

    c=(q+1,R0,...,R7).                                   (9)

The positive state tag separates every live configuration from the zero
delimiter, including configurations whose eight counters all vanish.
In an 18-window denote the two blocks by c,c'; their coordinates are
0,...,8 and 9,...,17. Each of the following is an explicit conjunction of
the atoms (3), so it is an H-expression with support in that window.

For every branch q -> t in the literal tables impose C_(q+1)(c0),
C_(t+1)(c'0), and N on all sixteen current/next counter sites. Then impose:

| Branch | Changed/tested register j | Every other register i |
|---|---|---|
| I j t | S(c_(j+1),c'_(j+1)) | Eq(c_(i+1),c'_(i+1)) |
| positive D j t z | S(c'_(j+1),c_(j+1)) | Eq(c_(i+1),c'_(i+1)) |
| zero D j t z | C_0(c_(j+1)) and Eq(c_(j+1),c'_(j+1)) | Eq(c_(i+1),c'_(i+1)) |
| positive T j t z | Pos(c_(j+1)) and Eq(c_(j+1),c'_(j+1)) | Eq(c_(i+1),c'_(i+1)) |
| zero T j t z | C_0(c_(j+1)) and Eq(c_(j+1),c'_(j+1)) | Eq(c_(i+1),c'_(i+1)) |

For the zero branches the target in the tag constraint is z. A positive D
needs no extra positivity atom: its successor counter is nonnegative and
S(c',c) makes the current counter at least one. Let Run be the union of
these finitely many branch expressions for M. There is no Run branch out
of q=21. Its only exit is supplied separately by

    Clear = [C_22(c0), N(c1),...,N(c8),
             C_0(c'0),...,C_0(c'8)];
    Restart = zeta_{9,...,17} Z;
    R = Run union Clear union Restart.                  (10)

Restart means precisely c=0 with c' arbitrary. It includes the all-zero
18-tuple. Clear sends exactly a genuine halted configuration to zero.
The retained U21 contributes 34 branches, and the nine added instructions
contribute 14. Thus (10) has 48 Run branches plus Clear and Restart, all
fifty alternatives specified by the two literal tables and the fixed grammar.
All symbols in (10), including bracketed conjunction, have finite
expansions into the primitives in Sections 1--2 and the literal tables.

## 5. Finite support enforces an actual accepting history

Define

    W = omega_18 R;
    Hist = W intersect sigma^-9 W;
    Reach = Block_9(Hist).                              (11)

Writing c_i=(f(9i),...,f(9i+8)), the two aligned block conditions in Hist
assert (c_i,c_(i+1)) in R for *every* integer i. The first covers even i,
and the shifted condition covers odd i. No transition is skipped.

Suppose c_0 is a live configuration in Reach. Because its tag is positive,
the next edge cannot use Restart. Until a zero block is reached, every
edge is an actual M transition, except that a halted state uses Clear.
Finite support supplies a first zero block at some positive index T.
The edge into it cannot be Run, whose target tag is positive, and its
nonzero source excludes Restart. It must be Clear, so c_(T-1) is a genuine
halt. This proves soundness without demanding that the whole witness
contain only one episode.

Conversely, write any finite M run ending at halt into blocks starting at
0, followed by the zero delimiter and all zeros thereafter. Put zero
blocks at negative indices. Restart permits the edge from block -1 to
the initial block, actual edges realize the run, and Clear terminates it.
This has finite support and lies in Hist. Thus Reach contains exactly the
live configurations that have a finite path to halt, together with any
zero configuration admitted by the restart convention.

Finally impose the literal initial configuration:

    Init = [C_23(c0), Pos(c1), C_0(c2),...,C_0(c8)];
    Accepted = Reach intersect Init;
    E_U = sigma^-1 Keep_({0,...,8},{1})(Accepted).         (12)

Init is a 9-window conjunction using (3). The forgotten coordinates in
(12) are existentially projected, including the nonzero initial tag;
they are not forced to zero before projection. Equations (8)--(12) prove

    E_U = {(n):n in U}.                                 (13)

This is a closed, finite H-expression specification from Z and S alone.
Only omega_2 and omega_18 are needed here. All other expansion lengths
depend on fixed numerals no larger than 31, adjacent swaps within an
18-site window and the thirty nonhalting instruction rows. No bound on runtime,
input size or register contents appears in the expression syntax.

Substitute (12) for the single E_U occurrence in
`positive7_higman_commutator_pattern_pascal.md`, equation (8). The resulting
closed finite expression is exactly

    X_U={(0,-n,1,n,1,-n,-1,n,-1,0):n in U},              (14)

with the frozen even-a/odd-b commutator convention. This closes the
expression-level open question in that note and in the preceding
instantiation-gap audit; those historical frozen questions are preserved.

## 6. Scope, retained boundaries and next finite data

**Remark 1 (the state tag is necessary for this delimiter proof).** An
untagged zero-counter configuration is the zero block regardless of its
control state. For example a machine that only loops through pure zero
tests and never halts would then admit an all-zero block witness if that
encoding were used. Finite support alone would certify nothing. The tag
q+1 and the source/target constraints in Run prevent that collapse.

**Remark 2 (one alignment is insufficient).** With only omega_18 R, no
condition joins the second configuration of one pair to the first of the
next. A single legal nonhalting transition surrounded by zero pairs would
therefore be admitted without its required next edge. The shifted second
condition in (11) is essential; merely counting legal pairs is not a run.

**Remark 3 (input zero and powers of two).** Omitting the positive check
at 29 would enter K with x=0 on n=2^e. Those values are excluded by (7),
irrespective of whether K happens to halt on them. The exact loader keeps
the check. This is an interface mismatch of that omitted-check proposal,
not a claim that any particular x=0 body run was evaluated or halts.

**Remark 4 (draft wording correction).** The first draft described the
six witness-based primitives as the "first six lines," although the display
grouped several on the same line. The corrected text names the six
operations explicitly. Their definitions and proof obligations are unchanged.

**Question 1 (remaining positive7 data, credited to the frozen gap audit).**
Apply the explicit H-to-benign-pair constructions to the finite expression
(14), retain the named generators, and give the actual finite presentation
and two image words. The expression now fixes the missing unary set, but
does not by itself supply those group objects or their numerical sizes.
The conditional r=n_H+6m_H+k_H+133 ledger remains conditional on them.

**Question 2 (arithmetic cost, credited to the active research goal).**
After the group data are materialized, determine the actual matrix alphabet
and its paid Diophantine circuit. Macro expansion size, the thirty machine
instructions and the block width 18 are not substitutes for that count.

The retained U21 contraction and strong universality are imported from
the repository's source-reviewed construction and Korec's theorem. This
note independently proves the new loader and every H-expression identity;
it does not re-certify the entire primary universality proof, historical
numerical checks, Higman embedding proof or any saved arithmetic source.
Only text/PDF reading, hand reasoning and fresh byte/read-span metadata
are used. No scientific program, supplied/frozen helper or saved source
array is executed, imported or evaluated; no degree propagation or build.

Aristotle and Pascal each read the complete 318-line mathematical draft,
independently matched every retained U21 row, and passed all loader,
primitive-expansion, alignment, delimiter, projection and scope checks.
Both explicitly kept the full Korec proof and historical numerical audits
outside their review scope. Final edits record the fifty alternatives,
the wording correction in Remark 4 and this provenance; no expression or
mathematical argument changed. The companion receipt binds this final text
and exact source-read spans. This author proof/metadata pair is frozen.
