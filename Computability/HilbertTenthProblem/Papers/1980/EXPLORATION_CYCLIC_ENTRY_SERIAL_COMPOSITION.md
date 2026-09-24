# Cyclic entry removes a routing addition: 118 operations

When the serial program's initial and final control states coincide,
the routing boundary constant can be absorbed into the already computed
2J=q-1. This gives **118 operations: 56 multiplications and 62
additions/subtractions**, with the same 43 positive unknowns and 31
equations as the complete 119-operation component.

The ordinary-input universal compiler can meet this cyclic-entry
condition. The resulting 118-operation family is therefore universal,
but remains above the established universal bound of 90. This note proves
both the arithmetic saving and the exact first-return input contract;
it does not interpret a syntactic program cycle as a halting computation
without that contract.

The full source and receipt are
`../verification/explore_cyclic_entry_serial_composition.py/.json`.
Its dependencies remain unchanged:
`EXPLORATION_MERGED_SERIAL_BOUNDS.md` for the complete119 system and
`EXPLORATION_THREE_RAW_COUNTER_UNIVERSAL_COMPILER.md` for the constructive
three-counter loader, tape simulation, cleanup and physical macros.

## 1. Exact source equivalence for equal control endpoints

Use all the 119-operation source equations and constants, specialized to I=F,
where I and F are the fixed singleton control words. Write

    O=V+h_s(FKplus-J)+h_z(FZ-J).

This is the existing computed routing output, not a new unknown. The old
routing equation is

    (RK-g)C+gI=(gI)q+RO.                         (1)

The retained geometry q=2J+1 makes it equivalent to

    (RK-g)C=(gI)(2J)+RO.                         (2)

The new residual minus the old residual is exactly

    gI(q-2J-1).                                 (3)

Every other source polynomial is identical. All supplied variables
remain positive and every unchanged Pell coordinate is preserved.
Equations(1) and(2) therefore define exactly the same positive witnesses
in the specialized family, in both directions. No range, carry,
divisibility or positivity argument is being substituted for the
integer identity(3).

The schedule already computes `twice_J` for the geometry and flags.
Remove `route_lhs=route_product+gI`, replace
`route_final=(gI)*q` by `route_final=(gI)*twice_J`, and compare
`route_product=route_rhs`. The product count is unchanged and one
addition disappears:

    119-1=118=56M+62A.

No supplied coordinate or free equality is removed. The acyclic norm
correction remains at its previous index. The current six-state
canonical instance already has I=F, so its two complete examples use
exactly the same fixed constants, width, packed integer and witnesses.

## 2. Identify only the accepting halt with the prefix entry

Start with the finite serial graph constructed in
`EXPLORATION_THREE_RAW_COUNTER_UNIVERSAL_COMPILER.md`. Its initial vertex
i is the first lane of the fixed all-plus/all-minus prefix. The unique
accepting halt a is a distinct vertex of phase zero. In that construction:

* i has no incoming edges and has its fixed prefix outgoing edge;
* a has no outgoing edges, and only accepting-cleanup exits reach it;
* all logical program locations, branch entries, macro phases and lanes
  are distinct vertices;
* every edge advances lane phase modulo three, and i has label
  (phase0, sign+, zero-test0).

Form the quotient that identifies a with i and makes no other
identification. Retain i's source label and outgoing prefix edge.
Redirect the old edges entering a to i. This describes every change:
there were no old edges entering i or leaving a, so the quotient creates
no other edges or choices.

The redirected predecessors have phase two. Thus all edges still advance
phase and no self-loop is introduced. Both fixed control endpoints are
now the same vertex i. The accepting halt's unused source label is
discarded; the prefix source label remains unchanged.

Compile the resulting vertex set into fresh distinct Sidon coordinates
and then into the fixed ROM. Distinct surviving vertices receive
distinct coordinates. The quotient is performed on vertices before
assigning these coordinates; it does not identify any two unrelated
vertices because their old or new numeric encodings happen to agree.
Only the prescribed pair a,i is merged. All program constants, including
the strengthened width threshold, are then fixed independently of x.

## 3. First positive return is exactly acceptance

The system's history has positive length: its geometry has q=Wv with
W=R^3>1, and after decoding it consists of at least one complete bank.
The empty path at i therefore cannot certify the new endpoint condition.

Consider any admissible positive-length history in the quotient graph,
starting at i with physical counters [2x,0,0] and ending at i with all
three counters zero. Let t>0 be its first return to i. Before that
return, none of the redirected incoming edges has been taken. Every
visited vertex and edge of the prefix of length t is consequently an
unchanged original graph vertex or edge, except that its last endpoint
i is interpreted as the old accepting halt a.

The only edges entering i are redirected accepting-cleanup exits.
Therefore this prefix is an original accepting execution from the
original raw input x. The existing compiler theorem, including its
exact zero tests and underflow exclusion, implies that the Turing
semidecider accepts the finite binary expansion of x. Cleanup ensures
that this first return already has physical counter values [0,0,0].

There may be later traversals starting from zero input. They cannot
produce false acceptance for the original x: the first return was
already an accepting original computation. No assertion about the
original semidecider's behavior on zero is required.

Conversely, any old accepting computation reaches a with all three
physical counters zero. Redirect its final edge to i and stop there.
It is an admissible positive-length quotient history with identical
updates and source tests. The labels of its final vertex are not
executed. Its first source sign remains plus, and its number of serial
blocks remains a multiple of six.

This proves, for every positive input x,

    old compiler accepts x
      iff the cyclic-entry graph has an admissible positive history
          from [2x,0,0] at i to [0,0,0] at i.

The proof concerns all admissible graph paths, including syntactic
nondeterministic choices; the original logical branch legality theorem
already excludes every invalid choice. It is not restricted to the
single deterministic trace used in the finite regression.

## 4. Full positive Diophantine interface and quantifiers

The specialized119 component exactly represents the cyclic-entry
labelled histories by its existing routing and counter proofs. Its
merged-bound positive converse still applies: the last source counter
must be one, its sign must be minus, and its source-zero label must be
zero because the final numerical counter is zero. This assertion does
not depend on whether the final control vertex is a fresh halt or the
initial vertex. A sufficiently large variable power-of-three width
satisfies the same fixed threshold and all finite numerical bounds.

The twelve packed fields, even index, direct unit-two mask, complete-bank
alignment, and positive fixed-sign43 Pell extension remain unchanged.
Equation(3) then transfers the resulting witnesses to the118 system.
In the other direction it transfers any118 witnesses to the specialized
119 system; decoding followed by the first-return argument proves
acceptance of x.

For any recursively enumerable set E of positive integers, choose its
fixed Turing semidecider, apply the existing raw-input three-counter
compiler, and perform the finite graph quotient above. The resulting
constants depend on E, never on x. They define a fixed system with one
positive input x, 43 positive existential unknowns and31 equations,
whose118-operation straight-line certificate satisfies

    the system has positive witnesses iff x belongs to E.

The operation x+x is still explicitly counted. The finite program
performs every unbounded input conversion; no free variable powers or
input-dependent numerals have been added. The original universal90
family remains the smaller verified result.

## 5. Exact and finite evidence

The checker verifies all 118 primitives, all 31 source comparisons, and
the precise residual identity(3). Thirty source polynomials are literally
unchanged. It reruns the predecessor's two complete canonical paths and
records their stronger inherited source checks separately from the21
retained outer equations. Exact valuations and all positive-kernel
hypotheses are unchanged; huge Pell coordinates are not instantiated.

A separate exact graph regression constructs the actual finite compiler
for the sample Turing machine. It checks that only the accepting vertex
is removed, that no original edge entered the prefix entry, that exactly
the accepting predecessors now enter it, and that all vertex labels,
phases and remaining edges are preserved. It follows every labelled
serial step on raw inputs1 through31, comparing acceptance with the
direct tape machine and recording the first positive return. Rejected
traces cannot return to the entry, and accepted traces do so with all
counters zero. The general first-return proof above supplies the
unbounded and all-path statement beyond these finite executions.

The fresh receipt records 4,124 original and 4,123 quotient vertices,
4,431 edges before and after the quotient, and exactly one accepting
predecessor. It checks 1,307,856 labelled serial blocks over the 31 full
runs, with 16 accepted and 15 rejected inputs. The two canonical
arithmetic examples retain valuations 210,240 and 315,360 and their
333,222-bit and 499,833-bit packed words, respectively.
