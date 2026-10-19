# Alternative foundations and what the encodings actually buy

## Result and scope

The strongest concrete result of this branch is the complete **946-bit
equational refutation packet** in `generated/`. Its ordinary model argument
is in `stack946_note.tex`, and the current run reproduces ten comparison
variants. It retains a fully adequate binding and equality interface. It
does **not** implement a new binary Turing machine, so it supplies no
sub-240 state claim. The present 240-state machine retains the original
calculus and has ordinary consistency and runtime arguments; its complete
exact-table Lean endpoint is still open at the inspected commit. The
different compensated244 machine is the closed external Lean baseline.[1]

The equational target is a **particular ground equation**,
`N(d,d) = d`. The equations themselves have the trivial one-element
algebra, so their bare consistency is not the desired statement. The
relevant theorem is nonderivability of that ground equation, equivalently
existence of a model separating its two sides, iff `Con(ZFC)`.

All repository claims here refer to ProveIt commit
`13ec39ed43148b1807f51ed6e6528e1c84659562`. The selected GitHub plugin was
used to inspect pinned files and to resolve upstream `zf-254` to
`c132d7eae8158cd3a9850ea3eb7251158c3dd821`. No local Coq/Lean build is
claimed by this foundations branch.

## The compact theory already behind the machine

The upstream 254-state machine searches a nonextensional theory SIR:
power-container `CP`, global-image collection `GIC`, native logical equality
and irreflexivity. Its quotient interpretation recovers ordinary set
theory; the upper relative-consistency proof uses the constructible
universe. The upstream current files report a closed Coq endpoint for the
literal table and for refutation of ZF, ZFC and SIR.[2]

This matters because dropping the familiar long list of ZFC axioms has
already happened. There is no separate extensionality, pairing, union,
infinity, separation or choice emitter to remove from the current machine.
The numerical calculus also shares its false code with `v0 in v0`, and
shares code zero with a truth alias. Irreflexivity is part of the soundness
of those aliases, including some apparently logical rows. Its freshness
gate permits `a=b` but requires `c!=a,b`; `c=b` would force a
self-membership in the container clause. Deleting that test without a
replacement interpretation is therefore not an optimization.[2]

## Comparison of serious candidate formalisms

| Formalism or modification | What is mathematically available | What still costs machine states |
|---|---|---|
| Existing SIR and complete numerical Hilbert calculus | An inherited literal-machine calibration and unbounded source/runtime arguments.[1][2] | Register arithmetic, source decoder, proof enumeration, binary routing and startup; current state reductions exploit these. |
| Raw equality-free EPSC | An ordinary derivational equivalence with seeded PSC, followed by the hereditary-saturation/ZFC comparison. It needs all formula matrices, ordinary common-domain first-order logic and arbitrary finite parameters.[3] | A complete binding/substitution engine. Simply deleting the original equality rows is unsound as a consistency-search replacement. The maintained complete control was 270 states in its cited compiler family.[3][4] |
| `CP + weak Collection + Separation` | Source 80 proves full GIC equivalent to weak Collection plus Separation in ordinary nonempty native-equality structures.[5] | Two separately emitted schemas, shared parsing and freshness, and their final compiler layout. No complete smaller machine was priced. |
| Finite assignment/class kernels | A finite language with a class-incidence predicate represents every pure-membership formula; a descriptor supplies its code and parameters. Source 40 has 15 clauses and explicit ordinary upper/lower models.[6] | Equality-aware ground inference, congruence, all subterms, formula descriptors and fair enumeration; the fixed axioms do not eliminate those tasks. |
| Native environment-stack kernel | Two unconditional equations replace conditional assignment update. Source 79 has a 14-equation, 1,169-bit complete packet and a same-carrier Boolean argument.[7] | Generic ground contextual equality, substitution with repeated variables, syntax storage, copying and a blank initializer. This branch shortens the packet to 946 bits. |
| Equational arithmetic/combinator presentation in general | Ground contextual rewriting is complete for a ground equation: failure of derivability gives the separating ground-term quotient. The implication applies to an exactly specified finite packet. | A universal interpreter must still carry the entire theory/query information. Fewer symbols or a tiny abstract universal machine do not charge a blank-tape loader. |
| The cited Map Theory model | The primary Berline--Grue construction proves consistency in ZFC plus an inaccessible cardinal.[8] | That cited upper bound is stronger than the requested calibration. It is not an established ZFC-equiconsistent shortcut from the cited source alone. |

These alternatives differ in where they place complexity. The native stack
kernel is attractive because it uses genuine equality in the external
equational proof mechanism while keeping the object theory itself
equality-free. It thereby avoids both conditional equality clauses and the
missing common-domain substitution seen in the reduced numerical logic.

### Selected earlier payloads and the accounting boundary

The 946-bit result improves the complete equational packet family. It is
not claimed to be the smallest numerical payload across all formalisms.
The following are exact recorded totals from selected inspected sources;
they are not global minimum claims.

| Source and variant | Format | Equations or clauses | Term nodes | Recorded bits |
|---|---|---:|---:|---:|
| Source 70, grouped Boolean equations | Complete equational packet | 21 equations | 446 | 2,324 |
| Source 77, selector dispatch | Complete equational packet | 18 equations | 420 | 2,194 |
| Source 78, membership elimination and alias | Complete equational packet | 22 equations | 420 | 1,768 |
| Intake 169, joint 77/78 with split congruences | Complete equational packet | 21 equations | 415 | 1,750 |
| Source 79, native stack | Complete equational packet | 14 equations | 214 | 1,169 |
| Source 79 review, truth fusion | Complete equational packet | 14 equations | 214 | 1,166 |
| This branch, shared stack/class constructor and spare slice | Complete equational packet | 14 equations | 215 | **946** |
| Source 42, native equality clause variant | Complete native clause packet | 16 clauses | 167 | **901** |
| Source 44, FC15* native variant | Clause template with external signature | 15 clauses | 182 | **881** |

Sources 70, 77, 78 and the intake joint construction charge the signature,
variable capacity, equations and ground endpoints.[10] Source 42's 901-bit
native clause codec separately charges its header, arities, equality index
and clause scopes; it assumes a native equality proof mechanism. Its
equality-completed version is 1,998 bits, while another Source 42 variant
has 917 native bits and 1,703 equality-completed bits.[11] Source 44's
881-bit stream has known predicate codes and takes the function signature,
arities and variant externally. Its equality-predicate template has 1,616
bits, still with that template boundary.[12] A fair implementation comparison
must price each format's corresponding interpreter and blank loader. None
of these data totals is a binary Turing-machine state count.

## Existing obstructions that rule out tempting deletions

### Equality deletion is not just an axiom-count question

The repository's finite-sort interpretation assigns different finite
domains to distinct variable labels. It validates the reduced logical
rows, either form of the retained quantifier row, atomic vacuity, and the
actual fresh C/G bundle, while making the refutation target false. The
source reviews explain a PA-formalizable invariant for the abstract search.
The issue is that different object variables can no longer be identified
by full substitution. The countermodel survives genuine primitive Bottom
and several later grammar reductions.[4]

Accordingly, the ordinary fact that an equality-free set theory has the
right strength does not justify removing equality from a particular
incomplete proof calculus. The new packet keeps native equations and full
equational substitution; none of these rows is silently deleted.

### Dropping GIC support loses much more than an output filter

The support arm says that every member collected is a genuine output of
the defining relation. Source 80's rational-cut model validates CP,
full weak Collection, ordinary Extensionality, Empty Set, Union,
Foundation and irreflexivity, but violates full GIC and relevant Separation.
Its Collection proof covers all formulas by rational affine automorphisms,
not only its finite test suite.[5]

The correct split is full weak Collection **plus full Separation**.
Removing support alone therefore lacks the desired consistency strength;
rejecting this one model would still not prove a replacement adequate.

### Fixed labels and restricted parameter counts need their own proofs

Earlier fixed-slot and cofinal-gate variants have explicit modal/sorted
counterinterpretations. EPSC2 and certain one-parameter repairs have
ordinary calibration arguments, but bare EPSC1 does not acquire full
strength merely because its formulas look similar. The repository records
concrete failures of the old Pairing/hereditary-domain shortcut and keeps
consistency strength distinct from nonderivability of one axiom.[3][4]

In the native stack implementation, the finite parameter list is stored
after the class-code slot and is arbitrarily long. De Bruijn binding
prepends a coordinate; the native tail equation shifts every old coordinate.
This is a concrete unbounded binding mechanism, not a fixed-slot promise.

### Eliminating all genuine functions cannot make a universal finite kernel

A finite, purely relational universal theory with finitely many constants
has a simple obstruction. If it has a nonempty model, the induced
substructure on the constants (or one arbitrary element if there are no
constants) is a bounded finite model. Checking those finitely many
structures decides satisfiability. Thus a universal finite presentation
encoding this consistency problem needs unboundedly generated ground
structure, such as the function symbols of the native kernel. This is a
structural restriction on that syntactic family, not a lower bound for
arbitrary presentations or Turing machines.

## The new 946-bit construction

The source-79 1,169-bit encoding has 16 operation symbols and three local
variables. Its fixed-width codec must distinguish 19 values, so each node
uses five bits. The new combination removes three symbols while adding
only one term node:

1. `J(a,b)=P(a,b)`: a stack cell also constructs the class NAND of its
   arguments. In the upper model, `P`, `A`, and `Q` still have disjoint,
   increasing numeric code ranges. The class meaning of a P-code becomes
   NAND; its meaning to the native projection function remains a stream cell.
2. `Pick(x)=W(x,d)`: interpret the class `d` as false in the upper model.
   The existential witness specification at that class then imposes no
   constraint on `W(s,d)`, so use it to choose a member of `s` whenever one
   exists. The general unused-slice principle is inherited from Source 40.[6]
3. `top=d`: transport an independent countably infinite Boolean algebra
   onto the **same carrier**, selecting its top to be the existing object d.
   This truth fusion was already identified by the source-79 review.[7]

There is no conflict between d being Boolean top and its denoted class
being false. The value of the object d in the Boolean algebra is d; the
value of the predicate function `p_eps(s,d)` is the Boolean bottom. They
are different expressions. The underlying stack and class operations are
retained on the same carrier when Boolean predicates are introduced.

For the reverse implication, take any nontrivial new equation model and
define the removed operation symbols by those three terms. Every old
equation follows literally. The new theory does not have to prove that
the d-class is false: that choice is made only to construct an upper model.
The standard ultrafilter conversion then applies to predicate values while
retaining native functions, so it recovers the original adequate kernel.
The Sheffer basis used here is the published Sh1 theorem.[9]

The complete accounting is `55 + 875 + 16 = 946` bits, including arities,
capacity, equation markers, every term and both ground endpoints. The new
215-node payload has 13 symbols and three local variables, exactly 16
opcodes, allowing four-bit nodes. The reduction is 223 bits from Source 79.
This is a composition effect: either symbol deletion by itself remains
above the opcode-width boundary and saves only three header bits.

## Executed evidence and the machine boundary

The packet builder checks all ten variants. Each passes both exact parsers,
all strict truncations and four malformed/trailing-input controls. Each
has 72 Boolean clause-group valuations. Source 79's 2,080 selector and
16,384 formula regressions were freshly run. An independent companion adds
480 native head/tail checks, 16,384 modified cons/NAND formula and chosen
witness checks, 32 spare member-choice cases and 320 arbitrary false-class
witness cases. The exact counts and hashes are in `generated/`.

The unbounded model proof relies on constructor arguments being strictly
smaller natural numbers, and on every fixed descriptor denoting one finite
pure-membership formula. These induction arguments are not replaced by the
bounded checks. The original EPSC comparison, first-order completeness and
the Boolean basis remain mathematical dependencies.

A machine consuming this packet must implement full ground substitutions,
arbitrary one-hole contexts, both rewrite directions and a fair unbounded
search. Its allocation and loader must be counted from an all-zero binary
tape. No supplied program currently combines those costs below 240 states.
For an immediate small reduction of the existing machine, preserving its
calibrated source while exploiting entry invariants remains better supported
than weakening its proof calculus.

The companion `ground_rewrite.py` now gives a complete abstract search
specification: it enumerates every finite binary certificate and checks
each described sequence of contextual ground rewrites. A substitution
assigns the **union of variables on both equation sides**, before applying
the selected orientation. Thus backward use of the head equation,
`x -> V(P(x,s),d)`, can introduce a fresh value for `s`; reversed Sh1 can
introduce its other variables. Matching only the variables on the source
side would be incomplete. Every finite certificate takes finite abstract
time to validate; no fixed term depth or trace length is imposed. The
implementation uses iterative term parsing, substitution, equality and
context rebuilding. The bounded 65,536-certificate run on the actual packet
is inconclusive, as expected; it supplies no evidence of nonderivability.

## Sources

[1] [Current rotation240 candidate](https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/Computability/BusyBeaver/Research/ZFC/candidate-rotation240/README.md).

[2] [Upstream exact 254-state theorem and trust surface](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/README.md),
[set-theory construction](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/design/settheory.md), and
[exact logical roots and aliases](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/design/logic.md).

[3] [Empty-seed EPSC, ordinary calibration and complete control](https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-146-source-14.md) and
[maintained parameter-reduction notes](https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/Computability/BusyBeaver/Research/ZFC/raw_psc.md).

[4] [Finite-sort countermodel and exact limitations](https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/Computability/BusyBeaver/Research/ZFC/typed_countermodel.md).

[5] [Rational-cut model and GIC/Collection/Separation comparison](https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-170.md).

[6] [Source 40 finite kernel and spare witness-slice precedent](https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-154-source-40.md).

[7] [Source 79 native-stack proof](https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/79-zb242-res-stack-kernel-stack_kernel_note.tex) and
[independent review](https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-169-source-79.md).

[8] [Berline--Grue, A kappa-denotational semantics for Map Theory in ZFC + SI](https://hjemmesider.diku.dk/~grue/papers/BerlineGrue97/BerlineGrue97.pdf), abstract and Theorem 7.2.1.

[9] [McCune et al., Short Single Axioms for Boolean Algebra](https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf), Theorem 2.

[10] [Source 70 grouped packet metrics](https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/70-c244-equational-metrics.json),
[Source 77 review](https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-169-source-77.md),
[Source 78 review](https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-169-source-78.md), and
[joint construction](https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-169.md).

[11] [Source 42, complete 901-bit native clause packet and equality comparison](https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-155-source-42.md).

[12] [Source 44 exact template metrics](https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/44-nine-data-kernel_metrics.json),
[codec with externally specified arities](https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/44-nine-code-ground_kernel.py), and
[ordinary review](https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-155-source-44.md).
