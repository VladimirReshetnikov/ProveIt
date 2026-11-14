# Contextual reduction research

All local labels in this note are native labels of the class-A History U208 table
`upstream/U208_ConPA_History_2026-10-29/U208_ConPA_History_2026-10-29/machine/u208.native.tm`.
SHA-256: `36b58fea7a184b1050914170e8f5240c8a13da218dbbfa7e1985cd73d516e5c7`.

No sub-208 candidate has yet survived an exact check in this branch.

## Stronger invariant construction

`window.cpp` computes the least reachable fixed point of a finite-window abstract
TM. A configuration is a control state and all 15 tape bits within radius 7 of
the head. Both possible values of the bit newly entering the window are allowed
at each move. The initial state is 0 with *every* possible window. Consequently
this is an overapproximation of every run from state 0 on every initial tape.
Every concrete execution projects to an abstract path, by induction on time.

For class A it yields 961,765 reachable abstract configurations. An exact
Shannon decision-tree cover reduces the sets to 2,692 Boolean cylinders. No
state is restricted to a single current read symbol. The corresponding class-B
cover has 2,698 cylinders. This provides unbounded-history local invariants,
rather than merely depth-k histories.

The `.bin` files store the raw Boolean characteristic vectors; context JSON
stores the exact cylinder covers. The builders are research infrastructure;
a production certificate should independently check initial inclusion,
transition closure, and equivalence between covers and bitsets, rather than
trusting these exploratory constructors.

## Searches completed without an accepted result

- Original one-row contextual-fold scheme, class A, history depth 7 and macro
  length at most 31: zero results.
- Both representative rows selected independently from the corresponding two
  original rows (without requiring an unchanged matching row): 85,284 oriented
  row choices, history depth 7, macro length 31: zero results.
- Head-offset quotient with offset +2 or -2, no representative-row mutation:
  37,053 pair/offset choices, history depth 8: zero results.
- Original one-row fold scheme using radius-7 fixed-point contexts: 369,152
  mutations in each of class A and class B: zero results. These searches use
  finite execution only for rejection and would apply exact branching to all
  surviving candidates.
- General one-row helper mutation, with no requirement that the other old row
  match: 42,642 oriented state pairs, arbitrary helper/write/direction for the
  changed row: no finite-screen survivors on class A.
- Two independently synthesized rows of the retained representative, allowing
  arbitrary first-step helpers but forbidding an unresolved cross-symbol
  representative revisit during each synthesis: 21,321 unordered state pairs:
  no finite-screen survivors.
- Finite marker conjugacy, no retained-row mutation: 37,053 choices: zero results.
- Finite marker conjugacy plus one retained-row mutation: 36,668 oriented pairs:
  no finite-screen survivors.
- Two changed rows, representative reverses direction while preserving the
  current bit and jumps to a helper, with one helper row freely changed:
  32,094,800 right-moving-decoder mutations and 10,135,200 left-scanner mutations:
  no finite-screen survivors.

The C++ screens use 12 sampled radius-7 patterns for each state/read symbol and
random exterior bits. A rejection is a counterexample to the specified bounded
local simulation requirement for that sampled context; it is not a proof that
the mutated machine has incorrect blank-input behavior. A positive result would
still require the complete symbolic checker. None of these restricted negative
results is a lower bound on the state count.

## Finite marker conjugacy

Suppose every retained incoming edge to a deleted state q moves in direction d.
Represent an old q-configuration by representative state r, the same head, and
the same tape except that the cell at offset -d is complemented. Complement the
written symbol on every retained incoming edge to q and redirect its target to
r. All ordinary transitions then commute with this representation. It remains
to prove the bounded macro for q, including removal or transfer of the marker
at its endpoint. This is a strictly broader relation than equal-tape state
identification. Our bounded screens found no accepted instance on this table.

## Two-sided joining search: instructive false positives

A broader search permitted both old and new machines to execute positive blocks
of at most 31 steps before agreeing on their full tape, head, and quotient state.
The finite screen retained 11 simple aliases:
`1→2`, `1→3`, `2→1`, `2→3`, `2→5`, `2→9`, `2→15`, `3→1`, `3→2`,
`3→5`, and `52→155`.

The scanner proposals are clearly unsuitable in general. For example deleting
3 and redirecting it to 2 makes both rows of state 2 loop left, eliminating the
zero-run detector's exit. These aliases pass random finite contexts because a
nearby one often makes the unmodified scanners meet before the distinction is
exposed.

The more interesting `52→155` failed exact symbolic branching. With the first
context of state 52 and future prefix `0011101` followed by a long run of ones,
the old machine reaches state 32 and the new one state 48, at the same head and
with the same tape, after 7 and 11 steps respectively. Both states scan ones to
the right, but on zero, 32 enters 48 and 48 enters 25. Thus they count different
numbers of separators. The recorded rejection is `join52_155.json`. Its absence
of a join by 31 steps is not alone a theorem about eventual blank-input behavior.

## Further directions

The strong failure of small local equal-tape folds suggests checking intended
canonical primitive frames, whose global tape organization is stronger than
any radius-7 invariant, or changing source tree layout together with the shared
runtime decoder. Whole-runtime symbolic contracts are the appropriate gate for
such candidates.

The unrestricted two-changed-row extension (arbitrary first write/direction,
first target is the second altered row's state, arbitrary second transition)
completed 235,136,640 mutations across 174 literal shared-row unordered pairs,
without a finite-screen survivor. This particular enumerator excludes the
initial state as both helper and deleted state; subsequent targeted one-row
screens cover initial-state helpers, keeping state 0, and deleting state 0
with a correspondingly mapped start state, also without survivors.

No row of state 0 is assumed unreachable: the actual incoming inventory is
`0/1`, `24/1`, `74/0`, and `94/1`. Its read-one branch is part of the runtime.

## Rejected dispatcher-cut abstraction

An exploratory abstraction seeded state 84 with canonical source-address windows
and stopped on every subsequent visit to 84. It reported a false `14/read1`
unreachability claim and several apparent 207-state aliases involving state 14.
A concrete check immediately rejected `14→39` on the canonical `CD` primitive
at source address `0000100`.

The reason is structural: state 84 is revisited inside a primitive on temporary,
marked program counters. A return to the dispatcher is not automatically a
canonical primitive boundary. The parent symbolic contract recognizes the full
expected endpoint frame, not just state 84. Consequently `frame_window7*` and
`frame_folds7.txt` are **rejected exploratory artifacts**, not sound full-runtime
invariants or accepted candidates. The literal table `without14_39.tm` is a
counterexample artifact only. The ordinary fixed-point invariants from state 0
with arbitrary tape do not have this problem.

## Source-layout combinations and source commutation

Ten individually finite-validated 208-state source rotations were screened,
then all 767 nonempty compatible subsets of them (excluding the one pair that
both changes state 162). Each table received a newly computed radius-7 fixed
point and the shared-row one-mutated-row fold screen. None produced a survivor.
The full mask/rotation inventory is in `combinations/results.json`.
The two 210-state shared-168 expansions provided by the comparison branch were
also screened, without a survivor.

The source-level commutation scan found only two kinds of entirely increment
subtree: state 99 represents two increments of register 1, and state 160 four
increments of register 1. There is no closed two-leaf subtree incrementing two
different registers. The full source has mixed adjacent increment runs only
of forms `(1,6)`, `(7,6)`, and `(8,6)`, all of length two; longer runs increment
register 1 exclusively. Normalizing every maximal adjacent CI run in every
complete source-decoder word produces no matching donor-state signatures in
either graph class. Thus direct deletion by swapping a commuting increment
pair into an existing decoder is unavailable in this restricted search.

## Source arithmetic and command protocols

The later source work uses class A's `variant_plain/u208.sites.json` and
`variant_plain/u208.native.tm` from the research packet, rather than assuming
that native labels in every class-A presentation are identical. Its source
SHA-256 is `cddbed7f20e7a8b085b7ca0e76811d07b021522375643b5d1134eec0d2d23164`.
It has 3,909 primitives and 197 distinct DAG nodes.

The final scheduler has **three commands**, S, MP, and AX. An earlier lineage
file has separate NIP and DROP commands, but that historical four-command
compiler cannot be applied directly to the final source. The current
`no_mp_padding/proof.md` uses the correct three-command compiler, with its
explicit reserved-zero trace. Its source-level completeness argument was
independently checked by the theory-audit branch.

### Finite inductive zero invariant

`no_mp_padding/prove_source_zero.py` is now standalone Python, with no NumPy,
solver, comparison-module, or shell dependency. It independently resolves the
source CFG using subtree intervals and verifies products of zero, positive,
and unconstrained natural values at every ordinal. The supplied certificate
checks all 5,080 applicable abstract edges, has 3,907 nonempty ordinal domains,
and includes both the ordinary positive-N initial store and the calibrated
source-ordinal-136 bootstrap store `(1,0,13,0,0,1,0,0,1)`.

It proves T=0 at ordinal 3847 and excludes the positive body ordinals 3848 and
3849. This is a finite verification of induction over all executions, not a
bounded run. There is also a direct local proof: `[3834,3837)` transfers T into
X, and the following equality test never increments T. Thus successful MP
enters its output block with T=H=X=Y=0.

No other globally constant CD branch was found by the completed zero/positive
abstraction. Relational invariants could strengthen this result. The affine
source donors 8/110 and 128/179 agree under some external-entry zeroes, but
both apparent substitutions would alias an ancestor to its own descendant
and create a recursive decoder cycle. Neither restoration tail is identity
under the established invariants, because scratch register X need not be zero
at that tail's entry. These pairs are rejected, not state-saving candidates.

### Exact source alternatives

| Variant | Primitive count | Distinct source DAG nodes | Source-level status |
|---|---:|---:|---|
| Original class A | 3,909 | 197 | Retained baseline |
| Remove only dead MP initial transfer | 3,906 | 198 | Same commands, stuttering deletion |
| MP without its successful zero push | 3,890 | 197 | Same calculus; revised strong compiler |
| Cache-return MP | 3,886 | 197 | Historical alternative with retained strong compiler |
| Move target into current and clear counter | 3,886 | 198 | Same calculus; MP proof block needs no cleanup |
| Direct unary selection test, five associations | 3,899 | 201 | Exactly the same S command |
| Copy plus unary scratch test | 3,900 | 199 | Exactly the same S command |

Every generator checks both source-CFG resolvers and every retained effect and
control edge under the ordinal translation. Every source keeps the exact
protected startup address at ordinal 136. These are source-level statements;
new literal allocations require their own complete tape-frame proof.

For no-padding MP, let `M=I(A,Y)` and retain the original helpers H, PUSH, and
DISCARD. Their MP uses are forced failures and therefore unchanged. Compile a
modus-ponens node by

`DISCARD; PUSH; B_M; PUSH; B_A; PUSH; S; S; MP′(Y); H`.

Immediately before MP′ the tuple is `(A,[0;w],0,M)`. Success yields
`(Y,[0;w],Y,0)`, and H tests/preserves Y, clears the counter, and removes that
reserved zero, yielding `(Y,w,0,0)` unless it already halts at Y=1. The
conservative credit weights remain S=-1, MP=0, AX=+10, so the inherited
bootstrap protection and cofinal completeness arguments still apply. The
ordinary proof is in `no_mp_padding/proof.md`.

Replacing the whole successful MP body by transfer D→H yields the already
known cache-return MP, not a new historical discovery. Transfer D→T instead
returns `(Y,w,0,0)` directly, so the ordinary compiler's premise setup followed
by successful MP is already the required strong conclusion. These variants
are supplied as alternative allocator inputs.

The new S implementations use a direct unary test for h=1, avoiding a general
comparison against a separately constructed one. Their all-natural proofs
split h=0, h=1, and h>=2 and use the usual decreasing-counter transfer/clear
inductions. `direct_selection/proof.md` gives the exact trees and proof;
256 finite pre-pop examples per association are implementation checks only.
The 25-primitive form consumes two H units, supplies two T increments, then
transfers the remainder; the 26-primitive form retains the old H→T,X copy and
tests/clears X directly.

The parent allocator found a 209-state implementation of no-padding MP that
passed 10,118 finite canonical primitive cases. That is not a sub-208 result
or a complete literal-machine proof. This branch produced no accepted
sub-208 machine. Primitive savings and source-DAG savings must not be reported
as literal-state savings.

## Reproduction and dependency map

Run the following from the archive/workspace root:

```sh
python analysis/reduction_search/reproduce_source_branch.py
```

This short standard-library driver regenerates the MP variants and S variants,
checks the two source-CFG resolvers, derives the zero invariant, and separately
verifies the saved certificate. The direct zero check can be run alone:

```sh
python analysis/reduction_search/no_mp_padding/prove_source_zero.py --certificate analysis/reduction_search/no_mp_padding/source_zero_certificate.json
```

The zero checker accepts `--source PATH` for a separately located copy of the
pinned source. The source generators import `analysis/comparison/source_inventory.py`,
which loads the retained `source_language.py` from the research packet. Thus
those generators need the original `upstream/u208_research_2026-10-29/` subtree
and the small comparison helper in addition to this directory. They use no
third-party Python modules.

The earlier finite-window/search infrastructure has separate optional
requirements: a C++17 compiler for `.cpp` programs, and NumPy for
`derive_window_contexts.py`. It is exploratory research infrastructure,
not a compact proof certificate. Large raw window bitsets are reproducible
from the builder and can be omitted from a compact archive if the exact
cylinder covers, builder, and source table remain. The full enormous mutation
screens are not part of the short reproduction command.

The extracted `u212_combined/` subtree was a read-only convenience copy for
checking lineage. Its authoritative source is the pinned upstream
`calibration/dependencies/u212_combined_2026-10-29.zip`; there is no need to ship
both copies. The relevant compiler and command-contract excerpts are already
included in the parent's `analysis/theory_lineage/` records.
