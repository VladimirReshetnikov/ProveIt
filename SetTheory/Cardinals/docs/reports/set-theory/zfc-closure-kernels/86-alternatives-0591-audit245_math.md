# Independent mathematical audit of the complete245 construction

## Finding

**The supplied ordinary proof establishes the requested ZFC equivalence for
this245-state table, once its explicit finite certificate computations and
blank initialization are checked. I found no missing mathematical invariant,
stronger-theory substitution, or calibration gap.** The actual-table macro
and all8391-case affine computations have now been independently replayed
successfully by the runtime audit lane; I also independently checked the
source bisimulation, parameter adaptation, all8390 residual normalizations,
and all16 macro induction proofs. The parent audit separately checks literal
blank initialization. The expanded whole-frame run is valuable corroboration
but is not an additional logical premise needed by the already complete
universal macro proof.

The exact object is the canonical table with SHA256

`17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13`.

It has245 working states0..244, start0, separate halt245, and490 binary rows.
Its equivalent old-label table has start95, dispatcher96, halt254 and SHA256
`f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267`.
This is a complete binary table with its initialization included, unlike the
open-port component libraries from our earlier search. A newly kernel-checked
Lean/Rocq endpoint is absent; that does not invalidate the ordinary proof.

## Scope of independent inspection

I read the runtime/composition proof, routing/bootstrap proof, source builder,
bisimulation generator and verifier, both affine drivers, whole-frame engine,
macro induction engine, parameterization checker, frame-composition checker,
and the exact seed/calibration modules and notes. The following inherited
files are byte-identical to our previously fully reviewed246 package:

- `check_macro_inductions.py`
- `review_affine_source.py`
- `prefix_affine.py`
- pinned `Prog254.v`
- `independent-calibration.tex`

The supplied `LogicalSeed246.lean` is also byte-identical to the user's
7ba1598461c6e485c5aeb8f673c0b1d571f8012b snapshot. Thus the package's different
ProveIt provenance pin does not silently change the proof-search source,
logical seed, or calibration used here.

Independent source checks are reproducible with
`audit245_source_independent.py`; results are in
`audit245_source_independent.json`. Additional parameter/frame/macro results
are in `audit245_math_checks.json`. These are ordinary mathematical audits,
not formal proof objects.

## 1. Exact source preservation

The source tree used for the new machine must be proved equivalent, rather
than merely retaining the same multiset of leaves: break/continue semantics
can change under arbitrary reassociation. The package supplies a genuine
finite bisimulation, which closes this potential gap.

My independent checker does not import `rmpath` or its certificate generator.
It reconstructs old leaves using the separately reviewed literal parser of
pinned `Prog254.v`, loads the new complete tree, and checks prefix-free/full
binary structure. All6460 ordered operations and arguments agree. It then
implements zero-extended tree lookup, fixed-width increment and suffix
truncation independently, and checks the supplied reachable bisimulation:

-3013 reachable control pairs;
-6024 edges, both guards at every paired decrement;
-one paired halt;
-every increment/control segment finite, at most5 instructions;
-equal per-register increment vectors on paired segments;
-every paired decrement names the same logical register;
-all residual paths are clean, with only ignored zero suffixes.

Equal increment vectors act identically on every natural register vector,
because increments commute before the next decrement. Matching decrement
registers preserve both the test outcome and the common decrement effect.
Finite induction on a run therefore transports halting both ways, from every
common initial register vector. No bounded register samples or restricted
reachable-value approximation is used. The initial segments are checked too.

The new path metadata is consequently tied to the original calibrated
program, rather than an accidentally different proof calculus. The exact
all-values runtime certificate must use these same paths, and its hashes and
physical-register permutation are checked by the package and replay lane.

## 2. Soundness of the symbolic inference rules

The symbolic tape representation is complete: left marker, pointer word,
zero gap, header, nine primary blocks, a nonempty finite spare suffix and
both infinite blank exteriors. A block is B(v)=0 followed by v+1 ones.
Arbitrary unary variables and arbitrary finite block lists are universally
quantified, not chosen finite test values.

The allowed proof rules have ordinary soundness proofs:

1. A literal transition uses the actual table row and changes exactly the
   current cell, state and head.
2. A self-loop scan over a run of length L is induction on L. It requires the
   move to point along that run and the target state to equal the current
   state. L=0 uses no step; L+1 uses one row and the induction hypothesis.
3. An unknown affine run is peeled only when its constant term proves length
   at least1. An undetermined zero-versus-positive branch is never guessed.
4. The four one-block theorems are derived by literal/unary rules with opaque
   arbitrary left and right contexts. They retain the same state and scan
   orientation while crossing exactly one block. Structural induction then
   licenses crossing an arbitrary finite list. The symbolic width variable
   denotes that list's actual finite encoded width; B and C blocks have the
   same width v+2.
5. The only additional word rewrite is C(A)1=1B(A), for C(v)=10 followed by
   v ones, and its reversal. Empty-list and cons induction prove it directly.
   It is an equality of complete finite words, not a tape-effect assumption.

The finite-list rule is generated only from these checked one-block theorem
signatures. Opaque contexts are never inspected. The symbolic engines reject
an unproved opaque-list encounter, an unjustified unknown-length branch, a
negative run, or exhausted symbolic fuel. They cannot turn an unresolved run
into acceptance.

The macro engine is rerun with TABLE set to this exact245 table. It proves
four traversal lemmas, positive decrement, zero decrement, increment and all
nine selectors. The zero-decrement proof explicitly exposes a following
block; the nonempty spare suffix guarantees one even at the last primary.
Increment appends a value-one spare; no macro removes the final spare.

The affine box interface permits a decrement only for the same physical
register named by the case guard, and only after marking that register. It
rejects a second operation on an already modified box. All342 interface
checks pass. Thus the opaque box interface is justified by the derived
actual-table macros, rather than assumed from a predecessor machine.

## 3. Padding, whole-frame effects and closure

The new tree has maximum path length51. The invariant uses header distance
D=64+n for arbitrary n>=0, so every initial pointer has a nonnegative gap.
The adaptation checker establishes literal source-body equality with the
reviewed affine rules except matched source/target padding, its input bound,
portable imports and output metadata. In particular, it changes no tape
transition, inference rule, named guard or register effect.

For each complete leaf path and each relevant decrement guard, the target
is a complete frame. It retains the entire successor word, including all
trailing zero cells and overflow. It has the specified single register
effect, unchanged other registers, and exact spare suffix. There are8391
obligations:1931 zero decrements,1931 positive decrements,2601 increments,
128 breaks,1799 continues and one halt. The independently replayed minimum
literal progress is13, not zero or merely a count of administrative rewrites.

Let o be pointer overflow and delta be1 for positive decrement,0 otherwise.
The endpoint head is h-o and its distance is D+delta+o. Therefore the new
parameter n'=n+delta+o is nonnegative. The spare suffix stays nonempty.
Every accepted scan/macro clock is a finite expression in finite register
values and list widths, so each simulated instruction really terminates.

I also ran the independent frame checker: all8390 nonhalting residual
pointers normalize to a next source leaf by an exact word equality, adding
or dropping only zero suffix cells while compensating the gap. The minimum
constant gap is13. Its delta histogram is6456 cases with0 and1934 with1.
The empty pointer normalizes correctly at the initial root. This closes the
iteration obligation; a finite one-instruction test alone would not suffice.

The expanded whole-frame engine genuinely replaces all nine register boxes
by separate arbitrary natural variables. In `--all-values` mode it discards
all interval restrictions, represents a positive selected register as1+x,
and uses a separate gap variable and an arbitrary first spare plus arbitrary
finite spare tail. It checks exact head displacement as well as the complete
tape and positive finite clock. Its rules are the literal/unary/list rules
above. Thus a passing expanded run is an independent implementation of the
same universal theorem, not merely8391 numerical examples.

## 4. Initialization and positive simulation

The claimed literal blank endpoint is

- old state96, head-5, marker-6, header176, D181;
- empty pointer;
- physical registers(0,0,0,3,0,0,3,0,0);
- logical registers(N,T,W,A,D,H,X,Y,L)=(3,0,0,0,3,0,0,0,0);
-167 spare blocks, all1, and exactly351 one-cells in the entire tape.

The archive checks sparse and dense literal executions for407915 steps and
compares the entire finite support, not a selected tape window. The complete
frame checker reconstructs exactly this support from the register/spare
values. The parent audit separately repeats the literal blank run. D181
initializes the arbitrary parameter at117, and the logical formula-bearing
registers T,W,H are all zero.

The bootstrap lock and1410 scanner contractions offer an explanatory second
route, but the theorem does not need to trust scanner shortening globally.
Its recurrent behavior is checked on the actual shortened table in every
guarded instruction case. A six-zero source bound alone would not prove it.
Likewise, label74's new grammar role is not confused with its removed fixed
scanner role; roles are charged in the actual245-state table.

For the unbounded simulation, every nonhalting source step has a positive
finite binary segment to another covered frame. A terminal source instruction
has a finite segment to the sole halt. Forward induction gives halting
preservation. For reflection, strong induction on a finite binary halting
time removes the next positive segment. Determinism prevents a nonterminal
segment from having crossed the halt earlier. No infinite choice, uniform
runtime bound, or coinductive assumption is needed. The blank prefix and
source bisimulation therefore yield exactly

    Halt(M245, blank) iff Halt(original p254, logical seed).

## 5. Composition inside ordinary ZFC

The seed is exactly the one already calibrated by `LogicalSeed246`, using
`DirtyProgram254.six_nonformula_path_iff 3 0 3 0 0 0` and the original-program
adapter. Safety is supplied by truth0 and good empty stack. Dirty-root
completeness supplies arbitrarily large padded contradiction programs, so
starting the candidate counter at3 omits no possible refutation. No stronger
axiom set or weakened freshness/equality rule has been substituted.

The previously reviewed endpoint chain is native numerical C254 refutation,
native theory refutation, ZF refutation, and conventional ZFC refutation.
Foundation and Choice adapters remain present. Set-coded first-order
completeness, bisimulation quotient, internally well-founded subdomain and
internal constructible subdomain are ordinary constructions inside ZFC.
They do not require a transitive, externally well-founded, or externally
omega-standard model. Satisfaction is for set structures, not a truth
predicate for the universe.

All new proof obligations are finite syntax computations and induction on
natural numbers, finite words/lists or finite computations. They are
formalizable inside ZFC. Thus composition proves

    ZFC proves: Halt(M245, blank) iff exists a conventional ZFC refutation.

Classical negation yields the requested statement

    ZFC proves: Nonhalt(M245, blank) iff Con(ZFC).

No consistency assumption is used in proving this biconditional. A later
assumption Con(ZFC) gives actual nonhalting and the usual unprovability of
that nonhalting statement. Two-sided independence is a different assertion
and needs appropriate extra soundness hypotheses; it is not needed here.

## Residual limits

No new Lean/Rocq kernel endpoint or serialized ZFC/PA proof object is supplied.
That is the stated mechanization boundary, not an ordinary mathematical gap.
The claim is not minimality among all machines. Search heuristics, finite
literal fixtures and blanket claims of row coverage are supplementary; the
universal induction/macro/frame/source chain above is what justifies the
unbounded conclusion. No external repository write was performed.

## Final corroboration received

The independent runtime lane completed `verify_all --whole-frame --literal`
successfully (exit0). Its fresh expanded all-values run checks8391 cases,
2312645 symbolic rules and all490 table rows, with minimum13 literal moves.
All8390 normalization gates and all8385 regenerated literal fixtures pass.
This closes the pending optional replay mentioned above and independently
corroborates the universal macro-based proof already accepted here.
