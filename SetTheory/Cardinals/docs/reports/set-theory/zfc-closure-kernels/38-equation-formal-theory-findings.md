# Exact model comparison for the original four-tag calculus

## Result and provenance

This continuation proves a previously missing implication in the ProveIt snapshot
`426592ce97e52d309bfb8f0132411556650b7ac1`:

> For every irreflexive membership structure, the original decoded-bundle model
> predicate and the original encodable-bundle model predicate are equivalent
> on that same structure.

It also identifies these predicates with an explicitly defined **native-equality**
CP/GIC model predicate and upgrades the abstract six-register enumerator to an
if-and-only-if characterization by absence of a nonempty model of that exact
theory. These are new Lean proofs in this deliverable. They do not change a
Turing-machine table, the numerical codec, any logical rule, or either original
bundle gate.

The new source files are:

- `src/BusyBeaver/ZFC/ModelBridge254.lean`;
- `src/BusyBeaver/ZFC/EnumModelBridge254.lean`;
- `src/BusyBeaver/ZFC/ModelBridge254Checks.lean`.

Their dependencies are 23 unchanged source files fetched from the immutable
commit above through the GitHub connector. `source_manifest.json` records
their original repository paths and Git blob identities. The build script
checks every Git blob identity before compiling the narrow source closure.

The cited user commits have distinct scopes. Commit
`6d8bc7f1ba02c83e54757366f019f61b966ed0b7` reconciles six reports, including
ordinary PSC saturation, the prior public 253 construction, and several
different 252-state artifacts. Commit
`63c83cf79986f8a92bb75460848a1d4f863b7b15` catalogues those reports.
Commit `0301aa64e0676bed17402a63de46996631252a51` proves the complete
312,975-step public-253 blank bootstrap, ending in state 33 at head -17 with
every tape cell specified. That finite bootstrap is substantial verified
progress, but does not itself prove arbitrary runtime simulation or the
internal consistency endpoint. The present continuation concerns the later
original-code model interface, whose reverse implication is explicitly left
open in `Code254Models.lean` at our pin.

## Exact theories

Fix a domain D and a binary relation E on D. Write IR(E) for

    for every x in D, not E(x,x).

Let delta(c) be the repository's all-natural original base-four decoder, and
let B(a,b,c) be the original numerical C/G/vacuity bundle. Its gate is exactly
c != a and c != b; it does not require a != b.

The decoded model predicate is

    Dec(E) :=
      for every a,b,c with c != a,b, and every valuation e : N -> D,
      Sat_E(e, delta(B(a,b,c))).

The encodable model predicate is

    Enc(E) :=
      for every Bottom-free named formula f whose literal encoder value
      equals B(a,b,c) for some gated a,b,c, and every valuation e,
      Sat_E(e,f).

These are the unchanged `Code254Models.ModelsDecoded` and
`Code254Models.ModelsEncodable` definitions.

Define Native(E) to require the actual `ProfileModel.containerForm` at
every valuation and the actual `ProfileSyntax.gicForm(phi)` for **every**
`SetTheory.Form` matrix phi at every valuation. Equality in a matrix is
actual equality of D. This is the new `ModelsNativeCPGIC` definition.

The checked statements include:

    IR(E) -> (Dec(E) <-> Enc(E))
    IR(E) -> (Dec(E) <-> Native(E)).

Consequently these three model predicates are equivalent on each irreflexive
structure. This is stronger and more precise than an equiconsistency
statement. The structure is unchanged; no quotient domain or modified
membership relation is used.

The model predicates are all vacuously true on an empty domain. Their
equivalence therefore needs no global inhabitant. In contrast, every
no-model/refutation theorem explicitly includes a valuation N -> D.
Its value at zero supplies an inhabitant, preventing the empty-domain
loophole previously corrected in the repository.

## The key observation: an already available stronger interface

The obvious attempted inverse would decode a numerical bundle, then encode
its decoded matrix. It cannot assume enc(delta(c)) = c. Code zero is a truth
alias, and positive codes may contain zero children. This is precisely why
an all-code argument is needed.

The useful pre-existing theorem is
`Code254GIC.collection_of_matrix`. Its matrix parameter is an arbitrary
actual `SetTheory.Form`, with no `EqualityFree` hypothesis. It states that
an irreflexive Enc model, with a valuation, supplies the global-image
collection instance for that matrix.

The exported `modelsCPGIC_of_encBundle` theorem discards some of this
strength because `ProfileModel.ModelsGIC` restricts matrices to equality-free
formulas. The stronger `collection_of_matrix` theorem itself retains
native equality. Its proof translates all formulas to named formulas,
preserving equality atoms, then pads the matrix to meet the actual original
bundle gates.

This difference is decisive. The newest `DuplicateProfiles.lean` theorem
correctly constructs, conditional on a nonempty equality-free CP/GIC model,
an irreflexive Boolean duplicate that is still an equality-free CP/GIC
model but fails native-equality GIC. The fixed native equality matrix
Eq(1,2), code 35, forces a literal singleton, whereas every duplicate set
contains both copies or neither.

That obstruction remains valid. The new proof does not infer native equality
from the weaker equality-free interface. It starts from Enc, whose stronger
native-equality collection interface was already available. Thus there is
no contradiction between the new model equivalence and the duplicate-model
obstruction.

The ordinary observational-equality interpretation may still be useful for
equiconsistency between equality-free and native presentations. It is not
needed to establish this particular same-structure equivalence.

## Proof of the new reverse direction

### 1. Translate an arbitrary decoded matrix exactly

For a valuation e and names a,b,c, define the binary relation

    R(x,y) := Sat_E(e[a := x][b := y], delta(c)).

The existing `NamedForm254.matrix` translates delta(c) to an actual
de Bruijn `Form` representing this relation. It handles shadowed binders
and repeated names. In particular, when a=b the output update has
precedence, exactly as in the displayed definition.

Apply `Code254GIC.collection_of_matrix` to that translated formula.
The result is the global-image collection instance for R:

    for every A there is S such that
      every y in S satisfies R(x,y) for some x;
      for every x in A for which some R-output exists,
      some R-output belongs to S.

No semantic schema over arbitrary external predicates is assumed. The
relation R is represented by one explicit first-order matrix generated from
delta(c), and collection is invoked for that actual matrix.

### 2. Use semantic all-code freshness

The existing `DecodeFresh254` module proves that for positive c every
variable label occurring in delta(c) is less than c. At c=0 the syntactic
claim fails, since delta(0) is Rel(0,0) -> Rel(0,0), but its satisfaction
is independent of the valuation.

The resulting semantic statement is uniform:

    Sat_E(e[c := s][a := x][b := y], delta(c))
      <-> Sat_E(e[a := x][b := y], delta(c)).

It holds for every c, including zero. This statement is used directly;
there is no assertion that enc(delta(c))=c.

The proof also compares environments below c to remove shadowed repeated
updates. Those comparisons are purely finite variable-index calculations.

### 3. Validate the literal C tree

The container resource says that each object p belongs to a transitive
container V such that each x in V has a power bound P in V containing
every subset of x.

Choose such a container for the object e(c). If a and b are distinct,
the original named C tree is exactly this property after the three
bound variable updates are simplified using the gates.

If a=b, its universally quantified closure premise becomes E(x,x).
IR makes that premise false, so only the requirement e(c) in V remains.
The same chosen container therefore witnesses this degenerate case.
The proof explicitly splits a=b rather than silently strengthening the
machine gate.

### 4. Validate the literal G tree

Apply the collection instance for R to A=e(b), obtaining S.
The outer existential binding of c to S does not change the matrix's
meaning by the semantic freshness theorem.

When a and b are distinct, the G coverage clause is exactly collection
coverage. The support clause writes the updates in the opposite order,
but distinct updates commute, so it is exactly collection support.

When a=b, the coverage premise is again E(x,x) and is false by IR.
For support, R(x,y) means that delta(c) holds with the common name assigned
y; the input x has been overwritten. Given support at y, choose y itself
for the existentially rebound common name. This is the small but necessary
point in the degenerate case.

The proof retains native equality throughout. An equality matrix therefore
means identity in the same D, rather than a profile equivalence.

### 5. Add the two vacuity clauses

The membership-vacuity and equality-vacuity clauses hold because their
quantifier name c differs from both atom names a and b. The two original
gates are used exactly here as well as in the preceding named-tree
calculations.

Finally, the existing semantic rules for numerical implication, conjunction,
existential quantification, universal quantification, membership and equality
identify satisfaction of delta(B(a,b,c)) with satisfaction of the literal
named bundle whose matrix is delta(c). This includes the numerical truth
alias; no syntactic round trip is required.

These five steps establish Enc(E) -> Dec(E).
The already proved `encodable_of_decoded` supplies the converse.

## Refutation and abstract enumerator consequences

The original code calculus `Code254.C254` has all eight original logical
rows, truth code zero, modus ponens, generalization, and the original gated
bundle. Falsity code F is the number 1.

Its existing soundness theorem uses Dec models, while its existing
completeness theorem uses Enc models. Before the new result, the two
directions had different model interfaces. They now have exactly the
same interface:

    C254(1) <->
      there is no nonempty irreflexive Dec model

and equivalently

    C254(1) <->
      there is no nonempty irreflexive Native CP/GIC model.

The source states “no nonempty model” as a universally quantified implication
that includes an explicit valuation. It does not assert that any model
exists.

The unchanged `Enum254.enum_halts_iff` theorem states that the abstract
six-register enumerator halts from zero exactly when C254(1) holds.
The new `EnumModelBridge254` module composes the equivalences and proves

    Enum254.Halts <->
      there is no nonempty irreflexive Native CP/GIC model,

with a parallel theorem for Dec models.

This is a theorem about the already defined abstract enumerator. It is not
an execution theorem for the 6,459-row `Prog254`, the compiled binary
interpreter, or either published finite-state table.

## Relation to the full research goal

This closes a real logical gap in the original-code verification route.
It does not make a 248/250/251/252 experimental frontend complete, prove a
new Turing-machine state bound, or finish

    ZFC proves (M does not halt <-> Con(ZFC)).

The exact remaining tasks should be kept separate:

1. Obtain the required effective consistency comparison with full ZFC,
   including Foundation and Choice, in the exact syntax and proof coding
   used for the target. The current Lean quotient development reaches
   ZF0, which omits Foundation and Choice. The repository's
   `foundation_choice_route.md` gives explicit remaining finite-refutation
   translation targets and relevant pinned upstream Coq sources.
2. Identify the abstract enumerator with the actual register decoder
   and then with all binary executions from the verified blank bootstrap.
   A finite bootstrap and separately checked register boxes do not prove
   this unbounded simulation by themselves.
3. Relate the Lean-level semantic theorem and proof calculus to the
   arithmetized predicates occurring in the asserted internal-ZFC theorem.
   A Lean proof over arbitrary types is not itself a serialized ZFC proof,
   nor an automatic arithmetic proof-code translator.
4. For any proposed smaller machine, account for the whole blank-start
   implementation: interpreter, stored program, initialization, halt
   convention, and all transitions.

The inherited reduced equality-free C/G experiments fail an independent
logical-completeness condition: the fixed-variable sorted countermodel
already recorded in the repository. The new proof deliberately retains
native equality and all original logical rows. It therefore repairs the
original route without rehabilitating those reduced calculi.

## Verification and integration

Run:

    ZFC_LEAN=/path/to/lean-4.32.0/bin/lean python build.py

The build requires only Python's standard library and the Lean 4.32.0
toolchain. It checks the pinned Git blob identities, compiles the entire
narrow source closure serially, then writes per-module logs and a summary
with source SHA-256 identities and printed axiom dependencies.

The new mathematical theorems use only the ordinary Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`. There are no custom
axioms, `sorry`, or `native_decide` proofs in the new files. The two
concrete caller checks cover native equality code 35 and the joint
edge case c=0, a=b=1; the empty-domain caller confirms that the model
equivalence itself needs no hidden inhabitant. These callers retain
the enormous encoded bundle numerals symbolically by a local elaboration
transparency setting. They do not change any definition or axiom.

For repository integration, copy the three new files into
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/` and import the two main
modules from the opt-in umbrella if desired. Extend the project's fresh
source runner with them. The bundled dependency sources are unchanged
reference material; they should not overwrite newer repository sources.

The README and comments that leave the same-structure Enc/Dec implication
open can then be updated to cite the new theorem. Comments warning that
equality-free `ModelsCPGIC` alone does not provide native equality should
remain: that warning is still mathematically correct.

## Immutable source references

- [Original model definitions and forward implication](https://github.com/VladimirReshetnikov/ProveIt/blob/426592ce97e52d309bfb8f0132411556650b7ac1/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254Models.lean)
- [All-formula native collection adapter](https://github.com/VladimirReshetnikov/ProveIt/blob/426592ce97e52d309bfb8f0132411556650b7ac1/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254GIC.lean)
- [All-code semantic freshness](https://github.com/VladimirReshetnikov/ProveIt/blob/426592ce97e52d309bfb8f0132411556650b7ac1/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DecodeFresh254.lean)
- [Exact named/de Bruijn matrix translation](https://github.com/VladimirReshetnikov/ProveIt/blob/426592ce97e52d309bfb8f0132411556650b7ac1/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/NamedForm254.lean)
- [Native-equality duplicate-model obstruction](https://github.com/VladimirReshetnikov/ProveIt/blob/426592ce97e52d309bfb8f0132411556650b7ac1/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DuplicateProfiles.lean)
- [Original numerical soundness and completeness](https://github.com/VladimirReshetnikov/ProveIt/blob/426592ce97e52d309bfb8f0132411556650b7ac1/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean)
- [Abstract enumerator equivalence](https://github.com/VladimirReshetnikov/ProveIt/blob/426592ce97e52d309bfb8f0132411556650b7ac1/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Enum254.lean)
- [Remaining Foundation/Choice comparison](https://github.com/VladimirReshetnikov/ProveIt/blob/426592ce97e52d309bfb8f0132411556650b7ac1/Computability/BusyBeaver/Research/ZFC/foundation_choice_route.md)

