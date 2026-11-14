# PA195 diagonal-freshness prerequisite

The diagonal calculus uses the numeric code `4 * Cantor(a,b) + tag` for
formula constructors. `PA195FreshBound.candidate_pra_fieldBound` is a Lean
proof of an actual theorem of candidate classical PRA: if that code is
positive, each of its two decoded Cantor fields is strictly smaller than the
code. The statement uses the bounded arithmetic graph of the literal Cantor
pairing, not Foundation's distinct pairing convention. Its model proof holds
in every model of IOpen, hence in every candidate-PRA model, including
nonstandard models; first-order completeness supplies the PRA derivation.

This proves only the immediate-field bound. It does not yet encode the
recursive occurrence predicate, prove the code is absent from its own decoded
formula, verify any generated proof template, or connect a PA refutation to
PA195 halting. The arithmetic needed to verify a primitive-recursive generator
must be distinguished from the possibly unrestricted PA induction instance
that generator inserts inside a PA proof.

To check from the repository root, set `IPRA_LEAN_OVERLAY` to the matching
audited project object directory and `IPRA_FOUNDATION_OVERLAY` to the matching
Foundation object directory, then run:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check.sh
```

The script verifies source and direct object hashes and rejects `sorryAx` in
the printed theorem dependencies. It uses the supplied audited object
directories; it does not rebuild their transitive dependencies.

`PA195DecodedFields.candidate_pra_decodedFieldBound` strengthens this to the
actual first decoder step: it uses the bounded graph for `p = n / 4`, then
the Cantor graph for its two components, and proves that both components are
strictly less than every positive `n`. Its supporting semantic theorem holds
for arbitrary IOpen model elements. Check this extension, including a fresh
build of `PA195FreshBound.olean`, with the same overlay variables:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-decoded.sh
```

This still proves only one decoder step, not represented recursive occurrence
or self-freshness.

`PA195PathBound.lean` proves an all-model path-descent result using candidate
PRA's open induction. For a supplied binary primitive-recursive function code
and seed, its values must describe a path whose intermediate nodes are positive
and whose next node is one of the two Cantor fields of the current node divided
by four. For an arbitrary, potentially nonstandard model-length limit, the
result bounds every visited node by the root and shows that every field of a
visited positive node is strictly below the root. `path_self_fresh` states
this as absence of the root from an explicitly defined path-occurrence
over-approximation.

The function code and its step equations are explicit hypotheses. The actual
PA195 recursive occurrence predicate and a path extractor connecting it to
the supplied code have not yet been defined or proved correct, so this is
not yet full self-freshness or a syntactic PRA theorem about that predicate.
To check the path result and rebuild both earlier calibration modules, use:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-path.sh
```

`PA195OccursFormula.lean` represents the path-occurrence over-approximation and
its positive-child step premise as explicit formulas of the candidate-PRA
language. For each **fixed** binary primitive-recursive path code `f`,
`candidate_pra_represented_path_fresh` proves the universally closed
conditional as an actual candidate-PRA theorem: if the represented path
obeys the represented step condition, its root does not occur as a Cantor
field on that path. The semantics of both formulas are checked in every
candidate-PRA model, including nonstandard ones. The fixed `f` is a theorem
parameter, not an internal quantifier over function codes.

The same four-tag decoder and diagonal clause are used by PA194. This
represented predicate remains an over-approximation for a *supplied* path;
no extractor has yet been shown to turn an arbitrary PA194 decoder
occurrence into such a path, so the theorem does not establish complete
self-freshness of the PA194 decoder. To check the representation and PRA
theorem using the same audited overlays, run:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-occurs.sh
```

`PA194ChildCodes.lean` uses candidate-PRA bounded witnessing to prove the
existence of a primitive-recursive function code for each of the exact two
PA194 decoder-child functions, `first(n / 4)` and `second(n / 4)`, together
with candidate-PRA proofs of their represented graph instances. The model
lemmas confirm those code values in every candidate-PRA model. These witness
codes are existentially supplied by Lean; an explicit serialized code is not
exported. A branch-choice iterator and the connection from arbitrary actual
decoder occurrences to such a path remain to be constructed.

To check the child-code results and freshly build their two earlier
prerequisites, use the same audited overlays and run:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-child.sh
```

`PA194PathZero.lean` removes the earlier positive-intermediate-node assumption:
both decoder children are at most the parent even for code zero, so model-length
child paths remain bounded through the truth-code case. Occurrence still
requires its visited node to be positive.

`PA194PathIterator.lean` explicitly constructs a primitive-recursive path
code from supplied root and branch-choice codes and the two child witness
codes. Given candidate-PRA graph proofs for those child codes, its model-step
theorem shows that each step chooses one of the exact decoder fields in every
candidate-PRA model. It does not require the branch selector to be Boolean:
zero chooses the second child and any nonzero value chooses the first. The
resulting path self-freshness theorem allows nonstandard model-length limits
and needs no positive-intermediate-node premise. Root and choice codes and
child-graph proofs are explicit parameters; the final extractor from arbitrary
actual decoder occurrences into those choices remains unproved.

To check these results and freshly rebuild their dependencies, run:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-iterator.sh
```

`PA194BranchSeed.lean` constructs the parameter interface for the branch
iterator. Candidate PRA supplies existential primitive-recursive witness codes
for both projections of an auxiliary seed pair and a Boolean branch-word bit
reader. In every candidate-PRA model, the seed packs a root and branch word;
the path starts at that root and its next exact decoder child is determined by
the branch-word bit at each index, including nonstandard indices. The
auxiliary seed uses Foundation's pairing; PA194 formula codes still use the
distinct Cantor pairing. The witness codes are not serialized.

This interface does not yet prove that an arbitrary occurrence in the actual
PA194 recursive decoder supplies a suitable branch word, nor does it prove a
consistency or halting implication. To check it with the same audited overlays
and fresh local prerequisite builds, run:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-branch.sh
```

`PA194StrongInduction.lean` derives strong induction for any fixed binary PR
code in every candidate-PRA model, using bounded induction. The companion
`PA194OccurrenceStrong.lean` proves self-freshness without constructing a
branch-word path: for a supplied binary PR occurrence code, it assumes that
any nonzero occurrence result at `(n, v)` comes from a positive `n` and is
explained by one of the two immediate Cantor fields of `n / 4`, or by a
nonzero occurrence result at one of those children. Under that uniform
one-step coverage hypothesis, every reported label is below its code, so the
code cannot occur in itself, including at nonstandard model elements.

This theorem still assumes the occurrence code and its all-model coverage
property. It does not construct PA194's actual occurrence code or establish
that property for it. Check the bounded-strong-induction route using:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-strong.sh
```

`PA194PackedDescent.lean` proves an actual candidate-PRA theorem that packages
a formula code and candidate label using an auxiliary Foundation pair. For a
positive PA194 formula code, pairing either exact quotient/Cantor child with
the same label gives a strictly smaller index. This is a rank ingredient for
an occurrence fixpoint; it does not construct the occurrence code or prove
its recursion-coverage property. The auxiliary Foundation pair is distinct
from the Cantor pair used by the PA194 decoder.

Check the theorem and freshly rebuild its calibration prerequisites with:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-packed.sh
```

`PA194OccurrenceCore.lean` defines the actual bounded one-step occurrence
core for PA194's four-tag numeric decoder. It treats code zero as truth,
recurses into both children for implication, exposes both labels for
membership and equality, and exposes the binder and recurses into the body
for universal quantification. The semantic theorem checks this exact reading
in every IOpen model; packed-child descent removes the explicit rank guards.
The history is interpreted through the bounded bit graph. Candidate PRA
supplies existential primitive-recursive codes both for the Boolean core and
for one bounded-history successor update of its fixpoint blueprint.

The successor code is not yet an iterated occurrence code. Correctness of the
full model-length stage iteration and identification with the recursive
decoder remain open. To check this module with the same audited overlays and
fresh local dependency builds, run:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-core.sh
```

`PA194OccurrenceStage.lean` gives an explicit primitive-recursive stage
iterator for any certified successor code. In every candidate-PRA model,
including nonstandard stages, it proves the base and successor equations and
the successor graph. For the concrete history collector, it also proves the
exact bounded-bit membership equation, with its code-correctness proofs stated
as hypotheses. It does not yet show stabilization of history bits, construct
the final occurrence predicate, or establish its recursion coverage. Check it
with the same audited overlays using:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-stage.sh
```

`PA194OccurrenceStageCore.lean` specializes the stage iterator to the actual
PA194 occurrence core. Candidate PRA certifies the required Boolean core,
history insertion, and bit-test component codes. For any such certified
codes, `modelStageRec` proves the exact four-tag decoded-child recurrence at
every stage of every candidate-PRA model, including nonstandard stages. This
still does not prove stabilization or the final occurrence coverage property.
Check the specialization and freshly rebuilt local prerequisites using:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-stage-core.sh
```

`PA194OccurrenceLocality.lean` proves that the occurrence core at packed index
`x` depends only on history bits below `x`. `PA194OccurrenceStable.lean`
uses an explicitly represented bounded invariant and candidate-PRA strong
induction to show that every bit `x` at any stage `t > x` agrees with its bit
at stage `x + 1`, even for nonstandard model elements. The theorem assumes a
candidate-PRA-certified bit code and the stated exact stage-update equation;
the preceding stage-core module supplies the latter for certified occurrence
components. Construction of the final occurrence code and its coverage
property remain separate. Check the locality and stabilization proofs with:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-stability.sh
```

`PA194OccurrenceCoverage.lean` derives the exact decoder's one-step coverage
from a history satisfying the update and stability equations.
`PA194OccurrenceCode.lean` constructs a binary primitive-recursive code by
testing the packed `(formula, label)` index at its own successor stage.
For certified core, insertion, and Boolean bit-test components it proves that
this code satisfies coverage in every candidate-PRA model. Composing with
strong induction gives a syntactic candidate-PRA proof that the code reports
no occurrence of a formula code in itself. The theorem
`PRA_has_selfFreshOccurrenceCode` proves that suitable certified component
codes exist and supplies the resulting proof; those component codes are not yet
serialized as explicit numerals.

This establishes the freshness lemma for the represented four-tag decoder.
It does not yet bind the code to PA194's emitted proof templates or prove a
machine consistency/halting reduction. Rebuild the complete local chain and
check the theorem's axioms using:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-occurrence-code.sh
```

`PA194BitTranslation.lean` gives the first concrete PA-syntax translation
piece: substitute source labels `a,b` into Foundation's bounded arithmetic
bit formula. A general substitution theorem shows that no other free labels
appear; in particular, helper quantifiers do not capture source labels. A
separate semantic theorem identifies the resulting formula with the exact
Foundation bit graph. These are Lean theorems about actual formulas and
structures; they do not yet supply a primitive-recursive formula-code
translator, its correctness proof inside PRA, or any proof-template compiler.
Check them with the audited overlays using:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-bit-translation.sh
```

`PA194ZeroAlias.lean` checks the exceptional numerical alias `I(0,0)=0`
for the stated Cantor-based source constructor and proves in Foundation PA
that `(0=0)` is equivalent to `((0=0) → (0=0))`. This PA proof is obtained
through the completeness interface; it is not yet a serialized derivation or
a proof-producing compiler. Check it with the audited overlays using:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-zero-alias.sh
```

`PA194BindTranslation.lean` provides capture-avoiding closure for a named
source label using a fresh de Bruijn binder. It proves that closure introduces
no new free source labels and removes the selected label, and verifies that
universal closure has the expected valuation semantics, including beneath
nested quantifiers. These are Lean theorems for actual formulas and structures;
the represented formula-code translator, its correctness in PRA, and the
uniform proof-template compiler remain open. Check with the audited overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-bind-translation.sh
```

`PA194FVarCode.lean` implements an explicit primitive-recursive code that maps
any source label to the exact Foundation free-variable term code. Candidate
PRA proves its graph agrees with Foundation's `qqFvarDef`, and the model
theorem covers nonstandard labels. This supplies one atomic operation needed
by the represented source-to-PA translator; the recursive translator and its
correctness remain open. Check the component using the audited overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-fvar-code.sh
```

`PA194TagCode.lean` gives an explicit primitive-recursive constructor for
Foundation's one-payload tagged syntax and proves its graph in candidate PRA.
Its all-model `modelAllGraph` specialization certifies tag 6 as the exact
Foundation universal-quantifier constructor, including for nonstandard body
codes. This supplies another atomic operation, not the recursive translator
or its proof of correctness. Recheck with the audited overlays using:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-tag-code.sh
```

`PA194Vacuity.lean` proves that closing a label absent from an actual
arithmetic formula leaves its truth unchanged in every nonempty structure.
Consequently Foundation PA proves the universally closed vacuity instance
`φ → ∀a φ` for each such formula `φ`, using the capture-avoiding closure.
This family of PA derivations is obtained via the completeness interface; it
is not a represented primitive-recursive proof-template compiler, and it does
not yet connect the PA194 code's all-model freshness theorem to the translated
formula. Check it with the audited overlays using:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-vacuity.sh
```

`PA194VarVectorCode.lean` composes the represented free-variable constructor
with a PRA-certified sequence append operation to construct a two-entry HFS
sequence from source labels `a,b`. Its graph states that both entries have the
exact Foundation free-variable codes, in order, and candidate PRA proves this
graph; the required append code is supplied by an existence theorem. The
append code has not been serialized as a numeral. Foundation term vectors use
`Vec.adjoin`, not this `Seq.seqCons` encoding, so this is not yet a certified
Foundation term-vector constructor. The recursive source translator remains
open. Recheck with the audited overlays using:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-var-vector-code.sh
```

`PA194RelCode.lean` implements Foundation's exact relation-formula constructor
as an explicit ternary primitive-recursive code from arity, relation-symbol
code, and argument-vector code. Candidate PRA proves its `qqRelDef` graph,
and the model theorem applies to nonstandard inputs. Connecting it to the
two-variable vector and recursively decoding PA194 formulas remain open.
Recheck with the audited overlays using:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-rel-code.sh
```

`PA194AtomCode.lean` composes the certified two-label sequence and relation-code
graphs. Candidate PRA proves that composite numeric graph, and a suitable
sequence append code is supplied existentially. Since Foundation term vectors
use `Vec.adjoin`, this result does not establish that the output is the code of
a well-formed Foundation atomic formula. The intended equality case must still
bind the arity and relation symbol to Foundation's actual equality encoding;
source membership additionally requires construction of the expanded bit
formula. Recursive formula translation and its correctness remain open.
Check with the audited overlays using:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-atom-code.sh
```

`PA194CanonicalVectorCode.lean` constructs the correct Foundation term
vector for two variable codes by right-folding `Vec.adjoin`, rather than using
`Seq.seqCons`. The code is fully explicit, and candidate PRA proves its
`qqFvarDef`/`adjoinDef` graph for all labels. An additional theorem identifies
the numeric expression with Foundation's actual `matrixToVec` in models of
IΣ₁, where that syntax interpretation is available. This repairs the vector
representation needed for a real atomic formula constructor; composition with
`qqRelDef` and the full recursive translator remain separate. Recheck with:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-canonical-vector.sh
```

`PA194CanonicalAtomCode.lean` composes the corrected `Vec.adjoin` vector
with the relation-code constructor, using explicit PR codes throughout.
Candidate PRA proves the composite graph for arbitrary arity and relation
codes, including nonstandard inputs. A separate theorem identifies this value
with Foundation's named `qqRel` applied to its `matrixToVec` of free-variable
term codes in IΣ₁ models; the Foundation definitions used in that statement
are introduced under IΣ₁. The equality symbol and arity still need to be
bound for PA194's equality atom, and source membership still needs its expanded
bit formula. Check with the audited overlays using:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-canonical-atom.sh
```

`PA194EqAtomCode.lean` binds the canonical atomic constructor to arity two
and Foundation's equality relation symbol, whose encoded value is zero. The
result is an explicit binary PR code and candidate PRA proves its graph for
all labels. In IΣ₁ models a separate theorem identifies the value with the
Foundation relation constructor applied to the exact two-variable matrix.
The recursive PA194 source decoder and the membership/bit translation remain
open. Check with the audited overlays using:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-eq-atom.sh
```

`PA194BVarCode.lean` supplies an explicit PR constructor for Foundation's
bound-variable term encoding and a candidate-PRA proof of its graph. The
separate `PA194QuadCode.lean` supplies a generic four-field tagged constructor
and a candidate-PRA graph proof; its tag-2 specialization is checked against
Foundation's `qqFuncDef` in every candidate-PRA model. These are components
for compiling the fixed bounded bit formula, whose helper variables must
remain bound; the formula compiler and substitution correctness remain open.
Recheck both with the audited overlays using:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-bit-syntax-codes.sh
```

`PA194NumeralCode.lean` constructs, for each externally fixed natural number
and input arity, an explicit PR constant function code. Its value is checked
in every candidate-PRA model, and candidate PRA proves that its graph agrees
with the corresponding nullary constant code. This can supply fixed syntax
tags and symbol codes to a static bit-formula compiler; it is a family of
finite codes, not a dynamically chosen numeral compiler. Check it using:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-numeral-code.sh
```

`PA194BitTemplate.lean` statically compiles a fixed closed arithmetic syntax
template into a binary PR code, mapping the two outer placeholders to source
free labels while keeping locally bound indices. For every template, it proves
in all candidate-PRA models that the generated code agrees with an explicitly
defined numeric constructor specification. `bitTemplateCode` applies this
construction to Foundation's exact bounded bit formula. The remaining crucial
step is to prove that the numeric specification is the Foundation quote of
capture-avoiding substitution; it is not yet a verified membership translator.

`PA194BitTemplateSize.lean` provides a reproducible executable size probe. Its
`#eval` reports 1,503,347 nodes, counting both `Code` and `Codes` constructors;
this is an evaluation rather than a kernel-checked size theorem. The generated
code has not been serialized. Rebuild and run the probe with:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-bit-template.sh
```
