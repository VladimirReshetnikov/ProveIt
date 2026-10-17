# The requested ZFC metatheory and the stronger PA project

## Precise distinction

The current request is for a finite binary machine M such that

    ZFC proves: Nonhalts(M, blank) iff Con(ZFC).

The repository also pursues a proof of the corresponding arithmetic sentence
in PA. That is a stronger demand on the available reasoning methods. The
unfinished represented proof translations in `pa_internalization.md` do not,
by themselves, obstruct an ordinary mathematical proof in ZFC.

The checked Lean endpoint is an external theorem about the literal machine
and the inductively defined first-order provability predicate. It should not
be presented as an already generated formal proof object in the repository's
object language of ZFC. Conversely, one should not infer that a mathematical
ZFC proof must wait for the PA coding project. A direct set-model argument is
available, with the following precise scope.

## Set-coded formulation

Inside ZFC, identify the natural numbers with omega. A deterministic binary
machine table is a fixed finite set of tuples. A finite computation is a
finite sequence of configurations; a configuration can use a finite set of
one-cell positions, a head integer, and a finite state. Equivalently one can
use a pair of finite tape words. These codings are intertranslatable by
recursion on omega. Let Halt_M(t) be the elementary arithmetic predicate that
t codes a blank-start halting computation, including the last write and head
move of the halting transition.

A formula or derivation is a finite syntax tree. A primitive recursive coding
gives an arithmetical predicate Proof_T(p,bottom) for the repository's actual
first-order calculus and literal axiom predicate T. The usual finite-tree
induction proves that existence of such a code agrees with membership in the
inductively generated derivability relation. This simple reification step is
necessary even when an external Lean theorem uses BProv in Prop.

Use the consistency statement

    Con(T) := for every p in omega, not Proof_T(p,bottom).

Different conventional finite proof calculi for the same ZFC axioms give the
same statement over ZFC by their ordinary derivation translations. This is a
specific syntactic consistency assertion, not the existence of a transitive
model and not the truth of ZFC.

## A useful countable-carrier lemma

**Lemma.** Suppose a countable first-order theory S has a nonempty model, and
a stated model construction uses only definable subdomains and quotients of
the input model. If that construction is proved uniformly for arbitrary
input structures and arbitrary finite formulas, then it can be carried out
inside ZFC using a set-sized countable carrier. It needs no inaccessible
cardinal, external well-foundedness of the input relation, or proper-class
domain.

**Proof.** By downward Loewenheim-Skolem, or directly by the countable Henkin
construction, take a model with nonempty domain D contained in omega. Its
membership relation is a subset of D squared. Satisfaction for this set
structure and arbitrary finite formulas is defined by recursion on formula
complexity. It is a set of tuples of formula codes and finite assignments,
all of which can be coded by natural numbers.

A definable subdomain is a subset of D by Separation. If E is the equivalence
relation used in a quotient, retain the least natural-number element of each
E class; these representatives form a subset of D. The quotient relation is
transported to those representatives. This uses the well-ordering of omega,
not an assumption that the modeled membership relation is externally well
founded. Iterate the construction as needed. A class definable *inside the
input model*, such as its internally well-founded part or its constructible
class, becomes an ordinary subset of the external set D. Uniform formula
induction supplies the interpretation and scheme laws for every ambient
finite formula code in omega. This is not an identification of ambient
omega with the possibly nonstandard natural numbers inside the model. All
objects used exist in ZFC. QED.

This lemma addresses the set-theoretic interpretation of the source proof;
it is not a global soundness proof for Lean, nor a claim that every Lean
universe can be interpreted inside ZFC. Only this concrete countable model
argument is interpreted.

For these sources the uniformity condition is visible in the interfaces:
the ZF Separation and Replacement fields quantify over the concrete Form
datatype, and the relevant interpretation theorems retain an arbitrary
phi:Form. The ambient model is never assumed transitive or externally well
founded. This distinction is essential when the metatheory reasons from
Con(ZFC) alone.

## Model-comparison theorem in ZFC

Let T be `NativeTheory254.NativeAx`: the universal closure of the literal
container axiom, all literal native-Form global-image collection instances,
and irreflexivity. The repository establishes two uniform model constructions:

1. From a nonempty model of ZF, the rank construction supplies the container
   and global-image collection interpretation and therefore a model of T.
2. From a nonempty model of T, form the profile quotient and take its
   *internally* well-founded part. The resulting nonempty structure is a
   model of ordinary ZF, including Power and Foundation. Closure is supplied
   by the actual collection instance, not by an unsupported assumption that
   every foundation-free ZF model already satisfies arbitrary Collection.

The separate constructible-model comparison gives a model of ZFC from any
nonempty ZF model, by passing to that model's own L. ZFC models already satisfy
ZF. Thus, with all constructions interpreted as in the countable-carrier
lemma, ZFC proves

    ExistsModel(T) iff ExistsModel(ZF) iff ExistsModel(ZFC).

First-order soundness and completeness are theorems of ZFC for these
countable, set-coded theories. Applying them to the two sides yields

    ZFC proves: Con(T) iff Con(ZF) iff Con(ZFC).

No consistency premise remains in this biconditional. Using the implication
Con(ZFC) -> ExistsModel(ZFC) does not prove Con(ZFC). Similarly, the output
model is not asserted to be transitive or to have the ambient omega as its
internal natural numbers.

## Connecting a literal proof-search machine

For the exact baseline machine, the source-specific ingredients are:

1. A finite blank computation reaches the stated clean source frame.
2. Every accepted binary instruction has the complete stated frame effect
   with a positive running time, for arbitrary relevant register values,
   gaps, and valid spare suffixes. Decoder coverage and absence of stray
   halting account for every possible runtime continuation.
3. The finite control program implements the command enumerator. Its command
   pointers decrease inside a candidate, candidate numbers increase, and the
   persistent theorem-stack invariant proves soundness.
4. A derivation-to-command-block construction proves completeness from the
   actual initial candidate counter. It does not assume whole-state resets
   between candidates.
5. The numerical C254 derivability relation and the literal first-order
   native theory have equivalent refutability.

The recorded proofs of these ingredients use the specified finite data,
recursion and induction on omega, and the set-coded satisfaction relation
above. Reconstructing those proofs with these codings gives their ZFC
versions; the mere fact that a statement concerns finite objects would not
be a proof that it is ZFC-provable. Assuming the exact recorded ingredients
and their indicated reconstructions, ZFC proves

    Exists t Halt_M(t) iff Exists p Proof_T(p,bottom).

Negating and composing with the model-comparison theorem gives the requested
mathematical theorem

    ZFC proves: not Exists t Halt_M(t) iff Con(ZFC).

For a changed source program, step 4 must be replaced by its new theorem, such
as the destructive-AX theorem in the companion note. For a changed binary
table, steps 1-3 require new exact certificates or a formally justified
simulation transfer. The logical comparison in step 5 and the native/ZF/ZFC
model constructions are reusable when the full C254 calculus is unchanged.

## What remains to be formalized and what does not

There are three different deliverable levels:

- A mathematical proof carried out in ZFC using the above finite encodings,
  induction, completeness, and set-sized model constructions.
- A checked external Lean theorem about the corresponding mathematical
  objects, which is what the pinned baseline endpoint records.
- A serialized proof in an explicitly defined object theory, with theorem
  quotation and an object-level proof checker, which would connect the first
  two levels in the repository's chosen formal framework.

One should state which level a new deliverable supplies. The handwritten ZFC
argument does not manufacture the third level. The external Lean audit also
does not, merely by listing its axiom dependencies. However the current user
request does not require a PA proof, and the direct mathematical argument
does not need an effective ZFC-to-ZF proof-code translator. Existential
refutation transfer through completeness suffices inside ZFC.

For PA, the same appeal to arbitrary set-model existence is unavailable.
Uniform translations on represented proof and trace codes, correct for all
elements of every PA model, are a separate and substantially more demanding
formalization. The repository correctly leaves that endpoint open.

## Primary source locations

All ProveIt URLs below are pinned to
`43026ff42f0939f09b9e95495248cfadcad38e38`.

- [Baseline machine and exact proof boundary](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Research/ZFC/candidate-permutation252/README.md)
- [BinaryZFC252 endpoint note](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Research/ZFC/binary_zfc252.md)
- [Choice calibration and its formal boundary](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Research/ZFC/choice_calibration254.md)
- [Native first-order theory](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/NativeTheory254.lean)
- [Native/ZF comparison](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WFTheory.lean)
- [Internally well-founded model construction](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WFModel.lean)
- [The stronger PA endpoint inventory](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Research/ZFC/pa_internalization.md)
