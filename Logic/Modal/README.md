# Foundation modal logic in Rocq/Coq

This project is an independent, idiomatic Rocq/Coq port of a high-value
semantic slice of
[FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation).
The source is pinned read-only at commit
`32e1a0956a8622fad067328ca1959729a7634428` under
`lib/FormalizedFormalLogic-Foundation`; none of the Coq modules imports or
modifies the Lean development.

The port focuses on results that are both central to Foundation's modal-logic
library and reusable while its larger named-system and canonical-model stack
is being reconstructed:

- primitive modal syntax, derived connectives, substitution, iteration,
  complexity, degree, subformulas, and complement-closed finite contexts;
- negation-normal syntax, structural De Morgan negation, modal CNF/DNF shape,
  direct semantics, and truth-preserving translations in both directions;
- executable Cantor encodings and surjective enumerations of ordinary and
  negation-normal formulas over natural-number atoms;
- a concrete Hilbert calculus for K with substitution, deduction, consistency
  criteria, contextual boxing, Kripke soundness, and syntactic consistency;
- a constructive-by-stages Lindenbaum extension for concrete K, maximal
  consistent theories, the canonical successor and truth lemmas, canonical
  countermodels, and soundness/completeness over all and finite frames;
- a reusable normal Hilbert calculus parameterized by substitution-closed
  modal axiom schemata, with weakening, K embedding, and soundness and
  consistency for KT, KD, KB, K4, K5, S4, S5, GL, and Grz;
- predicate-valued classical, quasinormal, and normal logics, their least
  normal and quasinormal sums, finite-basis and letterless omission theorems,
  and an exact finite boxed-context characterization of global consequence;
- a schema-generic Lindenbaum and canonical-model construction, specialized
  to canonical reflexivity, seriality, symmetry, transitivity, and right
  Euclideanity, with full soundness/completeness for KT, KD, KB, K4, K5, S4,
  and S5 and explicit small-frame strictness witnesses over K;
- schema-generic finite consistency over natural-number atoms, including the
  two insertion criteria, singleton and union laws, deterministic
  complement-closed extension, a finite-context Lindenbaum theorem,
  derivability/complement/implication membership laws, and an explicit
  powerset cover of the resulting context space;
- finite words of box, diamond, and negation, including polarity and exact
  size splitting, exhaustive finite size layers, formula action and
  substitution, syntactic translation/equivalence algebra, and reduction
  bootstrapping from a bounded set of modal lengths;
- a checked S5 normalizer sending every modal word to one of the six forms
  `id`, `not`, `box`, `diamond`, `not box`, and `not diamond`, together with
  actual S5 derivations of every returned equivalence and reduction;
- Kripke satisfaction, semantic substitution, iterated box/diamond laws, and
  validity of K;
- the relational complex algebra of every Kripke frame, with box/diamond
  laws, atom-polymorphic formula evaluation, and exact order/equality
  characterizations of implication, equivalence, and formula validity;
- complexity-bounded generated models with a strengthened budgeted truth
  lemma and invariance under changing the enclosing target formula;
- reflexive, transitive, and reflexive-transitive frame closures, their order
  properties, target termination, and converse well-foundedness results;
- PLoN's formula-indexed relational semantics, including all validity and
  countermodel equivalences and failure of replacement of equivalents;
- PLoN Hilbert soundness for arbitrary instantiated axioms, its explicit
  Lindenbaum and canonical-model completeness construction, and soundness,
  completeness, consistency, and strict-inclusion results for logic N;
- coarsest filtration through a formula's subformula closure, with a full
  truth lemma, a finite cover of at most `2 ^ length (subformulas p)` worlds,
  bounded finite countermodels, and both validity- and
  satisfiability-oriented semantic finite-model theorems;
- finest filtration and its nonempty-transitive-closure variant, including
  their truth lemmas, the same explicit finite bound, and preservation of
  reflexivity, seriality, symmetry, preorders, and equivalence frames;
- the general Geach axiom/frame-condition correspondence, with exact
  specializations T/reflexive, D/serial, B/symmetric, 4/transitive,
  5/right-Euclidean, Tc/coreflexive, and .2/strongly confluent;
- the .3/piecewise-strong-connectedness correspondence;
- the Kripke correspondence for Loeb's axiom;
- roots and transitive roots, direct and positive-reachability generated
  frames, inherited frame properties, generated submodels, and truth
  invariance through their bounded morphisms, including explicit inheritance
  of finite list covers by direct point generation;
- irreflexivization with exact reflexive-closure truth/validity transfer, and
  finite root extension with structural/tree laws, exact chain covers,
  embedding p-morphisms and truth preservation, added-root boxdot semantics,
  and finite-chain T-failure and witness theorems;
- the boxdot translation's basic semantic algebra, reflexive-closure
  characterization, and unconditional nat-atom K4/S4 preservation,
  reflection, and equivalence; finite GL/Grz and GL.3/Grz.3 frame
  transformations; the unconditional Triv-to-Ver direction; and explicitly
  dependency-gated reverse/named equivalences;
- Jeřábek's doubled-frame construction, its bounded morphism and six principal
  frame-class closure results, flags and boxdot logic properties, together
  with a precise explicit gate for the unavailable global finite-consequence
  argument behind the strong boxdot theorem;
- clusters and their (strict) skeletons, natural and explicitly finite
  bounded linear frames, immediate and transitive tree unravellings,
  algebraically specified frame ranks, one-root rank extension, and a
  corrected theory of balloon frames;
- exact semantic correspondences for iterated 4, Ver, .4, H, and Grz, plus
  the McKinsey, Makinson, and Boolos-condition validity theorems;
- exact weak-.2/piecewise-convergence and weak-.3/piecewise-connectedness
  correspondences, including their stronger-frame corollaries;
- bisimulation invariance, bounded-morphism truth preservation, and validity
  preservation by surjective bounded morphisms;
- the p-morphism proof that irreflexivity is not definable by any basic modal
  formula; and
- the deep first-order standard translation, including universal closure and
  the familiar existential translation of diamond.

## Formalization map

| Coq module | Main Foundation source | Ported boundary |
| --- | --- | --- |
| `Syntax.v` | `Modal/Formula/Basic.lean` | Primitive/derived syntax, iteration, substitution, complexity, degree, subformulas |
| `NNFormula.v` | `Modal/Formula/NNFormula.lean` | NNF syntax, negation, ordinary-formula translations, degree, modal CNF/DNF predicates |
| `FormulaEncoding.v` | `Modal/Formula/{Basic,NNFormula}.lean` | Executable Cantor codes/decoders and surjective enumerations for nat atoms |
| `PLoN.v` | `Modal/PLoN/Basic.lean` | Formula-indexed frames/models, satisfaction, validity, countermodels, failure of replacement of equivalents |
| `PLoNCompleteness.v` | `Modal/PLoN/{Hilbert,Completeness,Logic/N}.lean` | Generic PLoN Hilbert soundness/canonical completeness and complete logic-N metatheory, including strictness below EN and K |
| `Axioms.v` | `Modal/Axioms.lean` | Complete named schema catalog, including normal, Geach, provability, McKinsey, and boxdot schemata |
| `HilbertK.v` | `Modal/Hilbert/Normal/Basic.lean` | Constructive Hilbert K, substitution, derived classical rules, theories, deduction, consistency criteria, contextual boxing |
| `Kripke.v` | `Modal/Kripke/Basic.lean` | Frames, valuations, satisfaction, substitution, relation/modal iteration, K validity |
| `KripkeAlgebra.v` | `Modal/Kripke/Algebra.lean` | Relational complex algebras, modal operations, algebraic evaluation/satisfaction equivalence, and validity as subset/extensional equality |
| `NNFormulaSemantics.v` | `Modal/Kripke/NNFormula.lean` | Direct NNF semantics, semantic negation, translation correctness, validity equivalences |
| `HilbertKSoundness.v` | `Modal/Kripke/Hilbert.lean` | Framewise and contextual Kripke soundness for K, plus consistency |
| `Complement.v` | `Modal/Formula/Complement.lean` | Syntactic complement, complement-closed finite contexts, constructive semantic incompatibility |
| `FiniteMaximalContext.v` | `Modal/ComplementClosedConsistentFinset.lean`, `Modal/{Formula/Complement,MaximalConsistentSet}.lean` | Normal-schema finite consistency and insertion laws over nat atoms; deterministic complementary closure, finite Lindenbaum contexts, membership laws, and an explicit finite cover |
| `ComplexityLimited.v` | `Modal/Kripke/ComplexityLimited.lean` | Complexity-bounded generated frames, strengthened truth lemma, subformula-target invariance |
| `Filtration.v` | `Modal/Kripke/Filtration.lean` | Coarsest truth-profile filtration, explicit exponential cover, finite countermodels, semantic finite-model property |
| `CanonicalK.v` | `Modal/{Tableau,MaximalConsistentSet}.lean`, `Modal/Kripke/{Completeness,Logic/K}.lean` | Concrete K Lindenbaum completion, maximal theories, canonical truth/countermodel arguments, completeness and finite completeness |
| `NormalHilbert.v` | `Modal/Hilbert/{Axiom,Normal/Basic}.lean`, `Modal/{Entailment,Kripke/Logic}/*` | Schema-parameterized normal systems; named-system substitution, inclusion, soundness, and consistency |
| `LogicInfrastructure.v` | `Modal/Logic/{Basic,SumNormal,SumQuasiNormal,Global}.lean` | Predicate-valued logic structure; normal/quasinormal sums and recursors; finite bases, substitution omission, and global consequence |
| `CanonicalExtensions.v` | `Modal/{Tableau,MaximalConsistentSet}.lean`, `Modal/Kripke/{Completeness,Logic/{KT,K4,S4}}.lean` | Generic normal-extension canonical model; KT/K4/S4 canonicality, completeness, and strictness |
| `Modality.v` | `Modal/Modality/{Basic,S5}.lean`, `Modal/Kripke/Logic/S5.lean` | Modal-word algebra, size enumeration/splitting, syntactic translations and equivalences, generic finite reduction, S5 canonical completeness, and six-form normalization for every length |
| `CanonicalDB5.v` | `Modal/Entailment/{KD,KB,K5}.lean`, `Modal/Kripke/Logic/{KD,KB,K5}.lean` | Schema-generic D/B/Five canonicality; KD/KB/K5 soundness-completeness, D-to-P, and strictness over K |
| `Correspondence.v` | `Modal/Kripke/AxiomGeach.lean`, `AxiomPoint3.lean` | Generic Geach and standard named frame correspondences |
| `FiltrationExtensions.v` | `Modal/Kripke/Filtration.lean` | Finest and transitive-closure filtrations, truth, finite bounds, elementary frame-property preservation |
| `Loeb.v` | `Modal/Kripke/AxiomL.lean` | Loeb validity iff transitivity plus converse well-foundedness |
| `FrameProperties.v` | `Modal/Kripke/{Antisymmetric,Asymmetric,Closure,Irreflexive,Terminated}.lean` | Closure algebra, frame orders, termination, converse well-foundedness |
| `CorrespondenceExtensions.v` | `Modal/Kripke/Axiom{FourN,Grz,H,I,McK,Mk,Point4,Ver}.lean` | Further exact and directional named-axiom frame correspondences |
| `Preservation.v` | `Modal/Kripke/Preservation.lean` | Bisimulation and bounded-morphism invariance/preservation |
| `Root.v` | `Modal/Kripke/Root.lean` | Rooted and generated frames/models, structural inheritance, bounded morphisms, and truth invariance |
| `FrameTransformations.v` | `Modal/Kripke/{ExtendRoot,Irreflexivize}.lean` | Irreflexivization and reflexive truth transfer; finite added-root frames, trees, p-morphisms, exact covers, boxdot transfer, and T witnesses |
| `StructuralFrames.v` | `Modal/Kripke/{Cluster,LinearFrame,Tree,Rank,Balloon}.lean` | Extensional clusters and skeletons; linear examples and Z/Dum validity; tree unravellings; specified ranks; corrected balloon results |
| `WeakCorrespondence.v` | `Modal/Kripke/Axiom{WeakPoint2,WeakPoint3}.lean` | Exact weak-confluence and weak-connectedness frame correspondences |
| `Boxdot.v` | `Modal/Boxdot/{Basic,K4_S4,GL_Grz,GLPoint3_GrzPoint3,Ver_Triv,Jerabek}.lean` | Basic translation semantics; unconditional nat-atom K4/S4 and Triv-to-Ver results; finite frame transformations; conditional named equivalences; doubled frames and dependency-gated Jeřábek BDP surfaces |
| `Undefinability.v` | `Modal/Kripke/Undefinability.lean` | Irreflexivity is not modally definable |
| `StandardTranslation.v` | `Modal/VanBentham/StandardTranslation.lean` | Deep relational first-order translation and semantic correspondence |
| `Audit.v` | — | Public checks and kernel-assumption reports |

The standard translation uses a small dedicated first-order signature with one
unary predicate per modal atom and one binary accessibility relation.  This is
more faithful than forcing the translation through this repository's existing
set-theoretic first-order language, which intentionally has only one binary
nonlogical predicate.

## Classical boundary

Foundation defines diamond from box as `not (box (not p))`.  In constructive
type theory, a concrete successor introduces a diamond, but extracting a
successor from an arbitrary diamond needs classical double-negation
elimination.  The Coq port keeps those lemmas separate:

- box semantics, substitution, K, direct forward frame-validity proofs,
  bisimulation invariance, bounded-morphism preservation, and the
  irreflexivity undefinability theorem are constructive; the Hilbert K
  calculus, deduction theorem, soundness proof, and consistency theorem also
  introduce no meta-level classical axioms;
- existential diamond elimination, the generic/named converse
  correspondences involving diamond, classical derived conjunction and
  disjunction, semantic NNF negation and translation, Loeb's maximal-element
  characterization, PLoN countermodel extraction, the canonical K
  construction, and derived first-order existential semantics use
  `Classical_Prop.classic`.  The Lindenbaum construction also uses Coq's
  standard definite-description principle to turn formula enumeration into
  a computable choice of consistent extension.  Root comparison and some
  generated-frame constructions use classical logic or proof irrelevance.
  The extensional representation of quotient clusters additionally uses
  functional and propositional extensionality; its skeleton order laws need
  only those extensionality principles and proof irrelevance, while cluster
  shape classification, the natural linear-frame semantic examples, and
  balloon maximality use excluded middle.  Equality of bounded-subtype
  witnesses in the duplicate-free linear-frame cover uses proof irrelevance.
  Filtering an arbitrary finite cover into a point-generated subtype uses
  informative excluded middle, classical description, and proof irrelevance.
  The inductive tree-unravelling and algebraic rank/path kernels remain
  constructive.  The relation algebra, embedding p-morphism, embedded-world
  truth theorem, chain enumeration, and exact finite cover for added-root
  frames are also constructive.  Irreflexivized piecewise connectedness,
  reverse reflexivization validity, unique-root selection, and added-root
  boxdot transfer use excluded middle; deriving converse well-foundedness
  from finite transitive irreflexive frames and the finite-chain T witnesses
  additionally uses relational and dependent unique choice;
  the converse Grz correspondence additionally exposes standard relational
  choice used to select an infinite counterexample chain.

The independent PLoN canonical construction has the same sharply delimited
Lindenbaum dependency: its soundness and explicit countermodels use at most
classical propositional logic, while maximal completion and completeness also
use the standard definite-description principle.

The Kripke complex algebra uses predicates on worlds and extensional
equivalence as its set equality, so its box/top, box/intersection,
evaluation/satisfaction, implication-order, and formula/top results are
constructive and require no extensionality axiom.  Only the existential
diamond dual and the derived disjunction/equivalence readings use excluded
middle.  The Coq results are atom-polymorphic, strengthening the source's
natural-number valuation statements.

The finite complement-closed context layer keeps its boundary equally
explicit.  The consistency insertion criteria, complement derivations, and
membership/implication laws are closed under the global context.  Turning
inconsistency back into a derivation uses classical double-negation
elimination, while deterministic `finite_next`, enumeration, and the finite
Lindenbaum construction use `Classical_Prop.classic` plus the standard
definite-description principle.  Equality of proof-carrying extensional
contexts uses functional and propositional extensionality with proof
irrelevance; the concrete powerset cover combines those principles with the
classical construction boundary.

The modal-word syntax, decidable equality, size/splitting machinery, finite
size layers, atom-instance substitution lifting, and generic reduction
bootstrapping are constructive.  Generic syntactic congruence/equivalence is
routed through the already checked K completeness theorem, while S5
canonicality and the six-form normalizer use the schema-generic Lindenbaum
construction.  Those proof-theoretic results therefore expose exactly
`Classical_Prop.classic` and the standard definite-description principle;
the semantic normalization on a supplied S5 frame uses only excluded middle.

The canonical seriality and right-Euclidean arguments for D and Five use the
schema-generic successor/Lindenbaum construction and therefore expose
excluded middle plus definite description.  Canonical symmetry from B is
closed once maximal contexts are supplied.  KD/KB/K5 completeness inherits
the common Lindenbaum boundary; their explicit strictness witnesses require
only excluded middle through the exact frame correspondences.

The predicate-valued logic structures and the inductive sum recursors are
constructive.  Equality of predicate logics and symmetric or nested-union sum
equalities use functional and propositional extensionality; their extensional
equivalence forms remain constructive.  Generic consistency is nontriviality,
exactly as in Foundation; extracting a particular unprovable formula uses
excluded middle, while bottom-unprovability for classical logics is
constructive.  The singleton-normalized and trailing-top conjunctions, and the
individual-iterate and cumulative `boxLe` forms, are linked by checked
normal-logic equivalences using excluded middle.  Instantiating the abstract
normal-logic interface with the concrete schema calculus is routed through K
completeness and therefore additionally exposes definite description.  The
forward global-consequence characterization uses excluded middle, while its
reverse direction uses extensionality to contract the exact union-indexed
contexts; the final equivalence exposes both.

The doubled-frame relation preservation and p-morphism are constructive.
Boxdot is built from the classically encoded derived conjunction, so its
reflexive-closure and conjunction truth laws expose excluded middle.  Reverse
reflexivization and finite-frame transformations that delete reflexive edges
also use excluded middle.  The unconditional nat-atom K4/S4 proof-theoretic
equivalence is routed through the local K completeness theorem and therefore
additionally inherits the standard definite-description principle.  The
abstract Jeřábek SBDP implication uses excluded middle; its global-consequence
input and named completeness inputs are explicit arguments, not kernel
assumptions or claimed theorems.

`Audit.v` prints assumptions for representative theorems from both sides of
this boundary.  There are no admitted results.

The filtration is necessarily more explicit about classical data.  Boolean
truth profiles use excluded middle, representatives of realized profiles use
`constructive_indefinite_description`, and equality of the proof-carrying
profile inhabitants in the finite cover uses proof irrelevance.  The audit
shows that the structural list enumeration itself is constructive, the truth
lemma needs the first two principles, and the finite cover adds only proof
irrelevance—without functional or propositional extensionality.

## Parity boundary

Concrete Hilbert K now has checked soundness, canonical completeness, and
finite-frame completeness; KT, KD, KB, K4, K5, S4, and S5 also have checked
canonical soundness/completeness on their standard frame classes.  The normal
and quasinormal sum modules, predicate-logic basics, and global consequence
have complete mathematical parity.  Predicates and duplicate-insensitive lists
replace Lean sets and finite sets; explicit theorems connect the trailing-top
and singleton-normalized conjunctions and the cumulative and individual-box
presentations used in the implementation and source.  Every modal word has a
checked S5 equivalence and reduction to the six canonical modalities.  The boxdot
semantic core and all four K4/S4 theorem shapes are checked unconditionally
for the named natural-number-atom logics,
giving exact parity for `K4_S4.lean`.  The coverage ledger remains conservative
for `Boxdot/Basic.lean`: its semantic results are atom-polymorphic, but its Coq generic
proof-translation theorem is nat-only, and distinct Lean
big-conjunction/finite-set convenience surfaces are represented by list-based
counterparts.  Likewise, `FiniteMaximalContext.v` checks every mathematical
theorem shape in `ComplementClosedConsistentFinset.lean` for the generic
normal-schema calculus over natural-number atoms, but the ledger remains
`partial` because Foundation quantifies over arbitrary decidable atom types
and abstract classical entailments.  Lists are used only during construction;
the resulting finite carriers and their equality are extensional.  This
project still does not claim finite completeness for
K4/S4, the source's universal-frame reformulation or strict-inclusion chain
for S5, or completeness for GL, Grz, GL.3, Grz.3, or Triv.  Rooted
filtration preservation for piecewise confluence and connectedness and modal
companions also remain later work.

### Boxdot dependency gates

The remaining Boxdot results are stated with their unavailable dependencies
as ordinary propositions and hypotheses.  In particular:

- `boxdot_GL_finite_complete` and `boxdot_Grz_finite_complete` gate the two
  directions of the GL/Grz proof equivalence;
- `boxdot_GLPoint3_finite_complete` and
  `boxdot_GrzPoint3_finite_complete` similarly gate GL.3/Grz.3;
- `boxdot_Triv_complete` gates only the Ver-to-Triv reflection direction—the
  Triv-to-Ver translation is unconditional;
- each named Jeřábek BDP corollary requires its `logic_complete_on` premise and
  `jerabek_global_consequence_bridge`.  The latter isolates the source proof's
  finite global-consequence, finite-context, subformula, and fresh-atom
  construction, whose supporting APIs have not yet been ported.

No inhabitant of any of these completeness or bridge propositions is declared
or inferred.  Consequently the conditional equivalences must not be read as
proofs of the missing completeness theorems.

The structural-frame tranche deliberately records three representation or
source boundaries.  Coq's local `frame` has no finite-world typeclass, so it
uses explicit list covers instead: `StructuralFrames.v` supplies the finite
cluster-skeleton and bounded-linear-frame counterparts, including a
duplicate-free enumeration of each bounded carrier.  The source's finite
tree-unravelling instance is not yet reconstructed.  Tree paths use
inductive snoc constructors, making the source list-prefix/`IsChain` normal
form intrinsic; rank results are proved from an exact `frame_rank_spec`,
rather than reconstructing Foundation's finite converse-well-founded height
machinery.  Its rank development needs only a one-fresh-root construction;
independently, `FrameTransformations.v` checks the complete pinned
`extendRoot` theorem surface for the general `Fin n + F` carrier.  Lean's
finite-world, tree, and finite-set wrappers are represented by explicit Coq
conjunctions, duplicate-free list covers, and extensional cardinality
predicates; these are representation changes, not mathematical omissions.
Foundation's point-generated rank equality is an `axiom` at the pinned
revision, whereas the corresponding Coq restriction theorem is proved.

`Balloon.lean` also cannot be ported literally: its world relation is required
to be a strict total order while its envelope is nondegenerate, assumptions
that the cluster laws make inconsistent.  Moreover,
`farthermost_point_of_not_box` is admitted upstream and false without a
well-foundedness/finite hypothesis (the strict natural-number frame is an
explicit Coq counterexample).  `StructuralFrames.v` proves the inconsistency,
defines a coherent preorder-based balloon notion, and proves the intended
farthest-counterexample and Z-validity results with converse well-foundedness
stated explicitly.

## Checking

From `Logic/Modal/Coq`:

```powershell
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
coqchk -silent -Q . FoundationModal `
  FoundationModal.Syntax FoundationModal.NNFormula FoundationModal.Axioms `
  FoundationModal.FormulaEncoding FoundationModal.PLoN `
  FoundationModal.PLoNCompleteness `
  FoundationModal.Kripke FoundationModal.NNFormulaSemantics `
  FoundationModal.HilbertK FoundationModal.HilbertKSoundness `
  FoundationModal.KripkeAlgebra `
  FoundationModal.Complement `
  FoundationModal.ComplexityLimited FoundationModal.FrameProperties `
  FoundationModal.Filtration `
  FoundationModal.Correspondence FoundationModal.FiltrationExtensions `
  FoundationModal.CanonicalK `
  FoundationModal.Loeb FoundationModal.CorrespondenceExtensions FoundationModal.NormalHilbert `
  FoundationModal.LogicInfrastructure `
  FoundationModal.CanonicalExtensions `
  FoundationModal.FiniteMaximalContext `
  FoundationModal.Modality `
  FoundationModal.CanonicalDB5 `
  FoundationModal.StandardTranslation FoundationModal.Preservation FoundationModal.Root `
  FoundationModal.FrameTransformations `
  FoundationModal.StructuralFrames `
  FoundationModal.WeakCorrespondence `
  FoundationModal.Boxdot `
  FoundationModal.Undefinability FoundationModal.Audit
```

The root `_CoqProject` also registers every module under the logical prefix
`FoundationModal`.

## Attribution and license

Foundation is licensed under Apache-2.0; its license is retained in the pinned
submodule at `lib/FormalizedFormalLogic-Foundation/LICENSE`.  These Coq files
are a newly written port rather than a line-by-line transliteration.  Their
headers identify the corresponding upstream files, and this README records
the pinned revision.  A full repository copy of the Apache-2.0 text is also
available at
`Computability/CombinatoryLogic/Lean/LICENSE-Apache-2.0`.
