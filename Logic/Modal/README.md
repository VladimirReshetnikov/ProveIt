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
- Kripke satisfaction, semantic substitution, iterated box/diamond laws, and
  validity of K;
- complexity-bounded generated models with a strengthened budgeted truth
  lemma and invariance under changing the enclosing target formula;
- reflexive, transitive, and reflexive-transitive frame closures, their order
  properties, target termination, and converse well-foundedness results;
- PLoN's formula-indexed relational semantics, including all validity and
  countermodel equivalences and failure of replacement of equivalents;
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
  invariance through their bounded morphisms;
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
| `Axioms.v` | `Modal/Axioms.lean` | Complete named schema catalog, including normal, Geach, provability, McKinsey, and boxdot schemata |
| `HilbertK.v` | `Modal/Hilbert/Normal/Basic.lean` | Constructive Hilbert K, substitution, derived classical rules, theories, deduction, consistency criteria, contextual boxing |
| `Kripke.v` | `Modal/Kripke/Basic.lean` | Frames, valuations, satisfaction, substitution, relation/modal iteration, K validity |
| `NNFormulaSemantics.v` | `Modal/Kripke/NNFormula.lean` | Direct NNF semantics, semantic negation, translation correctness, validity equivalences |
| `HilbertKSoundness.v` | `Modal/Kripke/Hilbert.lean` | Framewise and contextual Kripke soundness for K, plus consistency |
| `Complement.v` | `Modal/Formula/Complement.lean` | Syntactic complement, complement-closed finite contexts, constructive semantic incompatibility |
| `ComplexityLimited.v` | `Modal/Kripke/ComplexityLimited.lean` | Complexity-bounded generated frames, strengthened truth lemma, subformula-target invariance |
| `Filtration.v` | `Modal/Kripke/Filtration.lean` | Coarsest truth-profile filtration, explicit exponential cover, finite countermodels, semantic finite-model property |
| `CanonicalK.v` | `Modal/{Tableau,MaximalConsistentSet}.lean`, `Modal/Kripke/{Completeness,Logic/K}.lean` | Concrete K Lindenbaum completion, maximal theories, canonical truth/countermodel arguments, completeness and finite completeness |
| `NormalHilbert.v` | `Modal/Hilbert/{Axiom,Normal/Basic}.lean`, `Modal/{Entailment,Kripke/Logic}/*` | Schema-parameterized normal systems; named-system substitution, inclusion, soundness, and consistency |
| `Correspondence.v` | `Modal/Kripke/AxiomGeach.lean`, `AxiomPoint3.lean` | Generic Geach and standard named frame correspondences |
| `FiltrationExtensions.v` | `Modal/Kripke/Filtration.lean` | Finest and transitive-closure filtrations, truth, finite bounds, elementary frame-property preservation |
| `Loeb.v` | `Modal/Kripke/AxiomL.lean` | Loeb validity iff transitivity plus converse well-foundedness |
| `FrameProperties.v` | `Modal/Kripke/{Antisymmetric,Asymmetric,Closure,Irreflexive,Terminated}.lean` | Closure algebra, frame orders, termination, converse well-foundedness |
| `CorrespondenceExtensions.v` | `Modal/Kripke/Axiom{FourN,Grz,H,I,McK,Mk,Point4,Ver}.lean` | Further exact and directional named-axiom frame correspondences |
| `Preservation.v` | `Modal/Kripke/Preservation.lean` | Bisimulation and bounded-morphism invariance/preservation |
| `Root.v` | `Modal/Kripke/Root.lean` | Rooted and generated frames/models, structural inheritance, bounded morphisms, and truth invariance |
| `WeakCorrespondence.v` | `Modal/Kripke/Axiom{WeakPoint2,WeakPoint3}.lean` | Exact weak-confluence and weak-connectedness frame correspondences |
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
  generated-frame constructions use classical logic or proof irrelevance;
  the converse Grz correspondence additionally exposes standard relational
  choice used to select an infinite counterexample chain.

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
finite-frame completeness.  This project does not yet claim Coq parity for
Foundation's completeness theorems for S4, S5, GL, or Grz; rooted filtration
preservation for piecewise confluence and connectedness; modal companions; or
the boxdot results.  Those later results require extensions of the proof
system and canonical-frame property arguments.  The present modules provide
the checked base on which those ports are being built.

## Checking

From `Logic/Modal/Coq`:

```powershell
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
coqchk -silent -Q . FoundationModal `
  FoundationModal.Syntax FoundationModal.NNFormula FoundationModal.Axioms `
  FoundationModal.FormulaEncoding FoundationModal.PLoN `
  FoundationModal.Kripke FoundationModal.NNFormulaSemantics `
  FoundationModal.HilbertK FoundationModal.HilbertKSoundness `
  FoundationModal.Complement `
  FoundationModal.ComplexityLimited FoundationModal.FrameProperties `
  FoundationModal.Filtration `
  FoundationModal.Correspondence FoundationModal.FiltrationExtensions `
  FoundationModal.CanonicalK `
  FoundationModal.Loeb FoundationModal.CorrespondenceExtensions FoundationModal.NormalHilbert `
  FoundationModal.StandardTranslation FoundationModal.Preservation FoundationModal.Root `
  FoundationModal.WeakCorrespondence `
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
