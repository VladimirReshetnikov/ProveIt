# Foundation modal logic in Rocq/Coq

This project is an independent, idiomatic Rocq/Coq port of a high-value
semantic slice of
[FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation).
The source is pinned read-only at commit
`32e1a0956a8622fad067328ca1959729a7634428` under
`lib/FormalizedFormalLogic-Foundation`; none of the Coq modules imports or
modifies the Lean development.

The port focuses on results that are both central to Foundation's modal-logic
library and reusable without first recreating its full Hilbert-calculus and
canonical-model stack:

- primitive modal syntax, derived connectives, substitution, iteration,
  complexity, degree, and subformulas;
- Kripke satisfaction, semantic substitution, iterated box/diamond laws, and
  validity of K;
- the general Geach axiom/frame-condition correspondence, with exact
  specializations T/reflexive, D/serial, B/symmetric, 4/transitive,
  5/right-Euclidean, Tc/coreflexive, and .2/strongly confluent;
- the .3/piecewise-strong-connectedness correspondence;
- the Kripke correspondence for Loeb's axiom;
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
| `Axioms.v` | `Modal/Axioms.lean` | K, T, D, B, 4, 5, Tc, .2, .3, Loeb, Grz, and generic Geach schemata |
| `Kripke.v` | `Modal/Kripke/Basic.lean` | Frames, valuations, satisfaction, substitution, relation/modal iteration, K validity |
| `Correspondence.v` | `Modal/Kripke/AxiomGeach.lean`, `AxiomPoint3.lean` | Generic Geach and standard named frame correspondences |
| `Loeb.v` | `Modal/Kripke/AxiomL.lean` | Loeb validity iff transitivity plus converse well-foundedness |
| `Preservation.v` | `Modal/Kripke/Preservation.lean` | Bisimulation and bounded-morphism invariance/preservation |
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
  irreflexivity undefinability theorem are constructive;
- existential diamond elimination, the generic/named converse
  correspondences involving diamond, classical derived conjunction and
  disjunction, Loeb's maximal-element characterization, and derived
  first-order existential semantics use `Classical_Prop.classic`.

`Audit.v` prints assumptions for representative theorems from both sides of
this boundary.  There are no admitted results.

## Parity boundary

This project does not yet claim Coq parity for Foundation's Hilbert-system
completeness theorems for K, S4, S5, GL, or Grz; filtration; modal companions;
or the boxdot results.  Those require the proof-system/canonical-model layers
and are deliberately not smuggled in as semantic hypotheses.  The present
modules provide the syntax and semantic infrastructure on which such ports can
be built.

## Checking

From `Logic/Modal/Coq`:

```powershell
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
coqchk -silent -Q . FoundationModal `
  FoundationModal.Syntax FoundationModal.Axioms FoundationModal.Kripke `
  FoundationModal.Correspondence FoundationModal.Loeb `
  FoundationModal.StandardTranslation FoundationModal.Preservation `
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
