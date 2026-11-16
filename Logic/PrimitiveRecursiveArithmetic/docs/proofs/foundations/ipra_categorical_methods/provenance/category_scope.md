# Category-theoretic scope and provenance

This note records the mathematical meaning and validation status of the category
claims in the accompanying paper. It is not an additional theorem or an
independent formal verification.

## Three representation levels

| Level | Data available | Meaning of the resulting claim |
| --- | --- | --- |
| Uniform finite tables | Explicit natural bounds, finite lists or arrays, and decidable table-validation tests | One first-order arithmetic theorem may quantify over the codes of all valid finite input tables. Table evaluation, finite products, bounded filtering, bounded reachability, and finite witness selection are fixed primitive recursive algorithms. |
| Fixed PR presentation | A fixed finite signature of PR numerical operations and guarded predicates, with supplied proofs of its laws | Each choice of these definitions gives an iPRA instance. The paper's elementary category equations, presentation-wise Yoneda calculation, adjunction calculation, and split equivalence criterion have this meaning. They do not quantify internally over all numerical functions. |
| External organization | Individual specified PR definitions and their proofs, organized as objects and arrows in the metatheory | This is bookkeeping for reusable mathematical interfaces and theorem schemes. An external category of PR constructions has not thereby become a first-order universe inside iPRA. |

“Finite” here means explicitly enumerated and bounded finite data, with the
specified equality tests. It does not mean an arbitrary abstract set merely
asserted to be finite without a usable listing. Invalid numerical inputs can be
totalized by defaults in PR definitions; guards make those defaults irrelevant.
The Python reference programs instead reject malformed inputs or use explicit
sentinels to make diagnostic mistakes visible.

A hom relation may use a supplied arithmetic equivalence relation on codes.
In that presentation-wise version, equality need not be decidable. Any algorithm
that filters, searches, or normalizes using equality requires an additional
decidable equality presentation or a suitable finite certificate interface.

## Claims supported by the human arguments

- Finite challenge contracts have explicit composition and identities, transport
  realization witnesses, and have finite categorical products. The query map
  uses a finite union of finite query sets. A uniform finite-table specialization
  gives a decidably presented, locally finite category of contract matrices.
- Finite table categories admit uniformly computed opposite and functor
  categories. The table category of finite sets has finite limits, finite
  colimits, and exponentials `[m]^[n] = [m^n]`, including empty cases.
- Yoneda is proved as a guarded pointwise calculation for each fixed
  presentation. For a finite table category and finite-valued family, the entire
  natural-transformation collection is also an explicitly enumerable finite
  table, so the theorem has the stronger uniform finite-code form.
- Left and right Kan extensions of finite-valued functors along finite table
  functors are given by explicit finite quotient and coherent-tuple formulas.
  Their universal maps and inverse identities are proved in the paper.
- The unit–counit adjunction calculation is valid for supplied fixed maps and
  their naturality and triangle laws. The equivalence criterion requires
  supplied PR arrow liftings and selected object isomorphisms, or bounded
  searches that actually produce those data. Finite tables supply such bounds.
- Exact local function tables on a finite covering family glue uniquely.
  Generalized two-modulus CRT is an explicit finite pullback construction.
  A fixed PR tower with proved bounded surjective liftings has a PR coherent
  point, obtained by bounded least lifting and ordinary primitive recursion.

These are human mathematical arguments at the stated arithmetic level. They
are not all completed Lean derivations.

## Relationship to established category theory

The category-theoretic identities and standard universal-property theorems are
not claimed as new theorems of ordinary category theory. Their standard setting
is described in Emily Riehl, *Category Theory in Context*, especially the
sections on equivalence, Yoneda, limits and colimits, adjunctions, and Kan
extensions:

https://emilyriehl.github.io/files/context.pdf

The relation-and-forward/backward-map construction has established predecessors
in Dialectica and Diller–Nahm category constructions. The report credits this
connection rather than claiming to invent it. A primary historical source is
Valeria de Paiva, *The Dialectica Categories*, Cambridge report UCAM-CL-TR-213
(1991, based on her 1988 dissertation):

https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-213.html

The contribution of this packet is its explicit arithmetic interfaces, bounds,
induction discipline, constructive splitting requirements, and integration with
the inspected ProveIt proof packets. It reuses and credits the repository's
existing finite-demand, finite-observation, compatibility, and lifting ideas.
Those ideas are not presented as discoveries first made in this packet.

## Exact executable coverage

`code/finite_categories.py` supplies finite category, functor, natural
transformation, finite set diagram, limit, colimit, Yoneda, and exponential
reference operations. `code/check_categories.py` checks the listed finite
instances, including empty categories, empty diagrams, and empty finite sets.

`code/challenge_contracts.py` supplies finite contract matrices, query bitsets,
arrows, identities, composition, products, and pairings, together with exact
small-instance checks of their laws.

`code/finite_descent.py` supplies finite gluing and generalized two-modulus CRT
and checks finite instances against explicit enumeration.

The finite Kan extension construction, the general adjunction and split
quasi-inverse construction, the no-computable-branch tree, and the general
surjective-tower theorem have human arguments and formalization plans; they are
not separately implemented or exhaustively validated by these reference
programs. Finite executable checks are not universal proofs, Lean proofs, or
iPRA derivations.

## Features and conclusions not claimed

- No internal universe of all sets, all small categories, all arbitrary
  functors, or all total computable functions is constructed.
- No uniform total PR evaluator for arbitrary PR program codes is assumed or
  produced. Finite table evaluation and bounded machine simulation do not have
  that forbidden interface.
- No exponential representing every PR function `Nat → Nat` with PR-total
  evaluation on numerical codes is claimed. Its diagonal obstruction does not
  contradict finite cartesian closure.
- Presentation-wise Yoneda does not assert the existence, inside iPRA, of the
  set of all transformations between arbitrary infinite presentations.
- Fullness and essential surjectivity of an infinite presentation are not
  silently converted into PR quasi-inverse selectors. The necessary selected
  isomorphisms and arrow liftings remain explicit resources.
- A finite class count is not converted into a uniformly computable complete
  representative list. The obstruction is uniform across the family, not the
  impossibility of any finite constant list for one fixed finite-class relation.
- Nonempty finite stages are not converted into a computable inverse-limit
  point. The tree counterexample is a metatheoretic computability statement;
  the positive tower theorem requires bounded surjective liftings.
- Exact finite gluing is not asserted for approximate overlap relations without
  an error contract, and its uniqueness conclusion is not transferred unchanged
  to approximate data.
- No unrestricted reflection, internal truth predicate, comprehension scheme,
  higher-type recursor, or general compactness principle is added to iPRA.
- The Lean sources are not reported as compiled in this environment. The
  object-level derivation source patterns and the larger formalization outline
  are distinguished from completed kernel checks.
