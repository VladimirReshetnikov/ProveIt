# Logic

- [`FoundationPort/`](FoundationPort/) maintains the exhaustive, conservative
  source-module ledger for the dependency-ordered Coq port of the pinned
  FormalizedFormalLogic/Foundation tree.
- [`FirstOrder/`](FirstOrder/) is a reusable one-binary-relation first-order
  syntax and semantics, natural-deduction calculus, soundness proof, Goedel
  completeness theorem, compactness lift, and deductive-transfer machinery.
- [`Modal/`](Modal/) is an independent Rocq/Coq port of Foundation's modal
  semantic core: Kripke semantics; the general Geach correspondence and its
  T, D, B, 4, 5, Tc, and .2 instances; the .3 correspondence; the Kripke-frame
  characterization of Löb's axiom; bisimulation and bounded-morphism
  preservation; irreflexivity undefinability; coarsest, finest, and
  transitive-closure filtrations with the semantic finite-model property; and
  the deep first-order standard translation.
- [`QuantifierCommutation/`](QuantifierCommutation/) proves constructive
  commutation laws for adjacent `∀` and `∃`, with finite counterexamples for
  nested `∄` and `∃!`, in Lean and Rocq/Coq.
- [`Propositional/ShefferStroke/`](Propositional/ShefferStroke/) formalizes
  NAND/NOR translations and Nicod's single-axiom calculus.
- [`Propositional/NaturalDeduction/`](Propositional/NaturalDeduction/) is the
  shared intuitionistic/classical propositional calculus used by the structural
  theorem developments.
- [`Propositional/FiniteMatrixNoncharacterizability/`](Propositional/FiniteMatrixNoncharacterizability/)
  formalizes Gödel's theorem that no finite deterministic truth-functional
  matrix—and hence no three-valued matrix—characterizes intuitionistic logic.
- [`Propositional/MonotonicityOfEntailment/`](Propositional/MonotonicityOfEntailment/)
  proves context weakening for intuitionistic and classical natural deduction
  in Lean and Rocq/Coq.
- [`Propositional/PrincipleOfExplosion/`](Propositional/PrincipleOfExplosion/)
  proves `P, ¬P ⊢ Q` and equivalent forms in both logics, in Lean and Rocq/Coq.
- [`Equational/`](Equational/) contains the sound equational checker and the
  Wolfram/Meredith/Sheffer/Huntington Boolean-algebra certificates.
- [`Interpretability/PAHF/`](Interpretability/PAHF/) proves the deductive
  bi-interpretation of PA with finite-generation hereditary finite set theory.
- [`PeanoArithmetic/ListCoding/`](PeanoArithmetic/ListCoding/) gives independent
  Lean and Rocq/Coq natural-number codings of finite lists and genuine PA
  formulae for twenty-five list and number-theoretic predicates,
  including flattening,
  subsequences, aggregate folds, extrema, median and unique-mode statistics,
  lexicographic order, one-based nth primes, natural powers and prime
  factorizations, canonical base digits and divisor lists, and the exact
  canonical list of distinct permutations.

The natural-deduction developments, FirstOrder, and PAHF are mathlib-free and
have standalone Lake configurations as well as root integration targets.
