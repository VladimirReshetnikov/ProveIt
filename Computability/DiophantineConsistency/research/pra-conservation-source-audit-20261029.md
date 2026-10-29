# PRA transfer: source-only audit, 2026-10-29

This is a read-only audit of upstream commit
`2396efcd472fd15d3a77b95119fbb71c11f1fbd2`, with Foundation pinned to
`32e1a0956a8622fad067328ca1959729a7634428`. It supersedes the now-obsolete
repunit planning assignment, not any accepted proof. No Lean build, compiler
overlay, dependency refresh, source change, or Git mutation was performed.
The newly advanced full endpoint dependency closure was not independently
replayed by this audit. Only this separate note is added; PRA_PROVABILITY_PLAN.md
and the controller's hierarchy work are untouched.

## What upstream actually proves

`HACurrentEquation2011.isigma1_proves_current_iff_consistency` has the closed type

```lean
𝗜𝚺₁ ⊢ FoundationHACurrentNoZero2011.classicalSentence 🡘
  FoundationZFCConsistencyNat.sourceSentence
```

It has no polynomial, normalization, source-axiom, or model hypothesis left.
The wrapper discharges `PolynomialBridge` using actual
`ArithmeticLocalNormalization.localNormalization`; the assembly discharges the
source bridge through the actual C222 consistency theorem and checker/machine
connection. Assembly obtains object-theory provability by completeness from
**all Type-0 IΣ₁ models**, not just standard natural-number truth. The file also
has the closed HA `ProofEquiv` endpoint. This audit read the complete endpoint,
assembly, and polynomial-bridge files, but is not a new transitive verification.

The only `PRA`/`Parsons` occurrences found by the repository-wide Lean search at
this upstream commit are explanatory comments in the assembly/endpoint files.
The same search, including primitive-recursive-arithmetic spellings and likely
filename variants, found no PRA theory or Parsons theorem in the pinned
Foundation tree. This is a scoped search result, not proof that no differently
named implementation exists anywhere.

## The normal-form obligation is small and concrete

The literal current sentence is `classicalNoZero naturalExpression`: fourteen
universal quantifiers over a negative equality of two arithmetic terms obtained
from `Expr.splitNatural`. It is Π₁. The consistency side is the coercion of
Foundation's already typed `Theory.consistent : 𝚷₁.Sentence`, with its actual ZFC
theory argument. Its definition is `.mkPi (∼provabilityPred T ⊥)`.

For reference, existing exact APIs include:

```lean
Hierarchy.accum (hp : Hierarchy Γ s φ) (Γ') : Hierarchy Γ' (s + 1) φ
Hierarchy.allItr_iff :
  Hierarchy 𝚷 (s + 1) (∀⁰^[k] φ) ↔ Hierarchy 𝚷 (s + 1) φ
Hierarchy.iff_iff : Hierarchy b s (φ 🡘 ψ) ↔
  (Hierarchy b s φ ∧ Hierarchy b.alt s φ ∧
   Hierarchy b s ψ ∧ Hierarchy b.alt s ψ)
```

Thus both Π₁ sides accumulate to both polarities at level 2, giving a literal
Π₂ biconditional. No equation-coefficient expansion or new arithmetic model
argument is needed. ROOT has separately assigned this exact syntactic lemma to
the controller; this note does not implement or duplicate it. If a future
conservation theorem is restricted to strict prenex ∀∃ formulas, one still needs
a proved conversion from this hierarchy certificate to its accepted input form.

## Existing logical machinery, and its exact limit

Foundation `FirstOrder/Basic/Calculus.lean` defines an actual finite proof:

```lean
structure Theory.Proof (T : Theory L) (σ : Sentence L) where
  axioms : List (Sentence L)
  axioms_mem : ∀ ψ ∈ axioms, ψ ∈ T
  derivation : OneSidedLK.Pullback Derivation Rewriting.emb (σ :: ∼axioms)
```

Foundation `FirstOrder/Hauptsatz.lean` exports:

```lean
LO.FirstOrder.Derivation.Canonical.hauptsatz
  [L.DecidableEq] {Γ : Sequent L} :
  ⊢ᴸᴷ¹ Γ → {d : ⊢ᴸᴷ¹ Γ // Derivation.IsCutFree d}
```

`FirstOrder/Basic/CutFree.lean` gives the concrete cut-free constructors and
their rewriting laws. Consequently the existing IΣ₁ proof can provide a finite
axiom list and a cut-free LK derivation with the negated axioms still present.
**Cut elimination does not delete those arithmetic induction axioms or replace
them by PRA deductions.** That is the missing arithmetic reduction.

Also, `Arithmetic/HFS/PRF.lean` defines `PR.Blueprint` and `PR.Construction` for
represented recursion under `[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`. These APIs are useful internally,
but are not a language of all primitive-recursive function codes, a PRA axiom
system, or a theorem extracting PRA proofs from IΣ₁ proofs. A Σ₁/Δ₁ graph and
IΣ₁-totality alone must not be relabelled as a PRA witness certificate.

## Literature and import feasibility

[Joosten, *Two Proofs of Parsons' Theorem*, §2, Theorem 2.1 and Lemma 2.2](https://www.phil.uu.nl/ozsl/articles/joosten01.pdf) gives a cut-free reduction
through the theory with a Σ₁ induction **rule**, followed by its PRA witnessing
argument. This makes the existing Hauptsatz a relevant starting point. The
paper discusses formalizability in arithmetic; it is not a Lean library or a
machine-checked artifact. Parameter handling, the strict Π₂ form, and induction
rule witnessing are substantive parts of that route.

[Ferreira, *A simple proof of Parsons' theorem*, Theorems 1.1/2.1, §3 and note 10](https://webpages.ciencias.ulisboa.pt/~fjferreira/yet.pdf) gives a second route
using Herbrand witnesses for ∃∀∃ consequences of universal theories and a
primitive recursion that defeats an induction counterexample. It explicitly
separates semantic proof from effective proof transformation. Adapting it would
need the appropriate Herbrand theorem and a genuine PRA presentation; neither
was found as a ready interface here.

Targeted web searches for Lean/Coq/Isabelle implementations found these primary
mathematical sources, but no inspectable machine-formalized Parsons package.
This is not an exhaustive global nonexistence claim. No external code was
downloaded, imported, or executed. An import-only completion is not supported
by the evidence inspected so far.

## Concrete mechanization interfaces still required

One defensible route is to add the following **proved constructions**, not new
axioms or user-supplied transfer assumptions:

1. An arity-indexed primitive-recursive code language `LPR`, defining equations,
   a first-order PRA theory with quantifier-free induction, and the embedding
   of the current ordered-ring language. First-order PRA must be explicit:
   quantifier-free Skolem arithmetic cannot literally state the displayed Π₂
   biconditional without a witness-form translation.
2. A checked normal-form/translation adapter for Foundation `Hierarchy 𝚷 2`,
   including bounded quantifiers and the exact consistency formula. The
   proposed interface, schematically, is
   `Hierarchy Π 2 φ → (IΣ₁ ⊢ φ) → PRA ⊢ embed φ`.
3. The arithmetic reduction, for example: introduce the Σ₁ induction-rule
   calculus; transform cut-free proofs containing negated IΣ₁ induction axioms
   into it; prove its required Π₂ consequences have PRA witnesses. This must
   handle the actual universally closed parameterized induction scheme in
   `Arithmetic/Schemata.lean`, not merely parameter-free induction.
4. Apply that theorem to the closed current proof and its hierarchy certificate.
   This gives a PRA proof **of the equivalence**; it does not prove ZFC
   consistency or equation unsolvability separately.

This is a substantial new metatheory development, although the pure logical
cut-elimination part already exists. A semantic conservation proof is also
possible in principle, but would need a new PRA-model construction/conservation
theorem; the present IΣ₁ completeness argument does not supply it.

## Direct primitive-recursive witness alternative

For this one result, one could instead provide primitive-recursive transforms
in both directions between (i) an actual coded ZFC refutation and (ii) an actual
14-variable natural zero, with PRA proofs of each conditional correctness
statement. Polynomial checking is a finite arithmetic computation. The exact
refutation checker and tuple encodings would also need proved PR definitions
and correctness in the selected PRA presentation. Classical contraposition
then recovers the same no-zero/consistency equivalence.

The repository's IΣ₁ existence endpoints and deterministic runtime definitions
do not yet provide those PRA-certified transforms or primitive-recursive bounds
on all searches/constructions. Unbounded search plus an IΣ₁ termination proof
cannot serve as the extraction theorem without circularly using Parsons.
Likewise extracting a proof witness with classical choice from completeness
does not establish an executable PR transformation. A general verified
conservation theorem avoids revisiting each arithmetic construction; a direct
route would require a new audit of all chosen witnesses and bounds. Neither
route is already completed by the source inspected here.

Externally, the published conservation theorem plus the closed IΣ₁ proof and
the elementary Π₂ classification justify ordinary mathematical PRA
proof-existence. What is absent is a Lean theorem with a defined PRA proof
relation as its conclusion, or a verified concrete PRA proof/witness artifact.

## Source pins

SHA-256, first six files read from the pinned upstream Git object; remaining
files read from the pinned Foundation source checkout. No object/cache freshness
claim is made.

| Source | SHA-256 |
|---|---|
| HACurrentEquation2011.lean | b041f0815e52985a3c60eed5bed9648a62f1bfd5f495d72d2ce3797b94e71e3e |
| HACurrentAssembly2011.lean | e931b4ffe793c62f091817febf1735e659fdd0b30afaa250e99a2353ba6ac934 |
| HACurrentPolynomialBridge2011.lean | 162231f1f15b7a0eb7ab3f0e6ab5366fa933ae0f53c4bbe16864558c721413b0 |
| FoundationHACurrentNoZero2011.lean | 27b99c298b218f276bb16c23e6dac964befa47bc7e34759b612898f754e7ac00 |
| FoundationHANoZero.lean | 8539882d474478c041177ed90eae788ff02167a7c15621117287e4ab3904eb60 |
| FoundationZFCConsistencyNat.lean | c9e90e5861848ece065a410ad2b0012617e481b9d4fbfccd37436b2ebf40b613 |
| FirstOrder/Hauptsatz.lean | ff8a2b5e584b692ec646db56deb5327c1fda0c76a6fada48569bfe571082db63 |
| FirstOrder/Basic/Calculus.lean | 03ede19d7a450f4f9f8d6925406c6e6509768ebdea4179fa70418436d47fe08a |
| FirstOrder/Basic/CutFree.lean | 5067e9701717d1ef09ebdbca0ea7ab2d2b586daa8e9a0bd1d5ed84e61473c7d7 |
| FirstOrder/Arithmetic/HFS/PRF.lean | 5925b829137d35293fa00955e81a584857e49a3db94baff1810b44bd05c7beeb |
| FirstOrder/Arithmetic/Basic/Hierarchy.lean | c9ac3be94e6691675ae3d37ed2d9e6a03abc0cd22a970db321ee447ea3eb14bf |
| FirstOrder/Incompleteness/Consistency.lean | f37a2b45a1cacec07d7fc50fcea2382a67ea81d70ca78c098ce41d7f8f2b922f |
