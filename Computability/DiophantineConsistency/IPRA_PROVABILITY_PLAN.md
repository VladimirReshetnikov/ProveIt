# Intuitionistic PRA provability of the current consistency equivalence

**Goal (set 31 October 2026).** Prove in Lean that *intuitionistic* primitive
recursive arithmetic proves the equivalence between unsolvability of the
maintained 14-variable equation and the consistency of ZFC. A Lean proof that
an intuitionistic derivation exists suffices, as for the HA endpoint.

## Starting point

* Classical endpoint: `PRA ⊢ lMap classicalSentence 🡘 lMap sourceSentence`,
  from `PRAStrictConReverse.comparison_if_bound` and
  `PRACurrentConsistencyEndpoint.boundCertificate_rho`. Here `sourceSentence`
  is Foundation's `ZFC.consistent = ∼rho`, with
  `rho = provabilityPred ZFC ⊥` (Σ₁).
* Foundation already provides intuitionistic first-order Hilbert systems over
  any language (`Hilbertᵢ L`, `Theoryᵢ L Λ`, `𝗜𝗻𝘁¹`) and the Gödel–Gentzen
  translation `φᴺ`. The repository's `FoundationTheoryGG.theory_intuitionistic`
  turns `T ⊢ φ` into `T.ToTheoryᵢ 𝗜𝗻𝘁¹ ⊢ φᴺ` for any decidable-equality
  language. Its target theory is the *translated* axiom set, not a
  conventional intuitionistic theory; the discharge below supplies that step.
* `PRABoundedFormula.PRA_proves_boundedBooleanCharacteristic`: every `Σ₀`
  formula `θ` of the PRA language has a code `c` with `PRA ⊢ c ∈ {0,1}` and
  `PRA ⊢ ∀x⃗ (c(x⃗) = 1 ↔ θ)`. `PRABoundedSearchCode` has bounded search codes.

## Definitions

* `ι : Semiformula L ξ n → Semiformulaᵢ L ξ n`, the *intuitionistic reading*
  of a classical (negation-normal) formula: atoms to atoms, negated atoms to
  `∼atom`, `⊤ ⊥ ⋏ ⋎ ∀ ∃` to themselves.
* `iPRA : Theoryᵢ language 𝗜𝗻𝘁¹`, conventional intuitionistic PRA in the PRA
  language: `ι` of the equality axioms, the defining equations of every code,
  the basic axioms (`S x ≠ 0`, successor injectivity, the order definition),
  and every open induction instance `ι (succInd φ)`, `φ` open.
* **Target theorem.**
  `iPRA ⊢ ι (lMap classicalSentence) 🡘 ∼ ι (lMap rho)`:
  "the equation has no positive zero iff ZFC proves no contradiction", with
  consistency read as `¬Prov(⊥)`. (`ι (sourceSentence)` is the De Morgan
  normal form of the same statement and is intuitionistically stronger; it is
  not the target.)

## Proof route

1. **Pure logic.** For every classical `φ`: `𝗜𝗻𝘁¹ ⊢ ι φ 🡒 φᴺ` (induction on
   `φ`; the negation-normal form has no implications). `ι` commutes with
   rewriting. For negative `φ` such as `classicalSentence`, `φᴺ` and `ι φ`
   agree up to the `∼∼` on atoms.
2. **Decidable atoms in iPRA.** `iPRA ⊢ s = t ⋎ ∼ s = t` and the same for `<`.
   This is the only intuitionistic arithmetic: `t = 0 ⋎ t ≠ 0` by open
   induction, then truncated subtraction for equality and the order
   definition for `<`. The HA files `HAEqualityDecidable`/`HAOrderDecidable`
   are a template, but only open induction may be used.
3. **Axiom transfer.** `iPRA ⊢ σᴺ` for every axiom `σ` of PRA: equality and
   the defining equations are atomic or negative; the basic axioms are
   negative; open induction uses `φᴺ ↔ ι φ` for open `φ` (by step 2) and
   `imply_doubleNegation`.
4. **Classical-to-iPRA transfer.** `PRA ⊢ σ → iPRA ⊢ σᴺ`: compose
   `theory_intuitionistic` with step 3 (discharge the finitely many
   translated axioms used).
5. **Bounded formulas.** For `Σ₀` `θ`: transfer the characteristic-code
   theorem to get `iPRA ⊢ θᴺ ↔ c = 1` (so `θᴺ` is decidable), transfer the
   bounded-search correctness theorem for witnesses, and conclude
   `iPRA ⊢ θᴺ 🡒 ι θ` by induction on `θ`. The bounded `∀` case needs no
   double-negation shift because `ᴺ` commutes with `∀`.
6. **Normalization of rho.** From step 4 on `boundCertificate_rho`
   (`PRA ⊢ rho → ∃w bnd rho w`) and step 5 on `bnd rho w`:
   `iPRA ⊢ rhoᴺ → ∼∼∃w ι (bnd rho w)`; with `ι (bnd rho w) → ι rho`
   (pure logic: `bnd` only bounds existentials) this gives
   `iPRA ⊢ ∼ ι rho → ∼ rhoᴺ`; step 1 gives the converse.
7. **Assembly.** Step 4 on the classical endpoint gives
   `iPRA ⊢ (classicalSentence 🡘 ∼rho)ᴺ`; steps 1 and 6 and
   `neg_doubleNegation` rewrite both sides into the target.

## Size (proof obligations)

* step 1: one recursive definition, three induction lemmas;
* step 2: about six iPRA derivations;
* step 3: five axiom families;
* step 4: one composition lemma;
* step 5: two transferred classical theorems (characteristic and search),
  one induction over `Σ₀` formulas;
* steps 6–7: one module.

## Status

* 31 October 2026: plan written; infrastructure surveyed. The classical
  endpoint `PRACurrentConsistencyEndpoint.pra_current_iff_consistency` is
  closed. `IPRATheory.lean` (definitions of `ι` and `iPRA`) is drafted, not
  yet compiled.
