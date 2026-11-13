import ZFCinPA.SchemaSourceSyntax
import ZFCinPA.QSchemaSem
import ZFCinPA.NativePeel
import ZFCinPA.SubstIdentity
import ZFCinPA.QFixed

set_option autoImplicit false
noncomputable section

/-!
# `ZF` is interpretable in the native theory, inside `IΣ₁` (`R3`)

In every model of `𝗜𝚺₁`, every internal axiom code of `𝗭𝗙` has an internal
`qTheory`-derivation of its WF interpretation (parameter
`QInterp.PN`), with domain side formulas:

* equality axioms and the seven fixed axioms: `QFixed.provable_interp_fixed`;
* a separation code `qqAlls b m` with core `K`: the congruence law of `K` is
  a theorem of pure equality logic (`SetCongruence.congruenceProof₁`), so its
  interpretation is derivable in `qTheory` with domain side formulas
  (`derivable_interp_of_EQ`, by `InternalInterpretation.derivable_iSet`);
  the compiled template `QSchemaSem.sepT` turns it into the interpreted
  separation body (`sep_base`; the code identities are
  `QTInterp.interp_translate`), and the peel closes the opened parameters
  (`sep_obligation`);
* replacement codes, the same with `replT` (`repl_obligation`).

Hence (`provable_falsum_native_of_ZF`) an internal `𝗭𝗙`-refutation yields an
internal `qTheory`-refutation, and by completeness

`𝗜𝚺₁ ⊢ Con(qTheory) → Con(𝗭𝗙)` and `𝗣𝗔 ⊢ Con(qTheory) → Con(𝗭𝗙)`.
-/

namespace LeanProofs.ZFCinPA.QSchema

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.SetPlaceholderQuotient
open LeanProofs.ZFCinPA.InternalInterpretation LeanProofs.BoundedPAConsistency.InternalRelativization
open LeanProofs.ZFCinPA.ValidatorSeedQTheory222 LeanProofs.ZFCinPA.QInterp LeanProofs.ZFCinPA.QTemplate
open LeanProofs.ZFCinPA.QTInterp LeanProofs.ZFCinPA.QSchemaSem LeanProofs.ZFCinPA.NativePeel
open LeanProofs.ZFCinPA.OpenSchemaTemplates
open scoped LO.FirstOrder.Arithmetic

local instance {k : ℕ} {arities : Fin k → ℕ} : Language.Mem (setTemplateLanguage k arities) :=
  ⟨Sum.inl Language.Set.Rel.mem⟩

/-! ## The source bodies as template translations -/

lemma emb_sepS : (Rewriting.emb sepS : Proposition SL) = sepBodySource (Rewriting.emb R1) := SchemaSourceSyntax.emb_sepS

lemma emb_repS : (Rewriting.emb repS : Proposition RL) = repBodySource (Rewriting.emb R2) := SchemaSourceSyntax.emb_repS

section Internal

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma subst_bvar0 (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (w : Bootstrapping.SemitermVec V ℒₛₑₜ 1 1) (hw : w 0 = .bvar 0) :
    (K.subst w).val = K.val := SchemaSourceSyntax.subst_bvar0 K w hw

lemma subst_bvar01 (K : Bootstrapping.Semiformula V ℒₛₑₜ 2)
    (w : Bootstrapping.SemitermVec V ℒₛₑₜ 2 2) (hw0 : w 0 = .bvar 0) (hw1 : w 1 = .bvar 1) :
    (K.subst w).val = K.val := SchemaSourceSyntax.subst_bvar01 K w hw0 hw1

lemma translate_sepS (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    (translateFormula (fun _ : Fin 1 ↦ K) (Rewriting.emb sepS : Proposition SL)).val =
      sepBodyVal K.val := SchemaSourceSyntax.translate_sepS K

lemma translate_repS (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    (translateFormula (fun _ : Fin 1 ↦ K) (Rewriting.emb repS : Proposition RL)).val =
      repBodyVal K.val := SchemaSourceSyntax.translate_repS K

/-! ## Transport of equality-logic theorems -/

lemma hTermSet : ∀ t : V, IsTerm ℒₛₑₜ t → ∃ j, t = ^&j :=
  fun _ ht ↦ SetRelativization.isTerm_eq_fvar ht

lemma domSet_zero_empty : domSet ℒₛₑₜ (dom (PN : V)) 0 = ∅ :=
  NativePeel.domSet_zero _

/-- Every internal equality axiom is interpreted-derivable. -/
lemma eq_obligation {p : V} (h : p ∈ (𝗘𝗤 ℒₛₑₜ : SetTheory).Δ₁Class) :
    ∃ m, Derivable qTheory (insert (interp (PN : V) p) (domSet ℒₛₑₜ (dom (PN : V)) m)) :=
  NativePeel.finite_obligation (𝗘𝗤 ℒₛₑₜ) Theory.EqAxiom.finite
    (fun σ hσ => QFixed.provable_interp_fixed σ (Or.inl hσ)) h

/-- **Equality-logic theorems transport**: the interpretation of an internal
`𝗘𝗤`-theorem is derivable in `qTheory` with domain side formulas. -/
lemma derivable_interp_of_EQ {φ : V} (h : Provable (𝗘𝗤 ℒₛₑₜ : SetTheory) φ) :
    ∃ m, Derivable qTheory (insert (interp (PN : V) φ) (domSet ℒₛₑₜ (dom (PN : V)) m)) :=
  InternalInterpretation.derivable_interp_of_provable good_PN hTermSet (fun _ _ hp ↦ eq_obligation hp) h

lemma derivable_domSet_mono {x m m' : V} (hm : m ≤ m') (hx : IsFormula ℒₛₑₜ x)
    (h : Derivable qTheory (insert x (domSet ℒₛₑₜ (dom (PN : V)) m))) :
    Derivable qTheory (insert x (domSet ℒₛₑₜ (dom (PN : V)) m')) :=
  InternalInterpretation.derivable_domSet_mono good_PN.isDom hm hx h

/-! ## The bases -/

/-- **The separation base**: the interpreted separation body over any core. -/
theorem sep_base {K : V} (hK : IsSemiformula ℒₛₑₜ 1 K) :
    ∃ m, Derivable qTheory
      (insert (interp (PN : V) (sepBodyVal K)) (domSet ℒₛₑₜ (dom (PN : V)) m)) := by
  let Kt : Bootstrapping.Semiformula V ℒₛₑₜ 1 := ⟨K, by simpa using hK⟩
  have hc : Provable (𝗘𝗤 ℒₛₑₜ : SetTheory) (SetCongruence.congruenceFormula 1 Kt).val :=
    Bootstrapping.tprovable_iff_provable.mp (SetCongruence.congruenceProof₁ (𝗘𝗤 ℒₛₑₜ) Kt)
  obtain ⟨m, hm⟩ := derivable_interp_of_EQ hc
  have ht := compileN_provable (k := 1) (arities := ar1) (fun _ ↦ by simp)
    (fun i ↦ IK ((fun _ : Fin 1 ↦ Kt) i)) sepT_provable
  rw [sepT, LogicalConnective.HomClass.map_imply, translateFormula_imp] at ht
  have hp := Bootstrapping.tprovable_iff_provable.mp ht
  rw [Bootstrapping.Semiformula.val_imp, ← interp_translate_emb, ← interp_translate_emb,
    translate_sepS, cong1, SetCongruence.translate_setPlaceholderCongruenceSentence] at hp
  have hS : IsFormula ℒₛₑₜ (interp (PN : V) (sepBodyVal K)) := by
    rw [sepBodyVal_eq Kt]
    exact isSemiformula_interp good_PN (sepBody Kt).isSemiformula
  exact ⟨m, derivable_mp hS hp hm⟩

/-- **The replacement base**: the interpreted replacement body over any core. -/
theorem repl_base {K : V} (hK : IsSemiformula ℒₛₑₜ 2 K) :
    ∃ m, Derivable qTheory
      (insert (interp (PN : V) (repBodyVal K)) (domSet ℒₛₑₜ (dom (PN : V)) m)) := by
  let Kt : Bootstrapping.Semiformula V ℒₛₑₜ 2 := ⟨K, by simpa using hK⟩
  have hc : Provable (𝗘𝗤 ℒₛₑₜ : SetTheory) (SetCongruence.congruenceFormula 2 Kt).val :=
    Bootstrapping.tprovable_iff_provable.mp (SetCongruence.congruenceProof₂ (𝗘𝗤 ℒₛₑₜ) Kt)
  obtain ⟨m, hm⟩ := derivable_interp_of_EQ hc
  have ht := compileN_provable (k := 1) (arities := ar2) (fun _ ↦ by show (2 : ℕ) ≤ 3; omega)
    (fun i ↦ IK ((fun _ : Fin 1 ↦ Kt) i)) replT_provable
  rw [replT, LogicalConnective.HomClass.map_imply, translateFormula_imp] at ht
  have hp := Bootstrapping.tprovable_iff_provable.mp ht
  rw [Bootstrapping.Semiformula.val_imp, ← interp_translate_emb, ← interp_translate_emb,
    translate_repS, cong2, SetCongruence.translate_setPlaceholderCongruenceSentence] at hp
  have hS : IsFormula ℒₛₑₜ (interp (PN : V) (repBodyVal K)) := by
    rw [repBodyVal_eq Kt]
    exact isSemiformula_interp good_PN (repBody Kt).isSemiformula
  exact ⟨m, derivable_mp hS hp hm⟩

/-! ## The schema obligations -/

/-- **Every internal separation axiom is interpreted-derivable.** -/
theorem sep_obligation {p : V} (hp : SepR p) :
    ∃ e, Derivable qTheory (insert (interp (PN : V) p) (domSet ℒₛₑₜ (dom (PN : V)) e)) :=
  NativePeel.schema_obligation good_PN sepBodyVal (fun _ hK => sep_base (by simpa using hK)) hp

/-- **Every internal replacement axiom is interpreted-derivable.** -/
theorem repl_obligation {p : V} (hp : RepR p) :
    ∃ e, Derivable qTheory (insert (interp (PN : V) p) (domSet ℒₛₑₜ (dom (PN : V)) e)) :=
  NativePeel.schema_obligation good_PN repBodyVal (fun _ hK => repl_base (by simpa using hK)) hp

/-! ## The axiom class of `𝗭𝗙` -/

lemma separation_class_iff (p : V) : p ∈ separationTheory.Δ₁Class ↔ SepR p := ModelCodedSchemaAxioms.separation_class_iff p

lemma replacement_class_iff (p : V) : p ∈ replacementTheory.Δ₁Class ↔ RepR p := ModelCodedSchemaAxioms.replacement_class_iff p

/-- The internal `𝗭𝗙` axiom class splits into four parts. -/
lemma mem_ZF_class {p : V} (h : p ∈ (𝗭𝗙 : SetTheory).Δ₁Class) :
    p ∈ (𝗘𝗤 ℒₛₑₜ : SetTheory).Δ₁Class ∨ p ∈ zfFixed.Δ₁Class ∨ SepR p ∨ RepR p := ModelCodedSchemaAxioms.mem_ZF_class h

/-- Every internal fixed axiom of `𝗭𝗙` is interpreted-derivable. -/
lemma fixed_obligation {p : V} (h : p ∈ zfFixed.Δ₁Class) :
    ∃ m, Derivable qTheory (insert (interp (PN : V) p) (domSet ℒₛₑₜ (dom (PN : V)) m)) :=
  NativePeel.list_obligation
    [Axiom.empty, Axiom.extentionality, Axiom.pairing, Axiom.union,
      Axiom.power, Axiom.infinity, Axiom.foundation]
    (fun σ hσ => QFixed.provable_interp_fixed σ (Or.inr (by simpa [zfFixed] using hσ))) h

/-- **Every internal axiom of `𝗭𝗙` is interpreted-derivable in `qTheory`.** -/
theorem zf_obligation (p : V) (_ : IsFormula ℒₛₑₜ p) (h : p ∈ (𝗭𝗙 : SetTheory).Δ₁Class) :
    ∃ m, Derivable qTheory (insert (interp (PN : V) p) (domSet ℒₛₑₜ (dom (PN : V)) m)) := by
  rcases mem_ZF_class h with h | h | h | h
  · exact eq_obligation h
  · exact fixed_obligation h
  · exact sep_obligation h
  · exact repl_obligation h

/-! ## The consistency transfer -/

/-- **`ZF` refutations become native refutations, in `IΣ₁`.** -/
theorem provable_falsum_native_of_ZF (h : Provable (𝗭𝗙 : SetTheory) (^⊥ : V)) :
    Provable qTheory (^⊥ : V) :=
  provable_falsum_of_interp good_PN hTermSet zf_obligation QFixed.provable_domain h

theorem consistent_ZF_of_native (h : qTheory.Consistent V) :
    (𝗭𝗙 : SetTheory).Consistent V := by
  have e : (⌜(⊥ : Sentence ℒₛₑₜ)⌝ : V) = ^⊥ := by
    simp [LO.FirstOrder.Sentence.quote_def, LO.FirstOrder.Semiformula.quote_def]
  intro hZF
  apply h
  unfold LO.FirstOrder.Theory.Consistent at *
  rw [e] at hZF ⊢
  exact provable_falsum_native_of_ZF hZF

end Internal

/-- **`𝗜𝚺₁ ⊢ Con(qTheory) → Con(𝗭𝗙)`.** -/
theorem iSigma1_proves_con_native_imp_con_ZF :
    𝗜𝚺₁ ⊢ (qTheory.consistent : ArithmeticSentence) 🡒 (𝗭𝗙 : SetTheory).consistent := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ hM
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := hM
  simp only [Semantics.Imp.models_imply]
  intro h
  have h' : qTheory.Consistent M := by simpa [models_iff] using h
  simpa [models_iff] using consistent_ZF_of_native h'

/-- **`𝗣𝗔 ⊢ Con(qTheory) → Con(𝗭𝗙)`.** -/
theorem peano_proves_con_native_imp_con_ZF :
    𝗣𝗔 ⊢ (qTheory.consistent : ArithmeticSentence) 🡒 (𝗭𝗙 : SetTheory).consistent :=
  Entailment.WeakerThan.pbl iSigma1_proves_con_native_imp_con_ZF

end LeanProofs.ZFCinPA.QSchema
