import PA194ReplacementOpening
import PA194SourceEqualityPreservation
import PA194SourceHead6Preservation
import PA194ContradictionInternalRefutation
import PA194InternalBitDiagonal
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194SourceHead5Preservation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194GenericRenameBase PA194GenericRenameAxiom PA194GenericRenameRules PA194RenameShiftCompatibility PA194RenameSubstitution PA194RenameContexts
open PA194SourceOutputWF PA194SourceRho8Preservation PA194SourceEqualityPreservation PA194SourceHead6Preservation PA194ReplacementOpening PA194ContradictionTranslation
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def bitBase : Bootstrapping.Semiformula M ℒₒᵣ 2 :=
  ⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝

lemma bitBase_fixed : shift ℒₒᵣ (bitBase (M := M)).val = (bitBase (M := M)).val := by
  change shift ℒₒᵣ (⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : M) = _
  rw [← Semiformula.quote_shift]
  congr 1
  change Rew.shift ▹ (Rewriting.emb bitDef.val : ArithmeticSemiformula Nat 2) = _
  apply Semiformula.rew_eq_self_of
  · intro x; simp
  · intro x hx
    exfalso
    have he : (Rewriting.emb bitDef.val : ArithmeticSemiformula Nat 2).freeVariables = ∅ :=
      Semiformula.freeVariables_emb bitDef.val
    change x ∈ (Rewriting.emb bitDef.val : ArithmeticSemiformula Nat 2).freeVariables at hx
    rw [he] at hx
    simpa using hx

lemma renameVec_two_fvars (label target a b : M) :
    renameVec replaceGraph replaceMap replaceGraph_correct (pair label target) 2 ?[^&a,^&b] =
      ?[^&(if label=a then target else a), ^&(if label=b then target else b)] := by
  unfold renameVec
  rw [show (2 : M) = 1+1 by norm_num,
    Language.TermRec.Construction.resultVec_cons _ _ _ (by simp) (by simp),
    show (1 : M) = 0+1 by simp,
    Language.TermRec.Construction.resultVec_cons _ _ _ (by simp) (by simp)]
  simp [termConstruction,replaceMap]

lemma rename_bit (label target a b : M) :
    renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) (bitFormula a b).val =
      (bitFormula (if label=a then target else a) (if label=b then target else b)).val := by
  have hbase : renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) (bitBase (M := M)).val = (bitBase (M := M)).val :=
    formula_fixed replaceGraph replaceMap replaceGraph_correct _ 2 _ (bitBase (M := M)).isSemiformula bitBase_fixed
  have h := formula_rename_subst replaceGraph replaceMap replaceGraph_correct (pair label target) 2 (bitBase (M := M)).val
    (bitBase (M := M)).isSemiformula 0 ?[^&b,^&a] (by simp)
  rw [hbase,renameVec_two_fvars] at h
  simpa [bitFormula,bitBase,Bootstrapping.Semiformula.val_substs, Bootstrapping.SemitermVec.val,
    matrixToVec, adjoin_def] using h

lemma rename_eq (label target a b : M) :
    renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target)
      (((Bootstrapping.Semiterm.fvar a : Bootstrapping.Term M ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar b).val) =
    (((Bootstrapping.Semiterm.fvar (if label=a then target else a) : Bootstrapping.Term M ℒₒᵣ) ≐
      Bootstrapping.Semiterm.fvar (if label=b then target else b)).val) := by
  have hr : (ℒₒᵣ : Language).IsRel (2 : M) (0 : M) := by
    apply Arithmetic.isRel_iff_LOR.mpr
    left
    exact ⟨rfl,rfl⟩
  have hv : IsUTermVec ℒₒᵣ (2 : M) ?[^&a,^&b] := by simp
  have h := rename_rel replaceGraph replaceMap replaceGraph_correct (pair label target) 2 0 ?[^&a,^&b] hr hv
  change renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) (^rel 2 0 ?[^&a,^&b]) =
    ^rel 2 0 (renameVec replaceGraph replaceMap replaceGraph_correct (pair label target) 2 ?[^&a,^&b]) at h
  rw [renameVec_two_fvars] at h
  have heq : Encodable.encode (Language.Eq.eq : (ℒₒᵣ : Language).Rel 2) = 0 := by decide
  simpa [Arithmetic.qqEQ, Arithmetic.eqIndex, heq] using h

lemma rename_imp (label target p q : M) (hp : IsFormula ℒₒᵣ p) (hq : IsFormula ℒₒᵣ q) :
    renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) (imp ℒₒᵣ p q) =
      imp ℒₒᵣ (renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) p)
        (renameFormula replaceGraph replaceMap replaceGraph_correct (pair label target) q) := by
  unfold imp
  rw [rename_or replaceGraph replaceMap replaceGraph_correct _ _ _ hp.isUFormula.neg hq.isUFormula,
    formula_neg replaceGraph replaceMap replaceGraph_correct _ 0 p hp]

lemma one_code : translated (1 : M) = (bitFormula 0 0).val := by
  simpa [memSource, cantor, triangle] using membership_code (0 : M) 0

lemma opening_head5 (label h : M) :
    substs1 ℒₒᵣ (^&h) (PA194InternalFormulaClose.close label 0
      (imp ℒₒᵣ (translated (eqSource h label)) (translated 1))) =
      imp ℒₒᵣ (((Bootstrapping.Semiterm.fvar h : Bootstrapping.Term M ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar h).val)
        (bitFormula (if label = 0 then h else 0) (if label = 0 then h else 0)).val := by
  have he : IsFormula ℒₒᵣ (translated (eqSource h label)) := (fixed_all_wf (eqSource h label)).1
  have hd : IsFormula ℒₒᵣ (translated (1 : M)) := (fixed_all_wf (1 : M)).1
  have hs := specialization_agreement label h (imp ℒₒᵣ (translated (eqSource h label)) (translated 1)) (IsSemiformula.imp.mpr ⟨he,hd⟩)
  rw [← hs, rename_imp label h (translated (eqSource h label)) (translated 1) he hd,
    equality_code, one_code, rename_eq, rename_bit]
  simp

lemma head5_typed (label h : M) :
    let D : Bootstrapping.Formula M ℒₒᵣ := ⟨translated 1, (fixed_all_wf 1).1⟩
    let Q : Bootstrapping.Semiformula M ℒₒᵣ 1 := ⟨PA194InternalFormulaClose.close label 0
      (imp ℒₒᵣ (translated (eqSource h label)) (translated 1)), by
        apply PA194InternalFormulaClose.close_wellformed
        exact IsSemiformula.imp.mpr ⟨(fixed_all_wf _).1,(fixed_all_wf _).1⟩⟩
    (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ (∀⁰ Q) 🡒 D := by
  classical
  dsimp only
  let T := (𝗣𝗔 : ArithmeticTheory).internalize M
  let D : Bootstrapping.Formula M ℒₒᵣ := ⟨translated 1, (fixed_all_wf 1).1⟩
  let Q : Bootstrapping.Semiformula M ℒₒᵣ 1 := ⟨PA194InternalFormulaClose.close label 0
      (imp ℒₒᵣ (translated (eqSource h label)) (translated 1)), by
        apply PA194InternalFormulaClose.close_wellformed
        exact IsSemiformula.imp.mpr ⟨(fixed_all_wf _).1,(fixed_all_wf _).1⟩⟩
  change T ⊢ (∀⁰ Q) 🡒 D
  let B := bitFormula (if label = 0 then h else 0) (if label = 0 then h else 0)
  let E : Bootstrapping.Formula M ℒₒᵣ :=
    (Bootstrapping.Semiterm.fvar h : Bootstrapping.Term M ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar h
  have hopen : Q.subst ![Bootstrapping.Semiterm.fvar h] = E 🡒 B := by
    apply Bootstrapping.Semiformula.ext
    change substs1 ℒₒᵣ (^&h) (PA194InternalFormulaClose.close label 0
      (imp ℒₒᵣ (translated (eqSource h label)) (translated 1))) = _
    exact opening_head5 label h
  apply Nonempty.intro
  apply FiniteContext.deduct'
  have hU : [∀⁰ Q] ⊢[T]! ∀⁰ Q := FiniteContext.byAxm (by simp)
  have hspec : [∀⁰ Q] ⊢[T]! E 🡒 B := by
    rw [← hopen]
    exact TProof.specializeWithCtx hU (Bootstrapping.Semiterm.fvar h)
  have heq : [∀⁰ Q] ⊢[T]! E := FiniteContext.of (Bootstrapping.Arithmetic.eq_refl (𝗣𝗔 : ArithmeticTheory) (Bootstrapping.Semiterm.fvar h)).some
  have hneg : [∀⁰ Q] ⊢[T]! ∼B := by
    apply FiniteContext.of
    simpa [B,bitFormula] using (PA194InternalBitDiagonal.internal_PA_proves_bit_diag_neg (if label = 0 then h else 0)).some
  exact CNC ⨀ hneg ⨀ (hspec ⨀ heq)

lemma head5 (label h : M) : Provable (𝗣𝗔 : ArithmeticTheory)
    (translated (impSource (allSource label (impSource (eqSource h label) 1)) 1)) := by
  have hnz : impSource (eqSource h label) 1 ≠ 0 := imp_nonzero_left _ _ (eqSource_nonzero h label)
  have houter : impSource (allSource label (impSource (eqSource h label) 1)) 1 ≠ 0 :=
    imp_nonzero_left _ _ (allSource_nonzero _ _)
  rw [imp_code _ _ houter, universal_code, imp_code _ _ hnz]
  exact (tprovable_iff_provable).mp (head5_typed label h)

#print axioms head5
#print axioms head5_typed
#print axioms opening_head5
#print axioms rename_bit
#print axioms rename_eq
end models
end PA194SourceHead5Preservation
