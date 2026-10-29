import ZFCinPA.ModelCodedBindFree
import ZFCinPA.ModelCodedSchemaAxioms

/-!
All-internal universally closed Separation/Replacement axiom constructors.
The input matrices may contain arbitrary internal free labels; no shift-fixedness
premise is imposed. Fixed represented closing graphs and direct axiom proof
codes are supplied. This source does not yet specialize a nonstandard number
of universal binders to recover the open schema body, nor translate set-theory
proofs or prove a PA consistency comparison.
-/
namespace LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.ModelCodedBindFree
open LeanProofs.ZFCinPA.ModelCodedSchemaAxioms
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

noncomputable def closeFormulaCode (L : Language) [L.Encodable] [L.LORDefinable]
    (p : V) : V :=
  qqAlls (bindFreeAt L 0 p) (bv L (bindFreeAt L 0 p))

noncomputable def closeFormulaCodeDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 2 := .mkSigma “out p.
      ∃ b, !(bindFreeAtDef L) b 0 p ∧ ∃ m, !(bvGraph L) m b ∧ !qqAllsDef out b m”

instance closeFormulaCode_defined : 𝚺₁-Function₁[V] (closeFormulaCode L)
    via closeFormulaCodeDef L := .mk fun e => by
  simp [closeFormulaCodeDef, closeFormulaCode]

lemma closeFormulaCode_isFormula {p : V} (hp : IsFormula L p) :
    IsFormula L (closeFormulaCode L p) := by
  have h : IsSemiformula L (0 + bv L (bindFreeAt L 0 p)) (bindFreeAt L 0 p) := by
    simpa using (bindFreeAt_closing hp).1.isSemiformula
  exact h.qqAlls

/-- A literal recognizer witness built by the all-internal closing traversal. -/
theorem closeFormulaCode_schemaRecognizer {a : Nat} (Fval : V → V)
    (K : Semiformula V L a) (hF : IsFormula L (Fval K.val))
    (hbound : K.val ≤ Fval K.val) :
    SchemaRecognizer L a Fval (closeFormulaCode L (Fval K.val)) := by
  rcases bindFreeAt_closing hF with ⟨hu, hs, hi⟩
  refine ⟨bv L (bindFreeAt L 0 (Fval K.val)), index_le_qqAlls _ _,
    bindFreeAt L 0 (Fval K.val), le_qqAlls _ _, rfl, hu, hs, rfl,
    K.val, ?_, K.isSemiformula, hi⟩
  rw [hi]
  exact hbound

noncomputable def closedSeparation (K : Semiformula V ℒₛₑₜ 1) : Formula V ℒₛₑₜ :=
  ⟨closeFormulaCode ℒₛₑₜ (sepBodyVal K.val), closeFormulaCode_isFormula
    (by rw [sepBodyVal_eq K]; exact (sepBody K).isSemiformula)⟩

noncomputable def closedReplacement (K : Semiformula V ℒₛₑₜ 2) : Formula V ℒₛₑₜ :=
  ⟨closeFormulaCode ℒₛₑₜ (repBodyVal K.val), closeFormulaCode_isFormula
    (by rw [repBodyVal_eq K]; exact (repBody K).isSemiformula)⟩

/-- No support bound, standardness or shift-fixedness premise on the matrix. -/
theorem closedSeparation_recognized (K : Semiformula V ℒₛₑₜ 1) :
    SepR (closedSeparation K).val := by
  apply closeFormulaCode_schemaRecognizer sepBodyVal K
  · rw [sepBodyVal_eq K]; exact (sepBody K).isSemiformula
  · have h := subst_le_sepBodyVal K.val
    rw [sep_core_subst_identity K] at h
    exact h

/-- No support bound, standardness or shift-fixedness premise on the matrix. -/
theorem closedReplacement_recognized (K : Semiformula V ℒₛₑₜ 2) :
    RepR (closedReplacement K).val := by
  apply closeFormulaCode_schemaRecognizer repBodyVal K
  · rw [repBodyVal_eq K]; exact (repBody K).isSemiformula
  · have h := subst3_le_repBodyVal K.val
    rw [rep_core_subst_identity K] at h
    exact h

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private lemma union_class_iff (T U : Theory ℒₛₑₜ) [T.Δ₁] [U.Δ₁] (p : V) :
    p ∈ (T ∪ U).Δ₁Class ↔ p ∈ T.Δ₁Class ∨ p ∈ U.Δ₁Class := ModelCodedSchemaAxioms.union_class_iff T U p

private lemma separation_class_iff (p : V) :
    p ∈ separationTheory.Δ₁Class ↔ SepR p := ModelCodedSchemaAxioms.separation_class_iff p

private lemma replacement_class_iff (p : V) :
    p ∈ replacementTheory.Δ₁Class ↔ RepR p := ModelCodedSchemaAxioms.replacement_class_iff p

theorem closedSeparation_mem_zf (K : Semiformula V ℒₛₑₜ 1) :
    (closedSeparation K).val ∈ (𝗭𝗙 : SetTheory).Δ₁Class := by
  change (closedSeparation K).val ∈
    (((𝗘𝗤 ℒₛₑₜ ∪ zfFixed) ∪ separationTheory) ∪ replacementTheory).Δ₁Class
  rw [union_class_iff, union_class_iff, union_class_iff]
  exact Or.inl (Or.inr ((separation_class_iff _).mpr (closedSeparation_recognized K)))

theorem closedReplacement_mem_zf (K : Semiformula V ℒₛₑₜ 2) :
    (closedReplacement K).val ∈ (𝗭𝗙 : SetTheory).Δ₁Class := by
  change (closedReplacement K).val ∈
    (((𝗘𝗤 ℒₛₑₜ ∪ zfFixed) ∪ separationTheory) ∪ replacementTheory).Δ₁Class
  rw [union_class_iff]
  exact Or.inr ((replacement_class_iff _).mpr (closedReplacement_recognized K))

theorem closedSeparation_mem_zfc (K : Semiformula V ℒₛₑₜ 1) :
    (closedSeparation K).val ∈ (𝗭𝗙𝗖 : SetTheory).Δ₁Class := by
  exact (union_class_iff (𝗭𝗙 : SetTheory) 𝗔𝗖 _).mpr (Or.inl (closedSeparation_mem_zf K))

theorem closedReplacement_mem_zfc (K : Semiformula V ℒₛₑₜ 2) :
    (closedReplacement K).val ∈ (𝗭𝗙𝗖 : SetTheory).Δ₁Class := by
  exact (union_class_iff (𝗭𝗙 : SetTheory) 𝗔𝗖 _).mpr (Or.inl (closedReplacement_mem_zf K))

/-- The proof code is the actual axiom constructor, without choosing a proof. -/
noncomputable def axiomCode (p : V) : V := axm (insert p ∅) p

private lemma axiomCode_isProof (T : Theory ℒₛₑₜ) [T.Δ₁] (p : Formula V ℒₛₑₜ)
    (hp : p.val ∈ T.Δ₁Class) : Proof T (axiomCode p.val) p.val := by
  change DerivationOf T (axm (insert p.val ∅) p.val) {p.val}
  refine ⟨?_, Derivation.axm (by simp) (by simp) hp⟩
  simp

theorem closedSeparation_zf_isProof (K : Semiformula V ℒₛₑₜ 1) :
    Proof (𝗭𝗙 : SetTheory) (axiomCode (closedSeparation K).val) (closedSeparation K).val :=
  axiomCode_isProof _ _ (closedSeparation_mem_zf K)

theorem closedReplacement_zf_isProof (K : Semiformula V ℒₛₑₜ 2) :
    Proof (𝗭𝗙 : SetTheory) (axiomCode (closedReplacement K).val) (closedReplacement K).val :=
  axiomCode_isProof _ _ (closedReplacement_mem_zf K)

theorem closedSeparation_zfc_isProof (K : Semiformula V ℒₛₑₜ 1) :
    Proof (𝗭𝗙𝗖 : SetTheory) (axiomCode (closedSeparation K).val) (closedSeparation K).val :=
  axiomCode_isProof _ _ (closedSeparation_mem_zfc K)

theorem closedReplacement_zfc_isProof (K : Semiformula V ℒₛₑₜ 2) :
    Proof (𝗭𝗙𝗖 : SetTheory) (axiomCode (closedReplacement K).val) (closedReplacement K).val :=
  axiomCode_isProof _ _ (closedReplacement_mem_zfc K)

end LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms
