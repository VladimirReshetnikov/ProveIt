import DiophantineConsistency.HerbrandPackedContextTransfer
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandPackedContextSemantics
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAHerbrandSelection HerbrandCommonParameters HerbrandPackedContextTransfer

theorem packedSide_eval {M : Type} [Structure language M]
    (side : Proposition language) (r : ℕ) (hr : side.fvSup ≤ r) (e : ℕ → M) :
    (packedSide side r hr).Eval (fun i : Fin r => e i.val) Empty.elim ↔ side.Eval ![] e := by
  exact HerbrandPackedContextTransfer.packedSide_eval side r hr e

theorem packedMatrix_code_eval {M : Type} [Structure language M]
    (θ : Semiproposition language 1) (r : ℕ) (hr : θ.fvSup ≤ r) (c : Code r) (e : ℕ → M) :
    (openMatrixAt (packedMatrix θ r hr) c).Eval (fun i : Fin r => e i.val) Empty.elim ↔
      θ.Eval ![Structure.func (L := language) c (fun i : Fin r => e i.val)] e := by
  unfold openMatrixAt
  rw [Semiformula.eval_substs]
  have hb : (Semiterm.val (L := language) (fun i : Fin r => e i.val) Empty.elim ∘
      Fin.cases (applyCode c (vars r)) (vars r)) =
      Fin.cases (Structure.func (L := language) c (fun i : Fin r => e i.val))
        (fun i : Fin r => e i.val) := by
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    change Structure.func (L := language) c (Semiterm.val (fun i : Fin r => e i.val) Empty.elim ∘ vars r) = _
    have hv : (Semiterm.val (L := language) (fun i : Fin r => e i.val) Empty.elim ∘ vars r) =
        (fun i : Fin r => e i.val) := by funext i; rfl
    rw [hv]
    rfl
  rw [hb]
  exact HerbrandPackedContextTransfer.packedMatrix_eval θ r hr e _

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Structure.Eq language M] in
theorem modelSelectedContext (side : Proposition language) (θ : Semiproposition language 1)
    (r : ℕ) (hs : side.fvSup ≤ r) (ht : θ.fvSup ≤ r) (c : Code r)
    (p : PRA ⊢ (∀⁰* (packedSide side r hs ⋎ openMatrixAt (packedMatrix θ r ht) c)))
    (e : ℕ → M) : side.Eval ![] e ∨
      θ.Eval ![Structure.func (L := language) c (fun i : Fin r => e i.val)] e := by
  have hh := models_of_provable (inferInstance : M↓[language] ⊧* PRA) p
  simp only [models_iff, Semiformula.eval_allClosure] at hh
  have hh' := hh (fun i : Fin r => e i.val)
  change (packedSide side r hs).Eval (fun i : Fin r => e i.val) Empty.elim ∨
    (openMatrixAt (packedMatrix θ r ht) c).Eval (fun i : Fin r => e i.val) Empty.elim at hh'
  exact hh'.elim (fun h => Or.inl ((packedSide_eval side r hs e).mp h))
    (fun h => Or.inr ((packedMatrix_code_eval θ r ht c e).mp h))
end models
end DiophantineConsistency.HerbrandPackedContextSemantics
