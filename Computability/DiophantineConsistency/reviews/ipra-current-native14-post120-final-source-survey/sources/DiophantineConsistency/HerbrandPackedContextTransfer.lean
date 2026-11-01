import DiophantineConsistency.HerbrandCommonParameters
import DiophantineConsistency.HerbrandExistentialSideSelection
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandPackedContextTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRAUniversalCandidate HerbrandCommonParameters HerbrandUniversalTree
  HerbrandContextualTreeSelection HerbrandParameterizedWitness

def packedSide (side : Proposition language) (r : ℕ) (hr : side.fvSup ≤ r) : Semisentence language r :=
  cast (congrArg (Semisentence language) (Nat.zero_add r)) (pack side r hr)

def packedMatrix (θ : Semiproposition language 1) (r : ℕ) (hr : θ.fvSup ≤ r) :
    Semisentence language (r+1) := by
  exact cast (congrArg (Semisentence language) (Nat.add_comm 1 r)) (pack θ r hr)

theorem cast_eval {M : Type} [Structure language M] {a b : ℕ} (h : a = b)
    (φ : Semisentence language a) (v : Fin b → M) :
    (cast (congrArg (Semisentence language) h) φ).Eval v Empty.elim ↔
      φ.Eval (fun i => v (Fin.cast h i)) Empty.elim := by
  cases h
  rfl

theorem packedSide_eval {M : Type} [Structure language M]
    (side : Proposition language) (r : ℕ) (hr : side.fvSup ≤ r) (e : ℕ → M) :
    (packedSide side r hr).Eval (fun i : Fin r => e i.val) Empty.elim ↔ side.Eval ![] e := by
  unfold packedSide
  rw [cast_eval (Nat.zero_add r), HerbrandCommonParameters.pack_eval (fallback := e)]
  have hb0 : (fun i : Fin 0 => e ((Fin.cast (Nat.zero_add r) (Fin.castAdd r i)).val)) = ![] := Subsingleton.elim _ _
  rw [hb0]
  apply Semiformula.eval_iff_of_funEqOn
  intro i hi
  have hir : i < r := lt_of_lt_of_le (Semiformula.lt_fvSup_of_fvar? hi) hr
  simp [hir]

theorem packedMatrix_eval {M : Type} [Structure language M]
    (θ : Semiproposition language 1) (r : ℕ) (hr : θ.fvSup ≤ r)
    (e : ℕ → M) (v : M) :
    (packedMatrix θ r hr).Eval (Fin.cases v (fun i : Fin r => e i.val)) Empty.elim ↔
      θ.Eval ![v] e := by
  unfold packedMatrix
  rw [cast_eval (Nat.add_comm 1 r), HerbrandCommonParameters.pack_eval (fallback := e)]
  have hb1 : (fun i : Fin 1 => Fin.cases v (fun k : Fin r => e k.val)
      (Fin.cast (Nat.add_comm 1 r) (Fin.castAdd r i))) = ![v] := by
    funext i
    exact Fin.cases rfl (fun i => Fin.elim0 i) i
  rw [hb1]
  apply Semiformula.eval_iff_of_funEqOn
  intro i hi
  have hir : i < r := lt_of_lt_of_le (Semiformula.lt_fvSup_of_fvar? hi) hr
  simp only [hir, ↓reduceDIte]
  have hc : Fin.cast (Nat.add_comm 1 r) (Fin.natAdd 1 ⟨i,hir⟩) = (⟨i,hir⟩ : Fin r).succ := by
    apply Fin.ext
    simp [Nat.add_comm]
  rw [hc]
  rfl

theorem side_eval {M : Type} [Structure language M]
    (side : Proposition language) (r : ℕ) (hr : side.fvSup ≤ r)
    (e : ℕ → M) : (parameterSide (packedSide side r hr)).Eval ![] e ↔ side.Eval ![] e := by
  rw [parameterSide_eval]
  exact packedSide_eval side r hr e

theorem matrix_eval {M : Type} [Structure language M]
    (θ : Semiproposition language 1) (r : ℕ) (hr : θ.fvSup ≤ r)
    (e : ℕ → M) (v : M) :
    (parameterMatrix (packedMatrix θ r hr)).Eval ![v] e ↔ θ.Eval ![v] e := by
  rw [parameterMatrix_eval]
  exact packedMatrix_eval θ r hr e v

theorem cast_tree {a b : ℕ} (h : a = b) (φ : Semisentence language a)
    (ht : ExistentialTree φ) : ExistentialTree (cast (congrArg (Semisentence language) h) φ) := by
  cases h
  exact ht

theorem cast_open {a b : ℕ} (h : a = b) (φ : Semisentence language a)
    (ho : φ.Open) : (cast (congrArg (Semisentence language) h) φ).Open := by
  cases h
  exact ho

theorem packedSide_tree (side : Proposition language) (r : ℕ) (hr : side.fvSup ≤ r)
    (h : ExistentialTree side) : ExistentialTree (packedSide side r hr) := by
  unfold packedSide
  exact cast_tree (Nat.zero_add r) _ (HerbrandCommonParameters.pack_tree side r hr h)

theorem packedMatrix_open (θ : Semiproposition language 1) (r : ℕ) (hr : θ.fvSup ≤ r)
    (h : θ.Open) : (packedMatrix θ r hr).Open := by
  unfold packedMatrix
  exact cast_open (Nat.add_comm 1 r) _ (HerbrandCommonParameters.pack_open θ r hr h)

/-- An actual universal-theory contextual proof survives common packing. -/
theorem packed_proof (side : Proposition language) (θ : Semiproposition language 1)
    (r : ℕ) (hs : side.fvSup ≤ r) (ht : θ.fvSup ≤ r)
    (p : UniversalAxiom ⊢ (side ⋎ (∃⁰ θ)).univCl) :
    UniversalAxiom ⊢ ((parameterSide (packedSide side r hs)) ⋎
      (∃⁰ (parameterMatrix (packedMatrix θ r ht)))).univCl := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M hM0 hM hEq hTheory
  have hm := models_of_provable hTheory p
  simp only [models_iff, Semiformula.eval_univCl] at hm ⊢
  intro e
  change (parameterSide (packedSide side r hs)).Eval ![] e ∨
    (∃⁰ (parameterMatrix (packedMatrix θ r ht))).Eval ![] e
  rw [side_eval, Semiformula.eval_ex]
  simp only [matrix_eval]
  exact hm e

/-- Common packing composes the actual U-proof with existential-side PR
selection, with all shared parameter bounds explicit. -/
theorem PRA_exists_packedSelection (side : Proposition language) (θ : Semiproposition language 1)
    (r : ℕ) (hs : side.fvSup ≤ r) (ht : θ.fvSup ≤ r)
    (hside : ExistentialTree side) (hθ : θ.Open)
    (p : UniversalAxiom ⊢ (side ⋎ (∃⁰ θ)).univCl) :
    ∃ c : PRAFiniteFunctionCodes.Code r, Primrec (PRAFiniteFunctionCodes.eval c) ∧
      PRATheory.PRA ⊢ (∀⁰* (packedSide side r hs ⋎ PRAHerbrandSelection.openMatrixAt (packedMatrix θ r ht) c)) := by
  exact HerbrandExistentialSideSelection.PRA_exists_selected (packedSide side r hs) (packedMatrix θ r ht)
    (packedMatrix_open θ r ht hθ) (packedSide_tree side r hs hside) (packed_proof side θ r hs ht p)
end DiophantineConsistency.HerbrandPackedContextTransfer
