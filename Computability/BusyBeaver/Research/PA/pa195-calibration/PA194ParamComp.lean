import PA194ParamRecursionGraph
/-! Uniform parameter-free Σ₁ graphs are closed under finite composition. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194ParamComp
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

def toFree {n : ℕ} (φ : 𝚺₁.Semisentence n) : ArithmeticFormula (Fin n) :=
  Rew.embSubsts (fun i => &i) ▹ φ.val

def compAux {k m : ℕ} (φ : 𝚺₁.Semisentence (m+1))
    (ψ : Fin m → 𝚺₁.Semisentence (k+1)) : ArithmeticFormula (Fin (k+1)) :=
    exsClosure ((Rew.bind (L := ℒₒᵣ) (ξ₁ := Fin (m+1)) ![] (&0 :> (#·)) ▹ toFree φ) ⋏
      Matrix.conj fun i => Rew.bind (L := ℒₒᵣ) (ξ₁ := Fin (k+1)) ![] (#i :> (&·.succ)) ▹ toFree (ψ i))

def compGraph {k m : ℕ} (φ : 𝚺₁.Semisentence (m+1))
    (ψ : Fin m → 𝚺₁.Semisentence (k+1)) : 𝚺₁.Semisentence (k+1) :=
  .mkSigma ((Rew.bind (L := ℒₒᵣ) (ξ₁ := Fin (k+1)) ![] (#0 :> (#·.succ))) ▹ compAux φ ψ) (by
    apply Hierarchy.rew
    apply Hierarchy.exsClosure
    apply Hierarchy.and
    · apply Hierarchy.rew
      exact Hierarchy.rew _ φ.sigma_prop
    · apply Hierarchy.conj_iff.mpr
      intro i
      apply Hierarchy.rew
      exact Hierarchy.rew _ (ψ i).sigma_prop)

section model
variable {M : Type} [ORingStructure M]

theorem toFree_iff {n : ℕ} (φ : 𝚺₁.Semisentence n) (e : Fin n → M) :
    (toFree φ).Evalf e ↔ φ.val.Evalb e := by
  simp [toFree, Semiformula.eval_embSubsts, Function.comp_def]

theorem compAux_iff {k m : ℕ} (φ : 𝚺₁.Semisentence (m+1))
    (ψ : Fin m → 𝚺₁.Semisentence (k+1)) (y : M) (v : Fin k → M) :
    (compAux φ ψ).Evalf (y :> v) ↔ ∃ w : Fin m → M,
      φ.val.Evalb (y :> w) ∧ ∀ i, (ψ i).val.Evalb (w i :> v) := by
  simp [compAux, Semiformula.eval_rew, Function.comp_def, Matrix.empty_eq, Matrix.comp_vecCons', toFree_iff]


theorem compGraph_iff {k m : ℕ} (φ : 𝚺₁.Semisentence (m+1))
    (ψ : Fin m → 𝚺₁.Semisentence (k+1)) (y : M) (v : Fin k → M) :
    (compGraph φ ψ).val.Evalb (y :> v) ↔ ∃ w : Fin m → M,
      φ.val.Evalb (y :> w) ∧ ∀ i, (ψ i).val.Evalb (w i :> v) := by
  simpa [compGraph, Semiformula.eval_rew, Matrix.empty_eq, Function.comp_def,
    Matrix.comp_vecCons'] using compAux_iff φ ψ y v

theorem compGraph_defined {k m : ℕ} (φ : 𝚺₁.Semisentence (m+1))
    (ψ : Fin m → 𝚺₁.Semisentence (k+1))
    (F : (Fin m → M) → M) (G : Fin m → (Fin k → M) → M)
    (hF : 𝚺₁.DefinedFunction F φ) (hG : ∀ i, 𝚺₁.DefinedFunction (G i) (ψ i)) :
    𝚺₁.DefinedFunction (fun v => F (fun i => G i v)) (compGraph φ ψ) := by
  apply HierarchySymbol.Defined.mk
  intro e
  have he : (e 0 :> fun i => e i.succ) = e := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [←he, compGraph_iff]
  simp only [hF.iff, (hG _).iff, Matrix.cons_val_zero, Matrix.cons_val_succ]
  constructor
  · rintro ⟨w, hw, hg⟩
    have : w = fun i => G i (fun i => e i.succ) := by funext i; exact hg i
    simpa [this] using hw
  · intro h
    exact ⟨fun i => G i (fun i => e i.succ), h, fun _ => rfl⟩

#print axioms compGraph_defined
#print axioms compAux_iff
end model
end PA194ParamComp
