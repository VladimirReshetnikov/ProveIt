import DiophantineConsistency.PRAPairedInductionMatrix
/-! Model-uniform normal forms for bounded positive formulas. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPositiveNormalization
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAPairedInductionMatrix

/-- A model-uniform bounded-matrix existential representation. Bound slot zero
is the witness; the remaining slots are the original bound variables. -/
structure Normal {n : ℕ} (φ : Semisentence language n) where
  matrix : Semisentence language (n+1)
  bounded : Hierarchy 𝚺 0 matrix
  correct : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA], ∀ v : Fin n → M,
      φ.Eval v Empty.elim ↔ ∃ w : M, matrix.Eval (Fin.cases w v) Empty.elim

/-- A bounded formula has a dummy existential witness. -/
def normalBounded {n : ℕ} (φ : Semisentence language n) (h : Hierarchy 𝚺 0 φ) : Normal φ where
  matrix := Rew.bShift ▹ φ
  bounded := Hierarchy.rew _ h
  correct := by
    intro M _ _ _ _ v
    have he (w : M) : (Rew.bShift ▹ φ).Eval (Fin.cases w v) Empty.elim ↔ φ.Eval v Empty.elim := by
      rw [Semiformula.eval_rew]
      have hb : (Semiterm.val (L := language) (Fin.cases w v) Empty.elim ∘ Rew.bShift ∘ Semiterm.bvar) = v := by
        funext i
        rfl
      have hf : (Semiterm.val (L := language) (Fin.cases w v) Empty.elim ∘ Rew.bShift ∘ Semiterm.fvar) =
          (Empty.elim : Empty → M) := Subsingleton.elim _ _
      rw [hb,hf]
    constructor
    · intro hp
      exact ⟨Classical.choice (inferInstance : Nonempty M), (he _).mpr hp⟩
    · rintro ⟨w,hw⟩
      exact (he w).mp hw

def normalOr {n : ℕ} {φ ψ : Semisentence language n} (a : Normal φ) (b : Normal ψ) : Normal (φ ⋎ ψ) where
  matrix := a.matrix ⋎ b.matrix
  bounded := Hierarchy.or a.bounded b.bounded
  correct := by
    intro M _ _ _ _ v
    have ha := a.correct M v
    have hb := b.correct M v
    change (φ.Eval v Empty.elim ∨ ψ.Eval v Empty.elim) ↔
      ∃ w : M, (a.matrix.Eval (Fin.cases w v) Empty.elim ∨ b.matrix.Eval (Fin.cases w v) Empty.elim)
    rw [ha,hb]
    constructor
    · rintro (⟨w,hw⟩ | ⟨w,hw⟩)
      · exact ⟨w,Or.inl hw⟩
      · exact ⟨w,Or.inr hw⟩
    · rintro ⟨w,hw | hw⟩
      · exact Or.inl ⟨w,hw⟩
      · exact Or.inr ⟨w,hw⟩
end DiophantineConsistency.PRAPositiveNormalization
