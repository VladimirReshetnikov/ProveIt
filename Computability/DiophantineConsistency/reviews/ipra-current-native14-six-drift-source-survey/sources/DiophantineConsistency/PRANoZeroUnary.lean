import DiophantineConsistency.PRAPositiveNormalize
import DiophantineConsistency.PRAPositiveMapPack
import DiophantineConsistency.PRABoundedWitness
/-! One unary open predicate for the negation of an arbitrary finite
quantifier-free arithmetic no-zero equation, in all candidate-PRA models. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRANoZeroUnary
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAPositiveNormalization PRAPositiveNormalize PRAPositiveMapPack
  PRABoundedCharacteristic PRABoundedWitness PRABoundedFormula

def noZero (n : ℕ) (a b : Semiterm ℒₒᵣ Empty n) : ArithmeticSentence :=
  ∀⁰* (Semiformula.nrel Language.ORing.Rel.eq ![a,b])

theorem positive_exsClosure {n : ℕ} (φ : Semisentence ℒₒᵣ n)
    (hφ : ParsonsBasePositive.Positive φ) : ParsonsBasePositive.Positive (∃⁰* φ) := by
  induction n with
  | zero => exact hφ
  | succ n ih =>
    simpa only [exsClosure_succ] using ih (∃⁰ φ) (ParsonsBasePositive.Positive.exs hφ)

theorem noZero_refutation_positive (n : ℕ) (a b : Semiterm ℒₒᵣ Empty n) :
    ParsonsBasePositive.Positive (∼noZero n a b) := by
  unfold noZero
  simp only [Semiformula.neg_allClosure, Semiformula.neg_nrel]
  apply positive_exsClosure
  exact ParsonsBasePositive.Positive.bounded (Hierarchy.rel _ _ _ _)

/-- Every finite literal equation has an actual candidate-PRA equivalence
between its mapped no-zero sentence and one unary open no-zero predicate. -/
theorem noZero_unary_open (n : ℕ) (a b : Semiterm ℒₒᵣ Empty n) :
    ∃ q : Semisentence language 1, q.Open ∧
      PRA ⊢ (Semiformula.lMap embedding (noZero n a b) 🡘 ∀⁰ q) := by
  let σ := noZero n a b
  obtain ⟨N⟩ := exists_normal (mapped (noZero_refutation_positive n a b))
  obtain ⟨c,_,_,hc⟩ := PRA_proves_boundedBooleanCharacteristic N.matrix N.bounded
  let q : Semisentence language 1 := ∼ characteristicMatrix c
  refine ⟨q,?_,?_⟩
  · simp [q,characteristicMatrix,Semiformula.Open]
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hM
    letI : M↓[language] ⊧* PRA := hM
    have hcorr := models_of_provable hM hc
    have hn := N.correct M (![] : Fin 0 → M)
    have he : ∀ w : M, N.matrix.Eval (Fin.cases w ![]) Empty.elim ↔
        (characteristicMatrix c).Eval ![w] Empty.elim := by
      intro w
      have hv : (Fin.cases w ![] : Fin 1 → M) = ![w] := by
        funext i
        exact Fin.cases rfl (fun j => Fin.elim0 j) i
      rw [hv]
      exact (modelCharacteristicMatrix c N.matrix hcorr ![w]).symm
    simp only [he] at hn
    simp only [LogicalConnective.HomClass.map_neg] at hn
    have hiff : (Semiformula.lMap embedding σ).Evalb (M := M) ![] ↔
        (∀⁰ q).Evalb (M := M) ![] := by
      simp only [q, Semiformula.eval_all, LogicalConnective.HomClass.map_neg]
      classical
      constructor
      · intro hs w hcw
        apply hn.mpr ⟨w,hcw⟩
        exact hs
      · intro h
        by_contra hs
        obtain ⟨w,hw⟩ := hn.mp hs
        exact h w hw
    simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply, models_iff]
    exact ⟨hiff.1,hiff.2⟩
end DiophantineConsistency.PRANoZeroUnary
