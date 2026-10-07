import OAI.Combinatorics.Progressions.Estimates.RawSourceTolerance

namespace OAI

section

namespace Erdos3

def booleanJetMassLog (q h : ℕ) (P : ℝ) : ℝ := q+P+(h : ℝ)*q

noncomputable def booleanToleranceC2Log {D α : Type*} [Fintype D] [Fintype α]
    {B : D → Type*} [∀ d, Fintype (B d)] (Z : Type*) [Fintype Z]
    (h : D → ℕ) (degree : ℕ) (P : ℝ) : ℝ :=
  3*Fintype.card (PolynomialParameter Z (JointBlockParameter B h α))*(degree+2 : ℕ)+
    (2*booleanJetMassLog (Fintype.card α) degree P+1)

theorem booleanJetMassBudget_le_exp (q h : ℕ) {W P : ℝ}
    (hW : 0 ≤ W) (hWP : W ≤ Real.exp P) :
    booleanJetMassBudget q h W ≤ Real.exp (booleanJetMassLog q h P) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hq : (q : ℝ)+1 ≤ Real.exp q := Real.add_one_le_exp _
  unfold booleanJetMassBudget
  calc
    _ ≤ (Real.exp 1)^q*(Real.exp P*(Real.exp q)^h) := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; unfold booleanJetMassLog; ring

theorem booleanToleranceC2Log_nonneg {D α : Type*} [Fintype D] [Fintype α]
    {B : D → Type*} [∀ d, Fintype (B d)] (Z : Type*) [Fintype Z]
    (h : D → ℕ) (degree : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ booleanToleranceC2Log (B := B) (α := α) Z h degree P := by
  unfold booleanToleranceC2Log booleanJetMassLog
  positivity

theorem booleanToleranceC2_le_exp {D α : Type*} [Fintype D] [Fintype α]
    {B : D → Type*} [∀ d, Fintype (B d)] (Z : Type*) [Fintype Z]
    (h : D → ℕ) (degree : ℕ) {Csum Wsum P : ℝ}
    (hC : 0 ≤ Csum) (hW : 0 ≤ Wsum) (hP : 0 ≤ P)
    (hCP : Csum ≤ Real.exp P) (hWP : Wsum ≤ Real.exp P) :
    booleanToleranceC2 (B := B) (α := α) Z h degree Csum Wsum ≤
      Real.exp (booleanToleranceC2Log (B := B) (α := α) Z h degree P) := by
  have hb : 0 ≤ booleanJetMassLog (Fintype.card α) degree P := by unfold booleanJetMassLog; positivity
  have hs := add_le_exp_add_one hb hb (booleanJetMassBudget_le_exp _ _ hC hCP) (booleanJetMassBudget_le_exp _ _ hW hWP)
  have hs' : booleanJetMassBudget (Fintype.card α) degree Csum+booleanJetMassBudget (Fintype.card α) degree Wsum ≤
      Real.exp (2*booleanJetMassLog (Fintype.card α) degree P+1) := by
    have he : booleanJetMassLog (Fintype.card α) degree P+
        booleanJetMassLog (Fintype.card α) degree P+1 =
        2*booleanJetMassLog (Fintype.card α) degree P+1 := by ring
    simpa only [he] using hs
  exact polynomialC2BoxBudget_le_exp _ _
    (add_nonneg (booleanJetMassBudget_nonneg _ _ hC) (booleanJetMassBudget_nonneg _ _ hW)) hs'

end Erdos3

end

end OAI
