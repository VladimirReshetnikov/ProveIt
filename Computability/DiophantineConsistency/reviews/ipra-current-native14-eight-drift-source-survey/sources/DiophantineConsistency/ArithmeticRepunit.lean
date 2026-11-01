import DiophantineConsistency.ArithmeticUnaryRecursion
import DiophantineConsistency.ArithmeticBinaryPopulation

/-! The represented binary repunit `rep d N = Σ_{i<N} 2^{d·i}` at arbitrary
internal width and length, with `(2^d-1)·rep d N + 1 = 2^{d·N}`, its uniqueness
as the solution of that identity, and the repeated-block population law
`population (a·rep d N) = N·population a` for `a < 2^d`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticRepunit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out d. out=0”
def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index d. ∃ p, !expDef p d ∧ out=previous*p+1”
def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef

noncomputable def construction : PR.Construction V blueprint where
  zero _ := 0
  succ parameters _ previous := previous*Exp.exp (parameters 0)+1
  zero_defined := .mk fun e => by simp [blueprint,zeroDef]
  succ_defined := .mk fun e => by simp [blueprint,succDef]

/-- `rep d N = Σ_{i<N} 2^{d·i}`, by Horner's rule. -/
noncomputable def rep (d N : V) : V := construction.result ![d] N
def repResultDef : 𝚺₁.Semisentence 3 := blueprint.resultDef
def repDef : 𝚺₁.Semisentence 3 := .mkSigma “out d N. !repResultDef out N d”

private theorem rep_result_defined :
    𝚺₁-Function₂[V] (fun N d => rep d N) via repResultDef :=
  ArithmeticUnaryRecursion.result_defined blueprint construction

instance rep_defined : 𝚺₁-Function₂[V] rep via repDef := .mk fun e => by
  have h := (rep_result_defined (V:=V)).df ![e 0, e 2, e 1]
  simp [repDef, h]
instance rep_definable : 𝚺₁-Function₂[V] rep := rep_defined.to_definable

@[simp] theorem rep_zero (d : V) : rep d 0 = 0 := by simp [rep,construction]
theorem rep_succ (d N : V) : rep d (N+1) = rep d N*Exp.exp d+1 := by
  simp [rep,PR.Construction.result_succ,construction]

/-- **The repunit identity**, at every internal width and length. -/
theorem repunit_identity (d N : V) : (Exp.exp d-1)*rep d N+1 = Exp.exp (d*N) := by
  obtain ⟨f, hf⟩ : ∃ f, Exp.exp d = f + 1 :=
    ⟨Exp.exp d - 1, (tsub_add_cancel_of_le (one_le_exp d)).symm⟩
  induction N using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ N ih =>
    rw [rep_succ, mul_add d N 1, mul_one, exp_add, ← ih, hf, add_tsub_cancel_right]
    ring

/-- The repunit is the unique solution of its identity when `d > 0`. -/
theorem eq_rep_of_identity {d N J : V} (hd : 0 < d)
    (h : (Exp.exp d-1)*J+1 = Exp.exp (d*N)) : J = rep d N := by
  have hpos : 0 < Exp.exp d - 1 := by
    have : 2 ≤ Exp.exp d := by
      have := exp_monotone_le.mpr (show (1:V) ≤ d from pos_iff_one_le.mp hd)
      simpa using this
    exact tsub_pos_of_lt (lt_of_lt_of_le one_lt_two this)
  have h2 := repunit_identity d N
  rw [← h2] at h
  exact mul_left_cancel₀ (ne_of_gt hpos) (add_right_cancel h)

/-- **Repeated blocks**: the population of a block repeated `N` times. -/
theorem population_repeat (d a N : V) (ha : a < Exp.exp d) :
    population (a*rep d N) = N*population a := by
  induction N using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ N ih =>
    rw [rep_succ, mul_add, mul_one, ← mul_assoc, concatenate _ _ _ ha, ih]
    ring

end DiophantineConsistency.ArithmeticRepunit
