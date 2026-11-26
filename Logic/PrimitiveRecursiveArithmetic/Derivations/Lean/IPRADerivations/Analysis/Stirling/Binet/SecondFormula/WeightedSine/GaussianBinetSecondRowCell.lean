import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Rectangles.GaussianBinetOscillatorySineRectangle
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.SineTransforms.GaussianBinetSineRealDampedPanels
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.Decay.GaussianBinetSecondDecayPointwise
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.SineTransforms.GaussianBinetSineFrozenPiTerm

/-!
# Shared exact cells of the arctangent and frozen sine quadratures

At positive frequency the actual arctangent sine cell, multiplied by
the frozen real decay, is the original complex damping times the
actual real-damped sine cell. The original zero-frequency column
keeps its explicit removable value.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondRowCell

open_ipra
open GaussianBinetOscillatoryColumns (damping)
open GaussianBinetOscillatorySineQuotient (quotient)
open GaussianBinetOscillatorySineRows (value_at_positive value_at_zero subst_endpoint)
open GaussianBinetSecondDecayPointwise (fullDecay frozenPiNumerator)
open GaussianBinetSineFrozenPiTerm (realNumerator realDenominator)
open GaussianEulerDecayMesh (observation subst_observation)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianStirlingConstant (piDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "RectBody" => GaussianBinetOscillatorySineRectangle.body
local notation "rectData" => GaussianBinetOscillatorySineRectangle.data

@[simp] private theorem subst_quotient {m : ℕ} (σ : Fin n → PTm m) (p a b C A B : PTm n) :
    Syn.subst σ (quotient p a b C A B) =
      quotient (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b)
        (Syn.subst σ C) (Syn.subst σ A) (Syn.subst σ B) := by simp [quotient,one]

private theorem symm_radius (p a b C D A B : PTm n) (e : Γ ⊢[PRAAx] C ≐ D) :
    Γ ⊢[PRAAx] quotient p a b C A B ≐ quotient p a b D A B := by
  have last {α : Type} (x₀ x₁ x₂ x₃ x₄ x₅ : α) : ![x₀,x₁,x₂,x₃,x₄,x₅] (5 : Fin 6) = x₅ := rfl
  simpa only [subst_quotient,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,last] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (quotient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![p,a,b,C,A,B]) (σ' := ![p,a,b,D,A,B])
      (fun i => by fin_cases i; exact .eqRefl p; exact .eqRefl a; exact .eqRefl b; exact e; exact .eqRefl A; exact .eqRefl B)

theorem decay_at (p k i a b : PTm n) : Γ ⊢[PRAAx]
    fullDecay p a b (frozenPiNumerator i k) (piDenominator k) ≐
      observation (realNumerator k i*a) (realDenominator k*b) p := by
  let H := frozenPiNumerator i k
  let J := piDenominator k
  have hn : Γ ⊢[PRAAx] two*(a*H) ≐ realNumerator k i*a := by
    unfold H frozenPiNumerator realNumerator GaussianBinetKernelImaginaryRatioRows.timeNumerator
    ipra_ring
  have hd : Γ ⊢[PRAAx] b*J ≐ realDenominator k*b := by
    unfold J realDenominator GaussianBinetKernelImaginaryRatioRows.timeDenominator
    ipra_ring
  simpa only [fullDecay,H,J,subst_observation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (observation (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![two*(a*H),b*J,p]) (σ' := ![realNumerator k i*a,realDenominator k*b,p])
      (fun j => by fin_cases j; exact hn; exact hd; exact .eqRefl p)

theorem positive_cell (j p k i X Y D sign a b R T L N : PTm n) (hj : Γ ⊢[PRAAx] le one j) :
    let S := D*L
    Γ ⊢[PRAAx]
      qmul (inst2 RectBody j (rectData p X Y D sign a b R T L N))
        (fullDecay (p+N) a b (frozenPiNumerator i k) (piDenominator k)) ≐
      qmul (damping p X Y D sign S j N R)
        (GaussianBinetSineRealDampedPanels.value (p+N) (realNumerator k i) (realDenominator k)
          (S*j) N a b S T) := by
  let S := D*L
  let d := damping p X Y D sign S j N R
  let v := quotient (p+N) a b (T*S) (S*j) N
  let w := observation (realNumerator k i*a) (realDenominator k*b) (p+N)
  have cell : Γ ⊢[PRAAx] inst2 RectBody j (rectData p X Y D sign a b R T L N) ≐ qmul d v :=
    (GaussianBinetOscillatorySineRectangle.row_at j p X Y D sign a b R T L N).eqTrans
      (value_at_positive j p X Y D sign a b R T L N hj)
  have angle := symm_radius (Γ := Γ) (p+N) a b (T*S) (S*T) (S*j) N (mul_comm T S)
  exact (qmul_congr cell (decay_at (p+N) k i a b)).eqTrans
    ((qmul_associative d v w).eqTrans
      (qmul_congr (.eqRefl d) ((qmul_commutative v w).eqTrans (qmul_congr (.eqRefl w) angle))))

theorem zero_cell (j p k i X Y D sign a b R T L N : PTm n) (hj : Γ ⊢[PRAAx] j ≐ zero) :
    Γ ⊢[PRAAx]
      qmul (inst2 RectBody j (rectData p X Y D sign a b R T L N))
        (fullDecay (p+N) a b (frozenPiNumerator i k) (piDenominator k)) ≐
      qmul (fraction a b) (observation (realNumerator k i*a) (realDenominator k*b) (p+N)) :=
  qmul_congr ((GaussianBinetOscillatorySineRectangle.row_at j p X Y D sign a b R T L N).eqTrans (value_at_zero j p X Y D sign a b R T L N hj))
    (decay_at (p+N) k i a b)

end LeanProofs.IPRA.Analysis.GaussianBinetSecondRowCell
