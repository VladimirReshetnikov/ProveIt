import IPRADerivations.Analysis.Trigonometry.Arctangent.Cayley.GaussianArctangentCayleyTrig
import IPRADerivations.Analysis.RationalArithmetic.Grids.RationalCubeMidpoint

/-!
# Separation of squared Cayley sines on a common mesh

The cleared difference factors into the two index differences,
the sum of the indices, and the two factors from the common mesh.
The estimate uses only three rational margins on the indices.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianArctangentCayleySquareGap

open_ipra
open ComplexLogarithmRemainder (eval_re_code)
open GaussianArctangentCayleyValues (denominator denominator_positive)
open GaussianArctangentCayleyTrig (sineCode sinePoint)
open GaussianRationalHorner (ofGaussian_represents positive_product scalar_congr qmul qmul_represents)
open GaussianRationalMetric (comparison_of_cleared)
open GaussianRootAlgebra (re_mul)
open RationalArithmetic (add)
open RationalArgmin (rationalLE)
open RationalCubeMidpoint (fraction fraction_represents)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def sqNumerator (M i : PTm n) : PTm n := (two*M*i)*(two*M*i)
def sqDenominator (M i : PTm n) : PTm n := denominator M i*denominator M i
def squareValue (M i : PTm n) : PTm n := fstT (qmul (sinePoint M i) (sinePoint M i))
def clearedDifference (M i j : PTm n) : PTm n :=
  num 4*(M*M)*(monus j i)*(i+j)*(monus (M*M) (i*j))*(M*M+i*j)
def separationDenominator (T : PTm n) : PTm n := num 4*T*T*T

theorem exact_gap (M i j : PTm n) (hij : Γ ⊢[PRAAx] le i j) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] sqNumerator M i*sqDenominator M j+clearedDifference M i j ≐
      sqNumerator M j*sqDenominator M i := by
  have hab := le_mul_mono (le_trans hij hj) hj
  have gap := natEq (eq_add_of_le hij)
  have comp := natEq (eq_add_of_le hab)
  simp only [IPRA.Q.mk_add,map_add] at gap comp
  apply deriveNat
  simp only [sqNumerator,sqDenominator,clearedDifference,denominator]
  ipra_simps
  calc
    _ = 4*𝔞 M^2*(𝔞 (monus j i)*(𝔞 i+𝔞 j)*(𝔞 (monus (M*M) (i*j))*(𝔞 M^2+𝔞 i*𝔞 j))) +
          (2*𝔞 M*𝔞 i)^2*(𝔞 M^2+𝔞 j^2)^2 := by ring
    _ = 4*𝔞 M^2*((𝔞 j-𝔞 i)*(𝔞 i+𝔞 j)*(𝔞 M^2-𝔞 i*𝔞 j)*(𝔞 M^2+𝔞 i*𝔞 j)) +
          (2*𝔞 M*𝔞 i)^2*(𝔞 M^2+𝔞 j^2)^2 := by
      have d : 𝔞 (monus j i) = 𝔞 j-𝔞 i := by linear_combination -gap
      have e : 𝔞 (monus (M*M) (i*j)) = 𝔞 M^2-𝔞 i*𝔞 j := by linear_combination -comp
      rw [d,e]
      ring
    _ = _ := by ring

private theorem denominator_bound (M i : PTm n) (hi : Γ ⊢[PRAAx] le i M) :
    Γ ⊢[PRAAx] le (sqDenominator M i) ((two*(M*M))*(two*(M*M))) := by
  have b : Γ ⊢[PRAAx] le (denominator M i) (two*(M*M)) :=
    le_congr (add_comm _ _) (by ipra_ring) (add_le_add_right (M*M) (le_mul_mono hi hi))
  exact le_mul_mono b b

private theorem complement_bound (M i j : PTm n) (hi : Γ ⊢[PRAAx] le i M) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] le (M*monus M j) (monus (M*M) (i*j)) := by
  have hab := le_mul_mono hi hj
  have ha := natEq (eq_add_of_le hi)
  have hb := natEq (eq_add_of_le hj)
  have hc := natEq (eq_add_of_le hab)
  apply le_of_eq_add (d := monus M i*j)
  apply deriveNat
  ipra_simps
  linear_combination -hc + 𝔞 M*hb + 𝔞 j*ha

theorem cleared_gap (M i j T : PTm n) (hij : Γ ⊢[PRAAx] le i j) (hj : Γ ⊢[PRAAx] le j M)
    (hstart : Γ ⊢[PRAAx] le M (T*i)) (hgap : Γ ⊢[PRAAx] le M (T*monus j i))
    (hend : Γ ⊢[PRAAx] le M (T*monus M j)) :
    Γ ⊢[PRAAx] le
      (sqDenominator M i*sqDenominator M j+separationDenominator T*(sqNumerator M i*sqDenominator M j))
      (separationDenominator T*(sqNumerator M j*sqDenominator M i)) := by
  have hi := le_trans hij hj
  have p : Γ ⊢[PRAAx] le M (T*(i+j)) :=
    le_trans hstart (le_mul_mono (le_refl T) (le_add_right i j))
  have q : Γ ⊢[PRAAx] le (M*M) (T*monus (M*M) (i*j)) :=
    le_trans (le_mul_mono (le_refl M) hend)
      (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl T) (complement_bound M i j hi hj)))
  have s := le_mul_mono (le_mul_mono (le_mul_mono hgap p) q) (le_add_right (M*M) (i*j))
  have s' := le_mul_mono (le_refl (num 16*(M*M))) s
  have lower : Γ ⊢[PRAAx] le (((two*(M*M))*(two*(M*M)))*((two*(M*M))*(two*(M*M))))
      (separationDenominator T*clearedDifference M i j) :=
    le_congr (by ipra_ring) (by unfold separationDenominator clearedDifference; ipra_ring) s'
  have h := le_trans (le_mul_mono (denominator_bound M i hi) (denominator_bound M j hj)) lower
  exact le_congr (.eqRefl _) (by
    refine (by ipra_ring : Γ ⊢[PRAAx]
      separationDenominator T*clearedDifference M i j+separationDenominator T*(sqNumerator M i*sqDenominator M j) ≐
      separationDenominator T*(sqNumerator M i*sqDenominator M j+clearedDifference M i j)).eqTrans
      (congrMul (.eqRefl _) (exact_gap M i j hij hj)))
    (add_le_add_right _ h)

theorem square_represents (M i : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (squareValue M i) (ZT.ofNat (sqNumerator M i)) (sqDenominator M i) := by
  have h := denominator_positive M i hM
  have rep := ofGaussian_represents (sineCode M i) (denominator M i) h
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) (qmul_represents _ _ _ _ _ _ h h rep rep).andE₁
  apply ZT.derive
  simp only [re_mul,sineCode,eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat,sqNumerator]
  ipra_simps
  ring

theorem rational_gap (M i j T : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hT : Γ ⊢[PRAAx] le one T)
    (hij : Γ ⊢[PRAAx] le i j) (hj : Γ ⊢[PRAAx] le j M)
    (hstart : Γ ⊢[PRAAx] le M (T*i)) (hgap : Γ ⊢[PRAAx] le M (T*monus j i))
    (hend : Γ ⊢[PRAAx] le M (T*monus M j)) :
    Γ ⊢[PRAAx] rationalLE (add (squareValue M i) (fraction one (separationDenominator T))) (squareValue M j) := by
  let E := sqDenominator M i
  let F := sqDenominator M j
  let D := separationDenominator T
  have he : Γ ⊢[PRAAx] le one E := positive_product _ _ (denominator_positive M i hM) (denominator_positive M i hM)
  have hf : Γ ⊢[PRAAx] le one F := positive_product _ _ (denominator_positive M j hM) (denominator_positive M j hM)
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ (positive_product _ _
    (le_of_eq_add (d := num 3) (by ipra_ring)) hT) hT) hT
  have rep : Γ ⊢[PRAAx] RationalArithmetic.represents (add (squareValue M i) (fraction one D))
      (ZT.ofNat (sqNumerator M i*D+E)) (E*D) := by
    apply scalar_congr (.eqRefl _) ?_ (.eqRefl _)
      (RationalRepresentations.represents_add _ _ _ _ _ _ (square_represents M i hM) (fraction_represents one D hd))
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
    ipra_simps
    ring
  exact comparison_of_cleared _ _ _ _ _ _ (positive_product _ _ he hd) hf rep (square_represents M j hM)
    (le_congr (by ipra_ring) (by ipra_ring) (cleared_gap M i j T hij hj hstart hgap hend))

def marginSource (M i j T : PTm n) : Fm PTm n :=
  (le one M ⋏ le one T) ⋏ (le i j ⋏ le j M) ⋏
    (le M (T*i) ⋏ le M (T*monus j i) ⋏ le M (T*monus M j))

theorem actual_Cayley_squared_sine_gap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (marginSource (var 0) (var 1) (var 2) (var 3) ⟶
      rationalLE (add (squareValue (var 0) (var 1)) (fraction one (separationDenominator (var 3))))
        (squareValue (var 0) (var 2))) := by
  refine closeUniv 4 (.impI ?_)
  let H : Fm PTm 4 := marginSource (var 0) (var 1) (var 2) (var 3)
  have h : [H] ⊢[PRAAx] H := .hyp0
  exact rational_gap _ _ _ _ h.andE₁.andE₁ h.andE₁.andE₂ h.andE₂.andE₁.andE₁ h.andE₂.andE₁.andE₂
    h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂

end LeanProofs.IPRA.Analysis.GaussianArctangentCayleySquareGap
