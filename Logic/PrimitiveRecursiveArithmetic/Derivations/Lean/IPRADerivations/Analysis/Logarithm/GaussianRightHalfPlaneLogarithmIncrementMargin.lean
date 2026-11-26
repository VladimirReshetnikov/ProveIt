import IPRADerivations.Analysis.Logarithm.GaussianRightHalfPlaneLogarithmIncrementBound

/-!
# Uniform small-step admission from a reciprocal real margin

The same explicit radius works across encoded points with a common
positive real margin and a common size bound. The smaller of the two
real numerators also supplies the squared radius comparison.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmIncrementMargin

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianLogGammaEulerResidualDomain (native)
open GaussianRightHalfPlaneArgument (wide wide_zero wide_one)
open GaussianRightHalfPlaneLogarithm (source)
open GaussianRightHalfPlaneLogarithmIncrementBound (input)
open GaussianRightHalfPlaneRadialContinuity (budget)
open GaussianRootAlgebra (sub)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (cancel_pos)
open RationalArithmetic (select select_zero select_one)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def lower (A a : PTm n) : PTm n := select (wide a A) A a

def smallStep (H K C D : PTm n) : Fm PTm n :=
  le (num 128*H*(C+one)*(K*K)) D

@[simp] theorem subst_lower {m : ℕ} (σ : Fin n → PTm m) (A a : PTm n) :
    Syn.subst σ (lower A a) = lower (Syn.subst σ A) (Syn.subst σ a) := by
  simp [lower,wide]

@[simp] theorem subst_smallStep {m : ℕ} (σ : Fin n → PTm m) (H K C D : PTm n) :
    (smallStep H K C D).subst σ = smallStep (Syn.subst σ H) (Syn.subst σ K) (Syn.subst σ C) (Syn.subst σ D) := by
  simp [smallStep,one]

theorem lower_bounds (A a D K : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (ha : Γ ⊢[PRAAx] le one a)
    (hl : Γ ⊢[PRAAx] le D (K*A)) (hr : Γ ⊢[PRAAx] le D (K*a)) :
    Γ ⊢[PRAAx] le one (lower A a) ⋏ (le (lower A a) A ⋏ (le (lower A a) a ⋏ le D (K*lower A a))) := by
  refine .orE (lt_or_le a A) ?_ ?_
  · have e : ((lt a A) :: Γ) ⊢[PRAAx] lower A a ≐ a :=
      select_one _ _ _ (wide_one a A Prf.hyp0)
    exact .andI (le_congr (.eqRefl _) e.eqSymm ha.wk)
      (.andI (le_congr e.eqSymm (.eqRefl _) (le_of_lt Prf.hyp0)) (.andI
        (le_congr e.eqSymm (.eqRefl _) (le_refl a)) (le_congr (.eqRefl _) (congrMul (.eqRefl K) e).eqSymm hr.wk)))
  · have e : ((le A a) :: Γ) ⊢[PRAAx] lower A a ≐ A :=
      select_zero _ _ _ (wide_zero a A Prf.hyp0)
    exact .andI (le_congr (.eqRefl _) e.eqSymm hA.wk)
      (.andI (le_congr e.eqSymm (.eqRefl _) (le_refl A)) (.andI
        (le_congr e.eqSymm (.eqRefl _) Prf.hyp0) (le_congr (.eqRefl _) (congrMul (.eqRefl K) e).eqSymm hl.wk)))

theorem admitted (A B neg a b sign D H K C : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (g : Γ ⊢[PRAAx] source a D sign)
    (hw : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (sub (native a b sign) (native A B neg)) H)
    (hK : Γ ⊢[PRAAx] le one K) (hA : Γ ⊢[PRAAx] le D (K*A)) (ha : Γ ⊢[PRAAx] le D (K*a))
    (hC : Γ ⊢[PRAAx] le (A+B+a+b) (C*D)) (hSmall : Γ ⊢[PRAAx] smallStep H K C D) :
    Γ ⊢[PRAAx] input A B neg a b sign D H (lower A a) (lower A a*lower A a) := by
  let J := lower A a
  have bounds := lower_bounds A a D K h.andE₁.andE₁ g.andE₁.andE₁ hA ha
  have hJ := bounds.andE₁
  have hjA := bounds.andE₂.andE₁
  have hja := bounds.andE₂.andE₂.andE₁
  have hD := bounds.andE₂.andE₂.andE₂
  have hKK := GaussianRationalHorner.positive_product _ _ hK hK
  have hK2 : Γ ⊢[PRAAx] le K (K*K) := le_congr (one_mul _) (.eqRefl _) (le_mul_mono hK (le_refl K))
  have hC1 : Γ ⊢[PRAAx] le one (C+one) := le_add_left one C
  have grow : Γ ⊢[PRAAx] le K ((C+one)*(K*K)) :=
    le_congr (one_mul K) (.eqRefl _) (le_mul_mono hC1 hK2)
  have angleBudget : Γ ⊢[PRAAx] le (K*(num 128*H)) (num 128*H*(C+one)*(K*K)) :=
    le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono (le_refl (num 128*H)) grow)
  have costAngle : Γ ⊢[PRAAx] le (K*(num 128*H)) D := le_trans angleBudget hSmall
  have angle : Γ ⊢[PRAAx] le (num 128*H) J := cancel_pos hK (le_trans costAngle hD)
  have costRad : Γ ⊢[PRAAx] le (num 16*H*C*(K*K)) D := by
    apply le_trans _ hSmall
    ipra_le 112*𝔞(H)*𝔞(C)*𝔞(K)^2+128*𝔞(H)*𝔞(K)^2
  have clear : Γ ⊢[PRAAx] le ((K*K)*(num 16*H*(C*D))) ((K*K)*(J*J)) := by
    exact le_congr (by ipra_ring) (by ipra_ring)
      (le_trans (le_mul_mono costRad (le_refl D)) (le_mul_mono hD hD))
  have radialBudget : Γ ⊢[PRAAx] le (num 16*H*(A+B+a+b)) (num 16*H*(C*D)) :=
    le_mul_mono (le_refl (num 16*H)) hC
  have rad : Γ ⊢[PRAAx] le (num 16*budget A B a b H) (J*J) :=
    le_congr (by unfold budget; ipra_ring) (.eqRefl _) (le_trans radialBudget (cancel_pos hKK clear))
  have l : Γ ⊢[PRAAx] le (J*J) (GaussianRightHalfPlaneRadialLogarithm.normNum A B) :=
    le_trans (le_mul_mono hjA hjA) (le_add_right _ _)
  have r : Γ ⊢[PRAAx] le (J*J) (GaussianRightHalfPlaneRadialLogarithm.normNum a b) :=
    le_trans (le_mul_mono hja hja) (le_add_right _ _)
  exact .andI (.andI h (.andI g (.andI hw (.andI (GaussianRationalHorner.positive_product _ _ hJ hJ) (.andI l r)))))
    (.andI hJ (.andI hjA (.andI hja (.andI angle rad))))

theorem actual_uniform_right_half_plane_logarithm_increment_admission_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      ((source (var 0) (var 6) (var 2) ⋏ (source (var 3) (var 6) (var 5) ⋏
        (ComplexLogarithmRemainder.bounded (sub (native (var 3) (var 4) (var 5))
          (native (var 0) (var 1) (var 2))) (var 7) ⋏
          (le one (var 8) ⋏ (le (var 6) (var 8*var 0) ⋏ (le (var 6) (var 8*var 3) ⋏
            (le (var 0+var 1+var 3+var 4) (var 9*var 6) ⋏ smallStep (var 7) (var 8) (var 9) (var 6)))))))) ⟶
        input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
          (lower (var 0) (var 3)) (lower (var 0) (var 3)*lower (var 0) (var 3))) :=
  closeUniv 10 (.impI (admitted _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmIncrementMargin
