import IPRADerivations.Analysis.Inequalities.NonnegativeArithmetic.RationalNonnegativePowerOrder

/-!
# A finite geometric-tail potential

For y=K-1 the actual numerator CK y^j bounds the remaining geometric
tail at stage j. Once twice that numerator fits below K^j it continues
to fit at every later internal stage. The complementary natural gap
gives a local multiplication inequality; it will telescope along the
actual finite-product recursor. No infinite product or global product
bound is a premise. C may be zero and K may be one.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeometricProductTail

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def tailNumerator (C K j : PTm n) : PTm n := C*K*pw (pred K) j
def gap (C K j : PTm n) : PTm n := monus (pw K j) (tailNumerator C K j)
def small (C K j : PTm n) : Fm PTm n := le (two*tailNumerator C K j) (pw K j)

ipra_subst tailNumerator
ipra_subst gap
ipra_subst small

theorem small_mono (C K T j : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (hT : Γ ⊢[PRAAx] small C K T) (hTj : Γ ⊢[PRAAx] le T j) : Γ ⊢[PRAAx] small C K j := by
  have lower : Γ ⊢[PRAAx] le (pred K) K :=
    le_congr (.eqRefl _) (RationalIntegerNormalization.positive_form hK).eqSymm (le_succ_self _)
  have crossed := RationalNonnegativePowerOrder.exponent_cross_antitone (pred K) K T j lower hTj
  have first : Γ ⊢[PRAAx] le (pw K T*(two*tailNumerator C K j))
      ((two*tailNumerator C K T)*pw K j) :=
    le_congr (by unfold tailNumerator; ipra_ring) (by unfold tailNumerator; ipra_ring)
      (mul_le_mul_right (two*C*K) crossed)
  have second := mul_le_mul_right (pw K j) hT
  exact RationalValueBounds.positive_cancel (RationalNonnegativePowers.denominator_positive K T hK)
    (le_trans first second)

theorem numerator_le (C K j : PTm n) (h : Γ ⊢[PRAAx] small C K j) : Γ ⊢[PRAAx]
    le (tailNumerator C K j) (pw K j) :=
  le_trans (le_of_eq_add (d := tailNumerator C K j) (by ipra_ring)) h

theorem gap_decomposition (C K j : PTm n) (h : Γ ⊢[PRAAx] small C K j) : Γ ⊢[PRAAx]
    pw K j ≐ tailNumerator C K j+gap C K j := eq_add_of_le (numerator_le C K j h)

theorem gap_le (C K j : PTm n) (h : Γ ⊢[PRAAx] small C K j) : Γ ⊢[PRAAx]
    le (gap C K j) (pw K j) :=
  le_of_eq_add (d := tailNumerator C K j) ((gap_decomposition C K j h).eqTrans (add_comm _ _))

theorem twice_gap (C K j : PTm n) (h : Γ ⊢[PRAAx] small C K j) : Γ ⊢[PRAAx]
    le (pw K j) (two*gap C K j) := by
  have bound : Γ ⊢[PRAAx] le (two*tailNumerator C K j) (tailNumerator C K j+gap C K j) :=
    le_congr (.eqRefl _) (gap_decomposition C K j h) h
  have half : Γ ⊢[PRAAx] le (tailNumerator C K j) (gap C K j) :=
    le_of_add_le_add_right (le_congr (by ipra_ring) (add_comm _ _) bound)
  exact le_congr (gap_decomposition C K j h).eqSymm (by ipra_ring)
    (add_le_add_right (gap C K j) half)

theorem tail_numerator_succ (C K j : PTm n) : Γ ⊢[PRAAx]
    tailNumerator C K (succ j) ≐ tailNumerator C K j*pred K := by
  have p := natEq (pw_succ (Γ := Γ) (pred K) j)
  apply deriveNat
  simp only [tailNumerator]
  ipra_simps
  rw [p]
  ring

/-- The extra square is nonnegative, including a zero tail numerator. -/
theorem gap_identity (C K j : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] small C K j) : Γ ⊢[PRAAx]
    pw K j*gap C K (succ j) ≐
      K*(pw K j+C*pw (pred K) j)*gap C K j+tailNumerator C K j*tailNumerator C K j := by
  have next := small_mono C K j (succ j) hK h (le_succ_self j)
  ipra_lc [tailNumerator] -𝔞 (pw K j)*natEq (gap_decomposition C K (succ j) next) +
    (𝔞 K*𝔞 (pw K j)+𝔞 C*𝔞 K*𝔞 (pw (pred K) j))*natEq (gap_decomposition C K j h) +
    (𝔞 (pw K j)*𝔞 C*𝔞 K*𝔞 (pw (pred K) j))*natEq (RationalIntegerNormalization.positive_form hK) +
    𝔞 (pw K j)*natEq (pw_succ (Γ := Γ) K j) - 𝔞 (pw K j)*natEq (tail_numerator_succ (Γ := Γ) C K j)

theorem gap_product_le (C K j : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] small C K j) : Γ ⊢[PRAAx]
    le (K*(pw K j+C*pw (pred K) j)*gap C K j) (pw K j*gap C K (succ j)) :=
  le_of_eq_add (gap_identity C K j hK h)

theorem geometric_tail_persists_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ small (var 0) (var 1) (var 2) ⟶ le (var 2) (var 3) ⟶
      small (var 0) (var 1) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (small_mono _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem complementary_gap_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ small (var 0) (var 1) (var 2) ⟶
      pw (var 1) (var 2)*gap (var 0) (var 1) (succ (var 2)) ≐
        var 1*(pw (var 1) (var 2)+var 0*pw (pred (var 1)) (var 2))*gap (var 0) (var 1) (var 2)+
          tailNumerator (var 0) (var 1) (var 2)*tailNumerator (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (gap_identity _ _ _ Prf.hyp1 Prf.hyp0)))
theorem complementary_gap_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ small (var 0) (var 1) (var 2) ⟶
      le (var 1*(pw (var 1) (var 2)+var 0*pw (pred (var 1)) (var 2))*gap (var 0) (var 1) (var 2))
        (pw (var 1) (var 2)*gap (var 0) (var 1) (succ (var 2)))) :=
  closeUniv 3 (.impI (.impI (gap_product_le _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGeometricProductTail
