import IPRADerivations.Analysis.Trigonometry.Sinc.GaussianScalarSincTaylor
import IPRADerivations.Analysis.Exponential.Polynomials.Coefficients.GaussianFiniteExponentialWeightedNorm
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.Coefficients.GaussianGammaRecurrenceWeightName
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerDifference

/-!
# Finite sinc bounds on the unit disk

The factorial weight for K tail rows is (2K+1)!. The tail is bounded
by half the squared argument radius times one minus the reciprocal of
this weight. The next weight multiplier pays for the next literal row
and preserves the reserve.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianScalarSincTaylorBounds

open_ipra
open GaussianScalarSincTaylor (sincTerm sincTaylor sincTail sinc_tail_zero sinc_tail_succ
  sinc_head_tail sinc_difference_tail)
open GaussianRationalPolynomialExponential (inverseFactorial factorial_positive)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (qone qone_bounded power powerF bounded_power bounded_product bound_congr)
open GaussianRationalPowerDifference (bounded_sum_same)
open GaussianPolynomialPerturbation (one_power power_positive)
open Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private def degree (k : PTm n) : PTm n := succ (two*k)
private def weight (k : PTm n) : PTm n := fact (degree k)
private def multiplier (k : PTm n) : PTm n := succ (degree k)*succ (succ (degree k))

private theorem weight_zero : Γ ⊢[PRAAx] weight (zero : PTm n) ≐ one :=
  (congrAp2 factF (congrSucc (mul_zero two)) (.eqRefl zero)).eqTrans
    ((fact_succ zero zero).eqTrans ((congrMul (fact_zero zero) (.eqRefl _)).eqTrans (one_mul _)))

private theorem weight_succ (k : PTm n) : Γ ⊢[PRAAx] weight (succ k) ≐ weight k*multiplier k := by
  have h : Γ ⊢[PRAAx] degree (succ k) ≐ succ (succ (degree k)) := by
    unfold degree
    ipra_ring
  exact (congrAp2 factF h (.eqRefl zero)).eqTrans
    ((fact_succ (succ (degree k)) zero).eqTrans
      ((congrMul (fact_succ (degree k) zero) (.eqRefl _)).eqTrans (by unfold weight multiplier; ipra_ring)))

private theorem weight_positive (k : PTm n) : Γ ⊢[PRAAx] le one (weight k) :=
  factorial_positive _

private theorem multiplier_lower (k : PTm n) : Γ ⊢[PRAAx] le (num 3) (multiplier k) :=
  le_of_eq_add (d := (two*k)*(two*k)+num 10*k+num 3) (by unfold multiplier degree; ipra_ring)

private theorem reserve_step (k : PTm n) :
    Γ ⊢[PRAAx] le (monus (weight k) one*multiplier k+two) (monus (weight (succ k)) one) := by
  refine le_of_eq_add (d := monus (multiplier k) (num 3)) ?_
  have a := natEq (eq_add_of_le (weight_positive (Γ := Γ) k))
  have b := natEq (eq_add_of_le (weight_positive (Γ := Γ) (succ k)))
  have w := natEq (weight_succ (Γ := Γ) k)
  have m := natEq (eq_add_of_le (multiplier_lower (Γ := Γ) k))
  apply deriveNat
  ipra_simps
  linear_combination 𝔞(multiplier k)*a-b+w+m

private alias square_power := Common.pw_two

private theorem even_power_bound (z A B k : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B) (hz : Γ ⊢[PRAAx] bounded z A B) :
    Γ ⊢[PRAAx] bounded (power z (two*succ k)) (A*A) (B*B) := by
  let d := two*k
  have hz₁ : Γ ⊢[PRAAx] bounded z one one :=
    bounded_radius_mono _ _ _ _ _ hB (le_refl one) (le_congr (by ipra_ring) (by ipra_ring) hAB) hz
  have small := bound_congr (.eqRefl _) (one_power d) (one_power d)
    (bounded_power z one one d (le_refl one) hz₁)
  have raw := bounded_product _ _ _ _ _ _ (power_positive B two hB) (le_refl one)
    (bounded_power z A B two hB hz) small
  have exp : Γ ⊢[PRAAx] two+d ≐ two*succ k := by
    dsimp only [d]
    ipra_ring
  have lhs := (GaussianRationalPowerAlgebra.power_add (Γ := Γ) z two d).eqSymm.eqTrans
    (congrAp2 powerF exp (.eqRefl z))
  exact bound_congr lhs
    ((by ipra_ring : Γ ⊢[PRAAx] pw A two*one ≐ pw A two).eqTrans (square_power A))
    ((by ipra_ring : Γ ⊢[PRAAx] pw B two*one ≐ pw B two).eqTrans (square_power B)) raw

private theorem term_bound (z A B k : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B) (hz : Γ ⊢[PRAAx] bounded z A B) :
    Γ ⊢[PRAAx] bounded (sincTerm z (succ k)) (A*A) ((B*B)*weight (succ k)) := by
  let d := degree (succ k)
  let F := weight (succ k)
  have hF := weight_positive (Γ := Γ) (succ k)
  have hb := positive_product _ _ hB hB
  have inv : Γ ⊢[PRAAx] bounded (inverseFactorial d) one F :=
    GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ hF
      (RationalArgmin.rationalLE_congr (GaussianFiniteExponentialWeightedNorm.inverse_factorial_norm d).eqSymm
        (.eqRefl _) (RationalArgmin.reflexive _))
  have raw := bounded_product _ _ _ _ _ _ (le_refl one) (positive_product _ _ hF hb)
    (GaussianGammaRecurrenceWeightName.parity_bound (succ k))
    (bounded_product _ _ _ _ _ _ hF hb inv (even_power_bound z A B k hB hAB hz))
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) raw

private def tailBudget (z A B k : PTm n) : Fm PTm n :=
  bounded (sincTail z k) ((A*A)*monus (weight k) one) (two*(B*B)*weight k)

@[simp] private theorem subst_tailBudget {m : ℕ} (σ : Fin n → PTm m) (z A B k : PTm n) :
    (tailBudget z A B k).subst σ = tailBudget (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by
  simp [tailBudget,weight,degree,Products.fact]

private theorem tail_budget_step (z A B k : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B) (hz : Γ ⊢[PRAAx] bounded z A B)
    (old : Γ ⊢[PRAAx] tailBudget z A B k) : Γ ⊢[PRAAx] tailBudget z A B (succ k) := by
  let F := weight k
  let G := weight (succ k)
  let s := multiplier k
  let D := two*(B*B)*F
  let E := two*(B*B)*G
  let T := (A*A)*(monus F one*s)
  have hb := positive_product _ _ hB hB
  have htwo : Γ ⊢[PRAAx] le one two := le_succ_self one
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ htwo hb) (weight_positive k)
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (positive_product _ _ htwo hb) (weight_positive (succ k))
  have e : Γ ⊢[PRAAx] E ≐ D*s :=
    (congrMul (.eqRefl (two*(B*B))) (weight_succ k)).eqTrans (by dsimp only [D]; ipra_ring)
  have scaled : Γ ⊢[PRAAx] bounded (sincTail z k) T E := by
    have en : Γ ⊢[PRAAx] ((A*A)*monus F one)*E ≐ T*D :=
      (congrMul (.eqRefl _) e).eqTrans (by dsimp only [T]; ipra_ring)
    exact bounded_radius_mono _ _ _ _ _ hD hE
      (le_congr en.eqSymm (.eqRefl _) (le_refl _)) old
  have row : Γ ⊢[PRAAx] bounded (sincTerm z (succ k)) (two*(A*A)) E :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hb (weight_positive (succ k))) hE
      (le_of_eq_add (d := zero) (by dsimp only [E]; ipra_ring)) (term_bound z A B k hB hAB hz)
  have sum := bounded_sum_same _ _ _ _ _ hE scaled row
  have pay : Γ ⊢[PRAAx] le (T+two*(A*A)) ((A*A)*monus G one) :=
    le_congr (by dsimp only [T]; ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (A*A)) (reserve_step k))
  exact bound_congr (sinc_tail_succ z k).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ hE hE (le_mul_mono pay (le_refl E)) sum)

private theorem tail_budget (z A B K : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B) (hz : Γ ⊢[PRAAx] bounded z A B) :
    Γ ⊢[PRAAx] tailBudget z A B K := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have ht : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift A) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hAB.shift
  have hu : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift z) (Syn.shift A) (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hz.shift
  have all : Γ ⊢[PRAAx] .all (tailBudget (Syn.shift z) (Syn.shift A) (Syn.shift B) (var 0)) := by
    ipra_qfind (le_QF _ _) [subst_tailBudget]
    · have hD : Γ ⊢[PRAAx] le one (two*(B*B)*weight zero) :=
        positive_product _ _ (positive_product _ _ (le_succ_self one) (positive_product _ _ hB hB)) (weight_positive zero)
      have e : Γ ⊢[PRAAx] (A*A)*monus (weight zero) one ≐ zero :=
        (congrMul (.eqRefl _) ((congrMonus weight_zero (.eqRefl one)).eqTrans (monus_self one))).eqTrans (mul_zero _)
      exact bound_congr (sinc_tail_zero z).eqSymm e.eqSymm (.eqRefl _)
        (GaussianMonicResidualRadius.zero_bounded _ _ hD)
    · exact tail_budget_step _ _ _ _ hs.wk ht.wk hu.wk Prf.hyp0
  simpa only [subst_tailBudget,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE K

theorem sinc_tail_bound (z A B K : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B) (hz : Γ ⊢[PRAAx] bounded z A B) :
    Γ ⊢[PRAAx] bounded (sincTail z K) (A*A) (two*(B*B)) := by
  let F := weight K
  let D := two*(B*B)
  have hd : Γ ⊢[PRAAx] le one D :=
    positive_product _ _ (le_succ_self one) (positive_product _ _ hB hB)
  have hD : Γ ⊢[PRAAx] le one (D*F) := positive_product _ _ hd (weight_positive K)
  have cmp := le_mul_mono (le_refl ((A*A)*D)) (GaussianMonicResidualRadius.monus_le_left (Γ := Γ) F one)
  exact bounded_radius_mono _ _ _ _ _ hD hd
    (le_congr (by dsimp only [F,D]; ipra_ring) (by dsimp only [F,D]; ipra_ring) cmp)
    (tail_budget z A B K hB hAB hz)

theorem small_argument_bound (z A B K : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B) (hz : Γ ⊢[PRAAx] bounded z A B) :
    Γ ⊢[PRAAx] distanceBounded (sincTaylor z (succ K)) qone (A*A) (two*(B*B)) :=
  bound_congr (sinc_difference_tail z K).eqSymm (.eqRefl _) (.eqRefl _) (sinc_tail_bound z A B K hB hAB hz)

theorem unit_disk_sinc_bound (z K : PTm n) (hz : Γ ⊢[PRAAx] bounded z one one) :
    Γ ⊢[PRAAx] bounded (sincTaylor z (succ K)) two one := by
  have hd : Γ ⊢[PRAAx] le one (two*(one*one)) := le_of_eq_add (d := one) (by ipra_ring)
  have tail := bounded_radius_mono _ _ _ one one hd (le_refl one) (by ipra_le 1)
    (sinc_tail_bound z one one K (le_refl one) (le_refl one) hz)
  exact bound_congr (sinc_head_tail z K).eqSymm (by ipra_ring) (.eqRefl _)
    (bounded_sum_same _ _ _ _ _ (le_refl one) qone_bounded tail)

theorem actual_finite_sinc_small_argument_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (((le one (var 2)) ⋏ le (var 1) (var 2)) ⟶ bounded (var 0) (var 1) (var 2) ⟶
      distanceBounded (sincTaylor (var 0) (succ (var 3))) qone ((var 1)*(var 1)) (two*(var 2*var 2))) :=
  closeUniv 4 (.impI (.impI (small_argument_bound _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

theorem actual_finite_sinc_unit_disk_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (bounded (var 0) one one ⟶ bounded (sincTaylor (var 0) (succ (var 1))) two one) :=
  closeUniv 2 (.impI (unit_disk_sinc_bound _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianScalarSincTaylorBounds
