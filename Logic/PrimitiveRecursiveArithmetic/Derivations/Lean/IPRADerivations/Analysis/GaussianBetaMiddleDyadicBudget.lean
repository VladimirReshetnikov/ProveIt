import IPRADerivations.Analysis.GaussianBetaUpperGridMonomialComparison
import IPRADerivations.Analysis.GaussianMonomialDecayBudget
import IPRADerivations.Analysis.GaussianBetaIntegralThreeSplit

/-!
# Upward stable finite budgets for the original beta/Euler middle grid

The two requested observation queries remain independent. A common later
auxiliary query and any sufficiently fine common mesh retain the exact
factorial cap divided by the original beta degree. Zero middle width is
included through its literal zero quadrature.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaMiddleDyadicBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (quadrature)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianMonomialDecayQuadrature (cap)
open GaussianBetaRowMonomialReference (comparisonNumerator comparisonDenominator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def source (z R B C E N : PTm n) : Fm PTm n :=
  GaussianEulerUpperPowerCoefficients.source z R B ⋏
    (le one E ⋏ (le one N ⋏ le (two*(E+C)) (E*N)))

def minimumMesh (j C R : PTm n) : PTm n :=
  GaussianMonomialDecayBudget.minimumMesh (succ j) C (R+two)
def minimumAuxiliary (j C N R : PTm n) : PTm n :=
  GaussianMonomialDecayBudget.minimumPrecision (succ j) C (R+two)+
    GaussianMonomialDecayBudget.minimumReference (succ j) (R+two)+
    GaussianFastValueCut.exponent (num 10*pw N (R+two)) j

def numerator (p v j R C E N : PTm n) : PTm n :=
  cap (R+two)*E*unit p*unit v*unit j+
    C*N*(unit p+unit v)*unit j+E*N*unit p*unit v
def denominator (p v j E N : PTm n) : PTm n := E*N*unit p*unit v*unit j

theorem denominator_positive (p v j E N : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le one (denominator p v j E N) :=
  positive_product _ _ (positive_product _ _ (positive_product _ _
    (positive_product _ _ hE hN) (unit_positive p)) (unit_positive v)) (unit_positive j)

theorem auxiliary_threshold (j w C N R : PTm n)
    (h : Γ ⊢[PRAAx] le (minimumAuxiliary j C N R) w) : Γ ⊢[PRAAx]
    le (GaussianMonomialDecayBudget.minimumPrecision (succ j) C (R+two)) w ⋏
      le (GaussianMonomialDecayBudget.minimumReference (succ j) (R+two)) w ⋏
      le (num 10*pw N (R+two)*unit j) (unit w) := by
  have first : Γ ⊢[PRAAx] le (GaussianMonomialDecayBudget.minimumPrecision (succ j) C (R+two)) (minimumAuxiliary j C N R) :=
    le_of_eq_add (d := GaussianMonomialDecayBudget.minimumReference (succ j) (R+two)+
      GaussianFastValueCut.exponent (num 10*pw N (R+two)) j) (by unfold minimumAuxiliary; ipra_ring)
  have second : Γ ⊢[PRAAx] le (GaussianMonomialDecayBudget.minimumReference (succ j) (R+two)) (minimumAuxiliary j C N R) :=
    le_of_eq_add (d := GaussianMonomialDecayBudget.minimumPrecision (succ j) C (R+two)+
      GaussianFastValueCut.exponent (num 10*pw N (R+two)) j) (by unfold minimumAuxiliary; ipra_ring)
  have third : Γ ⊢[PRAAx] le (GaussianFastValueCut.exponent (num 10*pw N (R+two)) j) (minimumAuxiliary j C N R) :=
    le_of_eq_add (d := GaussianMonomialDecayBudget.minimumPrecision (succ j) C (R+two)+
      GaussianMonomialDecayBudget.minimumReference (succ j) (R+two)) (by unfold minimumAuxiliary; ipra_ring)
  exact .andI (le_trans first h) (.andI (le_trans second h)
    (le_trans (GaussianFastValueCut.query_budget _ _) (GaussianExponentialReference.unit_monotone (le_trans third h))))

theorem monomial_bound (j w M C E N R : PTm n)
    (hE : Γ ⊢[PRAAx] le one E)
    (hM : Γ ⊢[PRAAx] le (minimumMesh j C R) M)
    (hw : Γ ⊢[PRAAx] le (minimumAuxiliary j C N R) w) : Γ ⊢[PRAAx]
    bounded (quadrature GaussianMonomialDecayQuadrature.evaluatorF w M E C E (R+two))
      (cap (R+two)*unit (succ j)+one) (unit (succ j)) := by
  have mesh := GaussianMonomialDecayBudget.mesh_threshold (succ j) M C (R+two) hM
  have aux := auxiliary_threshold j w C N R hw
  refine .orE (zero_or_succ C) ?_ ?_
  · have eq := (GaussianBetaIntegralThreeSplit.quadrature_congr (Γ := (C ≐ zero)::Γ)
      GaussianMonomialDecayQuadrature.evaluatorF (.eqRefl w) (.eqRefl M) (.eqRefl E) Prf.hyp0 (.eqRefl E) (.eqRefl (R+two))).eqTrans
      (GaussianCompactZeroWidth.quadrature_zero _ w M E E (R+two) hE.wk mesh.andE₁.wk)
    exact GaussianRationalReciprocal.bound_congr eq.eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianEulerNamedUpperTail.zero_bound _ _ (unit_positive (succ j)))
  · have hc : (C ≐ succ (pred C))::Γ ⊢[PRAAx] le one C :=
      le_congr (.eqRefl one) Prf.hyp0.eqSymm (zero_lt_succ (pred C))
    exact GaussianMonomialDecayBudget.original_grid_dyadic_bound w w (succ j) M C E (R+two)
      hE.wk hc hM.wk aux.andE₁.wk aux.andE₂.andE₁.wk

theorem residual_budget (C E N T J W : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hWidth : Γ ⊢[PRAAx] le C (E*N))
    (hQuery : Γ ⊢[PRAAx] le (num 10*T*J) W) : Γ ⊢[PRAAx]
    le (E*W+num 10*C*T*J) (two*E*N*W) := by
  ipra_le (𝔞(E*W))*sl hN+(𝔞(E*N))*sl hQuery+(𝔞(num 10*T*J))*sl hWidth

theorem scalar_budget (L C E N T J W P V : PTm n)
    (h : Γ ⊢[PRAAx] le (E*W+num 10*C*T*J) (two*E*N*W)) : Γ ⊢[PRAAx]
    le
      (((C*(T*(num 4*W+W)*P*V+N*W*W*(P+V)))*(N*(two*J))+
        (L*(two*J)+one)*(E*(N*W*W*P*V)))*(E*N*P*V*J))
      ((L*E*P*V*J+C*N*(P+V)*J+E*N*P*V)*
        ((E*(N*W*W*P*V))*(N*(two*J)))) := by
  ipra_le (𝔞(E*N*N*W*P*P*V*V*J))*sl h

private theorem unit_successor (j : PTm n) : Γ ⊢[PRAAx] unit (succ j) ≐ two*unit j :=
  (pw_succ two j).eqTrans (mul_comm _ _)

theorem original_middle_dyadic_bound (p v j w z R B C E N M : PTm n)
    (h : Γ ⊢[PRAAx] source z R B C E N)
    (hM : Γ ⊢[PRAAx] le (minimumMesh j C R) M)
    (hw : Γ ⊢[PRAAx] le (minimumAuxiliary j C N R) w) : Γ ⊢[PRAAx]
    distanceBounded
      (quadrature GaussianBetaKernelGridComparison.evaluatorF p M E C E (GaussianBetaKernelGridComparison.sampleDataBeta z B N))
      (quadrature GaussianEulerIntegrandName.evaluatorF v M E C E (GaussianEulerIntegrandName.fixedData z B))
      (numerator p v j R C E N) (denominator p v j E N) := by
  have he := h.andE₂.andE₁
  have hn := h.andE₂.andE₂.andE₁
  have mesh := GaussianMonomialDecayBudget.mesh_threshold (succ j) M C (R+two) hM
  have endpoint : Γ ⊢[PRAAx] le (E+C) (E*N) := le_trans
    (le_of_eq_add (d := E+C) (by ipra_ring)) h.andE₂.andE₂.andE₂
  have width : Γ ⊢[PRAAx] le C (E*N) := le_trans (le_of_eq_add (d := E) (by ipra_ring)) endpoint
  have src : Γ ⊢[PRAAx] GaussianBetaUpperGridMonomialComparison.source z R B E C E N N M :=
    .andI h.andE₁ (.andI he (.andI mesh.andE₁ (.andI (le_refl E) (.andI endpoint (.andI hn h.andE₂.andE₂.andE₂)))))
  have old := GaussianBetaUpperGridMonomialComparison.original_grid_from_monomial_bound p v w w z R B E C E N N M
    (cap (R+two)*unit (succ j)+one) (unit (succ j)) src (unit_positive (succ j)) (monomial_bound j w M C E N R he hM hw)
  have aux := auxiliary_threshold j w C N R hw
  have residual := residual_budget C E N (pw N (R+two)) (unit j) (unit w) hn width aux.andE₂.andE₂
  have pure := scalar_budget (cap (R+two)) C E N (pw N (R+two)) (unit j) (unit w) (unit p) (unit v) residual
  have change := unit_successor (Γ := Γ) j
  have compare : Γ ⊢[PRAAx]
      le (((C*comparisonNumerator p v w w (R+two) N N)*(N*unit (succ j))+
        (cap (R+two)*unit (succ j)+one)*(E*comparisonDenominator p v w w N))*denominator p v j E N)
        (numerator p v j R C E N*((E*comparisonDenominator p v w w N)*(N*unit (succ j)))) := by
    dsimp only [comparisonNumerator,comparisonDenominator,numerator,denominator]
    ipra_le sl pure using
      rw [natEq change]
      ipra_simps
  have hd := positive_product _ _ (positive_product _ _ he
    (positive_product _ _ (positive_product _ _ (positive_product _ _
      (positive_product _ _ hn (unit_positive w)) (unit_positive w)) (unit_positive p)) (unit_positive v)))
    (positive_product _ _ hn (unit_positive (succ j)))
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ hd
    (denominator_positive p v j E N he hn) compare old

theorem actual_middle_original_independent_queries_dyadic_budget_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
      ((source (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⋏
        (le (minimumMesh (var 2) (var 7) (var 5)) (var 10) ⋏
          le (minimumAuxiliary (var 2) (var 7) (var 9) (var 5)) (var 3))) ⟶
        distanceBounded
          (quadrature GaussianBetaKernelGridComparison.evaluatorF (var 0) (var 10) (var 8) (var 7) (var 8)
            (GaussianBetaKernelGridComparison.sampleDataBeta (var 4) (var 6) (var 9)))
          (quadrature GaussianEulerIntegrandName.evaluatorF (var 1) (var 10) (var 8) (var 7) (var 8)
            (GaussianEulerIntegrandName.fixedData (var 4) (var 6)))
          (numerator (var 0) (var 1) (var 2) (var 5) (var 7) (var 8) (var 9))
          (denominator (var 0) (var 1) (var 2) (var 8) (var 9))) :=
  closeUniv 11 (.impI (original_middle_dyadic_bound _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaMiddleDyadicBudget
