import IPRADerivations.Analysis.Names.FiniteOperations.Sums.Families.GaussianNamedFiniteSumFamily
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Families.GaussianNamedFiniteProductFamilyCongruence

/-!
# Rowwise equivalence of finite Gaussian sums

Each literal sum reads its own original row evaluator and row data.
Independent row estimates sum at the original finite count, then the
two computed query clocks absorb that count.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteSumFamilyCongruence

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianNamedFiniteProductFamilyCongruence (equalRows equal_at)
open GaussianNamedFiniteSumFamily (body data finite nameF sample_at term_at)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem finite_cross_distance (f g : PR 2) (t u : PTm 2) (p q N x y : PTm n)
    (h : Γ ⊢[PRAAx] equalRows f g t u N x y) :
    Γ ⊢[PRAAx] distanceBounded (finite f t p N x) (finite g u q N y)
      (N*(unit p+unit q)) (unit p*unit q) := by
  have rows : Γ ⊢[PRAAx] termsDistance (body f t) (body g u) N (pairT p x) (pairT q y)
      (unit p+unit q) (unit p*unit q) := by
    refine .allI (.impI ?_)
    let sh (a : PTm n) := Syn.shift a
    let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] equalRows f g t u (sh N) (sh x) (sh y) := by
      simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.wk
    have e := cross_at f g _ _ (sh p) (sh q) (equal_at f g t u (sh N) (sh x) (sh y) (var 0) hs Prf.hyp0)
    change Δ ⊢[PRAAx] distanceBounded
      (inst2 (body f t) (var 0) (Syn.shift (pairT p x)))
      (inst2 (body g u) (var 0) (Syn.shift (pairT q y))) (Syn.shift (unit p+unit q)) (Syn.shift (unit p*unit q))
    simpa only [Syn.shift,sh,subst_pairT,PTm.subst_mul,PTm.subst_add,GaussianCoefficientNameBounds.subst_unit] using
      distance_congr (term_at f t (var 0) (sh p) (sh x)).eqSymm
        (term_at g u (var 0) (sh q) (sh y)).eqSymm (.eqRefl _) (.eqRefl _) e
  exact sum_distance _ _ N _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) rows

theorem original_cross_distance (f g : PR 2) (t u : PTm 2) (p q N x y : PTm n)
    (h : Γ ⊢[PRAAx] equalRows f g t u N x y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f t) p (data N x)) (ap2 (nameF g u) q (data N y))
      (unit p+unit q) (unit p*unit q) := by
  let k := exponent N p
  let l := exponent N q
  have first := query_budget (Γ := Γ) N p
  have second := query_budget (Γ := Γ) N q
  have raw := finite_cross_distance f g t u k l N x y h
  have narrowed := distance_radius_mono _ _ _ _ (unit p+unit q) (unit p*unit q)
    (positive_product _ _ (unit_positive k) (unit_positive l))
    (positive_product _ _ (unit_positive p) (unit_positive q))
    (by ipra_le 𝔞(unit q)*𝔞(unit l)*sl first + 𝔞(unit p)*𝔞(unit k)*sl second) raw
  exact distance_congr (sample_at f t p N x).eqSymm (sample_at g u q N y).eqSymm (.eqRefl _) (.eqRefl _) narrowed

theorem family_sum_cross (f g : PR 2) (t u : PTm 2) (N x y : PTm n)
    (h : Γ ⊢[PRAAx] equalRows f g t u N x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f t) (nameF g u) (data N x) (data N y) := by
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] equalRows f g t u (sh N) (sh x) (sh y) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.shift
  simpa only [crossEquivalent,Syn.shift,sh,GaussianNamedFiniteSumFamily.subst_data] using
    original_cross_distance f g t u (var 1) (var 0) (sh N) (sh x) (sh y) hs

theorem actual_named_finite_family_sum_cross_closed (f g : PR 2) (t u : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (equalRows f g t u (var 0) (var 1) (var 2) ⟶
        crossEquivalent (nameF f t) (nameF g u) (data (var 0) (var 1)) (data (var 0) (var 2))) :=
  closeUniv 3 (.impI (family_sum_cross f g t u _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteSumFamilyCongruence
