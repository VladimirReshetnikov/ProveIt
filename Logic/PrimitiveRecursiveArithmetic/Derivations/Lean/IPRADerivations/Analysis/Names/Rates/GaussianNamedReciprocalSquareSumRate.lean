import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedFiniteSumFamilyRate
import IPRADerivations.Analysis.Series.ReciprocalSquares.GaussianReciprocalSquareSumDistance

/-!
# Reciprocal-square row rates for original finite Gaussian names

The summed leading error keeps the finite reciprocal-square telescoper.
The original finite-sum query clock pays the uniform per-row observation
errors and uses the actual original finite-sum programs.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianNamedReciprocalSquareSumRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianNamedFiniteSumFamily (body data finite nameF sample_at term_at)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def intervalDenominator (D N r : PTm n) : PTm n := D*GaussianReciprocalSquareInterval.denominator N r
def rowDenominator (D N i : PTm n) : PTm n := D*(succ (N+i)*succ (N+i))

def rows (f g : PR 2) (t u : PTm 2) (N x y C D : PTm n) : Fm PTm n := .all
  (independentRate f g (inst2 t (var 0) (Syn.shift x)) (inst2 u (var 0) (Syn.shift y))
    (Syn.shift C) (rowDenominator (Syn.shift D) (Syn.shift N) (var 0)))

@[simp] theorem subst_intervalDenominator {l : ℕ} (σ : Fin n → PTm l) (D N r : PTm n) :
    Syn.subst σ (intervalDenominator D N r) =
      intervalDenominator (Syn.subst σ D) (Syn.subst σ N) (Syn.subst σ r) := by simp [intervalDenominator]

@[simp] theorem subst_rowDenominator {l : ℕ} (σ : Fin n → PTm l) (D N i : PTm n) :
    Syn.subst σ (rowDenominator D N i) = rowDenominator (Syn.subst σ D) (Syn.subst σ N) (Syn.subst σ i) :=
  by simp [rowDenominator]

@[simp] theorem subst_rows {l : ℕ} (σ : Fin n → PTm l) (f g : PR 2) (t u : PTm 2) (N x y C D : PTm n) :
    (rows f g t u N x y C D).subst σ = rows f g t u (Syn.subst σ N) (Syn.subst σ x)
      (Syn.subst σ y) (Syn.subst σ C) (Syn.subst σ D) := by simp [rows,Syn.subst_shift,Syn.shift_subst]

theorem interval_denominator_positive (D N r : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (intervalDenominator D N r) :=
  positive_product _ _ hD (GaussianReciprocalSquareInterval.denominator_positive N r hN)

theorem row_at (f g : PR 2) (t u : PTm 2) (N x y C D i : PTm n)
    (h : Γ ⊢[PRAAx] rows f g t u N x y C D) :
    Γ ⊢[PRAAx] independentRate f g (inst2 t i x) (inst2 u i y) C (rowDenominator D N i) := by
  simpa only [rows,GaussianNamedInverseRate.subst_independentRate,subst_inst2,subst_rowDenominator,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i

theorem finite_rate (f g : PR 2) (t u : PTm 2) (p q N r x y C D : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] rows f g t u N x y C D) :
    Γ ⊢[PRAAx] distanceBounded (finite f t p r x) (finite g u q r y)
      ((C*r)*(unit p*unit q)+intervalDenominator D N r*(r*(unit p+unit q)))
      (rateDenominator (intervalDenominator D N r) p q) := by
  let A := unit p+unit q
  let W := unit p*unit q
  have each : Γ ⊢[PRAAx] GaussianReciprocalSquareSumDistance.rows (body f t) (body g u) N C D A W (pairT p x) (pairT q y) := by
    refine .allI ?_
    let sh (a : PTm n) := Syn.shift a
    let Δ := Γ.map Fm.shift
    let i : PTm (n+1) := var 0
    have hs : Δ ⊢[PRAAx] rows f g t u (sh N) (sh x) (sh y) (sh C) (sh D) :=
      by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift
    have e := rate_at f g _ _ (sh C) (rowDenominator (sh D) (sh N) i) (sh p) (sh q)
      (row_at f g t u (sh N) (sh x) (sh y) (sh C) (sh D) i hs)
    let D' := rowDenominator (sh D) (sh N) i
    have moved : Δ ⊢[PRAAx] distanceBounded
        (inst2 (body f t) i (pairT (sh p) (sh x)))
        (inst2 (body g u) i (pairT (sh q) (sh y)))
        (sh C*(unit (sh p)*unit (sh q))+(unit (sh p)+unit (sh q))*D')
        (D'*(unit (sh p)*unit (sh q))) :=
      distance_congr (term_at f t i (sh p) (sh x)).eqSymm
      (term_at g u i (sh q) (sh y)).eqSymm (by unfold rateNumerator; ipra_ring)
      (by unfold rateDenominator; ipra_ring) e
    simpa only [GaussianReciprocalSquareSumDistance.rows,GaussianReciprocalSquareSumDistance.radiusDenominator,
      rowDenominator,D',A,W,GaussianCoefficientNameBounds.subst_unit,subst_pairT,PTm.subst_add,PTm.subst_mul,Syn.shift,sh,Δ,i] using moved
  have raw := GaussianReciprocalSquareSumDistance.sum_distance (body f t) (body g u) N C D A W (pairT p x) (pairT q y)
    r hN hD (positive_product _ _ (unit_positive p) (unit_positive q)) each
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by unfold A W intervalDenominator GaussianReciprocalSquareSumDistance.radiusNumerator; ipra_ring)
    (by unfold W intervalDenominator rateDenominator GaussianReciprocalSquareSumDistance.radiusDenominator; ipra_ring) raw

theorem original_observations (f g : PR 2) (t u : PTm 2) (p q N r x y C D : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] rows f g t u N x y C D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f t) p (data r x)) (ap2 (nameF g u) q (data r y))
      (rateNumerator (C*r) (intervalDenominator D N r) p q) (rateDenominator (intervalDenominator D N r) p q) := by
  let k := exponent r p
  let l := exponent r q
  let Z := intervalDenominator D N r
  let U := unit p
  let V := unit q
  let K := unit k
  let L := unit l
  have hz := interval_denominator_positive D N r hD hN
  have first := mul_le_mul_right (Z*Z*U*K) (query_budget (Γ := Γ) r q)
  have second := mul_le_mul_right (Z*Z*V*L) (query_budget (Γ := Γ) r p)
  have hsum := add_le_add_right ((C*r)*(K*L)*(Z*U*V)) (add_le_add₂ first second)
  have pay : Γ ⊢[PRAAx] le (((C*r)*(K*L)+Z*(r*(K+L)))*rateDenominator Z p q)
      (rateNumerator (C*r) Z p q*rateDenominator Z k l) :=
    le_congr (by dsimp only [U,V,K,L,rateDenominator]; ipra_ring)
      (by dsimp only [U,V,K,L,rateDenominator,rateNumerator]; ipra_ring) hsum
  have near := distance_radius_mono _ _ _ _ _ _ (denominator_positive Z k l hz) (denominator_positive Z p q hz) pay
    (finite_rate f g t u k l N r x y C D hD hN h)
  exact distance_congr (sample_at f t p r x).eqSymm (sample_at g u q r y).eqSymm (.eqRefl _) (.eqRefl _) near

theorem rate (f g : PR 2) (t u : PTm 2) (N r x y C D : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] rows f g t u N x y C D) :
    Γ ⊢[PRAAx] independentRate (nameF f t) (nameF g u) (data r x) (data r y) (C*r) (intervalDenominator D N r) := by
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] rows f g t u (sh N) (sh x) (sh y) (sh C) (sh D) :=
    by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.shift
  have hd : Δ ⊢[PRAAx] le one (sh D) := by simpa [Fm.shift,Syn.shift,sh,Δ,one] using hD.shift.shift
  have hn : Δ ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,sh,Δ,one] using hN.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,Syn.shift,sh,Δ,GaussianNamedFiniteSumFamily.subst_data,subst_intervalDenominator,PTm.subst_mul] using
    original_observations f g t u (var 1) (var 0) (sh N) (sh r) (sh x) (sh y) (sh C) (sh D) hd hn hs

theorem actual_named_reciprocal_square_sum_rate_closed (f g : PR 2) (t u : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let N := var 0
       let r := var 1
       let x := var 2
       let y := var 3
       let C := var 4
       let D := var 5
       (le one D ⋏ (le one N ⋏ rows f g t u N x y C D)) ⟶
         independentRate (nameF f t) (nameF g u) (data r x) (data r y) (C*r) (intervalDenominator D N r)) :=
  closeUniv 6 (.impI (rate f g t u _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedReciprocalSquareSumRate
