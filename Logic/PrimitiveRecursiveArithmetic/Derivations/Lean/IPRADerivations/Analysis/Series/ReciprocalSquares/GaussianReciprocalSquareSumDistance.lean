import IPRADerivations.Analysis.Series.ReciprocalSquares.GaussianReciprocalSquareInterval
import IPRADerivations.Analysis.Names.GaussianNameArithmetic

/-!
# Finite reciprocal-square distances with a common observation error

Compare two literal rational sums with row errors
(C/(Dk^2)+A/E), where the row indices start at (N+1).
The finite telescope gives (Cr/(DN(N+r))+rA/E) while retaining the
two original row programs and every observation error.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianReciprocalSquareSumDistance

open_ipra
open GaussianReciprocalSquareInterval (denominator denominator_positive)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalReciprocal (bound_congr bounded_sum)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def radiusNumerator (C A D W r : PTm n) : PTm n := (C*W+A*D)*r

def radiusDenominator (D W : PTm n) : PTm n := D*W

def rows (f g : PTm 2) (N C D A W x y : PTm n) : Fm PTm n := .all
  (let k := succ (Syn.shift N+var 0)
   let M := Syn.shift D*(k*k)
   distanceBounded (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift y))
     (Syn.shift C*Syn.shift W+Syn.shift A*M) (radiusDenominator M (Syn.shift W)))

@[simp] theorem subst_radiusNumerator {m : ℕ} (σ : Fin n → PTm m) (C A D W r : PTm n) :
    Syn.subst σ (radiusNumerator C A D W r) =
      radiusNumerator (Syn.subst σ C) (Syn.subst σ A) (Syn.subst σ D) (Syn.subst σ W) (Syn.subst σ r) := by
  simp [radiusNumerator]

@[simp] theorem subst_radiusDenominator {m : ℕ} (σ : Fin n → PTm m) (D W : PTm n) :
    Syn.subst σ (radiusDenominator D W) = radiusDenominator (Syn.subst σ D) (Syn.subst σ W) := by
  simp [radiusDenominator]

@[simp] theorem subst_rows {m : ℕ} (σ : Fin n → PTm m) (f g : PTm 2) (N C D A W x y : PTm n) :
    (rows f g N C D A W x y).subst σ = rows f g (Syn.subst σ N) (Syn.subst σ C)
      (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ W) (Syn.subst σ x) (Syn.subst σ y) := by
  simp [rows,Syn.subst_shift,Syn.shift_subst]

theorem row_at (f g : PTm 2) (N C D A W x y i : PTm n) (h : Γ ⊢[PRAAx] rows f g N C D A W x y) :
    Γ ⊢[PRAAx] distanceBounded (inst2 f i x) (inst2 g i y)
      (C*W+A*(D*(succ (N+i)*succ (N+i)))) (radiusDenominator (D*(succ (N+i)*succ (N+i))) W) := by
  simpa only [rows,GaussianRationalMetric.subst_distanceBounded,subst_inst2,PTm.subst_mul,PTm.subst_add,
    subst_radiusDenominator,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i

private theorem sum_zero_bound (f g : PTm 2) (C D A W x y : PTm n)
    (h : Γ ⊢[PRAAx] le one (radiusDenominator D W)) :
    Γ ⊢[PRAAx] distanceBounded (sum f zero x) (sum g zero y) (radiusNumerator C A D W zero)
      (radiusDenominator D W) :=
  distance_congr (GaussianRationalFiniteSum.sum_zero f x).eqSymm
    (GaussianRationalFiniteSum.sum_zero g y).eqSymm (mul_zero _).eqSymm (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero qzero _ h)

private theorem sum_step (f g : PTm 2) (N C D A W x y r : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] le one D) (hW : Γ ⊢[PRAAx] le one W)
    (h : Γ ⊢[PRAAx] rows f g N C D A W x y)
    (ih : Γ ⊢[PRAAx] distanceBounded (sum f r x) (sum g r y)
      (radiusNumerator C A (D*denominator N r) W r) (radiusDenominator (D*denominator N r) W)) :
    Γ ⊢[PRAAx] distanceBounded (sum f (succ r) x) (sum g (succ r) y)
      (radiusNumerator C A (D*denominator N (succ r)) W (succ r))
      (radiusDenominator (D*denominator N (succ r)) W) := by
  let k := succ (N+r)
  let P := D*denominator N r
  let Q := D*(k*k)
  let T := D*denominator N (succ r)
  let U := radiusDenominator P W
  let V := radiusDenominator Q W
  let Z := radiusDenominator T W
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have hU : Γ ⊢[PRAAx] le one U := positive_product _ _ (positive_product _ _ hD (denominator_positive N r hN)) hW
  have hV : Γ ⊢[PRAAx] le one V := positive_product _ _ (positive_product _ _ hD (positive_product _ _ hk hk)) hW
  have hZ : Γ ⊢[PRAAx] le one Z := positive_product _ _ (positive_product _ _ hD (denominator_positive N (succ r) hN)) hW
  have added := bounded_sum _ _ _ U _ V hU hV ih (row_at f g N C D A W x y r h)
  have raw : Γ ⊢[PRAAx] distanceBounded (sum f (succ r) x) (sum g (succ r) y)
      (radiusNumerator C A P W r*V+(C*W+A*Q)*U) (U*V) := by
    exact distance_congr (GaussianRationalFiniteSum.sum_succ f r x).eqSymm
      (GaussianRationalFiniteSum.sum_succ g r y).eqSymm (.eqRefl _) (.eqRefl _)
      (bound_congr (GaussianNameArithmetic.sum_difference _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) added)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hV) hZ
    (le_of_eq_add (d := C*N*N*k*(D*D)*(W*W*W)) (by
      dsimp only [U,V,Z,P,Q,T,k,radiusNumerator,radiusDenominator,denominator]
      ipra_ring)) raw

theorem sum_distance (f g : PTm 2) (N C D A W x y r : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] le one D) (hW : Γ ⊢[PRAAx] le one W)
    (h : Γ ⊢[PRAAx] rows f g N C D A W x y) :
    Γ ⊢[PRAAx] distanceBounded (sum f r x) (sum g r y)
      (radiusNumerator C A (D*denominator N r) W r)
      (radiusDenominator (D*denominator N r) W) := by
  let sh (u : PTm n) := Syn.shift u
  let Δ := Γ.map Fm.shift
  have all : Γ ⊢[PRAAx] .all (distanceBounded (sum f (var 0) (sh x)) (sum g (var 0) (sh y))
      (radiusNumerator (sh C) (sh A) (sh D*denominator (sh N) (var 0)) (sh W) (var 0))
      (radiusDenominator (sh D*denominator (sh N) (var 0)) (sh W))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · have pos : Γ ⊢[PRAAx] le one (radiusDenominator (D*denominator N zero) W) :=
        positive_product _ _ (positive_product _ _ hD (denominator_positive N zero hN)) hW
      simpa only [GaussianRationalMetric.subst_distanceBounded,GaussianRationalFiniteSum.subst_sum,
        subst_radiusNumerator,subst_radiusDenominator,GaussianReciprocalSquareInterval.subst_denominator,
        PTm.subst_mul,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh] using
        sum_zero_bound f g C (D*denominator N zero) A W x y pos
    · have n' : Δ ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hN.shift
      have d' : Δ ⊢[PRAAx] le one (sh D) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hD.shift
      have w' : Δ ⊢[PRAAx] le one (sh W) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hW.shift
      have rows' : Δ ⊢[PRAAx] rows f g (sh N) (sh C) (sh D) (sh A) (sh W) (sh x) (sh y) := by
        simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift
      simpa only [GaussianRationalMetric.subst_distanceBounded,GaussianRationalFiniteSum.subst_sum,
        subst_radiusNumerator,subst_radiusDenominator,GaussianReciprocalSquareInterval.subst_denominator,
        PTm.subst_mul,Syn.subst_var,Syn.repl_zero,subst_repl_shift,sh] using
        sum_step f g (sh N) (sh C) (sh D) (sh A) (sh W) (sh x) (sh y) (var 0) n'.wk d'.wk w'.wk rows'.wk Prf.hyp0
  simpa only [GaussianRationalMetric.subst_distanceBounded,GaussianRationalFiniteSum.subst_sum,
    subst_radiusNumerator,subst_radiusDenominator,GaussianReciprocalSquareInterval.subst_denominator,
    PTm.subst_mul,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh] using all.allE r

theorem actual_reciprocal_square_sum_distance_closed (f g : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (let N := var 0
       let C := var 1
       let D := var 2
       let A := var 3
       let W := var 4
       let x := var 5
       let y := var 6
       let r := var 7
       (le one N ⋏ (le one D ⋏ le one W)) ⟶ rows f g N C D A W x y ⟶
         distanceBounded (sum f r x) (sum g r y) (radiusNumerator C A (D*denominator N r) W r)
           (radiusDenominator (D*denominator N r) W)) :=
  closeUniv 8 (.impI (.impI (sum_distance f g _ _ _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianReciprocalSquareSumDistance
