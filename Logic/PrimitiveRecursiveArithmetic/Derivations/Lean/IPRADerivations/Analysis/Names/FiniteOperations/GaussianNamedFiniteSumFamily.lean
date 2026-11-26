import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductFamily
import IPRADerivations.Analysis.Integration.GaussianRationalRiemannRefinement

/-!
# Sum a finite family of regular Gaussian names

Read each original row at a common precision increased by the numerical
number of terms. Compare the two literal rational sums by the sum of the
row errors. The computed precision absorbs the full count, including
the empty-family case.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteSumFamily

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent query_budget)
open GaussianNameEquivalence (point_at)
open GaussianNamedFiniteProductFamily (regularRows regular_at)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def body (f : PR 2) (t : PTm 2) : PTm 2 :=
  ap2 f (fstT (var 1)) (inst2 t (var 0) (sndT (var 1)))
def data (N x : PTm n) : PTm n := pairT N x
def finite (f : PR 2) (t : PTm 2) (k N x : PTm n) : PTm n := sum (body f t) N (pairT k x)
def observation (f : PR 2) (t : PTm 2) (p N x : PTm n) : PTm n := finite f t (exponent N p) N x
def nameF (f : PR 2) (t : PTm 2) : PR 2 :=
  PTm.toPR (observation f t (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2)

ipra_subst data

ipra_subst observation [finite]

theorem term_at (f : PR 2) (t : PTm 2) (i k x : PTm n) :
    Γ ⊢[PRAAx] inst2 (body f t) i (pairT k x) ≐ ap2 f k (inst2 t i x) := by
  change Γ ⊢[PRAAx] Syn.subst ![i,pairT k x]
    (ap2 f (fstT (var 1)) (inst2 t (var 0) (sndT (var 1)))) ≐ _
  simpa only [subst_ap2,subst_inst2,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    congrAp2 f (fst_pair k x) (congrInst2 t (.eqRefl i) (snd_pair k x))

private theorem observation_congr (f : PR 2) (t : PTm 2) (p : PTm n) {M N x y : PTm n}
    (hn : Γ ⊢[PRAAx] M ≐ N) (hx : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] observation f t p M x ≐ observation f t p N y := by
  simpa only [subst_observation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
      (observation f t (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![p,M,x]) (σ' := ![p,N,y]) (fun i => by fin_cases i; exact .eqRefl _; exact hn; exact hx)

theorem sample_at (f : PR 2) (t : PTm 2) (p N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF f t) p (data N x) ≐ observation f t p N x := by
  let y := data N x
  have e : Γ ⊢[PRAAx] ap2 (nameF f t) p y ≐ observation f t p (fstT y) (sndT y) := by
    simpa [nameF,ap2] using toPR_eq (Γ := Γ)
      (observation f t (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![p,y]
  exact e.eqTrans (observation_congr f t p (fst_pair N x) (snd_pair N x))

/-- Comparison at arbitrary row clocks before any increase of precision. -/
theorem finite_distance (f : PR 2) (t : PTm 2) (p q N x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f t N x) :
    Γ ⊢[PRAAx] distanceBounded (finite f t p N x) (finite f t q N x)
      (N*(unit p+unit q)) (unit p*unit q) := by
  have rows : Γ ⊢[PRAAx] termsDistance (body f t) (body f t) N (pairT p x) (pairT q x)
      (unit p+unit q) (unit p*unit q) := by
    refine .allI (.impI ?_)
    let sh (a : PTm n) := Syn.shift a
    let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] regularRows f t (sh N) (sh x) := by
      simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.wk
    have hr := regular_at f t (sh N) (sh x) (var 0) hs Prf.hyp0
    have e := point_at f (inst2 t (var 0) (sh x)) (sh p) (sh q) hr
    change Δ ⊢[PRAAx] distanceBounded
      (inst2 (body f t) (var 0) (Syn.shift (pairT p x)))
      (inst2 (body f t) (var 0) (Syn.shift (pairT q x))) (Syn.shift (unit p+unit q)) (Syn.shift (unit p*unit q))
    simpa only [Syn.shift,sh,subst_pairT,PTm.subst_mul,PTm.subst_add,
      GaussianCoefficientNameBounds.subst_unit] using
      distance_congr (term_at f t (var 0) (sh p) (sh x)).eqSymm
        (term_at f t (var 0) (sh q) (sh x)).eqSymm (.eqRefl _) (.eqRefl _) e
  exact sum_distance _ _ N _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) rows

theorem observed_distance (f : PR 2) (t : PTm 2) (p q N x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f t N x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f t) p (data N x)) (ap2 (nameF f t) q (data N x))
      (unit p+unit q) (unit p*unit q) := by
  let k := exponent N p
  let l := exponent N q
  have first := query_budget (Γ := Γ) N p
  have second := query_budget (Γ := Γ) N q
  have raw := finite_distance f t k l N x h
  have narrowed := distance_radius_mono _ _ _ _ (unit p+unit q) (unit p*unit q)
    (positive_product _ _ (unit_positive k) (unit_positive l))
    (positive_product _ _ (unit_positive p) (unit_positive q))
    (by ipra_le 𝔞(unit q)*𝔞(unit l)*sl first + 𝔞(unit p)*𝔞(unit k)*sl second) raw
  exact distance_congr (sample_at f t p N x).eqSymm (sample_at f t q N x).eqSymm (.eqRefl _) (.eqRefl _) narrowed

theorem regular (f : PR 2) (t : PTm 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f t N x) : Γ ⊢[PRAAx] pointCN (nameF f t) (data N x) := by
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] regularRows f t (sh N) (sh x) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.shift
  simpa only [pointCN,Syn.shift,sh,subst_data,GaussianEuclideanPointDistance.unit,unit] using observed_distance f t (var 1) (var 0) (sh N) (sh x) hs

theorem actual_regular_family_sum_closed (f : PR 2) (t : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (regularRows f t (var 0) (var 1) ⟶ pointCN (nameF f t) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (regular f t _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteSumFamily
