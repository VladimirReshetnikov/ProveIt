import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasRefinementEndpoints

/-!
# From translated refinement estimates to quotient constancy

The grid compares observations of the original quotient at two rational
points. Transport them to fixed charts before passing to the name-level
equality. The two transports and grid estimate cost five dyadic units.
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasRefinementReadback

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesVignerasIntegerPeriod (data input margin bound)
open GaussianBarnesVignerasMeshConstancy (mixed_close positive_chart)
open GaussianBarnesVignerasRefinementEndpoints (original_projection)
open GaussianBarnesVignerasRefinementWrap (body numerator observationClock)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDiscretePeriodicGridReadback (sample)
open GaussianNameEquivalence (crossEquivalent cross_symm)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalMetric (distanceBounded)
open GaussianSignedObservationReadback (realProjection)
open SignedDiscreteDerivativeOperators (divisor width)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Q" => GaussianBarnesVignerasLogQuotient.nameF

theorem fixed_distance (f : PR 2) (t : PTm 2) (x N i a b p : PTm n)
    (hD : Γ ⊢[PRAAx] le one (divisor x)) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N)
    (hp : Γ ⊢[PRAAx] le p (observationClock x))
    (hLeft : Γ ⊢[PRAAx] crossEquivalent (Q f) (Q f)
      (data t (numerator x (i*width x)) (divisor x)) (data t a b))
    (hRight : Γ ⊢[PRAAx] crossEquivalent (Q f) (Q f)
      (data t (numerator x (zero*width x)) (divisor x)) (data t one one))
    (hMesh : Γ ⊢[PRAAx] distanceBounded (realProjection (sample (body f t) x (rem i N)))
      (realProjection (sample (body f t) x (rem zero N))) one (unit p)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (Q f) p (data t a b)) (ap2 (Q f) p (data t one one)) (num 5) (unit p) := by
  let r := observationClock x
  let u := data t (numerator x (i*width x)) (divisor x)
  let v := data t (numerator x (zero*width x)) (divisor x)
  let q : PTm n := data t one one
  have hu := original_projection f t x N i hD hN hi
  have hv := original_projection f t x N zero hD hN hN
  have first := mixed_close (Q f) (data t a b) u p r (cross_symm _ _ _ _ hLeft) hp
  have third := distance_symmetric _ _ _ _ (unit_positive p)
    (mixed_close (Q f) q v p r (cross_symm _ _ _ _ hRight) hp)
  have second := distance_congr hu hv (.eqRefl _) (.eqRefl _) hMesh
  have thenFirst := distance_triangle_same _ _ _ _ _ _ (unit_positive p) first second
  have full := distance_triangle_same _ _ _ _ _ _ (unit_positive p) thenFirst third
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) full

def row (f : PR 2) (t : PTm 2) (x N i a b p : PTm n) : Fm PTm n :=
  (le one (divisor x) ⋏ le p (observationClock x)) ⋏
  ((crossEquivalent (Q f) (Q f)
      (data t (numerator x (i*width x)) (divisor x)) (data t a b) ⋏
    crossEquivalent (Q f) (Q f)
      (data t (numerator x (zero*width x)) (divisor x)) (data t one one)) ⋏
   distanceBounded (realProjection (sample (body f t) x (rem i N)))
      (realProjection (sample (body f t) x (rem zero N))) one (unit p))

def schedule (f : PR 2) (t s : PTm 2) (N i a b z : PTm n) : Fm PTm n :=
  .all (row f t (inst2 s (var 0) (Syn.shift z)) (Syn.shift N) (Syn.shift i)
    (Syn.shift a) (Syn.shift b) (var 0))

theorem constant (f : PR 2) (t s : PTm 2) (N i a b z : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hA : Γ ⊢[PRAAx] positive_chart f t a b) (h1 : Γ ⊢[PRAAx] positive_chart f t one one)
    (h : Γ ⊢[PRAAx] schedule f t s N i a b z) : Γ ⊢[PRAAx] crossEquivalent (Q f) (Q f) (data t a b) (data t one one) := by
  apply GaussianNameRingLaws.equivalent_of_envelope (Q f) (Q f) (data t a b) (data t one one) (num 5)
    (GaussianBarnesVignerasLogQuotient.regular f a b _ _ _ ha hb hA)
    (GaussianBarnesVignerasLogQuotient.regular f one one _ _ _ (le_refl one) (le_refl one) h1)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let x := inst2 s p (Syn.shift z)
  have nn : Δ ⊢[PRAAx] le one (Syn.shift N) := by simpa [Δ,Syn.shift,Fm.shift,one] using hN.shift
  have ii : Δ ⊢[PRAAx] lt (Syn.shift i) (Syn.shift N) := by simpa [Δ,Syn.shift,Fm.shift] using hi.shift
  have cert : Δ ⊢[PRAAx] row f t x (Syn.shift N) (Syn.shift i) (Syn.shift a) (Syn.shift b) p := h.allOpen
  have obs := fixed_distance f t x (Syn.shift N) (Syn.shift i) (Syn.shift a) (Syn.shift b) p
    cert.andE₁.andE₁ nn ii cert.andE₁.andE₂ cert.andE₂.andE₁.andE₁ cert.andE₂.andE₁.andE₂ cert.andE₂.andE₂
  change Δ ⊢[PRAAx] distanceBounded (ap2 (Q f) p (Syn.shift (data t a b)))
    (ap2 (Q f) p (Syn.shift (data t one one))) (Syn.shift (num 5 : PTm n)) (unit p)
  simpa only [Syn.shift,GaussianBarnesVignerasIntegerPeriod.subst_data,one,
    LeanProofs.IPRA.PTm.subst_num,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using obs

theorem actual_Barnes_refinement_fixed_chart_constancy_closed (f : PR 2) (t s : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let N := var 0
       let i := var 1
       let a := var 2
       let b := var 3
       let z := var 4
       ((le one N ⋏ lt i N) ⋏ ((le one a ⋏ le one b) ⋏
        (positive_chart f t a b ⋏ positive_chart f t one one))) ⟶ schedule f t s N i a b z ⟶
        crossEquivalent (Q f) (Q f) (data t a b) (data t one one)) :=
  closeUniv 5 (.impI (.impI (constant f t s _ _ _ _ _ Prf.hyp1.andE₁.andE₁ Prf.hyp1.andE₁.andE₂
    Prf.hyp1.andE₂.andE₁.andE₁ Prf.hyp1.andE₂.andE₁.andE₂ Prf.hyp1.andE₂.andE₂.andE₁
    Prf.hyp1.andE₂.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasRefinementReadback
