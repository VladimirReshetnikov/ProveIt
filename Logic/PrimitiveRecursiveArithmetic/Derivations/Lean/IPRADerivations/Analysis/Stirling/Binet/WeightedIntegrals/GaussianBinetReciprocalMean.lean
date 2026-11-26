import IPRADerivations.Analysis.Stirling.Binet.WeightedIntegrals.GaussianBinetReciprocalRows
import IPRADerivations.Analysis.Series.GaussianRationalNormalizedTelescope

/-!
# The literal finite reciprocal average on a complex horizontal cell

The mean evaluates the actual reciprocal at every rational mesh point
in the unit cell. The weight cancels the mesh size in the error bound,
leaving the sharp telescoping difference of positive real reciprocals.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetReciprocalMean

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetReciprocalRows (tagPoint tag_distance)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerReciprocalSlope (shiftedPoint)
open GaussianLogGammaEulerRepresentation (subst_argument)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalNormalizedTelescope (mean_error weight)
open GaussianRationalParameterTelescope (slopeRows)
open GaussianRationalReciprocal (reciprocal)
open GaussianRightHalfPlaneLogarithm (source)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def gridData (X Y E neg D : PTm n) : PTm n := pairT X (pairT Y (pairT E (pairT neg D)))

def data (A B D neg k M : PTm n) : PTm n := gridData (M*(A+k*D)) (M*B) (M*D) neg D

def rowBody : PTm 2 := reciprocal (argument
  (fstT (var 1)+var 0*sndT (sndT (sndT (sndT (var 1)))))
  (fstT (sndT (var 1))) (fstT (sndT (sndT (var 1)))) (fstT (sndT (sndT (sndT (var 1))))))

def value (A B D neg k M : PTm n) : PTm n := qmul (weight M) (sum rowBody M (data A B D neg k M))

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (A B D neg k M : PTm n) :
    Syn.subst σ (data A B D neg k M) =
      data (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ k) (Syn.subst σ M) := by
  simp [data, gridData]

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (A B D neg k M : PTm n) :
    Syn.subst σ (value A B D neg k M) =
      value (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ k) (Syn.subst σ M) := by
  simp [value]

theorem row_at (X Y E neg D j : PTm n) : Γ ⊢[PRAAx]
    inst2 rowBody j (gridData X Y E neg D) ≐ reciprocal (argument (X+j*D) Y E neg) := by
  let z := gridData X Y E neg D
  let s := sndT z
  let t := sndT s
  let w := sndT t
  have hx : Γ ⊢[PRAAx] fstT z ≐ X := fst_pair _ _
  have hs : Γ ⊢[PRAAx] s ≐ pairT Y (pairT E (pairT neg D)) := snd_pair _ _
  have ht := (congrSnd hs).eqTrans (snd_pair Y (pairT E (pairT neg D)))
  have hw := (congrSnd ht).eqTrans (snd_pair E (pairT neg D))
  have hy := (congrFst hs).eqTrans (fst_pair _ _)
  have he := (congrFst ht).eqTrans (fst_pair _ _)
  have hn := (congrFst hw).eqTrans (fst_pair _ _)
  have hd := (congrSnd hw).eqTrans (snd_pair _ _)
  simpa only [rowBody, inst2, subst_argument, GaussianRationalReciprocal.subst_reciprocal,
    PTm.subst_add, PTm.subst_mul, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, z, s, t, w] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (reciprocal (argument (var 0) (var 1) (var 2) (var 3)) : PTm 4)
      (σ := ![fstT z+j*sndT w,fstT s,fstT t,fstT w]) (σ' := ![X+j*D,Y,E,neg])
      (fun i => by fin_cases i; exact congrAdd hx (congrMul (.eqRefl j) hd); exact hy; exact he; exact hn)

theorem tag_at (A B D neg k M j : PTm n) : Γ ⊢[PRAAx]
    inst2 rowBody j (data A B D neg k M) ≐ reciprocal (tagPoint A B D neg k M j) :=
  row_at (M*(A+k*D)) (M*B) (M*D) neg D j

theorem finite_mean_distance (A B D neg k M : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    distanceBounded (value A B D neg k M) (reciprocal (shiftedPoint (argument A B D neg) k))
      (D*D) ((A+k*D)*(A+(k+one)*D)) := by
  let E := (A+k*D)*(A+(k+one)*D)
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _
    (le_trans h.andE₁.andE₁ (le_add_right _ _)) (le_trans h.andE₁.andE₁ (le_add_right _ _))
  apply mean_error rowBody M (data A B D neg k M) _ (D*D) E hM hE
  refine .allI (.impI ?_)
  let sh (v : PTm n) := Syn.shift v
  let Δ := lt (var 0) (sh M) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh A) (sh D) (sh neg) :=
    by simpa [Δ,sh,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using h.shift.wk
  have hm : Δ ⊢[PRAAx] le one (sh M) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hM.shift.wk
  let e := (sh A+sh k*sh D)*(sh A+(sh k+one)*sh D)
  have he : Δ ⊢[PRAAx] le one e := by simpa [e,E,Δ,sh,Fm.shift,Syn.shift,one] using hE.shift.wk
  have near := tag_distance (sh A) (sh B) (sh D) (sh neg) (sh k) (sh M) (var 0) hs hm (le_of_lt Prf.hyp0)
  have rev := GaussianRationalDistanceOrder.distance_symmetric _ _ (sh D*sh D) e he near
  simpa only [slopeRows, GaussianRationalRiemannRefinement.constant_entry, sh, Δ, E, e, Syn.shift,
    subst_data, GaussianRationalReciprocal.subst_reciprocal, GaussianLogGammaEulerReciprocalSlope.subst_shiftedPoint,
    subst_argument, PTm.subst_add, PTm.subst_mul, one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using
    GaussianRationalDistanceOrder.distance_congr (tag_at (sh A) (sh B) (sh D) (sh neg) (sh k) (sh M) (var 0)).eqSymm
      (.eqRefl _) (.eqRefl _) (.eqRefl _) rev

theorem actual_complex_reciprocal_rectangle_mean_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 2) (var 3) ⟶ le one (var 5) ⟶
      distanceBounded (value (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (reciprocal (shiftedPoint (argument (var 0) (var 1) (var 2) (var 3)) (var 4)))
        (var 2*var 2) ((var 0+var 4*var 2)*(var 0+(var 4+one)*var 2))) :=
  closeUniv 6 (.impI (.impI (finite_mean_distance _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetReciprocalMean
