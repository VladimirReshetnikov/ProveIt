import IPRADerivations.Analysis.Trigonometry.Arctangent.Cayley.FiniteTelescopes.GaussianArctangentCayleyExponentialStep
import IPRADerivations.Analysis.Trigonometry.Arctangent.PartialSums.GaussianArctangentExponentialPrefix
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameConjugation
import IPRADerivations.Analysis.Series.Telescoping.GaussianRationalParameterTelescope

/-!
# Finite exponential transport along the native arctangent grid

Each row multiplies the finite scalar exponential of the exact arctangent
prefix by the conjugate Cayley grid point. A finite forward telescope adds
the local error bounds and compares the final exponential sample with i.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentCayleyTelescope

open_ipra
open ComplexLogarithmRemainder (normSq_eval scale oneCode)
open GaussianArctangentCayleyExponentialStep (row sample subst_row subst_sample
  sample_zero sample_canonical local_exponential_step conjugate_left_endpoint)
open GaussianArctangentCayleyStep (conjugateValue)
open GaussianArctangentCayleyValues (imaginaryPoint numerator value unit_bound right_endpoint exact_square_norm)
open GaussianArctangentExponentialPrefix (source prefixValue prefix_zero prefix_succ prefix_bound)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (canonical ofGaussian_canonical ofGaussian_represents positive_product qmul
  canonical_unique qmul_canonical qmul_represents represents_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalParameterTelescope (forward forward_at forward_sum)
open GaussianRationalReciprocal (bound_congr conjugate re_conjugate im_conjugate qone qone_represents_scaled)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianRootAlgebra (equal equal_of_values re_mul im_mul re_scale im_scale re_one im_one)
open GaussianScalarExponentialProductTail (rectangleCutoff termsBounded sum_bound)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def error (M s : PTm n) : PTm n := num 128*unit s+M*M
def denominator (M s : PTm n) : PTm n := M*M*unit s

private def rowBody : PTm 2 :=
  row (fstT (var 1)) (var 0) (sndT (sndT (var 1)))
    (prefixValue (var 0) (fstT (var 1)) (fstT (sndT (var 1))))

private theorem row_at (j M L s : PTm n) : Γ ⊢[PRAAx]
    inst2 rowBody j (pairT M (pairT L s)) ≐ row M j s (prefixValue j M L) := by
  let x := pairT M (pairT L s)
  have hM : Γ ⊢[PRAAx] fstT x ≐ M := fst_pair _ _
  have hL : Γ ⊢[PRAAx] fstT (sndT x) ≐ L := (snd_pair M (pairT L s)).fstE
  have hs : Γ ⊢[PRAAx] sndT (sndT x) ≐ s := (snd_pair M (pairT L s)).sndE
  simpa [rowBody,inst2,x] using Prf.eqCongr
    (row (var 0) (var 1) (var 2) (prefixValue (var 1) (var 0) (var 3)) : PTm 4)
    (σ := ![fstT x,j,sndT (sndT x),fstT (sndT x)]) (σ' := ![M,j,s,L])
    (fun i => by fin_cases i; exact hM; exact .eqRefl _; exact hs; exact hL)

private theorem sample_congr (s : PTm n) {P Q : PTm n} (h : Γ ⊢[PRAAx] P ≐ Q) :
    Γ ⊢[PRAAx] sample P s ≐ sample Q s :=
  GaussianNameConjugation.scalar_sum_congr (rectangleCutoff two s) h

private theorem row_terms (K M L s : PTm n)
    (hsrc : Γ ⊢[PRAAx] source M L) (hM : Γ ⊢[PRAAx] le two M) (hK : Γ ⊢[PRAAx] le K M) :
    Γ ⊢[PRAAx] termsBounded (forward rowBody) K (pairT M (pairT L s)) (error M s) (denominator M s) := by
  have hsrc' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift M) (Syn.shift L) := by
    simpa [Fm.shift,Syn.shift] using hsrc.shift
  have hM' : Γ.map Fm.shift ⊢[PRAAx] le two (Syn.shift M) := by
    simpa [Fm.shift,Syn.shift,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hM.shift
  have hK' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift K) (Syn.shift M) := by
    simpa [Fm.shift,Syn.shift] using hK.shift
  refine .allI (.impI ?_)
  let j : PTm (n+1) := var 0
  let m := Syn.shift M
  let l := Syn.shift L
  let t := Syn.shift s
  have hdata : Syn.shift (pairT M (pairT L s)) = pairT m (pairT l t) := by
    simp [Syn.shift,m,l,t]
  have herror : Syn.shift (error M s) = error m t := by simp [error,Syn.shift,m,t]
  have hden : Syn.shift (denominator M s) = denominator m t := by simp [denominator,Syn.shift,m,t]
  rw [forward_at,hdata,herror,hden]
  have hj : (lt j (Syn.shift K) :: Γ.map Fm.shift) ⊢[PRAAx] lt j m := le_trans Prf.hyp0 hK'.wk
  have bound := prefix_bound j m l hsrc'.wk (le_trans (le_succ_self j) hj)
  have next := (row_at (succ j) m l t).eqTrans (qmul_congr
    (sample_congr t (prefix_succ j m l hsrc'.wk hj)) (.eqRefl (conjugateValue m (succ j))))
  exact distance_congr next.eqSymm (row_at j m l t).eqSymm
    (.eqRefl _) (.eqRefl _) (local_exponential_step m j t _ hM'.wk bound)

theorem denominator_positive (M s : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] le one (denominator M s) :=
  positive_product _ _ (positive_product _ _ hM hM) (unit_positive s)

theorem row_endpoint (K M L s : PTm n)
    (hsrc : Γ ⊢[PRAAx] source M L) (hM : Γ ⊢[PRAAx] le two M) (hK : Γ ⊢[PRAAx] le K M) :
    Γ ⊢[PRAAx] distanceBounded (row M K s (prefixValue K M L)) qone (K*error M s) (denominator M s) := by
  let x := pairT M (pairT L s)
  have hd := denominator_positive M s hsrc.andE₁
  have start : Γ ⊢[PRAAx] inst2 rowBody zero x ≐ qone := by
    have hz := sample_congr s (prefix_zero (Γ := Γ) M L)
    exact (row_at zero M L s).eqTrans
      ((qmul_congr (hz.eqTrans (sample_zero s)) (conjugate_left_endpoint M hsrc.andE₁)).eqTrans
        (qmul_one_right qone GaussianRationalSyntheticDivision.qone_canonical))
  have path := bound_congr (forward_sum rowBody K x) (.eqRefl _) (.eqRefl _)
    (sum_bound (forward rowBody) K x (error M s) (denominator M s) hd (row_terms K M L s hsrc hM hK))
  exact distance_congr (row_at K M L s) start (.eqRefl _) (.eqRefl _) path

private theorem conjugate_inverse (M j : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] qmul (conjugateValue M j) (value M j) ≐ qone := by
  let a := numerator M j
  let d := GaussianArctangentCayleyValues.denominator M j
  have h := GaussianArctangentCayleyValues.denominator_positive M j hM
  have hp := positive_product _ _ h h
  have e : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.mul (conjugate a) a) (scale (d*d) oneCode) := by
    apply equal_of_values
    · simp only [re_mul,re_conjugate,im_conjugate,re_scale,re_one]
      have hn := natEq (exact_square_norm (Γ := Γ) M j)
      rw [normSq_eval,Q.mk_mul,map_mul] at hn
      rw [Q.mk_mul,map_mul,mul_one]
      dsimp only [a,d]
      linear_combination hn
    · simp only [im_mul,re_conjugate,im_conjugate,im_scale,im_one]
      ring
  have rep := qmul_represents _ _ (conjugate a) a d d h h
    (ofGaussian_represents _ _ h) (ofGaussian_represents _ _ h)
  exact canonical_unique _ _ _ (d*d) (qmul_canonical _ _) (ofGaussian_canonical _ _ (le_refl one)) hp
    (represents_congr (.eqRefl _) e (.eqRefl _) rep) (qone_represents_scaled (d*d))

theorem partial_distance (K M L s : PTm n)
    (hsrc : Γ ⊢[PRAAx] source M L) (hM : Γ ⊢[PRAAx] le two M) (hK : Γ ⊢[PRAAx] le K M) :
    Γ ⊢[PRAAx] distanceBounded (sample (prefixValue K M L) s) (value M K) (K*error M s) (denominator M s) := by
  have hd := denominator_positive M s hsrc.andE₁
  have endpoint := row_endpoint K M L s hsrc hM hK
  have left : Γ ⊢[PRAAx] qmul (value M K) (row M K s (prefixValue K M L)) ≐ sample (prefixValue K M L) s :=
    (GaussianApproximateInverseDistance.right_rearrange _ _ _).eqTrans
      ((qmul_congr (conjugate_inverse M K hsrc.andE₁) (.eqRefl _)).eqTrans
        ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
          (qmul_one_right _ (sample_canonical _ _))))
  have hC : Γ ⊢[PRAAx] canonical (value M K) :=
    ofGaussian_canonical _ _ (GaussianArctangentCayleyValues.denominator_positive M K hsrc.andE₁)
  exact distance_congr left (qmul_one_right _ hC)
    (one_mul _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance _ _ _ one _ _ hd (unit_bound M K hsrc.andE₁) endpoint)

theorem endpoint_distance (M L s : PTm n)
    (hsrc : Γ ⊢[PRAAx] source M L) (hM : Γ ⊢[PRAAx] le two M) :
    Γ ⊢[PRAAx] distanceBounded (sample (prefixValue M M L) s) imaginaryPoint (M*error M s) (denominator M s) :=
  distance_congr (.eqRefl _) (right_endpoint M hsrc.andE₁) (.eqRefl _) (.eqRefl _)
    (partial_distance M M L s hsrc hM (le_refl M))

theorem actual_arctangent_Cayley_telescope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶ le two (var 0) ⟶
      distanceBounded (sample (prefixValue (var 0) (var 0) (var 1)) (var 2)) imaginaryPoint
        (var 0*error (var 0) (var 2)) (denominator (var 0) (var 2))) :=
  closeUniv 3 (.impI (.impI (endpoint_distance _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_arctangent_partial_Cayley_telescope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) ⟶ le two (var 1) ⟶ le (var 0) (var 1) ⟶
      distanceBounded (sample (prefixValue (var 0) (var 1) (var 2)) (var 3)) (value (var 1) (var 0))
        (var 0*error (var 1) (var 3)) (denominator (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (partial_distance _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianArctangentCayleyTelescope
