import IPRADerivations.Analysis.Barnes.Deflation.GaussianBarnesCanonicalDeflatedFactor
import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.GaussianGammaEulerHeadQuadratic
import IPRADerivations.Analysis.Integration.Quadrature.GaussianRationalQuadratureDifference
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialMajorant
import IPRADerivations.Core.CongruenceTactic

/-!
# Exact finite shift of the original Barnes factor exponents

At index k the correction changes by `(z+1/2)/k-1`. The sum of
these changes uses the original Euler harmonic point at the common
cutoff. All equalities compare Gaussian rational codes.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCorrectionShift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode zeroCode mul)
open GaussianBarnesCanonicalFactor (correction)
open GaussianGammaCanonicalExponent (harmonicPoint)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaHarmonicIncrement (reciprocalPoint harmonic_point_increment)
open GaussianRationalFiniteSum (multiplyBody multiply_body_at)
open GaussianRationalHorner (ofGaussian qmul qadd qzero represents represents_congr represents_rescale
  canonical_unique ofGaussian_canonical ofGaussian_represents qmul_represents qadd_canonical positive_product)
open GaussianRationalMetric (qsub qsub_canonical qsub_represents)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at finite_sum_difference)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr qsub_congr qone_canonical)
open GaussianRootAlgebra (sub equal_refl equal_of_values re_add im_add re_mul im_mul re_scale im_scale re_sub im_sub
  re_one im_one re_zero im_zero)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "rsum" => GaussianRationalFiniteSum.sum

def halfShift (z B : PTm n) : PTm n := ofGaussian (translated (scale two z) B one) (two*B)
def exponent (z B N : PTm n) : PTm n := qsub (qmul (halfShift z B) (harmonicPoint N)) (naturalPoint N)
def parameters (z B : PTm n) : PTm n := pairT z B
def body : PTm 2 := correction (fstT (var 1)) (sndT (var 1)) (succ (var 0))
def total (z B N : PTm n) : PTm n := rsum body N (parameters z B)

@[simp] theorem subst_parameters {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (parameters z B) = parameters (Syn.subst σ z) (Syn.subst σ B) := by simp [parameters]

@[simp] theorem subst_halfShift {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (halfShift z B) = halfShift (Syn.subst σ z) (Syn.subst σ B) := by simp [halfShift,two,one]

@[simp] theorem subst_exponent {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (exponent z B N) = exponent (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by simp [exponent]

@[simp] theorem subst_total {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (total z B N) = total (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by simp [total]

theorem body_at (i z B : PTm n) : Γ ⊢[PRAAx] inst2 body i (parameters z B) ≐ correction z B (succ i) := by
  change Γ ⊢[PRAAx] inst2 body i (pairT z B) ≐ correction z B (succ i)
  simp only [body,inst2,GaussianBarnesCanonicalFactor.subst_correction,subst_fstT,subst_sndT,
    ConciseIPRA.PTm.subst_succ,Syn.subst_var,Matrix.cons_val]
  ipra_congr (correction (var 0) (var 1) (var 2) : PTm 3) with
    [fst_pair z B, snd_pair z B, .eqRefl (succ i)]

theorem correction_represents (z B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] represents (correction z B k) (sub (mul z z) (scale (two*(B*k)) z)) (B*(two*(B*k))) := by
  let E := two*(B*k)
  have hE := positive_product two (B*k) (le_succ_self one) (positive_product B k hB hk)
  have hz := ofGaussian_represents z B hB
  exact qsub_represents _ _ _ _ _ (positive_product B E hB hE)
    (qmul_represents _ _ z z B E hB hE hz (ofGaussian_represents z E hE))
    (represents_rescale _ _ B E hz)

theorem row_shift (z B i : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qsub (correction (translated z B one) B (succ i)) (correction z B (succ i)) ≐
      qsub (qmul (halfShift z B) (reciprocalPoint i)) qone := by
  let k := succ i
  let w := translated z B one
  let a := translated (scale two z) B one
  let E := two*(B*k)
  let D := B*E
  let c := sub (mul w w) (scale E w)
  let d := sub (mul z z) (scale E z)
  have hk := zero_lt_succ (Γ := Γ) i
  have hA := positive_product two B (le_succ_self one) hB
  have hE := positive_product two (B*k) (le_succ_self one) (positive_product B k hB hk)
  have hD := positive_product B E hB hE
  have lhs := qsub_represents _ _ c d D hD (correction_represents w B k hB hk) (correction_represents z B k hB hk)
  have p := qmul_represents (halfShift z B) (reciprocalPoint i) a oneCode (two*B) k hA hk
    (ofGaussian_represents a (two*B) hA) (ofGaussian_represents oneCode k hk)
  have pp := represents_rescale _ _ ((two*B)*k) B p
  have moved : Γ ⊢[PRAAx] represents (qmul (halfShift z B) (reciprocalPoint i)) (scale B (mul a oneCode)) D :=
    represents_congr (.eqRefl _) (equal_refl _) (by dsimp only [D,E]; ipra_ring) pp
  have rhs := qsub_represents _ _ _ _ D hD moved (GaussianRationalReciprocal.qone_represents_scaled D)
  apply canonical_unique _ _ _ D (qsub_canonical _ _) (qsub_canonical _ _) hD lhs
  apply represents_congr (.eqRefl _) _ (.eqRefl _) rhs
  apply equal_of_values <;> simp only [c,d,a,w,D,E,translated,re_add,im_add,re_mul,im_mul,re_scale,im_scale,
    re_sub,im_sub,re_one,im_one] <;> ipra_simps <;> ring

private def reciprocalBody : PTm 2 := reciprocalPoint (var 0)
private def unitBody : PTm 2 := qone

private theorem reciprocal_at (i x : PTm n) : inst2 reciprocalBody i x = reciprocalPoint i := by
  simp [inst2,reciprocalBody]

private theorem unit_at (i x : PTm n) : inst2 unitBody i x = qone := by
  simp [inst2,unitBody]

private theorem reciprocal_sum (N : PTm n) : Γ ⊢[PRAAx] rsum reciprocalBody N zero ≐ harmonicPoint N := by
  have h : Γ ⊢[PRAAx] .all (rsum reciprocalBody (var 0) zero ≐ harmonicPoint (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,GaussianRationalFiniteSum.subst_sum,GaussianGammaCanonicalExponent.subst_harmonicPoint,
        ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero]
      exact (GaussianRationalFiniteSum.sum_zero _ _).eqTrans GaussianGammaEulerHeadQuadratic.harmonic_zero.eqSymm
    · simp only [Fm.subst_eq,GaussianRationalFiniteSum.subst_sum,GaussianGammaCanonicalExponent.subst_harmonicPoint,
        ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.repl_zero]
      have e := GaussianRationalFiniteSum.sum_succ (Γ := (rsum reciprocalBody (var 0) zero ≐ harmonicPoint (var 0)) :: Γ.map Fm.shift)
        reciprocalBody (var 0) zero
      rw [reciprocal_at] at e
      exact e.eqTrans ((qadd_congr Prf.hyp0 (.eqRefl (reciprocalPoint (var 0)))).eqTrans (harmonic_point_increment _).eqSymm)
  simpa only [Fm.subst_eq,GaussianRationalFiniteSum.subst_sum,GaussianGammaCanonicalExponent.subst_harmonicPoint,
    ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero] using h.allE N

private theorem natural_zero : Γ ⊢[PRAAx] naturalPoint (zero : PTm n) ≐ qzero := by
  refine canonical_unique _ _ zeroCode one (ofGaussian_canonical _ _ (le_refl one))
    GaussianRationalSyntheticDivision.qzero_canonical (le_refl one) ?_ (GaussianRationalHorner.zero_represents one)
  refine represents_congr (.eqRefl _) ?_ (.eqRefl _) (natural_point_represents zero)
  apply equal_of_values <;> simp only [re_scale,im_scale,re_zero,im_zero] <;> ipra_simps <;> ring

private theorem natural_one : Γ ⊢[PRAAx] naturalPoint (one : PTm n) ≐ qone := by
  refine canonical_unique _ _ oneCode one (ofGaussian_canonical _ _ (le_refl one)) qone_canonical (le_refl one) ?_
    (ofGaussian_represents oneCode one (le_refl one))
  refine represents_congr (.eqRefl _) ?_ (.eqRefl _) (natural_point_represents one)
  apply equal_of_values <;> simp only [re_scale,im_scale] <;> ipra_simps <;> ring

private theorem unit_sum (N : PTm n) : Γ ⊢[PRAAx] rsum unitBody N zero ≐ naturalPoint N := by
  have h : Γ ⊢[PRAAx] .all (rsum unitBody (var 0) zero ≐ naturalPoint (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,GaussianRationalFiniteSum.subst_sum,GaussianRationalNaturalScale.subst_naturalPoint,
        ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero]
      exact (GaussianRationalFiniteSum.sum_zero _ _).eqTrans natural_zero.eqSymm
    · simp only [Fm.subst_eq,GaussianRationalFiniteSum.subst_sum,GaussianRationalNaturalScale.subst_naturalPoint,
        ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.repl_zero]
      refine (GaussianRationalFiniteSum.sum_succ unitBody (var 0) zero).eqTrans ?_
      rw [unit_at]
      exact (qadd_congr Prf.hyp0 natural_one.eqSymm).eqTrans
        (GaussianPositiveExponentialMajorant.natural_successor_sum _)
  simpa only [Fm.subst_eq,GaussianRationalFiniteSum.subst_sum,GaussianRationalNaturalScale.subst_naturalPoint,
    ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero] using h.allE N

theorem total_shift (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qsub (total (translated z B one) B N) (total z B N) ≐ exponent z B N := by
  let w := translated z B one
  let x := parameters w B
  let y := parameters z B
  let a := halfShift z B
  let u := multiplyBody reciprocalBody
  let X := pairT a zero
  let lhs := differenceBody body body
  let rhs := differenceBody u unitBody
  have rows : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual lhs rhs N (pairT x y) (pairT X zero) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    let Z := Syn.shift z
    let B' := Syn.shift B
    let j : PTm (n+1) := var 0
    let W := translated Z B' one
    let A := halfShift Z B'
    have hb : Δ ⊢[PRAAx] le one B' := by simpa [Fm.shift,Syn.shift,Δ,B',one] using hB.shift.wk
    have left := (difference_body_at (Γ := Δ) body body j (parameters W B') (parameters Z B')).eqTrans
      (qsub_congr (body_at j W B') (body_at j Z B'))
    have right := difference_body_at (Γ := Δ) u unitBody j (pairT A zero) zero
    have product := multiply_body_at (Γ := Δ) reciprocalBody A j zero
    rw [unit_at] at right
    rw [reciprocal_at] at product
    simpa only [Syn.shift,subst_parameters,GaussianGammaEulerHeadLower.subst_translated,subst_pairT,subst_halfShift,
      ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,x,y,w,X,a,Z,B',j,W,A,Δ,lhs,rhs,one] using
      left.eqTrans ((row_shift Z B' j hb).eqTrans ((right.eqTrans (qsub_congr product (.eqRefl qone))).eqSymm))
  exact (finite_sum_difference body body N x y).eqSymm.eqTrans ((GaussianRationalFiniteSum.sum_congr_bounded lhs rhs N _ _ rows).eqTrans
    ((finite_sum_difference u unitBody N X zero).eqTrans (qsub_congr
      ((GaussianRationalFiniteSum.sum_multiply reciprocalBody a N zero).eqTrans (qmul_congr (.eqRefl a) (reciprocal_sum N)))
      (unit_sum N))))

theorem actual_Barnes_original_correction_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ qsub (total (translated (var 0) (var 1) one) (var 1) (var 2)) (total (var 0) (var 1) (var 2)) ≐
      exponent (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (total_shift _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCorrectionShift
