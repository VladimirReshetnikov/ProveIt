import IPRADerivations.Analysis.RationalArithmetic.Fibers.GaussianRationalFiberRightInverse
import IPRADerivations.Analysis.Series.Telescoping.GaussianRationalParameterTelescope
import IPRADerivations.Analysis.Stirling.Expansions.GaussianStirlingOddCoefficients

/-!
# The exact mean of the centered unit mesh

The signed left tags `i/N - 1/2` have sum `-1/2`.
Their primitive for the finite forward difference is
`i(i-N-1)/(2N)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeCenteredMesh

open_ipra
open ComplexLogarithmRemainder (code oneCode scale)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner
  (canonical_unique ofGaussian ofGaussian_represents positive_product represents_congr represents_rescale)
open GaussianRationalMetric (qnegative qsub qsub_represents qsub_canonical)
open GaussianRationalRiemannRefinement (leftSum weight)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRootAlgebra (equal equal_of_values re_sub re_scale re_one im_sub im_scale im_one)
open GaussianStirlingOddCoefficients (fraction_equal fraction_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def centered (i N : PTm n) : PTm n := qsub (fraction i N) (fraction one two)
def body : PTm 2 := centered (var 0) (var 1)

ipra_subst centered [one, two]

private def polyNative (i N : PTm n) : PTm n :=
  code (ZT.ofNat (i*i) - ZT.ofNat (i*succ N)) (ZT.ofNat zero)
private def poly (i N : PTm n) : PTm n := ofGaussian (polyNative i N) (two*N)
private def polyBody : PTm 2 := poly (var 0) (var 1)

private theorem poly_at (i N : PTm n) : inst2 polyBody i N = poly i N := by
  simp [polyBody,poly,polyNative,inst2,two]

theorem centered_at (i N : PTm n) : inst2 body i N = centered i N := by simp [body,inst2]

private theorem row (i N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] qsub (poly (succ i) N) (poly i N) ≐ centered i N := by
  let E := two*N
  let a := polyNative (succ i) N
  let b := polyNative i N
  let u := scale two (scale i oneCode)
  let v := scale N (scale one oneCode)
  have h₂ : Γ ⊢[PRAAx] le one (two : PTm n) := RationalAlgebra.two_positive
  have hE := positive_product two N h₂ hN
  have left := qsub_represents (poly (succ i) N) (poly i N) a b E hE
    (ofGaussian_represents a E hE) (ofGaussian_represents b E hE)
  have first := represents_rescale (fraction i N) (scale i oneCode) N two (ofGaussian_represents _ _ hN)
  have second := represents_rescale (fraction one two) (scale one oneCode) two N (ofGaussian_represents _ _ h₂)
  have right := qsub_represents (fraction i N) (fraction one two) u v E hE
    (represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl u) (mul_comm N two) first) second
  have e : Γ ⊢[PRAAx] equal (GaussianRootAlgebra.sub a b) (GaussianRootAlgebra.sub u v) := by
    apply equal_of_values <;>
      simp only [a,b,u,v,polyNative,re_sub,im_sub,re_scale,im_scale,re_one,im_one,
        ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_sub,ZT.toZ_ofNat] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ _ (qsub_canonical _ _) (qsub_canonical _ _) hE
    (represents_congr (.eqRefl _) e (.eqRefl _) left) right

private theorem endpoint (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] qsub (poly N N) (poly zero N) ≐ qnegative (fraction one two) := by
  let E := two*N
  let a := polyNative N N
  let b := polyNative zero N
  let d := scale N (scale one oneCode)
  have h₂ : Γ ⊢[PRAAx] le one (two : PTm n) := RationalAlgebra.two_positive
  have hE := positive_product two N h₂ hN
  have left := qsub_represents (poly N N) (poly zero N) a b E hE
    (ofGaussian_represents a E hE) (ofGaussian_represents b E hE)
  have right := GaussianRationalMetric.qnegative_represents (fraction one two) d E
    (represents_rescale (fraction one two) (scale one oneCode) two N (ofGaussian_represents _ _ h₂))
  have e : Γ ⊢[PRAAx] equal (GaussianRootAlgebra.sub a b) (ComplexLogarithmRemainder.neg d) := by
    apply equal_of_values <;>
      simp only [a,b,d,polyNative,re_sub,im_sub,re_scale,im_scale,re_one,im_one,
        GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg,
        ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_sub,ZT.toZ_ofNat] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ _ (qsub_canonical _ _) (GaussianRationalMetric.qnegative_canonical _) hE
    (represents_congr (.eqRefl _) e (.eqRefl _) left) right

theorem sum_centered (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] sum body N N ≐ qnegative (fraction one two) := by
  let f := GaussianRationalParameterTelescope.forward polyBody
  have replace : Γ ⊢[PRAAx] sum body N N ≐ sum f N N := by
    apply GaussianRationalFiniteSum.sum_congr_bounded
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift N)::Γ.map Fm.shift
    have hn : Δ ⊢[PRAAx] le one (Syn.shift N) := by simpa [Δ,Fm.shift,Syn.shift,one] using hN.shift.wk
    simpa only [Δ,f,Syn.shift,centered_at,GaussianRationalParameterTelescope.forward_at,poly_at] using
      (row (var 0) (Syn.shift N) hn).eqSymm
  have e : Γ ⊢[PRAAx] sum f N N ≐ qsub (poly N N) (poly zero N) := by
    simpa only [f,poly_at] using GaussianRationalParameterTelescope.forward_sum (Γ := Γ) polyBody N N
  exact replace.eqTrans (e.eqTrans (endpoint N hN))

theorem unit_weight (N D : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] weight D D N ≐ fraction one N :=
  fraction_equal D (D*N) one N (positive_product _ _ hD hN) hN (by ipra_ring)

theorem centered_mean (N D : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] leftSum body N N D D ≐ qnegative (fraction one (two*N)) := by
  have h₂ : Γ ⊢[PRAAx] le one (two : PTm n) := RationalAlgebra.two_positive
  exact (qmul_congr (unit_weight N D hN hD) (sum_centered N hN)).eqTrans
    ((GaussianRationalFiberRightInverse.multiply_negative_right _ _).eqTrans
      (GaussianInverseBinomialRows.negative_congr
        ((fraction_product _ _ _ _ hN h₂).eqTrans
          (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (mul_comm N two)))))

theorem actual_centered_left_grid_mean_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((le one (var 0) ⋏ le one (var 1)) ⟶
        leftSum body (var 0) (var 0) (var 1) (var 1) ≐ qnegative (fraction one (two*var 0))) :=
  closeUniv 2 (.impI (centered_mean _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRaabeCenteredMesh
