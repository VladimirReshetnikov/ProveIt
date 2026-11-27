import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.FirstDerivative.Cofinal.GaussianBarnesCanonicalPositiveFirstLogarithm
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.FiniteDerivatives.GaussianBarnesCanonicalThirdDerivativePositiveMargin
import IPRADerivations.Analysis.Gamma.Digamma.Series.GaussianGammaDigammaSeriesTerms

/-!
# The literal first Barnes logarithmic rows are scaled digamma rows

For positive `A/B`, let `x=(A-B)/B`. The original derivative row at
`k=i+1` equals `x*(1/k - B/(A+i*B))` at exact encoded rational
arithmetic. This includes the kept rows and gives equality of the
original full derivative prefix with the scaled literal digamma prefix.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFirstLogarithmDigammaPrefix

open_ipra
open ComplexLogarithmRemainder (scale oneCode)
open GaussianBarnesCanonicalThirdLogarithmRows (center shiftedNumerator shifted_positive base_at)
open GaussianBarnesCanonicalDerivativeRow (value offset)
open GaussianBarnesCanonicalFactor (base)
open GaussianDominantPairAlgebra (radiusPoint radiusNumerator radius_represents)
open GaussianGammaDigammaSeriesTerms (termBody partialSum)
open GaussianGammaDigammaFiniteSum (index)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalFiniteSum (sum multiplyBody termsEqual)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents canonical_unique
  represents represents_congr represents_cancel qmul qmul_represents qmul_canonical positive_product)
open GaussianRationalMetric (qsub qsub_represents)
open GaussianRationalReciprocal (reciprocal reciprocal_canonical reciprocal_identity)
open GaussianRationalSyntheticDivision (rescale_to qmul_congr qsub_congr)
open GaussianRootAlgebra (equal equal_of_values equal_refl re_scale im_scale re_one im_one
  re_mul im_mul re_sub im_sub)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "gmul" => ComplexLogarithmRemainder.mul
local notation "gsub" => GaussianRootAlgebra.sub

def coordinate (A B : PTm n) : PTm n := ofGaussian (center A B) B

@[simp] theorem subst_coordinate {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (coordinate A B) = coordinate (Syn.subst σ A) (Syn.subst σ B) := by
  simp [coordinate]

theorem reciprocal_base (A B i : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] reciprocal (base (center A B) B (succ i)) ≐ radiusPoint (B*succ i) (shiftedNumerator A B i) := by
  let a := shiftedNumerator A B i
  let d := B*succ i
  let b := base (center A B) B (succ i)
  let c := radiusPoint d a
  have ha := shifted_positive A B i hA
  have hd := positive_product B (succ i) hB (zero_lt_succ i)
  have admitBase : Γ ⊢[PRAAx] le B (B*A) := by ipra_le 𝔞 B*sl hA
  have lower := GaussianBarnesCanonicalThirdDerivativePositiveMargin.base_lower A B i B hB hB admitBase
  have nonzero := GaussianNameReciprocal.lower_norm_positive b B hB lower
  have inv := reciprocal_identity b nonzero
  have reversed := (GaussianRationalPowerAlgebra.qmul_commutative (radiusPoint a d) c).eqTrans
    (GaussianRationalTravelScaling.inverse_radius a d ha hd)
  have candidate := (qmul_congr (base_at A B i hB) (.eqRefl c)).eqTrans reversed
  exact GaussianEulerBetaProductPascal.inverse_unique _ _ _ (reciprocal_canonical _) (ofGaussian_canonical _ _ ha)
    inv candidate

private theorem difference_representation (A B i : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx] represents
      (qsub (fraction one (succ i)) (fraction B (shiftedNumerator A B i))) (center A B)
      (succ i*shiftedNumerator A B i) := by
  let k := succ i
  let d := shiftedNumerator A B i
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ i
  have hd := shifted_positive A B i hA
  have h := positive_product k d hk hd
  have left : Γ ⊢[PRAAx] represents (fraction one k) (scale d (scale one oneCode)) (k*d) :=
    rescale_to _ _ _ _ _ (ofGaussian_represents _ _ hk) (.eqRefl _)
  have right : Γ ⊢[PRAAx] represents (fraction B d) (scale k (scale B oneCode)) (k*d) :=
    rescale_to _ _ _ _ _ (ofGaussian_represents _ _ hd) (mul_comm _ _)
  have raw := qsub_represents _ _ _ _ _ h left right
  have e : Γ ⊢[PRAAx] equal (gsub (scale d (scale one oneCode)) (scale k (scale B oneCode))) (center A B) := by
    apply equal_of_values
    · simp only [re_sub,re_scale,re_one,center,ComplexLogarithmRemainder.eval_re_code,
        ZT.toZ_sub,ZT.toZ_ofNat,d,k,shiftedNumerator]
      ipra_simps
      ring
    · simp only [im_sub,im_scale,im_one,center,ComplexLogarithmRemainder.eval_im_code,
        ZT.toZ_ofNat,Q.mk_zero,map_zero]
      ring
  exact represents_congr (.eqRefl _) e (.eqRefl _) raw

theorem original_row (A B i : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] value (center A B) B (succ i) ≐
      qmul (coordinate A B) (inst2 termBody i (pairT A B)) := by
  let z := center A B
  let k := succ i
  let d := shiftedNumerator A B i
  let e := B*k
  let w := offset z B k
  let u := qmul w w
  let num := gmul z z
  let D := e*d
  let r := qsub (fraction one k) (fraction B d)
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ i
  have hd := shifted_positive A B i hA
  have he := positive_product B k hB hk
  have hD := positive_product e d he hd
  have hw : Γ ⊢[PRAAx] represents w z e := ofGaussian_represents _ _ he
  have hu := qmul_represents w w z z e e he he hw hw
  have hv := qmul_represents u (radiusPoint e d) num (radiusNumerator e) (e*e) d
    (positive_product e e he he) hd hu (radius_represents e d hd)
  have eq : Γ ⊢[PRAAx] equal (gmul num (radiusNumerator e)) (scale e num) := by
    apply equal_of_values
    · simp only [re_mul,re_scale,radiusNumerator,
        ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,
        ZT.toZ_ofNat,Q.mk_zero,map_zero]
      ring
    · simp only [im_mul,im_scale,radiusNumerator,
        ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,
        ZT.toZ_ofNat,Q.mk_zero,map_zero]
      ring
  have inv := qmul_congr (.eqRefl u) (reciprocal_base A B i hA hB)
  have actual : Γ ⊢[PRAAx] represents (value z B k) num D :=
    represents_cancel _ _ _ e he
      (represents_congr inv.eqSymm eq (by unfold D; ipra_ring) hv)
  have compact := qmul_represents (coordinate A B) r z z B (k*d) hB (positive_product k d hk hd)
    (ofGaussian_represents _ _ hB) (difference_representation A B i hA)
  have flat : Γ ⊢[PRAAx] r ≐ inst2 termBody i (pairT A B) := by
    have first := GaussianGammaDigammaStep.unit_step_value (Γ := Γ) (succ i) (zero_lt_succ i)
    exact (qsub_congr first (.eqRefl (fraction B d))).eqTrans
      (GaussianGammaDigammaSeriesTerms.term_at A B i).eqSymm
  exact canonical_unique _ _ num D (qmul_canonical _ _) (qmul_canonical _ _) hD
    actual (represents_congr (qmul_congr (.eqRefl _) flat) (equal_refl _) (by unfold D e; ipra_ring) compact)

private theorem prefix_row (A B i : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] inst2 GaussianBarnesCanonicalDerivativeTail.body i
        (GaussianBarnesCanonicalDerivativeTail.data (center A B) B zero) ≐
      inst2 (multiplyBody termBody) i (pairT (coordinate A B) (pairT A B)) := by
  have head := GaussianBarnesCanonicalDerivativeTail.body_at (Γ := Γ) (center A B) B zero i
  have same : Γ ⊢[PRAAx] value (center A B) B (succ (zero+i)) ≐ value (center A B) B (succ i) := by
    ipra_congr (value (var 0) (var 1) (var 2) : PTm 3)
      with [.eqRefl _, .eqRefl _, congrSucc (zero_add i)] using [GaussianBarnesCanonicalDerivativeRow.subst_value]
  have weighted := GaussianRationalFiniteSum.multiply_body_at (Γ := Γ) termBody (coordinate A B) i (pairT A B)
  exact head.eqTrans (same.eqTrans ((original_row A B i hA hB).eqTrans weighted.eqSymm))

theorem original_prefix (A B M : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalDerivativeTail.value (center A B) B zero M ≐
      qmul (coordinate A B) (partialSum A B M) := by
  let body := GaussianBarnesCanonicalDerivativeTail.body
  let c := coordinate A B
  let x := GaussianBarnesCanonicalDerivativeTail.data (center A B) B zero
  let y := pairT A B
  have rows : Γ ⊢[PRAAx] termsEqual body (multiplyBody termBody) M x (pairT c y) := by
    refine .allI (.impI ?_)
    let A' := Syn.shift A
    let B' := Syn.shift B
    let i : PTm (n+1) := var 0
    have hA' : (Γ.map Fm.shift) ⊢[PRAAx] le one A' := by simpa [Fm.shift,Syn.shift,A',one] using hA.shift
    have hB' : (Γ.map Fm.shift) ⊢[PRAAx] le one B' := by simpa [Fm.shift,Syn.shift,B',one] using hB.shift
    simpa only [Syn.shift,body,c,x,y,i,A',B',subst_coordinate,subst_pairT,
      GaussianBarnesCanonicalDerivativeTail.subst_data,GaussianBarnesCanonicalThirdLogarithmRows.subst_center,
      ConciseIPRA.PTm.subst_zero] using
      (prefix_row (Γ := lt i (Syn.shift M) :: Γ.map Fm.shift) A' B' i hA'.wk hB'.wk)
  exact (GaussianRationalFiniteSum.sum_congr_bounded body (multiplyBody termBody) M x (pairT c y) rows).eqTrans
    (GaussianRationalFiniteSum.sum_multiply termBody c M y)

theorem actual_Barnes_first_logarithm_digamma_prefix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (let A := var 0; let B := var 1; let M := var 2
     (le one A ⋏ le one B) ⟶ GaussianBarnesCanonicalDerivativeTail.value (center A B) B zero M ≐
       qmul (coordinate A B) (partialSum A B M)) :=
  closeUniv 3 (.impI (original_prefix _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFirstLogarithmDigammaPrefix
