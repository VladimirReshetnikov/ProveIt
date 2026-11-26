import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaPolygammaTailRows
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalSumMajorant
import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalReciprocalPowerTail

/-!
# The literal complex polygamma tail bound

The finite tail is the original sum of reciprocal Gaussian powers from
N+1 to N+r. A normalized term-by-term comparison with a scalar power
tail, followed by exact common-factor extraction, keeps the constant
2^(m+1). Restoring the derivative factorial gives the C30 bound for
each internal m ≥ 1 with N ≥ 2R and N ≥ 1.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPolygammaTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianGammaPolygammaTailRows (term normalizedTerm weight normalized_term_bound term_factor)
open GaussianPositiveRealArithmetic (numerator natural_representation)
open GaussianRationalFiniteSum (sum multiplyBody sum_multiply)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded qnegative)
open GaussianRationalReciprocal (qone power)
open GaussianRationalSumMajorant (majorized termsMajorized sum_majorized)
open GaussianEuclideanDistanceName (fraction_represents)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)
open Products (fact)
open RationalSupMetric (denominatorOf)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (z B e N : PTm n) : PTm n := pairT z (pairT B (pairT e N))
def row (i x : PTm n) : PTm n := term (fstT x) (fstT (sndT x))
  (succ (sndT (sndT (sndT x))+i)) (fstT (sndT (sndT x)))
def normalizedRow (i x : PTm n) : PTm n := normalizedTerm (fstT x) (fstT (sndT x))
  (succ (sndT (sndT (sndT x))+i)) (fstT (sndT (sndT x)))

def body : PTm 2 := row (var 0) (var 1)
def normalizedBody : PTm 2 := normalizedRow (var 0) (var 1)
def tail (z B e N r : PTm n) : PTm n := sum body r (data z B e N)
def normalizedTail (z B e N r : PTm n) : PTm n := sum normalizedBody r (data z B e N)
def derivativeTail (z B m N r : PTm n) : PTm n := qmul (radiusPoint (fact m) one) (tail z B (succ m) N r)
def signedTail (z B m N r : PTm n) : PTm n :=
  qmul (power (qnegative qone) (succ m)) (derivativeTail z B m N r)

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (z B e N : PTm n) :
    Syn.subst σ (data z B e N) = data (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ e) (Syn.subst σ N) := by
  simp [data]
@[simp] theorem subst_tail {l : ℕ} (σ : Fin n → PTm l) (z B e N r : PTm n) :
    Syn.subst σ (tail z B e N r) = tail (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ e) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [tail]
@[simp] theorem subst_derivativeTail {l : ℕ} (σ : Fin n → PTm l) (z B m N r : PTm n) :
    Syn.subst σ (derivativeTail z B m N r) =
      derivativeTail (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [derivativeTail,Products.fact,one]

private theorem read_data (z B e N : PTm n) : Γ ⊢[PRAAx]
    (fstT (data z B e N) ≐ z) ⋏ ((fstT (sndT (data z B e N)) ≐ B) ⋏
      ((fstT (sndT (sndT (data z B e N))) ≐ e) ⋏ (sndT (sndT (sndT (data z B e N))) ≐ N))) := by
  let x := data z B e N
  have y : Γ ⊢[PRAAx] sndT x ≐ pairT B (pairT e N) := snd_pair _ _
  have w := (congrSnd y).eqTrans (snd_pair B (pairT e N))
  exact .andI (fst_pair _ _) (.andI ((congrFst y).eqTrans (fst_pair _ _))
    (.andI ((congrFst w).eqTrans (fst_pair _ _)) ((congrSnd w).eqTrans (snd_pair _ _))))

theorem term_at (i z B e N : PTm n) : Γ ⊢[PRAAx] inst2 body i (data z B e N) ≐ term z B (succ (N+i)) e := by
  let x := data z B e N
  have h := read_data (Γ := Γ) z B e N
  simpa only [body,row,inst2,GaussianGammaPolygammaTailRows.subst_term,subst_fstT,subst_sndT,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,x] using
    Prf.eqCongr (term (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![fstT x,fstT (sndT x),succ (sndT (sndT (sndT x))+i),fstT (sndT (sndT x))])
      (σ' := ![z,B,succ (N+i),e]) (fun j => by
        fin_cases j
        · exact h.andE₁
        · exact h.andE₂.andE₁
        · exact congrSucc (congrAdd h.andE₂.andE₂.andE₂ (.eqRefl i))
        · exact h.andE₂.andE₂.andE₁)

theorem normalized_at (i z B e N : PTm n) : Γ ⊢[PRAAx]
    inst2 normalizedBody i (data z B e N) ≐ normalizedTerm z B (succ (N+i)) e := by
  let x := data z B e N
  have h := read_data (Γ := Γ) z B e N
  simpa only [normalizedBody,normalizedRow,inst2,GaussianGammaPolygammaTailRows.subst_normalizedTerm,subst_fstT,subst_sndT,
    PTm.subst_add,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,x] using
    Prf.eqCongr (normalizedTerm (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![fstT x,fstT (sndT x),succ (sndT (sndT (sndT x))+i),fstT (sndT (sndT x))])
      (σ' := ![z,B,succ (N+i),e]) (fun j => by
        fin_cases j
        · exact h.andE₁
        · exact h.andE₂.andE₁
        · exact congrSucc (congrAdd h.andE₂.andE₂.andE₂ (.eqRefl i))
        · exact h.andE₂.andE₂.andE₁)

private theorem row_majorant (i z R B e N : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hN : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    majorized (inst2 normalizedBody i (data z B e N))
      (inst2 RationalReciprocalPowerTail.body i (RationalReciprocalPowerTail.data e N)) := by
  let j := succ (N+i)
  have hj : Γ ⊢[PRAAx] le one j := zero_lt_succ _
  have hD := GaussianFactorBudget.power_positive (Γ := Γ) j e hj
  have bound := normalized_term_bound z R B j e hB hz
    (le_trans hN (le_trans (le_add_right N i) (le_succ_self _))) hj
  let q := RationalReciprocalPowerTail.reciprocalPower e j
  have rep : Γ ⊢[PRAAx] RationalArithmetic.represents q (ZT.ofNat one) (pw j e) :=
    fraction_represents one (pw j e) hD
  exact GaussianRationalSumMajorant.majorized_congr (normalized_at i z B e N).eqSymm
    (RationalReciprocalPowerTail.term_at e N i).eqSymm
    (GaussianRationalSumMajorant.from_representation (normalizedTerm z B j e) q one (pw j e) hD
      (GaussianRationalL1.nonnegative_of_representation _ _ _ hD rep) rep bound)

theorem normalized_bound (z R B e N r : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (he : Γ ⊢[PRAAx] le two e) (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] bounded (normalizedTail z B e N r) one (pred e*pw N (pred e)) := by
  let q := RationalReciprocalPowerTail.tail e N r
  let D := pred e*pw N (pred e)
  have hD := RationalReciprocalPowerTail.potential_denominator_positive e N he hN
  have rows : Γ ⊢[PRAAx] termsMajorized normalizedBody RationalReciprocalPowerTail.body r
      (data z B e N) (RationalReciprocalPowerTail.data e N) := by
    let Δ := Γ.map Fm.shift
    have hb : Δ ⊢[PRAAx] le one (Syn.shift B) := by simpa [Δ,Fm.shift,Syn.shift] using hB.shift
    have disk : Δ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (Syn.shift z) (Syn.shift R*Syn.shift B) :=
      by simpa [Δ,Fm.shift,Syn.shift] using hz.shift
    have wide : Δ ⊢[PRAAx] le (two*Syn.shift R) (Syn.shift N) :=
      by simpa [Δ,Fm.shift,Syn.shift] using hR.shift
    refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_data,RationalReciprocalPowerTail.subst_data] using
      row_majorant (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift e) (Syn.shift N) hb.wk disk.wk wide.wk
  have estimate : Γ ⊢[PRAAx] majorized (normalizedTail z B e N r) q :=
    sum_majorized normalizedBody RationalReciprocalPowerTail.body r _ _ rows
  have denom := RationalArgmin.denominator_positive (Γ := Γ) q
  have cleared := GaussianRationalMetric.comparison_to_cleared q (RationalReciprocalPowerTail.potential e N)
    (numerator q) one (denominatorOf q) D (natural_representation q estimate.andE₁)
    (fraction_represents one D hD) (RationalReciprocalPowerTail.sharp_tail e N r he hN)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ denom hD
    (le_congr (mul_comm _ _) (.eqRefl _) cleared) estimate.andE₂

theorem tail_factor (z B e N r : PTm n) : Γ ⊢[PRAAx]
    tail z B e N r ≐ qmul (weight e) (normalizedTail z B e N r) := by
  let x := data z B e N
  have rows : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual body (multiplyBody normalizedBody)
      r x (pairT (weight e) x) := by
    refine .allI (.impI ?_)
    let Z := Syn.shift z
    let B' := Syn.shift B
    let E := Syn.shift e
    let M := Syn.shift N
    let i : PTm (n+1) := var 0
    simpa only [Syn.shift,subst_data,subst_pairT,GaussianGammaPolygammaTailRows.weight,
      GaussianDominantPairAlgebra.subst_radiusPoint,subst_ap2,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero,Z,B',E,M,i,x,pw,one,two] using
      (term_at i Z B' E M).eqTrans ((term_factor Z B' (succ (M+i)) E).eqTrans
        ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl (weight E)) (normalized_at i Z B' E M).eqSymm).eqTrans
          (GaussianRationalFiniteSum.multiply_body_at normalizedBody (weight E) i (data Z B' E M)).eqSymm))
  have same : Γ ⊢[PRAAx] tail z B e N r ≐ sum (multiplyBody normalizedBody) r (pairT (weight e) x) :=
    GaussianRationalFiniteSum.sum_congr_bounded body (multiplyBody normalizedBody)
      (m := r) (x := x) (y := pairT (weight e) x) rows
  exact same.eqTrans (sum_multiply normalizedBody (weight e) r x)

theorem raw_tail_bound (z R B e N r : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (he : Γ ⊢[PRAAx] le two e) (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] bounded (tail z B e N r) (pw two e) (pred e*pw N (pred e)) := by
  have hD := RationalReciprocalPowerTail.potential_denominator_positive e N he hN
  exact GaussianRationalReciprocal.bound_congr (tail_factor z B e N r).eqSymm (by ipra_ring) (one_mul _)
    (GaussianRationalReciprocal.bounded_product (weight e) _ (pw two e) one one _ (le_refl one) hD
      (radius_bounded _ _ (le_refl one)) (normalized_bound z R B e N r hB hz he hN hR))

theorem C30_tail_bound (z R B m N r : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] bounded (derivativeTail z B m N r) (fact (pred m)*pw two (succ m)) (pw N m) := by
  let W := pw two (succ m)
  let T := pw N m
  have he : Γ ⊢[PRAAx] le two (succ m) := by
    ipra_le sl hm
  have hT := GaussianFactorBudget.power_positive (Γ := Γ) N m hN
  have hM := positive_product m T hm hT
  have old := GaussianRationalReciprocal.bound_congr (.eqRefl _) (.eqRefl W)
    (congrMul (pred_succ m) (congrAp2 powF (pred_succ m) (.eqRefl N)))
    (raw_tail_bound z R B (succ m) N r hB hz he hN hR)
  have prod := GaussianRationalReciprocal.bounded_product (radiusPoint (fact m) one) (tail z B (succ m) N r)
    (fact m) one W (m*T) (le_refl one) hM (radius_bounded _ _ (le_refl one)) old
  have em := GaussianOffDominantWeights.positive_succ_pred m hm
  have fm : Γ ⊢[PRAAx] fact m ≐ fact (pred m)*m :=
    (congrAp2 factF em (.eqRefl zero)).eqTrans
      ((ExponentialSeries.fact_succ' (pred m)).eqTrans (congrMul (.eqRefl _) em.eqSymm))
  have radius : Γ ⊢[PRAAx] le ((fact m*W)*T) ((fact (pred m)*W)*(one*(m*T))) := by
    apply le_of_eq_add (d := zero)
    apply deriveNat
    have eq := natEq fm
    simp only [Q.mk_mul,map_mul] at eq
    ipra_simps
    rw [eq]
    ring
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_refl one) hM) hT radius prod

theorem signed_C30_tail_bound (z R B m N r : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] bounded (signedTail z B m N r) (fact (pred m)*pw two (succ m)) (pw N m) := by
  let A := fact (pred m)*pw two (succ m)
  let D := pw N m
  let t := power (qnegative qone) (succ m)
  have hD := GaussianFactorBudget.power_positive (Γ := Γ) N m hN
  have negative : Γ ⊢[PRAAx] bounded (qnegative qone : PTm n) one one :=
    GaussianRationalReciprocal.bounded_negative _ _ _ (le_refl one) GaussianRationalReciprocal.qone_bounded
  have sign : Γ ⊢[PRAAx] bounded t one one :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (GaussianPolynomialPerturbation.one_power _) (GaussianPolynomialPerturbation.one_power _)
      (GaussianRationalReciprocal.bounded_power _ one one (succ m) (le_refl one) negative)
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (one_mul A) (one_mul D)
    (GaussianRationalReciprocal.bounded_product t _ one one A D (le_refl one) hD sign
      (C30_tail_bound z R B m N r hB hz hm hN hR))

theorem actual_original_polygamma_C30_finite_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 2) ⋏ ComplexLogarithmRemainder.bounded (var 0) (var 1*var 2)) ⟶
      (le one (var 3) ⋏ (le one (var 4) ⋏ le (two*var 1) (var 4))) ⟶
      bounded (signedTail (var 0) (var 2) (var 3) (var 4) (var 5))
        (fact (pred (var 3))*pw two (succ (var 3))) (pw (var 4) (var 3))) :=
  closeUniv 6 (.impI (.impI (signed_C30_tail_bound _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianGammaPolygammaTail
