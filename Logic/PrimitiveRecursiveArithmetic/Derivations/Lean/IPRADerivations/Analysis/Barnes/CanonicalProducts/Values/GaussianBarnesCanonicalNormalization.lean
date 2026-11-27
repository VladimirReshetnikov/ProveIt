import IPRADerivations.Analysis.Barnes.CanonicalProducts.FiniteProducts.GaussianBarnesCanonicalProduct
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.Taylor.GaussianGammaShiftedDeflatedZero
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalRoundedPower

/-!
# Normalization of the original Barnes product at zero

Every observation of the literal finite product is the exact rational one
at zero. The effective cutoff estimate carries this identity to the
original cofinal value, at any admitted denominator and radius.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNormalization

open_ipra
open ComplexLogarithmRemainder (normSq normSq_zero zeroCode)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalValue (nameF data prefixF)
open GaussianBarnesCanonicalProduct (literalData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_at multiplyF multiplyData multiplyModulus multiply_at)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (ofGaussian positive_product qadd qadd_canonical qmul qmul_canonical qzero)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalReciprocal (power powerF qone)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qmul_zero_left qmul_zero_right qone_canonical
  qsub_congr qzero_add qzero_canonical)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "pd" => GaussianBarnesCanonicalPrefactor.data
local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "hd" => GaussianBarnesCanonicalHead.data
local notation "F" => GaussianBarnesCanonicalFactor.nameF
local notation "rows" => GaussianNamedFiniteProductFamily.rowF F GaussianBarnesCanonicalHead.body

private theorem source_at_zero (z R B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] normSq z ≐ zero) : Γ ⊢[PRAAx] source z R B :=
  .andI hB (le_congr hz.eqSymm (.eqRefl _) (zero_le _))

private theorem multiply_sample (f g : PR 2) (p x y : PTm n) :
    let s := GaussianFastValueCut.exponent (multiplyModulus f g x y) p
    Γ ⊢[PRAAx] ap2 (multiplyF f g) p (multiplyData f g x y) ≐ qmul (ap2 f s x) (ap2 g s y) :=
  (multiply_at f g x y p).eqTrans (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _))

private theorem add_sample (f g : PR 2) (p x y : PTm n) :
    let s := GaussianFastValueCut.exponent two p
    Γ ⊢[PRAAx] ap2 (addF f g) p (addData x y) ≐ qadd (ap2 f s x) (ap2 g s y) :=
  (add_at f g x y p).eqTrans (GaussianExponentialReference.recode_fixed _ (qadd_canonical _ _))

private theorem exponential_sample (f : PR 2) (p R x : PTm n)
    (h : Γ ⊢[PRAAx] ap2 f (GaussianRadiusExponentialName.inputPrecision R p) x ≐ qzero) :
    Γ ⊢[PRAAx] ap2 (GaussianRadiusExponentialName.nameF f) p (GaussianRadiusExponentialName.data R x) ≐ qone :=
  (GaussianRadiusExponentialName.sample_at f R p x).eqTrans
    ((GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody
      (.eqRefl _) h).eqTrans (GaussianGammaCanonicalTailExponential.scalar_zero_point _))

theorem factor_sample (p z R B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hk : Γ ⊢[PRAAx] le one k) (hz : Γ ⊢[PRAAx] normSq z ≐ zero) :
    Γ ⊢[PRAAx] ap2 F p (GaussianBarnesCanonicalFactor.data z R B k) ≐ qone := by
  let s := GaussianBarnesCanonicalFactor.clock p z R B k
  let T := GaussianBarnesCanonicalFactor.exponentRadius R
  have rowFraction := GaussianGammaShiftedDeflatedZero.zero_fraction z (B*k) (positive_product _ _ hB hk) hz
  have baseOne : Γ ⊢[PRAAx] GaussianBarnesCanonicalFactor.base z B k ≐ qone :=
    (qadd_congr (.eqRefl _) rowFraction).eqTrans
      (GaussianNameRingLaws.add_zero_recode qone |>.eqTrans (GaussianExponentialReference.recode_fixed _ qone_canonical))
  have powered : Γ ⊢[PRAAx] GaussianBarnesCanonicalFactor.powerValue z B k ≐ qone :=
    (congrAp2 powerF (.eqRefl k) baseOne).eqTrans (GaussianRationalRoundedPower.qone_power k)
  have fraction := GaussianGammaShiftedDeflatedZero.zero_fraction z B hB hz
  have correctionZero : Γ ⊢[PRAAx] GaussianBarnesCanonicalFactor.correction z B k ≐ qzero :=
    (qsub_congr ((qmul_congr fraction (.eqRefl _)).eqTrans (qmul_zero_left _)) fraction).eqTrans
      (GaussianRationalReconstruction.qsub_zero_right qzero qzero_canonical)
  have c := constant_at (GaussianRadiusExponentialName.inputPrecision T s) _ |>.eqTrans correctionZero
  have e := exponential_sample constantF s T (GaussianBarnesCanonicalFactor.correction z B k) c
  exact (GaussianBarnesCanonicalFactor.sample_at p z R B k).eqTrans
    ((qmul_congr powered e).eqTrans (GaussianReciprocalHorner.qmul_one_right qone qone_canonical))

private theorem linear_sample (p z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] normSq z ≐ zero) :
    Γ ⊢[PRAAx] ap2 GaussianBarnesCanonicalPrefactor.linearF p (GaussianBarnesCanonicalPrefactor.linearData z B) ≐ qzero := by
  let C := GaussianStirlingConstant.nameF
  let a := ofGaussian z B
  let x : PTm n := GaussianStirlingConstant.nameData zero
  let s := GaussianFastValueCut.exponent (multiplyModulus constantF C a x) p
  have w := GaussianGammaShiftedDeflatedZero.zero_fraction z B hB hz
  exact (multiply_sample constantF C p a x).eqTrans
    ((qmul_congr ((constant_at s a).eqTrans w) (.eqRefl _)).eqTrans (qmul_zero_left _))

private theorem polynomial_sample (p z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] normSq z ≐ zero) :
    Γ ⊢[PRAAx] ap2 GaussianBarnesCanonicalPrefactor.polynomialF p (GaussianBarnesCanonicalPrefactor.polynomialData z B) ≐ qzero := by
  let C := GaussianBarnesCanonicalPrefactor.quadraticCoefficientF
  let x : PTm n := GaussianBarnesCanonicalPrefactor.quadraticCoefficientData
  let a := ofGaussian z B
  let v := qmul a a
  let t := GaussianFastValueCut.exponent two p
  let s := GaussianFastValueCut.exponent (multiplyModulus constantF C v x) t
  have e := GaussianGammaShiftedDeflatedZero.zero_fraction z B hB hz
  have square := (qmul_congr e (.eqRefl a)).eqTrans (qmul_zero_left a)
  have quadratic := (multiply_sample constantF C t v x).eqTrans
    ((qmul_congr ((constant_at s v).eqTrans square) (.eqRefl _)).eqTrans (qmul_zero_left _))
  exact (add_sample constantF (multiplyF constantF C) p a (multiplyData constantF C v x)).eqTrans
    ((qadd_congr ((constant_at t a).eqTrans e) quadratic).eqTrans (qzero_add qzero qzero_canonical))

private theorem correction_sample (p z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] normSq z ≐ zero) :
    Γ ⊢[PRAAx] ap2 GaussianBarnesCanonicalPrefactor.correctionF p (GaussianBarnesCanonicalPrefactor.correctionData z B) ≐ qzero := by
  let C := GaussianBarnesCanonicalPrefactor.polynomialF
  let a : PTm n := GaussianBarnesCanonicalPrefactor.negativeHalf
  let x := GaussianBarnesCanonicalPrefactor.polynomialData z B
  let s := GaussianFastValueCut.exponent (multiplyModulus constantF C a x) p
  exact (multiply_sample constantF C p a x).eqTrans
    ((qmul_congr (.eqRefl _) (polynomial_sample s z B hB hz)).eqTrans (qmul_zero_right _))

theorem prefactor_sample (p z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] normSq z ≐ zero) :
    Γ ⊢[PRAAx] ap2 P p (pd z B) ≐ qone := by
  let L := GaussianBarnesCanonicalPrefactor.linearF
  let C := GaussianBarnesCanonicalPrefactor.correctionF
  let T := GaussianBarnesCanonicalPrefactor.radius z B
  let LF := GaussianRadiusExponentialName.nameF L
  let CF := GaussianRadiusExponentialName.nameF C
  let x := GaussianBarnesCanonicalPrefactor.linearData z B
  let y := GaussianBarnesCanonicalPrefactor.correctionData z B
  let X := GaussianRadiusExponentialName.data T x
  let Y := GaussianRadiusExponentialName.data T y
  let s := GaussianFastValueCut.exponent (multiplyModulus LF CF X Y) p
  let t := GaussianRadiusExponentialName.inputPrecision T s
  have a := exponential_sample L s T x (linear_sample t z B hB hz)
  have b := exponential_sample C s T y (correction_sample t z B hB hz)
  exact (multiply_sample LF CF p X Y).eqTrans
    ((qmul_congr a b).eqTrans (GaussianReciprocalHorner.qmul_one_right qone qone_canonical))

private theorem raw_head_sample (p z R B N r : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] normSq z ≐ zero) :
    Γ ⊢[PRAAx] GaussianNamedFiniteProduct.sample rows p r (GaussianBarnesCanonicalHead.parameters z R B N) ≐ qone := by
  let sh (u : PTm n) := Syn.shift u
  let x := GaussianBarnesCanonicalHead.parameters z R B N
  let law (i : PTm (n+1)) : Fm PTm (n+1) := GaussianNamedFiniteProduct.sample rows (sh p) i (sh x) ≐ qone
  have all : Γ ⊢[PRAAx] .all (law (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [law,sh,Fm.subst_eq,GaussianNamedFiniteProduct.subst_sample,GaussianRationalReciprocal.subst_qone,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using GaussianNamedFiniteProduct.sample_zero rows p x
    · let Δ := law (var 0) :: Γ.map Fm.shift
      let j : PTm (n+1) := var 0
      have hB' : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hB.shift.wk
      have hz' : Δ ⊢[PRAAx] normSq (sh z) ≐ zero := by simpa [Δ,sh,Fm.shift,Syn.shift] using hz.shift.wk
      have hi : Δ ⊢[PRAAx] law j := Prf.hyp0
      let k := succ (sh N+j)
      have hrow := factor_sample (sh p) (sh z) (sh R) (sh B) k hB' (zero_lt_succ _) hz'
      have e : Δ ⊢[PRAAx] ap3 rows (sh p) j (sh x) ≐ qone := by
        simpa only [x,sh,Syn.shift,GaussianBarnesCanonicalHead.subst_parameters] using
          (GaussianBarnesCanonicalHead.factor_at (sh p) j (sh z) (sh R) (sh B) (sh N)).eqTrans hrow
      simpa only [law,sh,Fm.subst_eq,GaussianNamedFiniteProduct.subst_sample,GaussianRationalReciprocal.subst_qone,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
          (GaussianNamedFiniteProduct.sample_succ rows (sh p) j (sh x)).eqTrans
            ((qmul_congr hi e).eqTrans (GaussianReciprocalHorner.qmul_one_right qone qone_canonical))
  simpa only [law,sh,Fm.subst_eq,GaussianNamedFiniteProduct.subst_sample,GaussianRationalReciprocal.subst_qone,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r

theorem head_sample (p z R B N r : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] normSq z ≐ zero) :
    Γ ⊢[PRAAx] ap2 H p (hd z R B N r) ≐ qone :=
  (GaussianBarnesCanonicalHead.sample_at p z R B N r).eqTrans (raw_head_sample _ z R B N r hB hz)

theorem literal_sample (p z R B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] normSq z ≐ zero) :
    Γ ⊢[PRAAx] ap2 prefixF p (literalData z R B N) ≐ qone := by
  let x := pd z B
  let y := hd z R B zero N
  let s := GaussianFastValueCut.exponent (multiplyModulus P H x y) p
  exact (multiply_sample P H p x y).eqTrans
    ((qmul_congr (prefactor_sample s z B hB hz) (head_sample s z R B zero N hB hz)).eqTrans
      (GaussianReciprocalHorner.qmul_one_right qone qone_canonical))

theorem literal_cross (z R B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] normSq z ≐ zero) :
    Γ ⊢[PRAAx] crossEquivalent prefixF constantF (literalData z R B N) qone := by
  apply GaussianNameConjugation.equal_samples_cross prefixF constantF (literalData z R B N) qone
    (GaussianBarnesCanonicalProduct.literal_regular z R B N (source_at_zero z R B hB hz)) (constant_regular _)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  have hB' : Δ ⊢[PRAAx] le one (Syn.shift B) := by simpa [Δ,Fm.shift,Syn.shift,one] using hB.shift
  have hz' : Δ ⊢[PRAAx] normSq (Syn.shift z) ≐ zero := by simpa [Δ,Fm.shift,Syn.shift] using hz.shift
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianBarnesCanonicalProduct.subst_literalData,
    GaussianRationalReciprocal.subst_qone] using
    (literal_sample (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) hB' hz').eqTrans
      (constant_at (var 0) qone).eqSymm

theorem normalization (z R B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] normSq z ≐ zero) :
    Γ ⊢[PRAAx] crossEquivalent nameF constantF (data z R B) qone := by
  let x := data z R B
  apply GaussianNameRingLaws.equivalent_of_envelope nameF constantF x qone (num 3)
    (GaussianBarnesCanonicalValue.regular z R B (source_at_zero z R B hB hz)) (constant_regular _)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let Z := Syn.shift z
  let R' := Syn.shift R
  let D := Syn.shift B
  let p : PTm (n+1) := var 0
  let U := unit p
  let N := GaussianBarnesCanonicalProduct.cutoff p Z R' D
  have hD : Δ ⊢[PRAAx] le one D := by simpa [Δ,D,Fm.shift,Syn.shift,one] using hB.shift
  have z0 : Δ ⊢[PRAAx] normSq Z ≐ zero := by simpa [Δ,Z,Fm.shift,Syn.shift] using hz.shift
  have hu := unit_positive (Γ := Δ) p
  have hsq := positive_product _ _ hu hu
  have rate := GaussianNamedInverseRate.diagonal_rate prefixF nameF (literalData Z R' D N) (data Z R' D)
    one U p hu (GaussianBarnesCanonicalProduct.cutoff_rate p Z R' D (source_at_zero Z R' D hD z0))
  have budget : Δ ⊢[PRAAx] le ((one*U+two*U)*U) (num 3*(U*U)) :=
    le_of_eq_add (d := zero) (by ipra_ring)
  have d := distance_radius_mono _ _ _ _ (num 3) U hsq hu budget rate
  have estimate := distance_congr (.eqRefl _) ((literal_sample p Z R' D N hD z0).eqTrans (constant_at p qone).eqSymm)
    (.eqRefl _) (.eqRefl _) (distance_symmetric _ _ _ _ hu d)
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,x,Z,R',D,p,U,Syn.shift,
    GaussianBarnesCanonicalValue.subst_data,GaussianRationalReciprocal.subst_qone,
    LeanProofs.IPRA.PTm.subst_num] using estimate

theorem actual_Barnes_literal_product_at_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ crossEquivalent prefixF constantF (literalData zeroCode (var 0) (var 1) (var 2)) qone) :=
  closeUniv 3 (.impI (literal_cross zeroCode _ _ _ Prf.hyp0 normSq_zero))

theorem actual_Barnes_G_one_equals_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ crossEquivalent nameF constantF (data zeroCode (var 0) (var 1)) qone) :=
  closeUniv 2 (.impI (normalization zeroCode _ _ Prf.hyp0 normSq_zero))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNormalization
