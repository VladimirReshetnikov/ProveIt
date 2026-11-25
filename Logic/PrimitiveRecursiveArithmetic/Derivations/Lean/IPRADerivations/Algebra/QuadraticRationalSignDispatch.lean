import IPRADerivations.Algebra.QuadraticIntegerSignDispatch
import IPRADerivations.Algebra.QuadraticTowerSignCoherence
import IPRADerivations.Core.CertificateTactics

/-!
# The source native dispatch on original rational coefficients

The actual original rational arithmetic computes a^2-d*b^2. Positive
decoded denominators transport its native sign to the same integer-stage
dispatch, retaining the actual conditional third query. Only original
nonnegativity of the rational radicand is required. This supplies one
rational ground extension, not arbitrary-depth tower correctness.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticRationalSignDispatch

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis
open RationalSupMetric (numeratorOf denominatorOf)
open QuadraticSignCertificates (tag first second)
open QuadraticRationalRadicand (positiveNumerator integerRadicand stretch)
open QuadraticRationalClearing (clear denominator)
open QuadraticTowerSignRecipe (dispatch)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def scalarTag (q : PTm n) : PTm n := tag (numeratorOf q)
def norm (d x : PTm n) : PTm n := RationalArithmetic.add (RationalArithmetic.multiply (fstT x) (fstT x))
  (RationalArithmetic.negative (RationalArithmetic.multiply d (RationalArithmetic.multiply (sndT x) (sndT x))))
def nativeData (d x : PTm n) : PTm n := stretch (denominatorOf d) (clear x)
def normNumerator (d x : PTm n) : ZT n := ZT.ofNat (denominatorOf d)*(first (clear x)*first (clear x))-
  ZT.ofNat (positiveNumerator d)*(second (clear x)*second (clear x))
def third (d x : PTm n) : PTm n := sel (eqb (scalarTag (fstT x)) zero) (scalarTag d) (scalarTag (norm d x))
def recipe (d x : PTm n) : PTm n := dispatch (scalarTag (fstT x)) (scalarTag (sndT x)) (third d x)
@[simp] theorem subst_scalarTag {k : ℕ} (σ : Fin n → PTm k) (q : PTm n) :
    Syn.subst σ (scalarTag q) = scalarTag (Syn.subst σ q) := by simp [scalarTag]
@[simp] theorem subst_norm {k : ℕ} (σ : Fin n → PTm k) (d x : PTm n) :
    Syn.subst σ (norm d x) = norm (Syn.subst σ d) (Syn.subst σ x) := by simp [norm]
@[simp] theorem subst_nativeData {k : ℕ} (σ : Fin n → PTm k) (d x : PTm n) :
    Syn.subst σ (nativeData d x) = nativeData (Syn.subst σ d) (Syn.subst σ x) := by simp [nativeData,stretch]
@[simp] theorem subst_normNumerator {k : ℕ} (σ : Fin n → PTm k) (d x : PTm n) :
    (normNumerator d x).subst σ = normNumerator (Syn.subst σ d) (Syn.subst σ x) := by simp [normNumerator]
@[simp] theorem subst_third {k : ℕ} (σ : Fin n → PTm k) (d x : PTm n) :
    Syn.subst σ (third d x) = third (Syn.subst σ d) (Syn.subst σ x) := by simp [third,sel]
@[simp] theorem subst_recipe {k : ℕ} (σ : Fin n → PTm k) (d x : PTm n) :
    Syn.subst σ (recipe d x) = recipe (Syn.subst σ d) (Syn.subst σ x) := by simp [recipe]

/-- Any actual positive-denominator representation determines the native
numerator sign; no canonical scalar-code premise is needed. -/
theorem tag_of_representation (q D : PTm n) (a : ZT n) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] RationalArithmetic.represents q a D) : Γ ⊢[PRAAx] scalarTag q ≐ tag a :=
  (QuadraticRationalEmbedding.embedding_sign one q (le_refl one)).eqSymm.eqTrans
    ((QuadraticRationalClearing.representation_sign one (QuadraticRationalEmbedding.embed q)
      (QuadraticIntegerEmbedding.integer a) D (le_refl one) hD
      (QuadraticRationalEmbedding.embedding_represents q D a hq)).eqTrans
        (QuadraticIntegerEmbedding.integer_sign one a (le_refl one)))

theorem tag_positive_scale (k : PTm n) (a : ZT n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    tag (ZT.ofNat k*a) ≐ tag a := by
  have eq : Γ ⊢[PRAAx] QuadraticSignCertificates.equal (QuadraticIntegerEmbedding.integer (ZT.ofNat k*a))
      (QuadraticPositiveScaling.scale k (QuadraticIntegerEmbedding.integer a)) := by
    apply QuadraticConeOrder.equal_of_values
    · simp only [QuadraticIntegerEmbedding.integer_first,QuadraticPositiveScaling.scale_first,ZT.toZ_mul,ZT.toZ_ofNat]
    · simp only [QuadraticIntegerEmbedding.integer_second,QuadraticPositiveScaling.scale_second]
      ring
  exact (QuadraticIntegerEmbedding.integer_sign one _ (le_refl one)).eqSymm.eqTrans
    ((QuadraticConeOrder.sign_congr one _ _ (le_refl one) eq).eqTrans
      ((QuadraticPositiveScaling.sign_scale one k _ (le_refl one) hk).eqTrans
        (QuadraticIntegerEmbedding.integer_sign one a (le_refl one))))

theorem radicand_representation (d : PTm n) (hd : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative d) : Γ ⊢[PRAAx]
    RationalArithmetic.represents d (ZT.ofNat (positiveNumerator d)) (denominatorOf d) := by
  have negZero := QuadraticSignCertificates.negative_part_zero (numeratorOf d) hd
  have value : ZT.toZ Γ (numeratorOf d) = 𝔞(positiveNumerator d) := by
    rw [QuadraticSignCertificates.parts_value,natEq negZero]
    simp [positiveNumerator]
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,value]

theorem norm_representation (d x : PTm n) (hd : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative d) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (norm d x)
      (ZT.ofNat (denominator x*denominator x)*normNumerator d x)
      ((denominator x*denominator x)*(denominatorOf d*(denominator x*denominator x))) := by
  have source := QuadraticRationalClearing.clear_represents (Γ := Γ) x
  have aa := RationalRepresentations.represents_multiply _ _ _ _ _ _ (Prf.andE₁ source) (Prf.andE₁ source)
  have bb := RationalRepresentations.represents_multiply _ _ _ _ _ _ (Prf.andE₂ source) (Prf.andE₂ source)
  have dbb := RationalRepresentations.represents_multiply _ _ _ _ _ _ (radicand_representation d hd) bb
  have neg := RationalRepresentations.represents_negative _ _ _ dbb
  have total := RationalRepresentations.represents_add _ _ _ _ _ _ aa neg
  apply QuadraticRationalPairArithmetic.scalar_value_congr _ _ _ _ _ total
  simp only [normNumerator,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_mul,map_mul]
  ring

theorem denominator_square_positive (x : PTm n) : Γ ⊢[PRAAx] le one (denominator x*denominator x) :=
  RationalAlgebra.positive_product (QuadraticRationalClearing.denominator_positive x) (QuadraticRationalClearing.denominator_positive x)
theorem norm_tag (d x : PTm n) (hd : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative d) : Γ ⊢[PRAAx]
    scalarTag (norm d x) ≐ tag (normNumerator d x) :=
  (tag_of_representation _ _ _
    (RationalAlgebra.positive_product (denominator_square_positive x)
      (RationalAlgebra.positive_product (RationalArgmin.denominator_positive d) (denominator_square_positive x)))
        (norm_representation d x hd)).eqTrans (tag_positive_scale _ _ (denominator_square_positive x))

theorem native_norm (d x : PTm n) : Γ ⊢[PRAAx]
    ZT.eq (QuadraticSignCertificates.norm (integerRadicand d) (nativeData d x))
      (ZT.ofNat (denominatorOf d)*normNumerator d x) := by
  ipra_lc [QuadraticSignCertificates.norm, nativeData, QuadraticRationalRadicand.stretch_first, QuadraticRationalRadicand.stretch_second, normNumerator, integerRadicand]
theorem native_norm_tag (d x : PTm n) (hd : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative d) : Γ ⊢[PRAAx]
    tag (QuadraticSignCertificates.norm (integerRadicand d) (nativeData d x)) ≐ scalarTag (norm d x) :=
  (QuadraticIntegerSignDispatch.tag_value_congr _ _ (native_norm d x)).eqTrans
    ((tag_positive_scale _ _ (RationalArgmin.denominator_positive d)).eqTrans (norm_tag d x hd).eqSymm)

theorem native_first_tag (d x : PTm n) : Γ ⊢[PRAAx]
    tag (first (nativeData d x)) ≐ scalarTag (fstT x) :=
  (QuadraticIntegerSignDispatch.tag_value_congr _ _ (ZT.derive (by
    simpa only [nativeData,ZT.toZ_mul,ZT.toZ_ofNat] using QuadraticRationalRadicand.stretch_first (Γ := Γ) (denominatorOf d) (clear x)))).eqTrans
    ((tag_positive_scale _ _ (RationalArgmin.denominator_positive d)).eqTrans
      (tag_of_representation _ _ _ (QuadraticRationalClearing.denominator_positive x)
        (Prf.andE₁ (QuadraticRationalClearing.clear_represents x))).eqSymm)
theorem native_second_tag (d x : PTm n) : Γ ⊢[PRAAx]
    tag (second (nativeData d x)) ≐ scalarTag (sndT x) :=
  (QuadraticIntegerSignDispatch.tag_value_congr _ _ (ZT.derive (QuadraticRationalRadicand.stretch_second _ _))).eqTrans
    (tag_of_representation _ _ _ (QuadraticRationalClearing.denominator_positive x)
      (Prf.andE₂ (QuadraticRationalClearing.clear_represents x))).eqSymm
theorem native_radicand_tag (d : PTm n) (hd : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative d) : Γ ⊢[PRAAx]
    tag (ZT.ofNat (integerRadicand d)) ≐ scalarTag d := by
  have value : Γ ⊢[PRAAx] ZT.eq (ZT.ofNat (integerRadicand d)) (ZT.ofNat (denominatorOf d)*ZT.ofNat (positiveNumerator d)) := by
    ipra_lc [integerRadicand]
  exact (QuadraticIntegerSignDispatch.tag_value_congr _ _ value).eqTrans
    ((tag_positive_scale _ _ (RationalArgmin.denominator_positive d)).eqTrans
      (tag_of_representation _ _ _ (RationalArgmin.denominator_positive d) (radicand_representation d hd)).eqSymm)

/-- All three original lower-query tags, including the actual conditional
third operand, agree with the derived integer representation. -/
theorem native_third_tag (d x : PTm n) (hd : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative d) : Γ ⊢[PRAAx]
    QuadraticIntegerSignDispatch.third (integerRadicand d) (nativeData d x) ≐ third d x :=
  QuadraticTowerSignCoherence.third_select_congr (native_first_tag d x) (native_radicand_tag d hd) (native_norm_tag d x hd)
theorem native_recipe (d x : PTm n) (hd : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative d) : Γ ⊢[PRAAx]
    QuadraticIntegerSignDispatch.recipe (integerRadicand d) (nativeData d x) ≐ recipe d x :=
  QuadraticTowerSignCoherence.dispatch_congr (native_first_tag d x) (native_second_tag d x) (native_third_tag d x hd)

theorem positive_dispatch (d x : PTm n) (hd : Γ ⊢[PRAAx] QuadraticRationalRadicand.isPositive d) : Γ ⊢[PRAAx]
    recipe d x ≐ QuadraticRationalNonnegativeRadicand.sign d x := by
  have nn := QuadraticRationalRepresentationInvariance.positive_nonnegative d hd
  have nd := QuadraticRationalRadicand.integer_radicand_positive d hd
  have rep := QuadraticRationalRadicand.rescale_represents (Γ := Γ) (denominatorOf d) x (clear x) (denominator x)
    (RationalArgmin.denominator_positive d) (QuadraticRationalClearing.clear_represents x)
  have source := QuadraticRationalClearing.representation_sign (integerRadicand d)
    (QuadraticRationalRadicand.changeBasis d x) (nativeData d x) (denominator x*denominatorOf d) nd
    (RationalAlgebra.positive_product (QuadraticRationalClearing.denominator_positive x) (RationalArgmin.denominator_positive d)) rep
  exact (native_recipe d x nn).eqSymm.eqTrans
    ((QuadraticIntegerSignDispatch.positive_radicand_dispatch _ _ nd).eqTrans
      (source.eqSymm.eqTrans (QuadraticRationalNonnegativeRadicand.positive_branch d x hd).eqSymm))

theorem zero_integer_radicand (d : PTm n) (hd : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.radicandZero d) : Γ ⊢[PRAAx]
    integerRadicand d ≐ zero := by
  have pz : Γ ⊢[PRAAx] positiveNumerator d ≐ zero :=
    QuadraticSignCertificates.positive_part_zero _ (zle_of_comb 0 (by rw [ZT.toZ_eq hd]; ring) nn_zero)
  exact (congrMul pz (.eqRefl _)).eqTrans (zero_mul _)
theorem zero_dispatch (d x : PTm n) (hd : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.radicandZero d) : Γ ⊢[PRAAx]
    recipe d x ≐ QuadraticRationalNonnegativeRadicand.sign d x :=
  (native_recipe d x (QuadraticRationalRepresentationInvariance.zero_nonnegative d hd)).eqSymm.eqTrans
    ((QuadraticIntegerSignDispatch.recipe_radicand_congr _ (zero_integer_radicand d hd)).eqTrans
      ((QuadraticIntegerSignDispatch.zero_radicand_dispatch _).eqTrans
        ((native_first_tag d x).eqTrans (QuadraticRationalNonnegativeRadicand.zero_branch d x hd).eqSymm)))

theorem nonnegative_dispatch (d x : PTm n) (hd : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative d) : Γ ⊢[PRAAx]
    recipe d x ≐ QuadraticRationalNonnegativeRadicand.sign d x :=
  .orE (QuadraticRationalNonnegativeRadicand.radicand_cases d hd)
    (positive_dispatch d x Prf.hyp0) (zero_dispatch d x Prf.hyp0)

def output (d x : PTm n) : PTm n := pairT (recipe d x)
  (pairT (QuadraticRationalNonnegativeRadicand.sign d x) (pairT (norm d x) (pairT (third d x) (nativeData d x))))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (d x : PTm n) : PTm n := ap2 outputF d x
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (d x : PTm n) :
    Syn.subst σ (output d x) = output (Syn.subst σ d) (Syn.subst σ x) := by simp [output]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (d x : PTm n) :
    Syn.subst σ (run d x) = run (Syn.subst σ d) (Syn.subst σ x) := by simp [run]
theorem program_at (d x : PTm n) : Γ ⊢[PRAAx] run d x ≐ output d x := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![d,x]
theorem returned_recipe (d x : PTm n) : Γ ⊢[PRAAx] fstT (run d x) ≐ recipe d x :=
  (congrFst (program_at d x)).eqTrans (fst_pair _ _)
theorem returned_tail (d x : PTm n) : Γ ⊢[PRAAx] sndT (run d x) ≐
    pairT (QuadraticRationalNonnegativeRadicand.sign d x) (pairT (norm d x) (pairT (third d x) (nativeData d x))) :=
  (congrSnd (program_at d x)).eqTrans (snd_pair _ _)
theorem returned_source_sign (d x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run d x)) ≐ QuadraticRationalNonnegativeRadicand.sign d x :=
  (congrFst (returned_tail d x)).eqTrans (fst_pair _ _)
theorem returned_norm_pair (d x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run d x)) ≐ pairT (norm d x) (pairT (third d x) (nativeData d x)) :=
  (congrSnd (returned_tail d x)).eqTrans (snd_pair _ _)
theorem returned_norm (d x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run d x))) ≐ norm d x :=
  (congrFst (returned_norm_pair d x)).eqTrans (fst_pair _ _)
theorem returned_queries (d x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run d x))) ≐ pairT (third d x) (nativeData d x) :=
  (congrSnd (returned_norm_pair d x)).eqTrans (snd_pair _ _)
theorem returned_third (d x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run d x)))) ≐ third d x :=
  (congrFst (returned_queries d x)).eqTrans (fst_pair _ _)
theorem returned_native (d x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run d x)))) ≐ nativeData d x :=
  (congrSnd (returned_queries d x)).eqTrans (snd_pair _ _)
theorem returned_equal (d x : PTm n) (hd : Γ ⊢[PRAAx] QuadraticRationalNonnegativeRadicand.nonnegative d) : Γ ⊢[PRAAx]
    fstT (run d x) ≐ fstT (sndT (run d x)) :=
  (returned_recipe d x).eqTrans ((nonnegative_dispatch d x hd).eqTrans (returned_source_sign d x).eqSymm)

theorem actual_native_rational_coefficient_tags_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (tag (first (nativeData (var 0) (var 1))) ≐ scalarTag (fstT (var 1)) ⋏
      tag (second (nativeData (var 0) (var 1))) ≐ scalarTag (sndT (var 1))) :=
  closeUniv 2 (.andI (native_first_tag _ _) (native_second_tag _ _))
theorem actual_native_rational_norm_tag_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (QuadraticRationalNonnegativeRadicand.nonnegative (var 0) ⟶
      tag (QuadraticSignCertificates.norm (integerRadicand (var 0)) (nativeData (var 0) (var 1))) ≐ scalarTag (norm (var 0) (var 1))) :=
  closeUniv 2 (.impI (native_norm_tag _ _ Prf.hyp0))
theorem actual_native_rational_conditional_third_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (QuadraticRationalNonnegativeRadicand.nonnegative (var 0) ⟶
      QuadraticIntegerSignDispatch.third (integerRadicand (var 0)) (nativeData (var 0) (var 1)) ≐ third (var 0) (var 1)) :=
  closeUniv 2 (.impI (native_third_tag _ _ Prf.hyp0))
theorem actual_native_rational_dispatch_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (QuadraticRationalNonnegativeRadicand.nonnegative (var 0) ⟶
      QuadraticIntegerSignDispatch.recipe (integerRadicand (var 0)) (nativeData (var 0) (var 1)) ≐ recipe (var 0) (var 1)) :=
  closeUniv 2 (.impI (native_recipe _ _ Prf.hyp0))
theorem actual_positive_rational_dispatch_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (QuadraticRationalRadicand.isPositive (var 0) ⟶ recipe (var 0) (var 1) ≐ QuadraticRationalNonnegativeRadicand.sign (var 0) (var 1)) :=
  closeUniv 2 (.impI (positive_dispatch _ _ Prf.hyp0))
theorem actual_zero_rational_dispatch_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (QuadraticRationalNonnegativeRadicand.radicandZero (var 0) ⟶ recipe (var 0) (var 1) ≐ QuadraticRationalNonnegativeRadicand.sign (var 0) (var 1)) :=
  closeUniv 2 (.impI (zero_dispatch _ _ Prf.hyp0))
theorem actual_nonnegative_rational_dispatch_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (QuadraticRationalNonnegativeRadicand.nonnegative (var 0) ⟶ recipe (var 0) (var 1) ≐ QuadraticRationalNonnegativeRadicand.sign (var 0) (var 1)) :=
  closeUniv 2 (.impI (nonnegative_dispatch _ _ Prf.hyp0))
theorem actual_rational_dispatch_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem actual_returned_rational_dispatch_equal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (QuadraticRationalNonnegativeRadicand.nonnegative (var 0) ⟶ fstT (run (var 0) (var 1)) ≐ fstT (sndT (run (var 0) (var 1)))) :=
  closeUniv 2 (.impI (returned_equal _ _ Prf.hyp0))

end LeanProofs.IPRA.Algebra.QuadraticRationalSignDispatch
