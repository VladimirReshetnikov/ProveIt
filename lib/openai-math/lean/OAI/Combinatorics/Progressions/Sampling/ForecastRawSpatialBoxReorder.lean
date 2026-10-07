/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import OAI.Combinatorics.Progressions.Estimates.ComplexDiagonalVolumeIntegral
import OAI.Combinatorics.Progressions.Lattices.ForecastIntegerAxisSplit
import OAI.Combinatorics.Progressions.Sampling.ForecastFiniteSpatialFamily

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

noncomputable def mixedCoveredJetDeckReference {m : ℕ} (O E : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (E j)] (N : ℕ) [NeZero N] :
    Measure (∀ j, O j → E j → ZMod N) :=
  (PMF.uniformOfFintype (∀ j, O j → E j → ZMod N)).toMeasure

theorem mixedCoveredJetRawReference_prod {m : ℕ} {I O E : Fin m → Type*}
    [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} (N : ℕ) [NeZero N] :
    mixedCoveredJetRawReference (I := I) (O := O) (E := E) (n := n) N =
      (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod
        (mixedCoveredJetDeckReference O E N) := rfl

variable {m : ℕ} (I E : Fin m → Type*) [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable (n : Fin m → ℕ) (N : ℕ) [NeZero N]

abbrev ForecastSingleDeckResidues (E : Fin m → Type*) (N : ℕ) :=
  ∀ j, Unit → E j → ZMod N

local notation "single" => (fun _ : Fin m => Unit)
local notation "RealAxis" => (Σ j, I j)
local notation "IntAxis" => (Σ j, Fin (n j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := single) (E := E) (n := n) N

theorem forecastSingleMixedRawReference_eq :
    raw = (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) Unit)).prod (mixedCoveredJetDeckReference single E N) := by
  exact mixedCoveredJetRawReference_prod (I := I) (O := single) (E := E) (n := n) N

noncomputable def forecastSingleMixedRawEquiv :
    MixedCoveredJetSource I single E n N ≃ᵐ
      (((RealAxis → ℝ) × (IntAxis → ℤ)) × (∀ j, Unit → E j → ZMod N)) where
  toFun z := ((fun a => (z.1 a.1).1 a.2 (), fun a => (z.1 a.1).2 a.2 ()), z.2)
  invFun p := (fun j => (fun i _ => p.1.1 ⟨j, i⟩, fun i _ => p.1.2 ⟨j, i⟩), p.2)
  left_inv z := by
    apply Prod.ext
    · funext j
      apply Prod.ext <;> funext i t <;> cases t <;> rfl
    · rfl
  right_inv p := rfl
  measurable_toFun := by
    change Measurable (fun z : MixedCoveredJetSource I single E n N =>
      ((fun a : RealAxis => (z.1 a.1).1 a.2 (),
        fun a : IntAxis => (z.1 a.1).2 a.2 ()), z.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : ((RealAxis → ℝ) × (IntAxis → ℤ)) × (∀ j, Unit → E j → ZMod N) =>
      (fun j => (fun i (_ : Unit) => p.1.1 ⟨j, i⟩,
        fun i (_ : Unit) => p.1.2 ⟨j, i⟩), p.2))
    fun_prop

omit [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [NeZero N] in
theorem forecastSingleMixedRawEquiv_coe :
    (forecastSingleMixedRawEquiv I E n N : MixedCoveredJetSource I single E n N →
      (((RealAxis → ℝ) × (IntAxis → ℤ)) × (∀ j, Unit → E j → ZMod N))) =
    Prod.map (fun z : ∀ j, (I j → Unit → ℝ) × (Fin (n j) → Unit → ℤ) =>
      (fun a : RealAxis => (z a.1).1 a.2 (), fun a : IntAxis => (z a.1).2 a.2 ())) id := rfl

noncomputable def forecastSingleMixedRawPoint (v : RealAxis → ℝ) (k : IntAxis → ℤ)
    (deck : (∀ j, Unit → E j → ZMod N)) : MixedCoveredJetSource I single E n N :=
  (fun j => (fun i _ => v ⟨j, i⟩, fun i _ => k ⟨j, i⟩), deck)

omit [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [NeZero N] in
theorem forecastSingleMixedRawEquiv_symm_apply
    (p : ((RealAxis → ℝ) × (IntAxis → ℤ)) × (∀ j, Unit → E j → ZMod N)) :
    (forecastSingleMixedRawEquiv I E n N).symm p =
      forecastSingleMixedRawPoint I E n N p.1.1 p.1.2 p.2 := rfl

omit [∀ j, Fintype (E j)] [NeZero N] in
private theorem forecastSingleRawLayer_preserving (j : Fin m) : MeasurePreserving
    ((mixedArrayRegroup (I j) (Fin (n j)) Unit).trans
      (MeasurableEquiv.funUnique Unit ((I j → ℝ) × (Fin (n j) → ℤ))))
    (mixedArrayReference (I j) (Fin (n j)) Unit)
    ((volume : Measure (I j → ℝ)).prod (Measure.count : Measure (Fin (n j) → ℤ))) :=
  (measurePreserving_funUnique _ Unit).comp
    (mixedArrayRegroup_volume_count (I j) (Fin (n j)) Unit)

omit [∀ j, Fintype (E j)] [NeZero N] in
private theorem forecastSingleRawReal_flatten : MeasurePreserving
    (MeasurableEquiv.piCurry (fun j (_ : I j) => ℝ)).symm
    (Measure.pi (fun j => (volume : Measure (I j → ℝ))))
    (volume : Measure (RealAxis → ℝ)) := by
  refine ⟨(MeasurableEquiv.piCurry (fun j (_ : I j) => ℝ)).symm.measurable, ?_⟩
  exact sigmaFiniteProductMeasure_flatten (fun _ : RealAxis => (volume : Measure ℝ))

omit [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [NeZero N] in
private theorem forecastSingleRawInteger_flatten : MeasurePreserving
    (MeasurableEquiv.piCurry (fun j (_ : Fin (n j)) => ℤ)).symm
    (Measure.pi (fun j => (Measure.count : Measure (Fin (n j) → ℤ))))
    (Measure.count : Measure (IntAxis → ℤ)) := by
  refine ⟨(MeasurableEquiv.piCurry (fun j (_ : Fin (n j)) => ℤ)).symm.measurable, ?_⟩
  change Measure.map (fun (x : ∀ j, Fin (n j) → ℤ) (a : IntAxis) => x a.1 a.2) _ = _
  have h := sigmaFiniteProductMeasure_flatten (fun _ : IntAxis => (Measure.count : Measure ℤ))
  simpa only [pi_count_measure] using h

omit [∀ j, Fintype (E j)] [NeZero N] in
private theorem forecastSingleRawArray_preserving :
    MeasurePreserving
      (fun z : ∀ j, (I j → Unit → ℝ) × (Fin (n j) → Unit → ℤ) =>
        (fun a : RealAxis => (z a.1).1 a.2 (), fun a : IntAxis => (z a.1).2 a.2 ()))
      (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) Unit))
      ((volume : Measure (RealAxis → ℝ)).prod (Measure.count : Measure (IntAxis → ℤ))) := by
  have hlayers := measurePreserving_pi
    (fun j => mixedArrayReference (I j) (Fin (n j)) Unit)
    (fun j => (volume : Measure (I j → ℝ)).prod (Measure.count : Measure (Fin (n j) → ℤ)))
    (forecastSingleRawLayer_preserving I n)
  have hreal := forecastSingleRawReal_flatten I
  have hint := forecastSingleRawInteger_flatten n
  have h := (((hreal.prod hint).comp
    (dependentPiProd_measurePreserving
      (fun j => (volume : Measure (I j → ℝ)))
      (fun j => (Measure.count : Measure (Fin (n j) → ℤ))))).comp hlayers)
  convert h using 1
  rfl

theorem forecastSingleMixedRawEquiv_measurePreserving :
    MeasurePreserving (forecastSingleMixedRawEquiv I E n N) raw
      (((volume : Measure (RealAxis → ℝ)).prod
        (Measure.count : Measure (IntAxis → ℤ))).prod (mixedCoveredJetDeckReference single E N)) := by
  rw [forecastSingleMixedRawEquiv_coe, forecastSingleMixedRawReference_eq]
  have hid : MeasurePreserving (id : (∀ j, Unit → E j → ZMod N) → (∀ j, Unit → E j → ZMod N)) (mixedCoveredJetDeckReference single E N) (mixedCoveredJetDeckReference single E N) := MeasurePreserving.id _
  have hp := (forecastSingleRawArray_preserving I n).prod hid
  exact hp

theorem forecastSingleMixedRaw_integral (f : MixedCoveredJetSource I single E n N → ℂ) :
    (∫ z, f z ∂raw) =
      ∫ p : ((RealAxis → ℝ) × (IntAxis → ℤ)) × (∀ j, Unit → E j → ZMod N),
        f (forecastSingleMixedRawPoint I E n N p.1.1 p.1.2 p.2)
        ∂((volume : Measure (RealAxis → ℝ)).prod Measure.count).prod (mixedCoveredJetDeckReference single E N) := by
  have h := ((forecastSingleMixedRawEquiv_measurePreserving I E n N).symm
    (forecastSingleMixedRawEquiv I E n N)).integral_comp
      (forecastSingleMixedRawEquiv I E n N).symm.measurableEmbedding f
  simpa only [forecastSingleMixedRawEquiv_symm_apply] using h.symm

theorem forecastSingleMixedRaw_integrable_iff
    (f : MixedCoveredJetSource I single E n N → ℂ) :
    Integrable (fun p : ((RealAxis → ℝ) × (IntAxis → ℤ)) × (∀ j, Unit → E j → ZMod N) =>
      f (forecastSingleMixedRawPoint I E n N p.1.1 p.1.2 p.2))
      (((volume : Measure (RealAxis → ℝ)).prod Measure.count).prod (mixedCoveredJetDeckReference single E N)) ↔
        Integrable f raw := by
  have h := ((forecastSingleMixedRawEquiv_measurePreserving I E n N).symm
    (forecastSingleMixedRawEquiv I E n N)).integrable_comp_emb
      (forecastSingleMixedRawEquiv I E n N).symm.measurableEmbedding (g := f)
  simpa only [forecastSingleMixedRawEquiv_symm_apply, Function.comp_def] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

noncomputable local instance : DecidableEq Unit := Classical.decEq Unit

private theorem uniform_complex_integral {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (f : α → ℂ) :
    (∫ a, f a ∂(PMF.uniformOfFintype α).toMeasure) = 𝔼 a, f a := by
  rw [PMF.integral_eq_sum, Fintype.expect_eq_sum_div_card]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, ← Finset.mul_sum]
  rw [div_eq_inv_mul]

variable {m : ℕ} (E : Fin m → Type*) (N : ℕ)

def forecastSingleDeckEquiv :
    ForecastSingleDeckResidues E N ≃ ((Σ j, E j) → ZMod N) where
  toFun deck a := deck a.1 () a.2
  invFun r j _ e := r ⟨j, e⟩
  left_inv deck := by funext j u e; cases u; rfl
  right_inv r := rfl

theorem forecastSingleDeckAverage [∀ j, Fintype (E j)] [NeZero N]
    (f : ForecastSingleDeckResidues E N → ℂ) :
    (∫ deck, f deck ∂mixedCoveredJetDeckReference (fun _ : Fin m => Unit) E N) =
      𝔼 r : (Σ j, E j) → ZMod N, f (fun j _ e => r ⟨j, e⟩) := by
  rw [mixedCoveredJetDeckReference, uniform_complex_integral]
  exact Fintype.expect_equiv (forecastSingleDeckEquiv E N) f
    (fun r => f (fun j _ e => r ⟨j, e⟩)) (fun deck => by congr 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} (I E : Fin m → Type*) [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (N : ℕ) [NeZero N]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ) (R : Fin m → ℝ) (hR : ∀ j, 0 < R j)

local notation "single" => (fun _ : Fin m => Unit)
local notation "RealAxis" => (Σ j, I j)
local notation "IntAxis" => (Σ j, Fin (n j))
local notation "Deck" => ForecastSingleDeckResidues E N
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := single) (E := E) (n := n) N
local notation "deckLaw" => mixedCoveredJetDeckReference single E N
local notation "short" => AllocatedShortIntegerAxis U basis L
local notation "active" => AllocatedActiveIntegerAxis U basis L

include hR in
theorem forecastSingleMixedRaw_normalized_split_integral
    (f : MixedCoveredJetSource I single E n N → ℂ) (hf : Integrable f raw) :
    (∫ z, f z ∂raw) = ((∏ a : RealAxis, R a.1 : ℝ) : ℂ) *
      ∫ v : RealAxis → ℝ,
        ∫ k : (short → ℤ) × (active → ℤ),
          ∫ deck : Deck,
            f (forecastSingleMixedRawPoint I E n N
              (fun a => R a.1 * v a) (forecastIntegerAxisMerge U basis L k.1 k.2) deck)
            ∂deckLaw ∂Measure.count.prod Measure.count := by
  have hi := (forecastSingleMixedRaw_integrable_iff I E n N f).mpr hf
  rw [forecastSingleMixedRaw_integral I E n N f, integral_prod _ hi,
    integral_prod _ hi.integral_prod_left]
  rw [complex_integral_eq_positive_diagonal (fun a : RealAxis => R a.1)
    (fun a => hR a.1)]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v =>
    forecastIntegerAxisSplit_integral U basis L
      (fun k : IntAxis → ℤ => ∫ deck : Deck,
        f (forecastSingleMixedRawPoint I E n N (fun a => R a.1 * v a) k deck) ∂deckLaw))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

private theorem productGridReorder_preserving
    {V S A D : Type*} [MeasurableSpace V] [MeasurableSpace S]
    [MeasurableSpace A] [MeasurableSpace D]
    (μV : Measure V) (μS : Measure S) (μA : Measure A) (μD : Measure D)
    [SFinite μV] [SFinite μS] [SFinite μA] [SFinite μD] :
    MeasurePreserving (fun p : (V × (S × A)) × D => ((p.1.2.1, p.2), (p.1.1, p.1.2.2)))
      ((μV.prod (μS.prod μA)).prod μD) ((μS.prod μD).prod (μV.prod μA)) := by
  have h₁ := (measurePreserving_prodAssoc μV μS μA).symm MeasurableEquiv.prodAssoc
  have h₂ := (Measure.measurePreserving_swap (μ := μV) (ν := μS)).prod (MeasurePreserving.id μA)
  have h₃ := measurePreserving_prodAssoc μS μV μA
  have hleft := (h₃.comp (h₂.comp h₁)).prod (MeasurePreserving.id μD)
  have h₄ := measurePreserving_prodAssoc μS (μV.prod μA) μD
  have h₅ := (MeasurePreserving.id μS).prod
    (Measure.measurePreserving_swap (μ := μV.prod μA) (ν := μD))
  have h₆ := (measurePreserving_prodAssoc μS μD (μV.prod μA)).symm MeasurableEquiv.prodAssoc
  convert h₆.comp (h₅.comp (h₄.comp hleft)) using 1
  rfl

variable {m : ℕ} (I E : Fin m → Type*) [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (N : ℕ) [NeZero N]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

local notation "single" => (fun _ : Fin m => Unit)
local notation "RealAxis" => (Σ j, I j)
local notation "IntAxis" => (Σ j, Fin (n j))
local notation "Deck" => ForecastSingleDeckResidues E N
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := single) (E := E) (n := n) N
local notation "deckLaw" => mixedCoveredJetDeckReference single E N
local notation "short" => AllocatedShortIntegerAxis U basis L
local notation "active" => AllocatedActiveIntegerAxis U basis L
local notation "gridMeasure" => Measure.prod
  (Measure.prod (Measure.count : Measure (short → ℤ)) deckLaw)
  (Measure.prod (volume : Measure (RealAxis → ℝ)) (Measure.count : Measure (active → ℤ)))

noncomputable def forecastRawGridEquiv : MixedCoveredJetSource I single E n N ≃ᵐ
    (((short → ℤ) × Deck) × ((RealAxis → ℝ) × (active → ℤ))) where
  toFun z := (((fun a => (z.1 a.val.1).2 a.val.2 ()), z.2),
    ((fun a => (z.1 a.1).1 a.2 ()), fun a => (z.1 a.val.1).2 a.val.2 ()))
  invFun p := forecastSingleMixedRawPoint I E n N p.2.1
    (forecastIntegerAxisMerge U basis L p.1.1 p.2.2) p.1.2
  left_inv z := by
    apply Prod.ext
    · funext j
      apply Prod.ext
      · funext i t
        cases t
        rfl
      · funext i t
        cases t
        simp only [forecastSingleMixedRawPoint, forecastIntegerAxisMerge]
        split <;> rfl
    · rfl
  right_inv p := by
    apply Prod.ext
    · apply Prod.ext
      · funext a
        exact forecastIntegerAxisMerge_short U basis L p.1.1 p.2.2 a
      · rfl
    · apply Prod.ext
      · rfl
      · funext a
        exact forecastIntegerAxisMerge_active U basis L p.1.1 p.2.2 a
  measurable_toFun := by
    change Measurable (fun z : MixedCoveredJetSource I single E n N =>
      (((fun a : short => (z.1 a.val.1).2 a.val.2 ()), z.2),
        ((fun a : RealAxis => (z.1 a.1).1 a.2 ()),
          fun a : active => (z.1 a.val.1).2 a.val.2 ())))
    fun_prop
  measurable_invFun := by
    unfold forecastSingleMixedRawPoint
    have hm := (forecastIntegerAxisSplit U basis L).symm.measurable
    change Measurable (fun p : ((short → ℤ) × Deck) × ((RealAxis → ℝ) × (active → ℤ)) => (fun j =>
      (fun i (_ : Unit) => p.2.1 ⟨j, i⟩,
        fun i (_ : Unit) => (forecastIntegerAxisSplit U basis L).symm (p.1.1, p.2.2) ⟨j, i⟩), p.1.2))
    fun_prop

theorem forecastRawGridEquiv_measurePreserving :
    MeasurePreserving (forecastRawGridEquiv I E N U basis L) raw gridMeasure := by
  let : IsProbabilityMeasure deckLaw := by unfold mixedCoveredJetDeckReference; infer_instance
  have hs := ((MeasurePreserving.id (volume : Measure (RealAxis → ℝ))).prod
    (forecastIntegerAxisSplit_measurePreserving U basis L)).prod (MeasurePreserving.id deckLaw)
  have hr := productGridReorder_preserving (volume : Measure (RealAxis → ℝ))
    (Measure.count : Measure (short → ℤ)) (Measure.count : Measure (active → ℤ)) deckLaw
  convert hr.comp (hs.comp (forecastSingleMixedRawEquiv_measurePreserving I E n N)) using 1
  rfl

theorem forecastRawGrid_integrable_iff
    (f : MixedCoveredJetSource I single E n N → ℂ) :
    Integrable (fun p : ((short → ℤ) × Deck) × ((RealAxis → ℝ) × (active → ℤ)) =>
      f (forecastSingleMixedRawPoint I E n N p.2.1
        (forecastIntegerAxisMerge U basis L p.1.1 p.2.2) p.1.2)) gridMeasure ↔
      Integrable f raw :=
  ((forecastRawGridEquiv_measurePreserving I E N U basis L).symm
    (forecastRawGridEquiv I E N U basis L)).integrable_comp_emb
      (forecastRawGridEquiv I E N U basis L).symm.measurableEmbedding

theorem forecastRawGrid_integral
    (f : MixedCoveredJetSource I single E n N → ℂ) (hf : Integrable f raw) :
    (∫ z, f z ∂raw) =
      ∫ ks : short → ℤ, ∫ deck : Deck, ∫ v : RealAxis → ℝ, ∫ ka : active → ℤ,
        f (forecastSingleMixedRawPoint I E n N v
          (forecastIntegerAxisMerge U basis L ks ka) deck)
          ∂Measure.count ∂volume ∂deckLaw ∂Measure.count := by
  let : IsProbabilityMeasure deckLaw := by unfold mixedCoveredJetDeckReference; infer_instance
  have hi := (forecastRawGrid_integrable_iff I E N U basis L f).mpr hf
  have he := ((forecastRawGridEquiv_measurePreserving I E N U basis L).symm
    (forecastRawGridEquiv I E N U basis L)).integral_comp
      (forecastRawGridEquiv I E N U basis L).symm.measurableEmbedding f
  change (∫ p, f (forecastSingleMixedRawPoint I E n N p.2.1
    (forecastIntegerAxisMerge U basis L p.1.1 p.2.2) p.1.2) ∂gridMeasure) = _ at he
  rw [← he, integral_prod _ hi, integral_prod _ hi.integral_prod_left]
  apply integral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hi.prod_right_ae] with ks hks
  apply integral_congr_ae
  filter_upwards [hks] with deck hdeck
  exact integral_prod _ hdeck

theorem forecastRawGrid_rows_integrable_ae
    (f : MixedCoveredJetSource I single E n N → ℂ) (hf : Integrable f raw) :
    ∀ᵐ ks : short → ℤ ∂Measure.count, ∀ᵐ deck : Deck ∂deckLaw,
      Integrable (fun p : (RealAxis → ℝ) × (active → ℤ) =>
        f (forecastSingleMixedRawPoint I E n N p.1
          (forecastIntegerAxisMerge U basis L ks p.2) deck))
        ((volume : Measure (RealAxis → ℝ)).prod Measure.count) := by
  let : IsProbabilityMeasure deckLaw := by unfold mixedCoveredJetDeckReference; infer_instance
  exact Measure.ae_ae_of_ae_prod
    ((forecastRawGrid_integrable_iff I E N U basis L f).mpr hf).prod_right_ae

theorem forecastRawGrid_normalized_integral
    (R : Fin m → ℝ) (hR : ∀ j, 0 < R j)
    (f : MixedCoveredJetSource I single E n N → ℂ) (hf : Integrable f raw) :
    (∫ z, f z ∂raw) = ((∏ a : RealAxis, R a.1 : ℝ) : ℂ) *
      ∫ ks : short → ℤ, ∫ deck : Deck, ∫ v : RealAxis → ℝ, ∫ ka : active → ℤ,
        f (forecastSingleMixedRawPoint I E n N (fun a => R a.1 * v a)
          (forecastIntegerAxisMerge U basis L ks ka) deck)
          ∂Measure.count ∂volume ∂deckLaw ∂Measure.count := by
  rw [forecastRawGrid_integral I E N U basis L f hf]
  conv_rhs => rw [← integral_const_mul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun ks => ?_)
  dsimp only
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun deck => ?_)
  dsimp only
  exact complex_integral_eq_positive_diagonal (fun a : RealAxis => R a.1)
    (fun a => hR a.1) _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

private theorem productLeftComm_preserving
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (fun p : A × (B × C) => (p.2.1, (p.1, p.2.2)))
      (μ.prod (ν.prod ρ)) (ν.prod (μ.prod ρ)) := by
  have h₁ := (measurePreserving_prodAssoc μ ν ρ).symm MeasurableEquiv.prodAssoc
  have h₂ := (Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id ρ)
  convert (measurePreserving_prodAssoc ν μ ρ).comp (h₂.comp h₁) using 1
  rfl

private theorem spatialGridReorder_preserving
    {K S D V A : Type*} [MeasurableSpace K] [MeasurableSpace S] [MeasurableSpace D]
    [MeasurableSpace V] [MeasurableSpace A]
    (μK : Measure K) (μS : Measure S) (μD : Measure D) (μV : Measure V) (μA : Measure A)
    [SFinite μK] [SFinite μS] [SFinite μD] [SFinite μV] [SFinite μA] :
    MeasurePreserving (fun p : K × ((S × D) × (V × A)) =>
      (p.2.1.2, (p.2.2.1, (p.2.1.1, (p.1, p.2.2.2)))))
      (μK.prod ((μS.prod μD).prod (μV.prod μA)))
      (μD.prod (μV.prod (μS.prod (μK.prod μA)))) := by
  have h₁ := (MeasurePreserving.id μK).prod (measurePreserving_prodAssoc μS μD (μV.prod μA))
  have h₂ := productLeftComm_preserving μK μS (μD.prod (μV.prod μA))
  have h₃ := (MeasurePreserving.id μS).prod (productLeftComm_preserving μK μD (μV.prod μA))
  have h₄ := (MeasurePreserving.id μS).prod
    ((MeasurePreserving.id μD).prod (productLeftComm_preserving μK μV μA))
  have h₅ := productLeftComm_preserving μS μD (μV.prod (μK.prod μA))
  have h₆ := (MeasurePreserving.id μD).prod (productLeftComm_preserving μS μV (μK.prod μA))
  convert h₆.comp (h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))) using 1
  rfl

private theorem integerSumCoordinates_preserving {X A : Type*} [Finite X] [Finite A] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : X ⊕ A => ℤ))
      Measure.count (Measure.count.prod Measure.count) := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : X ⊕ A => ℤ)
  refine ⟨e.measurable, ?_⟩
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply e.measurable (measurableSet_singleton z)]
  have he : e ⁻¹' {z} = {e.symm z} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact e.toEquiv.eq_symm_apply.symm
  rw [he, Measure.count_singleton, ← Set.singleton_prod_singleton,
    Measure.prod_prod, Measure.count_singleton, Measure.count_singleton, one_mul]

variable {m : ℕ} (I E : Fin m → Type*) [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (N : ℕ) [NeZero N]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ) (X : Type*) [Fintype X]

local notation "single" => (fun _ : Fin m => Unit)
local notation "RealAxis" => (Σ j, I j)
local notation "Deck" => ForecastSingleDeckResidues E N
local notation "RawSource" => MixedCoveredJetSource I single E n N
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := single) (E := E) (n := n) N
local notation "deckLaw" => mixedCoveredJetDeckReference single E N
local notation "short" => AllocatedShortIntegerAxis U basis L
local notation "active" => AllocatedActiveIntegerAxis U basis L
local notation "Target" => Deck × ((RealAxis → ℝ) × ((short → ℤ) × ((X ⊕ active) → ℤ)))
local notation "targetLaw" => Measure.prod deckLaw (Measure.prod (volume : Measure (RealAxis → ℝ))
  (Measure.prod (Measure.count : Measure (short → ℤ)) (Measure.count : Measure ((X ⊕ active) → ℤ))))

noncomputable def forecastRawSpatialEquiv : ((X → ℤ) × RawSource) ≃ᵐ Target where
  toFun p := (p.2.2, ((fun a => (p.2.1 a.1).1 a.2 ()),
    ((fun a => (p.2.1 a.val.1).2 a.val.2 ()),
      Sum.elim p.1 (fun a => (p.2.1 a.val.1).2 a.val.2 ()))))
  invFun p := ((fun x => p.2.2.2 (Sum.inl x)),
    forecastSingleMixedRawPoint I E n N p.2.1
      (forecastIntegerAxisMerge U basis L p.2.2.1 (fun a => p.2.2.2 (Sum.inr a))) p.1)
  left_inv p := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext j
        apply Prod.ext
        · funext i t
          cases t
          rfl
        · funext i t
          cases t
          simp only [forecastSingleMixedRawPoint, forecastIntegerAxisMerge]
          split <;> rfl
      · rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · funext a
          exact forecastIntegerAxisMerge_short U basis L p.2.2.1
            (fun a => p.2.2.2 (Sum.inr a)) a
        · funext a
          cases a with
          | inl x => rfl
          | inr a =>
            exact forecastIntegerAxisMerge_active U basis L p.2.2.1
              (fun a => p.2.2.2 (Sum.inr a)) a
  measurable_toFun := by
    change Measurable (fun p : (X → ℤ) × RawSource =>
      (p.2.2, ((fun a : RealAxis => (p.2.1 a.1).1 a.2 ()),
        ((fun a : short => (p.2.1 a.val.1).2 a.val.2 ()),
          Sum.elim p.1 (fun a : active => (p.2.1 a.val.1).2 a.val.2 ())))))
    apply Measurable.prodMk measurable_snd.snd
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.of_eval
    intro a
    cases a <;> fun_prop
  measurable_invFun := by
    have hm := (forecastIntegerAxisSplit U basis L).symm.measurable
    change Measurable (fun p : Target => ((fun x => p.2.2.2 (Sum.inl x)),
      (fun j => (fun i (_ : Unit) => p.2.1 ⟨j,i⟩,
        fun i (_ : Unit) => (forecastIntegerAxisSplit U basis L).symm
          (p.2.2.1, fun a => p.2.2.2 (Sum.inr a)) ⟨j,i⟩), p.1)))
    fun_prop

theorem forecastRawSpatialEquiv_measurePreserving :
    MeasurePreserving (forecastRawSpatialEquiv I E N U basis L X)
      ((Measure.count : Measure (X → ℤ)).prod raw) targetLaw := by
  let : IsProbabilityMeasure deckLaw := by unfold mixedCoveredJetDeckReference; infer_instance
  let : SigmaFinite raw := by rw [forecastSingleMixedRawReference_eq I E n N]; infer_instance
  have h₁ := (MeasurePreserving.id (Measure.count : Measure (X → ℤ))).prod
    (forecastRawGridEquiv_measurePreserving I E N U basis L)
  have h₂ := spatialGridReorder_preserving (Measure.count : Measure (X → ℤ))
    (Measure.count : Measure (short → ℤ)) deckLaw (volume : Measure (RealAxis → ℝ))
    (Measure.count : Measure (active → ℤ))
  have hjoin := (integerSumCoordinates_preserving (X := X) (A := active)).symm
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : X ⊕ active => ℤ))
  have h₃ := (MeasurePreserving.id deckLaw).prod
    ((MeasurePreserving.id (volume : Measure (RealAxis → ℝ))).prod
      ((MeasurePreserving.id (Measure.count : Measure (short → ℤ))).prod hjoin))
  convert h₃.comp (h₂.comp h₁) using 1
  rfl

theorem forecastRawSpatial_integral
    (F : (X → ℤ) → RawSource → ℂ)
    (hF : Integrable (fun p : (X → ℤ) × RawSource => F p.1 p.2)
      ((Measure.count : Measure (X → ℤ)).prod raw)) :
    (∫ p : (X → ℤ) × RawSource, F p.1 p.2
      ∂(Measure.count : Measure (X → ℤ)).prod raw) =
      ∫ deck : Deck, ∫ v : RealAxis → ℝ,
        ∑' ks : short → ℤ, ∑' k : (X ⊕ active) → ℤ,
          F (fun x => k (Sum.inl x)) (forecastSingleMixedRawPoint I E n N v
            (forecastIntegerAxisMerge U basis L ks (fun a => k (Sum.inr a))) deck)
        ∂volume ∂deckLaw := by
  let : IsProbabilityMeasure deckLaw := by unfold mixedCoveredJetDeckReference; infer_instance
  let e := forecastRawSpatialEquiv I E N U basis L X
  have hp := (forecastRawSpatialEquiv_measurePreserving I E N U basis L X).symm e
  have hi := (hp.integrable_comp_emb e.symm.measurableEmbedding).mpr hF
  have he := hp.integral_comp e.symm.measurableEmbedding (fun p => F p.1 p.2)
  change (∫ p : Target, F (fun x => p.2.2.2 (Sum.inl x))
    (forecastSingleMixedRawPoint I E n N p.2.1
      (forecastIntegerAxisMerge U basis L p.2.2.1 (fun a => p.2.2.2 (Sum.inr a))) p.1)
      ∂targetLaw) = _ at he
  change Integrable (fun p : Target => F (fun x => p.2.2.2 (Sum.inl x))
    (forecastSingleMixedRawPoint I E n N p.2.1
      (forecastIntegerAxisMerge U basis L p.2.2.1 (fun a => p.2.2.2 (Sum.inr a))) p.1))
      targetLaw at hi
  rw [← he, integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with deck hd
  rw [integral_prod _ hd]
  apply integral_congr_ae
  filter_upwards [hd.prod_right_ae] with v hv
  rw [integral_prod _ hv, integral_countable hv.integral_prod_left]
  simp only [count_real_singleton, one_smul]
  apply tsum_congr
  intro ks
  have hrow := Measure.ae_count_iff.mp hv.prod_right_ae ks
  simpa only [count_real_singleton, one_smul] using integral_countable hrow

theorem forecastRawSpatialBox_normalized_integral
    (R : Fin m → ℝ) (hR : ∀ j, 0 < R j)
    (F : (X → ℤ) → RawSource → ℂ) (s : Finset (X → ℤ))
    (hf : ∀ u ∈ s, Integrable (F u) raw)
    (hzero : ∀ u ∉ s, ∀ z, F u z = 0) :
    (∑ u ∈ s, ∫ z, F u z ∂raw) = ((∏ a : RealAxis, R a.1 : ℝ) : ℂ) *
      ∫ deck : Deck, ∫ v : RealAxis → ℝ,
        ∑' ks : short → ℤ, ∑' k : (X ⊕ active) → ℤ,
          F (fun x => k (Sum.inl x))
            (forecastSingleMixedRawPoint I E n N (fun a => R a.1 * v a)
              (forecastIntegerAxisMerge U basis L ks (fun a => k (Sum.inr a))) deck)
        ∂volume ∂deckLaw := by
  let : IsProbabilityMeasure deckLaw := by unfold mixedCoveredJetDeckReference; infer_instance
  let : SigmaFinite raw := by rw [forecastSingleMixedRawReference_eq I E n N]; infer_instance
  have hF := forecastFiniteSpatialFamily_integrable raw F s hf hzero
  rw [forecastFiniteSpatialFamily_sum_integral raw F s hf hzero,
    forecastRawSpatial_integral I E N U basis L X F hF]
  conv_rhs => rw [← integral_const_mul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun deck => ?_)
  dsimp only
  exact complex_integral_eq_positive_diagonal (fun a : RealAxis => R a.1)
    (fun a => hR a.1) _

end Erdos3.VectorPolynomial

end

end OAI
