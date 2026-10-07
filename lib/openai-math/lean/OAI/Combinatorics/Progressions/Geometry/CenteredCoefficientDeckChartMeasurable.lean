/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import OAI.Combinatorics.Progressions.Estimates.ConstantCenterUniformLifts
import OAI.Combinatorics.Progressions.Lattices.CoefficientDeckResidueMask
import OAI.Combinatorics.Progressions.Linear.JointFrameCoefficientCoverSample

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
attribute [local irreducible] coefficientDeckKernelEquiv canonicalCoefficientDeckSample coefficientSamplerAmbientPoint

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

def coefficientDeckChartEvent (q : ℕ) [NeZero q]
    (event : CoefficientChartResidues K n E q → Prop) (y : CoefficientTorus (K := K) U) : Prop :=
  ∃ x : CoefficientSamplerArrays (K := K) I n, ∃ r : CoefficientDeckResidues (K := K) E q,
    (∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2) ∧
    canonicalCoefficientDeckSample U bW b hb o q (NeZero.pos q) x r = y ∧
    event (coefficientSamplerChartResidues q x r)

omit [Fintype K] in
theorem coefficientDeckChartEvent_sample_iff (q : ℕ) [NeZero q]
    (event : CoefficientChartResidues K n E q → Prop)
    (x : CoefficientSamplerArrays (K := K) I n)
    (hx : ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2)
    (r : CoefficientDeckResidues (K := K) E q) :
    coefficientDeckChartEvent U bW b hb o q event
      (canonicalCoefficientDeckSample U bW b hb o q (NeZero.pos q) x r) ↔
      event (coefficientSamplerChartResidues q x r) := by
  constructor
  · rintro ⟨x', r', hx', he, hp⟩
    have h : (x', r') = (x, r) := canonicalCoefficientDeckSample_injOn_smallAmbient U bW b hb o q (NeZero.pos q)
      (x₁ := (x', r')) (x₂ := (x, r)) hx' hx (by exact he)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact hp
  · intro he
    exact ⟨x, r, hx, rfl, he⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped Classical

variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

omit [Fintype K] in

theorem coefficientSamplerAmbientPoint_measurable (a : CoefficientAmbientIndex K J) :
    Measurable (fun x : CoefficientSamplerArrays (K := K) I n =>
      coefficientSamplerAmbientPoint U b o x a) := by
  exact (PiLp.continuous_apply 2 (fun _ : J a.1.1 => ℝ) a.2).measurable.comp
    ((normalizedLatticePoint_continuous (euclideanSubspace (U a.1.1)) (b a.1.1)).measurable.comp
      ((orthonormalMixedChart (o a.1.1)).measurable.comp
        ((measurable_pi_apply a.1.2).comp
          ((mixedArrayRegroup _ _ _).measurable.comp (measurable_pi_apply a.1.1)))))

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

theorem coefficientDeckChartEvent_measurableSet (q : ℕ) [NeZero q]
    (event : CoefficientChartResidues K n E q → Prop) :
    MeasurableSet {y | coefficientDeckChartEvent U bW b hb o q event y} := by
  let T := CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) E q
  let chart : Set T := {z | (∀ a, |coefficientSamplerAmbientPoint U b o z.1 a| < 1/2) ∧
    event (coefficientSamplerChartResidues q z.1 z.2)}
  have hsmall : MeasurableSet {z : T | ∀ a,
      |coefficientSamplerAmbientPoint U b o z.1 a| < 1/2} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro a
    exact measurableSet_lt ((coefficientSamplerAmbientPoint_measurable U b o a).comp measurable_fst).abs
      measurable_const
  have hread : Measurable (fun z : T => coefficientSamplerChartResidues q z.1 z.2) := by
    apply Measurable.of_eval
    intro j
    apply Measurable.of_eval
    intro e
    apply Measurable.of_eval
    intro i
    cases i with
    | inl i =>
      exact (measurable_of_countable (fun v : ℤ => (v : ZMod q))).comp
        ((measurable_pi_apply e).comp ((measurable_pi_apply i).comp
          (measurable_snd.comp ((measurable_pi_apply j).comp measurable_fst))))
    | inr i =>
      exact (measurable_pi_apply i).comp ((measurable_pi_apply e).comp
        ((measurable_pi_apply j).comp measurable_snd))
  have hchart : MeasurableSet chart := hsmall.inter
    (hread (Set.toFinite {r | event r}).measurableSet)
  have instS : StandardBorelSpace (CoefficientSamplerArrays (K := K) I n) := by infer_instance
  have instR : StandardBorelSpace (CoefficientDeckResidues (K := K) E q) := by infer_instance
  let : StandardBorelSpace T := @StandardBorelSpace.prod _ _ _ _ instS instR
  have himage := hchart.image_of_measurable_injOn
    (canonicalCoefficientDeckSample_measurable U bW b hb o q)
    ((canonicalCoefficientDeckSample_injOn_smallAmbient U bW b hb o q (NeZero.pos q)).mono
      (fun _ hz => hz.1))
  convert himage using 1
  ext y
  constructor
  · rintro ⟨x, r, hs, hy, he⟩
    exact ⟨(x,r), ⟨hs,he⟩, hy⟩
  · rintro ⟨⟨x,r⟩, ⟨hs,he⟩, hy⟩
    exact ⟨x,r,hs,hy,he⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical
variable {K : Type*} [Fintype K] {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

omit [Fintype K] in
theorem coefficientEventRead_chart_identity (q : ℕ) [NeZero q]
    (sample : CoefficientSamplerArrays (K := K) I n) (y : CoefficientTorus (K := K) U)
    (hbase : quotientIntegerCover (coefficientIntegerLattice U) q y =
      canonicalCoefficientSample U b hb o sample)
    (hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o sample a| < 1/2)
    (read : CoefficientChartResidues K n E q)
    (hread : ∀ event : CoefficientChartResidues K n E q → Prop,
      coefficientDeckChartEvent U bW b hb o q event y ↔ event read) :
    canonicalCoefficientDeckSample U bW b hb o q (NeZero.pos q) sample
      (fun j a i => read j a (.inr i)) = y := by
  obtain ⟨r, hr, _⟩ := canonicalCoefficientDeckSample_existsUnique_residue
    U bW b hb o q (NeZero.pos q) sample y hbase
  have hevent := (hread (fun r => r = read)).mpr rfl
  rw [← hr, coefficientDeckChartEvent_sample_iff U bW b hb o q _ sample hsmall r] at hevent
  have he : r = (fun j a i => read j a (.inr i)) := by
    funext j a i
    exact congrFun (congrFun (congrFun hevent j) a) (.inr i)
  simpa only [he] using hr

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*}

theorem coefficientEventRead_jet_chart (root : K → ℤ) (D : Matrix α K ℤ)
    (rows : ∀ j, O j → Finset α) (q : ℕ) [NeZero q]
    (sample : CoefficientSamplerArrays (K := K) I n) (y : CoefficientTorus (K := K) U)
    (hbase : quotientIntegerCover (coefficientIntegerLattice U) q y =
      canonicalCoefficientSample U b hb o sample)
    (hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o sample a| < 1/2)
    (read : CoefficientChartResidues K n E q)
    (hread : ∀ event : CoefficientChartResidues K n E q → Prop,
      coefficientDeckChartEvent U bW b hb o q event y ↔ event read) :
    euclideanCoefficientJetMap U root D rows y =
      coveredJetChart U b hb bW q (mixedCoveredJetCoordinates U o q
        (canonicalCoefficientJetArrays root D rows sample,
          coefficientDeckJetMap root D rows q (fun j a i => read j a (.inr i)))) := by
  rw [← coefficientEventRead_chart_identity U bW b hb o q sample y hbase hsmall read hread]
  exact canonicalCoefficientDeckSample_chart U o root D rows b hb bW q sample _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped Classical

variable {K X : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

theorem affineCoefficientCoverSample_center_measurable {C : Type*} [MeasurableSpace C]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (poly j) d ∈ U j)
    (c : C → ∀ j, U j) (hc : Measurable c) (a : X → ℤ)
    (z : Option K × X → ℤ) (q : ℕ) :
    Measurable (fun center => affineCoefficientCoverSample U
      (fun j => translate (fun x => (a x : ℝ)) (subtractConstant (c center j).val (poly j)))
      (fun j => coefficients_translate_mem (U j) (fun x => (a x : ℝ)) _
        (coefficients_subtractConstant_mem (U j) (c center j) (poly j) (hm j)))
      q (fun k x => (z (k,x) : ℝ))) := by
  have hcarray : Measurable (fun center => constantCoefficientArray (K := K) U
      (fun s => c center s.1)) := by
    apply Measurable.of_eval
    intro s
    by_cases hs : s.2.val = 0
    · simpa only [constantCoefficientArray, LinearMap.coe_mk, AddHom.coe_mk, hs, ite_true, Function.comp_def] using
        (measurable_pi_apply s.1).comp hc
    · simpa only [constantCoefficientArray, LinearMap.coe_mk, AddHom.coe_mk, hs, ite_false] using
        (measurable_const : Measurable (fun _ : C => (0 : U s.1)))
  have hcentered : Measurable (fun center => centeredAffineCoefficientArray U poly hm (c center)
      (fun k x => (jointIntegerFrame (a,z) k x : ℝ))) :=
    measurable_const.sub hcarray
  have hq := (show Continuous (QuotientAddGroup.mk' (coefficientIntegerLattice (K := K) U)) from
    QuotientAddGroup.continuous_mk).measurable.comp (hcentered.const_smul (q : ℝ)⁻¹)
  convert hq using 1
  funext center
  apply congrArg (fun v : CoefficientArray (K := K) U =>
    QuotientAddGroup.mk' (coefficientIntegerLattice U) ((q : ℝ)⁻¹ • v))
  exact (affineSampleCoefficientArray_joint_frame U
    (fun j => subtractConstant (c center j).val (poly j))
    (fun j => coefficients_subtractConstant_mem (U j) (c center j) (poly j) (hm j)) a z).trans
      (affineSampleCoefficientArray_subtractConstant U poly hm (c center) _)

variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [CompactSpace (CoefficientTorus (K := K) U)]

theorem coefficientDeckChartEvent_center_measurableSet {C : Type*} [MeasurableSpace C]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (poly j) d ∈ U j)
    (c : C → ∀ j, U j) (hc : Measurable c) (a : X → ℤ)
    (z : Option K × X → ℤ) (q : ℕ) [NeZero q]
    (event : CoefficientChartResidues K n E q → Prop) :
    MeasurableSet {center | coefficientDeckChartEvent U bW b hb o q event
      (affineCoefficientCoverSample U
        (fun j => translate (fun x => (a x : ℝ)) (subtractConstant (c center j).val (poly j)))
        (fun j => coefficients_translate_mem (U j) (fun x => (a x : ℝ)) _
          (coefficients_subtractConstant_mem (U j) (c center j) (poly j) (hm j)))
        q (fun k x => (z (k,x) : ℝ)))} :=
  (coefficientDeckChartEvent_measurableSet U bW b hb o q event).preimage
    (affineCoefficientCoverSample_center_measurable U poly hm c hc a z q)

end Erdos3.VectorPolynomial

end

end OAI
