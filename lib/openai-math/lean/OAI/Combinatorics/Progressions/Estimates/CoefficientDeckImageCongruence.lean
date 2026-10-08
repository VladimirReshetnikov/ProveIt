/- Modified for ProveIt: import Lean 4.32 compatibility declarations and
supply explicit finite/sigma-finite product-measure instances for the
older Mathlib instance search. Statements are unchanged. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.CoefficientDeckCoordinates
import OAI.Combinatorics.Progressions.Geometry.CoefficientJetCoordinates
import OAI.Combinatorics.Progressions.Probability.CanonicalCoverLaw
import OAI.Combinatorics.Progressions.Probability.UniformImageLawCongruence

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

theorem uniformPMF_pi_map {T : Type*} [Fintype T] [DecidableEq T] {X Y : T → Type*}
    [∀ t, Fintype (X t)] [∀ t, Nonempty (X t)] [∀ t, Fintype (Y t)]
    (f : ∀ t, X t → Y t) (y : ∀ t, Y t) :
    ((PMF.uniformOfFintype (∀ t, X t)).map (fun x t => f t (x t)) y).toReal =
      ∏ t, ((PMF.uniformOfFintype (X t)).map (f t) (y t)).toReal := by
  simp_rw [pmf_map_toReal_indicator, tsum_fintype]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hi : (if (fun t => f t (x t)) = y then (1 : ℝ) else 0) =
      ∏ t, if f t (x t) = y t then (1 : ℝ) else 0 := by
    by_cases h : (fun t => f t (x t)) = y
    · have he t := congrFun h t
      simp only [he, ite_true, Finset.prod_const_one]
    · have hn : ¬ ∀ t, f t (x t) = y t := fun he => h (funext he)
      obtain ⟨t, ht⟩ := not_forall.mp hn
      rw [ite_eq_right h]
      exact (Finset.prod_eq_zero (Finset.mem_univ t) (ite_eq_right ht)).symm
  rw [hi]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Fintype.card_pi, Nat.cast_prod, ENNReal.toReal_prod, Finset.prod_inv_distrib,
    Finset.prod_mul_distrib]

theorem uniformPMF_map_coordinates {X X' Y Y' : Type*}
    [Fintype X] [Nonempty X] [Fintype X'] [Nonempty X']
    (a : X ≃ X') (b : Y ≃ Y') (f : X → Y) (y : Y) :
    (PMF.uniformOfFintype X).map f y =
      (PMF.uniformOfFintype X').map (fun x => b (f (a.symm x))) (b y) := by
  have h : ((PMF.uniformOfFintype X).map f).map b =
      (PMF.uniformOfFintype X').map (fun x => b (f (a.symm x))) := by
    rw [← uniformPMF_map_equiv a.symm, PMF.map_comp, PMF.map_comp]
    rfl
  rw [← h]
  exact (pmf_map_injective_at _ b b.injective y).symm

theorem uniformPMF_transposed_images {T : Type*} [Fintype T] [DecidableEq T]
    {A B C V : T → Type*} [∀ t, Fintype (A t)] [∀ t, DecidableEq (A t)]
    [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]
    [∀ t, Fintype (C t)] [∀ t, DecidableEq (C t)]
    [∀ t, Fintype (V t)] [∀ t, Nonempty (V t)]
    (f : ∀ t, (A t → V t) → (C t → V t)) (y : ∀ t, C t → B t → V t) :
    ((PMF.uniformOfFintype (∀ t, A t → B t → V t)).map
      (fun x t c b => f t (fun a => x t a b) c) y).toReal =
      ∏ t, ∏ b, ((PMF.uniformOfFintype (A t → V t)).map (f t) (fun c => y t c b)).toReal := by
  let a : (∀ t, A t → B t → V t) ≃ (∀ t, B t → A t → V t) :=
    Equiv.piCongrRight fun t => Equiv.piComm (fun _ : A t => fun _ : B t => V t)
  let b : (∀ t, C t → B t → V t) ≃ (∀ t, B t → C t → V t) :=
    Equiv.piCongrRight fun t => Equiv.piComm (fun _ : C t => fun _ : B t => V t)
  rw [uniformPMF_map_coordinates a b]
  change ((PMF.uniformOfFintype (∀ t, B t → A t → V t)).map
    (fun x t b => f t (x t b)) (fun t b c => y t c b)).toReal = _
  refine (uniformPMF_pi_map (fun t (x : B t → A t → V t) b => f t (x b))
    (fun t b c => y t c b)).trans ?_
  apply Finset.prod_congr rfl
  intro t _
  exact uniformPMF_pi_map (fun _ : B t => f t) (fun b c => y t c b)

theorem uniformPMF_product_image {X R S : Type*}
    [MeasurableSpace X] [MeasurableSpace R] [MeasurableSpace S]
    [Fintype R] [Nonempty R] [MeasurableSingletonClass R]
    (ρ : Measure X) [SFinite ρ] (f : R → S) :
    (ρ.prod (PMF.uniformOfFintype R).toMeasure).map (fun p => (p.1, f p.2)) =
      ρ.prod ((PMF.uniformOfFintype R).map f).toMeasure := by
  have hf : Measurable f := measurable_of_finite _
  have h := Measure.map_prod_map ρ (PMF.uniformOfFintype R).toMeasure measurable_id hf
  rw [Measure.map_id, PMF.toMeasure_map f _ hf] at h
  exact h.symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem boundedCoefficientJetMatrix_mulVec {α K O : Type*}
    [DecidableEq α] [Fintype K] (root : K → ℤ) (D : Matrix α K ℤ)
    (h : ℕ) (rows : O → Finset α) (x : BoundedIntegerExponent K h → ℤ) :
    boundedCoefficientJetMatrix root D h rows *ᵥ
        (fun e => x (boundedCoefficientIntegerExponentEquiv K h e)) =
      boundedDegreeIntegerJetMatrix root D h rows *ᵥ x := by
  ext o
  exact Fintype.sum_equiv (boundedCoefficientIntegerExponentEquiv K h) _ _ (fun _ => rfl)

theorem boundedCoefficientJetMatrix_range {α K O : Type*}
    [DecidableEq α] [Fintype K] (root : K → ℤ) (D : Matrix α K ℤ)
    (h : ℕ) (rows : O → Finset α) :
    (boundedCoefficientJetMatrix root D h rows).mulVecLin.range =
      (boundedDegreeIntegerJetMatrix root D h rows).mulVecLin.range := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    let e := boundedCoefficientIntegerExponentEquiv K h
    refine ⟨fun d => x (e.symm d), ?_⟩
    have he := boundedCoefficientJetMatrix_mulVec root D h rows (fun d => x (e.symm d))
    have hi : (fun d => x (e.symm (boundedCoefficientIntegerExponentEquiv K h d))) = x :=
      funext (fun d => congrArg x (e.symm_apply_apply d))
    rw [hi] at he
    exact he.symm.trans hx
  · rintro ⟨x, hx⟩
    exact ⟨_, (boundedCoefficientJetMatrix_mulVec root D h rows x).trans hx⟩

theorem boundedCoefficientJetMatrix_multiplier {α K O : Type*}
    [DecidableEq α] [Fintype K] (root : K → ℤ) (D : Matrix α K ℤ)
    (h : ℕ) (rows : O → Finset α) (v : O → ℤ) :
    coefficientImageMultiplier (boundedCoefficientJetMatrix root D h rows) v =
      coefficientImageMultiplier (boundedDegreeIntegerJetMatrix root D h rows) v := by
  classical
  exact congrArg (fun L : Submodule ℤ (O → ℤ) =>
    if v ∈ L then (L.toAddSubgroup.index : ℝ) else 0)
    (boundedCoefficientJetMatrix_range root D h rows)

theorem boundedCoefficientJetMatrix_mask {α K O : Type*}
    [DecidableEq α] [Fintype K] (root : K → ℤ) (D : Matrix α K ℤ)
    (h : ℕ) (rows : O → Finset α) (P : O → ℝ) (f : (O → ℝ) → ℝ) (v : O → ℤ) :
    coefficientImageMask (boundedCoefficientJetMatrix root D h rows) P f v =
      coefficientImageMask (boundedDegreeIntegerJetMatrix root D h rows) P f v := by
  simp only [coefficientImageMask_eq_multiplier, boundedCoefficientJetMatrix_multiplier]

theorem boundedCoefficientJetMatrix_index_le {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℕ) [NeZero a]
    (hperiod : integerScalarLattice α (a : ℤ) ≤ D.mulVecLin.range)
    (h : ℕ) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hdegree : ∀ o, (rows o).card ≤ h) :
    (boundedCoefficientJetMatrix root D h rows).mulVecLin.range.toAddSubgroup.index ≤
      (a ^ h) ^ Fintype.card O := by
  rw [boundedCoefficientJetMatrix_range]
  exact boundedDegreeIntegerJetMatrix_index_le root D a hperiod h rows hinj hdegree

theorem boundedCoefficientJetMatrix_residue_iff {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℕ)
    (hperiod : integerScalarLattice α (a : ℤ) ≤ D.mulVecLin.range)
    (s h : ℕ) (hh : h ≤ s) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hdegree : ∀ o, (rows o).card ≤ h) (v : O → ℤ) :
    v ∈ (boundedCoefficientJetMatrix root D h rows).mulVecLin.range ↔
      ∃ x : VectorPolynomial.BoundedCoefficientExponent K h → ZMod (a ^ s),
        integerResidueMatrix (boundedCoefficientJetMatrix root D h rows) (a ^ s) *ᵥ x =
          integerResidueMap O (a ^ s) v := by
  have hp : integerScalarLattice O ((a ^ s : ℕ) : ℤ) ≤
      (boundedCoefficientJetMatrix root D h rows).mulVecLin.range := by
    rw [boundedCoefficientJetMatrix_range, Nat.cast_pow]
    exact boundedDegreeIntegerJetMatrix_common_period root D (a : ℤ) hperiod s h hh rows hinj hdegree
  exact integerMatrixImage_residue_iff _ (a ^ s) hp v

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

attribute [local irreducible] coefficientDeckKernelEquiv

variable {K : Type*} [Fintype K] {m : ℕ} {J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

noncomputable def canonicalCoefficientDeckSample (d : ℕ) (hd : 0 < d)
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) B d) :
    CoefficientTorus (K := K) U :=
  canonicalCoefficientCoverLift U b hb o d x + (coefficientDeckKernelEquiv U bW d hd r).val

omit [Fintype K] in
theorem canonicalCoefficientDeckSample_coordinate (d : ℕ) (hd : 0 < d)
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) B d)
    (j : Fin m) (e : BoundedCoefficientExponent K (j.val + 1)) :
    euclideanCoefficientEquiv U (canonicalCoefficientDeckSample U bW b hb o d hd x r) j e =
      normalizedCoverLift (euclideanSubspace (U j)) (b j) (hb j) d
        (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (x j) e)) +
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd (r j e)).val := by
  simp only [canonicalCoefficientDeckSample, map_add, Pi.add_apply,
    coefficientDeckKernelEquiv_coordinate, canonicalCoefficientCoverLift, AddEquiv.apply_symm_apply]

omit [Fintype K] in
theorem canonicalCoefficientDeckSample_projection (d : ℕ) (hd : 0 < d)
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) B d) :
    quotientIntegerCover (coefficientIntegerLattice (K := K) U) d
        (canonicalCoefficientDeckSample U bW b hb o d hd x r) = canonicalCoefficientSample U b hb o x := by
  rw [canonicalCoefficientDeckSample, map_add, canonicalCoefficientCoverLift_projection U b hb o d hd,
    (coefficientDeckKernelEquiv U bW d hd r).property, add_zero]

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

theorem canonicalCoefficientDeckSample_measurable (d : ℕ) [NeZero d] :
    Measurable (fun p : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d =>
      canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2) := by
  exact ((canonicalCoefficientCoverLift_measurable U b hb o d).comp measurable_fst).add
    ((measurable_subtype_coe.comp (measurable_of_finite
      (coefficientDeckKernelEquiv U bW d (Nat.pos_of_ne_zero (NeZero.ne d))))).comp measurable_snd)

theorem canonicalCoefficientDeckSample_relabel (d : ℕ) [NeZero d]
    [Fintype (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker]
    (ρ : Measure (CoefficientSamplerArrays (K := K) I n)) [SFinite ρ] :
    (ρ.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure).map
        (fun x : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d =>
          canonicalCoefficientDeckSample (K := K) U bW b hb o d
            (Nat.pos_of_ne_zero (NeZero.ne d)) x.1 x.2) =
      finiteKernelLiftLaw (G := CoefficientTorus (K := K) U) (H := CoefficientTorus (K := K) U)
        (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d) ρ
        (canonicalCoefficientCoverLift (K := K) U b hb o d) := by
  let e : CoefficientDeckResidues (K := K) B d ≃
      (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker :=
    (coefficientDeckKernelEquiv (K := K) (J := J) (B := B) U bW d
      (Nat.pos_of_ne_zero (NeZero.ne d))).toEquiv
  have he : Measurable e := measurable_of_finite _
  have hm : (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure.map e =
      (PMF.uniformOfFintype
        (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker).toMeasure := by
    rw [PMF.toMeasure_map e _ he, uniformPMF_map_equiv e]
  have hp := Measure.map_prod_map ρ
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure measurable_id he
  rw [Measure.map_id, hm] at hp
  have hg : Measurable (fun p : CoefficientSamplerArrays (K := K) I n ×
      (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker =>
        canonicalCoefficientCoverLift U b hb o d p.1 + p.2.val) :=
    ((canonicalCoefficientCoverLift_measurable U b hb o d).comp measurable_fst).add
      (measurable_subtype_coe.comp measurable_snd)
  rw [finiteKernelLiftLaw, hp, Measure.map_map hg (measurable_id.prodMap he)]
  rfl

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include ν in
theorem canonicalCoefficientDeckSample_law
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (hw : ∀ j i e, 0 < w j i e)
    (hs : ∀ j e x, mixedCoefficientDensity (fun i => c j i e) (fun i => w j i e)
      (fun i => p j i e) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j))
    (d : ℕ) [NeZero d] :
    ((Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))).prod
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure).map
        (fun x : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d =>
          canonicalCoefficientDeckSample (K := K) U bW b hb o d
          (Nat.pos_of_ne_zero (NeZero.ne d)) x.1 x.2) =
      realDensityMeasure μ (fun y => canonicalCoefficientDensity U b hb o c w p
        (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d y)) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  let _ := coefficientCoverKernelFintype (K := K) U d hd
  let : ∀ j, IsProbabilityMeasure (mixedScalarArrayLaw (c j) (w j) (p j)) :=
    fun j => mixedScalarArrayLaw_probability _ _ (hw j) _
  let : IsProbabilityMeasure (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))) :=
    Measure.pi.instIsProbabilityMeasure _
  let : IsFiniteMeasure (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))) :=
    ⟨by simp [measure_univ]⟩
  let : SigmaFinite (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j))) :=
    IsFiniteMeasure.toSigmaFinite _
  exact (canonicalCoefficientDeckSample_relabel (K := K) U bW b hb o d
    (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j)))).trans
      (canonicalCoefficientCoverLaw (K := K) U b hb o μ ν c w p hw hs d hd)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

noncomputable def coefficientDeckJetMap (d : ℕ) :
    CoefficientDeckResidues (K := K) B d →+ (∀ j, O j → B j → ZMod d) where
  toFun r j t := ∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) t e • r j e
  map_zero' := by
    funext j t i
    simp
  map_add' r s := by
    funext j t
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

omit [Fintype α] [∀ j, Fintype (J j)] [∀ j, Fintype (B j)] in
theorem coefficientDeckJetMap_coordinate (d : ℕ) (r : CoefficientDeckResidues (K := K) B d)
    (j : Fin m) (i : B j) :
    (fun t => coefficientDeckJetMap root D rows d r j t i) =
      integerResidueMatrix (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d *ᵥ
        (fun e => r j e i) := by
  funext t
  change (∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) t e • r j e) i =
    ∑ e, ((boundedCoefficientJetMatrix root D (j.val + 1) (rows j) t e : ℤ) : ZMod d) * r j e i
  simp only [Finset.sum_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply]

theorem coefficientDeckKernel_jets (d : ℕ) (hd : 0 < d)
    (r : CoefficientDeckResidues (K := K) B d) (j : Fin m) (t : O j) :
    euclideanCoefficientJetMap U root D rows (coefficientDeckKernelEquiv U bW d hd r).val j t =
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd (coefficientDeckJetMap root D rows d r j t)).val := by
  rw [euclideanCoefficientJetMap_apply]
  simp_rw [coefficientDeckKernelEquiv_coordinate]
  let f := ((quotientIntegerCover
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup d).ker.subtype).comp
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd).toAddMonoidHom
  change (∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) t e • f (r j e)) =
    f (∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) t e • r j e)
  simp only [map_sum, map_zsmul]

variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem canonicalCoefficientDeckSample_jets (d : ℕ) (hd : 0 < d)
    (x : CoefficientSamplerArrays (K := K) I n) (r : CoefficientDeckResidues (K := K) B d)
    (j : Fin m) (t : O j) :
    euclideanCoefficientJetMap U root D rows (canonicalCoefficientDeckSample U bW b hb o d hd x r) j t =
      euclideanCoefficientJetMap U root D rows (canonicalCoefficientCoverLift U b hb o d x) j t +
      (coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd (coefficientDeckJetMap root D rows d r j t)).val := by
  simp only [canonicalCoefficientDeckSample, map_add, Pi.add_apply,
    coefficientDeckKernel_jets]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

omit [Fintype α] in
theorem coefficientDeckJetMap_joint_mask (d : ℕ) [NeZero d]
    (hperiod : ∀ j, integerScalarLattice (O j) (d : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range)
    (v : ∀ j, O j → B j → ℤ) :
    ((PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).map
      (coefficientDeckJetMap root D rows d) (fun j t i => (v j t i : ZMod d))).toReal =
        ∏ j, ∏ i, coefficientImageMultiplier
          (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) (fun t => v j t i) /
            (d : ℝ) ^ Fintype.card (O j) := by
  have he : (coefficientDeckJetMap (B := B) root D rows d :
      CoefficientDeckResidues (K := K) B d → (∀ j, O j → B j → ZMod d)) =
      (fun x j t i => (integerResidueMatrix
        (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d *ᵥ
          (fun e => x j e i)) t) := by
    funext x j t i
    exact congrFun (coefficientDeckJetMap_coordinate root D rows d x j i) t
  rw [he]
  refine (uniformPMF_transposed_images
    (A := fun j : Fin m => BoundedCoefficientExponent K (j.val + 1))
    (B := B) (C := O) (V := fun _ => ZMod d)
    (fun j x => integerResidueMatrix
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d *ᵥ x)
    (fun j t i => (v j t i : ZMod d))).trans ?_
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro i _
  exact uniformResidueMatrix_image_mask (I := O j)
    (J := BoundedCoefficientExponent K (j.val + 1))
    (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d (hperiod j) (fun t => v j t i)

theorem coefficientDeckJetMap_commonPeriod_mask (a : ℕ) [NeZero a]
    (hperiod : integerScalarLattice α (a : ℤ) ≤ D.mulVecLin.range)
    (s : ℕ) (hs : m ≤ s) (hinj : ∀ j, Function.Injective (rows j))
    (hdegree : ∀ j t, (rows j t).card ≤ j.val + 1) (v : ∀ j, O j → B j → ℤ) :
    ((PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B (a ^ s))).map
      (coefficientDeckJetMap root D rows (a ^ s))
        (fun j t i => (v j t i : ZMod (a ^ s)))).toReal =
      ∏ j, ∏ i, coefficientImageMultiplier
        (boundedDegreeIntegerJetMatrix root D (j.val + 1) (rows j)) (fun t => v j t i) /
          ((a ^ s : ℕ) : ℝ) ^ Fintype.card (O j) := by
  have hp (j : Fin m) : integerScalarLattice (O j) ((a ^ s : ℕ) : ℤ) ≤
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range := by
    rw [boundedCoefficientJetMatrix_range, Nat.cast_pow]
    exact boundedDegreeIntegerJetMatrix_common_period root D (a : ℤ) hperiod s (j.val + 1)
      ((Nat.succ_le_of_lt j.isLt).trans hs) (rows j) (hinj j) (hdegree j)
  simpa only [boundedCoefficientJetMatrix_multiplier] using
    coefficientDeckJetMap_joint_mask root D rows (a ^ s) hp v

omit [Fintype α] [∀ j, Fintype (O j)] in
theorem coefficientDeckJetMap_independent_source {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) [SFinite ρ] (d : ℕ) [NeZero d] :
    (ρ.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure).map
        (fun p => (p.1, coefficientDeckJetMap root D rows d p.2)) =
      ρ.prod ((PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).map
        (coefficientDeckJetMap root D rows d)).toMeasure :=
  uniformPMF_product_image ρ (coefficientDeckJetMap root D rows d)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

omit [∀ j, Fintype (O j)] [∀ j, Fintype (B j)] in
theorem coefficientDeckJetMap_mem_range_iff (d : ℕ)
    (v : ∀ j, O j → B j → ZMod d) :
    v ∈ (coefficientDeckJetMap root D rows d).range ↔
      ∀ j (i : B j), (fun t => v j t i) ∈
        (integerResidueMatrix (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d).mulVecLin.toAddMonoidHom.range := by
  constructor
  · rintro ⟨a, rfl⟩ j i
    exact ⟨(fun e => a j e i), (coefficientDeckJetMap_coordinate root D rows d a j i).symm⟩
  · intro h
    change ∀ j (i : B j), ∃ a, integerResidueMatrix
      (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) d *ᵥ a = (fun t => v j t i) at h
    choose a ha using h
    refine ⟨(fun j e i => a j i e), ?_⟩
    funext j t i
    exact (congrFun (coefficientDeckJetMap_coordinate root D rows d (fun j e i => a j i e) j i) t).trans
      (congrFun (ha j i) t)

omit [∀ j, Fintype (O j)] [∀ j, Fintype (B j)] in
theorem coefficientDeckJetMap_range_eq_of_integer_range_eq
    (root' : K → ℤ) (D' : Matrix α K ℤ)
    (h : ∀ j, (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range =
      (boundedCoefficientJetMatrix root' D' (j.val + 1) (rows j)).mulVecLin.range)
    (d : ℕ) :
    (coefficientDeckJetMap (B := B) root D rows d).range =
      (coefficientDeckJetMap (B := B) root' D' rows d).range := by
  ext v
  simp only [coefficientDeckJetMap_mem_range_iff]
  apply forall_congr'
  intro j
  apply forall_congr'
  intro i
  rw [integerResidueMatrix_range_eq_of_integer_range_eq _ _ (h j) d]

theorem coefficientDeckJetMap_law_eq_of_integer_range_eq
    (root' : K → ℤ) (D' : Matrix α K ℤ)
    (h : ∀ j, (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)).mulVecLin.range =
      (boundedCoefficientJetMatrix root' D' (j.val + 1) (rows j)).mulVecLin.range)
    (d : ℕ) [NeZero d] :
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).map
      (coefficientDeckJetMap root D rows d) =
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).map
        (coefficientDeckJetMap root' D' rows d) :=
  uniformPMF_map_hom_eq_of_range_eq _ _
    (coefficientDeckJetMap_range_eq_of_integer_range_eq root D rows root' D' h d)

end Erdos3.VectorPolynomial

end

end OAI
