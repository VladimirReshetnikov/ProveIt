/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
 Use older set-comprehension and discrete-subgroup names; statements unchanged.
Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Compat.Set
import OAI.Compat.Isometry
import OAI.Combinatorics.Progressions.Dynamics.LocalizedAverageScaleBudget
import OAI.Combinatorics.Progressions.Estimates.NativeSpaceMap
import OAI.Combinatorics.Progressions.Estimates.RealificationModuleTopology
import OAI.Combinatorics.Progressions.Fourier.BohrTorusApproximation
import OAI.Combinatorics.Progressions.Fourier.RealQuarterTorusExtension
import OAI.Combinatorics.Progressions.Geometry.CoordinateQuotientModel
import OAI.Combinatorics.Progressions.Geometry.StepOneCoordinateMetric
import OAI.Combinatorics.Progressions.Lattices.RationalLatticeFunctional

namespace OAI

section

namespace Erdos3.RationalTorus

open Module

def Algebra (d : ℕ) := Fin d → ℚ

instance (d : ℕ) : AddCommGroup (Algebra d) :=
  inferInstanceAs (AddCommGroup (Fin d → ℚ))

instance (d : ℕ) : Module ℚ (Algebra d) :=
  inferInstanceAs (Module ℚ (Fin d → ℚ))

instance (d : ℕ) : LieRing (Algebra d) where
  toAddCommGroup := inferInstanceAs (AddCommGroup (Fin d → ℚ))
  bracket _ _ := 0
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := rfl
  leibniz_lie _ _ _ := by simp

instance (d : ℕ) : LieAlgebra ℚ (Algebra d) where
  toModule := inferInstanceAs (Module ℚ (Fin d → ℚ))
  lie_smul _ _ _ := by
    change (0 : Algebra d) = _ • (0 : Algebra d)
    exact (smul_zero _).symm

theorem lie_eq_zero {d : ℕ} (x y : Algebra d) : ⁅x, y⁆ = 0 := rfl

noncomputable def basis (d : ℕ) : Basis (Fin d) ℚ (Algebra d) := by
  change Basis (Fin d) ℚ (Fin d → ℚ)
  exact Pi.basisFun ℚ (Fin d)

theorem basis_repr (d : ℕ) (x : Algebra d) (i : Fin d) : (basis d).repr x i = x i := by
  change Fin d → ℚ at x
  exact Pi.basisFun_repr ℚ (Fin d) x i

theorem basis_equivFun (d : ℕ) (x : Algebra d) : (basis d).equivFun x = x := by
  ext i
  exact basis_repr d x i

theorem basis_equivFun_symm (d : ℕ) (x : Fin d → ℚ) : (basis d).equivFun.symm x = x := by
  have h := basis_equivFun d ((basis d).equivFun.symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

def filtration (d : ℕ) : NilpotentLieFiltration (Algebra d) 1 where
  layer j := if j ≤ 1 then ⊤ else ⊥
  antitone := by
    intro i j hij
    by_cases hj : j ≤ 1
    · have hi := hij.trans hj
      simp only [hi, hj, ite_true, le_refl]
    · simp only [hj, ite_false, bot_le]
  one_eq_top := by simp
  lie_mem := by
    intro i j a b _ _
    rw [lie_eq_zero]
    exact Submodule.zero_mem _
  terminal := by simp

theorem basis_layers (d j : ℕ) :
    (filtration d).layer j = Submodule.span ℚ ((basis d) '' {_i : Fin d | j ≤ (1 : ℕ)}) := by
  by_cases hj : j ≤ 1
  · simpa only [filtration, hj, ite_true, Set.setOf_true, Set.image_univ] using (basis d).span_eq.symm
  · simp only [filtration, hj, ite_false, Set.setOf_false, Set.image_empty, Submodule.span_empty]

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_step_one_character :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L 1 d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → ∀ η : L →ₗ[ℚ] ℚ,
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ p) →
      (∀ z : D.RealGroup, z ∈ D.realLattice → ∃ n : ℤ, realifyFunctional η z.coord = n) →
      ∃ f : D.Space → ℂ,
        (letI := D.metricSpace; LipschitzWith ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ f) ∧
        (∀ x, ‖f x‖ = 1) ∧
        ∀ z : D.RealGroup, f (QuotientGroup.mk z) = logCharacter (realifyFunctional η) z := by
  obtain ⟨C, hC, hseed⟩ := exists_native_central_seed 1
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD η hη hint
  let := D.metricSpace
  obtain ⟨K, hK, f, hLip, _, heq⟩ := hseed D hp hD η hη hint
  have heq' (z : D.RealGroup) : f (QuotientGroup.mk z) = logCharacter (realifyFunctional η) z :=
    heq z (by rw [D.filtration.realification.subgroup_one]; trivial)
  refine ⟨f, hLip.weaken hK, ?_, heq'⟩
  intro x
  induction x using Quotient.inductionOn with
  | h z => rw [heq', logCharacter_norm]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalTorus

open Module

noncomputable def lattice (d : ℕ) : Subgroup (filtration d).Group where
  carrier := {g | IntegralVector g.coord}
  one_mem' := ⟨0, fun _ => rfl⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨z, hz⟩ := ha
    obtain ⟨w, hw⟩ := hb
    refine ⟨z + w, ?_⟩
    intro i
    rw [(filtration d).stepOne_coord_mul]
    change a.coord i + b.coord i = ((z + w) i : ℚ)
    simp only [Pi.add_apply, Int.cast_add, hz, hw]
  inv_mem' := by
    intro a ha
    obtain ⟨z, hz⟩ := ha
    refine ⟨-z, ?_⟩
    intro i
    change -(a.coord i) = ((-z) i : ℚ)
    simp only [Pi.neg_apply, Int.cast_neg, hz]

theorem lattice_coordinates (d : ℕ) :
    bchSubgroupCoordinates (basis d) (lattice d) = {x | IntegralVector x} := by
  ext x
  change IntegralVector ((basis d).equivFun.symm x) ↔ IntegralVector x
  rw [basis_equivFun_symm]

theorem lattice_inner_grid (d : ℕ) :
    scaledIntegerGrid 1 ⊆ bchSubgroupCoordinates (basis d) (lattice d) := by
  rw [lattice_coordinates]
  rintro x ⟨z, rfl⟩
  exact ⟨z, fun i => by simp⟩

theorem lattice_outer_grid (d : ℕ) :
    bchSubgroupCoordinates (basis d) (lattice d) ⊆ denominatorGrid 1 := by
  rw [lattice_coordinates]
  intro x hx
  simpa only [denominatorGrid, Set.mem_ofPred_eq, Nat.cast_one, one_smul] using hx

noncomputable def nilmanifold (d : ℕ) : RationalFilteredNilmanifold (Algebra d) 1 d :=
  (filtration d).ofAdaptedBasis (basis d) (fun _ => 1) (basis_layers d)
    (lattice d) 1 (by decide) (lattice_inner_grid d) (lattice_outer_grid d)

theorem nilmanifold_geometry (d : ℕ) {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) :
    (nilmanifold d).GeometryComplexityLE p := by
  apply (filtration d).ofAdaptedBasis_geometry (basis d) (fun _ => 1) (basis_layers d)
    (lattice d) 1 (by decide) (lattice_inner_grid d) (lattice_outer_grid d) hp hd
  · simpa only [Nat.cast_one] using Real.one_le_exp hp
  · intro i j k
    simpa [lieStructureConstants, lie_eq_zero, rationalLogHeight] using hp

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalTorus

open scoped TensorProduct

noncomputable instance instRealTopology (d : ℕ) : TopologicalSpace (ℝ ⊗[ℚ] Algebra d) :=
  moduleTopology ℝ (ℝ ⊗[ℚ] Algebra d)

instance instRealTopologicalAddGroup (d : ℕ) : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra d) :=
  IsModuleTopology.topologicalAddGroup ℝ _

instance instRealContinuousSMul (d : ℕ) : ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra d) :=
  ModuleTopology.continuousSMul ℝ _

instance instRealT2Space (d : ℕ) : T2Space (ℝ ⊗[ℚ] Algebra d) :=
  realification_moduleTopology_t2 (basis d)

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalTorus

open scoped TensorProduct

noncomputable def phaseCoordinates (d : ℕ) (g : (nilmanifold d).RealGroup) :
    Fin d → CircleFourier.Circle :=
  fun i => (((basis d).baseChange ℝ).repr g.coord i : CircleFourier.Circle)

theorem phaseCoordinates_one (d : ℕ) :
    phaseCoordinates d 1 = 0 := by
  ext i
  simp [phaseCoordinates]

theorem phaseCoordinates_mul (d : ℕ) (g h : (nilmanifold d).RealGroup) :
    phaseCoordinates d (g * h) = phaseCoordinates d g + phaseCoordinates d h := by
  ext i
  simp only [phaseCoordinates, (nilmanifold d).filtration.realification.stepOne_coord_mul,
    map_add, Finsupp.add_apply, AddCircle.coe_add, Pi.add_apply]

theorem phaseCoordinates_inv (d : ℕ) (g : (nilmanifold d).RealGroup) :
    phaseCoordinates d g⁻¹ = -phaseCoordinates d g := by
  ext i
  simp [phaseCoordinates]

theorem phaseCoordinates_lattice (d : ℕ) (g : (nilmanifold d).RealGroup)
    (hg : g ∈ (nilmanifold d).realLattice) : phaseCoordinates d g = 0 := by
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
  obtain ⟨z, hz⟩ : IntegralVector a.coord := ha
  ext i
  change ((((basis d).baseChange ℝ).equivFun
    (NilpotentLieBCHGroup.realificationHom a).coord) i : CircleFourier.Circle) = 0
  rw [NilpotentLieBCHGroup.realificationHom_coordinates]
  dsimp only
  rw [basis_repr, hz]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  refine ⟨z i, ?_⟩
  simp

noncomputable def phaseProjection (d : ℕ) :
    (nilmanifold d).Space → (Fin d → CircleFourier.Circle) :=
  Quotient.lift (phaseCoordinates d) (fun a b hab => by
    have h := phaseCoordinates_lattice d (a⁻¹ * b) (QuotientGroup.leftRel_apply.mp hab)
    apply Eq.symm
    apply sub_eq_zero.mp
    simpa only [phaseCoordinates_mul, phaseCoordinates_inv, sub_eq_add_neg, add_comm] using h)

@[simp] theorem phaseProjection_mk (d : ℕ) (g : (nilmanifold d).RealGroup) :
    phaseProjection d (QuotientGroup.mk g) = phaseCoordinates d g := rfl

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalTorus

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct NNReal

abbrev BottomQuotient (d : ℕ) := Algebra d ⧸ (⊥ : LieIdeal ℚ (Algebra d))

theorem exists_bottom_quotient_character :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d : ℕ)
      [TopologicalSpace (ℝ ⊗[ℚ] BottomQuotient d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] BottomQuotient d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] BottomQuotient d)]
      [T2Space (ℝ ⊗[ℚ] BottomQuotient d)] (i₀ : Fin d) {p : ℝ},
      0 ≤ p → (d : ℝ) ≤ p →
      ∃ (e : ℕ) (E : RationalFilteredNilmanifold (BottomQuotient d) 1 e),
        E.GeometryComplexityLE p ∧
        (∀ i j, rationalLogHeight (E.basis.repr
          (lieQuotientMap (⊥ : LieIdeal ℚ (Algebra d)) (basis d j)) i) ≤ p) ∧
        ∃ (η : BottomQuotient d →ₗ[ℚ] ℚ) (V : E.Space → ℂ),
          (∀ x, η (lieQuotientMap (⊥ : LieIdeal ℚ (Algebra d)) x) = x i₀) ∧
          (letI := E.metricSpace;
            LipschitzWith ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩ V) ∧
          (∀ x, ‖V x‖ = 1) ∧
          ∀ z : E.RealGroup, V (QuotientGroup.mk z) = logCharacter (realifyFunctional η) z := by
  obtain ⟨C, hC, hcharacter⟩ := exists_native_step_one_character
  refine ⟨C, hC, ?_⟩
  intro d _ _ _ _ i₀ p hp hd
  classical
  have hI : (filtration d).layer (1 + 1) ≤ (⊥ : LieIdeal ℚ (Algebra d)).toSubmodule := by
    rw [(filtration d).terminal]
    exact bot_le
  have hspan : (⊥ : LieIdeal ℚ (Algebra d)).toSubmodule =
      Submodule.span ℚ (basis d '' (∅ : Set (Fin d))) := by simp
  let E := (filtration d).coordinateQuotientModel (basis d) (fun _ => 1) (basis_layers d)
    (⊥ : LieIdeal ℚ (Algebra d)) hI ∅ hspan (lattice d) 1 (by decide)
    (lattice_inner_grid d) (lattice_outer_grid d)
  have hE : E.GeometryComplexityLE p := by
    apply (filtration d).coordinateQuotientModel_geometry (basis d) (fun _ => 1) (basis_layers d)
      (⊥ : LieIdeal ℚ (Algebra d)) hI ∅ hspan (lattice d) 1 (by decide)
      (lattice_inner_grid d) (lattice_outer_grid d) hp
    · simpa only [Fintype.card_fin] using hd
    · simpa only [Nat.cast_one] using Real.one_le_exp hp
    · intro i j k
      simpa [lieStructureConstants, lie_eq_zero, rationalLogHeight] using hp
  let η : BottomQuotient d →ₗ[ℚ] ℚ :=
    (⊥ : Submodule ℚ (Algebra d)).liftQ ((basis d).coord i₀) bot_le
  have hη (x : Algebra d) : η (lieQuotientMap (⊥ : LieIdeal ℚ (Algebra d)) x) = x i₀ :=
    basis_repr d x i₀
  have hproj (i) (j) : rationalLogHeight (E.basis.repr
      (lieQuotientMap (⊥ : LieIdeal ℚ (Algebra d)) (basis d j)) i) ≤ p := by
    change rationalLogHeight (((supportedQuotientBasis (basis d)
      (⊥ : Submodule ℚ (Algebra d)) ∅ hspan).reindex (Fintype.equivFin _)).repr
        ((⊥ : Submodule ℚ (Algebra d)).mkQ (basis d j)) i) ≤ p
    rw [Basis.repr_reindex_apply, supportedQuotientBasis_repr_mk]
    exact rationalLogHeight_le_of_height (basis_repr_height_one _ _ _)
      (by simpa only [Nat.cast_one] using Real.one_le_exp hp)
  have hheight (i) : rationalLogHeight (η (E.basis i)) ≤ p := by
    change rationalLogHeight (η (((supportedQuotientBasis (basis d)
      (⊥ : Submodule ℚ (Algebra d)) ∅ hspan).reindex (Fintype.equivFin _)) i)) ≤ p
    rw [Basis.reindex_apply, supportedQuotientBasis_apply]
    change rationalLogHeight ((basis d).repr (basis d _) i₀) ≤ p
    exact rationalLogHeight_le_of_height (basis_repr_height_one _ _ _)
      (by simpa only [Nat.cast_one] using Real.one_le_exp hp)
  have hint : ∀ z : E.RealGroup, z ∈ E.realLattice →
      ∃ n : ℤ, realifyFunctional η z.coord = n := by
    apply E.realLattice_functional_integral η
    intro z hz
    obtain ⟨g, hg, rfl⟩ := hz
    obtain ⟨a, ha⟩ := hg
    refine ⟨a i₀, ?_⟩
    change η (lieQuotientMap (⊥ : LieIdeal ℚ (Algebra d)) g.coord) = _
    rw [hη]
    exact ha i₀
  obtain ⟨V, hLip, hnorm, heq⟩ := hcharacter E hp hE η hheight hint
  exact ⟨_, E, hE, hproj, η, V, hη, hLip, hnorm, heq⟩

end Erdos3.RationalTorus

end

section

namespace Erdos3.CircleFourier

theorem real_phase_map_lipschitz {ι : Type*} [Fintype ι] :
    LipschitzWith 1 (fun v : ι → ℝ => fun i => (v i : Circle)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg dist_nonneg).mpr
  intro i
  change ‖(v i : Circle) - (w i : Circle)‖ ≤ dist v w
  calc
    _ = ‖((v i - w i : ℝ) : Circle)‖ := rfl
    _ ≤ ‖v i - w i‖ := QuotientAddGroup.norm_mk_le_norm
    _ = dist (v i) (w i) := rfl
    _ ≤ dist v w := dist_le_pi_dist v w i

end Erdos3.CircleFourier

namespace Erdos3.RationalTorus

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable (d : ℕ)
  [TopologicalSpace (ℝ ⊗[ℚ] Algebra d)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra d)] [T2Space (ℝ ⊗[ℚ] Algebra d)]

theorem phaseCoordinates_lipschitz :
    letI := rightMetricSpace
      (hnil := (nilmanifold d).filtration.realification.lowerCentralSeries_eq_bot)
      ((basis d).baseChange ℝ)
    LipschitzWith 1 (phaseCoordinates d) := by
  let := rightMetricSpace
    (hnil := (nilmanifold d).filtration.realification.lowerCentralSeries_eq_bot)
    ((basis d).baseChange ℝ)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hc := ((nilmanifold d).filtration.realification.stepOne_coordinates_lipschitz
    ((basis d).baseChange ℝ)).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, basisHomeomorph_apply] at hc
  have hphase : dist (phaseCoordinates d x) (phaseCoordinates d y) ≤
      dist (((basis d).baseChange ℝ).equivFun x.coord)
        (((basis d).baseChange ℝ).equivFun y.coord) := by
    change dist
      (fun i : Fin d => (((basis d).baseChange ℝ).repr x.coord i : CircleFourier.Circle))
      (fun i : Fin d => (((basis d).baseChange ℝ).repr y.coord i : CircleFourier.Circle)) ≤ _
    simpa only [NNReal.coe_one, one_mul, Basis.equivFun_apply] using
      CircleFourier.real_phase_map_lipschitz.dist_le_mul
        (((basis d).baseChange ℝ).equivFun x.coord)
        (((basis d).baseChange ℝ).equivFun y.coord)
  simpa only [NNReal.coe_one, one_mul] using hphase.trans hc

theorem phaseProjection_lipschitz :
    letI := (nilmanifold d).metricSpace
    LipschitzWith 1 (phaseProjection d) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] Algebra d) :=
    ((basis d).baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace
    (hnil := (nilmanifold d).filtration.realification.lowerCentralSeries_eq_bot)
    ((basis d).baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul
    (hnil := (nilmanifold d).filtration.realification.lowerCentralSeries_eq_bot)
    ((basis d).baseChange ℝ)
  exact rightCosetMetricSpace_lipschitz_lift (nilmanifold d).realLattice
    (nilmanifold d).realLattice_closed_discrete.1 (phaseProjection d)
    (phaseCoordinates_lipschitz d)

end Erdos3.RationalTorus

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d t : ℕ}

noncomputable def torusPhaseLinear (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t) :
    (ℝ ⊗[ℚ] L) →ₗ[ℝ] (Fin t → ℝ) :=
  ((RationalTorus.basis t).baseChange ℝ).equivFun.toLinearMap.comp (φ.toLinearMap.baseChange ℝ)

theorem torusPhaseLinear_tmul (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t)
    (a : ℝ) (x : L) (i : Fin t) :
    torusPhaseLinear φ (a ⊗ₜ[ℚ] x) i = a * (φ x i : ℝ) := by
  change ((RationalTorus.basis t).baseChange ℝ).repr
    (φ.toLinearMap.baseChange ℝ (a ⊗ₜ[ℚ] x)) i = _
  rw [LinearMap.baseChange_tmul, Module.Basis.baseChange_repr_tmul, RationalTorus.basis_repr]
  simpa [Algebra.smul_def] using mul_comm (φ x i : ℝ) a

variable (D : RationalFilteredNilmanifold L s d) (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t)

theorem torusPhaseLinear_mul (g h : D.RealGroup) :
    torusPhaseLinear φ (g * h).coord = torusPhaseLinear φ g.coord + torusPhaseLinear φ h.coord := by
  let f := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := (RationalTorus.nilmanifold t).filtration.lowerCentralSeries_eq_bot) φ
  change ((RationalTorus.basis t).baseChange ℝ).equivFun (f (g * h)).coord =
    ((RationalTorus.basis t).baseChange ℝ).equivFun (f g).coord +
      ((RationalTorus.basis t).baseChange ℝ).equivFun (f h).coord
  rw [f.map_mul, (RationalTorus.nilmanifold t).filtration.realification.stepOne_coord_mul, map_add]

theorem torusPhaseLinear_inv (g : D.RealGroup) :
    torusPhaseLinear φ g⁻¹.coord = -torusPhaseLinear φ g.coord :=
  (torusPhaseLinear φ).map_neg g.coord

variable (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice → IntegralVector (φ z.coord))

include hphase in
theorem torusPhase_lattice_map :
    D.lattice ≤ (RationalTorus.nilmanifold t).lattice.comap
      (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
        (hM := (RationalTorus.nilmanifold t).filtration.lowerCentralSeries_eq_bot) φ) := by
  intro z hz
  exact hphase z hz

noncomputable def nativeTorusProjection : D.Space → (Fin t → CircleFourier.Circle) :=
  (RationalTorus.phaseProjection t) ∘
    D.nativeSpaceMap (RationalTorus.nilmanifold t) φ (torusPhase_lattice_map D φ hphase)

theorem nativeTorusProjection_mk (g : D.RealGroup) (i : Fin t) :
    nativeTorusProjection D φ hphase (QuotientGroup.mk g) i =
      (torusPhaseLinear φ g.coord i : CircleFourier.Circle) := rfl

noncomputable def nativeTorusLocalLift : D.Space → (Fin t → ℝ) :=
  centeredTorusLift ∘ nativeTorusProjection D φ hphase

theorem nativeTorusLocalLift_mk (g : D.RealGroup)
    (hg : ∀ i, |torusPhaseLinear φ g.coord i| ≤ 1 / 4) :
    nativeTorusLocalLift D φ hphase (QuotientGroup.mk g) = torusPhaseLinear φ g.coord := by
  funext i
  exact centeredCircleLift_coe (hg i)

include hphase in
theorem torusPhaseLinear_eq_of_small (g h : D.RealGroup)
    (hg : ∀ i, |torusPhaseLinear φ g.coord i| ≤ 1 / 4)
    (hh : ∀ i, |torusPhaseLinear φ h.coord i| ≤ 1 / 4)
    (heq : (QuotientGroup.mk g : D.Space) = QuotientGroup.mk h) :
    torusPhaseLinear φ g.coord = torusPhaseLinear φ h.coord := by
  rw [← nativeTorusLocalLift_mk D φ hphase g hg, ← nativeTorusLocalLift_mk D φ hphase h hh, heq]

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem nativeTorusProjection_lipschitz {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (ht : (t : ℝ) ≤ p) (hcoords : ∀ i j, rationalLogHeight (φ (D.basis j) i) ≤ p) :
    letI := D.metricSpace
    LipschitzWith ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩
      (nativeTorusProjection D φ hphase) := by
  let := D.metricSpace
  let := (RationalTorus.nilmanifold t).metricSpace
  have hmap := D.nativeSpaceMap_lipschitz (RationalTorus.nilmanifold t) φ
    (torusPhase_lattice_map D φ hphase) hp hD (RationalTorus.nilmanifold_geometry t hp ht)
    (fun i j => by
      change rationalLogHeight ((RationalTorus.basis t).repr (φ (D.basis j)) i) ≤ p
      rw [RationalTorus.basis_repr]
      exact hcoords i j)
  have h : LipschitzWith ((1 : ℝ≥0) * ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩)
      (nativeTorusProjection D φ hphase) := (RationalTorus.phaseProjection_lipschitz t).comp hmap
  exact h.weaken (le_of_eq (_root_.one_mul
    (⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩ : ℝ≥0)))

theorem nativeTorusLocalLift_lipschitzOn {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (ht : (t : ℝ) ≤ p) (hcoords : ∀ i j, rationalLogHeight (φ (D.basis j) i) ≤ p) :
    letI := D.metricSpace
    LipschitzOnWith ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩
      (nativeTorusLocalLift D φ hphase)
      {x | ∀ i, ‖nativeTorusProjection D φ hphase x i‖ ≤ 1 / 4} := by
  let := D.metricSpace
  have hmap := nativeTorusProjection_lipschitz D φ hphase hp hD ht hcoords
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have h := centeredTorusLift_lipschitzOn.dist_le_mul
    (nativeTorusProjection D φ hphase x) hx (nativeTorusProjection D φ hphase y) hy
  simp only [NNReal.coe_one, _root_.one_mul] at h
  exact h.trans (hmap.dist_le_mul x y)

end Erdos3

end

section

namespace Erdos3.RationalTorus

open scoped BigOperators TensorProduct NNReal

variable {σ : Type*} [Fintype σ] (d : ℕ)

noncomputable def affineOrbit (b : Fin d → ℝ) (a : σ → Fin d → ℝ) :
    (nilmanifold d).filtration.realification.PolynomialOrbit (fun _ : σ => 1) :=
  (nilmanifold d).filtration.realification.affinePolynomialOrbit
    (((basis d).baseChange ℝ).equivFun.symm b)
    (fun j => ((basis d).baseChange ℝ).equivFun.symm (a j))

theorem affineOrbit_coordinates (b : Fin d → ℝ) (a : σ → Fin d → ℝ) (x : σ → ℤ) :
    ((basis d).baseChange ℝ).equivFun
        ((nilmanifold d).filtration.realification.polynomialOrbitEval (fun _ => 1) x
          (affineOrbit d b a)).coord =
      b + ∑ j, (x j : ℝ) • a j := by
  unfold affineOrbit
  rw [NilpotentLieFiltration.affinePolynomialOrbit_integer_coord, map_add, map_sum]
  simp only [map_smul, LinearEquiv.apply_symm_apply]

theorem affineOrbit_phases (b : Fin d → ℝ) (a : σ → Fin d → ℝ) (x : σ → ℤ) :
    phaseCoordinates d
        ((nilmanifold d).filtration.realification.polynomialOrbitEval (fun _ => 1) x
          (affineOrbit d b a)) =
      fun i => ((b + ∑ j, (x j : ℝ) • a j) i : CircleFourier.Circle) := by
  change (fun i => (((basis d).baseChange ℝ).equivFun
    ((nilmanifold d).filtration.realification.polynomialOrbitEval (fun _ => 1) x
      (affineOrbit d b a)).coord i : CircleFourier.Circle)) = _
  rw [affineOrbit_coordinates]

variable [TopologicalSpace (ℝ ⊗[ℚ] Algebra d)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra d)] [T2Space (ℝ ⊗[ℚ] Algebra d)]
  (b : Fin d → ℝ) (a : σ → Fin d → ℝ)
  (Ψ : (Fin d → CircleFourier.Circle) → ℂ) (M K : ℝ≥0)
  (hΨ : ∀ v, ‖Ψ v‖ ≤ M) (hLip : LipschitzWith K Ψ)

noncomputable def affineNiltest : (nilmanifold d).Niltest (fun _ : σ => 1) where
  orbit := affineOrbit d b a
  observable := Ψ ∘ phaseProjection d
  normBound := M
  lipBound := K
  norm_le x := hΨ (phaseProjection d x)
  lipschitz := by
    let := (nilmanifold d).metricSpace
    simpa only [mul_one] using hLip.comp (phaseProjection_lipschitz d)

theorem affineNiltest_eval (x : σ → ℤ) :
    (affineNiltest d b a Ψ M K hΨ hLip).eval x =
      Ψ (fun i => ((b + ∑ j, (x j : ℝ) • a j) i : CircleFourier.Circle)) := by
  change Ψ (phaseCoordinates d
    ((nilmanifold d).filtration.realification.polynomialOrbitEval (fun _ => 1) x
      (affineOrbit d b a))) = _
  rw [affineOrbit_phases]

theorem affineNiltest_evalCyclic (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (affineNiltest d b a Ψ M K hΨ hLip).evalCyclic N x =
      Ψ (fun i => ((b + ∑ j, ((x j).val : ℝ) • a j) i : CircleFourier.Circle)) := by
  rw [RationalFilteredNilmanifold.Niltest.evalCyclic, affineNiltest_eval]
  simp only [Int.cast_natCast]

theorem affineNiltest_complexity {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hbudget : Real.log (2 + (M : ℝ) + (K : ℝ)) ≤ p) :
    (affineNiltest d b a Ψ M K hΨ hLip).ComplexityLE p :=
  ⟨nilmanifold_geometry d hp hd, hbudget⟩

end Erdos3.RationalTorus

end

section

namespace Erdos3

open RationalFilteredNilmanifold CircleFourier
open scoped TensorProduct NNReal

theorem exists_cyclic_character_niltest {N : ℕ} [NeZero N] (χ : AddChar (ZMod N) ℂ) :
    ∃ T : (RationalTorus.nilmanifold 1).Niltest (fun _ : Unit => 1),
      T.normBound ≤ 1 ∧ T.ComplexityLE 12 ∧
      ∀ x : ZMod N, T.evalCyclic N (fun _ => x) = χ x := by
  obtain ⟨r, hr⟩ := AddChar.zmodAddEquiv.surjective χ
  obtain ⟨theta, htheta⟩ := CyclicBohr.exists_real_frequency_phase r
  have hphase (x : ZMod N) :
      character (((x.val : ℝ) * theta : ℝ) : CircleFourier.Circle) = χ x := by
    rw [htheta]
    exact congrArg (fun ψ : AddChar (ZMod N) ℂ => ψ x) hr
  let Ψ : (Fin 1 → CircleFourier.Circle) → ℂ := fun v => character (v 0)
  have hΨ (v) : ‖Ψ v‖ ≤ (1 : ℝ≥0) := by
    exact le_of_eq (norm_character (v 0))
  have hLip : LipschitzWith characterLipConstant Ψ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (character_lipschitz.dist_le_mul (x 0) (y 0)).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y 0) characterLipConstant.coe_nonneg)
  let T := RationalTorus.affineNiltest 1 0 (fun _ : Unit => fun _ => theta)
    Ψ 1 characterLipConstant hΨ hLip
  have hT : T.ComplexityLE 12 := by
    apply RationalTorus.affineNiltest_complexity 1 0 (fun _ : Unit => fun _ => theta)
      Ψ 1 characterLipConstant hΨ hLip (by norm_num) (by norm_num)
    change Real.log (2 + 1 + 2 * Real.pi) ≤ 12
    have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + 1 + 2 * Real.pi)
    linarith [Real.pi_lt_four]
  refine ⟨T, le_rfl, hT, ?_⟩
  intro x
  simpa [T, Ψ, RationalTorus.affineNiltest_evalCyclic] using hphase x

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct NNReal

theorem torus_reindex_lipschitz {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι → κ) :
    LipschitzWith 1 (fun v : κ → CircleFourier.Circle => fun i => v (e i)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg dist_nonneg).mpr
  intro i
  change ‖v (e i) - w (e i)‖ ≤ dist v w
  rw [← dist_eq_norm]
  exact dist_le_pi_dist v w (e i)

namespace RationalTorus

variable {ι : Type*} [Fintype ι] {d : ℕ} (e : ι ≃ Fin d)
  (Ψ : (ι → CircleFourier.Circle) → ℝ)

noncomputable def reindexedRealObservable : (Fin d → CircleFourier.Circle) → ℂ :=
  fun v => (Ψ (fun i => v (e i)) : ℂ)

omit [Fintype ι] in
theorem reindexedRealObservable_norm (hΨ : ∀ v, 0 ≤ Ψ v ∧ Ψ v ≤ 1)
    (v : Fin d → CircleFourier.Circle) : ‖reindexedRealObservable e Ψ v‖ ≤ (1 : ℝ≥0) := by
  change ‖(Ψ (fun i => v (e i)) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hΨ _).1]
  exact (hΨ _).2

theorem reindexedRealObservable_lipschitz {K : ℝ≥0} (hLip : LipschitzWith K Ψ) :
    LipschitzWith K (reindexedRealObservable e Ψ) := by
  change LipschitzWith K (fun v : Fin d → CircleFourier.Circle => (Ψ (fun i => v (e i)) : ℂ))
  simpa only [one_mul, mul_one, Function.comp_def] using
    Complex.isometry_ofReal.lipschitzWith.comp (hLip.comp (torus_reindex_lipschitz e))

variable [TopologicalSpace (ℝ ⊗[ℚ] Algebra d)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra d)] [T2Space (ℝ ⊗[ℚ] Algebra d)]
  (b a : ι → ℝ) (K : ℝ≥0)
  (hΨ : ∀ v, 0 ≤ Ψ v ∧ Ψ v ≤ 1) (hLip : LipschitzWith K Ψ)

noncomputable def realAffineNiltest : (nilmanifold d).Niltest (fun _ : Unit => 1) :=
  affineNiltest d (fun i => b (e.symm i)) (fun _ : Unit => fun i => a (e.symm i))
    (reindexedRealObservable e Ψ) 1 K (reindexedRealObservable_norm e Ψ hΨ)
    (reindexedRealObservable_lipschitz e Ψ hLip)

theorem realAffineNiltest_unitInterval :
    (realAffineNiltest e Ψ b a K hΨ hLip).UnitIntervalValued := by
  intro z
  change 0 = 0 ∧ 0 ≤ Ψ (fun i => phaseProjection d z (e i)) ∧
    Ψ (fun i => phaseProjection d z (e i)) ≤ 1
  exact ⟨rfl, hΨ _⟩

theorem realAffineNiltest_evalCyclic (N : ℕ) [NeZero N] (x : ZMod N) :
    (realAffineNiltest e Ψ b a K hΨ hLip).evalCyclic N (fun _ => x) =
      (Ψ (fun i => ((b i + (x.val : ℝ) * a i : ℝ) : CircleFourier.Circle)) : ℂ) := by
  unfold realAffineNiltest
  rw [affineNiltest_evalCyclic]
  simp [reindexedRealObservable]

theorem realAffineNiltest_complexity {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hbudget : Real.log (3 + (K : ℝ)) ≤ p) :
    (realAffineNiltest e Ψ b a K hΨ hLip).ComplexityLE p := by
  apply affineNiltest_complexity _ _ _ _ _ _ _ _ hp hd
  simpa only [NNReal.coe_one, show (2 : ℝ) + 1 = 3 by norm_num] using hbudget

end RationalTorus
end Erdos3

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal

variable {N : ℕ} [NeZero N]

noncomputable def approximationLipBound (B : Set N) (rho : ℝ≥0) : ℝ≥0 :=
  ((B.rank : ℝ≥0) * (B.approximationWidth rho)⁻¹) * CircleFourier.characterLipConstant

noncomputable def approximationComplexity (B : Set N) (rho : ℝ≥0) : ℝ :=
  max (B.rank : ℝ) (Real.log (3 + (B.approximationLipBound rho : ℝ)))

theorem approximationComplexity_nonneg (B : Set N) (rho : ℝ≥0) :
    0 ≤ B.approximationComplexity rho :=
  (Nat.cast_nonneg B.rank).trans (le_max_left _ _)

theorem exists_upperApprox_niltest (B : Set N) (hB : 0 < B.radius)
    (rho : ℝ≥0) (hrho : 0 < rho) (z : ZMod N) :
    ∃ T : (RationalTorus.nilmanifold B.rank).Niltest (fun _ : Unit => 1),
      T.UnitIntervalValued ∧ T.ComplexityLE (B.approximationComplexity rho) ∧
      ∀ x : ZMod N, T.evalCyclic N (fun _ => x) = (B.upperApprox rho (x - z) : ℂ) := by
  obtain ⟨theta, htheta⟩ := B.exists_torus_approximation_orbit rho
  have hΨ : ∀ v, 0 ≤ B.torusUpperApprox rho v ∧ B.torusUpperApprox rho v ≤ 1 :=
    fun v => (B.torus_approximation_ranges rho v).1
  have hLip : LipschitzWith (B.approximationLipBound rho) (B.torusUpperApprox rho) :=
    (B.torus_approximations_lipschitz hB rho hrho).1
  let e : B.frequencies ≃ Fin B.rank := B.frequencies.equivFin
  let b : B.frequencies → ℝ := fun r => -(z.val : ℝ) * theta r
  let T := RationalTorus.realAffineNiltest e (B.torusUpperApprox rho) b theta
    (B.approximationLipBound rho) hΨ hLip
  refine ⟨T, ?_, ?_, ?_⟩
  · exact RationalTorus.realAffineNiltest_unitInterval e (B.torusUpperApprox rho) b theta
      (B.approximationLipBound rho) hΨ hLip
  · exact RationalTorus.realAffineNiltest_complexity e (B.torusUpperApprox rho) b theta
      (B.approximationLipBound rho) hΨ hLip (B.approximationComplexity_nonneg rho)
      (le_max_left _ _) (le_max_right _ _)
  · intro x
    dsimp only [T]
    rw [RationalTorus.realAffineNiltest_evalCyclic]
    have hphase : (fun r => ((b r + (x.val : ℝ) * theta r : ℝ) : CircleFourier.Circle)) =
        (fun r => ((((x.val : ℝ) - (z.val : ℝ)) * theta r : ℝ) : CircleFourier.Circle)) := by
      funext r
      congr 1
      dsimp [b]
      ring
    rw [hphase, (htheta x z).1]

theorem exists_lowerApprox_niltest (B : Set N) (hB : 0 < B.radius)
    (rho : ℝ≥0) (hrho : 0 < rho) (z : ZMod N) :
    ∃ T : (RationalTorus.nilmanifold B.rank).Niltest (fun _ : Unit => 1),
      T.UnitIntervalValued ∧ T.ComplexityLE (B.approximationComplexity rho) ∧
      ∀ x : ZMod N, T.evalCyclic N (fun _ => x) = (B.lowerApprox rho (x - z) : ℂ) := by
  obtain ⟨theta, htheta⟩ := B.exists_torus_approximation_orbit rho
  have hΨ : ∀ v, 0 ≤ B.torusLowerApprox rho v ∧ B.torusLowerApprox rho v ≤ 1 :=
    fun v => (B.torus_approximation_ranges rho v).2
  have hLip : LipschitzWith (B.approximationLipBound rho) (B.torusLowerApprox rho) :=
    (B.torus_approximations_lipschitz hB rho hrho).2
  let e : B.frequencies ≃ Fin B.rank := B.frequencies.equivFin
  let b : B.frequencies → ℝ := fun r => -(z.val : ℝ) * theta r
  let T := RationalTorus.realAffineNiltest e (B.torusLowerApprox rho) b theta
    (B.approximationLipBound rho) hΨ hLip
  refine ⟨T, ?_, ?_, ?_⟩
  · exact RationalTorus.realAffineNiltest_unitInterval e (B.torusLowerApprox rho) b theta
      (B.approximationLipBound rho) hΨ hLip
  · exact RationalTorus.realAffineNiltest_complexity e (B.torusLowerApprox rho) b theta
      (B.approximationLipBound rho) hΨ hLip (B.approximationComplexity_nonneg rho)
      (le_max_left _ _) (le_max_right _ _)
  · intro x
    dsimp only [T]
    rw [RationalTorus.realAffineNiltest_evalCyclic]
    have hphase : (fun r => ((b r + (x.val : ℝ) * theta r : ℝ) : CircleFourier.Circle)) =
        (fun r => ((((x.val : ℝ) - (z.val : ℝ)) * theta r : ℝ) : CircleFourier.Circle)) := by
      funext r
      congr 1
      dsimp [b]
      ring
    rw [hphase, (htheta x z).2]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem upperApprox_comparison_of_niltests
    (B : Set N) (hB : 0 < B.radius) (rho : ℝ≥0) (hrho : 0 < rho)
    (f g : ZMod N → ℝ) {P epsilon : ℝ}
    (hbudget : B.approximationComplexity rho ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P epsilon f g) (z : ZMod N) :
    (𝔼 x, B.upperApprox rho (x - z) * (f x - g x)) ≤ epsilon := by
  obtain ⟨T, hunit, hT, hEval⟩ := B.exists_upperApprox_niltest hB rho hrho z
  have h := hcompare (RationalTorus.nilmanifold B.rank) le_rfl T hunit (hT.mono hbudget)
  simpa only [hEval, Complex.ofReal_re, mul_comm] using h

theorem average_sub_le_of_niltest_comparison
    (B : Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular) (rho : ℝ≥0) (hrho : 0 < rho)
    (hsmall : rho ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (f g : ZMod N → ℝ) {W P epsilon : ℝ} (hW : 0 ≤ W)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ W)
    (hbudget : B.approximationComplexity rho ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P epsilon f g) (z : ZMod N) :
    (𝔼 x ∈ B.carrier, (f (z + x) - g (z + x))) ≤
      (N : ℝ) / B.carrier.card * epsilon + W * (400 * (max B.rank 1 : ℕ) * (rho : ℝ)) :=
  B.average_sub_le_of_upperApprox hBpos hB rho hrho hsmall f g hW hf hg z
    (B.upperApprox_comparison_of_niltests hBpos rho hrho f g hbudget hcompare z)

theorem sum_average_sub_le_of_niltest_comparison
    (B : Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular) (rho : ℝ≥0) (hrho : 0 < rho)
    (hsmall : rho ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (f g : ZMod N → ℝ) {W P epsilon : ℝ} (hW : 0 ≤ W)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ W)
    (hbudget : B.approximationComplexity rho ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P epsilon f g) (z : ZMod N) :
    (𝔼 s ∈ B.carrier, 𝔼 t ∈ B.carrier, (f (z + s + t) - g (z + s + t))) ≤
      (N : ℝ) / B.carrier.card * epsilon + W * (400 * (max B.rank 1 : ℕ) * (rho : ℝ)) :=
  B.sum_average_sub_le_of_upperApprox hBpos hB rho hrho hsmall f g hW hf hg
    (B.upperApprox_comparison_of_niltests hBpos rho hrho f g hbudget hcompare) z

theorem small_sum_average_of_niltest_comparison
    (B : Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular)
    (f g : ZMod N → ℝ) {W eta P epsilon : ℝ} (hW : 0 ≤ W) (heta : 0 < eta)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ W)
    (hepsilon : epsilon ≤ (eta / 2) * ((B.carrier.card : ℝ) / N))
    (hbudget : B.approximationComplexity (localizedAverageScale B.rank W (eta / 2)) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P epsilon f g) (z : ZMod N) :
    (𝔼 s ∈ B.carrier, 𝔼 t ∈ B.carrier, (f (z + s + t) - g (z + s + t))) ≤ eta := by
  apply B.small_sum_average_of_upperApprox hBpos hB f g hW heta hf hg hepsilon
  intro y
  exact B.upperApprox_comparison_of_niltests hBpos _
    (localizedAverageScale_spec B.rank hW (by positivity)).1 f g hbudget hcompare y

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem coe_approximationLipBound (B : Set N) (rho : ℝ≥0) :
    (B.approximationLipBound rho : ℝ) =
      (B.rank : ℝ) / ((rho : ℝ) * B.radius) * (2 * Real.pi) := by
  have hwidth : (B.approximationWidth rho : ℝ) = (rho : ℝ) * B.radius := rfl
  unfold approximationLipBound
  rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_inv,
    hwidth, CircleFourier.coe_characterLipConstant, div_eq_mul_inv]

theorem approximationComplexity_exp_le (B : Set N) (rho : ℝ≥0) {Q R : ℝ}
    (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (hrho : Real.exp (-Q) ≤ (rho : ℝ)) (hwidth : Real.exp (-R) ≤ B.radius) :
    B.approximationComplexity rho ≤ (B.rank : ℝ) + Q + R + 12 := by
  have hrhopos : 0 < (rho : ℝ) := (Real.exp_pos _).trans_le hrho
  have hwpos : 0 < B.radius := (Real.exp_pos _).trans_le hwidth
  have hprod : Real.exp (-(Q + R)) ≤ (rho : ℝ) * B.radius := by
    calc
      _ = Real.exp (-Q) * Real.exp (-R) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul hrho hwidth (Real.exp_nonneg _) hrhopos.le
  have hinv : ((rho : ℝ) * B.radius)⁻¹ ≤ Real.exp (Q + R) := by
    have h := one_div_le_one_div_of_le (Real.exp_pos _) hprod
    simpa only [one_div, Real.exp_neg, inv_inv] using h
  have hrank : (B.rank : ℝ) ≤ Real.exp (B.rank : ℝ) := by
    linarith [Real.add_one_le_exp (B.rank : ℝ)]
  have hpi : 2 * Real.pi ≤ (8 : ℝ) := by linarith [Real.pi_lt_four]
  have hK : (B.approximationLipBound rho : ℝ) ≤
      8 * Real.exp ((B.rank : ℝ) + Q + R) := by
    rw [coe_approximationLipBound, div_eq_mul_inv]
    calc
      _ ≤ Real.exp (B.rank : ℝ) * Real.exp (Q + R) * 8 := by gcongr
      _ = _ := by rw [← Real.exp_add, ← add_assoc, mul_comm]
  have hone : 1 ≤ Real.exp ((B.rank : ℝ) + Q + R) :=
    Real.one_le_exp (by positivity)
  change max (B.rank : ℝ) (Real.log (3 + (B.approximationLipBound rho : ℝ))) ≤ _
  apply max_le
  · linarith
  · apply (Real.log_le_iff_le_exp (by positivity)).mpr
    calc
      _ ≤ 11 * Real.exp ((B.rank : ℝ) + Q + R) := by linarith
      _ ≤ Real.exp 12 * Real.exp ((B.rank : ℝ) + Q + R) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        linarith [Real.add_one_le_exp 12]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem card_ratio_ge_exp_width (B : Set N) (hB1 : B.radius ≤ 1) {R : ℝ}
    (hwidth : Real.exp (-R) ≤ B.radius) :
    Real.exp (-((B.rank : ℝ) * (R + 10))) ≤ (B.carrier.card : ℝ) / N := by
  have hB : 0 < B.radius := (Real.exp_pos _).trans_le hwidth
  have hbase : Real.exp (-(R + 10)) ≤ B.radius / 10 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10)).mpr
    calc
      _ ≤ Real.exp (-(R + 10)) * Real.exp 10 := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        linarith [Real.add_one_le_exp 10]
      _ = Real.exp (-R) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hwidth
  have hpower : Real.exp (-((B.rank : ℝ) * (R + 10))) ≤ (B.radius / 10) ^ B.rank := by
    calc
      _ = Real.exp (-(R + 10)) ^ B.rank := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) hbase _
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  apply (le_div_iff₀ hN).mpr
  exact (mul_le_mul_of_nonneg_right hpower hN.le).trans (card_lower_bound B hB hB1)

theorem small_sum_average_of_exponential_niltest_comparison
    (B : Set N) (hB : B.IsRankRegular) (hB1 : B.radius ≤ 1)
    (f g : ZMod N → ℝ) {W A E R P : ℝ}
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hE : 0 ≤ E) (hR : 0 ≤ R)
    (hWcap : W ≤ Real.exp A) (hwidth : Real.exp (-R) ≤ B.radius)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ W)
    (hcomplexity : 2 * (B.rank : ℝ) + A + E + R + 1612 ≤ P)
    (hprecision : E + 2 + (B.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) f g) (z : ZMod N) :
    (𝔼 s ∈ B.carrier, 𝔼 t ∈ B.carrier, (f (z + s + t) - g (z + s + t))) ≤ Real.exp (-E) := by
  have hBpos : 0 < B.radius := (Real.exp_pos _).trans_le hwidth
  have hbudget : B.approximationComplexity
      (localizedAverageScale B.rank W (Real.exp (-E) / 2)) ≤ P := by
    have h := B.approximationComplexity_exp_le _
      (show 0 ≤ (B.rank : ℝ) + A + E + 1600 by positivity) hR
      (localizedAverageScale_exp_lower B.rank hW hWcap hA hE) hwidth
    exact h.trans (by linarith)
  have hhalf : Real.exp (-(E + 2)) ≤ Real.exp (-E) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ Real.exp (-(E + 2)) * Real.exp 2 := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        linarith [Real.add_one_le_exp 2]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have herror : Real.exp (-P) ≤ (Real.exp (-E) / 2) * ((B.carrier.card : ℝ) / N) := by
    calc
      _ ≤ Real.exp (-(E + 2 + (B.rank : ℝ) * (R + 10))) :=
        Real.exp_le_exp.mpr (neg_le_neg hprecision)
      _ = Real.exp (-(E + 2)) * Real.exp (-((B.rank : ℝ) * (R + 10))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul hhalf (B.card_ratio_ge_exp_width hB1 hwidth)
        (Real.exp_nonneg _) (by positivity)
  exact B.small_sum_average_of_niltest_comparison hBpos hB f g hW (Real.exp_pos _)
    hf hg herror hbudget hcompare z

end Erdos3.CyclicBohr.Set

end

end OAI
