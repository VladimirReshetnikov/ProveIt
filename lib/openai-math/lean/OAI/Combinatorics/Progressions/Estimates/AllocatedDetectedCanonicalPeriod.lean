/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.ContainedSupportedProgressionReference
import OAI.Combinatorics.Progressions.Linear.AllocatedSlicedDenseKernelSource
import OAI.Combinatorics.Progressions.Linear.ScalarKernelDenseSliceStride
import OAI.Combinatorics.Progressions.Nilpotent.AllocatedNiltestSupportedSlicedDetection

namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {α G X : Type*} [Fintype α] [DecidableEq α] [Fintype G] [Fintype X]
variable {L M : ℕ} (selection : α ↪ G) (stride : X → ℕ) (height : ℕ)

noncomputable def canonicalSlicedModulus (x : G → IntegerScalarCubeBox α L) : ℕ :=
  if hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x then
    residueRefinedPeriod (kernelPeriodCandidate (height + 1)
      (goodKernelUniformCandidate selection x hx height)) stride
  else 1

theorem canonicalSlicedModulus_good (x : G → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x) :
    canonicalSlicedModulus (M := M) selection stride height x =
      residueRefinedPeriod (kernelPeriodCandidate (height + 1)
        (goodKernelUniformCandidate selection x hx height)) stride := by
  simp only [canonicalSlicedModulus, dite_eq_left hx]

theorem canonicalSlicedModulus_pos (hs : ∀ i, 0 < stride i)
    (x : G → IntegerScalarCubeBox α L) :
    0 < canonicalSlicedModulus (M := M) selection stride height x := by
  unfold canonicalSlicedModulus
  split_ifs with hx
  · exact residueRefinedPeriod_pos (kernelPeriodCandidate_pos _ _) stride hs
  · norm_num

theorem canonicalSlicedModulus_le_exp {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hM : (M : ℝ) ≤ Real.exp P) (hs : ∀ i, (stride i : ℝ) ≤ Real.exp Q)
    (x : G → IntegerScalarCubeBox α L) :
    (canonicalSlicedModulus (M := M) selection stride height x : ℝ) ≤
      Real.exp ((height + 1 : ℕ) * P + Fintype.card X * Q) := by
  unfold canonicalSlicedModulus
  split_ifs with hx
  · exact residueRefinedPeriod_exp_bound _ stride
      (kernelPeriodCandidate_le_exp hM (height + 1) _) hs
  · exact_mod_cast Real.one_le_exp (add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) hP) (mul_nonneg (Nat.cast_nonneg _) hQ))

theorem canonicalSlicedModulus_candidate_dvd
    (x : G → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    (candidate : Fin M) (hc : candidate = goodKernelUniformCandidate selection x hx height) :
    kernelPeriodCandidate (height + 1) candidate ∣
      canonicalSlicedModulus (M := M) selection stride height x := by
  subst candidate
  rw [canonicalSlicedModulus_good selection stride height x hx]
  exact ⟨∏ i, stride i, rfl⟩

theorem canonicalSlicedModulus_stride_period_dvd
    (x : G → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    (candidate : Fin M) (hc : candidate = goodKernelUniformCandidate selection x hx height) (i : X) :
    stride i * kernelPeriodCandidate (height + 1) candidate ∣
      canonicalSlicedModulus (M := M) selection stride height x := by
  subst candidate
  rw [canonicalSlicedModulus_good selection stride height x hx]
  exact stride_mul_dvd_residueRefinedPeriod _ stride i

end Erdos3

end

section

namespace Erdos3

variable {α G X : Type*} [Fintype α] [DecidableEq α] [Fintype G] [Fintype X]
variable {L M : ℕ} (selection : α ↪ G) (stride : X → ℕ) (height : ℕ)

theorem canonicalSlicedModulus_jet_period
    (x : G → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    {O : Type*} [Fintype O] (degree : ℕ) (hdegree : degree ≤ height + 1)
    (rows : O → Finset α) (hinj : Function.Injective rows) (hrows : ∀ o, (rows o).card ≤ degree) :
    integerScalarLattice O (canonicalSlicedModulus (M := M) selection stride height x : ℤ) ≤
      (scalarKernelIntegerJet x degree rows).mulVecLin.range := by
  have hd := canonicalSlicedModulus_candidate_dvd selection stride height x hx
    (goodKernelUniformCandidate selection x hx height) rfl
  exact (integerScalarLattice_le_of_nat_dvd hd).trans
    ((goodKernelUniformCandidate_spec selection x hx height).2 O degree hdegree rows hinj hrows)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)
local notation "kernelLaw" => FiniteProbabilityWeights.pi
  (fun _ : G => integerScalarCubeWeights (Fin (s + 2)) S.value S.positive)

local notation "Path" => bases × rectangularWeightIndices 0 widths 1
local notation "pathLaw" => allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
  N hN hW hτ hξ stride cells hmass bases hbases htotal

theorem allocatedOriginalPathLaw_niltest_good_sliced_source
    (P : Polynomial ℕ)
    {T : Type} [Fintype T] [Nonempty T]
    (e : T → LayerSamplerVariables G I n B → ℤ) (he : Function.Injective e)
    {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
    {L : ∀ z, Tests z → Type} [∀ z j, LieRing (L z j)] [∀ z j, LieAlgebra ℚ (L z j)]
    {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] L z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] L z j)]
    (D : ∀ z j, RationalFilteredNilmanifold (L z j) s (dims z j))
    (V : ∀ z j, (D z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset T)
    (c : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (step : ∀ z, Tests z → ℕ)
    (H : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ z j, 0 < step z j)
    (hslices : ∀ z j, (slices z j).image e = commonStrideBox (c z j) (step z j) (H z j))
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hdense : ∀ z j, IsDenseCommonStrideBox sides p ((slices z j).image e))
    (hdimension : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q)
    (hcomplexity : ∀ z j, (V z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) q))
    (hcap : ∀ z j, ((V z j).normBound : ℝ) ≤ 1)
    (f : (X → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hmesh : Fintype.card (LayerSamplerVariables G I n B) * Real.exp (-p) ≤ α / 8)
    (hthreshold : Real.exp (-q) ≤ α / 4)
    (hdetected : α ≤ sampledSliceSeminorm (pathLaw)
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((V z j).eval (commonStrideIndex (c z j) (step z j) (e t)))) f)
    (selection : Fin (s + 1) ↪ G) (hG : (s + 1) * (s + 3) ≤ Fintype.card G)
    (hkernel : scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊
      (((Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
        Real.exp (-((q + sampledSupportedSlicedDetectionConstant s P) ^ sampledSupportedSlicedDetectionConstant s P)) ^
          (2 ^ (s + 1))) / 2) ≤ S.value)
    (modulus : (G → IntegerScalarCubeBox (Fin (s + 1)) S.value) → ℕ) [∀ x, NeZero (modulus x)] :
    let gain := (Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
      Real.exp (-((q + sampledSupportedSlicedDetectionConstant s P) ^ sampledSupportedSlicedDetectionConstant s P)) ^
        (2 ^ (s + 1))
    let Mk := scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊ (gain / 2)
    ∃ (c₀ : LayerSamplerVariables G I n B → ℤ) (step₀ : ℕ)
      (H₀ : LayerSamplerVariables G I n B → ℕ) (_hstep₀ : 0 < step₀) (hH₀ : ∀ k, 0 < H₀ k),
      (∀ i, integerProgressionSupport (c₀ i) (step₀ : ℤ) (H₀ i) ⊆ Finset.Ico (0 : ℤ) (sides i : ℤ)) ∧
      (∀ i, Real.exp (-(p + 1)) * sides i ≤ (H₀ i : ℝ)) ∧
    ∃ (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value),
      GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x ∧
    ∃ (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (modulus x))
      (hr : 0 < (principalTupleWeights (α := Fin (s + 1)) B (layerSamplerDegree I n)
        (fun j => H₀ (Sum.inr j)) (fun j => hH₀ (Sum.inr j))).mass
          (Finset.univ.filter (fun y => principalResidueLabel (modulus x) y = r))),
      ∃ hsubset : ∀ j, integerProgressionSupport (c₀ (Sum.inr j)) (step₀ : ℤ) (H₀ (Sum.inr j)) ⊆
        Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ),
      gain / 2 ≤ ((containedSupportedProgressionLaw B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (fun j => H₀ (Sum.inr j)) (fun _ => step₀)
        (fun j => c₀ (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
        (fun j => hH₀ (Sum.inr j)) hsubset (modulus x) r hr).complexMean
        (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
          N hN hW hτ hξ stride cells hmass bases x y f)).re := by
  intro gain Mk
  obtain ⟨c₀, step₀, H₀, hstep₀, hH₀, hsubset₀, hcounts₀, _, _, hpositive⟩ :=
    allocatedOriginalPathLaw_niltest_sliced_detection_with_sides B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases hbases htotal P e he D V slices c step H hstep hslices
      p q hp hq hdense hdimension hcomplexity hcap f hf α hα hαone hmesh hthreshold hdetected
  have hgain : 0 < gain := mul_pos (mul_pos (Real.exp_pos _) (half_pos hα)) (pow_pos (Real.exp_pos _) _)
  obtain ⟨x, _, hx, r, hr, hsource⟩ := allocatedSlicedCubeSource_good_kernel_dense_residue
    B U b hb o hR hσ S X poly hmem N hN hW hτ hξ stride cells hmass bases hbases htotal
    H₀ hH₀ c₀ step₀ hsubset₀ selection (by simpa only [Nat.add_assoc] using hG) hgain hkernel hstep₀
    (fun g => hcounts₀ (Sum.inl g)) f hf hpositive modulus
  exact ⟨c₀, step₀, H₀, hstep₀, hH₀, hsubset₀, hcounts₀, x, hx, r, hr,
    (fun j => hsubset₀ (Sum.inr j)), hsource⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)
local notation "kernelLaw" => FiniteProbabilityWeights.pi
  (fun _ : G => integerScalarCubeWeights (Fin (s + 2)) S.value S.positive)

local notation "Path" => bases × rectangularWeightIndices 0 widths 1
local notation "pathLaw" => allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
  N hN hW hτ hξ stride cells hmass bases hbases htotal

theorem allocatedOriginalPathLaw_canonical_sliced_source
    (P : Polynomial ℕ)
    {T : Type} [Fintype T] [Nonempty T]
    (e : T → LayerSamplerVariables G I n B → ℤ) (he : Function.Injective e)
    {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
    {L : ∀ z, Tests z → Type} [∀ z j, LieRing (L z j)] [∀ z j, LieAlgebra ℚ (L z j)]
    {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] L z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] L z j)]
    (D : ∀ z j, RationalFilteredNilmanifold (L z j) s (dims z j))
    (V : ∀ z j, (D z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset T)
    (c : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (step : ∀ z, Tests z → ℕ)
    (H : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ z j, 0 < step z j)
    (hslices : ∀ z j, (slices z j).image e = commonStrideBox (c z j) (step z j) (H z j))
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hdense : ∀ z j, IsDenseCommonStrideBox sides p ((slices z j).image e))
    (hdimension : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q)
    (hcomplexity : ∀ z j, (V z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) q))
    (hcap : ∀ z j, ((V z j).normBound : ℝ) ≤ 1)
    (f : (X → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hmesh : Fintype.card (LayerSamplerVariables G I n B) * Real.exp (-p) ≤ α / 8)
    (hthreshold : Real.exp (-q) ≤ α / 4)
    (hdetected : α ≤ sampledSliceSeminorm (pathLaw)
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((V z j).eval (commonStrideIndex (c z j) (step z j) (e t)))) f)
    (selection : Fin (s + 1) ↪ G) (hG : (s + 1) * (s + 3) ≤ Fintype.card G)
    (hkernel : scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊
      (((Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
        Real.exp (-((q + sampledSupportedSlicedDetectionConstant s P) ^ sampledSupportedSlicedDetectionConstant s P)) ^
          (2 ^ (s + 1))) / 2) ≤ S.value)
    (hstride : ∀ i, 0 < stride i) :
    let gain := (Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
      Real.exp (-((q + sampledSupportedSlicedDetectionConstant s P) ^ sampledSupportedSlicedDetectionConstant s P)) ^
        (2 ^ (s + 1))
    let Mk := scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊ (gain / 2)
    let modulus := canonicalSlicedModulus (M := Mk) selection stride m
    ∃ (c₀ : LayerSamplerVariables G I n B → ℤ) (step₀ : ℕ)
      (H₀ : LayerSamplerVariables G I n B → ℕ) (_hstep₀ : 0 < step₀) (hH₀ : ∀ k, 0 < H₀ k),
      (∀ i, integerProgressionSupport (c₀ i) (step₀ : ℤ) (H₀ i) ⊆ Finset.Ico (0 : ℤ) (sides i : ℤ)) ∧
      (∀ i, Real.exp (-(p + 1)) * sides i ≤ (H₀ i : ℝ)) ∧
      (step₀ : ℝ) ≤ 4 * Real.exp (p + 1) ∧
    ∃ (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value),
      GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x ∧
    ∃ (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (modulus x))
      (hr : 0 < (principalTupleWeights (α := Fin (s + 1)) B (layerSamplerDegree I n)
        (fun j => H₀ (Sum.inr j)) (fun j => hH₀ (Sum.inr j))).mass
          (Finset.univ.filter (fun y => principalResidueLabel (modulus x) y = r))),
      ∃ hsubset : ∀ j, integerProgressionSupport (c₀ (Sum.inr j)) (step₀ : ℤ) (H₀ (Sum.inr j)) ⊆
        Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ),
      let law := containedSupportedProgressionLaw B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (fun j => H₀ (Sum.inr j)) (fun _ => step₀)
        (fun j => c₀ (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
        (fun j => hH₀ (Sum.inr j)) hsubset (modulus x) r hr
      gain / 2 ≤ (law.complexMean (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
        N hN hW hτ hξ stride cells hmass bases x y f)).re ∧
      ∃ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S),
        0 < law.weight y₀ ∧
        (∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ))) ∧
        (∀ axis : LayerSamplerAxis I n → Prop,
          0 < (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
            (allocatedPrincipalSides B U b S) (fun j => H₀ (Sum.inr j)) (fun _ => step₀)
            (fun j => c₀ (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
            (fun j => hH₀ (Sum.inr j)) hsubset (modulus x) r hr axis).weight (principalAxisRestrict axis y₀)) ∧
        (∀ y, law.weight y ≠ 0 → principalResidueLabel (modulus x) y = principalResidueLabel (modulus x) y₀) := by
  intro gain Mk modulus
  let : ∀ x, NeZero (modulus x) := fun x =>
    ⟨(canonicalSlicedModulus_pos selection stride m hstride x).ne'⟩
  obtain ⟨c₀, step₀, H₀, hstep₀, hH₀, hsubset₀, hdense₀, x, hx, r, hr, hsubset, hsource⟩ :=
    allocatedOriginalPathLaw_niltest_good_sliced_source B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal P e he D V slices c step H hstep hslices
    p q hp hq hdense hdimension hcomplexity hcap f hf α hα hαone hmesh hthreshold hdetected
    selection hG hkernel modulus
  have hgain : 0 < gain := by
    dsimp only [gain]
    exact mul_pos (mul_pos (Real.exp_pos _) (half_pos hα)) (pow_pos (Real.exp_pos _) _)
  let g₀ : G := selection ⟨0, by omega⟩
  have hstrideBound := (scalarKernelCutoff_dense_slice_stride s G (half_pos hgain)
    (c₀ (Sum.inl g₀)) hkernel hstep₀ (hsubset₀ (Sum.inl g₀)) (hdense₀ (Sum.inl g₀))).2
  refine ⟨c₀, step₀, H₀, hstep₀, hH₀, hsubset₀, hdense₀, hstrideBound, x, hx, r, hr, hsubset, hsource, ?_⟩
  exact exists_containedSupportedProgressionReference B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (fun j => H₀ (Sum.inr j)) (fun _ => step₀)
    (fun j => c₀ (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
    (fun j => hH₀ (Sum.inr j)) hsubset (modulus x) r hr

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)
local notation "kernelLaw" => FiniteProbabilityWeights.pi
  (fun _ : G => integerScalarCubeWeights (Fin (s + 2)) S.value S.positive)

local notation "Path" => bases × rectangularWeightIndices 0 widths 1
local notation "pathLaw" => allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
  N hN hW hτ hξ stride cells hmass bases hbases htotal

theorem allocatedOriginalPathLaw_canonical_period_source
    (P : Polynomial ℕ)
    {T : Type} [Fintype T] [Nonempty T]
    (e : T → LayerSamplerVariables G I n B → ℤ) (he : Function.Injective e)
    {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
    {L : ∀ z, Tests z → Type} [∀ z j, LieRing (L z j)] [∀ z j, LieAlgebra ℚ (L z j)]
    {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] L z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] L z j)]
    (D : ∀ z j, RationalFilteredNilmanifold (L z j) s (dims z j))
    (V : ∀ z j, (D z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset T)
    (c : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (step : ∀ z, Tests z → ℕ)
    (H : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ z j, 0 < step z j)
    (hslices : ∀ z j, (slices z j).image e = commonStrideBox (c z j) (step z j) (H z j))
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hdense : ∀ z j, IsDenseCommonStrideBox sides p ((slices z j).image e))
    (hdimension : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q)
    (hcomplexity : ∀ z j, (V z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) q))
    (hcap : ∀ z j, ((V z j).normBound : ℝ) ≤ 1)
    (f : (X → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hmesh : Fintype.card (LayerSamplerVariables G I n B) * Real.exp (-p) ≤ α / 8)
    (hthreshold : Real.exp (-q) ≤ α / 4)
    (hdetected : α ≤ sampledSliceSeminorm (pathLaw)
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((V z j).eval (commonStrideIndex (c z j) (step z j) (e t)))) f)
    (selection : Fin (s + 1) ↪ G) (hG : (s + 1) * (s + 3) ≤ Fintype.card G)
    (hkernel : scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊
      (((Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
        Real.exp (-((q + sampledSupportedSlicedDetectionConstant s P) ^ sampledSupportedSlicedDetectionConstant s P)) ^
          (2 ^ (s + 1))) / 2) ≤ S.value)
    (hstride : ∀ i, 0 < stride i) :
    let gain := (Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
      Real.exp (-((q + sampledSupportedSlicedDetectionConstant s P) ^ sampledSupportedSlicedDetectionConstant s P)) ^
        (2 ^ (s + 1))
    let Mk := scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊ (gain / 2)
    ∃ (c₀ : LayerSamplerVariables G I n B → ℤ) (step₀ : ℕ)
      (H₀ : LayerSamplerVariables G I n B → ℕ) (_hstep₀ : 0 < step₀) (hH₀ : ∀ k, 0 < H₀ k),
      (∀ i, integerProgressionSupport (c₀ i) (step₀ : ℤ) (H₀ i) ⊆ Finset.Ico (0 : ℤ) (sides i : ℤ)) ∧
      (∀ i, Real.exp (-(p + 1)) * sides i ≤ (H₀ i : ℝ)) ∧
      (step₀ : ℝ) ≤ 4 * Real.exp (p + 1) ∧
    ∃ (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value),
      ∃ hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x,
      let period := kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m)
      0 < Mk ∧ 0 < period ∧ period ≤ Mk ^ (m + 1) ∧
    ∃ (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod period stride))
      (hr : 0 < (principalTupleWeights (α := Fin (s + 1)) B (layerSamplerDegree I n)
        (fun j => H₀ (Sum.inr j)) (fun j => hH₀ (Sum.inr j))).mass
          (Finset.univ.filter (fun y => principalResidueLabel (residueRefinedPeriod period stride) y = r))),
      ∃ hsubset : ∀ j, integerProgressionSupport (c₀ (Sum.inr j)) (step₀ : ℤ) (H₀ (Sum.inr j)) ⊆
        Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ),
      let law := containedSupportedProgressionLaw B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (fun j => H₀ (Sum.inr j)) (fun _ => step₀)
        (fun j => c₀ (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
        (fun j => hH₀ (Sum.inr j)) hsubset (residueRefinedPeriod period stride) r hr
      gain / 2 ≤ (law.complexMean (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
        N hN hW hτ hξ stride cells hmass bases x y f)).re ∧
      ∃ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S),
        0 < law.weight y₀ ∧
        (∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ))) ∧
        (∀ axis : LayerSamplerAxis I n → Prop,
          0 < (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
            (allocatedPrincipalSides B U b S) (fun j => H₀ (Sum.inr j)) (fun _ => step₀)
            (fun j => c₀ (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
            (fun j => hH₀ (Sum.inr j)) hsubset (residueRefinedPeriod period stride) r hr axis).weight (principalAxisRestrict axis y₀)) ∧
        (∀ y, law.weight y ≠ 0 → principalResidueLabel (residueRefinedPeriod period stride) y = principalResidueLabel (residueRefinedPeriod period stride) y₀) := by
  intro gain Mk
  obtain ⟨c₀, step₀, H₀, hstep₀, hH₀, hsubset₀, hdense₀, hstrideBound, x, hx, htail⟩ :=
    allocatedOriginalPathLaw_canonical_sliced_source B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases hbases htotal P e he D V slices c step H hstep hslices
      p q hp hq hdense hdimension hcomplexity hcap f hf α hα hαone hmesh hthreshold hdetected
      selection hG hkernel hstride
  have hMk : 0 < Mk := Nat.zero_lt_of_lt (goodKernelUniformCandidate selection x hx m).isLt
  refine ⟨c₀, step₀, H₀, hstep₀, hH₀, hsubset₀, hdense₀, hstrideBound, x, hx,
    hMk, kernelPeriodCandidate_pos _ _, kernelPeriodCandidate_le _ _, ?_⟩
  erw [canonicalSlicedModulus_good selection stride m x hx] at htail
  exact htail

end Erdos3.VectorPolynomial

end

end OAI
