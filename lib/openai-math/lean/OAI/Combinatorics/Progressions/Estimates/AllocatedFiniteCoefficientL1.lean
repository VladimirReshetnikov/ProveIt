import OAI.Combinatorics.Progressions.Probability.AllocatedLongIntegralMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedLongJet_residue_coefficient_comparison {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P e ε : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (hε : 0 < ε)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
    (modulus : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
    (u : PrincipalAxisTuples (α := α) grid sides)
    (p : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hr : ∀ v, p.weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j)
    (z : AllocatedLongJetRows B U basis S O) :
    let C := Real.exp (allocatedDensityLog (G := G) B α O P)
    let CM : ℝ := layerKernelIndexBound m M
    let normalized := fun v => principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v
    |p.mean (fun v => (∏ a, allocatedLongJetOutputScale B U basis S (O := O) a) *
        allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) -
      (∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
        p.mean (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
          (normalized v) (allocatedLongJetRealCoordinates B U basis S z))| ≤
      Fintype.card {a // ¬grid a} * ε * (1 + CM * C + ε)^Fintype.card {a // ¬grid a} := by
  intro C CM normalized
  have hreplace := allocatedFixedKernel_replacement B U basis hR hσ S x rows hM selection hx hq
    hinj hrows hσ1 hP he hε hMP hRP hRi hσi hcount hεe hlarge modulus hperiod s hA hi u p residue hr
  have hcap := (allocatedLongJetTarget_exp_bounds B U basis hR hσ S x rows s hA
    hM hi hP hMP hRP hRi hσi hcount u hσ1).2.1
  have hCM : 1 ≤ CM := by
    change (1 : ℝ) ≤ (layerKernelIndexBound m M : ℝ)
    exact_mod_cast Nat.succ_le_of_lt (show 0 < layerKernelIndexBound m M from pow_pos hM _)
  have hm (a : {a // ¬grid a}) :
      0 ≤ allocatedLongJetMask B U basis S x rows modulus residue a (z a) ∧
        allocatedLongJetMask B U basis S x rows modulus residue a (z a) ≤ CM := by
    rcases a with ⟨⟨j,a⟩, ha⟩
    cases a with
    | inl i => exact ⟨zero_le_one, hCM⟩
    | inr i => exact (hreplace j i (Nat.lt_of_not_ge ha)).1 _
  have herr (v) (hv : p.weight v ≠ 0) (a : {a // ¬grid a}) :
      |allocatedLongJetOutputScale B U basis S (O := O) a *
          allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a (z a) -
        allocatedLongJetMask B U basis S x rows modulus residue a (z a) *
          allocatedLongJetTarget B U basis S x u rows s hA (normalized v) a (z a)| ≤ ε := by
    rcases a with ⟨⟨j,a⟩, ha⟩
    cases a with
    | inl i => simpa only [allocatedLongJetOutputScale, allocatedLongJetFactor,
        allocatedLongJetMask, allocatedLongJetTarget, normalized, sub_self, abs_zero] using hε.le
    | inr i => exact (hreplace j i (Nat.lt_of_not_ge ha)).2 v hv _
  have hid (v) : allocatedNormalizedLongJetDensity B U basis S x u rows s hA
      (normalized v) (allocatedLongJetRealCoordinates B U basis S z) =
      ∏ a, allocatedLongJetTarget B U basis S x u rows s hA (normalized v) a (z a) := by
    exact Finset.prod_congr rfl (fun a _ =>
      (allocatedLongJetTarget_normalized B U basis S x u rows s hA (normalized v) z a).symm)
  simp_rw [hid]
  rw [← p.mean_const_mul, ← p.mean_sub]
  apply p.abs_mean_le_on_support
  intro v hv
  rw [allocatedLongJet_scaled_density]
  exact masked_product_error _ _ _ (Real.exp_nonneg _) (zero_le_one.trans hCM) hε.le
    (fun a => hcap _ a (z a))
    (fun a => by rw [abs_of_nonneg (hm a).1]; exact (hm a).2) (herr v hv)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m,
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
variable (hσ1 : ∀ j, σ j ≤ 1)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "T" => Real.exp (allocatedJetSupportLog (G := G) B α O P)
local notation "Q" => ∏ a, allocatedLongJetOutputScale B U basis S (O := O) a
local notation "V" => (2*T+1)^Fintype.card (Σ a : LayerSamplerAxis I n, O (Sigma.fst a))
local notation "reference" => allocatedLongJetReference B U basis S O

variable (w : FiniteProbabilityWeights (PrincipalAxisTuples (α := α)
  (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) (allocatedPrincipalSides B U basis S)))
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "density" => (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1)
local notation "normalized" => principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides)
local notation "target" => (fun (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
  (z : AllocatedLongJetRows B U basis S O) =>
  ∏ a, allocatedLongJetTarget B U basis S x u rows s hA (normalized v) a (z a))
local notation "proxy" => (fun (z : AllocatedLongJetRows B U basis S O) =>
  (∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) * w.mean (fun v => target v z))

omit [DecidableEq G] [∀ layer, DecidableEq (I layer)] [∀ axis, DecidableEq (B axis)] in
include hR hσ hσ1 in
theorem allocatedPrincipalLongJetTarget_measurable
    [DecidableEq G] [∀ layer, DecidableEq (I layer)] [∀ axis, DecidableEq (B axis)]
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    Measurable (target v) := by
  apply Finset.measurable_prod
  intro a _
  have he : Measurable (allocatedLongJetTarget B U basis S x u rows s hA (normalized v) a) :=
    Measurable.of_uncurry_left
      (f := fun y za => allocatedLongJetTarget B U basis S x u rows s hA y a za)
      (x := normalized v)
      (allocatedLongJetTarget_row_measurable B U basis hR hσ S x u rows s hA hσ1 a)
  exact he.comp (measurable_pi_apply a)

include hR hσ hσ1 in
theorem allocatedFiniteLongJetProxy_measurable :
    Measurable (proxy : AllocatedLongJetRows B U basis S O → ℝ) := by
  have hm : Measurable (fun z : AllocatedLongJetRows B U basis S O =>
      ∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) :=
    Finset.measurable_prod _ (fun a _ =>
      (allocatedLongJetMask_measurable B U basis S x rows modulus residue a).comp (measurable_pi_apply a))
  exact hm.mul (w.mean_measurable (fun z v => target v z)
    (fun v => allocatedPrincipalLongJetTarget_measurable B U basis hR hσ S x u rows s hA hσ1 v))

omit [∀ layer, DecidableEq (I layer)] [∀ axis, DecidableEq (B axis)] in
include hR hσ hσ1 hM hi hP hMP hRP hRi hσi hcount in
theorem allocatedLongJetTarget_principal_product_zero
    [∀ layer, DecidableEq (I layer)] [∀ axis, DecidableEq (B axis)]
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (z : AllocatedLongJetRows B U basis S O)
    (hz : z ∉ allocatedLongJetBox B U basis S O T) : target v z = 0 := by
  have hv : ‖normalized v‖ ≤ 1 :=
    principalTupleNormalized_norm_le (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) (principalAxisLength (fun a => ¬grid a) sides)
      (fun d => allocatedPrincipalSides_pos B U basis S ⟨d.1.val, d.2⟩) v
  have ha : ∃ a, z a ∉ allocatedLongJetRowBox B U basis S O T a := by
    simpa only [allocatedLongJetBox, Set.mem_univ_pi, not_forall] using hz
  obtain ⟨a, ha⟩ := ha
  exact Finset.prod_eq_zero (Finset.mem_univ a)
    (allocatedLongJetTarget_zero_off_box B U basis S hR hσ x rows s hA
      hM hi hP hMP hRP hRi hσi hcount u hσ1 (normalized v) hv a (z a) ha)

include hM hi hP hMP hRP hRi hσi hcount in
theorem allocatedFiniteLongJet_l1_comparison {ε : ℝ} (hε : 0 ≤ ε)
    (he : ∀ z, |w.mean (fun v => Q * density v z) - proxy z| ≤ ε) :
    Integrable (fun z => proxy z/Q) reference ∧
      (∫ z, |w.mean (fun v => density v z)-proxy z/Q| ∂reference) ≤ V*ε := by
  have hQ : 0 < Q := Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U basis S a)
  have hf : Measurable (fun z => w.mean (fun v => density v z)) :=
    w.mean_measurable _ (fun v => allocatedLongJetDensity_measurable B U basis hR hσ S x u v rows s hA hσ1)
  have hfi : Integrable (fun z => w.mean (fun v => density v z)) reference :=
    integrable_finsetSum _ (fun v _ =>
      ((allocatedLongJetDensity_probability_data B U basis hR hσ S x u v rows s hA hσ1).2.1).const_mul (w.weight v))
  have hzero (z) (hz : z ∉ allocatedLongJetBox B U basis S O T) : w.mean (fun v => density v z) = 0 := by
    have hh : (fun v => density v z) = fun _ => 0 := by
      funext v
      exact allocatedLongJetDensity_zero_off_box B U basis S hR hσ x rows s hA hM hi hP hMP hRP hRi hσi hcount u hσ1 v z hz
    rw [hh, w.mean_const]
  have hgzero (z) (hz : z ∉ allocatedLongJetBox B U basis S O T) : proxy z = 0 := by
    have hh (v) : target v z = 0 := by
      exact allocatedLongJetTarget_principal_product_zero B U basis hR hσ S x u rows s hA
        hM hi hP hMP hRP hRi hσi hcount hσ1 v z hz
    simp only [hh, w.mean_const, mul_zero]
  have hgm : Measurable (proxy : AllocatedLongJetRows B U basis S O → ℝ) := by
    exact allocatedFiniteLongJetProxy_measurable B U basis hR hσ S x u rows s hA hσ1 w modulus residue
  apply normalized_box_density_l1 reference (allocatedLongJetBox B U basis S O T)
    (allocatedLongJetBox_measurable B U basis S O T) (allocatedLongJetBox_measure_lt_top B U basis S O T)
    _ _ hf hgm hfi hzero hgzero hQ hε (allocatedLongJetBox_measure_bound B U basis S O (Real.exp_pos _).le)
  intro z
  simpa only [w.mean_const_mul] using he z

end Erdos3.VectorPolynomial

end

end OAI
