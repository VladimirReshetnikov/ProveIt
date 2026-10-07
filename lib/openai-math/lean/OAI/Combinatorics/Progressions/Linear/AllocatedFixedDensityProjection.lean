import OAI.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem trimmedSpatialWidths_antitone_budget {K X : Type*} {W W' τ : ℝ}
    (hW : 0 ≤ W) (hWW' : W ≤ W') (hτ : 0 ≤ τ) (N : X → ℕ)
    (z : Option K × X) :
    trimmedSpatialWidths W' τ N z ≤ trimmedSpatialWidths W τ N z := by
  rcases z with ⟨k, i⟩
  cases k with
  | none => exact le_rfl
  | some k =>
    dsimp only [trimmedSpatialWidths, centeredSpatialWidths]
    gcongr

theorem spatialWidthFraction_le_allocated_width {K X : Type*} {P W τ : ℝ}
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hWP : W ≤ Real.exp P) (hτ : 0 ≤ τ)
    (N : X → ℕ) (z : Option K × X) :
    spatialWidthFraction P τ * (N z.2 : ℝ) ≤ trimmedSpatialWidths W τ N z := by
  exact (spatialWidthFraction_le_trimmed_width P hτ N z).trans
    (trimmedSpatialWidths_antitone_budget hW
      (hWP.trans (Real.exp_le_exp.mpr (by linarith))) hτ N z)

namespace VectorPolynomial

open BooleanCubeKernel

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (c : LayerSamplerVariables G I n B → ℤ)

theorem allocatedPhysicalRootBudget_constant_le (k : LayerSamplerVariables G I n B) :
    |(c k : ℝ)| ≤ allocatedPhysicalRootBudget B U basis S c := by
  classical
  apply (Finset.single_le_sum (fun k _ => abs_nonneg (c k : ℝ)) (Finset.mem_univ k)).trans
  exact le_add_of_nonneg_right (by positivity)

theorem allocatedPhysicalCube_site_le_exp {q : ℕ}
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q)
      (allocatedPrincipalSides B U basis S))
    {P : ℝ} (hroot : allocatedPhysicalRootBudget B U basis S c ≤ Real.exp P)
    (hL : (S.value : ℝ) ≤ Real.exp P) (s : Finset (Fin q)) (k : LayerSamplerVariables G I n B) :
    |((affineSite (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) s (some k) : ℤ) : ℝ)| ≤
      Real.exp (P + (q + 2 : ℕ)) := by
  have hs : (s.card : ℝ) ≤ q := by
    exact_mod_cast (show s.card ≤ q from by simpa only [Fintype.card_fin] using s.card_le_univ)
  have hd (i) : |(allocatedPhysicalCubeDirections B U basis S x y i k : ℝ)| ≤ Real.exp P :=
    (allocatedPhysicalCube_directions_bound B U basis S x y i k).trans hL
  have hr : |(allocatedPhysicalCubeRoot B U basis S c x y k : ℝ)| ≤ Real.exp P :=
    (allocatedPhysicalCube_root_budget B U basis S c x y k).trans hroot
  have hsum : |∑ i ∈ s, (allocatedPhysicalCubeDirections B U basis S x y i k : ℝ)| ≤
      (q : ℝ) * Real.exp P := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i ∈ s, Real.exp P := Finset.sum_le_sum (fun i _ => hd i)
      _ = (s.card : ℝ) * Real.exp P := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hs (Real.exp_nonneg P)
  calc
    _ ≤ Real.exp P + (q : ℝ) * Real.exp P := by
      simp only [affineSite, Int.cast_add, Int.cast_sum]
      exact (abs_add_le _ _).trans (add_le_add hr hsum)
    _ ≤ Real.exp ((q : ℝ) + 2) * Real.exp P := by
      have hq : (q : ℝ) + 1 ≤ Real.exp ((q : ℝ) + 2) := by
        linarith [Real.add_one_le_exp ((q : ℝ) + 2)]
      nlinarith [Real.exp_pos P]
    _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Polynomial
open scoped BigOperators

theorem exists_allocated_fixed_density_projection (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P W : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P) (_hW : 0 ≤ W)
    (_hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M),
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S))
    {X : Type*} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    {F : Type*} [Fintype F]
    (frequency : F → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ)
    (_hfrequency : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ Real.exp P),
    ∃ b : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ,
      (∀ a j s t, |(b a j s t : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
    ∀ (coeff : F → ℂ) (_hcoeff : (∑ a, ‖coeff a‖) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : X → ℤ)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ δ : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hδ : 0 < δ) (_hδP : δ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (density : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ℝ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ v, ‖(density v : ℂ) - coefficientTorusFourierSum U frequency coeff v‖ ≤ η),
    let V := trimmedSpatialWidths (K := LayerSamplerVariables G I n B) W τ N
    let root := allocatedPhysicalCubeRoot B U basis S c x y
    let dirs := allocatedPhysicalCubeDirections B U basis S x y
    let pa := fun j => translate (fun d => (base d : ℝ)) (p j)
    let hma := fun j => coefficients_translate_mem (U j) (fun d => (base d : ℝ)) (p j) (hm j)
    ∃ (hV : ∀ z, 0 < V z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T V z),
      ‖(∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
        (physicalCubeSiteTest test (physicalCubeRootDifferences root dirs base z) *
          (density (affineSampleCoefficientTorus U pa hma (fun k d => (z (k, d) : ℝ))) : ℂ))) -
        ∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
          physicalCubeCoveredTest U root dirs D p hm frequency b coeff test
            (physicalCubeRootDifferences root dirs base z)‖ ≤ η + δ := by
  obtain ⟨A₀, _, hprojection⟩ := exists_fixed_kernel_density_projection m q
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget ((4 * X + C (q + 130 + A₀)) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro G _ I _ n B _ J _ U basis R σ S c x P W hP hG hW hroot hWP hL M hperiod
  let Q := spatialSamplingBudget P + (q + 2 : ℕ)
  have hPQ : P ≤ Q := by
    dsimp [Q, spatialSamplingBudget]
    linarith [Nat.cast_nonneg (α := ℝ) (q + 2)]
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hsiteQ : P + (q + 2 : ℕ) ≤ Q := by dsimp [Q, spatialSamplingBudget]; linarith
  have hcost : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    calc
      _ = (4 * P + (q + 130 + A₀ : ℕ)) ^ A₀ := by
        congr 1
        dsimp [Q, spatialSamplingBudget]
        push_cast
        ring
      _ ≤ _ := by simpa [Polynomial.eval₂_pow] using hbudget P hP
  have hExp := Real.exp_le_exp.mpr hPQ
  obtain ⟨a, ha, _, hperiod⟩ := hperiod
  obtain ⟨D, hD, hDP, hrows⟩ := hprojection (fun g => c (.inl g) + (x g none : ℤ))
    (fun i g => (x g (some i) : ℤ)) (a : ℤ) (by exact_mod_cast ha.ne') hperiod
    hQ (hG.trans hPQ) (fun s g =>
      (kernelCubeBox_site_le_exp (fun g => c (.inl g)) x
        (fun g => (allocatedPhysicalRootBudget_constant_le B U basis S c (.inl g)).trans (hroot.trans hWP))
        hL s g).trans (Real.exp_le_exp.mpr hsiteQ))
  refine ⟨D, hD, hDP.trans (Real.exp_le_exp.mpr hcost), ?_⟩
  intro y X _ _ hX hdim F _ frequency hfrequency
  obtain ⟨b, hb, hproj⟩ := hrows (hX.trans hPQ) (hdim.trans hPQ) U
    (allocatedPhysicalCubeRoot B U basis S c x y) (allocatedPhysicalCubeDirections B U basis S x y)
    Sum.inl (fun _ => rfl) (fun _ _ => rfl)
    (Real.exp_nonneg Q) (Real.exp_nonneg Q) le_rfl le_rfl
    (fun s k => (allocatedPhysicalCube_site_le_exp B U basis S c x y (hroot.trans hWP) hL s k).trans
      (Real.exp_le_exp.mpr hsiteQ)) frequency (fun a j d hd t => (hfrequency a j d hd t).trans hExp)
  refine ⟨b, fun a j s t => (hb a j s t).trans (Real.exp_le_exp.mpr hcost), ?_⟩
  intro coeff hcoeff p hp hm base stride hs hsP τ δ hτ hτP hδ hδP N hsize rank hrank hRank
    test htest T hT density η hη happrox
  have hN (d) : 0 < N d := by exact_mod_cast (Real.exp_pos _).trans_le (hsize d)
  have hV := trimmedSpatialWidths_pos (K := LayerSamplerVariables G I n B) hW hτ N hN
  have hρP : 1 / spatialWidthFraction P τ ≤ Real.exp Q :=
    (spatialWidthFraction_inv_le hP hτ hτP).trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  obtain ⟨hZ, he⟩ := hproj coeff (Real.exp_nonneg Q) le_rfl (hcoeff.trans hExp)
    p hp hm base stride hs (Real.exp_nonneg Q) le_rfl (spatialWidthFraction_pos P hτ) hδ
    hρP (by simpa only [one_div] using hδP.trans hExp) (fun d => (hsP d).trans hExp)
    (fun d => (N d : ℝ)) (fun d => (Real.exp_le_exp.mpr hcost).trans (hsize d)) hrank
    ((Real.exp_le_exp.mpr hcost).trans hRank) test htest T hT
    (trimmedSpatialWidths W τ N) hV (spatialWidthFraction_le_allocated_width hP hW hWP hτ.le N)
    density hη happrox
  exact ⟨hV, hZ, he⟩

end Erdos3.VectorPolynomial

end

end OAI
