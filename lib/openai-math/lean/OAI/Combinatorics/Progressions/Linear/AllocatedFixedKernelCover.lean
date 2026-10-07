import OAI.Combinatorics.Progressions.Geometry.SpatialChoiceEnvelope
import OAI.Combinatorics.Progressions.Probability.PositiveDensityNormalization

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

noncomputable def allocatedPhysicalCubeRoot : LayerSamplerVariables G I n B → ℤ :=
  fun k => c k + Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ)) k

noncomputable def allocatedPhysicalCubeDirections : Matrix α (LayerSamplerVariables G I n B) ℤ :=
  fun i => Sum.elim (fun g => (x g (some i) : ℤ)) (fun j => (y j (some i) : ℤ))

theorem allocatedPhysicalCube_vertex (t : Finset α) :
    integerAffineCube (allocatedPhysicalCubeRoot B U basis S c x y)
        (allocatedPhysicalCubeDirections B U basis S x y) t =
      fun k => c k + Sum.elim
        (fun g => integerScalarCubeValue (fun i => (x g i : ℤ)) t)
        (fun j => integerScalarCubeValue (fun i => (y j i : ℤ)) t) k := by
  funext k
  cases k <;> simp only [integerAffineCube, allocatedPhysicalCubeRoot,
    allocatedPhysicalCubeDirections, Sum.elim_inl, Sum.elim_inr, integerScalarCubeValue] <;> ring

omit [Fintype α] in
theorem allocatedPhysicalCube_principal_columns (i : Unit ⊕ α)
    (j : PrincipalTupleIndex B (layerSamplerDegree I n)) :
    physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
        (allocatedPhysicalCubeDirections B U basis S x y) i (some (.inr j)) =
      principalSpatialColumns (fun j => c (.inr j)) id y i j := by
  cases i <;> rfl

omit [Fintype α] in
theorem allocatedPhysicalCube_kernel_columns (i : Unit ⊕ α) (g : G) :
    physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
        (allocatedPhysicalCubeDirections B U basis S x y) i (some (.inl g)) =
      rootDifferenceMatrix (fun g => c (.inl g) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) i (.inr g) := by
  cases i <;> rfl

omit [Fintype α] in
theorem allocatedPhysicalCube_base_column (i : Unit ⊕ α) :
    physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
        (allocatedPhysicalCubeDirections B U basis S x y) i none =
      rootDifferenceMatrix (fun g => c (.inl g) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) i (.inl ()) := by
  cases i with
  | inl i => cases i; rfl
  | inr i => rfl

theorem allocatedPhysicalCube_physical_vertex {X : Type*} (base : X → ℤ)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) (a : X) (t : Finset α) :
    physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U basis S c x y)
        (allocatedPhysicalCubeDirections B U basis S x y) base z a (.inl ()) +
      ∑ i ∈ t, physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U basis S c x y)
        (allocatedPhysicalCubeDirections B U basis S x y) base z a (.inr i) =
      jointIntegerPhysicalSite (fun k => c k + Sum.elim
        (fun g => integerScalarCubeValue (fun i => (x g i : ℤ)) t)
        (fun j => integerScalarCubeValue (fun i => (y j i : ℤ)) t) k) (base, z) a := by
  rw [physicalCubeRootDifferences_vertex, allocatedPhysicalCube_vertex]

omit [Fintype α] in
theorem allocatedPhysicalCube_join_columns
    (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
      (allocatedPrincipalSides B U basis S))
    (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
      (allocatedPrincipalSides B U basis S))
    (i : Unit ⊕ α) (j : PrincipalTupleIndex B (layerSamplerDegree I n)) :
    physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x
        (principalAxisJoin (allocatedGridAxis (I := I) U basis S.value) u v))
      (allocatedPhysicalCubeDirections B U basis S x
        (principalAxisJoin (allocatedGridAxis (I := I) U basis S.value) u v)) i (some (.inr j)) =
      allocatedSpatialColumns B U basis S u (fun _ : Unit => fun j => c (.inr j))
        (fun _ : Unit => id) v () i j := by
  exact allocatedPhysicalCube_principal_columns B U basis S c x _ i j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators

theorem kernelCubeBox_site_le_exp {G : Type*} {q L : ℕ}
    (c : G → ℤ) (x : G → IntegerScalarCubeBox (Fin q) L) {P : ℝ}
    (hc : ∀ g, |(c g : ℝ)| ≤ Real.exp P) (hL : (L : ℝ) ≤ Real.exp P)
    (s : Finset (Fin q)) (g : G) :
    |((BooleanCubeKernel.affineSite (fun g => c g + (x g none : ℤ))
      (fun i g => (x g (some i) : ℤ)) s (some g) : ℤ) : ℝ)| ≤ Real.exp (P + (q + 2 : ℕ)) := by
  have hx (i) : |((x g i : ℤ) : ℝ)| ≤ Real.exp P := by
    have hi := Finset.mem_Ico.mp (x g i).property
    have hl : |((x g i : ℤ) : ℝ)| ≤ L := by exact_mod_cast abs_le.mpr ⟨hi.1, hi.2.le⟩
    exact hl.trans hL
  have hs : (s.card : ℝ) ≤ q := by
    exact_mod_cast (show s.card ≤ q from by simpa only [Fintype.card_fin] using s.card_le_univ)
  have hsum : |∑ i ∈ s, ((x g (some i) : ℤ) : ℝ)| ≤ (q : ℝ) * Real.exp P := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i ∈ s, Real.exp P := Finset.sum_le_sum (fun i _ => hx (some i))
      _ = (s.card : ℝ) * Real.exp P := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hs (Real.exp_nonneg P)
  have hraw : |(c g : ℝ) + ((x g none : ℤ) : ℝ) + ∑ i ∈ s, ((x g (some i) : ℤ) : ℝ)| ≤
      ((q : ℝ) + 2) * Real.exp P := by
    have h := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (hc g) (hx none))) hsum)
    nlinarith
  calc
    _ = |(c g : ℝ) + ((x g none : ℤ) : ℝ) + ∑ i ∈ s, ((x g (some i) : ℤ) : ℝ)| := by
      simp only [BooleanCubeKernel.affineSite, Int.cast_add, Int.cast_sum]
    _ ≤ ((q : ℝ) + 2) * Real.exp P := hraw
    _ ≤ Real.exp ((q : ℝ) + 2) * Real.exp P := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg P)
      linarith [Real.add_one_le_exp ((q : ℝ) + 2)]
    _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

namespace VectorPolynomial

open BooleanCubeKernel Polynomial

theorem exists_allocated_fixed_kernel_cover (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hc : ∀ g, |(c (.inl g) : ℝ)| ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M),
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S))
      {F : Type*} [Fintype F]
      (frequency : F → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ),
    (∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ Real.exp P) →
    ∃ b : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ,
      (∀ a j s t, |(b a j s t : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
        (hm : ∀ j d, coefficients (p j) d ∈ U j) (coeff : F → ℂ)
        (z : Option (LayerSamplerVariables G I n B) → X → ℝ),
        affineCubeFourierProjection U (allocatedPhysicalCubeRoot B U basis S c x y)
          (allocatedPhysicalCubeDirections B U basis S x y) frequency p coeff z =
        retainedSiteFourierSum U (allocatedPhysicalCubeRoot B U basis S c x y)
          (allocatedPhysicalCubeDirections B U basis S x y) frequency b coeff
          (affineCoveredSiteSample U (allocatedPhysicalCubeRoot B U basis S c x y)
            (allocatedPhysicalCubeDirections B U basis S x y) D p hm z) := by
  obtain ⟨A₀, _, hcover⟩ := exists_fixed_kernel_site_fourier_projection m q
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget ((X + C (q + 2 + A₀)) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro G _ I _ n B _ J _ U basis R σ S c x P hP hG hc hL M hperiod
  let Q := P + (q + 2 : ℕ)
  have hPQ : P ≤ Q := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hbound : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    simpa [Q, Polynomial.eval₂_pow, Nat.cast_add, add_assoc] using hbudget P hP
  obtain ⟨a, ha, _, hperiod⟩ := hperiod
  obtain ⟨D, hD, hDP, hrows⟩ := hcover (fun g => c (.inl g) + (x g none : ℤ))
    (fun i g => (x g (some i) : ℤ)) (a : ℤ) (by exact_mod_cast ha.ne') hperiod hQ (hG.trans hPQ)
    (kernelCubeBox_site_le_exp (fun g => c (.inl g)) x hc hL)
  refine ⟨D, hD, hDP.trans (Real.exp_le_exp.mpr hbound), ?_⟩
  intro y F _ frequency hfrequency
  obtain ⟨b, hb, he⟩ := hrows (allocatedPhysicalCubeRoot B U basis S c x y)
    (allocatedPhysicalCubeDirections B U basis S x y) Sum.inl (fun _ => rfl) (fun _ _ => rfl) U frequency
    (fun a j d hd t => (hfrequency a j d hd t).trans (Real.exp_le_exp.mpr hPQ))
  exact ⟨b, fun a j s t => (hb a j s t).trans (Real.exp_le_exp.mpr hbound), he⟩

end VectorPolynomial
end Erdos3

end

end OAI
