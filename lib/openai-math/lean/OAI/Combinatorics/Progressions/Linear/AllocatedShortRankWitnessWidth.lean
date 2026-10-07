import OAI.Combinatorics.Progressions.Dynamics.PhysicalBadProductErrorBudget
import OAI.Combinatorics.Progressions.Geometry.AllocatedSpatialWitnessComparison
import OAI.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineFullWitness
import OAI.Combinatorics.Progressions.Probability.AllocatedSpatialCoefficientReferenceLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

def allocatedReadCoefficientChartResidues {M : ℕ}
    (f : AllocatedActualCoefficientIndex G X I E n B → ZMod M) :
    CoefficientChartResidues (LayerSamplerVariables G I n B) n E M :=
  fun j q => Sum.elim (fun i => allocatedReadProjection f ⟨j,Sum.inr i⟩ q)
    (allocatedReadDeck f j q)

def allocatedChartActualResidues {M : ℕ}
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod M)
    (chart : CoefficientChartResidues (LayerSamplerVariables G I n B) n E M) :
    AllocatedActualCoefficientIndex G X I E n B → ZMod M :=
  allocatedMixedFullArray
    (Sum.elim noise (fun ⟨j,q,i⟩ => chart j q (Sum.inl i)))
    (fun ⟨j,q,i⟩ => chart j q (Sum.inr i)) (fun _ => 0)

@[simp] theorem allocatedChartActualResidues_noise {M : ℕ}
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod M)
    (chart : CoefficientChartResidues (LayerSamplerVariables G I n B) n E M) :
    allocatedReadNoise (allocatedChartActualResidues noise chart) = noise := rfl

@[simp] theorem allocatedChartActualResidues_deck {M : ℕ}
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod M)
    (chart : CoefficientChartResidues (LayerSamplerVariables G I n B) n E M) :
    allocatedReadDeck (allocatedChartActualResidues noise chart) =
      fun j q i => chart j q (Sum.inr i) := rfl

@[simp] theorem allocatedChartActualResidues_integer {M : ℕ}
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod M)
    (chart : CoefficientChartResidues (LayerSamplerVariables G I n B) n E M)
    (j : Fin m) (i : Fin (n j)) :
    allocatedReadProjection (allocatedChartActualResidues noise chart) ⟨j,Sum.inr i⟩ =
      fun q => chart j q (Sum.inl i) := rfl

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

def allocatedChartResiduePrimePowerWitness
    (inactive : LayerSamplerAxis I n → Prop) (C : ℝ)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod M)
    (chart : CoefficientChartResidues (LayerSamplerVariables G I n B) n E M) : Prop :=
  allocatedResiduePrimePowerWitness inactive C P A M hdiv
    (allocatedChartActualResidues noise chart)

theorem allocatedChartResiduePrimePowerWitness_read
    (inactive : LayerSamplerAxis I n → Prop) (C : ℝ)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (f : AllocatedActualCoefficientIndex G X I E n B → ZMod M) :
    allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
      (allocatedReadNoise f) (allocatedReadCoefficientChartResidues f) =
      allocatedResiduePrimePowerWitness inactive C P A M hdiv f := by
  unfold allocatedChartResiduePrimePowerWitness
  apply allocatedResiduePrimePowerWitness_congr_outputs
  · rfl
  · rfl
  · intro j i
    rfl

theorem allocatedChartResiduePrimePowerWitness_iff_actual
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
      (allocatedReadNoise (fun i => (f i : ZMod M)))
      (allocatedReadCoefficientChartResidues (fun i => (f i : ZMod M))) ↔
      ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val) f := by
  rw [allocatedChartResiduePrimePowerWitness_read]
  exact allocatedResiduePrimePowerWitness_iff_actual inactive spatial kernel block C P A M hdiv f

omit [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in

theorem allocatedReadCoefficientChartResidues_sampler
    (M : ℕ) (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (x : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hinteger : ∀ (j : Fin m) (i : Fin (n j))
      (q : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
      allocatedReadProjection f ⟨j,Sum.inr i⟩ q = (x j).2 i q) :
    allocatedReadCoefficientChartResidues (fun i => (f i : ZMod M)) =
      coefficientSamplerChartResidues M x (fun j q i => ((allocatedReadDeck f j q i : ℤ) : ZMod M)) := by
  funext j q i
  cases i with
  | inl i => exact congrArg (fun z : ℤ => (z : ZMod M)) (hinteger j i q)
  | inr i => rfl

theorem allocatedChartResiduePrimePowerWitness_sampler_iff_actual
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (x : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hinteger : ∀ (j : Fin m) (i : Fin (n j))
      (q : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
      allocatedReadProjection f ⟨j,Sum.inr i⟩ q = (x j).2 i q) :
    allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
      (fun q => ((allocatedReadNoise f q : ℤ) : ZMod M))
      (coefficientSamplerChartResidues M x (fun j q i => ((allocatedReadDeck f j q i : ℤ) : ZMod M))) ↔
      ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val) f := by
  rw [← allocatedReadCoefficientChartResidues_sampler M f x hinteger]
  exact allocatedChartResiduePrimePowerWitness_iff_actual inactive spatial kernel block C P A M hdiv f

theorem allocatedChartResiduePrimePowerWitness_mixedArray_iff_actual
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (x : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (deck : ∀ j, BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → ℤ) :
    allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
      (fun q => (noise q : ZMod M))
      (coefficientSamplerChartResidues M x (fun j q i => (deck j q i : ZMod M))) ↔
      ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
        (allocatedMixedFullArray
          (Sum.elim noise (fun ⟨j,q,i⟩ => (x j).2 i q))
          (fun ⟨j,q,i⟩ => deck j q i) continuous) := by
  exact allocatedChartResiduePrimePowerWitness_sampler_iff_actual
    inactive spatial kernel block C P A M hdiv
    (allocatedMixedFullArray
      (Sum.elim noise (fun ⟨j,q,i⟩ => (x j).2 i q))
      (fun ⟨j,q,i⟩ => deck j q i) continuous) x (fun _ _ _ => rfl)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

theorem allocatedChartResiduePrimePowerWitness_integerDeck_iff
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (q : ℕ) [NeZero q] (hdiv : ∀ p : P, p.val ^ A p.val ∣ q)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (a : CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q) :
    allocatedChartResiduePrimePowerWitness inactive C P A q hdiv
      (fun v => (noise v : ZMod q)) (coefficientIntegerDeckChartResidues q a r) ↔
    ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
      (allocatedMixedFullArray (Sum.elim noise a)
        (fun ⟨j,e,i⟩ => ((r j e i).val : ℤ)) (fun _ => 0)) := by
  let f := allocatedMixedFullArray (Sum.elim noise a)
    (fun ⟨j,e,i⟩ => ((r j e i).val : ℤ)) (fun _ => 0)
  have hchart : allocatedReadCoefficientChartResidues (fun i => (f i : ZMod q)) =
      coefficientIntegerDeckChartResidues q a r := by
    funext j e i
    cases i with
    | inl i => rfl
    | inr i =>
      change (((r j e i).val : ℤ) : ZMod q) = r j e i
      simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  have h := allocatedChartResiduePrimePowerWitness_iff_actual
    inactive spatial kernel block C P A q hdiv f
  rw [hchart] at h
  exact h

variable (B) {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedSpatialRankReferenceLaw
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (q : ℕ) [NeZero q] (hdiv : ∀ p : P, p.val ^ A p.val ∣ q)
    (noiseLaw : PMF (Option (LayerSamplerVariables G I n B) × X → ℤ)) :
    (∑' z, (noiseLaw z).toReal *
      ∫ a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
          CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q,
        (if allocatedChartResiduePrimePowerWitness inactive C P A q hdiv
          (fun v => (z v : ZMod q)) (coefficientSamplerChartResidues q a.1 a.2)
          then (1 : ℝ) else 0)
        ∂(allocatedCoefficientSource B U b hR hσ S).prod
          (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q)).toMeasure) =
    ((noiseLaw.bind fun z => (allocatedCoefficientIntegerPMF B U b hR hσ S).bind
      fun a => (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q)).map
        fun r => decide (∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
          (allocatedMixedFullArray (Sum.elim z a)
            (fun ⟨j,e,i⟩ => ((r j e i).val : ℤ)) (fun _ => 0)))) true).toReal := by
  have h := allocatedSpatialCoefficientReferenceLaw B U b hR hσ S q noiseLaw
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q))
    (allocatedChartResiduePrimePowerWitness inactive C P A q hdiv)
  simpa only [allocatedChartResiduePrimePowerWitness_integerDeck_iff
    inactive spatial kernel block C P A q hdiv] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable local instance spatialReferenceSmoothFintype :
    Fintype (AllocatedFullSmoothCoefficientIndex G X I n B) := inferInstance
noncomputable local instance spatialReferenceDeckFintype :
    Fintype (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := inferInstance
noncomputable local instance spatialReferenceDeckDecidableEq :
    DecidableEq (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := Classical.decEq _

theorem allocatedSpatialRank_cell_bind_eq
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (residue : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V)) (N : ℕ) [NeZero N]
    {Y : Type*}
    (test : (AllocatedFullSmoothCoefficientIndex G X I n B → ℤ) →
      (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N) → Y) :
    ((residueSmoothPMF residue stride hstride V hV hZ).bind fun noise =>
      (allocatedCoefficientIntegerPMF B U basis hR hσ S).bind fun a =>
        (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)).map
          fun deck => test (Sum.elim noise a) (coefficientDeckScalarEquiv deck)) =
    ((independentProductPMF (allocatedFullSmoothScalarPMF B U basis hR hσ S
      (residueSmoothScalarPMFs residue stride hstride V hV hZ))).bind fun z =>
        (PMF.uniformOfFintype
          (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N)).map
          fun deck => test (allocatedFullSmoothAffine (fun x => (stride x : ℤ)) residue z) deck) := by
  rw [allocatedFullSmoothProductPMF_factorization, PMF.bind_bind]
  simp_rw [PMF.bind_map]
  rw [residueSmoothPMF, residueSmoothIndexPMF_eq_independent, PMF.bind_map]
  apply congrArg (PMF.bind _)
  funext noise
  apply congrArg (PMF.bind _)
  funext a
  simp only [Function.comp_apply]
  have haff : Sum.elim (residueLatticeArray residue stride noise) a =
      allocatedFullSmoothAffine (fun x => (stride x : ℤ)) residue (Sum.elim noise a) := by
    funext t
    cases t <;> rfl
  rw [haff]
  exact coefficientDeckScalar_uniform_test N
    (test (allocatedFullSmoothAffine (fun x => (stride x : ℤ)) residue (Sum.elim noise a)))

noncomputable def allocatedSpatialRankSelectedWidth {L : ℕ}
    (spatial : Fin L ↪ G) (stride : X → ℕ)
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) :
    AllocatedSmoothRankCoefficientIndex X (allocatedGridAxis (I := I) U basis S.value) L → ℝ :=
  allocatedSelectedSmoothWidth B U basis S (allocatedGridAxis (I := I) U basis S.value)
    (fun l x => residueProfileWidth stride V (some (.inl (spatial l)),x))

theorem allocatedSpatialRank_cell_event {L N D : ℕ} [NeZero N]
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis
      (allocatedGridAxis (I := I) U basis S.value) j, Fin L ↪ B ⟨j,b.val⟩)
    (hm : 0 < m) (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (residue : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V))
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hpositive : ∀ p ∈ P, 0 < A p)
    (hdeep : ∀ p ∈ P, ∀ x, 2 * (stride x).factorization p ≤ A p)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hthreshold : ∀ p ∈ P, modularCoefficientPrimeThreshold m ≤ p ^ A p)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : P, p.val ^ A p.val) ≤ allocatedSpatialRankSelectedWidth B U basis S spatial stride V j) :
    (((residueSmoothPMF residue stride hstride V hV hZ).bind fun noise =>
      (allocatedCoefficientIntegerPMF B U basis hR hσ S).bind fun a =>
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)).map
        fun deck => decide (∀ p : P, allocatedActualModulusBad
          (allocatedGridAxis (I := I) U basis S.value) spatial kernel block C (p.val ^ A p.val)
          (allocatedMixedFullArray (Sum.elim noise a)
            (fun ⟨j,e,i⟩ => ((deck j e i).val : ℤ)) (fun _ => 0)))) true).toReal ≤
      1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (∏ p : P, p.val ^ A p.val) /
          allocatedSpatialRankSelectedWidth B U basis S spatial stride V j := by
  let inactive := allocatedGridAxis (I := I) U basis S.value
  let noiseCenter : Fin L → X → ℝ :=
    fun l x => residueProfileCenter residue stride (some (.inl (spatial l)),x)
  let noiseWidth : Fin L → X → ℝ :=
    fun l x => residueProfileWidth stride V (some (.inl (spatial l)),x)
  let center := allocatedSelectedSmoothCenter B U basis S inactive noiseCenter
  let width := allocatedSelectedSmoothWidth B U basis S inactive noiseWidth
  let noisePMF := residueSmoothScalarPMFs residue stride hstride V hV hZ
  let laws := allocatedFullSmoothScalarPMF B U basis hR hσ S noisePMF
  have hnw : ∀ l x, 0 < noiseWidth l x :=
    fun l x => residueProfileWidth_pos stride V hstride hV _
  have hnm : ∀ l x, 0 < shiftedSmoothSampleSum (noiseCenter l x) (noiseWidth l x) :=
    fun l x => shiftedSmoothProductMass_coordinate_pos _ _
      (residueProfileWidth_pos stride V hstride hV) hZ _
  have hactive := allocatedGridPrincipalRank_active B U basis S
  have hw : ∀ j, 0 < width j :=
    allocatedSelectedSmoothWidth_pos B U basis hR S inactive noiseWidth hnw
  have hmasses : ∀ j, 0 < shiftedSmoothSampleSum (center j) (width j) :=
    allocatedSelectedSmoothMass_pos B U basis hR S inactive noiseCenter noiseWidth hnm hactive
  have hz : 0 < shiftedSmoothProductMass center width := by
    rw [shiftedSmoothProductMass_eq_prod _ _ hw]
    exact Finset.prod_pos (fun j _ => hmasses j)
  have hcoordinate : ∀ i, laws (allocatedSmoothFullEmbedding inactive spatial block i) =
      shiftedSmoothCoefficientPMF (center i) (width i) (hw i)
        (shiftedSmoothProductMass_coordinate_pos center width hw hz i) := by
    intro i
    exact allocatedFullSmoothScalarPMF_selected B U basis hR hσ S inactive spatial block
      noiseCenter noiseWidth noisePMF hnw hnm (fun _ _ => rfl) hactive i
  have h := allocatedAffineProductMixed_primePower_event inactive spatial kernel block
    (fun _ => 0) stride hstride residue laws hm center width hw hz hcoordinate
    P A hprime hcover hpositive hdeep hD hC hL hthreshold hlarge
  let test := fun (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → ℤ)
      (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N) =>
    decide (∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
      (allocatedMixedFullArray smooth (fun t => ((deck t).val : ℤ)) (fun _ => 0)))
  have he := allocatedSpatialRank_cell_bind_eq B U basis hR hσ S stride hstride residue V hV hZ N test
  exact (congrArg (fun p : PMF Bool => (p true).toReal) he).trans_le h

theorem allocatedSpatialRank_reference_event {L N D : ℕ} [NeZero N]
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis
      (allocatedGridAxis (I := I) U basis S.value) j, Fin L ↪ B ⟨j,b.val⟩)
    (hm : 0 < m) (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride V z)
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hpositive : ∀ p ∈ P, 0 < A p)
    (hdeep : ∀ p ∈ P, ∀ x, 2 * (stride x).factorization p ≤ A p)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hthreshold : ∀ p ∈ P, modularCoefficientPrimeThreshold m ≤ p ^ A p)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : P, p.val ^ A p.val) ≤ allocatedSpatialRankSelectedWidth B U basis S spatial stride V j) :
    (((selectedResidueSmoothPMF stride cells V hV hZ).bind fun noise =>
      (allocatedCoefficientIntegerPMF B U basis hR hσ S).bind fun a =>
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)).map
        fun deck => decide (∀ p : P, allocatedActualModulusBad
          (allocatedGridAxis (I := I) U basis S.value) spatial kernel block C (p.val ^ A p.val)
          (allocatedMixedFullArray (Sum.elim noise a)
            (fun ⟨j,e,i⟩ => ((deck j e i).val : ℤ)) (fun _ => 0)))) true).toReal ≤
      1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (∏ p : P, p.val ^ A p.val) /
          allocatedSpatialRankSelectedWidth B U basis S spatial stride V j := by
  have hc (r : cells) : 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative stride r.val) stride)
      (residueProfileWidth stride V) := by
    rw [shiftedSmoothProductMass_eq_prod _ _ (residueProfileWidth_pos stride V hstride hV)]
    exact Finset.prod_pos (fun z _ => shiftedSmoothSampleSum_pos _ (hscale z))
  apply selectedResidueSmoothPMF_bind_le_of_cells stride hstride cells V hV hZ hc
  intro r
  exact allocatedSpatialRank_cell_event B U basis hR hσ S spatial kernel block hm stride hstride
    (boundedColumnResidueRepresentative stride r.val) V hV (hc r) P A hprime hcover hpositive
    hdeep hD hC hL hthreshold hlarge

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in

theorem exists_allocated_physical_rank_witness_comparison
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) [NeZero q] (hq : 0 < q)
    {P δ : ℝ} (hP : 0 ≤ P) (hmP : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hqP : (q : ℝ) ≤ Real.exp P) (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type} [Fintype X] [DecidableEq X]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {Ps ε ρ Rs Smax : ℝ} (hPs : 0 ≤ Ps) (hX : (Fintype.card X : ℝ) ≤ Ps)
    (hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Ps)
    (hqPs : (q : ℝ) ≤ Real.exp Ps)
    (hε : 0 < ε) (hρ : 0 < ρ) (hεPs : 1 / ε ≤ Real.exp Ps) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp Ps) (hstrideMax : ∀ x, ((stride x * q : ℕ) : ℝ) ≤ Smax)
    (H : X → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hcells : cells.Nonempty)
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ}
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
    (rankC : ℝ) (primes : Finset ℕ) [∀ p : primes, NeZero p.val] (depth : ℕ → ℕ)
    (hdiv : ∀ p : primes, p.val ^ depth p.val ∣ q)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hsmallError : 2 * δ + ε ≤ 1 / 2) :
    let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 2 * δ + ε ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      |(∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
          (if coefficientDeckChartEvent U bW b hb o q (allocatedChartResiduePrimePowerWitness inactive rankC primes depth q hdiv
            (fun v => (z v : ZMod q))) (sample z) then 1 else 0)) -
        (((selectedResidueSmoothPMF stride cells width hwidth hZ).bind fun z =>
          (allocatedCoefficientIntegerPMF B U b hR hσ S).bind fun a =>
            (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q)).map
              fun r => decide (∀ p : primes, allocatedActualModulusBad inactive spatial kernel block
                rankC (p.val ^ depth p.val) (allocatedMixedFullArray (Sum.elim z a)
                  (fun ⟨j,e,i⟩ => ((r j e i).val : ℤ)) (fun _ => 0)))) true).toReal| ≤
        12 * (2 * δ + ε) := by
  dsimp only
  obtain ⟨hD0, hZ, hDpos, hmass, hlower, hupper, he⟩ :=
    exists_allocated_spatial_witness_comparison B U bW b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall q hq hP hmP hK hRP hσP hcount hI hn hJ hAP hLP
      hCP hVP hqP hδ hδP μ ν poly hp hm hPs hX hframe hqPs hε hρ hεPs hρPs stride hstride
      hSmax hSmaxPs hstrideMax H hsize hrank hRs cells hcells
      (allocatedChartResiduePrimePowerWitness inactive rankC primes depth q hdiv)
      width hwidth hwide hfreqPs hmassPs hsmallError
  have href := allocatedSpatialRankReferenceLaw (E := E) B U b hR hσ S inactive spatial kernel block
    rankC primes depth q hdiv (selectedResidueSmoothPMF stride cells width hwidth hZ)
  rw [href] at he
  exact ⟨hD0, hZ, hDpos, hmass, hlower, hupper, he⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable local instance shortSpatialReferenceSmoothFintype :
    Fintype (AllocatedFullSmoothCoefficientIndex G X I n B) := inferInstance
noncomputable local instance shortSpatialReferenceDeckFintype :
    Fintype (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := inferInstance
noncomputable local instance shortSpatialReferenceDeckDecidableEq :
    DecidableEq (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := Classical.decEq _

theorem allocatedShortPrincipalRank_active (j : Fin m)
    (i : AllocatedCongruenceIntegerAxis (allocatedShortAxis (I := I) U basis S.value) j) :
    S.value ^ (j.val + 1) < basisAxisScale (basis j) i.val := by
  exact Nat.lt_of_not_ge i.property

noncomputable def allocatedShortRankSelectedWidth {L : ℕ}
    (spatial : Fin L ↪ G) (stride : X → ℕ)
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) :
    AllocatedSmoothRankCoefficientIndex X (allocatedShortAxis (I := I) U basis S.value) L → ℝ :=
  allocatedSelectedSmoothWidth B U basis S (allocatedShortAxis (I := I) U basis S.value)
    (fun l x => residueProfileWidth stride V (some (.inl (spatial l)),x))

theorem allocatedShortRank_cell_event {L N D : ℕ} [NeZero N]
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis
      (allocatedShortAxis (I := I) U basis S.value) j, Fin L ↪ B ⟨j,b.val⟩)
    (hm : 0 < m) (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (residue : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V))
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hpositive : ∀ p ∈ P, 0 < A p)
    (hdeep : ∀ p ∈ P, ∀ x, 2 * (stride x).factorization p ≤ A p)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hthreshold : ∀ p ∈ P, modularCoefficientPrimeThreshold m ≤ p ^ A p)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : P, p.val ^ A p.val) ≤ allocatedShortRankSelectedWidth B U basis S spatial stride V j) :
    (((residueSmoothPMF residue stride hstride V hV hZ).bind fun noise =>
      (allocatedCoefficientIntegerPMF B U basis hR hσ S).bind fun a =>
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)).map
        fun deck => decide (∀ p : P, allocatedActualModulusBad
          (allocatedShortAxis (I := I) U basis S.value) spatial kernel block C (p.val ^ A p.val)
          (allocatedMixedFullArray (Sum.elim noise a)
            (fun ⟨j,e,i⟩ => ((deck j e i).val : ℤ)) (fun _ => 0)))) true).toReal ≤
      1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (∏ p : P, p.val ^ A p.val) /
          allocatedShortRankSelectedWidth B U basis S spatial stride V j := by
  let inactive := allocatedShortAxis (I := I) U basis S.value
  let noiseCenter : Fin L → X → ℝ :=
    fun l x => residueProfileCenter residue stride (some (.inl (spatial l)),x)
  let noiseWidth : Fin L → X → ℝ :=
    fun l x => residueProfileWidth stride V (some (.inl (spatial l)),x)
  let center := allocatedSelectedSmoothCenter B U basis S inactive noiseCenter
  let width := allocatedSelectedSmoothWidth B U basis S inactive noiseWidth
  let noisePMF := residueSmoothScalarPMFs residue stride hstride V hV hZ
  let laws := allocatedFullSmoothScalarPMF B U basis hR hσ S noisePMF
  have hnw : ∀ l x, 0 < noiseWidth l x :=
    fun l x => residueProfileWidth_pos stride V hstride hV _
  have hnm : ∀ l x, 0 < shiftedSmoothSampleSum (noiseCenter l x) (noiseWidth l x) :=
    fun l x => shiftedSmoothProductMass_coordinate_pos _ _
      (residueProfileWidth_pos stride V hstride hV) hZ _
  have hactive := allocatedShortPrincipalRank_active B U basis S
  have hw : ∀ j, 0 < width j :=
    allocatedSelectedSmoothWidth_pos B U basis hR S inactive noiseWidth hnw
  have hmasses : ∀ j, 0 < shiftedSmoothSampleSum (center j) (width j) :=
    allocatedSelectedSmoothMass_pos B U basis hR S inactive noiseCenter noiseWidth hnm hactive
  have hz : 0 < shiftedSmoothProductMass center width := by
    rw [shiftedSmoothProductMass_eq_prod _ _ hw]
    exact Finset.prod_pos (fun j _ => hmasses j)
  have hcoordinate : ∀ i, laws (allocatedSmoothFullEmbedding inactive spatial block i) =
      shiftedSmoothCoefficientPMF (center i) (width i) (hw i)
        (shiftedSmoothProductMass_coordinate_pos center width hw hz i) := by
    intro i
    exact allocatedFullSmoothScalarPMF_selected B U basis hR hσ S inactive spatial block
      noiseCenter noiseWidth noisePMF hnw hnm (fun _ _ => rfl) hactive i
  have h := allocatedAffineProductMixed_primePower_event inactive spatial kernel block
    (fun _ => 0) stride hstride residue laws hm center width hw hz hcoordinate
    P A hprime hcover hpositive hdeep hD hC hL hthreshold hlarge
  let test := fun (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → ℤ)
      (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N) =>
    decide (∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
      (allocatedMixedFullArray smooth (fun t => ((deck t).val : ℤ)) (fun _ => 0)))
  have he := allocatedSpatialRank_cell_bind_eq B U basis hR hσ S stride hstride residue V hV hZ N test
  exact (congrArg (fun p : PMF Bool => (p true).toReal) he).trans_le h

theorem allocatedShortRank_reference_event {L N D : ℕ} [NeZero N]
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis
      (allocatedShortAxis (I := I) U basis S.value) j, Fin L ↪ B ⟨j,b.val⟩)
    (hm : 0 < m) (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride V z)
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hpositive : ∀ p ∈ P, 0 < A p)
    (hdeep : ∀ p ∈ P, ∀ x, 2 * (stride x).factorization p ≤ A p)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hthreshold : ∀ p ∈ P, modularCoefficientPrimeThreshold m ≤ p ^ A p)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : P, p.val ^ A p.val) ≤ allocatedShortRankSelectedWidth B U basis S spatial stride V j) :
    (((selectedResidueSmoothPMF stride cells V hV hZ).bind fun noise =>
      (allocatedCoefficientIntegerPMF B U basis hR hσ S).bind fun a =>
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)).map
        fun deck => decide (∀ p : P, allocatedActualModulusBad
          (allocatedShortAxis (I := I) U basis S.value) spatial kernel block C (p.val ^ A p.val)
          (allocatedMixedFullArray (Sum.elim noise a)
            (fun ⟨j,e,i⟩ => ((deck j e i).val : ℤ)) (fun _ => 0)))) true).toReal ≤
      1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (∏ p : P, p.val ^ A p.val) /
          allocatedShortRankSelectedWidth B U basis S spatial stride V j := by
  have hc (r : cells) : 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative stride r.val) stride)
      (residueProfileWidth stride V) := by
    rw [shiftedSmoothProductMass_eq_prod _ _ (residueProfileWidth_pos stride V hstride hV)]
    exact Finset.prod_pos (fun z _ => shiftedSmoothSampleSum_pos _ (hscale z))
  apply selectedResidueSmoothPMF_bind_le_of_cells stride hstride cells V hV hZ hc
  intro r
  exact allocatedShortRank_cell_event B U basis hR hσ S spatial kernel block hm stride hstride
    (boundedColumnResidueRepresentative stride r.val) V hV (hc r) P A hprime hcover hpositive
    hdeep hD hC hL hthreshold hlarge

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

omit [Fintype X] in

theorem allocatedSpatialRankSelectedWidth_common_gap {L : ℕ}
    (spatial : Fin L ↪ G) (stride : X → ℕ)
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) {W : ℝ}
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
      8 * (probabilityProfileLipschitz : ℝ) * W ≤
        (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
          ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)))
    (hspatial : ∀ l x, 8 * (probabilityProfileLipschitz : ℝ) * W ≤
      residueProfileWidth stride V (some (.inl (spatial l)), x)) :
    ∀ a, 8 * (probabilityProfileLipschitz : ℝ) * W ≤
      allocatedSpatialRankSelectedWidth B U basis S spatial stride V a := by
  rintro ⟨j, (x | i), l⟩
  · exact hspatial l x.val
  · exact hprincipal j i.val (allocatedGridPrincipalRank_active B U basis S j i)

theorem allocatedSpatialRankSelectedWidth_budget {L : ℕ}
    (spatial : Fin L ↪ G) (stride : X → ℕ)
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) {cap W κ : ℝ}
    (hcap : 0 < cap) (hκ : 0 < κ) (hcapW : cap ≤ W)
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
      8 * (probabilityProfileLipschitz : ℝ) * W ≤
        (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
          ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)))
    (hspatial : ∀ l x, 8 * (probabilityProfileLipschitz : ℝ) * W ≤
      residueProfileWidth stride V (some (.inl (spatial l)), x))
    (hbudget : 2 * (Fintype.card (AllocatedSmoothRankCoefficientIndex X
        (allocatedGridAxis (I := I) U basis S.value) L) : ℝ) * cap / κ ≤ W) :
    (∀ a, 8 * (probabilityProfileLipschitz : ℝ) * cap ≤
      allocatedSpatialRankSelectedWidth B U basis S spatial stride V a) ∧
    (∑ a, 16 * (probabilityProfileLipschitz : ℝ) * cap /
      allocatedSpatialRankSelectedWidth B U basis S spatial stride V a) ≤ κ := by
  apply finite_residue_error_common_gap_budget
    (allocatedSpatialRankSelectedWidth B U basis S spatial stride V)
    (lt_of_lt_of_le zero_lt_one probabilityProfileLipschitz_one_le) hcap hκ hcapW
  · exact allocatedSpatialRankSelectedWidth_common_gap B U basis S spatial stride V hprincipal hspatial
  · exact hbudget

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

omit [Fintype X] in

theorem allocatedShortRankSelectedWidth_common_gap {L : ℕ}
    (spatial : Fin L ↪ G) (stride : X → ℕ)
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) {W : ℝ}
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
      8 * (probabilityProfileLipschitz : ℝ) * W ≤
        (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
          ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)))
    (hspatial : ∀ l x, 8 * (probabilityProfileLipschitz : ℝ) * W ≤
      residueProfileWidth stride V (some (.inl (spatial l)), x)) :
    ∀ a, 8 * (probabilityProfileLipschitz : ℝ) * W ≤
      allocatedShortRankSelectedWidth B U basis S spatial stride V a := by
  rintro ⟨j, (x | i), l⟩
  · exact hspatial l x.val
  · exact hprincipal j i.val (allocatedShortPrincipalRank_active B U basis S j i)

theorem allocatedShortRankSelectedWidth_budget {L : ℕ}
    (spatial : Fin L ↪ G) (stride : X → ℕ)
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) {cap W κ : ℝ}
    (hcap : 0 < cap) (hκ : 0 < κ) (hcapW : cap ≤ W)
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
      8 * (probabilityProfileLipschitz : ℝ) * W ≤
        (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
          ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)))
    (hspatial : ∀ l x, 8 * (probabilityProfileLipschitz : ℝ) * W ≤
      residueProfileWidth stride V (some (.inl (spatial l)), x))
    (hbudget : 2 * (Fintype.card (AllocatedSmoothRankCoefficientIndex X
        (allocatedShortAxis (I := I) U basis S.value) L) : ℝ) * cap / κ ≤ W) :
    (∀ a, 8 * (probabilityProfileLipschitz : ℝ) * cap ≤
      allocatedShortRankSelectedWidth B U basis S spatial stride V a) ∧
    (∑ a, 16 * (probabilityProfileLipschitz : ℝ) * cap /
      allocatedShortRankSelectedWidth B U basis S spatial stride V a) ≤ κ := by
  apply finite_residue_error_common_gap_budget
    (allocatedShortRankSelectedWidth B U basis S spatial stride V)
    (lt_of_lt_of_le zero_lt_one probabilityProfileLipschitz_one_le) hcap hκ hcapW
  · exact allocatedShortRankSelectedWidth_common_gap B U basis S spatial stride V hprincipal hspatial
  · exact hbudget

end Erdos3.VectorPolynomial

end

end OAI
