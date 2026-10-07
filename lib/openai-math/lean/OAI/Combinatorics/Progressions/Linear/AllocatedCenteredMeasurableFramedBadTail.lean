import OAI.Combinatorics.Progressions.Estimates.AllocatedCenteredMeasurableBadTail

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

def allocatedJointFrameRead {R : Type*} [Add R] (a : X → R)
    (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    AllocatedActualCoefficientIndex G X I E n B → R
  | .inl (none,x) => a x + f (.inl (none,x))
  | .inl (some k,x) => f (.inl (some k,x))
  | .inr k => f (.inr k)

theorem allocatedJointFrameRead_noise (a : X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedReadNoise (allocatedJointFrameRead a f) =
      fun t => BooleanCubeKernel.jointIntegerFrame (a, allocatedReadNoise f) t.1 t.2 := by
  funext t
  rcases t with ⟨k,x⟩
  cases k <;> rfl

@[simp] theorem allocatedJointFrameRead_noise_some {R : Type*} [Add R] (a : X → R)
    (f : AllocatedActualCoefficientIndex G X I E n B → R)
    (k : LayerSamplerVariables G I n B) (x : X) :
    allocatedReadNoise (allocatedJointFrameRead a f) (some k,x) =
      allocatedReadNoise f (some k,x) := rfl

@[simp] theorem allocatedJointFrameRead_deck {R : Type*} [Add R] (a : X → R)
    (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    allocatedReadDeck (allocatedJointFrameRead a f) = allocatedReadDeck f := rfl

@[simp] theorem allocatedJointFrameRead_projection {R : Type*} [Add R] (a : X → R)
    (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    allocatedReadProjection (allocatedJointFrameRead a f) = allocatedReadProjection f := rfl

theorem allocatedJointFrameRead_reduce (M : ℕ) (a : X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    (fun i => ((allocatedJointFrameRead a f i : ℤ) : ZMod M)) =
      allocatedJointFrameRead (fun x => (a x : ZMod M)) (fun i => (f i : ZMod M)) := by
  funext i
  rcases i with ⟨k,x⟩ | k
  · cases k
    · exact Int.cast_add _ _
    · rfl
  · rfl

variable [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]

theorem allocatedOriginalCongruenceTop_congr_slopes
    (inactive : LayerSamplerAxis I n → Prop) (M : ℕ)
    (f g : AllocatedActualCoefficientIndex G X I E n B → ZMod M)
    (hnoise : ∀ (k : LayerSamplerVariables G I n B) (x : X),
      allocatedReadNoise f (some k,x) = allocatedReadNoise g (some k,x))
    (hdeck : allocatedReadDeck f = allocatedReadDeck g)
    (hinteger : ∀ (j : Fin m) (i : Fin (n j)),
      allocatedReadProjection f ⟨j,Sum.inr i⟩ = allocatedReadProjection g ⟨j,Sum.inr i⟩)
    (j : Fin m) (v : LayerSamplerVariables G I n B → ZMod M)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    allocatedOriginalTaggedTop inactive j (allocatedReadNoise f) (allocatedReadDeck f)
      (fun a => allocatedReadProjection f ⟨j,a.val⟩) v
      (allocatedCongruenceOutputEmbedding inactive j o) =
    allocatedOriginalTaggedTop inactive j (allocatedReadNoise g) (allocatedReadDeck g)
      (fun a => allocatedReadProjection g ⟨j,a.val⟩) v
      (allocatedCongruenceOutputEmbedding inactive j o) := by
  rcases o with x | i | a
  · exact spatialRankPolynomial_conditioned_top_congr (allocatedLongEmbedding inactive)
      (fun k => allocatedReadNoise f (k,x.val)) (fun k => allocatedReadNoise g (k,x.val))
      (fun k => hnoise k x.val) v v
  · simp only [allocatedCongruenceOutputEmbedding_deck, allocatedOriginalTaggedTop, hdeck]
  · simp only [allocatedCongruenceOutputEmbedding_integer, allocatedOriginalTaggedTop, hinteger]

variable [Fintype X] [∀ j, Fintype (E j)]

theorem allocatedResidueModulusBad_congr_slopes
    (inactive : LayerSamplerAxis I n → Prop) (C : ℝ) (M : ℕ) [NeZero M]
    (f g : AllocatedActualCoefficientIndex G X I E n B → ZMod M)
    (hnoise : ∀ (k : LayerSamplerVariables G I n B) (x : X),
      allocatedReadNoise f (some k,x) = allocatedReadNoise g (some k,x))
    (hdeck : allocatedReadDeck f = allocatedReadDeck g)
    (hinteger : ∀ (j : Fin m) (i : Fin (n j)),
      allocatedReadProjection f ⟨j,Sum.inr i⟩ = allocatedReadProjection g ⟨j,Sum.inr i⟩) :
    allocatedResidueModulusBad inactive C M f = allocatedResidueModulusBad inactive C M g := by
  unfold allocatedResidueModulusBad
  simp only [allocatedOriginalCongruenceTop_congr_slopes inactive M f g hnoise hdeck hinteger]

theorem allocatedActualModulusBad_jointFrame
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (M : ℕ) [NeZero M] (a : X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedActualModulusBad inactive spatial kernel block C M (allocatedJointFrameRead a f) =
      allocatedActualModulusBad inactive spatial kernel block C M f := by
  rw [allocatedActualModulusBad_eq_residue, allocatedActualModulusBad_eq_residue,
    allocatedJointFrameRead_reduce]
  exact allocatedResidueModulusBad_congr_slopes inactive C M _ _ (fun _ _ => rfl) rfl (fun _ _ => rfl)

theorem allocatedJointFrameRead_rankBad
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ) (p d : ℕ)
    (a : X → ℤ) (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedCongruenceRankBad inactive
      (allocatedReadNoise (allocatedJointFrameRead a f)) (allocatedReadDeck (allocatedJointFrameRead a f))
      (fun j b => allocatedReadProjection (allocatedJointFrameRead a f) ⟨j,b.val⟩)
      spatial kernel block P C p d
      (allocatedCongruenceIntegerSelectedCoefficients inactive
        (allocatedReadNoise (allocatedJointFrameRead a f)) (allocatedReadDeck (allocatedJointFrameRead a f))
        (fun j b => allocatedReadProjection (allocatedJointFrameRead a f) ⟨j,b.val⟩)
        spatial kernel block) =
    allocatedCongruenceRankBad inactive (allocatedReadNoise f) (allocatedReadDeck f)
      (fun j b => allocatedReadProjection f ⟨j,b.val⟩) spatial kernel block P C p d
      (allocatedCongruenceIntegerSelectedCoefficients inactive (allocatedReadNoise f) (allocatedReadDeck f)
        (fun j b => allocatedReadProjection f ⟨j,b.val⟩) spatial kernel block) := by
  unfold allocatedCongruenceRankBad smoothResiduePrimeBad
  apply propext
  apply exists_congr
  intro hp
  let : NeZero p := inferInstanceAs (NeZero (⟨p,hp⟩ : P).val)
  exact (allocatedActualModulusBad_jointFrame inactive spatial kernel block C (p ^ d) a f).to_iff

theorem allocatedJointFrameRead_badDepth
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (C : ℝ) (p : ℕ)
    (a : X → ℤ) (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedCongruenceBadDepth inactive
      (allocatedReadNoise (allocatedJointFrameRead a f)) (allocatedReadDeck (allocatedJointFrameRead a f))
      (fun j b => allocatedReadProjection (allocatedJointFrameRead a f) ⟨j,b.val⟩)
      spatial kernel block P A C p =
    allocatedCongruenceBadDepth inactive (allocatedReadNoise f) (allocatedReadDeck f)
      (fun j b => allocatedReadProjection f ⟨j,b.val⟩) spatial kernel block P A C p := by
  unfold allocatedCongruenceBadDepth largestTestedBadDepth
  simp only [allocatedJointFrameRead_rankBad]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

omit [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in

theorem allocatedReplaceReadNoise_eq_jointFrame
    (base : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hf : allocatedReadNoise f = integerBaseTranslation base + z) :
    allocatedReplaceReadNoise B z f = allocatedJointFrameRead (-base) f := by
  funext i
  rcases i with ⟨k,x⟩ | i
  · have h := congrFun hf (k,x)
    cases k with
    | none =>
      change z (none,x) = -base x + f (.inl (none,x))
      change f (.inl (none,x)) = base x + z (none,x) at h
      omega
    | some k =>
      change z (some k,x) = f (.inl (some k,x))
      simpa only [allocatedReadNoise, Pi.add_apply, integerBaseTranslation,
        baseArrayJoin, Pi.zero_apply, zero_add] using h.symm
  · rfl

variable [Fintype X]

theorem allocatedReplaceReadNoise_modulusBad
    (base : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hf : allocatedReadNoise f = integerBaseTranslation base + z)
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ}
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,b.val⟩)
    (C : ℝ) (M : ℕ) [NeZero M] :
    allocatedActualModulusBad inactive spatial kernel block C M (allocatedReplaceReadNoise B z f) =
      allocatedActualModulusBad inactive spatial kernel block C M f := by
  rw [allocatedReplaceReadNoise_eq_jointFrame B base z f hf]
  exact allocatedActualModulusBad_jointFrame inactive spatial kernel block C M (-base) f

theorem allocatedReplaceReadNoise_primeBad
    (base : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hf : allocatedReadNoise f = integerBaseTranslation base + z)
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ}
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ) (p d : ℕ) :
    allocatedActualPrimeBad inactive spatial kernel block P C p d (allocatedReplaceReadNoise B z f) =
      allocatedActualPrimeBad inactive spatial kernel block P C p d f := by
  rw [allocatedReplaceReadNoise_eq_jointFrame B base z f hf]
  exact allocatedJointFrameRead_rankBad inactive spatial kernel block P C p d (-base) f

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

section BadDepth
variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]
variable (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ)

theorem allocatedActualPrimeBad_jointFrame (p d : ℕ) (a : X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedActualPrimeBad inactive spatial kernel block P C p d (allocatedJointFrameRead a f) =
      allocatedActualPrimeBad inactive spatial kernel block P C p d f := by
  rw [allocatedActualPrimeBad_eq_rankBad, allocatedActualPrimeBad_eq_rankBad]
  exact allocatedJointFrameRead_rankBad inactive spatial kernel block P C p d a f

theorem allocatedActualPrimeBad_depth_jointFrame (A : ℕ → ℕ) (p : ℕ) (a : X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P C) p
        (allocatedJointFrameRead a f) =
      largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P C) p f := by
  rw [allocatedActualPrimeBad_depth, allocatedActualPrimeBad_depth]
  exact allocatedJointFrameRead_badDepth inactive spatial kernel block P A C p a f

theorem allocatedActualPrimeBad_product_jointFrame (A : ℕ → ℕ) (a : X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    (∏ p ∈ P, p ^ largestTestedBadDepth A
      (allocatedActualPrimeBad inactive spatial kernel block P C) p (allocatedJointFrameRead a f)) =
    ∏ p ∈ P, p ^ largestTestedBadDepth A
      (allocatedActualPrimeBad inactive spatial kernel block P C) p f := by
  simp only [allocatedActualPrimeBad_depth_jointFrame]

end BadDepth

section RecoveredSample
variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {c : ∀ j, U j} {a : X → ℤ}
variable {sample : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I E n B → ℤ}

theorem AllocatedCenteredRecoveredSampleReadAt.jointFrame
    (h : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center c a sample read)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedReadNoise (allocatedJointFrameRead a (read z)) =
        (fun t => jointIntegerFrame (a,z) t.1 t.2) ∧
    allocatedReadDeck (allocatedJointFrameRead a (read z)) = allocatedReadDeck (read z) ∧
    allocatedReadProjection (allocatedJointFrameRead a (read z)) = allocatedReadProjection (read z) ∧
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center a z ≠ 0 →
      canonicalCoefficientSample U b hb o (sample z) =
        affineSampleCoefficientTorus U (fun j => subtractConstant (c j).val (poly j))
          (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hm j))
          (fun k x => (jointIntegerFrame (a,z) k x : ℝ)) ∧
      (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (sample z j) ∧
        mixedArraySupported (allocatedLayerCenters B U b S j)
          (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample z j)) ∧
      (∀ d, |coefficientSamplerAmbientPoint U b o (sample z) d| < 1/2) ∧
      (∀ (j : Fin m) (i : Fin (n j))
        (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
        allocatedReadProjection (allocatedJointFrameRead a (read z)) ⟨j, Sum.inr i⟩ e =
          (sample z j).2 i e)) := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · rw [allocatedJointFrameRead_noise, (h z).1]
  · intro hz
    have hs := (h z).2 hz
    refine ⟨?_, hs.2.1, hs.2.2.1, hs.2.2.2.1⟩
    exact hs.1.trans (affineSampleCoefficientTorus_joint_frame U
      (fun j => subtractConstant (c j).val (poly j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hm j)) a z)

end RecoveredSample
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {c : ∀ j, U j} {a : X → ℤ}
variable {sample : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I E n B → ℤ}

theorem AllocatedCenteredRecoveredSampleReadAt.centeredJointFrame_read
    (h : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center c a sample read)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedReplaceReadNoise B z (allocatedJointFrameRead a (read z)) = read z := by
  funext i
  rcases i with i | i
  · exact (congrFun (h z).1 i).symm
  · rfl

theorem AllocatedCenteredRecoveredSampleReadAt.centeredJointFrame_cover
    (h : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center c a sample read)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hz : allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center a z ≠ 0)
    (q : ℕ) [NeZero q]
    (event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop) :
    coefficientDeckChartEvent U bW b hb o q event
      (affineCoefficientCoverSample U (fun j => subtractConstant (c j).val (poly j))
        (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hm j)) q
        (fun k x => (jointIntegerFrame (a,z) k x : ℝ))) ↔
      event (allocatedReadCoefficientChartResidues
        (fun i => (allocatedReplaceReadNoise B z
          (allocatedJointFrameRead a (read z)) i : ZMod q))) := by
  have hs := ((h z).2 hz).2.2.2.2.1 q (NeZero.pos q) event
  rw [h.centeredJointFrame_read B U bW b hb o S hR hσ poly hm
    inactive spatial kernel block C z]
  change coefficientDeckChartEvent U bW b hb o q event
    (affineCoefficientCoverSample U
      (fun j => translate (fun x => (a x : ℝ)) (subtractConstant (c j).val (poly j)))
      (fun j => coefficients_translate_mem (U j) (fun x => (a x : ℝ))
        (subtractConstant (c j).val (poly j))
        (coefficients_subtractConstant_mem (U j) (c j) (poly j) (hm j))) q
      (fun k x => (z (k,x) : ℝ))) ↔
    event (allocatedReadCoefficientChartResidues (fun i => (read z i : ZMod q))) at hs
  rw [affineCoefficientCoverSample_joint_frame] at hs
  exact hs

theorem AllocatedCenteredRecoveredSampleReadAt.centeredJointFrame_recovery
    (h : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center c a sample read)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hz : allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center a z ≠ 0) :
    allocatedReadNoise (allocatedReplaceReadNoise B z
      (allocatedJointFrameRead a (read z))) = z ∧
    canonicalCoefficientSample U b hb o (sample z) =
      affineSampleCoefficientTorus U (fun j => subtractConstant (c j).val (poly j))
        (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hm j))
        (fun k x => (jointIntegerFrame (a,z) k x : ℝ)) ∧
    (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (sample z j) ∧
      mixedArraySupported (allocatedLayerCenters B U b S j)
        (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j)
        (sample z j)) ∧
    (∀ d, |coefficientSamplerAmbientPoint U b o (sample z) d| < 1/2) ∧
    (∀ (j : Fin m) (i : Fin (n j))
      (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
      allocatedReadProjection (allocatedReplaceReadNoise B z
        (allocatedJointFrameRead a (read z))) ⟨j, Sum.inr i⟩ e = (sample z j).2 i e) ∧
    (∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
      ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
        coefficientDeckChartEvent U bW b hb o q event
          (affineCoefficientCoverSample U (fun j => subtractConstant (c j).val (poly j))
            (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hm j)) q
            (fun k x => (jointIntegerFrame (a,z) k x : ℝ))) ↔
          event (allocatedReadCoefficientChartResidues
            (fun i => (allocatedReplaceReadNoise B z
              (allocatedJointFrameRead a (read z)) i : ZMod q)))) := by
  have hs := (h.jointFrame B U bW b hb o S hR hσ poly hm
    inactive spatial kernel block C z).2.2.2 hz
  refine ⟨rfl, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, ?_⟩
  intro q hq
  let : NeZero q := ⟨hq.ne'⟩
  exact h.centeredJointFrame_cover B U bW b hb o S hR hσ poly hm
    inactive spatial kernel block C z hz q

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (rankC : ℝ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (c : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ∀ j, U j)
variable (hc : Measurable c)
variable (sample : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
  (Option (LayerSamplerVariables G I n B) × X → ℤ) → CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (read : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
  (Option (LayerSamplerVariables G I n B) × X → ℤ) → AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hread : ∀ center a, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
  inactive spatial kernel block rankC center (c center) a (sample center a) (read center a))
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
variable (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (hD : ∀ center, 0 < selectedJointDensityMass bases stride cells width
  (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center))
local notation "jointLaw" => (fun center => selectedJointFiniteLaw bases hbases stride cells width hwidth hZ
  (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)
  (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm center) (hD center))
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U)) [IsProbabilityMeasure μ]
variable (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (cutoff : ℕ)

omit [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)] in
theorem allocatedCentered_joint_weight_measurable : ∀ x, Measurable (fun center => (jointLaw center).weight x) :=
    selectedJointFiniteLaw_weight_measurable bases hbases stride cells width hwidth hZ
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm)
      (allocatedCenteredJointDensity_measurable_center B U b hb o hR hσ S poly hm)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm) hD

omit [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
  [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
  [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)] in
include hread in
theorem allocatedCentered_joint_positive_rankCertificate : ∀ center (x : bases × rectangularWeightIndices 0 width 1),
      0 < (jointLaw center).weight x →
      AllocatedPhysicalRankReadCertificate B U bW b hb o
        (allocatedCenteredConditionalPolynomial U poly (c center) x.1.val)
        (allocatedCenteredConditionalPolynomial_mem U poly hm (c center) x.1.val)
        inactive spatial kernel block rankC x.2.val (read center x.1.val x.2.val) := by
    intro center x hx
    have hdensity := (selectedJointFiniteLaw_support bases hbases stride cells width hwidth hZ
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm center) (hD center) x hx).2.ne'
    exact ((hread center x.1.val x.2.val).2 hdensity).2.2.2.2.2

include hc hread in

theorem exists_allocatedCentered_measurable_unframed_bad_tail
    {ε : ℝ} (hbound : (centeredFiniteProbabilityMeasure μ jointLaw).real
      {z | cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (allocatedActualPrimeBad inactive spatial kernel block P rankC) p
        (read z.1 z.2.1.val z.2.2.val)} ≤ ε) :
    ∃ bad : Set (CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 width 1)),
      MeasurableSet bad ∧ (centeredFiniteProbabilityMeasure μ jointLaw).real bad ≤ ε ∧
      ∀ center x, 0 < (jointLaw center).weight x →
        (cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
          (allocatedActualPrimeBad inactive spatial kernel block P rankC) p
          (read center x.1.val x.2.val) ↔ (center,x) ∈ bad) := by
  have hweight := allocatedCentered_joint_weight_measurable B U b hb o S hR hσ poly hm
    stride cells width hwidth hZ bases hbases hD
  have hcertificate := allocatedCentered_joint_positive_rankCertificate B U bW b hb o S hR hσ poly hm
    inactive spatial kernel block rankC c sample read hread stride cells width hwidth hZ bases hbases hD
  obtain ⟨bad, hbad, hmassbad, heq, _⟩ := exists_allocatedCentered_badProduct_measurable_tail
    (C := CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (Ω := bases × rectangularWeightIndices 0 width 1) B U bW b hb o poly hm inactive spatial kernel block rankC c hc
    (fun x => x.1.val) (fun x => x.2.val) jointLaw
    (fun center x => read center x.1.val x.2.val) hcertificate P A cutoff μ hweight hbound
  exact ⟨bad, hbad, hmassbad, heq⟩

include hc hread in

theorem exists_allocatedCentered_measurable_framed_bad_tail
    {ε : ℝ} (hbound : (centeredFiniteProbabilityMeasure μ jointLaw).real
      {z | cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (allocatedActualPrimeBad inactive spatial kernel block P rankC) p
        (read z.1 z.2.1.val z.2.2.val)} ≤ ε) :
    ∃ bad : Set (CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 width 1)),
      MeasurableSet bad ∧ (centeredFiniteProbabilityMeasure μ jointLaw).real bad ≤ ε ∧
      (∀ center x, 0 < (jointLaw center).weight x →
        ((center,x) ∈ bad ↔ cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
          (allocatedActualPrimeBad inactive spatial kernel block P rankC) p
          (allocatedJointFrameRead x.1.val (read center x.1.val x.2.val)))) ∧
      ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ jointLaw,
        z ∈ bad ↔ cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
          (allocatedActualPrimeBad inactive spatial kernel block P rankC) p
          (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val)) := by
  have hweight := allocatedCentered_joint_weight_measurable B U b hb o S hR hσ poly hm
    stride cells width hwidth hZ bases hbases hD
  obtain ⟨bad, hbad, hmassbad, heq⟩ := exists_allocatedCentered_measurable_unframed_bad_tail
    B U bW b hb o S hR hσ poly hm inactive spatial kernel block rankC c hc sample read hread
    stride cells width hwidth hZ bases hbases hD μ P A cutoff hbound
  have hpositive : ∀ center x, 0 < (jointLaw center).weight x →
      ((center,x) ∈ bad ↔ cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (allocatedActualPrimeBad inactive spatial kernel block P rankC) p
        (allocatedJointFrameRead x.1.val (read center x.1.val x.2.val))) := by
    intro center x hx
    rw [allocatedActualPrimeBad_product_jointFrame]
    exact (heq center x hx).symm
  refine ⟨bad, hbad, hmassbad, hpositive, ?_⟩
  exact (centeredFiniteProbabilityMeasure_ae_positive_weight μ jointLaw hweight).mono
    (fun z hz => hpositive z.1 z.2 hz)

end Erdos3.VectorPolynomial

end

end OAI
