import OAI.Combinatorics.Progressions.Lattices.AllocatedPhysicalIntegerRankLaw
import OAI.Combinatorics.Progressions.Polynomial.AllocatedCenteredConditionalPolynomial

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
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
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)

def AllocatedPhysicalRankReadCertificate
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) : Prop :=
  ∀ (P : Finset ℕ) (hP : ∀ p : P, NeZero p.val), letI := hP
    ∀ (A : ℕ → ℕ) (M : ℕ) (hM : 0 < M), letI : NeZero M := ⟨hM.ne'⟩
      ∀ hdiv : ∀ p : P, p.val ^ A p.val ∣ M,
        coefficientDeckChartEvent U bW b hb o M
          (allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
            (fun v => (z v : ZMod M)))
          (affineCoefficientCoverSample U poly hm M (fun k x => (z (k,x) : ℝ))) ↔
        ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val) f

theorem allocatedPhysicalRankReadCertificate_of_event_read
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hnoise : allocatedReadNoise f = z)
    (hevent : ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
      ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
        coefficientDeckChartEvent U bW b hb o q event
          (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) ↔
        event (allocatedReadCoefficientChartResidues (fun i => (f i : ZMod q)))) :
    AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z f := by
  intro P hP
  let := hP
  intro A M hM
  let : NeZero M := ⟨hM.ne'⟩
  intro hdiv
  have he := hevent M hM (allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
    (fun v => (z v : ZMod M)))
  apply he.trans
  have hn : allocatedReadNoise (fun i => (f i : ZMod M)) = fun v => (z v : ZMod M) := by
    funext v
    change ((allocatedReadNoise f v : ℤ) : ZMod M) = _
    rw [hnoise]
  rw [← hn]
  exact allocatedChartResiduePrimePowerWitness_iff_actual inactive spatial kernel block C P A M hdiv f

theorem AllocatedPhysicalRankReadCertificate.modulusBad_congr
    {z : Option (LayerSamplerVariables G I n B) × X → ℤ}
    {f g : AllocatedActualCoefficientIndex G X I E n B → ℤ}
    (hf : AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z f)
    (hg : AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z g)
    (p a : ℕ) [NeZero p] :
    allocatedActualModulusBad inactive spatial kernel block C (p ^ a) f ↔
      allocatedActualModulusBad inactive spatial kernel block C (p ^ a) g := by
  let P : Finset ℕ := {p}
  have hP : ∀ q : P, NeZero q.val := by
    intro q
    have hq : q.val = p := Finset.mem_singleton.mp q.property
    rw [hq]
    infer_instance
  let := hP
  have hpa : 0 < p ^ a := pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) _
  let : NeZero (p ^ a) := ⟨hpa.ne'⟩
  have hdiv : ∀ q : P, q.val ^ (fun _ => a) q.val ∣ p ^ a := by
    intro q
    have hq : q.val = p := Finset.mem_singleton.mp q.property
    simp only [hq, dvd_refl]
  have he := (hf P hP (fun _ => a) (p ^ a) hpa hdiv).symm.trans
    (hg P hP (fun _ => a) (p ^ a) hpa hdiv)
  constructor
  · intro h
    apply (he.mp ?_) ⟨p, Finset.mem_singleton_self p⟩
    intro q
    obtain ⟨q, hq⟩ := q
    have hqp : q = p := Finset.mem_singleton.mp hq
    subst q
    exact h
  · intro h
    apply (he.mpr ?_) ⟨p, Finset.mem_singleton_self p⟩
    intro q
    obtain ⟨q, hq⟩ := q
    have hqp : q = p := Finset.mem_singleton.mp hq
    subst q
    exact h

theorem AllocatedPhysicalRankReadCertificate.primeBad_congr
    {z : Option (LayerSamplerVariables G I n B) × X → ℤ}
    {f g : AllocatedActualCoefficientIndex G X I E n B → ℤ}
    (hf : AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z f)
    (hg : AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z g)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (p : P) (a : ℕ) :
    allocatedActualPrimeBad inactive spatial kernel block P C p.val a f ↔
      allocatedActualPrimeBad inactive spatial kernel block P C p.val a g := by
  rw [allocatedActualPrimeBad_iff_modulusBad, allocatedActualPrimeBad_iff_modulusBad]
  exact hf.modulusBad_congr B U bW b hb o poly hm inactive spatial kernel block C hg p.val a

theorem selectedResidueDensityPMF_certifiedRead_badProduct_congr
    (modulus : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X modulus))
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells width z)
    (D : (Option (LayerSamplerVariables G I n B) × X → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus cells width D)
    (read other : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ z, D z ≠ 0 →
      AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z (read z))
    (hother : ∀ z, D z ≠ 0 →
      AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z (other z))
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (threshold : ℕ) :
    (∑' z, (selectedResidueDensityPMF modulus cells width hwidth hZ D hD0 hD z).toReal *
      (if threshold < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (fun p a z => allocatedActualPrimeBad inactive spatial kernel block P C p a (read z)) p z
      then (1 : ℝ) else 0)) =
    ∑' z, (selectedResidueDensityPMF modulus cells width hwidth hZ D hD0 hD z).toReal *
      (if threshold < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (fun p a z => allocatedActualPrimeBad inactive spatial kernel block P C p a (other z)) p z
      then (1 : ℝ) else 0) := by
  apply selectedResidueDensityPMF_badProduct_event_congr
  intro z hz p hp a _ _
  exact (hread z hz).primeBad_congr B U bW b hb o poly hm inactive spatial kernel block C
    (hother z hz) P ⟨p, hp⟩ a

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
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

theorem exists_allocatedPhysical_recovered_sample_read :
    ∃ (sample : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
      (read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ),
      ∀ z, allocatedReadNoise (read z) = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ≠ 0 →
        (canonicalCoefficientSample U b hb o (sample z) =
          affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ∧
        (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (sample z j) ∧
          mixedArraySupported (allocatedLayerCenters B U b S j)
            (allocatedLayerWidths B U b S j)
            (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample z j)) ∧
        (∀ (j : Fin m) (i : Fin (n j))
          (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
          allocatedReadProjection (read z) ⟨j, Sum.inr i⟩ e = (sample z j).2 i e) ∧
        ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
          ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
            coefficientDeckChartEvent U bW b hb o q event
              (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) ↔
            event (allocatedReadCoefficientChartResidues (fun i => (read z i : ZMod q)))) := by
  have hex (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
      ∃ (x : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
        (f : AllocatedActualCoefficientIndex G X I E n B → ℤ),
        allocatedReadNoise f = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ≠ 0 →
        (canonicalCoefficientSample U b hb o x =
          affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ∧
        (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (x j) ∧
          mixedArraySupported (allocatedLayerCenters B U b S j)
            (allocatedLayerWidths B U b S j)
            (allocatedLayerIntegerPMFs B U b hR hσ S j) (x j)) ∧
        (∀ (j : Fin m) (i : Fin (n j))
          (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
          allocatedReadProjection f ⟨j, Sum.inr i⟩ e = (x j).2 i e) ∧
        ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
          ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
            coefficientDeckChartEvent U bW b hb o q event
              (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) ↔
            event (allocatedReadCoefficientChartResidues (fun i => (f i : ZMod q)))) := by
    by_cases hz : allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) = 0
    · refine ⟨fun _ => (0, 0),
        allocatedMixedFullArray (Sum.elim z (fun _ => 0)) (fun _ => 0) (fun _ => 0), rfl, ?_⟩
      intro h
      exact (h hz).elim
    · obtain ⟨x, hx, _⟩ := canonicalCoefficientDensity_recover_unique U b hb o
        (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerPMFs B U b hR hσ S) hz
      have hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2 := by
        intro a
        exact (hx.2 a.1.1).1 a.1.2 a.2
      obtain ⟨f, hfnoise, hfint, hfevent⟩ := exists_allocatedCoefficient_integer_event_read
        U bW b hb o (affineSampleCoefficientArray U poly hm (fun k x => (z (k,x) : ℝ)))
        x hx.1 hsmall z
      exact ⟨x, f, hfnoise, fun _ => ⟨hx.1, hx.2, hfint, hfevent⟩⟩
  choose sample read hread using hex
  exact ⟨sample, read, hread⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
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

def allocatedReplaceReadNoise
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    AllocatedActualCoefficientIndex G X I E n B → ℤ :=
  Sum.elim z (fun i => read (.inr i))

omit [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in
@[simp] theorem allocatedReplaceReadNoise_noise
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedReadNoise (allocatedReplaceReadNoise B z read) = z := rfl

omit [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in
@[simp] theorem allocatedReplaceReadNoise_deck
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedReadDeck (allocatedReplaceReadNoise B z read) = allocatedReadDeck read := rfl

omit [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in
@[simp] theorem allocatedReplaceReadNoise_projection
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedReadProjection (allocatedReplaceReadNoise B z read) = allocatedReadProjection read := rfl

omit [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in
@[simp] theorem allocatedReplaceReadNoise_chart
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ) (q : ℕ) :
    allocatedReadCoefficientChartResidues
      (fun i => (allocatedReplaceReadNoise B z read i : ZMod q)) =
      allocatedReadCoefficientChartResidues (fun i => (read i : ZMod q)) := rfl

theorem exists_allocatedAnchored_recovered_sample_read (base : X → ℤ) :
    ∃ (sample : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
      (read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ),
      ∀ z, allocatedReadNoise (read z) = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U poly hm (fun k x => ((integerBaseTranslation base (k,x) + z (k,x) : ℤ) : ℝ))) ≠ 0 →
        (canonicalCoefficientSample U b hb o (sample z) =
          affineSampleCoefficientTorus U poly hm (fun k x => ((integerBaseTranslation base (k,x) + z (k,x) : ℤ) : ℝ))) ∧
        (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (sample z j) ∧
          mixedArraySupported (allocatedLayerCenters B U b S j)
            (allocatedLayerWidths B U b S j)
            (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample z j)) ∧
        (∀ (j : Fin m) (i : Fin (n j))
          (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
          allocatedReadProjection (read z) ⟨j, Sum.inr i⟩ e = (sample z j).2 i e) ∧
        ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
          ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
            coefficientDeckChartEvent U bW b hb o q event
              (affineCoefficientCoverSample U poly hm q (fun k x => ((integerBaseTranslation base (k,x) + z (k,x) : ℤ) : ℝ))) ↔
            event (allocatedReadCoefficientChartResidues (fun i => (read z i : ZMod q)))) := by
  obtain ⟨sample, read, hread⟩ := exists_allocatedPhysical_recovered_sample_read
    B U bW b hb o S hR hσ poly hm
  refine ⟨fun z => sample (integerBaseTranslation base + z),
    fun z => allocatedReplaceReadNoise B z (read (integerBaseTranslation base + z)), ?_⟩
  intro z
  refine ⟨rfl, ?_⟩
  intro hz
  exact (hread (integerBaseTranslation base + z)).2 hz

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
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

def AllocatedCenteredRecoveredSampleReadAt
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j) (a : X → ℤ)
    (sample : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I E n B → ℤ) : Prop :=
  ∀ z, allocatedReadNoise (read z) = z ∧
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center a z ≠ 0 →
      (canonicalCoefficientSample U b hb o (sample z) =
        affineSampleCoefficientTorus U (allocatedCenteredConditionalPolynomial U poly c a)
          (allocatedCenteredConditionalPolynomial_mem U poly hm c a)
          (fun k x => (z (k,x) : ℝ))) ∧
      (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (sample z j) ∧
        mixedArraySupported (allocatedLayerCenters B U b S j)
          (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample z j)) ∧
      (∀ d, |coefficientSamplerAmbientPoint U b o (sample z) d| < 1/2) ∧
      (∀ (j : Fin m) (i : Fin (n j))
        (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
        allocatedReadProjection (read z) ⟨j, Sum.inr i⟩ e = (sample z j).2 i e) ∧
      (∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
        ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
          coefficientDeckChartEvent U bW b hb o q event
            (affineCoefficientCoverSample U (allocatedCenteredConditionalPolynomial U poly c a)
              (allocatedCenteredConditionalPolynomial_mem U poly hm c a) q
              (fun k x => (z (k,x) : ℝ))) ↔
          event (allocatedReadCoefficientChartResidues (fun i => (read z i : ZMod q)))) ∧
      AllocatedPhysicalRankReadCertificate B U bW b hb o
        (allocatedCenteredConditionalPolynomial U poly c a)
        (allocatedCenteredConditionalPolynomial_mem U poly hm c a)
        inactive spatial kernel block C z (read z))

theorem exists_allocatedCentered_recovered_sample_read
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1)))) (a : X → ℤ) :
    ∃ sample read, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center c a sample read := by
  obtain ⟨sample, read, hread⟩ := exists_allocatedPhysical_recovered_sample_read B U bW b hb o S hR hσ
    (allocatedCenteredConditionalPolynomial U poly c a)
    (allocatedCenteredConditionalPolynomial_mem U poly hm c a)
  refine ⟨sample, read, ?_⟩
  intro z
  refine ⟨(hread z).1, ?_⟩
  intro hz
  have hdensity := allocatedCenteredConditionalPolynomial_density U poly hm c a B b hb o hR hσ S center hc z
  have hrec := (hread z).2 (hdensity.trans_ne hz)
  refine ⟨hrec.1, hrec.2.1, ?_, hrec.2.2.1, hrec.2.2.2, ?_⟩
  · intro d
    exact (hrec.2.1 d.1.1).1 d.1.2 d.2
  · exact allocatedPhysicalRankReadCertificate_of_event_read B U bW b hb o
      (allocatedCenteredConditionalPolynomial U poly c a)
      (allocatedCenteredConditionalPolynomial_mem U poly hm c a)
      inactive spatial kernel block C z (read z) (hread z).1 hrec.2.2.2

theorem exists_allocatedCentered_recovered_sample_reads
    (c : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ∀ j, U j)
    (hc : ∀ center, coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c center s.1)))) :
    ∃
      (sample : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
        (Option (LayerSamplerVariables G I n B) × X → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
      (read : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
        (Option (LayerSamplerVariables G I n B) × X → ℤ) →
          AllocatedActualCoefficientIndex G X I E n B → ℤ),
      ∀ center a, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
        inactive spatial kernel block C center (c center) a (sample center a) (read center a) := by
  choose sample read hread using fun center a =>
    exists_allocatedCentered_recovered_sample_read B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center (c center) (hc center) a
  exact ⟨sample, read, hread⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
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

noncomputable def allocatedAnchoredRecoveredSample (base : X → ℤ) :
    (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n :=
  Classical.choose (exists_allocatedAnchored_recovered_sample_read
    B U bW b hb o S hR hσ poly hm base)

noncomputable def allocatedAnchoredRecoveredRead (base : X → ℤ) :
    (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I E n B → ℤ :=
  Classical.choose (Classical.choose_spec (exists_allocatedAnchored_recovered_sample_read
    B U bW b hb o S hR hσ poly hm base))

theorem allocatedAnchoredRecoveredSource_spec (base : X → ℤ)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedReadNoise (allocatedAnchoredRecoveredRead B U bW b hb o S hR hσ poly hm base z) = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U poly hm (fun k x => ((integerBaseTranslation base (k,x) + z (k,x) : ℤ) : ℝ))) ≠ 0 →
        (canonicalCoefficientSample U b hb o (allocatedAnchoredRecoveredSample B U bW b hb o S hR hσ poly hm base z) =
          affineSampleCoefficientTorus U poly hm (fun k x => ((integerBaseTranslation base (k,x) + z (k,x) : ℤ) : ℝ))) ∧
        (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (allocatedAnchoredRecoveredSample B U bW b hb o S hR hσ poly hm base z j) ∧
          mixedArraySupported (allocatedLayerCenters B U b S j)
            (allocatedLayerWidths B U b S j)
            (allocatedLayerIntegerPMFs B U b hR hσ S j) (allocatedAnchoredRecoveredSample B U bW b hb o S hR hσ poly hm base z j)) ∧
        (∀ (j : Fin m) (i : Fin (n j))
          (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
          allocatedReadProjection (allocatedAnchoredRecoveredRead B U bW b hb o S hR hσ poly hm base z) ⟨j, Sum.inr i⟩ e = (allocatedAnchoredRecoveredSample B U bW b hb o S hR hσ poly hm base z j).2 i e) ∧
        ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
          ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
            coefficientDeckChartEvent U bW b hb o q event
              (affineCoefficientCoverSample U poly hm q (fun k x => ((integerBaseTranslation base (k,x) + z (k,x) : ℤ) : ℝ))) ↔
            event (allocatedReadCoefficientChartResidues (fun i => (allocatedAnchoredRecoveredRead B U bW b hb o S hR hσ poly hm base z i : ZMod q)))) :=
  (Classical.choose_spec (Classical.choose_spec (exists_allocatedAnchored_recovered_sample_read
    B U bW b hb o S hR hσ poly hm base))) z

end Erdos3.VectorPolynomial

end

end OAI
