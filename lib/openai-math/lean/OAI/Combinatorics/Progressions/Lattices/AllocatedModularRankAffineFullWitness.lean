import OAI.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineProbability
import OAI.Combinatorics.Progressions.Linear.AllocatedModularRankActualRefreshBad
import OAI.Combinatorics.Progressions.Probability.MixedSelectedCoefficientProbability

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

theorem allocatedCongruenceIntegerSelectedCoefficients_read
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedCongruenceIntegerSelectedCoefficients inactive
      (allocatedReadNoise f) (allocatedReadDeck f)
      (fun j a => allocatedReadProjection f ⟨j, a.val⟩) spatial kernel block =
      f ∘ allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block := by
  funext s
  rcases s with ⟨j, (x | i | a), l⟩ <;> rfl

theorem allocatedCongruenceIntegerSelectedCoefficients_refresh
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (c : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ) :
    let refreshed := Function.extend
      (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block) c f
    allocatedCongruenceIntegerSelectedCoefficients inactive
      (allocatedReadNoise refreshed) (allocatedReadDeck refreshed)
      (fun j a => allocatedReadProjection refreshed ⟨j, a.val⟩) spatial kernel block = c := by
  dsimp only
  rw [allocatedCongruenceIntegerSelectedCoefficients_read]
  funext s
  exact (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block).injective.extend_apply
    c f s

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

def allocatedResidueModulusBad
    (inactive : LayerSamplerAxis I n → Prop) (C : ℝ) (M : ℕ) [NeZero M]
    (f : AllocatedActualCoefficientIndex G X I E n B → ZMod M) : Prop :=
  ∃ v : LayerSamplerVariables G I n B → ZMod M, ∃ j : Fin m,
    ∃ w : AllocatedCongruenceRankOutput X E inactive j → ZMod M,
      (∃ o, IsUnit (w o)) ∧ (M : ℝ) ^ (-C) <
        (𝔼 u : Fin j.val → LayerSamplerLongVariables inactive G B → ZMod M,
          if polynomialLinearRow (polynomialIterDifference j.val
            (∑ o, w o • allocatedOriginalTaggedTop inactive j
              (allocatedReadNoise f) (allocatedReadDeck f)
              (fun a => allocatedReadProjection f ⟨j,a.val⟩) v
              (allocatedCongruenceOutputEmbedding inactive j o)) u) = 0 then 1 else 0)

def allocatedActualModulusBad
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (M : ℕ) [NeZero M]
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) : Prop :=
  allocatedCongruenceModulusBad inactive (allocatedReadNoise f) (allocatedReadDeck f)
    (fun j a => allocatedReadProjection f ⟨j,a.val⟩) spatial kernel block C M
    (fun z => (allocatedCongruenceIntegerSelectedCoefficients inactive
      (allocatedReadNoise f) (allocatedReadDeck f)
      (fun j a => allocatedReadProjection f ⟨j,a.val⟩) spatial kernel block z : ZMod M))

theorem allocatedActualModulusBad_eq_residue
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (M : ℕ) [NeZero M]
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedActualModulusBad inactive spatial kernel block C M f =
      allocatedResidueModulusBad inactive C M (fun i => (f i : ZMod M)) := by
  unfold allocatedActualModulusBad allocatedCongruenceModulusBad
    allocatedCongruenceRankFailureProbability allocatedResidueModulusBad
  simp only [allocatedCongruenceIntegerSelectedCoefficients_reduce,
    allocatedCongruenceRankPolynomial_original]
  rfl

theorem allocatedActualModulusBad_congr_residue
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (M : ℕ) [NeZero M]
    (f g : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hfg : ∀ i, (f i : ZMod M) = (g i : ZMod M)) :
    allocatedActualModulusBad inactive spatial kernel block C M f ↔
      allocatedActualModulusBad inactive spatial kernel block C M g := by
  rw [allocatedActualModulusBad_eq_residue, allocatedActualModulusBad_eq_residue]
  exact (congrArg (allocatedResidueModulusBad inactive C M) (funext hfg)).to_iff

def allocatedResiduePrimePowerWitness
    (inactive : LayerSamplerAxis I n → Prop) (C : ℝ)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (fM : AllocatedActualCoefficientIndex G X I E n B → ZMod M) : Prop :=
  ∀ p : P, allocatedResidueModulusBad inactive C (p.val ^ A p.val)
    (fun i => ZMod.castHom (hdiv p) (ZMod (p.val ^ A p.val)) (fM i))

theorem allocatedResiduePrimePowerWitness_iff_actual
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedResiduePrimePowerWitness inactive C P A M hdiv (fun i => (f i : ZMod M)) ↔
      ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val) f := by
  unfold allocatedResiduePrimePowerWitness
  apply forall_congr'
  intro p
  rw [allocatedActualModulusBad_eq_residue]
  have hcast : (fun i => ZMod.castHom (hdiv p) (ZMod (p.val ^ A p.val)) (f i : ZMod M)) =
      (fun i => (f i : ZMod (p.val ^ A p.val))) := by
    funext i
    exact map_intCast _ _
  rw [hcast]

omit [Fintype X] [∀ j, Fintype (E j)] in

theorem allocatedOriginalCongruenceTop_congr_outputs
    (inactive : LayerSamplerAxis I n → Prop) (M : ℕ)
    (f g : AllocatedActualCoefficientIndex G X I E n B → ZMod M)
    (hnoise : allocatedReadNoise f = allocatedReadNoise g)
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
  · simp only [allocatedCongruenceOutputEmbedding_spatial, allocatedOriginalTaggedTop, hnoise]
  · simp only [allocatedCongruenceOutputEmbedding_deck, allocatedOriginalTaggedTop, hdeck]
  · simp only [allocatedCongruenceOutputEmbedding_integer, allocatedOriginalTaggedTop, hinteger]

theorem allocatedResidueModulusBad_congr_outputs
    (inactive : LayerSamplerAxis I n → Prop) (C : ℝ) (M : ℕ) [NeZero M]
    (f g : AllocatedActualCoefficientIndex G X I E n B → ZMod M)
    (hnoise : allocatedReadNoise f = allocatedReadNoise g)
    (hdeck : allocatedReadDeck f = allocatedReadDeck g)
    (hinteger : ∀ (j : Fin m) (i : Fin (n j)),
      allocatedReadProjection f ⟨j,Sum.inr i⟩ = allocatedReadProjection g ⟨j,Sum.inr i⟩) :
    allocatedResidueModulusBad inactive C M f = allocatedResidueModulusBad inactive C M g := by
  unfold allocatedResidueModulusBad
  simp only [allocatedOriginalCongruenceTop_congr_outputs inactive M f g hnoise hdeck hinteger]

theorem allocatedResiduePrimePowerWitness_congr_outputs
    (inactive : LayerSamplerAxis I n → Prop) (C : ℝ)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (f g : AllocatedActualCoefficientIndex G X I E n B → ZMod M)
    (hnoise : allocatedReadNoise f = allocatedReadNoise g)
    (hdeck : allocatedReadDeck f = allocatedReadDeck g)
    (hinteger : ∀ (j : Fin m) (i : Fin (n j)),
      allocatedReadProjection f ⟨j,Sum.inr i⟩ = allocatedReadProjection g ⟨j,Sum.inr i⟩) :
    allocatedResiduePrimePowerWitness inactive C P A M hdiv f =
      allocatedResiduePrimePowerWitness inactive C P A M hdiv g := by
  unfold allocatedResiduePrimePowerWitness
  apply propext
  apply forall_congr'
  intro p
  apply Eq.to_iff
  apply allocatedResidueModulusBad_congr_outputs
  · funext q
    exact congrArg (ZMod.castHom (hdiv p) (ZMod (p.val ^ A p.val))) (congrFun hnoise q)
  · funext j q i
    exact congrArg (ZMod.castHom (hdiv p) (ZMod (p.val ^ A p.val)))
      (congrFun (congrFun (congrFun hdeck j) q) i)
  · intro j i
    funext q
    exact congrArg (ZMod.castHom (hdiv p) (ZMod (p.val ^ A p.val))) (congrFun (hinteger j i) q)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]
variable (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ)

def allocatedActualPrimeBad (p a : ℕ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) : Prop :=
  ∃ hp : p ∈ P, letI : NeZero p := inferInstanceAs (NeZero (⟨p, hp⟩ : P).val)
    allocatedActualModulusBad inactive spatial kernel block C (p ^ a) f

theorem allocatedActualPrimeBad_iff_modulusBad (p : P) (a : ℕ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedActualPrimeBad inactive spatial kernel block P C p.val a f ↔
      allocatedActualModulusBad inactive spatial kernel block C (p.val ^ a) f := by
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨p.property, h⟩

theorem allocatedActualPrimeBad_eq_rankBad (p a : ℕ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedActualPrimeBad inactive spatial kernel block P C p a f =
      allocatedCongruenceRankBad inactive (allocatedReadNoise f) (allocatedReadDeck f)
        (fun j a => allocatedReadProjection f ⟨j, a.val⟩) spatial kernel block P C p a
        (allocatedCongruenceIntegerSelectedCoefficients inactive
          (allocatedReadNoise f) (allocatedReadDeck f)
          (fun j a => allocatedReadProjection f ⟨j, a.val⟩) spatial kernel block) := rfl

theorem allocatedActualPrimeBad_false_of_notMem {p : ℕ} (hp : p ∉ P) (a : ℕ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    ¬ allocatedActualPrimeBad inactive spatial kernel block P C p a f := by
  rintro ⟨h, _⟩
  exact hp h

theorem allocatedActualPrimeBad_depth (A : ℕ → ℕ) (p : ℕ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P C) p f =
      allocatedCongruenceBadDepth inactive (allocatedReadNoise f) (allocatedReadDeck f)
        (fun j a => allocatedReadProjection f ⟨j, a.val⟩) spatial kernel block P A C p := by
  unfold allocatedCongruenceBadDepth largestTestedBadDepth
  apply congrArg (fun t : Finset ℕ => t.sup id)
  apply Finset.filter_congr
  intro a _
  exact (allocatedActualPrimeBad_eq_rankBad inactive spatial kernel block P C p a f).to_iff

theorem allocatedActualPrimeBad_prescribedDeep_eq (cutoff : ℕ → ℕ) (p a : ℕ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    prescribedDeepBad cutoff (allocatedActualPrimeBad inactive spatial kernel block P C) p a f =
      prescribedDeepBad cutoff
        (allocatedCongruenceRankBad inactive (allocatedReadNoise f) (allocatedReadDeck f)
          (fun j a => allocatedReadProjection f ⟨j, a.val⟩) spatial kernel block P C) p a
        (allocatedCongruenceIntegerSelectedCoefficients inactive
          (allocatedReadNoise f) (allocatedReadDeck f)
          (fun j a => allocatedReadProjection f ⟨j, a.val⟩) spatial kernel block) := rfl

theorem allocatedActualPrimeBad_deep_depth (A cutoff : ℕ → ℕ) (p : ℕ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    largestTestedBadDepth A
      (prescribedDeepBad cutoff (allocatedActualPrimeBad inactive spatial kernel block P C)) p f =
      largestTestedBadDepth A
        (prescribedDeepBad cutoff
          (allocatedCongruenceRankBad inactive (allocatedReadNoise f) (allocatedReadDeck f)
            (fun j a => allocatedReadProjection f ⟨j, a.val⟩) spatial kernel block P C)) p
        (allocatedCongruenceIntegerSelectedCoefficients inactive
          (allocatedReadNoise f) (allocatedReadDeck f)
          (fun j a => allocatedReadProjection f ⟨j, a.val⟩) spatial kernel block) := by
  unfold largestTestedBadDepth
  apply congrArg (fun t : Finset ℕ => t.sup id)
  apply Finset.filter_congr
  intro a _
  exact (allocatedActualPrimeBad_prescribedDeep_eq inactive spatial kernel block P C cutoff p a f).to_iff

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights

private theorem affineWitness_uniform_le (Y : Type*) (f g : Fintype Y)
    [Nonempty Y] (F : Y → Prop) (r : ℝ)
    (h : @eventProbability Y f (@uniform Y f _) F ≤ r) :
    @eventProbability Y g (@uniform Y g _) F ≤ r := by
  cases Subsingleton.elim f g
  exact h

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable local instance affineWitnessSmoothIndexFintype (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedSmoothRankCoefficientIndex X inactive L) := inferInstance
noncomputable local instance affineWitnessDeckIndexFintype :
    Fintype (AllocatedDeckRankCoefficientIndex E L) := inferInstance
noncomputable local instance affineWitnessDeckIndexDecidableEq :
    DecidableEq (AllocatedDeckRankCoefficientIndex E L) := Classical.decEq _
noncomputable local instance affineWitnessCongruenceIndexFintype (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedCongruenceCoefficientIndex X E inactive L) := inferInstance
noncomputable local instance affineWitnessCongruenceIndexDecidableEq (inactive : LayerSamplerAxis I n → Prop) :
    DecidableEq (AllocatedCongruenceCoefficientIndex X E inactive L) := Classical.decEq _

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

def allocatedAffineMixedModulusBad (stride : X → ℕ)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    (C : ℝ) (M : ℕ) [NeZero M]
    (x : (AllocatedSmoothRankCoefficientIndex X inactive L ⊕
      AllocatedDeckRankCoefficientIndex E L) → ZMod M) : Prop :=
  allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C M
    (allocatedCongruenceAffineCoefficients inactive (fun x => (stride x : ZMod M))
      (fun j => (offset j : ZMod M)) (allocatedMixedCoefficientEquiv inactive L (ZMod M) x))

theorem allocatedAffineMixedModulusBad_probability {p a D : ℕ} [NeZero p]
    (hm : 0 < m) (hp : p.Prime) (ha : 0 < a)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hdeep : ∀ x, 2 * (stride x).factorization p ≤ a)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    {C : ℝ} (hC : 0 ≤ C)
    (hlarge : modularCoefficientPrimeThreshold m ≤ p ^ a)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L) :
    (uniform ((AllocatedSmoothRankCoefficientIndex X inactive L ⊕
      AllocatedDeckRankCoefficientIndex E L) → ZMod (p ^ a))).eventProbability
        (allocatedAffineMixedModulusBad inactive noise r projection spatial kernel block
          stride offset C (p ^ a)) ≤ 1 / ((p ^ a : ℕ) : ℝ) ^ 10 := by
  have he := allocatedMixedCoefficient_uniform_event (X := X) (E := E) inactive L (p ^ a)
    (fun c => allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C (p ^ a)
      (allocatedCongruenceAffineCoefficients inactive (fun x => (stride x : ZMod (p ^ a)))
        (fun j => (offset j : ZMod (p ^ a))) c))
  have hs := allocatedCongruenceModulusBad_affine_probability inactive noise r projection
    spatial kernel block hm hp ha hD stride hstride hdeep
    (fun j => (offset j : ZMod (p ^ a))) hC hlarge hL
  have hb := he.le.trans (affineWitness_uniform_le _ _ _ _ _ hs)
  exact affineWitness_uniform_le _ _ _ _ _ hb

theorem allocatedAffineMixed_primePower_event {N D : ℕ} [NeZero N]
    (hm : 0 < m) (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    (center width : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ)
    (hwidth : ∀ j, 0 < width j) (hZ : 0 < shiftedSmoothProductMass center width)
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hpositive : ∀ p ∈ P, 0 < A p)
    (hdeep : ∀ p ∈ P, ∀ x, 2 * (stride x).factorization p ≤ A p)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hthreshold : ∀ p ∈ P, modularCoefficientPrimeThreshold m ≤ p ^ A p)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : P, p.val ^ A p.val) ≤ width j) :
    ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
      (uniform (AllocatedDeckRankCoefficientIndex E L → ZMod N))).eventProbability
      (fun x => ∀ p : P, allocatedCongruenceModulusBad inactive noise r projection spatial kernel block
        C (p.val ^ A p.val) (fun j =>
          (allocatedMixedAffineSelectedValues inactive (fun x => (stride x : ℤ)) offset
            x.1.val x.2 j : ZMod (p.val ^ A p.val)))) ≤
      1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) *
          (∏ p : P, p.val ^ A p.val) / width j := by
  have h := mixedSmoothUniform_primePower_event (N := N) center width hwidth hZ P A
    hprime hcover
    (fun p => allocatedAffineMixedModulusBad inactive noise r projection spatial kernel block
      stride offset C (p.val ^ A p.val))
    (fun p => by
      have ht := allocatedAffineMixedModulusBad_probability inactive noise r projection spatial kernel block
        hm (hprime p p.property) (hpositive p p.property) hD stride hstride (hdeep p p.property)
        offset hC (hthreshold p p.property) hL
      exact affineWitness_uniform_le _ _ _ _ _ ht)
    hlarge
  simpa only [allocatedAffineMixedModulusBad, allocatedMixedAffineSelectedValues_natCast] using h

theorem allocatedAffineMixedActual_primePower_event
    (fixed : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    {N D : ℕ} [NeZero N]
    (hm : 0 < m) (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    (center width : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ)
    (hwidth : ∀ j, 0 < width j) (hZ : 0 < shiftedSmoothProductMass center width)
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hpositive : ∀ p ∈ P, 0 < A p)
    (hdeep : ∀ p ∈ P, ∀ x, 2 * (stride x).factorization p ≤ A p)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hthreshold : ∀ p ∈ P, modularCoefficientPrimeThreshold m ≤ p ^ A p)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : P, p.val ^ A p.val) ≤ width j) :
    ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
      (uniform (AllocatedDeckRankCoefficientIndex E L → ZMod N))).eventProbability
      (fun x => ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
        (Function.extend (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block)
          (allocatedMixedAffineSelectedValues inactive (fun x => (stride x : ℤ)) offset x.1.val x.2) fixed)) ≤
      1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) *
          (∏ p : P, p.val ^ A p.val) / width j := by
  have h := allocatedAffineMixed_primePower_event inactive
    (allocatedReadNoise fixed) (allocatedReadDeck fixed)
    (fun j a => allocatedReadProjection fixed ⟨j,a.val⟩) spatial kernel block hm stride hstride offset
    center width hwidth hZ P A hprime hcover hpositive hdeep hD hC hL hthreshold hlarge
  simpa only [allocatedActualModulusBad, allocatedActualRefresh_modulusBad] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights
attribute [local irreducible] allocatedActualModulusBad allocatedMixedFullArray independentProductPMF

private theorem affine_decide_eq_classical (p : Prop) [d : Decidable p] :
    @decide p d = @decide p (Classical.propDecidable p) := by
  cases Subsingleton.elim d (Classical.propDecidable p)
  rfl

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable local instance affineFullWitnessSmoothFintype :
    Fintype (AllocatedFullSmoothCoefficientIndex G X I n B) := inferInstance
noncomputable local instance affineFullWitnessSmoothDecidableEq :
    DecidableEq (AllocatedFullSmoothCoefficientIndex G X I n B) := Classical.decEq _
noncomputable local instance affineFullWitnessSelectedSmoothDecidableEq (inactive : LayerSamplerAxis I n → Prop) :
    DecidableEq (AllocatedSmoothRankCoefficientIndex X inactive L) := Classical.decEq _
noncomputable local instance affineFullWitnessDeckFintype :
    Fintype (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := inferInstance
noncomputable local instance affineFullWitnessDeckDecidableEq :
    DecidableEq (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := Classical.decEq _
noncomputable local instance affineFullWitnessSelectedSmoothFintype (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedSmoothRankCoefficientIndex X inactive L) := inferInstance
noncomputable local instance affineFullWitnessSelectedDeckFintype :
    Fintype (AllocatedDeckRankCoefficientIndex E L) := inferInstance
noncomputable local instance affineFullWitnessSelectedDeckDecidableEq :
    DecidableEq (AllocatedDeckRankCoefficientIndex E L) := Classical.decEq _

theorem allocatedAffineProductMixed_primePower_event
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → ℤ)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (residue : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (laws : AllocatedFullSmoothCoefficientIndex G X I n B → PMF ℤ)
    {N D : ℕ} [NeZero N] (hm : 0 < m)
    (center width : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ)
    (hwidth : ∀ j, 0 < width j) (hZ : 0 < shiftedSmoothProductMass center width)
    (hcoordinate : ∀ i, laws (allocatedSmoothFullEmbedding inactive spatial block i) =
      shiftedSmoothCoefficientPMF (center i) (width i) (hwidth i)
        (shiftedSmoothProductMass_coordinate_pos center width hwidth hZ i))
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hpositive : ∀ p ∈ P, 0 < A p)
    (hdeep : ∀ p ∈ P, ∀ x, 2 * (stride x).factorization p ≤ A p)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hthreshold : ∀ p ∈ P, modularCoefficientPrimeThreshold m ≤ p ^ A p)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : P, p.val ^ A p.val) ≤ width j) :
    (((independentProductPMF laws).bind
      (fun x => (PMF.uniformOfFintype
        (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N)).map
        (fun deck => decide (∀ p : P,
          allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
            (allocatedMixedFullArray (allocatedFullSmoothAffine (fun x => (stride x : ℤ)) residue x)
            (fun i => (deck i).val) continuous))))) true).toReal ≤
      1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (∏ p : P, p.val ^ A p.val) / width j := by
  let e := allocatedSmoothFullEmbedding (X := X) inactive spatial block
  let d := allocatedDeckFullEmbedding (E := E) (I := I) (n := n) (B := B) kernel
  let bad : (AllocatedFullSmoothCoefficientIndex G X I n B → ℤ) →
      (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N) → Prop :=
    fun x deck => ∀ p : P,
    allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
      (allocatedMixedFullArray (allocatedFullSmoothAffine (fun x => (stride x : ℤ)) residue x)
            (fun i => (deck i).val) continuous)
  let δ : ℝ := 1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
    ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (∏ p : P, p.val ^ A p.val) / width j
  have hδ : 0 ≤ δ := add_nonneg (by positivity)
    (Finset.sum_nonneg (fun j _ => div_nonneg (by positivity) (hwidth _).le))
  have hconditional : ∀ (fixed : AllocatedFullSmoothCoefficientIndex G X I n B → ℤ)
      (fixedDeck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N),
      ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
        (uniform (AllocatedDeckRankCoefficientIndex E L → ZMod N))).eventProbability
        (fun z => bad (Function.extend e z.1.val fixed) (Function.extend d z.2 fixedDeck)) ≤ δ := by
    intro fixed fixedDeck
    have h := allocatedAffineMixedActual_primePower_event inactive spatial kernel block
      (allocatedMixedFullArray
        (allocatedFullSmoothAffine (fun x => (stride x : ℤ)) residue fixed)
        (fun i => (fixedDeck i).val) continuous) hm stride hstride
      (allocatedSelectedNoiseOffset inactive spatial residue)
      center width hwidth hZ P A hprime hcover hpositive hdeep hD hC hL hthreshold hlarge
    simpa only [e, d, bad, δ, allocatedMixedFullArray_affine_refresh_selected] using h
  simpa only [bad, δ, affine_decide_eq_classical] using
    independentProduct_uniform_smooth_selected_event_probability_le
      e d laws center width hwidth hZ hcoordinate N bad hδ hconditional

end Erdos3.VectorPolynomial

end

end OAI
