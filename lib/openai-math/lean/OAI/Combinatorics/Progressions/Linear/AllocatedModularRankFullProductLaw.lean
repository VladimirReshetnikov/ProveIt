import Mathlib.Probability.Distributions.Uniform
import OAI.Combinatorics.Progressions.Estimates.FiniteMixedArrayRefresh
import OAI.Combinatorics.Progressions.Estimates.IndependentProductPMFSum
import OAI.Combinatorics.Progressions.Lattices.AllocatedCoefficientIntegerMarginal
import OAI.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

noncomputable def allocatedPrincipalRankCenter : ℝ :=
  (3 * principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card / 2) *
    ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))

noncomputable def allocatedPrincipalRankWidth : ℝ :=
  (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card / 2) *
    ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))

include hR in

theorem allocatedPrincipalRankWidth_pos : 0 < allocatedPrincipalRankWidth B U basis S j i := by
  apply mul_pos (div_pos (principalProfileSize_pos (hR j) _) (by norm_num))
  exact div_pos (by exact_mod_cast basisAxisScale_pos (basis j) i)
    (pow_pos (by exact_mod_cast S.positive) _)

include hR in

theorem allocatedPrincipalRankWidth_large
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i) :
    8 * (probabilityProfileLipschitz : ℝ) ≤ allocatedPrincipalRankWidth B U basis S j i :=
  integerAxisPrincipal_width (Nat.zero_lt_succ _) S.positive
    (principalProfileSize_pos (hR j) _) (S.gap j i hactive)

include hR in
theorem allocatedPrincipalRankMass_pos
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i) :
    0 < shiftedSmoothSampleSum (allocatedPrincipalRankCenter B U basis S j i)
      (allocatedPrincipalRankWidth B U basis S j i) :=
  shiftedSmoothSampleSum_pos _ (allocatedPrincipalRankWidth_large B U basis hR S j i hactive)

theorem allocatedLayerIntegerPMFs_principal_shiftedSmooth
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (b : B ⟨j, Sum.inr i⟩) :
    allocatedLayerIntegerPMFs B U basis hR hσ S j i
      (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) =
      shiftedSmoothCoefficientPMF (allocatedPrincipalRankCenter B U basis S j i)
        (allocatedPrincipalRankWidth B U basis S j i)
        (allocatedPrincipalRankWidth_pos B U basis hR S j i)
        (allocatedPrincipalRankMass_pos B U basis hR S j i hactive) := by
  have h := allocatedPrincipalNormalizedSource_law B U basis hR hσ S j i hactive b
  rw [allocatedPrincipalNormalizedSource, principalNormalizedSource_law] at h
  exact h.symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

abbrev AllocatedFullSmoothCoefficientIndex (G X : Type*) (I : Fin m → Type*)
    (n : Fin m → ℕ) (B : LayerSamplerAxis I n → Type*) :=
  (Option (LayerSamplerVariables G I n B) × X) ⊕
    (Σ j : Fin m, BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) × Fin (n j))

abbrev AllocatedFullContinuousCoefficientIndex (G : Type*) (I : Fin m → Type*)
    (n : Fin m → ℕ) (B : LayerSamplerAxis I n → Type*) :=
  Σ j : Fin m, BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) × I j

def allocatedFullCoefficientSplit :
    AllocatedActualCoefficientIndex G X I E n B ≃
      AllocatedFullSmoothCoefficientIndex G X I n B ⊕
        (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E ⊕
          AllocatedFullContinuousCoefficientIndex G I n B) where
  toFun t := match t with
    | .inl x => .inl (.inl x)
    | .inr (.inl d) => .inr (.inl d)
    | .inr (.inr ⟨⟨j,.inl i⟩,q⟩) => .inr (.inr ⟨j,q,i⟩)
    | .inr (.inr ⟨⟨j,.inr i⟩,q⟩) => .inl (.inr ⟨j,q,i⟩)
  invFun t := match t with
    | .inl (.inl x) => .inl x
    | .inr (.inl d) => .inr (.inl d)
    | .inr (.inr ⟨j,q,i⟩) => .inr (.inr ⟨⟨j,.inl i⟩,q⟩)
    | .inl (.inr ⟨j,q,i⟩) => .inr (.inr ⟨⟨j,.inr i⟩,q⟩)
  left_inv := by rintro (x | d | ⟨⟨j,(i | i)⟩,q⟩) <;> rfl
  right_inv := by rintro ((x | ⟨j,q,i⟩) | d | ⟨j,q,i⟩) <;> rfl

noncomputable def allocatedSmoothFullSlot
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩) :
    AllocatedSmoothRankCoefficientIndex X inactive L → AllocatedFullSmoothCoefficientIndex G X I n B
  | ⟨_j,.inl x,l⟩ => .inl (some (.inl (spatial l)),x.val)
  | ⟨j,.inr i,l⟩ => .inr ⟨j,
      principalCoefficientSlot (layerSamplerDegree I n) ⟨j,.inr i.val⟩
        (block j ⟨.inr i.val,i.property⟩ l), i.val⟩

theorem allocatedSmoothFullSlot_injective
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩) :
    Function.Injective (allocatedSmoothFullSlot (X := X) inactive spatial block) := by
  rintro ⟨j,(x | i),l⟩ ⟨k,(y | a),q⟩ he
  · have hjk : j = k := Fin.ext (x.property.trans y.property.symm)
    subst k
    have hp := Sum.inl.inj he
    have hl : l = q := spatial.injective
      (Sum.inl.inj (Option.some.inj (congrArg Prod.fst hp)))
    have hxy : x = y := Subtype.ext (congrArg Prod.snd hp)
    subst q
    subst y
    rfl
  · cases he
  · cases he
  · have hh := Sum.inr.inj he
    have hjk : j = k := congrArg Sigma.fst hh
    subst k
    have hp := eq_of_heq (Sigma.mk.inj hh).2
    have hia : i = a := Subtype.ext (congrArg Prod.snd hp)
    subst a
    have hblocks := principalCoefficientSlot_injective (G := G)
      (layerSamplerDegree I n) ⟨j,.inr i.val⟩ (Nat.zero_lt_succ _) (congrArg Prod.fst hp)
    have hl : l = q := (block j ⟨.inr i.val,i.property⟩).injective hblocks
    subst q
    rfl

noncomputable def allocatedSmoothFullEmbedding
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩) :
    AllocatedSmoothRankCoefficientIndex X inactive L ↪ AllocatedFullSmoothCoefficientIndex G X I n B :=
  ⟨allocatedSmoothFullSlot inactive spatial block, allocatedSmoothFullSlot_injective inactive spatial block⟩

noncomputable def allocatedDeckFullSlot (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G) :
    AllocatedDeckRankCoefficientIndex E L → CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E
  | ⟨j,e,l⟩ => ⟨j,kernelRankCoefficientSlot (layerSamplerDegree I n) (kernel j) l,e⟩

theorem allocatedDeckFullSlot_injective (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G) :
    Function.Injective (allocatedDeckFullSlot (I := I) (E := E) (n := n) (B := B) kernel) := by
  rintro ⟨j,e,l⟩ ⟨k,f,q⟩ he
  have hjk : j = k := congrArg Sigma.fst he
  subst k
  have hp := eq_of_heq (Sigma.mk.inj he).2
  have hl : l = q := kernelRankCoefficientSlot_injective
    (layerSamplerDegree I n) (kernel j) (Nat.zero_lt_succ _) (congrArg Prod.fst hp)
  have hef : e = f := congrArg Prod.snd hp
  subst q
  subst f
  rfl

noncomputable def allocatedDeckFullEmbedding (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G) :
    AllocatedDeckRankCoefficientIndex E L ↪ CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E :=
  ⟨allocatedDeckFullSlot kernel, allocatedDeckFullSlot_injective kernel⟩

def allocatedMixedFullArray {R : Type*}
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → R)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → R) :
    AllocatedActualCoefficientIndex G X I E n B → R :=
  Sum.elim smooth (Sum.elim deck continuous) ∘ allocatedFullCoefficientSplit

@[simp] theorem allocatedMixedFullArray_noise {R : Type*}
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → R)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → R) (x) :
    allocatedReadNoise (allocatedMixedFullArray smooth deck continuous) x = smooth (.inl x) := rfl

@[simp] theorem allocatedMixedFullArray_deck {R : Type*}
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → R)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → R) (j) (q) (e) :
    allocatedReadDeck (allocatedMixedFullArray smooth deck continuous) j q e = deck ⟨j,q,e⟩ := rfl

@[simp] theorem allocatedMixedFullArray_integer {R : Type*}
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → R)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → R) (j) (q) (i) :
    allocatedReadProjection (allocatedMixedFullArray smooth deck continuous) ⟨j,.inr i⟩ q =
      smooth (.inr ⟨j,q,i⟩) := rfl

@[simp] theorem allocatedMixedFullArray_continuous {R : Type*}
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → R)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → R) (j) (q) (i) :
    allocatedReadProjection (allocatedMixedFullArray smooth deck continuous) ⟨j,.inl i⟩ q =
      continuous ⟨j,q,i⟩ := rfl

def allocatedReadFullSmooth {R : Type*}
    (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    AllocatedFullSmoothCoefficientIndex G X I n B → R
  | .inl x => allocatedReadNoise f x
  | .inr ⟨j,q,i⟩ => allocatedReadProjection f ⟨j,.inr i⟩ q

def allocatedReadFullDeck {R : Type*}
    (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R :=
  fun ⟨j,q,e⟩ => allocatedReadDeck f j q e

def allocatedReadFullContinuous {R : Type*}
    (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    AllocatedFullContinuousCoefficientIndex G I n B → R :=
  fun ⟨j,q,i⟩ => allocatedReadProjection f ⟨j,.inl i⟩ q

theorem allocatedMixedFullArray_read {R : Type*}
    (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    allocatedMixedFullArray (allocatedReadFullSmooth f) (allocatedReadFullDeck f)
      (allocatedReadFullContinuous f) = f := by
  funext t
  rcases t with x | d | ⟨⟨j,(i | i)⟩,q⟩ <;> rfl

theorem allocatedMixedFullArray_reduce {N : ℕ} [NeZero N]
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → ℤ)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → ℤ) :
    (fun t => ((allocatedMixedFullArray (R := ℤ) smooth (fun k => (deck k).val) continuous t : ℤ) : ZMod N)) =
      allocatedMixedFullArray (fun k => (smooth k : ZMod N)) deck
        (fun k => (continuous k : ZMod N)) := by
  funext t
  rcases t with x | d | ⟨⟨j,(i | i)⟩,q⟩
  · rfl
  · change (((deck d).val : ℤ) : ZMod N) = deck d
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  · rfl
  · rfl

theorem allocatedFullCoefficientSplit_selected
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩)
    (s : AllocatedCongruenceCoefficientIndex X E inactive L) :
    allocatedFullCoefficientSplit (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block s) =
      mixedArrayEmbedding (allocatedSmoothFullEmbedding inactive spatial block)
        (allocatedDeckFullEmbedding kernel) (allocatedCongruenceCoefficientSplit inactive L s) := by
  rcases s with ⟨j,(x | e | i),l⟩ <;> rfl

theorem allocatedMixedFullArray_refresh {R : Type*}
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩)
    (selectedSmooth : AllocatedSmoothRankCoefficientIndex X inactive L → R)
    (selectedDeck : AllocatedDeckRankCoefficientIndex E L → R)
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → R)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → R) :
    allocatedMixedFullArray
      (Function.extend (allocatedSmoothFullEmbedding inactive spatial block) selectedSmooth smooth)
      (Function.extend (allocatedDeckFullEmbedding kernel) selectedDeck deck) continuous =
      Function.extend (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block)
        (Sum.elim selectedSmooth selectedDeck ∘ allocatedCongruenceCoefficientSplit inactive L)
        (allocatedMixedFullArray smooth deck continuous) :=
  mixedArray_extend_comp_equiv (allocatedSmoothFullEmbedding inactive spatial block)
    (allocatedDeckFullEmbedding kernel) (allocatedCongruenceCoefficientSplit inactive L)
    allocatedFullCoefficientSplit (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block)
    (allocatedFullCoefficientSplit_selected inactive spatial kernel block)
    selectedSmooth selectedDeck smooth deck continuous

theorem allocatedMixedFullArray_refresh_selected {N : ℕ}
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩)
    (selectedSmooth : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (selectedDeck : AllocatedDeckRankCoefficientIndex E L → ZMod N)
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → ℤ)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → ℤ) :
    allocatedMixedFullArray
      (Function.extend (allocatedSmoothFullEmbedding inactive spatial block) selectedSmooth smooth)
      (fun k => ((Function.extend (allocatedDeckFullEmbedding kernel) selectedDeck deck k).val : ℤ)) continuous =
      Function.extend (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block)
        (allocatedMixedSelectedValues inactive selectedSmooth selectedDeck)
        (allocatedMixedFullArray smooth (fun k => (deck k).val) continuous) := by
  have hdeck : (fun k => ((Function.extend (allocatedDeckFullEmbedding kernel) selectedDeck deck k).val : ℤ)) =
      Function.extend (allocatedDeckFullEmbedding kernel) (fun k => ((selectedDeck k).val : ℤ)) (fun k => ((deck k).val : ℤ)) := by
    funext k
    exact Function.apply_extend (fun z : ZMod N => (z.val : ℤ)) _ _ _
  rw [hdeck]
  exact allocatedMixedFullArray_refresh inactive spatial kernel block selectedSmooth
    (fun k => (selectedDeck k).val) smooth (fun k => (deck k).val) continuous

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable def allocatedFullSmoothScalarPMF
    (noisePMF : Option (LayerSamplerVariables G I n B) × X → PMF ℤ) :
    AllocatedFullSmoothCoefficientIndex G X I n B → PMF ℤ
  | .inl x => noisePMF x
  | .inr ⟨j,q,i⟩ => allocatedLayerIntegerPMFs B U basis hR hσ S j i q

variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩)
    (noiseCenter noiseWidth : Fin L → X → ℝ)

noncomputable def allocatedSelectedSmoothCenter : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ
  | ⟨_j,.inl x,l⟩ => noiseCenter l x.val
  | ⟨j,.inr i,_l⟩ => allocatedPrincipalRankCenter B U basis S j i.val

noncomputable def allocatedSelectedSmoothWidth : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ
  | ⟨_j,.inl x,l⟩ => noiseWidth l x.val
  | ⟨j,.inr i,_l⟩ => allocatedPrincipalRankWidth B U basis S j i.val

include hR in
theorem allocatedSelectedSmoothWidth_pos (hnoise : ∀ l x, 0 < noiseWidth l x)
    (a : AllocatedSmoothRankCoefficientIndex X inactive L) :
    0 < allocatedSelectedSmoothWidth B U basis S inactive noiseWidth a := by
  rcases a with ⟨j,(x | i),l⟩
  · exact hnoise l x.val
  · exact allocatedPrincipalRankWidth_pos B U basis hR S j i.val

include hR in
theorem allocatedSelectedSmoothMass_pos
    (hnoise : ∀ l x, 0 < shiftedSmoothSampleSum (noiseCenter l x) (noiseWidth l x))
    (hactive : ∀ j (i : AllocatedCongruenceIntegerAxis inactive j),
      S.value ^ (j.val + 1) < basisAxisScale (basis j) i.val)
    (a : AllocatedSmoothRankCoefficientIndex X inactive L) :
    0 < shiftedSmoothSampleSum (allocatedSelectedSmoothCenter B U basis S inactive noiseCenter a)
      (allocatedSelectedSmoothWidth B U basis S inactive noiseWidth a) := by
  rcases a with ⟨j,(x | i),l⟩
  · exact hnoise l x.val
  · exact allocatedPrincipalRankMass_pos B U basis hR S j i.val (hactive j i)

theorem allocatedFullSmoothScalarPMF_selected
    (noisePMF : Option (LayerSamplerVariables G I n B) × X → PMF ℤ)
    (hnoiseWidth : ∀ l x, 0 < noiseWidth l x)
    (hnoiseMass : ∀ l x, 0 < shiftedSmoothSampleSum (noiseCenter l x) (noiseWidth l x))
    (hnoise : ∀ l x, noisePMF (some (.inl (spatial l)), x) =
      shiftedSmoothCoefficientPMF (noiseCenter l x) (noiseWidth l x)
        (hnoiseWidth l x) (hnoiseMass l x))
    (hactive : ∀ j (i : AllocatedCongruenceIntegerAxis inactive j),
      S.value ^ (j.val + 1) < basisAxisScale (basis j) i.val)
    (a : AllocatedSmoothRankCoefficientIndex X inactive L) :
    allocatedFullSmoothScalarPMF B U basis hR hσ S noisePMF
      (allocatedSmoothFullEmbedding inactive spatial block a) =
      shiftedSmoothCoefficientPMF
        (allocatedSelectedSmoothCenter B U basis S inactive noiseCenter a)
        (allocatedSelectedSmoothWidth B U basis S inactive noiseWidth a)
        (allocatedSelectedSmoothWidth_pos B U basis hR S inactive noiseWidth hnoiseWidth a)
        (allocatedSelectedSmoothMass_pos B U basis hR S inactive noiseCenter noiseWidth
          hnoiseMass hactive a) := by
  rcases a with ⟨j,(x | i),l⟩
  · exact hnoise l x.val
  · exact allocatedLayerIntegerPMFs_principal_shiftedSmooth B U basis hR hσ S j i.val
      (hactive j i) (block j ⟨.inr i.val,i.property⟩ l)

theorem allocatedGridPrincipalRank_active (j : Fin m)
    (i : AllocatedCongruenceIntegerAxis (allocatedGridAxis (I := I) U basis S.value) j) :
    S.value ^ (j.val + 1) < basisAxisScale (basis j) i.val := by
  have hlarge : S.value ^ (layerTailDegree m + 1) < basisAxisScale (basis j) i.val :=
    Nat.lt_of_not_ge i.property
  exact (Nat.pow_le_pow_right S.positive
    ((layerDegree_le_tailDegree j).trans (Nat.le_succ _))).trans_lt hlarge

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

theorem allocatedFullSmoothProductPMF_factorization
    {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)
    (noisePMF : Option (LayerSamplerVariables G I n B) × X → PMF ℤ) :
    independentProductPMF (allocatedFullSmoothScalarPMF B U basis hR hσ S noisePMF) =
      (independentProductPMF noisePMF).bind (fun noise =>
        (allocatedCoefficientIntegerPMF B U basis hR hσ S).map (Sum.elim noise)) :=
  independentProductPMF_sum (allocatedFullSmoothScalarPMF B U basis hR hσ S noisePMF)

theorem coefficientDeckScalar_uniform_map {K : Type*} [Fintype K]
    {m : ℕ} {E : Fin m → Type*} [∀ j, Fintype (E j)]
    (N : ℕ) [NeZero N] :
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) E N)).map
      (coefficientDeckScalarEquiv (K := K) (E := E) (N := N)) =
      PMF.uniformOfFintype (CoefficientDeckScalarIndex K E → ZMod N) := by
  let e := coefficientDeckScalarEquiv (K := K) (E := E) (N := N)
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  change (PMF.uniformOfFintype _).map e (e x) = _
  rw [pmf_map_injective_at _ _ e.injective]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_congr e]

theorem coefficientDeckScalar_uniform_symm_map {K : Type*} [Fintype K]
    {m : ℕ} {E : Fin m → Type*} [∀ j, Fintype (E j)]
    (N : ℕ) [NeZero N] :
    (PMF.uniformOfFintype (CoefficientDeckScalarIndex K E → ZMod N)).map
      (coefficientDeckScalarEquiv (K := K) (E := E) (N := N)).symm =
      PMF.uniformOfFintype (CoefficientDeckResidues (K := K) E N) := by
  let e := (coefficientDeckScalarEquiv (K := K) (E := E) (N := N)).symm
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  change (PMF.uniformOfFintype _).map e (e x) = _
  rw [pmf_map_injective_at _ _ e.injective]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_congr e]

theorem coefficientDeckScalar_uniform_test {K : Type*}
    {m : ℕ} {E : Fin m → Type*} (N : ℕ)
    [Fintype (CoefficientDeckResidues (K := K) E N)]
    [Fintype (CoefficientDeckScalarIndex K E → ZMod N)]
    {Y : Type*} (test : (CoefficientDeckScalarIndex K E → ZMod N) → Y) :
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) E N)).map
      (fun deck => test (coefficientDeckScalarEquiv deck)) =
      (PMF.uniformOfFintype (CoefficientDeckScalarIndex K E → ZMod N)).map test := by
  let e := coefficientDeckScalarEquiv (K := K) (E := E) (N := N)
  have he : (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) E N)).map e =
      PMF.uniformOfFintype (CoefficientDeckScalarIndex K E → ZMod N) := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [pmf_map_injective_at _ _ e.injective]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_congr e]
  have h := congrArg (fun p => p.map test) he
  simpa only [PMF.map_comp, Function.comp_def] using h

end Erdos3.VectorPolynomial

end

end OAI
