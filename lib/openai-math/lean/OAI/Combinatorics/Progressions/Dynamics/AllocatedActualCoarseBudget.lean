import OAI.Combinatorics.Progressions.Estimates.AllocatedCommonCoarsePartition
import OAI.Combinatorics.Progressions.Estimates.AllocatedGenuineCoverFromRaw
import OAI.Combinatorics.Progressions.Estimates.PreparedUniformEarlyRadiusWithCutoff
import OAI.Combinatorics.Progressions.Polynomial.AllocatedCommonCoarseLogPolynomial

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

attribute [local instance 2000] fullBooleanRowSetFintype

section Logs

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)]

noncomputable def allocatedCommonSmoothingLog (dim : ℕ) (A T : ℝ≥0) (p P E : ℝ) : ℝ :=
  physicalIdealSmoothingLog (B := B)
    (O := fun i : LayerSamplerAxis I n => BoundedBooleanJet (Fin dim) (i.1.val + 1))
    (α := Fin dim) (layerSamplerDegree I n) A T
    (profileReferenceErrorLog P ((E + 1) + 1 + 4))
    (allocatedProfileGainLog m (allocatedComparisonDimension m p) P (allocatedSiteKernelMaskLog m P))

noncomputable def allocatedCommonTailLog (dim : ℕ) (A T : ℝ≥0) (p P E : ℝ) : ℝ :=
  physicalIdealTailLog (B := B)
    (O := fun i : LayerSamplerAxis I n => BoundedBooleanJet (Fin dim) (i.1.val + 1))
    (α := Fin dim) G (G × Option (Fin dim)) (layerSamplerDegree I n) A T m
    (profileReferenceErrorLog P ((E + 1) + 1 + 4))
    (allocatedProfileGainLog m (allocatedComparisonDimension m p) P (allocatedSiteKernelMaskLog m P))

theorem allocatedCommonSmoothingLog_nonneg (dim : ℕ) (A T : ℝ≥0) {p P E : ℝ}
    (hp : 0 ≤ p) (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 ≤ allocatedCommonSmoothingLog B dim A T p P E := by
  have htarget : 0 ≤ profileReferenceErrorLog P ((E + 1) + 1 + 4) := by
    have h := coefficientErrorSpatialLog_nonneg hP
    unfold profileReferenceErrorLog
    linarith
  exact physicalIdealSmoothingLog_nonneg (layerSamplerDegree I n) A T htarget
    (allocatedProfileGainLog_nonneg m (allocatedComparisonDimension_bounds m hp).1 hP
      (allocatedSiteKernelMaskLog_nonneg m hP))

end Logs

theorem exists_allocatedCommonRegularizationLog_bound (m dim : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧
      ∀ {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)] (A T : ℝ≥0)
        {p P E : ℝ}, 0 ≤ p → 0 ≤ P → 0 ≤ E → dim ≤ m + 1 →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        allocatedCommonSmoothingLog B dim A T p P E ≤ (p + A + T + P + E + a) ^ a ∧
          allocatedCommonTailLog (G := G) B dim A T p P E ≤ (p + A + T + P + E + a) ^ a := by
  obtain ⟨b, _, hLogs⟩ := exists_allocatedPhysicalIdealLogs_bound m dim
  obtain ⟨b₀, _, hEarly⟩ := exists_allocatedCommonCoverEarlyLog_bound m
  let poly : Polynomial ℕ :=
    (Polynomial.X + 2 * (Polynomial.X + 1 + Polynomial.C b₀) ^ b₀ + Polynomial.C b) ^ b
  obtain ⟨a, ha, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ A T p P E hp hP hE hdim hvars hI hn
  let target := profileReferenceErrorLog P ((E + 1) + 1 + 4)
  let gain := allocatedProfileGainLog m (allocatedComparisonDimension m p) P (allocatedSiteKernelMaskLog m P)
  have htarget : 0 ≤ target := by
    have h := coefficientErrorSpatialLog_nonneg hP
    dsimp [target, profileReferenceErrorLog]
    linarith
  have hgain : 0 ≤ gain := allocatedProfileGainLog_nonneg m (allocatedComparisonDimension_bounds m hp).1 hP
    (allocatedSiteKernelMaskLog_nonneg m hP)
  obtain ⟨hSmooth, hTail⟩ := hLogs B A T hp htarget hgain hdim hvars hI hn
  obtain ⟨_, _, _, _, _, _, _, _, _, herror, hgainBound, _⟩ :=
    allocatedCommonCoverEarlyLog_bounds m hp (le_refl 0) hP (le_refl 0) (show 0 ≤ E + 1 by linarith)
  have htargetError : target ≤ allocatedReferenceIdealError m (allocatedComparisonDimension m p) P
      ((E + 1) + 1 + 4) := by
    have hD := (allocatedComparisonDimension_bounds m hp).1
    change target ≤ target + (allocatedComparisonDimension m p) ^ 3 * ((m + 1 : ℕ) * P)
    exact le_add_of_nonneg_right (by positivity)
  let s : ℝ := p + A + T + P + E
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hEarlyBound : allocatedCommonCoverEarlyLog m p 0 P 0 (E + 1) ≤ (s + 1 + b₀) ^ b₀ := by
    have h := hEarly hp (le_refl 0) hP (le_refl 0) (show 0 ≤ E + 1 by linarith)
    apply h.trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [s]
    linarith [A.coe_nonneg, T.coe_nonneg]
  have htargetBound : target ≤ (s + 1 + b₀) ^ b₀ := (htargetError.trans herror).trans hEarlyBound
  have hgainBound' : gain ≤ (s + 1 + b₀) ^ b₀ := hgainBound.trans hEarlyBound
  have hsum : p + A + T + target + gain ≤ s + 2 * (s + 1 + b₀) ^ b₀ := by
    dsimp only [s] at *
    linarith
  have hFinal : (p + A + T + target + gain + b) ^ b ≤ (s + a) ^ a := by
    apply (pow_le_pow_left₀ (by positivity) (add_le_add hsum le_rfl) b).trans
    simpa [poly, Polynomial.eval₂_pow] using hpoly s hs
  exact ⟨hSmooth.trans hFinal, hTail.trans hFinal⟩

theorem exists_regularizedCommonCoverThreshold_bound (m dim A₀ Kraw Ksite : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧
      ∀ {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)] (A T : ℝ≥0)
        {p c P E : ℝ}, 0 ≤ p → 0 ≤ c → 0 ≤ P → 0 ≤ E → dim ≤ m + 1 →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        (allocatedCommonCoverParameter (G := G) B dim A₀ Kraw p c P
            (allocatedCommonSmoothingLog B dim A T p P E) (E + 1) + Ksite) ^ Ksite ≤
          (p + c + A + T + P + E + a) ^ a := by
  obtain ⟨b, _, hSmooth⟩ := exists_allocatedCommonRegularizationLog_bound m dim
  obtain ⟨k, _, hThreshold⟩ := exists_allocatedCommonCoverThreshold_bound m dim A₀ Kraw Ksite
  let poly : Polynomial ℕ := (Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b + 1 + Polynomial.C k) ^ k
  obtain ⟨a, ha, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ A T p c P E hp hc hP hE hdim hvars hI hn
  have he := allocatedCommonSmoothingLog_nonneg B dim A T hp hP hE
  have hsmooth := (hSmooth B A T hp hP hE hdim hvars hI hn).1
  have hthreshold := hThreshold B hp hc hP he (show 0 ≤ E + 1 by linarith) hvars
  let s : ℝ := p + c + A + T + P + E
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have heBound : allocatedCommonSmoothingLog B dim A T p P E ≤ (s + b) ^ b := by
    apply hsmooth.trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [s]
    linarith
  have hsum : p + c + P + allocatedCommonSmoothingLog B dim A T p P E + (E + 1) ≤
      s + (s + b) ^ b + 1 := by
    dsimp only [s] at *
    linarith [A.coe_nonneg, T.coe_nonneg]
  apply hthreshold.trans
  apply (pow_le_pow_left₀ (by positivity) (add_le_add hsum le_rfl) k).trans
  simpa [poly, Polynomial.eval₂_pow] using hpoly s hs

theorem exists_fixedRegularizedCommonCoverThreshold_bound (m dim A₀ Kraw Ksite : ℕ)
    (A T : ℝ≥0) :
    ∃ a : ℕ, 2 ≤ a ∧
      ∀ {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)]
        {p c P E : ℝ}, 0 ≤ p → 0 ≤ c → 0 ≤ P → 0 ≤ E → dim ≤ m + 1 →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        (allocatedCommonCoverParameter (G := G) B dim A₀ Kraw p c P
            (allocatedCommonSmoothingLog B dim A T p P E) (E + 1) + Ksite) ^ Ksite ≤
          (p + c + P + E + a) ^ a := by
  obtain ⟨b, hb, hbound⟩ := exists_regularizedCommonCoverThreshold_bound m dim A₀ Kraw Ksite
  let a := b + ⌈(A : ℝ) + T⌉₊ + 2
  have ha : 2 ≤ a := by dsimp [a]; omega
  have hba : b ≤ a := by dsimp [a]; omega
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ p c P E hp hc hP hE hdim hvars hI hn
  have h := hbound B A T hp hc hP hE hdim hvars hI hn
  have hcut : (A : ℝ) + T ≤ (⌈(A : ℝ) + T⌉₊ : ℝ) := Nat.le_ceil _
  have hside : p + c + A + T + P + E + b ≤ p + c + P + E + a := by
    dsimp only [a]
    push_cast
    linarith
  have hbase : 1 ≤ p + c + P + E + (a : ℝ) := by
    have har : (2 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  exact (h.trans (pow_le_pow_left₀ (by positivity) hside b)).trans (pow_le_pow_right₀ hbase hba)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

attribute [local instance 2000] fullBooleanRowSetFintype

section Scales

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)]

theorem allocatedCommonTailLog_nonneg (dim : ℕ) (A T : ℝ≥0) {p P E : ℝ}
    (hp : 0 ≤ p) (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 ≤ allocatedCommonTailLog (G := G) B dim A T p P E := by
  have htarget : 0 ≤ profileReferenceErrorLog P ((E + 1) + 1 + 4) := by
    have h := coefficientErrorSpatialLog_nonneg hP
    unfold profileReferenceErrorLog
    linarith
  exact physicalIdealTailLog_nonneg G (G × Option (Fin dim)) (layerSamplerDegree I n) A T m htarget
    (allocatedProfileGainLog_nonneg m (allocatedComparisonDimension_bounds m hp).1 hP
      (allocatedSiteKernelMaskLog_nonneg m hP))

noncomputable def allocatedCommonWidth (dim : ℕ) (A T : ℝ≥0) (p P E : ℝ) : ℝ :=
  Real.exp (-allocatedCommonTailLog (G := G) B dim A T p P E)

noncomputable def allocatedCommonGeometryLog (dim : ℕ) (A T : ℝ≥0) (p g P E : ℝ) : ℝ :=
  g + allocatedCommonRadiusLog m p g + allocatedCommonTailLog (G := G) B dim A T p P E

theorem allocatedCommonWidth_bounds (dim : ℕ) (A T : ℝ≥0) {p P E : ℝ}
    (hp : 0 ≤ p) (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 < allocatedCommonWidth (G := G) B dim A T p P E ∧
      allocatedCommonWidth (G := G) B dim A T p P E ≤ 1 ∧
      (allocatedCommonWidth (G := G) B dim A T p P E)⁻¹ =
        Real.exp (allocatedCommonTailLog (G := G) B dim A T p P E) := by
  refine ⟨Real.exp_pos _, ?_, ?_⟩
  · exact Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (allocatedCommonTailLog_nonneg (G := G) B dim A T hp hP hE))
  · simp only [allocatedCommonWidth, Real.exp_neg, inv_inv]

theorem allocatedCommonWidth_le (dim : ℕ) (A T : ℝ≥0) {p P E t : ℝ}
    (ht : 0 < t) (hti : t⁻¹ ≤ Real.exp (allocatedCommonTailLog (G := G) B dim A T p P E)) :
    allocatedCommonWidth (G := G) B dim A T p P E ≤ t := by
  have h := (inv_le_inv₀ (Real.exp_pos (allocatedCommonTailLog (G := G) B dim A T p P E))
    (inv_pos.mpr ht)).2 hti
  simpa only [allocatedCommonWidth, Real.exp_neg, inv_inv] using h

theorem allocatedCommonGeometryLog_bounds (dim : ℕ) (A T : ℝ≥0) {p g P E : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hP : 0 ≤ P) (hE : 0 ≤ E) :
    let c := allocatedCommonGeometryLog (G := G) B dim A T p g P E
    0 ≤ c ∧ g ≤ c ∧ allocatedCommonRadiusLog m p g ≤ c ∧
      allocatedCommonTailLog (G := G) B dim A T p P E ≤ c ∧
      (allocatedCommonRadius m p g)⁻¹ ≤ Real.exp c ∧
      (allocatedCommonWidth (G := G) B dim A T p P E)⁻¹ ≤ Real.exp c := by
  have hr := (allocatedCommonRadiusLog_bounds m hp hg).1
  have ht := allocatedCommonTailLog_nonneg (G := G) B dim A T hp hP hE
  have hrg : allocatedCommonRadiusLog m p g ≤ allocatedCommonGeometryLog (G := G) B dim A T p g P E := by
    unfold allocatedCommonGeometryLog
    linarith
  have htg : allocatedCommonTailLog (G := G) B dim A T p P E ≤
      allocatedCommonGeometryLog (G := G) B dim A T p g P E := by
    unfold allocatedCommonGeometryLog
    linarith
  refine ⟨hr.trans hrg, ?_, hrg, htg, ?_, ?_⟩
  · unfold allocatedCommonGeometryLog
    linarith
  · rw [(allocatedCommonRadius_bounds m hp hg).2.2]
    exact Real.exp_le_exp.mpr hrg
  · rw [(allocatedCommonWidth_bounds (G := G) B dim A T hp hP hE).2.2]
    exact Real.exp_le_exp.mpr htg

end Scales

theorem exists_allocatedCommonGeometryLog_bound (m dim : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧
      ∀ {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)] (A T : ℝ≥0)
        {p g P E : ℝ}, 0 ≤ p → 0 ≤ g → 0 ≤ P → 0 ≤ E → dim ≤ m + 1 →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        allocatedCommonGeometryLog (G := G) B dim A T p g P E ≤ (p + g + A + T + P + E + a) ^ a := by
  obtain ⟨b, _, hRadius⟩ := exists_allocatedCommonRadiusLog_bound m
  obtain ⟨k, _, hTail⟩ := exists_allocatedCommonRegularizationLog_bound m dim
  let poly : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b +
    (Polynomial.X + Polynomial.C k) ^ k
  obtain ⟨a, ha, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ A T p g P E hp hg hP hE hdim hvars hI hn
  let s : ℝ := p + g + A + T + P + E
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hr : allocatedCommonRadiusLog m p g ≤ (s + b) ^ b := by
    apply (hRadius p g hp hg).trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [s]
    linarith [A.coe_nonneg, T.coe_nonneg]
  have ht : allocatedCommonTailLog (G := G) B dim A T p P E ≤ (s + k) ^ k := by
    apply (hTail B A T hp hP hE hdim hvars hI hn).2.trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [s]
    linarith
  have hsum : allocatedCommonGeometryLog (G := G) B dim A T p g P E ≤
      s + (s + b) ^ b + (s + k) ^ k := by
    unfold allocatedCommonGeometryLog
    dsimp only [s] at *
    linarith [A.coe_nonneg, T.coe_nonneg]
  apply hsum.trans
  simpa [poly, Polynomial.eval₂_pow] using hpoly s hs

theorem exists_geometricCommonCoverThreshold_bound (m dim A₀ Kraw Ksite : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧
      ∀ {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)] (A T : ℝ≥0)
        {p g P E : ℝ}, 0 ≤ p → 0 ≤ g → 0 ≤ P → 0 ≤ E → dim ≤ m + 1 →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        (allocatedCommonCoverParameter (G := G) B dim A₀ Kraw p
            (allocatedCommonGeometryLog (G := G) B dim A T p g P E) P
            (allocatedCommonSmoothingLog B dim A T p P E) (E + 1) + Ksite) ^ Ksite ≤
          (p + g + A + T + P + E + a) ^ a := by
  obtain ⟨b, _, hGeometry⟩ := exists_allocatedCommonGeometryLog_bound m dim
  obtain ⟨k, _, hThreshold⟩ := exists_regularizedCommonCoverThreshold_bound m dim A₀ Kraw Ksite
  let poly : Polynomial ℕ := (Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b + Polynomial.C k) ^ k
  obtain ⟨a, ha, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ A T p g P E hp hg hP hE hdim hvars hI hn
  have hc := (allocatedCommonGeometryLog_bounds (G := G) B dim A T hp hg hP hE).1
  have hgeom := hGeometry B A T hp hg hP hE hdim hvars hI hn
  have hthreshold := hThreshold B A T hp hc hP hE hdim hvars hI hn
  let s : ℝ := p + g + A + T + P + E
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsum : p + allocatedCommonGeometryLog (G := G) B dim A T p g P E + A + T + P + E ≤
      s + (s + b) ^ b := by
    dsimp only [s] at *
    linarith
  apply hthreshold.trans
  apply (pow_le_pow_left₀ (by positivity) (add_le_add hsum le_rfl) k).trans
  simpa [poly, Polynomial.eval₂_pow] using hpoly s hs

theorem exists_fixedGeometricCommonCoverThreshold_bound (m dim A₀ Kraw Ksite : ℕ)
    (A T : ℝ≥0) :
    ∃ a : ℕ, 2 ≤ a ∧
      ∀ {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)]
        {p g P E : ℝ}, 0 ≤ p → 0 ≤ g → 0 ≤ P → 0 ≤ E → dim ≤ m + 1 →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        (allocatedCommonCoverParameter (G := G) B dim A₀ Kraw p
            (allocatedCommonGeometryLog (G := G) B dim A T p g P E) P
            (allocatedCommonSmoothingLog B dim A T p P E) (E + 1) + Ksite) ^ Ksite ≤
          (p + g + P + E + a) ^ a := by
  obtain ⟨b, hb, hbound⟩ := exists_geometricCommonCoverThreshold_bound m dim A₀ Kraw Ksite
  let a := b + ⌈(A : ℝ) + T⌉₊ + 2
  have ha : 2 ≤ a := by dsimp [a]; omega
  have hba : b ≤ a := by dsimp [a]; omega
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ p g P E hp hg hP hE hdim hvars hI hn
  have h := hbound B A T hp hg hP hE hdim hvars hI hn
  have hcut : (A : ℝ) + T ≤ (⌈(A : ℝ) + T⌉₊ : ℝ) := Nat.le_ceil _
  have hside : p + g + A + T + P + E + b ≤ p + g + P + E + a := by
    dsimp only [a]
    push_cast
    linarith
  have hbase : 1 ≤ p + g + P + E + (a : ℝ) := by
    have har : (2 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  exact (h.trans (pow_le_pow_left₀ (by positivity) hside b)).trans (pow_le_pow_right₀ hbase hba)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

attribute [local instance 2000] fullBooleanRowSetFintype

section Scales

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedProductGeometryLog (dim : ℕ) (A T : ℝ≥0) (p g P E : ℝ) : ℝ :=
  g + allocatedCommonProductRadiusLog m p g + allocatedCommonTailLog (G := G) B dim A T p P E

theorem allocatedProductGeometryLog_bounds (dim : ℕ) (A T : ℝ≥0) {p g P E : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hP : 0 ≤ P) (hE : 0 ≤ E) :
    let c := allocatedProductGeometryLog (G := G) B dim A T p g P E
    0 ≤ c ∧ g ≤ c ∧ allocatedCommonProductRadiusLog m p g ≤ c ∧
      allocatedCommonTailLog (G := G) B dim A T p P E ≤ c ∧
      (allocatedCommonProductRadius m p g)⁻¹ ≤ Real.exp c ∧
      (allocatedCommonWidth (G := G) B dim A T p P E)⁻¹ ≤ Real.exp c := by
  have hr := (allocatedCommonProductRadius_bounds m hp hg).1
  have ht := allocatedCommonTailLog_nonneg (G := G) B dim A T hp hP hE
  have hrg : allocatedCommonProductRadiusLog m p g ≤
      allocatedProductGeometryLog (G := G) B dim A T p g P E := by
    unfold allocatedProductGeometryLog
    linarith
  have htg : allocatedCommonTailLog (G := G) B dim A T p P E ≤
      allocatedProductGeometryLog (G := G) B dim A T p g P E := by
    unfold allocatedProductGeometryLog
    linarith
  refine ⟨hr.trans hrg, ?_, hrg, htg, ?_, ?_⟩
  · unfold allocatedProductGeometryLog
    linarith
  · rw [(allocatedCommonProductRadius_bounds m hp hg).2.2.2.1]
    exact Real.exp_le_exp.mpr hrg
  · rw [(allocatedCommonWidth_bounds (G := G) B dim A T hp hP hE).2.2]
    exact Real.exp_le_exp.mpr htg

end Scales

theorem exists_allocatedProductGeometryLog_bound (m dim : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧
      ∀ {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)] (A T : ℝ≥0)
        {p g P E : ℝ}, 0 ≤ p → 0 ≤ g → 0 ≤ P → 0 ≤ E → dim ≤ m + 1 →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        allocatedProductGeometryLog (G := G) B dim A T p g P E ≤ (p + g + A + T + P + E + a) ^ a := by
  obtain ⟨b, _, hRadius⟩ := exists_allocatedCommonProductRadiusLog_bound m
  obtain ⟨k, _, hTail⟩ := exists_allocatedCommonRegularizationLog_bound m dim
  let poly : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b +
    (Polynomial.X + Polynomial.C k) ^ k
  obtain ⟨a, ha, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ A T p g P E hp hg hP hE hdim hvars hI hn
  let s : ℝ := p + g + A + T + P + E
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hr : allocatedCommonProductRadiusLog m p g ≤ (s + b) ^ b := by
    apply (hRadius (p := p) (g := g) hp hg).trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [s]
    linarith [A.coe_nonneg, T.coe_nonneg]
  have ht : allocatedCommonTailLog (G := G) B dim A T p P E ≤ (s + k) ^ k := by
    apply (hTail B A T hp hP hE hdim hvars hI hn).2.trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [s]
    linarith
  have hsum : allocatedProductGeometryLog (G := G) B dim A T p g P E ≤
      s + (s + b) ^ b + (s + k) ^ k := by
    unfold allocatedProductGeometryLog
    dsimp only [s] at *
    linarith [A.coe_nonneg, T.coe_nonneg]
  apply hsum.trans
  simpa [poly, Polynomial.eval₂_pow] using hpoly s hs

theorem exists_productGeometricCommonCoverThreshold_bound (m dim A₀ Kraw Ksite : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧
      ∀ {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)] (A T : ℝ≥0)
        {p g P E : ℝ}, 0 ≤ p → 0 ≤ g → 0 ≤ P → 0 ≤ E → dim ≤ m + 1 →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        (allocatedCommonCoverParameter (G := G) B dim A₀ Kraw p
            (allocatedProductGeometryLog (G := G) B dim A T p g P E) P
            (allocatedCommonSmoothingLog B dim A T p P E) (E + 1) + Ksite) ^ Ksite ≤
          (p + g + A + T + P + E + a) ^ a := by
  obtain ⟨b, _, hGeometry⟩ := exists_allocatedProductGeometryLog_bound m dim
  obtain ⟨k, _, hThreshold⟩ := exists_regularizedCommonCoverThreshold_bound m dim A₀ Kraw Ksite
  let poly : Polynomial ℕ := (Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b + Polynomial.C k) ^ k
  obtain ⟨a, ha, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ A T p g P E hp hg hP hE hdim hvars hI hn
  have hc := (allocatedProductGeometryLog_bounds (G := G) B dim A T hp hg hP hE).1
  have hgeom := hGeometry B A T hp hg hP hE hdim hvars hI hn
  have hthreshold := hThreshold B A T hp hc hP hE hdim hvars hI hn
  let s : ℝ := p + g + A + T + P + E
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsum : p + allocatedProductGeometryLog (G := G) B dim A T p g P E + A + T + P + E ≤
      s + (s + b) ^ b := by
    dsimp only [s] at *
    linarith
  apply hthreshold.trans
  apply (pow_le_pow_left₀ (by positivity) (add_le_add hsum le_rfl) k).trans
  simpa [poly, Polynomial.eval₂_pow] using hpoly s hs

theorem exists_fixedProductGeometricCommonCoverThreshold_bound (m dim A₀ Kraw Ksite : ℕ)
    (A T : ℝ≥0) :
    ∃ a : ℕ, 2 ≤ a ∧
      ∀ {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)]
        {p g P E : ℝ}, 0 ≤ p → 0 ≤ g → 0 ≤ P → 0 ≤ E → dim ≤ m + 1 →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        (allocatedCommonCoverParameter (G := G) B dim A₀ Kraw p
            (allocatedProductGeometryLog (G := G) B dim A T p g P E) P
            (allocatedCommonSmoothingLog B dim A T p P E) (E + 1) + Ksite) ^ Ksite ≤
          (p + g + P + E + a) ^ a := by
  obtain ⟨b, hb, hbound⟩ := exists_productGeometricCommonCoverThreshold_bound m dim A₀ Kraw Ksite
  let a := b + ⌈(A : ℝ) + T⌉₊ + 2
  have ha : 2 ≤ a := by dsimp [a]; omega
  have hba : b ≤ a := by dsimp [a]; omega
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ p g P E hp hg hP hE hdim hvars hI hn
  have h := hbound B A T hp hg hP hE hdim hvars hI hn
  have hcut : (A : ℝ) + T ≤ (⌈(A : ℝ) + T⌉₊ : ℝ) := Nat.le_ceil _
  have hside : p + g + A + T + P + E + b ≤ p + g + P + E + a := by
    dsimp only [a]
    push_cast
    linarith
  have hbase : 1 ≤ p + g + P + E + (a : ℝ) := by
    have har : (2 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  exact (h.trans (pow_le_pow_left₀ (by positivity) hside b)).trans (pow_le_pow_right₀ hbase hba)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

theorem exists_allocatedCommonCoarseBudget (m dim : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {G : Type*} [Fintype G] (X : Type*) [Fintype X]
      (selection : Fin dim ↪ G) {M modulus : ℕ} {p c P e E : ℝ},
      0 ≤ p → 0 ≤ c → 0 ≤ P → 0 ≤ e → 0 ≤ E →
      (Fintype.card G : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ P →
      0 < M → (M : ℝ) ≤ Real.exp P → modulus ≤ M ^ (m + 1) →
      let r := allocatedCommonCoarseMesh m X selection M modulus p c P e E
      r⁻¹ ≤ Real.exp ((p + c + P + e + E + a) ^ a) ∧
        allocatedSpatialCoefficientCap X selection M modulus r ≤
          Real.exp ((p + c + P + e + E + a) ^ a) := by
  obtain ⟨a, ha, hlog⟩ := exists_allocatedCommonCoarseLog_bound m dim
  refine ⟨a, ha, ?_⟩
  intro G _ X _ selection M modulus p c P e E hp hc hP he hE hG hX hM hMP hmod
  obtain ⟨hr, hcap⟩ := allocatedCommonCoarseMesh_partition_budget m X selection
    hp hc hP he hE hG hX hM hMP hmod
  obtain ⟨hlogr, hlogcap⟩ := hlog (show 0 ≤ p + c + P + e + E by positivity)
  exact ⟨hr.trans (Real.exp_le_exp.mpr hlogr), hcap.trans (Real.exp_le_exp.mpr hlogcap)⟩

noncomputable def allocatedActualCommonCoarseMesh {m dim : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)]
    (X : Type*) [Fintype X] (selection : Fin dim ↪ G) (M modulus : ℕ)
    (A T : ℝ≥0) (p g P E : ℝ) : ℝ :=
  allocatedCommonCoarseMesh m X selection M modulus p
    (allocatedCommonGeometryLog (G := G) B dim A T p g P E) P
    (allocatedCommonSmoothingLog B dim A T p P E) E

theorem exists_actualCommonCoarseBudget (m dim : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧
      ∀ {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)] (A T : ℝ≥0)
        (X : Type*) [Fintype X] (selection : Fin dim ↪ G) {M modulus : ℕ}
        {p g P E : ℝ}, 0 ≤ p → 0 ≤ g → 0 ≤ P → 0 ≤ E → dim ≤ m + 1 →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        (Fintype.card X : ℝ) ≤ P → 0 < M → (M : ℝ) ≤ Real.exp P →
        modulus ≤ M ^ (m + 1) →
        let r := allocatedActualCommonCoarseMesh B X selection M modulus A T p g P E
        r⁻¹ ≤ Real.exp ((p + g + A + T + P + E + a) ^ a) ∧
          allocatedSpatialCoefficientCap X selection M modulus r ≤
            Real.exp ((p + g + A + T + P + E + a) ^ a) := by
  obtain ⟨b, _, hCoarse⟩ := exists_allocatedCommonCoarseBudget m dim
  obtain ⟨k, _, hGeometry⟩ := exists_allocatedCommonGeometryLog_bound m dim
  obtain ⟨l, _, hSmoothing⟩ := exists_allocatedCommonRegularizationLog_bound m dim
  let poly : Polynomial ℕ :=
    (Polynomial.X + (Polynomial.X + Polynomial.C k) ^ k +
      (Polynomial.X + Polynomial.C l) ^ l + Polynomial.C b) ^ b
  obtain ⟨a, ha, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ A T X _ selection M modulus p g P E hp hg hP hE hdim hvars hI hn hX hM hMP hmod
  have hc := (allocatedCommonGeometryLog_bounds (G := G) B dim A T hp hg hP hE).1
  have he := allocatedCommonSmoothingLog_nonneg B dim A T hp hP hE
  have hG : (Fintype.card G : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvars
  obtain ⟨hr, hcap⟩ := hCoarse X selection hp hc hP he hE hG hX hM hMP hmod
  have hcBound := hGeometry B A T hp hg hP hE hdim hvars hI hn
  let s : ℝ := p + g + A + T + P + E
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have heBound : allocatedCommonSmoothingLog B dim A T p P E ≤ (s + l) ^ l := by
    apply (hSmoothing B A T hp hP hE hdim hvars hI hn).1.trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [s]
    linarith only [hg]
  have hsum : p + allocatedCommonGeometryLog (G := G) B dim A T p g P E + P +
      allocatedCommonSmoothingLog B dim A T p P E + E + b ≤
        s + (s + k) ^ k + (s + l) ^ l + b := by
    change allocatedCommonGeometryLog (G := G) B dim A T p g P E ≤ (s + k) ^ k at hcBound
    dsimp only [s] at *
    linarith only [hcBound, heBound, hg, A.coe_nonneg, T.coe_nonneg]
  have hfinal : (p + allocatedCommonGeometryLog (G := G) B dim A T p g P E + P +
      allocatedCommonSmoothingLog B dim A T p P E + E + b) ^ b ≤ (s + a) ^ a := by
    apply (pow_le_pow_left₀ (by positivity) hsum b).trans
    simpa [poly, Polynomial.eval₂_pow] using hpoly s hs
  exact ⟨hr.trans (Real.exp_le_exp.mpr hfinal), hcap.trans (Real.exp_le_exp.mpr hfinal)⟩

theorem exists_fixedActualCommonCoarseBudget (m dim : ℕ) (A T : ℝ≥0) :
    ∃ a : ℕ, 2 ≤ a ∧
      ∀ {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)]
        (X : Type*) [Fintype X] (selection : Fin dim ↪ G) {M modulus : ℕ}
        {p g P E : ℝ}, 0 ≤ p → 0 ≤ g → 0 ≤ P → 0 ≤ E → dim ≤ m + 1 →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        (Fintype.card X : ℝ) ≤ P → 0 < M → (M : ℝ) ≤ Real.exp P →
        modulus ≤ M ^ (m + 1) →
        let r := allocatedActualCommonCoarseMesh B X selection M modulus A T p g P E
        r⁻¹ ≤ Real.exp ((p + g + P + E + a) ^ a) ∧
          allocatedSpatialCoefficientCap X selection M modulus r ≤
            Real.exp ((p + g + P + E + a) ^ a) := by
  obtain ⟨b, _, hbound⟩ := exists_actualCommonCoarseBudget m dim
  let a := b + ⌈(A : ℝ) + T⌉₊ + 2
  have ha : 2 ≤ a := by dsimp [a]; omega
  have hba : b ≤ a := by dsimp [a]; omega
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ X _ selection M modulus p g P E hp hg hP hE hdim hvars hI hn hX hM hMP hmod
  obtain ⟨hr, hcap⟩ := hbound B A T X selection hp hg hP hE hdim hvars hI hn hX hM hMP hmod
  have hcut : (A : ℝ) + T ≤ (⌈(A : ℝ) + T⌉₊ : ℝ) := Nat.le_ceil _
  have hside : p + g + A + T + P + E + b ≤ p + g + P + E + a := by
    dsimp only [a]
    push_cast
    linarith only [hcut]
  have hbase : 1 ≤ p + g + P + E + (a : ℝ) := by
    have har : (2 : ℝ) ≤ a := by exact_mod_cast ha
    linarith only [hp, hg, hP, hE, har]
  have hfinal := Real.exp_le_exp.mpr
    ((pow_le_pow_left₀ (by positivity) hside b).trans (pow_le_pow_right₀ hbase hba))
  exact ⟨hr.trans hfinal, hcap.trans hfinal⟩

end Erdos3.VectorPolynomial

end

end OAI
