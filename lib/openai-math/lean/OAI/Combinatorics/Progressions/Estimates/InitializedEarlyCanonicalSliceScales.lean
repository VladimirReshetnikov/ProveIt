import OAI.Combinatorics.Progressions.Lattices.EarlyAllocatedAffineL1Scales

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {s : ℕ}
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset (Fin (s + 1)))
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j a, (rows j a).card ≤ j.val + 1)

include hrows hcard in
theorem exists_early_allocated_canonical_slice_scales
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {target D p q a Qstride : ℝ} (hdegree : 0 < m)
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) O D)
    (htarget : 0 ≤ target) (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) (hQstride : 0 ≤ Qstride)
    (Cdetect nX : ℕ) :
    let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) p q a
    let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + p + 4)
    let F := p + 2
    let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
    let δ := Real.exp (-(p + 1))
    let maskLog := D * ((m * 2 ^ (m + 1) : ℕ) * Pk)
    let E := target + maskLog + 5
    let η := Real.exp (-E)
    let Prho := 2 * affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F + 2
    let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1) (A : ℝ) (T : ℝ) E F
    let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
    0 ≤ Prho ∧ 0 ≤ Ptail ∧
    ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ partition, 0 < ρ partition ∧ ρ partition ≤ 1 ∧ (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho) ∧
    ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
      t⁻¹ ≤ Real.exp Ptail ∧
      AllocatedAffineCoveredComparison.{uJ,uQ,_,_,_,_,_} (G := G) B rows δ η ρ t htone ∧
      ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        (R : Fin m → ℝ), (∀ j, 0 < R j) →
        ∀ {pRadius : ℝ}, 0 ≤ pRadius → (∀ j, (R j)⁻¹ ≤ Real.exp pRadius) →
        let P := pRadius + Ptail
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
          (∀ j, (R j)⁻¹ ≤ Real.exp P) ∧ (∀ j : Fin m, ((fun _ => t) j)⁻¹ ≤ Real.exp P) ∧
          Real.exp (allocatedAffineLengthLog m D P Prho Pk target F Tmod) ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp ((D + P + Prho + Pk + target + F + Tmod + K) ^ K) ∧
          ∀ α : ℝ, Real.exp (-a) ≤ α →
            scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊
              (((Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
                Real.exp (-((q + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value := by
  intro gainLog Pk F Tmod δ maskLog E η Prho Ptail K
  have hgain0 : 0 ≤ gainLog := slicedDetectionGainLog_nonneg s Cdetect _ hp hq ha
  have hPk : 0 ≤ Pk := by
    dsimp only [Pk]
    rw [scalarKernelLogarithmicBudget_eq]
    positivity
  have hF : 0 ≤ F := by dsimp only [F]; linarith
  have hTmod : 0 ≤ Tmod := by dsimp only [Tmod]; positivity
  have hδ : 0 < δ := Real.exp_pos _
  have hδone : δ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hδF : (δ / 2)⁻¹ ≤ Real.exp F := by
    dsimp only [δ, F]
    simp only [Real.exp_neg, div_eq_mul_inv, mul_inv_rev, inv_inv]
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp 1 * Real.exp (p + 1) := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm.trans (congrArg Real.exp (by ring))
  obtain ⟨hPrho, hPtail, ρ, hρ, t, ht, htone, htlog, hs, hscales⟩ :=
    exists_early_allocated_affine_l1_scales.{uJ,uQ} B rows hrows hcard ψ hψ hrange hzero hone A T hLip hTransition
      block hblock hdim hδ hδone htarget hPk hF hTmod hδF
  refine ⟨hPrho, hPtail, ρ, hρ, t, ht, htone, htlog, hs, ?_⟩
  intro J _ U basis R hR pRadius hpRadius hRi P
  obtain ⟨S, hRiP, hσP, hlength, hupper⟩ := hscales U basis R hR hpRadius hRi
  refine ⟨S, hRiP, hσP, hlength, hupper, ?_⟩
  intro α hα
  have hcutoff := slicedDetection_kernel_cutoff_bound s Cdetect
    (Fintype.card (LayerSamplerVariables G I n B)) G hp hq ha hα
  exact allocatedAffineLength_kernel_ready hdegree hdim.nonneg (add_nonneg hpRadius hPtail)
    hPrho hPk htarget hF hTmod hcutoff hlength

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

noncomputable def canonicalSublevelCutoffLip : ℝ≥0 :=
  Classical.choose exists_smooth_sublevel_cutoff

noncomputable def canonicalSublevelCutoff : ℝ → ℝ :=
  Classical.choose (Classical.choose_spec exists_smooth_sublevel_cutoff).2

noncomputable def canonicalTransitionLip : ℝ≥0 :=
  Classical.choose exists_smoothTransition_lipschitz

theorem canonicalSublevelCutoff_spec :
    ContDiff ℝ ∞ canonicalSublevelCutoff ∧
    (∀ t, canonicalSublevelCutoff t ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ t, |t| ≤ 1 → canonicalSublevelCutoff t = 0) ∧
    (∀ t, 2 ≤ |t| → canonicalSublevelCutoff t = 1) ∧
    LipschitzWith canonicalSublevelCutoffLip canonicalSublevelCutoff :=
  Classical.choose_spec (Classical.choose_spec exists_smooth_sublevel_cutoff).2

theorem canonicalTransitionLip_spec :
    LipschitzWith canonicalTransitionLip Real.smoothTransition :=
  (Classical.choose_spec exists_smoothTransition_lipschitz).2

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {s : ℕ}
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset (Fin (s + 1)))

theorem exists_initialized_early_canonical_slice_scales
    (hrows : ∀ j, Function.Injective (rows j))
    (hcard : ∀ j a, (rows j a).card ≤ j.val + 1)
    (hblocks : ∀ a : LayerSamplerAxis I n, Fintype.card (O a.1) ≤ Fintype.card (B a))
    {target D p q a Qstride : ℝ} (hdegree : 0 < m)
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) O D)
    (htarget : 0 ≤ target) (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) (hQstride : 0 ≤ Qstride)
    (Cdetect nX : ℕ) :
    let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) p q a
    let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + p + 4)
    let F := p + 2
    let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
    let δ := Real.exp (-(p + 1))
    let maskLog := D * ((m * 2 ^ (m + 1) : ℕ) * Pk)
    let E := target + maskLog + 5
    let η := Real.exp (-E)
    let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F + 2
    let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1) (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
    let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
    0 ≤ Prho ∧ 0 ≤ Ptail ∧
    ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ partition, 0 < ρ partition ∧ ρ partition ≤ 1 ∧ (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho) ∧
    ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
      t⁻¹ ≤ Real.exp Ptail ∧
      AllocatedAffineCoveredComparison.{uJ,uQ,_,_,_,_,_} (G := G) B rows δ η ρ t htone ∧
      ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        (R : Fin m → ℝ), (∀ j, 0 < R j) →
        ∀ {pRadius : ℝ}, 0 ≤ pRadius → (∀ j, (R j)⁻¹ ≤ Real.exp pRadius) →
        let P := pRadius + Ptail
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
          (∀ j, (R j)⁻¹ ≤ Real.exp P) ∧ (∀ j : Fin m, ((fun _ => t) j)⁻¹ ≤ Real.exp P) ∧
          Real.exp (allocatedAffineLengthLog m D P Prho Pk target F Tmod) ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp ((D + P + Prho + Pk + target + F + Tmod + K) ^ K) ∧
          ∀ α : ℝ, Real.exp (-a) ≤ α →
            scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊
              (((Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
                Real.exp (-((q + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value := by
  let block (a : LayerSamplerAxis I n) : O a.1 ↪ B a :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (hblocks a))
  obtain ⟨hsmooth, hrange, hzero, hone, hLip⟩ := canonicalSublevelCutoff_spec
  exact exists_early_allocated_canonical_slice_scales.{uJ,uQ} B rows hrows hcard
    canonicalSublevelCutoff hsmooth hrange hzero hone
    canonicalSublevelCutoffLip canonicalTransitionLip hLip canonicalTransitionLip_spec
    (fun a => block a) (fun a => (block a).injective) hdegree hdim
    htarget hp hq ha hQstride Cdetect nX

attribute [local instance 2000] fullBooleanRowSetFintype
local notation "fullRowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
local notation "fullRowTypes" => (fun j : Fin m => (fullRowSets j : Type))
local notation "fullRows" => (fun j : Fin m => (Subtype.val : fullRowSets j → Finset (Fin (s + 1))))

theorem exists_primitive_early_canonical_slice_scales
    {target pnum p q a Qstride : ℝ} (hdegree : 0 < m) (hs : s ≤ m)
    (hpnum : 0 ≤ pnum)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pnum)
    (hn : ∀ j, (n j : ℝ) ≤ pnum)
    (hblocks : ∀ b : LayerSamplerAxis I n,
      (boundedBooleanJetRows (Fin (s + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b))
    (htarget : 0 ≤ target) (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) (hQstride : 0 ≤ Qstride)
    (Cdetect nX : ℕ) :
    let D := allocatedComparisonDimension m pnum
    let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) p q a
    let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + p + 4)
    let F := p + 2
    let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
    let δ := Real.exp (-(p + 1))
    let maskLog := D * ((m * 2 ^ (m + 1) : ℕ) * Pk)
    let E := target + maskLog + 5
    let η := Real.exp (-E)
    let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F + 2
    let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1) (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
    let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
    0 ≤ Prho ∧ 0 ≤ Ptail ∧
    ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ partition, 0 < ρ partition ∧ ρ partition ≤ 1 ∧ (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho) ∧
    ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
      t⁻¹ ≤ Real.exp Ptail ∧
      AllocatedAffineCoveredComparison.{uJ,uQ,_,_,_,_,_} (G := G) B fullRows δ η ρ t htone ∧
      ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        (R : Fin m → ℝ), (∀ j, 0 < R j) →
        ∀ {pRadius : ℝ}, 0 ≤ pRadius → (∀ j, (R j)⁻¹ ≤ Real.exp pRadius) →
        let P := pRadius + Ptail
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
          (∀ j, (R j)⁻¹ ≤ Real.exp P) ∧ (∀ j : Fin m, ((fun _ => t) j)⁻¹ ≤ Real.exp P) ∧
          Real.exp (allocatedAffineLengthLog m D P Prho Pk target F Tmod) ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp ((D + P + Prho + Pk + target + F + Tmod + K) ^ K) ∧
          ∀ α : ℝ, Real.exp (-a) ≤ α →
            scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊
              (((Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
                Real.exp (-((q + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value := by
  intro D
  let (j : Fin m) : Nonempty (fullRowTypes j) :=
    ⟨⟨∅, (mem_boundedBooleanJetRows _ _).mpr (by simp)⟩⟩
  have hinj : ∀ j, Function.Injective (fullRows j) := fun _ => Subtype.val_injective
  have hcard : ∀ j (a : fullRowTypes j), (fullRows j a).card ≤ j.val + 1 :=
    fun j a => (mem_boundedBooleanJetRows _ _).mp a.property
  have hdim : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) fullRowTypes D :=
    allocatedComparisonDimensions_of_primitive B fullRows
      (by simpa only [Fintype.card_fin] using Nat.succ_le_succ hs) hinj hpnum hK hI hn
  have hblocks' : ∀ b : LayerSamplerAxis I n,
      Fintype.card (fullRowTypes b.1) ≤ Fintype.card (B b) := by
    intro b
    simpa only [Fintype.card_coe] using hblocks b
  exact exists_initialized_early_canonical_slice_scales.{uJ,uQ} B fullRows hinj hcard hblocks'
    hdegree hdim htarget hp hq ha hQstride Cdetect nX

end Erdos3.VectorPolynomial

end

end OAI
