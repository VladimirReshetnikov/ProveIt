import OAI.Combinatorics.Progressions.Estimates.SharedWidthPreparedChoice
import OAI.Combinatorics.Progressions.Estimates.SharedWidthPreparedLateToleranceFreeTrimSource
import OAI.Combinatorics.Progressions.Polynomial.PreparedUniformDegreePrecisionBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem exists_preparedUniformDegreeSampler
    {ι : Type*} [Fintype ι] (R σ : Fin m → ℝ) (lengthLogs : ι → ℝ)
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    {D P Pmin W Qw : ℝ} {Lmin : ℕ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hDP : D ≤ P) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hLogs : ∀ i, 0 ≤ lengthLogs i)
    (hPmin : 0 ≤ Pmin) (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin)
    (hW : 1 ≤ W) (hQw : 0 ≤ Qw) (hWexp : W ≤ Real.exp Qw) :
    let Lsum := ∑ i, lengthLogs i
    let Pseed := allocatedScaleLog (P + Lsum + Pmin + 1)
    ∃ S : LayerSamplerScale (G := G) B U basis R σ,
      (∀ i, Real.exp (lengthLogs i) ≤ S.value) ∧
      Lmin ≤ S.value ∧
      (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
      ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
            ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)) := by
  intro Lsum Pseed
  let Q := P + Lsum + Pmin + 1
  let L0 := ⌈Real.exp (Lsum + Pmin)⌉₊
  let S0 := selectedLayerSamplerScale (G := G) B U basis R σ hR hσ L0
  have hP : 0 ≤ P := hdim.nonneg.trans hDP
  have hsum : 0 ≤ Lsum := Finset.sum_nonneg (fun i _ => hLogs i)
  have hQ : 0 ≤ Q := by dsimp only [Q]; linarith only [hP, hsum, hPmin]
  have hPQ : P ≤ Q := by dsimp only [Q]; linarith only [hsum, hPmin]
  have hLQ : Lsum + Pmin + 1 ≤ Q := by dsimp only [Q]; linarith only [hP]
  have hL0 : (L0 : ℝ) ≤ Real.exp Q :=
    (natCeil_le_exp_succ_of_le (add_nonneg hsum hPmin) le_rfl).trans
      (Real.exp_le_exp.mpr hLQ)
  have hS0 : (S0.value : ℝ) ≤ Real.exp Pseed := by
    apply selectedLayerSamplerScale_exp_bound B U basis R σ hR hσ L0 hQ
      (hdim.degree.trans (hDP.trans hPQ))
      (fun j => (hdim.integer_axes B j).trans (hDP.trans hPQ))
      (fun j => (hRi j).trans (Real.exp_le_exp.mpr hPQ))
      (fun j => (hσi j).trans (Real.exp_le_exp.mpr hPQ))
      (fun j => (hdim.coefficients j).trans (hDP.trans hPQ))
    · exact (hdim.profile.trans (hDP.trans hPQ)).trans
        (by linarith only [Real.add_one_le_exp Q])
    · exact hL0
  have hPSeed : P ≤ Pseed := hPQ.trans (le_allocatedScaleLog hQ)
  obtain ⟨S, hS0S, hS, hgap⟩ := exists_allocatedWitnessScale_of_bounded_source
    B U basis R σ S0 hdim (hDP.trans hPSeed) hR hσ
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hPSeed))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hPSeed))
    hS0 hW hQw hWexp
  have hL0S : L0 ≤ S.value :=
    (selectedLayerSamplerScale_bounds B U basis R σ hR hσ L0).1.trans hS0S
  have hExpS : Real.exp (Lsum + Pmin) ≤ (S.value : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hL0S)
  refine ⟨S, ?_, ?_, hS, hgap⟩
  · intro i
    have hi : lengthLogs i ≤ Lsum :=
      Finset.single_le_sum (fun j _ => hLogs j) (Finset.mem_univ i)
    exact (Real.exp_le_exp.mpr (hi.trans (le_add_of_nonneg_right hPmin))).trans hExpS
  · exact Nat.cast_le.mp (hLmin.trans
      ((Real.exp_le_exp.mpr (le_add_of_nonneg_left hsum)).trans hExpS))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

structure PreparedUniformDegreeComparison
    {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    (s : ℕ) (D target Pk Prho Ptail pDetect : ℝ) where
  ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0
  hρ : ∀ partition, 0 < ρ partition
  hρ1 : ∀ partition, ρ partition ≤ 1
  hρlog : ∀ partition, (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho
  t : ℝ
  ht : 0 < t
  htone : t ≤ 1
  htinv : t⁻¹ ≤ Real.exp Ptail
  hs : AllocatedAffineCoveredComparison.{0,0,0,0,0,0,0} (G := G) B
    (fun j : Fin m => (Subtype.val :
      boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) → Finset (Fin (s + 1))))
    (Real.exp (-(pDetect + 1)))
    (Real.exp (-(target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5))) ρ t htone

theorem exists_preparedUniformDegreeComparison
    {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {pnum pDetect aDetect target Qstride : ℝ} (hm : 0 < m) (hs : s ≤ m)
    (hnum : 0 ≤ pnum)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) (hn : ∀ j, (n j : ℝ) ≤ pnum)
    (hblocks : ∀ b : LayerSamplerAxis I n,
      (boundedBooleanJetRows (Fin (s + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b))
    (hp : 0 ≤ pDetect) (ha : 0 ≤ aDetect) (htarget : 0 ≤ target) (hQ : 0 ≤ Qstride)
    (Cdetect nX : ℕ) :
    let D := allocatedComparisonDimension m pnum
    let gainLog := slicedDetectionGainLog s Cdetect
      (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
    let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
    let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
    let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
      (canonicalTransitionLip : ℝ) E (pDetect + 2) + 2
    let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E (pDetect + 2)
    0 ≤ Prho ∧ 0 ≤ Ptail ∧
      Nonempty (PreparedUniformDegreeComparison (G := G) B s D target Pk Prho Ptail pDetect) := by
  intro D gainLog Pk E Prho Ptail
  obtain ⟨hRho, hTail, ρ, hρ, t, ht, htone, htinv, hcomparison, _⟩ :=
    exists_primitive_early_canonical_slice_scales.{0,0} B hm hs hnum
      hvars hI hn hblocks htarget hp hp ha hQ Cdetect nX
  refine ⟨hRho, hTail, ⟨{
    ρ := ρ
    hρ := fun partition => (hρ partition).1
    hρ1 := fun partition => (hρ partition).2.1
    hρlog := fun partition => (hρ partition).2.2
    t := t
    ht := ht
    htone := htone
    htinv := htinv
    hs := ?_ }⟩⟩
  exact @hcomparison

private theorem uniformDegree_affineLength_density_fin
    (m nX : ℕ) (D P Prho Pk target p Qstride : ℝ) :
    Real.exp (allocatedAffineLengthLog m D P Prho Pk target (p + 1)
      (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤
    Real.exp (allocatedAffineLengthLog m D P Prho Pk target (p + 2)
      (((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride)) := by
  simp only [Fintype.card_fin]
  exact Real.exp_le_exp.mpr (allocatedAffineLengthLog_prepared_density m D P Prho Pk target p _)

private theorem uniformDegree_comparison_eta (target cost : ℝ) :
    Real.exp (-(target + cost + 5)) ≤ Real.exp (-(target + 1 + cost + 4)) := by
  apply Real.exp_le_exp.mpr
  linarith only

def PreparedUniformDegreeGeometryAt
    {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (s Cdetect nX : ℕ)
    (Bstruct Pscale D target Pk Prho Qstride pDetect pRadius aDetect gainLog : ℝ) : Prop :=
    Nonempty (AllocatedEarlyNativeSourceGeometryGeneral (B := B) (U := U)
      (basis := basis) (S := S) (s := s) (nX := nX)
      Bstruct Pscale D target Pk Prho Qstride pDetect
      (Real.toNNReal (Real.exp pRadius))) ∧
    ∀ α : ℝ, Real.exp (-aDetect) ≤ α →
      let gain := (Real.exp (-((5 * pDetect + 20) *
          Fintype.card (LayerSamplerVariables G I n B) + pDetect + 2)) * (α / 2)) *
        Real.exp (-((pDetect + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))
      Real.exp (-gainLog) ≤ gain ∧
        (scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊ (gain / 2) : ℝ) ≤
          Real.exp Pk ∧
        scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (pDetect + 1)⌉₊ (gain / 2) ≤ S.value

def PreparedUniformDegreeGeometryStatement (m : ℕ) (Cdetect : Fin (m + 1) → ℕ)
    {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {Bstruct pnum pDetect aDetect Qstride : ℝ} (nX : ℕ)
    (target : Fin (m + 1) → ℝ)
 : Prop :=
    let Aradius := Classical.choose (exists_preparedUniformEarlyRadius.{0,0,0,0} m)
    let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m Bstruct Bstruct
    let D := allocatedComparisonDimension m pnum
    let gainLog := fun s : Fin (m + 1) => slicedDetectionGainLog s.val (Cdetect s)
      (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
    let Pk := fun s : Fin (m + 1) =>
      scalarKernelLogarithmicBudget (Fin (s.val + 1)) G (gainLog s + pDetect + 4)
    let E := fun s : Fin (m + 1) => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : Fin (m + 1) => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect + 2) + 2
    let Ptail := fun s : Fin (m + 1) => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect + 2)
    let Tmod := fun s : Fin (m + 1) => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    pRadius ∈ Set.Icc 0 ((Bstruct + Bstruct + Aradius) ^ Aradius) ∧
    (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧ 0 ≤ D ∧
    (∀ s, 0 ≤ gainLog s ∧ 0 ≤ Pk s ∧ 0 ≤ Prho s ∧ 0 ≤ Ptail s) ∧
    ∃ t : Fin (m + 1) → ℝ,
      (∀ s, 0 < t s ∧ t s ≤ 1 ∧ (t s)⁻¹ ≤ Real.exp (Ptail s)) ∧
    ∀ {Qσ : ℝ}, 0 ≤ Qσ →
      let σ := preparedUniformDegreeTolerance t Qσ
      let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
      let lengthLogs := fun s : Fin (m + 1) => allocatedAffineLengthLog m D Pscale (Prho s) (Pk s)
        (target s) (pDetect + 2) (Tmod s)
      0 < σ ∧ σ ≤ 1 ∧ (∀ s, σ ≤ t s) ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ 0 ≤ Pscale ∧ D ≤ Pscale ∧
      (∀ s, Pk s ≤ Pscale) ∧
      ∀ (Lmin : ℕ) {W Qw Pmin : ℝ},
        1 ≤ W → 0 ≤ Qw → W ≤ Real.exp Qw →
        0 ≤ Pmin → (Lmin : ℝ) ≤ Real.exp Pmin →
      ∀ {J : Fin m → Type} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ),
      let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
      ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => σ),
        Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
        (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
          8 * (probabilityProfileLipschitz : ℝ) * W ≤
            (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
              ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
        ∀ s : Fin (m + 1), PreparedUniformDegreeGeometryAt B U basis S s.val (Cdetect s) nX
          Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride pDetect pRadius aDetect (gainLog s)

theorem exists_preparedUniformDegreeGeometry (m : ℕ) (Cdetect : Fin (m + 1) → ℕ)
    {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {Bstruct pnum pDetect aDetect Qstride : ℝ} (nX : ℕ)
    (target : Fin (m + 1) → ℝ)
    (hm : 0 < m) (hB : 0 ≤ Bstruct) (hnum : pnum ∈ Set.Icc 0 Bstruct)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) (hn : ∀ j, (n j : ℝ) ≤ pnum)
    (hblocks : ∀ s : Fin (m + 1), ∀ b : LayerSamplerAxis I n,
      (boundedBooleanJetRows (Fin (s.val + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b))
    (hp : 0 ≤ pDetect) (ha : 0 ≤ aDetect) (hQstride : 0 ≤ Qstride)
    (htarget : ∀ s, 0 ≤ target s) :
    PreparedUniformDegreeGeometryStatement (G := G) m Cdetect B
      (Bstruct := Bstruct) (pnum := pnum) (pDetect := pDetect)
      (aDetect := aDetect) (Qstride := Qstride) nX target := by
  delta PreparedUniformDegreeGeometryStatement
  intro Aradius pRadius R D gainLog Pk E Prho Ptail Tmod
  obtain ⟨hRadius, hR, hgeometry⟩ :=
    (Classical.choose_spec (exists_preparedUniformEarlyRadius.{0,0,0,0} m)).2 hB hB
  have hD : 0 ≤ D := (allocatedComparisonDimension_bounds m hnum.1).1
  have hD1 : 1 ≤ D := by
    have hd := (allocatedComparisonDimension_bounds m hnum.1).2.1
    have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    exact hm1.trans hd
  have hgain (s) : 0 ≤ gainLog s :=
    slicedDetectionGainLog_nonneg s.val (Cdetect s) _ hp hp ha
  have hPk (s) : 0 ≤ Pk s := by
    change 0 ≤ scalarKernelLogarithmicBudget (Fin (s.val + 1)) G (gainLog s + pDetect + 4)
    rw [scalarKernelLogarithmicBudget_eq]
    have := hgain s
    positivity
  have hcompare (s : Fin (m + 1)) : 0 ≤ Prho s ∧ 0 ≤ Ptail s ∧
      Nonempty (PreparedUniformDegreeComparison (G := G) B s.val D (target s)
        (Pk s) (Prho s) (Ptail s) pDetect) :=
    exists_preparedUniformDegreeComparison B hm (Nat.le_of_lt_succ s.isLt) hnum.1
      hvars hI hn (hblocks s) hp ha (htarget s) hQstride (Cdetect s) nX
  let data := fun s => Classical.choice (hcompare s).2.2
  let t := fun s => (data s).t
  have hTail (s) : 0 ≤ Ptail s := (hcompare s).2.1
  have hdimensions (s : Fin (m + 1)) : AllocatedComparisonDimensions (G := G) B
      (Fin (s.val + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (s.val + 1)) (j.val + 1) : Type)) D :=
    allocatedComparisonDimensions_of_primitive B
      (fun j => (Subtype.val : boundedBooleanJetRows (Fin (s.val + 1)) (j.val + 1) → Finset (Fin (s.val + 1))))
      (by simpa only [Fintype.card_fin] using Nat.succ_le_succ (Nat.le_of_lt_succ s.isLt))
      (fun _ => Subtype.val_injective) hnum.1 hvars hI hn
  refine ⟨hRadius, hR, hD, fun s => ⟨hgain s, hPk s, (hcompare s).1, hTail s⟩,
    t, fun s => ⟨(data s).ht, (data s).htone, (data s).htinv⟩, ?_⟩
  intro Qσ hQσ σ Pscale lengthLogs
  obtain ⟨hσ, hσone, hσt, hσexp, hσinv, hPscale, hTailScale⟩ :=
    preparedUniformDegreeTolerance_bounds t Ptail (fun s => (data s).ht)
      (fun s => (data s).htone) hTail (fun s => (data s).htinv)
      hQσ (add_nonneg hD hRadius.1)
  have hsum : 0 ≤ ∑ s, Ptail s := Finset.sum_nonneg (fun s _ => hTail s)
  have hDscale : D ≤ Pscale := by
    change D ≤ D + pRadius + ∑ s, Ptail s + Qσ
    linarith only [hRadius.1, hsum, hQσ]
  have hRadiusScale : pRadius ≤ Pscale := by
    change pRadius ≤ D + pRadius + ∑ s, Ptail s + Qσ
    linarith only [hD, hsum, hQσ]
  have hPkScale (s) : Pk s ≤ Pscale :=
    (prepared_affineProfileToleranceEnvelope_kernel_bound hm canonicalSublevelCutoffLip
      canonicalTransitionLip hD1 (hPk s) (htarget s) hp).trans (hTailScale s)
  have hF : 0 ≤ pDetect + 2 := by linarith only [hp]
  have hTmod (s) : 0 ≤ Tmod s :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (hPk s))
      (mul_nonneg (Nat.cast_nonneg _) hQstride)
  have hLengths (s) : 0 ≤ lengthLogs s :=
    (allocatedAffineLengthLog_bounds m hD hPscale (hcompare s).1 (hPk s)
      (htarget s) hF (hTmod s)).2.2.1
  refine ⟨hσ, hσone, hσt, hσexp, hσinv, hPscale, hDscale, hPkScale, ?_⟩
  intro Lmin W Qw Pmin hW hQw hWexp hPmin hLmin J _ U basis Pseed
  have hRi (j) : (R j)⁻¹ ≤ Real.exp Pscale :=
    (hR j).2.2.trans (Real.exp_le_exp.mpr hRadiusScale)
  obtain ⟨S, hlengths, hfloor, hS, hwidth⟩ :=
    exists_preparedUniformDegreeSampler B U basis R (fun _ => σ) lengthLogs
      (hdimensions ⟨0, Nat.succ_pos m⟩) hDscale (fun j => (hR j).1) (fun _ => hσ)
      hRi (fun _ => hσinv) hLengths hPmin hLmin hW hQw hWexp
  refine ⟨S, hfloor, hS, hwidth, ?_⟩
  intro s
  let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (s.val + 1)) (j.val + 1)
  let : ∀ j : Fin m, Nonempty (rowSets j) := fun j =>
    ⟨⟨∅, (mem_boundedBooleanJetRows (j.val + 1) ∅).mpr (by simp)⟩⟩
  obtain ⟨hrone, _, hT, hsource, hradius, hbudgets⟩ :=
    hgeometry (G := G) B rowSets
      (by simpa only [Fintype.card_fin] using Nat.succ_le_succ (Nat.le_of_lt_succ s.isLt))
      (hvars.trans hnum.2) (fun j => (hI j).trans hnum.2) (fun j => (hn j).trans hnum.2)
  have hcount (j : Fin m) : (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp Pscale :=
    ((add_le_add ((hdimensions s).coefficients j) (le_refl (1 : ℝ))).trans
      (Real.add_one_le_exp D)).trans (Real.exp_le_exp.mpr hDscale)
  refine ⟨?_, ?_⟩
  · refine allocatedEarlyNativeSourceGeometryGeneral_of_fields B U basis S
      Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride pDetect (Real.toNNReal (Real.exp pRadius))
      hPscale (fun j => (hR j).2.1.trans (Real.one_le_exp hPscale))
      hRi (fun _ => hσinv) hcount (hdimensions s) (hPk s) (hcompare s).1 (htarget s) ?_
      (Real.exp (-(E s))) (Real.exp_pos _).le ?_ (data s).ρ (data s).t (data s).htone
      ((data s).hs)
      (data s).hρ (data s).hρ1 (data s).hρlog (fun _ => hσt s)
      (allocatedIdealCoverSupport (G := G) B rowSets) hT hsource
      (allocatedProductIdealSiteRadius (G := G) B rowSets) hrone hradius hbudgets
      (fun j => (hR j).2.2.trans (Real.le_coe_toNNReal _))
    · exact (uniformDegree_affineLength_density_fin m nX D Pscale (Prho s) (Pk s)
        (target s) pDetect Qstride).trans (hlengths s)
    · exact uniformDegree_comparison_eta (target s) (D * ((m * 2 ^ (m + 1) : ℕ) * Pk s))
  · intro α hα gain
    have hcutoff := slicedDetection_kernel_cutoff_bound s.val (Cdetect s)
      (Fintype.card (LayerSamplerVariables G I n B)) G hp hp ha hα
    exact ⟨slicedDetectionGain_lower s.val (Cdetect s) _ hα, hcutoff,
      allocatedAffineLength_kernel_ready hm hD hPscale (hcompare s).1 (hPk s)
        (htarget s) hF (hTmod s) hcutoff (hlengths s)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

theorem preparedUniformDegreeGeometryAt_of_prescribedScale
    {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {Bstruct pnum pDetect aDetect Qstride Pscale target Prho Ptail : ℝ}
    (Cdetect nX : ℕ)
    (hm : 0 < m) (hs : s ≤ m)
    (hB : 0 ≤ Bstruct) (hnum : pnum ∈ Set.Icc 0 Bstruct)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pnum)
    (hn : ∀ j, (n j : ℝ) ≤ pnum)
    (hp : 0 ≤ pDetect) (ha : 0 ≤ aDetect) (hQstride : 0 ≤ Qstride)
    (htarget : 0 ≤ target) (hPrho : 0 ≤ Prho)
    (hPscale : 0 ≤ Pscale)
    (hDscale : allocatedComparisonDimension m pnum ≤ Pscale)
    (hRadiusScale : allocatedCommonProductRadiusLog m Bstruct Bstruct ≤ Pscale) :
    let D := allocatedComparisonDimension m pnum
    let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m Bstruct Bstruct
    let gainLog := slicedDetectionGainLog s Cdetect
      (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
    let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
    ∀ (comparison : PreparedUniformDegreeComparison (G := G) B s D target Pk Prho Ptail pDetect)
      {σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ),
      (∀ j, σ j ≤ comparison.t) →
      (∀ j, (σ j)⁻¹ ≤ Real.exp Pscale) →
      Real.exp (allocatedAffineLengthLog m D Pscale Prho Pk target (pDetect + 2)
        (((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride)) ≤ S.value →
      PreparedUniformDegreeGeometryAt B U basis S s Cdetect nX
        Bstruct Pscale D target Pk Prho Qstride pDetect pRadius aDetect gainLog := by
  intro D pRadius R gainLog Pk comparison σ S hσt hσinv hlength
  obtain ⟨hRadius, hR, hgeometry⟩ :=
    (Classical.choose_spec (exists_preparedUniformEarlyRadius.{0,0,0,0} m)).2 hB hB
  have hD : 0 ≤ D := (allocatedComparisonDimension_bounds m hnum.1).1
  have hgain : 0 ≤ gainLog := slicedDetectionGainLog_nonneg s Cdetect _ hp hp ha
  have hPk : 0 ≤ Pk := by
    change 0 ≤ scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
    rw [scalarKernelLogarithmicBudget_eq]
    positivity
  have hTmod : 0 ≤ ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) hPk)
      (mul_nonneg (Nat.cast_nonneg _) hQstride)
  have hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)) D :=
    allocatedComparisonDimensions_of_primitive B
      (fun j => (Subtype.val : boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) → Finset (Fin (s + 1))))
      (by simpa only [Fintype.card_fin] using Nat.succ_le_succ hs)
      (fun _ => Subtype.val_injective) hnum.1 hvars hI hn
  let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)
  let : ∀ j : Fin m, Nonempty (rowSets j) := fun j =>
    ⟨⟨∅, (mem_boundedBooleanJetRows (j.val + 1) ∅).mpr (by simp)⟩⟩
  obtain ⟨hrone, _, hT, hsource, hradius, hbudgets⟩ :=
    hgeometry (G := G) B rowSets
      (by simpa only [Fintype.card_fin] using Nat.succ_le_succ hs)
      (hvars.trans hnum.2) (fun j => (hI j).trans hnum.2) (fun j => (hn j).trans hnum.2)
  have hRi (j) : (R j)⁻¹ ≤ Real.exp Pscale :=
    (hR j).2.2.trans (Real.exp_le_exp.mpr hRadiusScale)
  have hcount (j : Fin m) : (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp Pscale :=
    ((add_le_add (hdimensions.coefficients j) (le_refl (1 : ℝ))).trans
      (Real.add_one_le_exp D)).trans (Real.exp_le_exp.mpr hDscale)
  refine ⟨?_, ?_⟩
  · refine allocatedEarlyNativeSourceGeometryGeneral_of_fields B U basis S
      Bstruct Pscale D target Pk Prho Qstride pDetect (Real.toNNReal (Real.exp pRadius))
      hPscale (fun j => (hR j).2.1.trans (Real.one_le_exp hPscale))
      hRi hσinv hcount hdimensions hPk hPrho htarget ?_
      (Real.exp (-(target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5)))
      (Real.exp_pos _).le ?_ comparison.ρ comparison.t comparison.htone comparison.hs
      comparison.hρ comparison.hρ1 comparison.hρlog hσt
      (allocatedIdealCoverSupport (G := G) B rowSets) hT hsource
      (allocatedProductIdealSiteRadius (G := G) B rowSets) hrone hradius hbudgets
      (fun j => (hR j).2.2.trans (Real.le_coe_toNNReal _))
    · apply le_trans _ hlength
      simp only [Fintype.card_fin]
      exact Real.exp_le_exp.mpr
        (allocatedAffineLengthLog_prepared_density m D Pscale Prho Pk target pDetect _)
    · apply Real.exp_le_exp.mpr
      linarith only
  · intro α hα gain
    have hcutoff := slicedDetection_kernel_cutoff_bound s Cdetect
      (Fintype.card (LayerSamplerVariables G I n B)) G hp hp ha hα
    exact ⟨slicedDetectionGain_lower s Cdetect _ hα, hcutoff,
      allocatedAffineLength_kernel_ready hm hD hPscale hPrho hPk htarget
        (by linarith only [hp]) hTmod hcutoff hlength⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section Consumer

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog u pModel
local notation "qDetect" => allocatedModelTestLog u pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
variable (α τ : ℝ)
variable {P : ℝ}

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "jetHaar" => Measure.pi (fun j =>
  @Measure.pi (selectedRows j) _ (fullBooleanRowSetFintype (s + 1) (Fin.val j + 1)) _
    (fun _ : selectedRows j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

structure PreparedUniformDegreeDirectScalarBounds
    (m s nX nVars : ℕ) (Cdetect : ℕ)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius u pModel pSlice : ℝ) : Prop where
  master_nonneg : 0 ≤ Pmaster
  late : Pmaster ≤ Plate
  chart_master : Pchart ≤ Pmaster
  dimension_master : D ≤ Pmaster
  radius_master : pRadius ≤ Pmaster
  scale_late : Pscale ≤ Plate
  kernel_scale : Pk ≤ Pscale
  kernel_master : Pk ∈ Set.Icc 0 Pmaster
  stride_master : Qstride ∈ Set.Icc 0 Pmaster
  detect_master : allocatedModelTestLog u pModel ∈ Set.Icc 0 Pmaster
  ambient_master : (nX : ℝ) ≤ Pmaster
  u_master : u ∈ Set.Icc 0 Pmaster
  model_master : pModel ∈ Set.Icc 0 Pmaster
  slice_model : pSlice ≤ pModel
  count_model : (nVars : ℝ) ≤ Real.exp pModel
  rho_master : Prho ∈ Set.Icc 0 Pmaster
  target_master : target ∈ Set.Icc 0 Pmaster
  gain_master : pGain ∈ Set.Icc 0 Pmaster
  coarse_master : pGain + 32 ≤ Pmaster
  coarse_lower : pGain + 32 ≤ coarseTarget
  coarse_late : coarseTarget ≤ Plate
  physical_master : Pphysical ∈ Set.Icc 0 Pmaster
  degree_physical : ((m + 1 : ℕ) : ℝ) ≤ Pphysical
  detector_physical : ((s + 2 : ℕ) : ℝ) ≤ Pphysical
  variables_physical : (nVars : ℝ) ≤ Pphysical
  ambient_physical : (nX : ℝ) ≤ Pphysical
  kernel_physical : Pk ≤ Pphysical
  stride_physical : Qstride ≤ Pphysical
  gain_log : slicedDetectionGainLog s Cdetect nVars
    (allocatedModelTestLog u pModel) (allocatedModelTestLog u pModel)
    (2 * u + 4 * pModel + 7) ≤ pGain
  precision : pGain + 32 + coefficientErrorSpatialLog Pphysical + 8 ≤ target
  xi_late : 2 * (spatialPrimitiveEnvelope Pphysical coarseTarget 0 +
    spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical coarseTarget 0)) + 4 ≤ Plate

include hb o bW μ ν μrows hR hσ in

theorem preparedUniformDegreeDirectSource_of_geometry (hsm : s ≤ m)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B))
      (sampledSupportedSlicedDetectionConstant s Pdetect)
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius u pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s
      (sampledSupportedSlicedDetectionConstant s Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride pDetect pRadius
      (2 * u + 4 * pModel + 7) pGain)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσone : ∀ j, σ j ≤ 1)
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hcapacity : (s + 1) * (s + 3) ≤ Fintype.card G)
    (hαlower : Real.exp (-(2 * u + 4 * pModel + 7)) ≤ α) (hαone : α ≤ 1) :
    PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  obtain ⟨⟨geometry⟩, hgainKernel⟩ := geometryAt
  intro hstride hstrideBound Cchart hCchart hCchartBound hchart Cforward hforward
    hForward hVtail hVactual _hprofile hcutoff hτfree hτfreeInv hτfreeHalf hτfreeDim
    r W ξn hξn hξle hξInvLate hW cells poly hp hmem Rrank hNlarge hrank hRankLarge V
    hcells bases Z
  have hExpMaster : Real.exp Pchart ≤ Real.exp Pmaster :=
    Real.exp_le_exp.mpr scalar.chart_master
  have hRiMaster (j) := (hRinv j).trans (Real.exp_le_exp.mpr scalar.radius_master)
  have hσLate (j) := (geometry.hσi j).trans (Real.exp_le_exp.mpr scalar.scale_late)
  have hτInvMaster : τ⁻¹ ≤ Real.exp Pmaster :=
    hτfreeInv.trans (Real.exp_le_exp.mpr scalar.physical_master.2)
  have hξone := hξle.trans (preparedModularCanonicalDetector_narrow_width_le_one (Fin nX)
    (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
    (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
      Pdetect pDetect pDetect α) Pphysical coarseTarget)
  obtain ⟨hNpos, hbases, hbox, hmass, hnormalizer, hmargin⟩ :=
    preparedModularGeneralDetector_late_positive_bounds B U basis S hb o μ ν hR hσ
      hσone Cforward Vtail hforward hVactual Cchart hCchart hchart
      (geometry.hbudgets Cchart hCchart hCchartBound).1 scalar.master_nonneg scalar.late
      geometry.hdimensions scalar.dimension_master scalar.ambient_master
      hRiMaster hσLate hSLate
      (fun j => (hForward j).trans hExpMaster) (fun j => (hVtail j).trans hExpMaster)
      poly hp hmem stride hstride
      (fun i => (hstrideBound i).trans (Real.exp_le_exp.mpr scalar.stride_master.2))
      hτfree hτInvMaster hτfreeHalf hτfreeDim hξn hξone hξInvLate
      N hrank cells hcells hNlarge hRankLarge
  let : ∀ i, NeZero (N i) := fun i => ⟨(hNpos i).ne'⟩
  have hMk := (hgainKernel α hαlower).2
  have hMkPk : (allocatedDetectedKernelCutoff s G
      (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect pDetect α : ℝ)
      ≤ Real.exp Pk := hMk.1
  have hMkP := hMkPk.trans (Real.exp_le_exp.mpr scalar.kernel_scale)
  have hKMaster : (Real.toNNReal (Real.exp pRadius) : ℝ) ≤ Real.exp Pmaster := by
    rw [Real.coe_toNNReal (Real.exp pRadius) (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr scalar.radius_master
  have consumer := preparedModularGeneralDirectDetectionFreeTrimSharedWidthInterface_of_geometry
    (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S) (P := Pscale)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (α := α) (τ := τ)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (μ := μ) (ν := ν) (μrows := μrows)
    hsm Pchart D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
    (Real.toNNReal (Real.exp pRadius)) geometry
  have completed := consumer scalar.late scalar.master_nonneg scalar.dimension_master
    scalar.kernel_master scalar.stride_master scalar.detect_master scalar.ambient_master
    hRone hRiMaster hσLate hSLate hKMaster (hcutoff.trans hExpMaster) hMkP hMkPk
    hstride hstrideBound Cchart hCchart hCchartBound hchart Cforward hforward
    (fun j => (hForward j).trans hExpMaster) (fun j => (hVtail j).trans hExpMaster) hVactual
    hBa hBi scalar.u_master scalar.model_master scalar.slice_model scalar.count_model hαlower hαone
    scalar.rho_master scalar.target_master scalar.gain_master scalar.coarse_master
    scalar.coarse_lower scalar.coarse_late scalar.physical_master scalar.degree_physical
    scalar.detector_physical scalar.variables_physical scalar.ambient_physical
    scalar.kernel_physical scalar.stride_physical scalar.gain_log scalar.precision scalar.xi_late
    hτfree hτfreeInv hξn hξle hξInvLate
  refine ⟨hNpos, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path pathLaw sides Sites e Tests _ Ldetect _ _ dims _ _ _ _
    Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense hcount hcomplexity hnorm
    budget'
  exact completed cells poly hp hmem hNlarge hrank hRankLarge hcells hbases hmass
    hnormalizer.2.2.1 Ddetect Vdetect slices cdetect stepdetect Hdetect hstep hboxDetect hdense hcount
    hcomplexity hnorm hcapacity hMk.2

end Consumer
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

noncomputable def preparedUniformDegreeDirectMaster (m : ℕ)
    (Pchart D pRadius u pModel Qstride Pphysical : ℝ)
    (Prho target gainLog : Fin (m + 1) → ℝ) : ℝ :=
  Pchart + D + pRadius + u + pModel + allocatedModelTestLog u pModel + Qstride +
    Pphysical + ∑ s, (Prho s + target s + gainLog s + 32)

noncomputable def preparedUniformDegreeDirectCoarse (m : ℕ)
    (gainLog : Fin (m + 1) → ℝ) (requestedCoarse : ℝ) : ℝ :=
  max (∑ s, (gainLog s + 32)) requestedCoarse

noncomputable def preparedUniformDegreeDirectLate
    (Pmaster Pscale Pphysical coarseTarget extraLate : ℝ) : ℝ :=
  max Pmaster (max Pscale (max coarseTarget (max
    (2 * (spatialPrimitiveEnvelope Pphysical coarseTarget 0 +
      spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical coarseTarget 0)) + 4)
    extraLate)))

theorem preparedUniformDegreeDirectScalarBounds_explicit
    (m : ℕ) (Cdetect : Fin (m + 1) → ℕ) (G : Type) [Fintype G]
    (nX count : ℕ) (Pchart D pRadius u pModel pSlice Qstride Pscale
      requestedCoarse extraLate : ℝ) (Prho : Fin (m + 1) → ℝ)
    (hchart : 0 ≤ Pchart) (hD : 0 ≤ D) (hradius : 0 ≤ pRadius)
    (hu : 0 ≤ u) (hmodel : 0 ≤ pModel) (hstride : 0 ≤ Qstride)
    (hrho : ∀ s, 0 ≤ Prho s) (hslice : pSlice ≤ pModel)
    (hcount : (count : ℝ) ≤ Real.exp pModel) :
    let pDetect := allocatedModelTestLog u pModel
    let gainLog := fun s : Fin (m + 1) =>
      slicedDetectionGainLog s.val (Cdetect s) count pDetect pDetect
        (2 * u + 4 * pModel + 7)
    let Pk := fun s : Fin (m + 1) =>
      scalarKernelLogarithmicBudget (Fin (s.val + 1)) G (gainLog s + pDetect + 4)
    let Pphysical : ℝ := ((m + 2 : ℕ) : ℝ) + nX + count + Qstride + ∑ s, Pk s
    let target := fun s : Fin (m + 1) =>
      gainLog s + 40 + coefficientErrorSpatialLog Pphysical
    let Pmaster := preparedUniformDegreeDirectMaster m Pchart D pRadius u pModel
      Qstride Pphysical Prho target gainLog
    let coarseTarget := preparedUniformDegreeDirectCoarse m gainLog requestedCoarse
    let Plate := preparedUniformDegreeDirectLate Pmaster Pscale Pphysical coarseTarget extraLate
    (∀ s, Pk s ≤ Pscale) →
    ∀ s : Fin (m + 1), PreparedUniformDegreeDirectScalarBounds m s.val nX count
      (Cdetect s) Pchart Pscale D (target s) (Pk s) (Prho s) Qstride Pmaster Plate
      (gainLog s) Pphysical coarseTarget pRadius u pModel pSlice := by
  intro pDetect gainLog Pk Pphysical target Pmaster coarseTarget Plate hkernelScale
  have hp : 0 ≤ pDetect := by dsimp only [pDetect, allocatedModelTestLog]; positivity
  have ha : 0 ≤ 2 * u + 4 * pModel + 7 := by positivity
  have hg (s) : 0 ≤ gainLog s :=
    slicedDetectionGainLog_nonneg s.val (Cdetect s) count hp hp ha
  have hk (s) : 0 ≤ Pk s := by
    dsimp only [Pk]
    rw [scalarKernelLogarithmicBudget_eq]
    have := hg s
    positivity
  have hkSum0 : 0 ≤ ∑ s, Pk s := Finset.sum_nonneg (fun s _ => hk s)
  have hkSum (s) : Pk s ≤ ∑ t, Pk t :=
    Finset.single_le_sum (fun t _ => hk t) (Finset.mem_univ s)
  have hphysEq : Pphysical = (m : ℝ) + 2 + nX + count + Qstride + ∑ s, Pk s := by
    simp only [Pphysical, Nat.cast_add, Nat.cast_ofNat]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hnX0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg nX
  have hcount0 : (0 : ℝ) ≤ count := Nat.cast_nonneg count
  have hphysical0 : 0 ≤ Pphysical := by
    linarith only [hphysEq, hm0, hnX0, hcount0, hstride, hkSum0]
  have hkernelPhysical (s) : Pk s ≤ Pphysical := by
    linarith only [hphysEq, hm0, hnX0, hcount0, hstride, hkSum s]
  have herror0 := coefficientErrorSpatialLog_nonneg hphysical0
  have ht (s) : 0 ≤ target s := by
    dsimp only [target]
    have := hg s
    positivity
  let total := ∑ s : Fin (m + 1), (Prho s + target s + gainLog s + 32)
  have hentry (s) : 0 ≤ Prho s + target s + gainLog s + 32 := by
    have := hrho s
    have := ht s
    have := hg s
    positivity
  have htotal0 : 0 ≤ total := Finset.sum_nonneg (fun s _ => hentry s)
  have htotal (s) : Prho s + target s + gainLog s + 32 ≤ total :=
    Finset.single_le_sum (fun s _ => hentry s) (Finset.mem_univ s)
  have hmasterEq : Pmaster =
      Pchart + D + pRadius + u + pModel + pDetect + Qstride + Pphysical + total := rfl
  have hmaster0 : 0 ≤ Pmaster := by
    linarith only [hmasterEq, hchart, hD, hradius, hu, hmodel, hp, hstride,
      hphysical0, htotal0]
  have hphysicalMaster : Pphysical ≤ Pmaster := by
    linarith only [hmasterEq, hchart, hD, hradius, hu, hmodel, hp, hstride, htotal0]
  have htotalMaster : total ≤ Pmaster := by
    linarith only [hmasterEq, hchart, hD, hradius, hu, hmodel, hp, hstride, hphysical0]
  have hlate : Pmaster ≤ Plate := le_max_left _ _
  have hscaleLate : Pscale ≤ Plate :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hcoarseLate : coarseTarget ≤ Plate :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hxiLate : 2 * (spatialPrimitiveEnvelope Pphysical coarseTarget 0 +
      spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical coarseTarget 0)) + 4
      ≤ Plate :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  intro s
  have hsm : s.val ≤ m := Nat.le_of_lt_succ s.isLt
  have hsmReal : (s.val : ℝ) ≤ m := by exact_mod_cast hsm
  have hlocalMaster := (htotal s).trans htotalMaster
  have hgainEntry (t : Fin (m + 1)) : (0 : ℝ) ≤ gainLog t + 32 := by
    have := hg t
    positivity
  have hcoarseSum : gainLog s + 32 ≤ ∑ t, (gainLog t + 32) :=
    Finset.single_le_sum (fun t _ => hgainEntry t) (Finset.mem_univ s)
  refine {
    master_nonneg := hmaster0
    late := hlate
    chart_master := ?_
    dimension_master := ?_
    radius_master := ?_
    scale_late := hscaleLate
    kernel_scale := hkernelScale s
    kernel_master := ⟨hk s, (hkernelPhysical s).trans hphysicalMaster⟩
    stride_master := ⟨hstride, ?_⟩
    detect_master := ⟨hp, ?_⟩
    ambient_master := le_trans ?_ hphysicalMaster
    u_master := ⟨hu, ?_⟩
    model_master := ⟨hmodel, ?_⟩
    slice_model := hslice
    count_model := hcount
    rho_master := ⟨hrho s, ?_⟩
    target_master := ⟨ht s, ?_⟩
    gain_master := ⟨hg s, ?_⟩
    coarse_master := ?_
    coarse_lower := hcoarseSum.trans (le_max_left _ _)
    coarse_late := hcoarseLate
    physical_master := ⟨hphysical0, hphysicalMaster⟩
    degree_physical := ?_
    detector_physical := ?_
    variables_physical := ?_
    ambient_physical := ?_
    kernel_physical := hkernelPhysical s
    stride_physical := ?_
    gain_log := le_rfl
    precision := ?_
    xi_late := hxiLate }
  · linarith only [hmasterEq, hD, hradius, hu, hmodel, hp, hstride, hphysical0, htotal0]
  · linarith only [hmasterEq, hchart, hradius, hu, hmodel, hp, hstride, hphysical0, htotal0]
  · linarith only [hmasterEq, hchart, hD, hu, hmodel, hp, hstride, hphysical0, htotal0]
  · linarith only [hmasterEq, hchart, hD, hradius, hu, hmodel, hp, hphysical0, htotal0]
  · linarith only [hmasterEq, hchart, hD, hradius, hu, hmodel, hstride, hphysical0, htotal0]
  · linarith only [hphysEq, hm0, hcount0, hstride, hkSum0]
  · linarith only [hmasterEq, hchart, hD, hradius, hmodel, hp, hstride, hphysical0, htotal0]
  · linarith only [hmasterEq, hchart, hD, hradius, hu, hp, hstride, hphysical0, htotal0]
  · linarith only [hlocalMaster, ht s, hg s]
  · linarith only [hlocalMaster, hrho s, hg s]
  · linarith only [hlocalMaster, hrho s, ht s]
  · linarith only [hlocalMaster, hrho s, ht s]
  · simp only [Nat.cast_add, Nat.cast_one]
    linarith only [hphysEq, hnX0, hcount0, hstride, hkSum0]
  · simp only [Nat.cast_add, Nat.cast_ofNat]
    linarith only [hphysEq, hsmReal, hnX0, hcount0, hstride, hkSum0]
  · linarith only [hphysEq, hm0, hnX0, hstride, hkSum0]
  · linarith only [hphysEq, hm0, hcount0, hstride, hkSum0]
  · linarith only [hphysEq, hm0, hnX0, hcount0, hkSum0]
  · dsimp only [target]
    linarith only

theorem preparedUniformDegreeDirectLate_extra
    (Pmaster Pscale Pphysical coarseTarget extraLate : ℝ) :
    extraLate ≤ preparedUniformDegreeDirectLate Pmaster Pscale Pphysical coarseTarget extraLate :=
  (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))

theorem preparedUniformDegreeDirectCoarse_requested
    (m : ℕ) (gainLog : Fin (m + 1) → ℝ) (requestedCoarse : ℝ) :
    requestedCoarse ≤ preparedUniformDegreeDirectCoarse m gainLog requestedCoarse :=
  le_max_right _ _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped Classical BigOperators NNReal

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m s nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (selection : Fin (s + 1) ↪ G) (Pdetect : Polynomial ℕ)
variable {Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical
  coarseTarget pRadius u pModel pSlice α : ℝ}

local notation "pDetect" => allocatedModelTestLog u pModel
local notation "canonicalWidth" => normalizedTupleNarrowWidth (Fin nX)
  (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
  (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
    Pdetect pDetect pDetect α) Pphysical coarseTarget

theorem preparedUniformDegreeCanonicalWidth_inv
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B))
      (sampledSupportedSlicedDetectionConstant s Pdetect)
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius u pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s
      (sampledSupportedSlicedDetectionConstant s Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride pDetect pRadius
      (2 * u + 4 * pModel + 7) pGain)
    (hαlower : Real.exp (-(2 * u + 4 * pModel + 7)) ≤ α) :
    canonicalWidth⁻¹ ≤ Real.exp Plate := by
  have hMk := (geometryAt.2 α hαlower).2.1
  have hCoarse : 0 ≤ coarseTarget := by
    linarith only [scalar.gain_master.1, scalar.coarse_lower]
  have hwidth := preparedModularDetector_narrow_width B selection scalar.physical_master.1
    hCoarse (hMk.trans (Real.exp_le_exp.mpr scalar.kernel_physical))
    scalar.detector_physical scalar.variables_physical scalar.ambient_physical
  exact hwidth.2.trans (Real.exp_le_exp.mpr scalar.xi_late)

theorem preparedUniformDegreeSharedWidth
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B))
      (sampledSupportedSlicedDetectionConstant s Pdetect)
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius u pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s
      (sampledSupportedSlicedDetectionConstant s Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride pDetect pRadius
      (2 * u + 4 * pModel + 7) pGain)
    (hαlower : Real.exp (-(2 * u + 4 * pModel + 7)) ≤ α) :
    let ξ := Real.exp (-Plate)
    0 < ξ ∧ ξ⁻¹ = Real.exp Plate ∧ ξ ≤ canonicalWidth := by
  have hinv := preparedUniformDegreeCanonicalWidth_inv B U basis S selection Pdetect
    scalar geometryAt hαlower
  have hpositive := normalizedTupleNarrowWidth_pos (Fin nX)
    (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
    (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
      Pdetect pDetect pDetect α) Pphysical coarseTarget
  have h := sharedWidthPreparedChoice (fun _ : Unit => canonicalWidth) Plate
    (fun _ => hpositive) (fun _ => hinv)
  exact ⟨h.1, h.2.1, h.2.2 ()⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedUniformDegreeDirectMaster_budget (m A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {P Pchart D pRadius u pModel Qstride Pphysical : ℝ}
      {Prho target gainLog : Fin (m + 1) → ℝ},
      0 ≤ P →
      Pchart ≤ (P + A) ^ A → D ≤ (P + A) ^ A → pRadius ≤ (P + A) ^ A →
      u ≤ (P + A) ^ A → pModel ≤ (P + A) ^ A →
      Qstride ≤ (P + A) ^ A → Pphysical ≤ (P + A) ^ A →
      (∀ s, Prho s ≤ (P + A) ^ A) → (∀ s, target s ≤ (P + A) ^ A) →
      (∀ s, gainLog s ≤ (P + A) ^ A) →
      preparedUniformDegreeDirectMaster m Pchart D pRadius u pModel Qstride Pphysical
        Prho target gainLog ≤ (P + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let b := (X + Polynomial.C A) ^ A
  let poly := 14 * b + 12 + Polynomial.C (m + 1) * (3 * b + 32)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro P Pchart D pRadius u pModel Qstride Pphysical Prho target gainLog
    hP hchart hD hradius hu hmodel hstride hphysical hrho htarget hgain
  have hsum : (∑ s, (Prho s + target s + gainLog s + 32)) ≤
      ((m + 1 : ℕ) : ℝ) * (3 * (P + A) ^ A + 32) := by
    calc
      _ ≤ ∑ _s : Fin (m + 1), (3 * (P + A) ^ A + 32) := by
        apply Finset.sum_le_sum
        intro s _
        linarith only [hrho s, htarget s, hgain s]
      _ = _ := by simp [mul_add]
  have htotal : preparedUniformDegreeDirectMaster m Pchart D pRadius u pModel Qstride
      Pphysical Prho target gainLog ≤
      14 * (P + A) ^ A + 12 + ((m + 1 : ℕ) : ℝ) * (3 * (P + A) ^ A + 32) := by
    unfold preparedUniformDegreeDirectMaster allocatedModelTestLog
    linarith only [hchart, hD, hradius, hu, hmodel, hstride, hphysical, hsum]
  apply htotal.trans
  simpa [poly, X, b, Polynomial.eval₂_pow] using hbound P hP

end Erdos3.VectorPolynomial

end

end OAI
