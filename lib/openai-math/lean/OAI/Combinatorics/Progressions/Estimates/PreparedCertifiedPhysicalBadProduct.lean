import OAI.Combinatorics.Progressions.Dynamics.PreparedBadProductInputBudget
import OAI.Combinatorics.Progressions.Estimates.PreparedEnlargedModularAllocation
import OAI.Combinatorics.Progressions.Geometry.PreparedSpatialWitnessWidth
import OAI.Combinatorics.Progressions.Linear.AllocatedPhysicalCertifiedRankWitnessLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem selectedResidueDensityPMF_stride_quantitative_badPrimeProduct
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    (S : Finset ℕ) (A : ℕ → ℕ) (bad : ℕ → ℕ → (K × I → ℤ) → Prop)
    {stride Qs Q : ℕ} (hstride : 0 < stride)
    (hprime : ∀ p ∈ S, p.Prime) (hQs : 2 ≤ Qs)
    (hQ : 1 ≤ Q) (hdepth : ∀ p ∈ S, p ^ A p ≤ Q)
    {E Vlog : ℝ} (hE : 0 ≤ E) (hVlog : 0 ≤ Vlog) (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hjoint :
      let R := quantitativeBadPrimeRadius E
      let η := Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))
      ∀ (T : Finset ℕ), T ⊆ S → ∀ a : ℕ → ℕ,
        (∀ p ∈ T, 0 < a p ∧ a p ≤ A p ∧ Qs ≤ p ^ a p ∧
          2 * stride.factorization p < a p) →
        (∏ p ∈ T, p ^ a p) ≤ max Q (R ^ 2) →
        (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
          (if ∀ p ∈ T, bad p (a p) x then 1 else 0)) ≤
          1 / ((∏ p ∈ T, p ^ a p : ℕ) : ℝ) ^ 10 + η) :
    let R := quantitativeBadPrimeRadius E
    let η := Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))
    0 < R ∧ (R : ℝ) ≤ Real.exp (E + 3) ∧ 0 < η ∧
      ((max Q (R ^ 2) : ℕ) : ℝ) ≤ Real.exp (Vlog + 2 * E + 6) ∧
      η⁻¹ ≤ Real.exp (Vlog + 3 * E + 8) ∧
      (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal *
        (if stride ^ 2 * (smallPrimePowerCorrection Qs * R) <
          ∏ p ∈ S, p ^ largestTestedBadDepth A bad p x then 1 else 0)) ≤ Real.exp (-E) := by
  obtain ⟨hR, hRexp, _⟩ := quantitativeBadPrimeRadius_bounds hE
  obtain ⟨hη, herror⟩ := quantitativeBadPrimeRadius_error hE Q hQ
  obtain ⟨hwitness, haccuracy⟩ := quantitativeBadPrimeRadius_witness_budget hE hVlog Q hQexp
  refine ⟨hR, hRexp, hη, hwitness, ?_, ?_⟩
  · simpa only [one_div] using haccuracy
  · exact (selectedResidueDensityPMF_stride_badPrimeProduct
      modulus G V hV hZ D hD0 hD S A bad hstride hprime hQs hQ hR hdepth hη.le hjoint).trans herror

end Erdos3

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

variable (Elog Vlog : ℝ) (Q : ℕ)
local notation "κ" => physicalBadProductAccuracy Elog Vlog
local notation "Rbad" => quantitativeBadPrimeRadius Elog
local notation "cap" => (max Q (Rbad ^ 2) : ℕ)
local notation "inactive" => allocatedGridAxis (I := I) U b S.value

include bW hC hV in

theorem exists_allocated_physical_certified_bad_product
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog) (hQ : 1 ≤ Q)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hmpos : 0 < m)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    {P : ℝ} (hP : 0 ≤ P) (hmP : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hbudgetP : Vlog + 3 * Elog + 16 ≤ P)
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
    {Ps ρ Rs Smax : ℝ} (hPs : 0 ≤ Ps) (hX : (Fintype.card X : ℝ) ≤ Ps)
    (hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Ps)
    (hbudgetPs : Vlog + 3 * Elog + 16 ≤ Ps)
    (hρ : 0 < ρ) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp Ps) (hstrideMax : ∀ x, ((stride x * cap : ℕ) : ℝ) ≤ Smax)
    (H : X → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hcells : cells.Nonempty)
    {L D : ℕ}
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
    (rankC : ℝ) (hrankC : 0 ≤ rankC)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    (hL : ⌈2 * (rankC + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride width z)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * (cap : ℝ) ≤
      allocatedSpatialRankSelectedWidth B U b S spatial stride width j)
    (hresidueError : (∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (cap : ℝ) /
      allocatedSpatialRankSelectedWidth B U b S spatial stride width j) ≤ κ) :
    let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
    ∃ read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ,
      (∀ z, allocatedReadNoise (read z) = z) ∧
      (∀ z, Dphysical z ≠ 0 →
        ∀ (primes : Finset ℕ) (hne : ∀ p : primes, NeZero p.val),
          letI := hne
          ∀ (depth : ℕ → ℕ) (q : ℕ) (hq : 0 < q),
            letI : NeZero q := ⟨hq.ne'⟩
            ∀ hdiv : ∀ p : primes, p.val ^ depth p.val ∣ q,
              coefficientDeckChartEvent U bW b hb o q
                (allocatedChartResiduePrimePowerWitness inactive rankC primes depth q hdiv
                  (fun v => (z v : ZMod q)))
                (affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))) ↔
              ∀ p : primes, allocatedActualModulusBad inactive spatial kernel block rankC
                (p.val ^ depth p.val) (read z)) ∧
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 3 * κ ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      0 < Rbad ∧ (Rbad : ℝ) ≤ Real.exp (Elog + 3) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
          (∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
            (if (∏ x, stride x) ^ 2 *
              (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * Rbad) <
                ∏ p ∈ primes, p ^ largestTestedBadDepth depth
                  (fun p a z => allocatedActualPrimeBad inactive spatial kernel block primes rankC p a (read z)) p z
              then (1 : ℝ) else 0)) ≤ Real.exp (-Elog) := by
  dsimp only
  obtain ⟨hκ, hκinv, hsmallError, _, herrors⟩ :=
    physicalBadProductAccuracy_budget hElog hVlog Q hQ hQexp
  obtain ⟨hcapexp, _⟩ := quantitativeBadPrimeRadius_witness_budget hElog hVlog Q hQexp
  have hcap : 0 < cap := lt_of_lt_of_le (by omega : 0 < Q) (le_max_left _ _)
  have hcapP : (cap : ℝ) ≤ Real.exp P := hcapexp.trans
    (Real.exp_le_exp.mpr (by linarith))
  have hcapPs : (cap : ℝ) ≤ Real.exp Ps := hcapexp.trans
    (Real.exp_le_exp.mpr (by linarith))
  have hκP : κ⁻¹ ≤ Real.exp P := by rw [hκinv]; exact Real.exp_le_exp.mpr hbudgetP
  have hκPs : 1 / κ ≤ Real.exp Ps := by
    rw [one_div, hκinv]; exact Real.exp_le_exp.mpr hbudgetPs
  obtain ⟨hD0, hZ, hDpos, read, hnoise, hread, hmass, hlower, hupper, hcompare⟩ :=
    exists_allocated_physical_certified_rank_witness_law B U bW b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall cap hcap hP hmP hK hRP hσP hcount hI hn hJ hAP hLP
      hCP hVP hcapP hκ hκP μ ν poly hp hm hPs hX hframe hcapPs hκ hρ hκPs hρPs stride hstride
      hSmax hSmaxPs hstrideMax H hsize hrank hRs cells hcells inactive spatial kernel block
      rankC width hwidth hwide hfreqPs hmassPs hsmallError
  have hRbad := quantitativeBadPrimeRadius_bounds hElog
  refine ⟨hD0, hZ, hDpos, read, hnoise, hread, ?_, hlower, hupper, hRbad.1, hRbad.2.1, ?_⟩
  · linarith
  intro primes hprime
  let : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
  intro depth hdepth
  let bad := fun p a z => allocatedActualPrimeBad inactive spatial kernel block primes rankC p a (read z)
  have hstrideprod : 0 < ∏ x, stride x := Finset.prod_pos (fun x _ => hstride x)
  apply (selectedResidueDensityPMF_stride_quantitative_badPrimeProduct stride cells width hwidth
    hZ _ hD0 hDpos primes depth bad hstrideprod hprime
    (modularCoefficientPrimeThreshold_two_le m) hQ hdepth hElog hVlog hQexp ?_).2.2.2.2.2
  dsimp only
  intro T hT a ha hbound
  let hTprime : ∀ p ∈ T, p.Prime := fun p hp => hprime p (hT hp)
  let hTne : ∀ p : T, NeZero p.val := fun p => ⟨(hTprime p.val p.property).ne_zero⟩
  let := hTne
  let M : ℕ := ∏ p ∈ T, p ^ a p
  have hM : 0 < M := Finset.prod_pos (fun p hp => pow_pos (hTprime p hp).pos _)
  let : NeZero M := ⟨hM.ne'⟩
  have hdiv : ∀ p : T, p.val ^ a p.val ∣ M :=
    fun p => Finset.dvd_prod_of_mem (fun p => p ^ a p) p.property
  have hprod : (∏ p : T, p.val ^ a p.val) = M := by
    exact (Finset.prod_subtype T (fun _ => Iff.rfl) (fun p => p ^ a p)).symm
  have hMbound : (M : ℝ) ≤ cap := Nat.cast_le.mpr hbound
  have hlargeM : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : T, p.val ^ a p.val) ≤ allocatedSpatialRankSelectedWidth B U b S spatial stride width j := by
    intro j
    rw [hprod]
    exact (mul_le_mul_of_nonneg_left hMbound (by positivity)).trans (hlarge j)
  have hreference := allocatedSpatialRank_reference_event (N := M) B U b hR hσ S spatial kernel block
    hmpos stride hstride cells width hwidth hZ hscale T a hTprime
    (fun p hp => hdiv ⟨p,hp⟩) (fun p hp => (ha p hp).1)
    (fun p hp x => column_stride_depth_le_of_product_stride stride hstride (ha p hp).2.2.2 x)
    hD hrankC hL (fun p hp => (ha p hp).2.2.1) hlargeM
  have hsum : (∑ j, 16 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : T, p.val ^ a p.val) / allocatedSpatialRankSelectedWidth B U b S spatial stride width j) ≤ κ := by
    apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) hresidueError
    rw [hprod]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hMbound (by positivity))
      ((by positivity : (0 : ℝ) ≤ 8 * (probabilityProfileLipschitz : ℝ) * (cap : ℝ)).trans (hlarge j))
  have hc := hcompare T hTne a M hM hbound hdiv
  have hevent (z) : (∀ p ∈ T, bad p (a p) z) ↔
      ∀ p : T, allocatedActualModulusBad inactive spatial kernel block rankC (p.val ^ a p.val) (read z) := by
    constructor
    · intro h p
      obtain ⟨_, hh⟩ := h p.val p.property
      exact hh
    · intro h p hp
      exact ⟨hT hp, h ⟨p,hp⟩⟩
  simp_rw [hevent]
  rw [hprod] at hreference hsum
  have hup := (abs_le.mp hc).2
  dsimp only [M] at hreference
  linarith

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

variable (Elog Vlog : ℝ) (Q : ℕ)
local notation "κ" => physicalBadProductAccuracy Elog Vlog
local notation "Rbad" => quantitativeBadPrimeRadius Elog
local notation "cap" => (max Q (Rbad ^ 2) : ℕ)
local notation "inactive" => allocatedShortAxis (I := I) U b S.value

include bW hC hV in

theorem exists_allocated_short_physical_certified_bad_product
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog) (hQ : 1 ≤ Q)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hmpos : 0 < m)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    {P : ℝ} (hP : 0 ≤ P) (hmP : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hbudgetP : Vlog + 3 * Elog + 16 ≤ P)
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
    {Ps ρ Rs Smax : ℝ} (hPs : 0 ≤ Ps) (hX : (Fintype.card X : ℝ) ≤ Ps)
    (hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Ps)
    (hbudgetPs : Vlog + 3 * Elog + 16 ≤ Ps)
    (hρ : 0 < ρ) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp Ps) (hstrideMax : ∀ x, ((stride x * cap : ℕ) : ℝ) ≤ Smax)
    (H : X → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hcells : cells.Nonempty)
    {L D : ℕ}
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
    (rankC : ℝ) (hrankC : 0 ≤ rankC)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    (hL : ⌈2 * (rankC + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride width z)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * (cap : ℝ) ≤
      allocatedShortRankSelectedWidth B U b S spatial stride width j)
    (hresidueError : (∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (cap : ℝ) /
      allocatedShortRankSelectedWidth B U b S spatial stride width j) ≤ κ) :
    let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
    ∃ read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ,
      (∀ z, allocatedReadNoise (read z) = z) ∧
      (∀ z, Dphysical z ≠ 0 →
        ∀ (primes : Finset ℕ) (hne : ∀ p : primes, NeZero p.val),
          letI := hne
          ∀ (depth : ℕ → ℕ) (q : ℕ) (hq : 0 < q),
            letI : NeZero q := ⟨hq.ne'⟩
            ∀ hdiv : ∀ p : primes, p.val ^ depth p.val ∣ q,
              coefficientDeckChartEvent U bW b hb o q
                (allocatedChartResiduePrimePowerWitness inactive rankC primes depth q hdiv
                  (fun v => (z v : ZMod q)))
                (affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))) ↔
              ∀ p : primes, allocatedActualModulusBad inactive spatial kernel block rankC
                (p.val ^ depth p.val) (read z)) ∧
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 3 * κ ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      0 < Rbad ∧ (Rbad : ℝ) ≤ Real.exp (Elog + 3) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
          (∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
            (if (∏ x, stride x) ^ 2 *
              (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * Rbad) <
                ∏ p ∈ primes, p ^ largestTestedBadDepth depth
                  (fun p a z => allocatedActualPrimeBad inactive spatial kernel block primes rankC p a (read z)) p z
              then (1 : ℝ) else 0)) ≤ Real.exp (-Elog) := by
  dsimp only
  obtain ⟨hκ, hκinv, hsmallError, _, herrors⟩ :=
    physicalBadProductAccuracy_budget hElog hVlog Q hQ hQexp
  obtain ⟨hcapexp, _⟩ := quantitativeBadPrimeRadius_witness_budget hElog hVlog Q hQexp
  have hcap : 0 < cap := lt_of_lt_of_le (by omega : 0 < Q) (le_max_left _ _)
  have hcapP : (cap : ℝ) ≤ Real.exp P := hcapexp.trans
    (Real.exp_le_exp.mpr (by linarith))
  have hcapPs : (cap : ℝ) ≤ Real.exp Ps := hcapexp.trans
    (Real.exp_le_exp.mpr (by linarith))
  have hκP : κ⁻¹ ≤ Real.exp P := by rw [hκinv]; exact Real.exp_le_exp.mpr hbudgetP
  have hκPs : 1 / κ ≤ Real.exp Ps := by
    rw [one_div, hκinv]; exact Real.exp_le_exp.mpr hbudgetPs
  obtain ⟨hD0, hZ, hDpos, read, hnoise, hread, hmass, hlower, hupper, hcompare⟩ :=
    exists_allocated_physical_certified_rank_witness_law B U bW b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall cap hcap hP hmP hK hRP hσP hcount hI hn hJ hAP hLP
      hCP hVP hcapP hκ hκP μ ν poly hp hm hPs hX hframe hcapPs hκ hρ hκPs hρPs stride hstride
      hSmax hSmaxPs hstrideMax H hsize hrank hRs cells hcells inactive spatial kernel block
      rankC width hwidth hwide hfreqPs hmassPs hsmallError
  have hRbad := quantitativeBadPrimeRadius_bounds hElog
  refine ⟨hD0, hZ, hDpos, read, hnoise, hread, ?_, hlower, hupper, hRbad.1, hRbad.2.1, ?_⟩
  · linarith
  intro primes hprime
  let : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
  intro depth hdepth
  let bad := fun p a z => allocatedActualPrimeBad inactive spatial kernel block primes rankC p a (read z)
  have hstrideprod : 0 < ∏ x, stride x := Finset.prod_pos (fun x _ => hstride x)
  apply (selectedResidueDensityPMF_stride_quantitative_badPrimeProduct stride cells width hwidth
    hZ _ hD0 hDpos primes depth bad hstrideprod hprime
    (modularCoefficientPrimeThreshold_two_le m) hQ hdepth hElog hVlog hQexp ?_).2.2.2.2.2
  dsimp only
  intro T hT a ha hbound
  let hTprime : ∀ p ∈ T, p.Prime := fun p hp => hprime p (hT hp)
  let hTne : ∀ p : T, NeZero p.val := fun p => ⟨(hTprime p.val p.property).ne_zero⟩
  let := hTne
  let M : ℕ := ∏ p ∈ T, p ^ a p
  have hM : 0 < M := Finset.prod_pos (fun p hp => pow_pos (hTprime p hp).pos _)
  let : NeZero M := ⟨hM.ne'⟩
  have hdiv : ∀ p : T, p.val ^ a p.val ∣ M :=
    fun p => Finset.dvd_prod_of_mem (fun p => p ^ a p) p.property
  have hprod : (∏ p : T, p.val ^ a p.val) = M := by
    exact (Finset.prod_subtype T (fun _ => Iff.rfl) (fun p => p ^ a p)).symm
  have hMbound : (M : ℝ) ≤ cap := Nat.cast_le.mpr hbound
  have hlargeM : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : T, p.val ^ a p.val) ≤ allocatedShortRankSelectedWidth B U b S spatial stride width j := by
    intro j
    rw [hprod]
    exact (mul_le_mul_of_nonneg_left hMbound (by positivity)).trans (hlarge j)
  have hreference := allocatedShortRank_reference_event (N := M) B U b hR hσ S spatial kernel block
    hmpos stride hstride cells width hwidth hZ hscale T a hTprime
    (fun p hp => hdiv ⟨p,hp⟩) (fun p hp => (ha p hp).1)
    (fun p hp x => column_stride_depth_le_of_product_stride stride hstride (ha p hp).2.2.2 x)
    hD hrankC hL (fun p hp => (ha p hp).2.2.1) hlargeM
  have hsum : (∑ j, 16 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : T, p.val ^ a p.val) / allocatedShortRankSelectedWidth B U b S spatial stride width j) ≤ κ := by
    apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) hresidueError
    rw [hprod]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hMbound (by positivity))
      ((by positivity : (0 : ℝ) ≤ 8 * (probabilityProfileLipschitz : ℝ) * (cap : ℝ)).trans (hlarge j))
  have hc := hcompare T hTne a M hM hbound hdiv
  have hevent (z) : (∀ p ∈ T, bad p (a p) z) ↔
      ∀ p : T, allocatedActualModulusBad inactive spatial kernel block rankC (p.val ^ a p.val) (read z) := by
    constructor
    · intro h p
      obtain ⟨_, hh⟩ := h p.val p.property
      exact hh
    · intro h p hp
      exact ⟨hT hp, h ⟨p,hp⟩⟩
  simp_rw [hevent]
  rw [hprod] at hreference hsum
  have hup := (abs_le.mp hc).2
  dsimp only [M] at hreference
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

variable (Elog Vlog : ℝ) (Q : ℕ)

include bW hC hV in

theorem exists_prepared_certified_physical_bad_product
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog) (hQ : 1 ≤ Q)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hmpos : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1/4)
    {P : ℝ} (hP : 0 ≤ P)
    (hprimitive : (((((m + 1) * ((enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) + 1) ^ m : ℕ)) + (enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) : ℕ) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hbudgetP : Vlog + 3 * Elog + 16 ≤ P)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {Ps ρ Rs Smax : ℝ} (hPs : 0 ≤ Ps) (hframePrimitive : ((((enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) + 1) * nX : ℕ) : ℝ) ≤ Ps)
    (hbudgetPs : Vlog + 3 * Elog + 16 ≤ Ps)
    (hρ : 0 < ρ) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (stride : Fin nX → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp Ps) (hstrideMax : ∀ x, ((stride x * ((max Q ((quantitativeBadPrimeRadius Elog) ^ 2) : ℕ)) : ℕ) : ℝ) ≤ Smax)
    (H : Fin nX → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride))
    (hcells : cells.Nonempty)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) * (physicalBadProductGap (((modularInitialBlockCount m (nX + m * M)) * ((nX + m * M : ℕ)) : ℕ)) Elog Vlog Q) ≤
        (layerSamplerGapWidth (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j,i⟩ / 2) *
          ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)))
    (hPPS : P ≤ Ps) (hWlog : 2 * P + 2 * Vlog + 5 * Elog + 24 ≤ Ps) :
    let Dphysical := fun z : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ =>
      allocatedCoefficientDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
    ∃ read : (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
        AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ,
      (∀ z, allocatedReadNoise (read z) = z) ∧
      (∀ z, Dphysical z ≠ 0 →
        ∀ (primes : Finset ℕ) (hne : ∀ p : primes, NeZero p.val),
          letI := hne
          ∀ (depth : ℕ → ℕ) (q : ℕ) (hq : 0 < q),
            letI : NeZero q := ⟨hq.ne'⟩
            ∀ hdiv : ∀ p : primes, p.val ^ depth p.val ∣ q,
              coefficientDeckChartEvent U bW b hb o q
                (allocatedChartResiduePrimePowerWitness (allocatedGridAxis (I := (PreparedSamplerContinuous prep)) U b S.value) ((modularInitialRankStrength m (nX + m * M) : ℝ)) primes depth q hdiv
                  (fun v => (z v : ZMod q)))
                (affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))) ↔
              ∀ p : primes, allocatedActualModulusBad (allocatedGridAxis (I := (PreparedSamplerContinuous prep)) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedGridAxis (I := (PreparedSamplerContinuous prep)) U b S.value)) ((modularInitialRankStrength m (nX + m * M) : ℝ))
                (p.val ^ depth p.val) (read z)) ∧
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 3 * (physicalBadProductAccuracy Elog Vlog) ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      0 < (quantitativeBadPrimeRadius Elog) ∧ ((quantitativeBadPrimeRadius Elog) : ℝ) ≤ Real.exp (Elog + 3) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
          (∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
            (if (∏ x, stride x) ^ 2 *
              (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * (quantitativeBadPrimeRadius Elog)) <
                ∏ p ∈ primes, p ^ largestTestedBadDepth depth
                  (fun p a z => allocatedActualPrimeBad (allocatedGridAxis (I := (PreparedSamplerContinuous prep)) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedGridAxis (I := (PreparedSamplerContinuous prep)) U b S.value)) primes ((modularInitialRankStrength m ((nX + m * M : ℕ)) : ℝ)) p a (read z)) p z
              then (1 : ℝ) else 0)) ≤ Real.exp (-Elog) := by
  obtain ⟨hmCount, _, hAllocCount, _, hvCount, hIcount, hnCount, hJcount, hcoeffCount, hframeCount⟩ :=
    preparedBadProduct_input_counts prep (modularInitialBlockCount m (nX + m * M)) nX hCoord
  have hpnum : ((enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) : ℝ) ≤ P := (Nat.cast_le.mpr (Nat.le_add_left (enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) (((m + 1) * ((enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) + 1) ^ m : ℕ)))).trans hprimitive
  have hcoeff : ((((m + 1) * ((enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) + 1) ^ m : ℕ)) : ℝ) ≤ P := (Nat.cast_le.mpr (Nat.le_add_right (((m + 1) * ((enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) + 1) ^ m : ℕ)) (enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))))).trans hprimitive
  have hmP : (m : ℝ) ≤ P := (Nat.cast_le.mpr hmCount).trans hpnum
  have hK : (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ) ≤ P :=
    (Nat.cast_le.mpr hvCount).trans hpnum
  have hI : ∀ j, (Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) ≤ P := fun j => (Nat.cast_le.mpr (hIcount j)).trans hpnum
  have hn : ∀ j, ((preparedSamplerTransverse prep) j : ℝ) ≤ P := fun j => (Nat.cast_le.mpr (hnCount j)).trans hpnum
  have hJ : ∀ j, (Fintype.card (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j) : ℝ) ≤ P := fun j => (Nat.cast_le.mpr (hJcount j)).trans hpnum
  have hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (j.val+1)) : ℝ) ≤ P :=
    fun j => (Nat.cast_le.mpr (hcoeffCount j)).trans hcoeff
  have hframe : (Fintype.card (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX) : ℝ) ≤ Ps :=
    (Nat.cast_le.mpr hframeCount).trans hframePrimitive
  have hX : (Fintype.card (Fin nX) : ℝ) ≤ Ps := by
    simp only [Fintype.card_fin]
    apply le_trans (Nat.cast_le.mpr ?_) hframePrimitive
    nlinarith
  obtain ⟨hrankC, hD, hL⟩ := preparedInitialRank_parameters prep U o bW nX M hCoord hmpos
  obtain ⟨hWone, hcapW, hWbudget⟩ := physicalBadProductGap_budget (((modularInitialBlockCount m (nX + m * M)) * ((nX + m * M : ℕ)) : ℕ)) hElog hVlog Q hQ hQexp
  have hκ := physicalBadProductAccuracy_pos Elog Vlog
  have hDalloc : ((nX + m * M : ℕ)) ≤ (modularInitialBlockCount m (nX + m * M)) := by
    unfold modularInitialBlockCount
    have hpow : 0 < (2 : ℕ) ^ m := pow_pos (by norm_num) m
    calc
      nX + m * M ≤ modularInitialRankStrength m (nX + m * M) + (nX + m * M) + 10 := by omega
      _ ≤ 2 ^ m * (modularInitialRankStrength m (nX + m * M) + (nX + m * M) + 10) :=
        Nat.le_mul_of_pos_left _ hpow
      _ ≤ _ := Nat.le_succ _
  have hNsq : (((modularInitialBlockCount m (nX + m * M)) * ((nX + m * M : ℕ)) : ℕ)) ≤ (enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) * (enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) := Nat.mul_le_mul hAllocCount (hDalloc.trans hAllocCount)
  have hpnumExp : ((enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) : ℝ) ≤ Real.exp P := hpnum.trans (by linarith [Real.add_one_le_exp P])
  have hNexp : ((((modularInitialBlockCount m (nX + m * M)) * ((nX + m * M : ℕ)) : ℕ)) : ℝ) ≤ Real.exp (2 * P) := by
    have hh := mul_le_mul hpnumExp hpnumExp (Nat.cast_nonneg (enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M)))) (Real.exp_nonneg P)
    rw [← Real.exp_add] at hh
    have hs : (((enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) * (enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) : ℕ) : ℝ) ≤ Real.exp (2 * P) := by
      simpa only [Nat.cast_mul, two_mul] using hh
    exact (Nat.cast_le.mpr hNsq).trans hs
  have hWPs : (physicalBadProductGap (((modularInitialBlockCount m (nX + m * M)) * ((nX + m * M : ℕ)) : ℕ)) Elog Vlog Q) ≤ Real.exp Ps :=
    (physicalBadProductGap_exp_bound (((modularInitialBlockCount m (nX + m * M)) * ((nX + m * M : ℕ)) : ℕ)) hElog hVlog (by positivity : 0 ≤ 2 * P) Q hQexp hNexp).trans
      (Real.exp_le_exp.mpr hWlog)
  have hstrideExp : ∀ x, (stride x : ℝ) ≤ Real.exp Ps := by
    intro x
    apply le_trans _ (hSmaxPs)
    apply le_trans (Nat.cast_le.mpr ?_) (hstrideMax x)
    have hc : 1 ≤ ((max Q ((quantitativeBadPrimeRadius Elog) ^ 2) : ℕ)) := hQ.trans (le_max_left _ _)
    nlinarith
  have hnoiseGap : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) * (physicalBadProductGap (((modularInitialBlockCount m (nX + m * M)) * ((nX + m * M : ℕ)) : ℕ)) Elog Vlog Q) ≤ residueProfileWidth stride width z := by
    intro z
    exact spatial_witness_width_of_exp_size hPs (allocatedMaskedTiltedConstant_ge_two m)
      hρ hρPs (hsize z.2) (hwide z) (by exact_mod_cast hstride z.2) (hstrideExp z.2)
      (hAP.trans (Real.exp_le_exp.mpr hPPS)) (le_trans zero_le_one hWone) hWPs
  have hcap : (0 : ℝ) < (((max Q ((quantitativeBadPrimeRadius Elog) ^ 2) : ℕ)) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by omega : 0 < Q) (le_max_left Q ((quantitativeBadPrimeRadius Elog) ^ 2))
  have hcountSmooth := preparedInitialRank_smooth_card_le prep nX M hCoord hmpos (allocatedGridAxis (I := (PreparedSamplerContinuous prep)) U b S.value)
  have hactualBudget : 2 * (Fintype.card (AllocatedSmoothRankCoefficientIndex (Fin nX) (allocatedGridAxis (I := (PreparedSamplerContinuous prep)) U b S.value) (modularInitialBlockCount m (nX + m * M))) : ℝ) *
      (((max Q ((quantitativeBadPrimeRadius Elog) ^ 2) : ℕ)) : ℝ) / (physicalBadProductAccuracy Elog Vlog) ≤ (physicalBadProductGap (((modularInitialBlockCount m (nX + m * M)) * ((nX + m * M : ℕ)) : ℕ)) Elog Vlog Q) := by
    apply le_trans _ hWbudget
    apply div_le_div_of_nonneg_right _ hκ.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcountSmooth) (by norm_num)) hcap.le
  obtain ⟨hlarge, hresidueError⟩ := allocatedSpatialRankSelectedWidth_budget (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (preparedInitialRankSpatialEmbedding (m := m) nX M) stride width
    hcap hκ hcapW hprincipal (fun l x => hnoiseGap _) hactualBudget
  have hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride width z := by
    intro z
    calc
      _ = 8 * (probabilityProfileLipschitz : ℝ) * 1 := (mul_one _).symm
      _ ≤ _ := (mul_le_mul_of_nonneg_left hWone (by positivity)).trans (hnoiseGap z)
  exact exists_allocated_physical_certified_bad_product (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S C V hC hV Elog Vlog Q
    hElog hVlog hQ hQexp hmpos hR hσ hσ1 Cinv hCinv hchart hsmall hP hmP hK hRP hσP hcount hI hn hJ
    hAP hLP hCP hVP hbudgetP μ ν poly hp hm hPs hX hframe hbudgetPs hρ hρPs stride hstride
    hSmax hSmaxPs hstrideMax H hsize hrank hRs cells hcells (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedGridAxis (I := (PreparedSamplerContinuous prep)) U b S.value))
    ((modularInitialRankStrength m ((nX + m * M : ℕ)) : ℝ)) hrankC hD hL width hwidth hwide hfreqPs hmassPs hscale hlarge hresidueError

end Erdos3.VectorPolynomial

end

end OAI
