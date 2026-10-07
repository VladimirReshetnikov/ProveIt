/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.PreparedModularCanonicalDetectorPeriodBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

def allocatedAmbientNormalizationLog {A : Type*} [Semiring A]
    (dim : ℕ) (D V Q E : A) : A :=
  (dim + 1 : ℕ) * D * (8 + Q + E) + (dim : ℕ) * D * (V + 1)

theorem finiteProductPower_exponential_bound {X : Type*} [Fintype X]
    (f : X → ℝ) {B D : ℝ} (hB : 0 ≤ B) (hf0 : ∀ x, 0 ≤ f x)
    (hf : ∀ x, f x ≤ Real.exp B) (hX : (Fintype.card X : ℝ) ≤ D) (n : ℕ) :
    (∏ x, f x ^ n) ≤ Real.exp ((n : ℝ) * D * B) := by
  calc
    _ ≤ ∏ _x : X, (Real.exp B) ^ n := Finset.prod_le_prod₀
      (fun x _ => pow_nonneg (hf0 x) _) (fun x _ => pow_le_pow_left₀ (hf0 x) (hf x) _)
    _ = Real.exp ((Fintype.card X : ℝ) * ((n : ℝ) * B)) := by
      rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (calc
      _ ≤ D * ((n : ℝ) * B) := mul_le_mul_of_nonneg_right hX (mul_nonneg (Nat.cast_nonneg _) hB)
      _ = _ := by ring)

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {X : Type*} [Fintype X] (N q : X → ℕ) {τ : ℝ}

local notation "W" => allocatedPhysicalRootBudget B U b S (fun _ => 0)
local notation "hW" => allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)

theorem allocatedAmbientVolume_log_bound {D V Q E : ℝ}
    (hV : 0 ≤ V) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp V)
    (hX : (Fintype.card X : ℝ) ≤ D)
    (hN : ∀ x, 0 < N x) (hq : ∀ x, 0 < q x) (hτ : 0 < τ)
    (hqexp : ∀ x, (q x : ℝ) ≤ Real.exp Q) (hτexp : 1 / τ ≤ Real.exp E) :
    let volume := ∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (trimmedSpatialRootScale τ N q x)
      (trimmedSpatialSlopeScale W τ N q x) S.value i
    (((integerBox N).card : ℝ) ^ (dim + 1) / volume ≤
      Real.exp (allocatedAmbientNormalizationLog dim D V Q E)) ∧
    ((integerBoxCubeCount N dim : ℝ) / volume ≤
      Real.exp (allocatedAmbientNormalizationLog dim D V Q E)) := by
  intro volume
  have hS : (0 : ℝ) < S.value := Nat.cast_pos.mpr S.positive
  have hscales (x : X) := trimmedSpatial_scales_pos hW hτ N q x (hN x) (hq x)
  have hvolume : 0 < volume := Finset.prod_pos (fun x _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hscales x).1 (hscales x).2 hS i))
  have hscalar (x : X) : 8 * (q x : ℝ) / τ ≤ Real.exp (8 + Q + E) := by
    calc
      _ = (8 * (q x : ℝ)) * (1 / τ) := by ring
      _ ≤ (Real.exp 8 * Real.exp Q) * Real.exp E := mul_le_mul
        (mul_le_mul (by linarith [Real.add_one_le_exp (8 : ℝ)] : (8 : ℝ) ≤ Real.exp 8)
          (hqexp x) (Nat.cast_nonneg _) (Real.exp_pos _).le)
        hτexp (div_nonneg zero_le_one hτ.le) (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have hfirst : (∏ x, (8 * (q x : ℝ) / τ) ^ (dim + 1)) ≤
      Real.exp ((dim + 1 : ℕ) * D * (8 + Q + E)) :=
    finiteProductPower_exponential_bound (fun x => 8 * (q x : ℝ) / τ)
      (by linarith only [hQ, hE]) (fun x => by positivity) hscalar hX (dim + 1)
  have hratio0 : 0 ≤ (1 + W) / (S.value : ℝ) := div_nonneg (by linarith [hW]) hS.le
  have hratio : (1 + W) / (S.value : ℝ) ≤ Real.exp (V + 1) :=
    (allocatedPhysicalRootBudget_zero_ratio B U b S (Real.exp_pos V).le hvars).trans (by
      rw [(allocatedPrimitiveRootRatio_bounds (Real.exp_pos V).le).1, add_comm]
      exact one_add_le_exp_succ hV le_rfl)
  have hinner := pow_le_exp_mul_of_le_exp hratio0 hratio (by linarith only [hV]) dim
    (le_refl (dim : ℝ))
  have houter := pow_le_exp_mul_of_le_exp (pow_nonneg hratio0 dim) hinner
    (mul_nonneg (Nat.cast_nonneg _) (by linarith only [hV])) (Fintype.card X) hX
  have hsecond : (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X ≤
      Real.exp ((dim : ℕ) * D * (V + 1)) := by
    apply houter.trans_eq
    congr 1
    ring
  have hphysical : (∏ x, (N x : ℝ)) ^ (dim + 1) / volume ≤
      Real.exp (allocatedAmbientNormalizationLog dim D V Q E) := by
    dsimp only [volume]
    rw [trimmedSpatial_ambient_volume_ratio dim N q hW hτ hS hN hq]
    apply (mul_le_mul hfirst hsecond (pow_nonneg (pow_nonneg hratio0 dim) _) (Real.exp_pos _).le).trans_eq
    rw [← Real.exp_add]
    rfl
  have hbox : ((integerBox N).card : ℝ) ^ (dim + 1) / volume ≤
      Real.exp (allocatedAmbientNormalizationLog dim D V Q E) := by
    simpa only [card_integerBox, Nat.cast_prod] using hphysical
  have hcubes : (integerBoxCubeCount N dim : ℝ) ≤ ((integerBox N).card : ℝ) ^ (dim + 1) := by
    exact_mod_cast integerBoxCubeCount_upper N dim
  exact ⟨hbox, (div_le_div_of_nonneg_right hcubes hvolume.le).trans hbox⟩

theorem allocatedAmbientVolume_pre_bound {D V Q E : ℝ}
    (hV : 0 ≤ V) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ V)
    (hX : (Fintype.card X : ℝ) ≤ D)
    (hN : ∀ x, 0 < N x) (hq : ∀ x, 0 < q x) (hτ : 0 < τ)
    (hqexp : ∀ x, (q x : ℝ) ≤ Real.exp Q) (hτexp : 1 / τ ≤ Real.exp E) :
    let volume := ∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (trimmedSpatialRootScale τ N q x)
      (trimmedSpatialSlopeScale W τ N q x) S.value i
    (((integerBox N).card : ℝ) ^ (dim + 1) / volume ≤
      Real.exp (allocatedAmbientNormalizationLog dim D V Q E)) ∧
    ((integerBoxCubeCount N dim : ℝ) / volume ≤
      Real.exp (allocatedAmbientNormalizationLog dim D V Q E))  := by
  have hvarsExp : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp V :=
    hvars.trans (by linarith [Real.add_one_le_exp V])
  exact allocatedAmbientVolume_log_bound B U b S N q hV hQ hE hvarsExp hX hN hq hτ hqexp hτexp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical

theorem physicalAmbientVolume_log_bound {X : Type*} [Fintype X] [DecidableEq X]
    (dim : ℕ) (N q : X → ℕ) {W τ L D V Q E : ℝ}
    (hW : 0 ≤ W) (hL : 1 ≤ L)
    (hV : 0 ≤ V) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (hWscale : W ≤ Real.exp V * L)
    (hX : (Fintype.card X : ℝ) ≤ D)
    (hN : ∀ x, 0 < N x) (hq : ∀ x, 0 < q x) (hτ : 0 < τ)
    (hqexp : ∀ x, (q x : ℝ) ≤ Real.exp Q) (hτexp : 1 / τ ≤ Real.exp E) :
    let volume := ∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (trimmedSpatialRootScale τ N q x)
      (trimmedSpatialSlopeScale W τ N q x) L i
    (((integerBox N).card : ℝ) ^ (dim + 1) / volume ≤
      Real.exp (allocatedAmbientNormalizationLog dim D V Q E)) ∧
    ((integerBoxCubeCount N dim : ℝ) / volume ≤
      Real.exp (allocatedAmbientNormalizationLog dim D V Q E)) := by
  intro volume
  have hS : (0 : ℝ) < L := zero_lt_one.trans_le hL
  have hscales (x : X) := trimmedSpatial_scales_pos hW hτ N q x (hN x) (hq x)
  have hvolume : 0 < volume := Finset.prod_pos (fun x _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hscales x).1 (hscales x).2 hS i))
  have hscalar (x : X) : 8 * (q x : ℝ) / τ ≤ Real.exp (8 + Q + E) := by
    calc
      _ = (8 * (q x : ℝ)) * (1 / τ) := by ring
      _ ≤ (Real.exp 8 * Real.exp Q) * Real.exp E := mul_le_mul
        (mul_le_mul (by linarith [Real.add_one_le_exp (8 : ℝ)] : (8 : ℝ) ≤ Real.exp 8)
          (hqexp x) (Nat.cast_nonneg _) (Real.exp_pos _).le)
        hτexp (div_nonneg zero_le_one hτ.le) (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have hfirst : (∏ x, (8 * (q x : ℝ) / τ) ^ (dim + 1)) ≤
      Real.exp ((dim + 1 : ℕ) * D * (8 + Q + E)) :=
    finiteProductPower_exponential_bound (fun x => 8 * (q x : ℝ) / τ)
      (by linarith only [hQ, hE]) (fun x => by positivity) hscalar hX (dim + 1)
  have hratio0 : 0 ≤ (1 + W) / (L : ℝ) := div_nonneg (by linarith [hW]) hS.le
  have hratio : (1 + W) / (L : ℝ) ≤ Real.exp (V + 1) :=
    calc
      _ ≤ 1 + Real.exp V := (div_le_iff₀ hS).mpr (by nlinarith only [hL, hWscale])
      _ ≤ _ := one_add_le_exp_succ hV le_rfl
  have hinner := pow_le_exp_mul_of_le_exp hratio0 hratio (by linarith only [hV]) dim
    (le_refl (dim : ℝ))
  have houter := pow_le_exp_mul_of_le_exp (pow_nonneg hratio0 dim) hinner
    (mul_nonneg (Nat.cast_nonneg _) (by linarith only [hV])) (Fintype.card X) hX
  have hsecond : (((1 + W) / (L : ℝ)) ^ dim) ^ Fintype.card X ≤
      Real.exp ((dim : ℕ) * D * (V + 1)) := by
    apply houter.trans_eq
    congr 1
    ring
  have hphysical : (∏ x, (N x : ℝ)) ^ (dim + 1) / volume ≤
      Real.exp (allocatedAmbientNormalizationLog dim D V Q E) := by
    dsimp only [volume]
    rw [trimmedSpatial_ambient_volume_ratio dim N q hW hτ hS hN hq]
    apply (mul_le_mul hfirst hsecond (pow_nonneg (pow_nonneg hratio0 dim) _) (Real.exp_pos _).le).trans_eq
    rw [← Real.exp_add]
    rfl
  have hbox : ((integerBox N).card : ℝ) ^ (dim + 1) / volume ≤
      Real.exp (allocatedAmbientNormalizationLog dim D V Q E) := by
    simpa only [card_integerBox, Nat.cast_prod] using hphysical
  have hcubes : (integerBoxCubeCount N dim : ℝ) ≤ ((integerBox N).card : ℝ) ^ (dim + 1) := by
    exact_mod_cast integerBoxCubeCount_upper N dim
  exact ⟨hbox, (div_le_div_of_nonneg_right hcubes hvolume.le).trans hbox⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_canonicalSlicedNative_input_budget (m dim Amass Aanalytic : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {P D p v F Prho Pk target Banalytic pGeometry Ecoarse gain : ℝ} {nX : ℕ},
      0 ≤ P → D ∈ Set.Icc 0 P → p ∈ Set.Icc 0 P → v ∈ Set.Icc 0 P →
      F ∈ Set.Icc 0 P → Prho ∈ Set.Icc 0 P → Pk ∈ Set.Icc 0 P →
      target ∈ Set.Icc 0 P → Banalytic ∈ Set.Icc 0 P →
      pGeometry ∈ Set.Icc 0 P → Ecoarse ∈ Set.Icc 0 P →
      gain ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      let Emodel := (D + p + v + F + Prho + Pk + target + Amass) ^ Amass
      let analytic := (D + p + v + F + Prho + Pk + target + Banalytic + Aanalytic) ^ Aanalytic
      let Espatial := coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim (pGeometry + Ecoarse))
      let volumeLog := allocatedAmbientNormalizationLog dim (nX : ℝ) pGeometry pGeometry pGeometry
      let Pvolume := (nX : ℝ) + volumeLog
      let budget := (P + C) ^ C
      P ≤ budget ∧ Emodel ∈ Set.Icc 0 budget ∧ analytic ∈ Set.Icc 0 budget ∧
        Espatial ∈ Set.Icc 0 budget ∧ Pvolume ∈ Set.Icc 0 budget ∧
        volumeLog ≤ Pvolume ∧ (nX : ℝ) ≤ gain + 8 + Emodel + Espatial + Pvolume := by
  obtain ⟨Aspatial, _, hspatial⟩ := exists_allocatedEarlyCoarseLog_bound m dim
  let X : Polynomial ℕ := Polynomial.X
  let massPoly := (7 * X + Polynomial.C Amass) ^ Amass
  let analyticPoly := (8 * X + Polynomial.C Aanalytic) ^ Aanalytic
  let spatialPoly := (2 * X + Polynomial.C Aspatial) ^ Aspatial
  let volumePoly := X + allocatedAmbientNormalizationLog dim X X X X
  obtain ⟨C, hC, hbound⟩ :=
    exists_natPolynomial_eval_budget (X + massPoly + analyticPoly + spatialPoly + volumePoly)
  refine ⟨C, hC, ?_⟩
  intro P D p v F Prho Pk target Banalytic pGeometry Ecoarse gain nX hP hD hp hv hF hPrho hPk
    htarget hBanalytic hGeometry hEcoarse hgain hnX Emodel analytic Espatial volumeLog Pvolume budget
  let massBound := (7 * P + Amass) ^ Amass
  let analyticBound := (8 * P + Aanalytic) ^ Aanalytic
  let spatialBound := (2 * P + Aspatial) ^ Aspatial
  let volumeBound := P + allocatedAmbientNormalizationLog dim P P P P
  have hsum : P + massBound + analyticBound + spatialBound + volumeBound ≤ budget := by
    simpa [X, massPoly, analyticPoly, spatialPoly, volumePoly, massBound, analyticBound,
      spatialBound, volumeBound, allocatedAmbientNormalizationLog, Polynomial.eval₂_pow] using hbound P hP
  have hD0 : 0 ≤ D := hD.1
  have hp0 : 0 ≤ p := hp.1
  have hv0 : 0 ≤ v := hv.1
  have hF0 : 0 ≤ F := hF.1
  have hPrho0 : 0 ≤ Prho := hPrho.1
  have hPk0 : 0 ≤ Pk := hPk.1
  have htarget0 : 0 ≤ target := htarget.1
  have hBanalytic0 : 0 ≤ Banalytic := hBanalytic.1
  have hGeometry0 : 0 ≤ pGeometry := hGeometry.1
  have hEcoarse0 : 0 ≤ Ecoarse := hEcoarse.1
  have hmass0 : 0 ≤ Emodel := by dsimp [Emodel]; positivity
  have hanalytic0 : 0 ≤ analytic := by dsimp [analytic]; positivity
  have hspatial0 : 0 ≤ Espatial :=
    (coarseSpatialLogs_nonneg (allocatedEarlyCoarseInput_bounds m dim
      (add_nonneg hGeometry.1 hEcoarse.1)).1).2
  have hvolume0 : 0 ≤ volumeLog := by
    dsimp [volumeLog, allocatedAmbientNormalizationLog]
    positivity
  have hPvolume0 : 0 ≤ Pvolume := add_nonneg (Nat.cast_nonneg _) hvolume0
  have hm : Emodel ≤ massBound := by
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hD.2, hp.2, hv.2, hF.2, hPrho.2, hPk.2, htarget.2]
  have ha : analytic ≤ analyticBound := by
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hD.2, hp.2, hv.2, hF.2, hPrho.2, hPk.2, htarget.2, hBanalytic.2]
  have hs : Espatial ≤ spatialBound := by
    apply (hspatial (add_nonneg hGeometry.1 hEcoarse.1)).2.trans
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hGeometry.2, hEcoarse.2]
  have hvb : Pvolume ≤ volumeBound := by
    dsimp only [Pvolume, volumeLog, volumeBound, allocatedAmbientNormalizationLog]
    gcongr <;> first | assumption | exact hGeometry.2
  have hm0 : 0 ≤ massBound := by dsimp [massBound]; positivity
  have ha0 : 0 ≤ analyticBound := by dsimp [analyticBound]; positivity
  have hs0 : 0 ≤ spatialBound := by dsimp [spatialBound]; positivity
  have hv0 : 0 ≤ volumeBound := by
    dsimp [volumeBound, allocatedAmbientNormalizationLog]
    positivity
  refine ⟨?_, ⟨hmass0, ?_⟩, ⟨hanalytic0, ?_⟩, ⟨hspatial0, ?_⟩,
    ⟨hPvolume0, ?_⟩, ?_, ?_⟩
  · linarith only [hsum, hm0, ha0, hs0, hv0]
  · linarith only [hsum, hm, hP, ha0, hs0, hv0]
  · linarith only [hsum, ha, hP, hm0, hs0, hv0]
  · linarith only [hsum, hs, hP, hm0, ha0, hv0]
  · linarith only [hsum, hvb, hP, hm0, ha0, hs0]
  · exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  · dsimp only [Pvolume]
    linarith only [hgain.1, hmass0, hspatial0, hvolume0]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators
universe uI uQ

private def generalNativePrimitiveEnvelope {α : Type*} [Semiring α]
    (m dim Cgrid Cpref : ℕ) (P : α) : α :=
  let q : α := (m + 1 : ℕ) * P + P * P
  let t : α := dim + q + (P + 1) + 1
  let g : α := Cgrid + (dim + 1 : ℕ) * q + (P + 1) + 4
  9 * P + (slicedGridGeometryLog P P P t + g) + (P + Cpref) ^ Cpref

private theorem generalNative_grid_mono
    {D v w t D' v' w' t' : ℝ} (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (ht : 0 ≤ t)
    (hDD : D ≤ D') (hvv : v ≤ v') (hww : w ≤ w') (htt : t ≤ t') :
    slicedGridGeometryLog D v w t ≤ slicedGridGeometryLog D' v' w' t' := by
  have hD' := hD.trans hDD
  unfold slicedGridGeometryLog
  gcongr

theorem exists_preparedModularGeneralNative_budget
    (m dim Cgrid Amass Aanalytic Anorm : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {I : Fin m → Type uI} [∀ j, Fintype (I j)]
      {n : Fin m → ℕ} {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
      {nX : ℕ} {P Dg vg wg pDetect Pnum Pk Qstride Prho target Banalytic Pphysical Ecoarse pGain : ℝ},
      0 ≤ P → Dg ∈ Set.Icc 0 P → vg ∈ Set.Icc 0 P → wg ∈ Set.Icc 0 P →
      pDetect ∈ Set.Icc 0 P → Pnum ∈ Set.Icc 0 P → Pk ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P → Prho ∈ Set.Icc 0 P → target ∈ Set.Icc 0 P →
      Banalytic ∈ Set.Icc 0 P → Pphysical ∈ Set.Icc 0 P → Ecoarse ∈ Set.Icc 0 P →
      pGain ∈ Set.Icc 0 P → (nX : ℝ) ≤ P →
      (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P →
      (∀ j, (Fintype.card (Q j) : ℝ) ≤ P) →
      let qlog := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let tg := (dim : ℝ) + qlog + (pDetect + 1) + 1
      let pg := (Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qlog + (pDetect + 1) + 4
      let gridlog := slicedGridGeometryLog Dg vg wg tg + pg
      let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin dim)) * (Pnum + 8) * (1 + 4 * Pnum) +
        Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
        ∑ j : Fin m, (Fintype.card (Q j) : ℝ) *
          (Fintype.card (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type) * ((m + 1 : ℕ) * Pk))
      let primitive := Dg + gridlog + vg + Fmodel + Prho + Pk + target + Banalytic +
        Pphysical + Ecoarse + pGain
      let Pnative := P + primitive
      let Cnative := Classical.choose (exists_canonicalSlicedNative_input_budget m dim Amass Aanalytic)
      let Bbudget := (Pnative + Cnative) ^ Cnative
      let normalizedCost := (Bbudget + Anorm) ^ Anorm
      let Emodel := (Dg + gridlog + vg + Fmodel + Prho + Pk + target + Amass) ^ Amass
      let analytic := (Dg + gridlog + vg + Fmodel + Prho + Pk + target + Banalytic + Aanalytic) ^ Aanalytic
      let Espatial := coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim (Pphysical + Ecoarse))
      let volumeLog := allocatedAmbientNormalizationLog dim (nX : ℝ) Pphysical Pphysical Pphysical
      let Pvolume := (nX : ℝ) + volumeLog
      let budget := (P + C) ^ C
      P ≤ Pnative ∧ primitive ∈ Set.Icc 0 budget ∧ Pnative ∈ Set.Icc 0 budget ∧
      Bbudget ∈ Set.Icc 0 budget ∧ normalizedCost ∈ Set.Icc 0 budget ∧
      Emodel ∈ Set.Icc 0 budget ∧ analytic ∈ Set.Icc 0 budget ∧
      Espatial ∈ Set.Icc 0 budget ∧ Pvolume ∈ Set.Icc 0 budget ∧
      volumeLog ≤ Pvolume ∧ (nX : ℝ) ≤ pGain + 8 + Emodel + Espatial + Pvolume := by
  let Cpref := Classical.choose (exists_canonicalSlicedModelPrefactor_budget.{uI,uQ} m dim)
  let Cnative := Classical.choose (exists_canonicalSlicedNative_input_budget m dim Amass Aanalytic)
  let X : Polynomial ℕ := Polynomial.X
  let primPoly := generalNativePrimitiveEnvelope m dim Cgrid Cpref X
  let nativePoly := X + primPoly
  let costPoly := (nativePoly + Polynomial.C Cnative) ^ Cnative
  let normPoly := (costPoly + Polynomial.C Anorm) ^ Anorm
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (nativePoly + costPoly + normPoly)
  refine ⟨C, hC, ?_⟩
  intro I _ n Q _ nX P Dg vg wg pDetect Pnum Pk Qstride Prho target Banalytic Pphysical Ecoarse pGain
    hP hD hv hw hpDetect hPnum hPk hQstride hPrho htarget hBanalytic hPphysical hEcoarse hpGain
    hnX haxes hQ qlog tg pg gridlog Fmodel primitive Pnative Cnative' Bbudget normalizedCost
    Emodel analytic Espatial volumeLog Pvolume budget
  have hD0 := hD.1
  have hv0 := hv.1
  have hw0 := hw.1
  have hpDetect0 := hpDetect.1
  have hPk0 := hPk.1
  have hQstride0 := hQstride.1
  have hPrho0 := hPrho.1
  have htarget0 := htarget.1
  have hBanalytic0 := hBanalytic.1
  have hPphysical0 := hPphysical.1
  have hEcoarse0 := hEcoarse.1
  have hpGain0 := hpGain.1
  let qb := ((m + 1 : ℕ) : ℝ) * P + P * P
  let tb := (dim : ℝ) + qb + (P + 1) + 1
  let gb := (Cgrid : ℝ) + ((dim + 1 : ℕ) : ℝ) * qb + (P + 1) + 4
  let gridBound := slicedGridGeometryLog P P P tb + gb
  let primBound := generalNativePrimitiveEnvelope m dim Cgrid Cpref P
  let nativeBound := P + primBound
  let costBound := (nativeBound + Cnative) ^ Cnative
  let normBound := (costBound + Anorm) ^ Anorm
  have hq0 : 0 ≤ qlog := by dsimp only [qlog]; positivity
  have hq : qlog ≤ qb := add_le_add
    (mul_le_mul_of_nonneg_left hPk.2 (Nat.cast_nonneg _))
    (mul_le_mul hnX hQstride.2 hQstride0 hP)
  have ht0 : 0 ≤ tg := by dsimp only [tg]; positivity
  have ht : tg ≤ tb := by dsimp only [tg, tb]; linarith only [hq, hpDetect.2]
  have hpg0 : 0 ≤ pg := by dsimp only [pg]; positivity
  have hpg : pg ≤ gb := by
    dsimp only [pg, gb]
    exact add_le_add (add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _))) (add_le_add hpDetect.2 le_rfl)) le_rfl
  have hgrid0 : 0 ≤ gridlog := by dsimp only [gridlog, slicedGridGeometryLog]; positivity
  have hgrid : gridlog ≤ gridBound := add_le_add
    (generalNative_grid_mono hD0 hv0 hw0 ht0 hD.2 hv.2 hw.2 ht) hpg
  have hf : Fmodel ∈ Set.Icc 0 ((P + Cpref) ^ Cpref) :=
    (Classical.choose_spec (exists_canonicalSlicedModelPrefactor_budget.{uI,uQ} m dim)).2
      hP hPnum hPk haxes hQ
  have hf0 := hf.1
  have hprim0 : 0 ≤ primitive := by dsimp only [primitive]; positivity
  have hprim : primitive ≤ primBound := by
    change primitive ≤ 9 * P + gridBound + (P + Cpref) ^ Cpref
    dsimp only [primitive]
    linarith only [hD.2, hgrid, hv.2, hf.2, hPrho.2, hPk.2, htarget.2,
      hBanalytic.2, hPphysical.2, hEcoarse.2, hpGain.2]
  have hPN0 : 0 ≤ Pnative := add_nonneg hP hprim0
  have hPnative : P ≤ Pnative := le_add_of_nonneg_right hprim0
  have hPN : Pnative ≤ nativeBound := add_le_add le_rfl hprim
  have hNbound0 : 0 ≤ nativeBound := hPN0.trans hPN
  have hcost0 : 0 ≤ costBound := by dsimp only [costBound]; positivity
  have hnorm0 : 0 ≤ normBound := by dsimp only [normBound]; positivity
  have htotal : nativeBound + costBound + normBound ≤ budget := by
    simpa [nativePoly, primPoly, costPoly, normPoly, X, nativeBound, primBound, costBound,
      normBound, generalNativePrimitiveEnvelope, slicedGridGeometryLog, Polynomial.eval₂_pow]
      using hbound P hP
  have hcost : Bbudget ≤ costBound := by
    apply pow_le_pow_left₀ (by positivity)
    exact add_le_add hPN le_rfl
  have hnorm : normalizedCost ≤ normBound := by
    apply pow_le_pow_left₀ (by dsimp only [Bbudget]; positivity)
    exact add_le_add hcost le_rfl
  have hbudgetB : Bbudget ≤ budget := by linarith only [htotal, hcost, hNbound0, hnorm0]
  have hBD : Dg ∈ Set.Icc 0 Pnative := ⟨hD0, hD.2.trans hPnative⟩
  have hBgrid : gridlog ∈ Set.Icc 0 Pnative := by
    refine ⟨hgrid0, ?_⟩
    dsimp only [Pnative, primitive]
    linarith only [hP, hD0, hv0, hf0, hPrho0, hPk0, htarget0,
      hBanalytic0, hPphysical0, hEcoarse0, hpGain0]
  have hBF : Fmodel ∈ Set.Icc 0 Pnative := by
    refine ⟨hf0, ?_⟩
    dsimp only [Pnative, primitive]
    linarith only [hP, hD0, hv0, hgrid0, hPrho0, hPk0, htarget0,
      hBanalytic0, hPphysical0, hEcoarse0, hpGain0]
  have lift (x : ℝ) (hx : x ∈ Set.Icc 0 P) : x ∈ Set.Icc 0 Pnative :=
    ⟨hx.1, hx.2.trans hPnative⟩
  obtain ⟨_, hmass, hanalytic, hspatial, hvolume, hvlog, hdimension⟩ :=
    (Classical.choose_spec (exists_canonicalSlicedNative_input_budget m dim Amass Aanalytic)).2
      hPN0 hBD hBgrid (lift vg hv) hBF (lift Prho hPrho) (lift Pk hPk)
      (lift target htarget) (lift Banalytic hBanalytic) (lift Pphysical hPphysical)
      (lift Ecoarse hEcoarse) (lift pGain hpGain) (hnX.trans hPnative)
  have liftBudget (x : ℝ) (hx : x ∈ Set.Icc 0 Bbudget) : x ∈ Set.Icc 0 budget :=
    ⟨hx.1, hx.2.trans hbudgetB⟩
  refine ⟨hPnative, ⟨hprim0, ?_⟩, ⟨hPN0, ?_⟩,
    ⟨by dsimp only [Bbudget]; positivity, hbudgetB⟩,
    ⟨by dsimp only [normalizedCost, Bbudget]; positivity, ?_⟩,
    liftBudget _ hmass, liftBudget _ hanalytic, liftBudget _ hspatial,
    liftBudget _ hvolume, hvlog, hdimension⟩
  · linarith only [htotal, hPN, hP, hcost0, hnorm0]
  · linarith only [htotal, hPN, hcost0, hnorm0]
  · linarith only [htotal, hnorm, hNbound0, hcost0]

theorem exists_preparedModularGeneralNative_all_stages_budget (m : ℕ)
    (Cgrid Amass Aanalytic Anorm : Fin (m + 1) → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ P : ℝ, 0 ≤ P → ∀ s : Fin (m + 1),
      let Cs := Classical.choose (exists_preparedModularGeneralNative_budget.{uI,uQ}
        m (s.val + 1) (Cgrid s) (Amass s) (Aanalytic s) (Anorm s))
      (P + Cs) ^ Cs ≤ (P + C) ^ C := by
  let Cs (s : Fin (m + 1)) := Classical.choose
    (exists_preparedModularGeneralNative_budget.{uI,uQ}
      m (s.val + 1) (Cgrid s) (Amass s) (Aanalytic s) (Anorm s))
  let poly : Polynomial ℕ := ∑ s : Fin (m + 1),
    (Polynomial.X + Polynomial.C (Cs s)) ^ Cs s
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro P hP s
  have hsum : (P + Cs s) ^ Cs s ≤ ∑ t : Fin (m + 1), (P + Cs t) ^ Cs t :=
    Finset.single_le_sum (f := fun t : Fin (m + 1) => (P + (Cs t : ℝ)) ^ Cs t)
      (fun t _ => pow_nonneg (by positivity) _) (Finset.mem_univ s)
  apply hsum.trans
  simpa [poly, Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow] using hbound P hP

end Erdos3.VectorPolynomial

end

end OAI
