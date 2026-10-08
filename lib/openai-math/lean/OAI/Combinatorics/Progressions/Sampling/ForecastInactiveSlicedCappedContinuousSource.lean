/-
Modified for ProveIt: use an explicit reducible rewrite for the continuous
forecast expansion on Lean 4.32. The upstream theorem statements are unchanged.
-/
import OAI.Combinatorics.Progressions.Fourier.ForecastInactiveCharacterSite
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedFixedGridCap
import OAI.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedFixedScalarCapBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {A : Type*} [Fintype A]

noncomputable def forecastInactiveSlicedSiteNumerics
    (selected : A → Σ j : Fin m, Fin (n j)) (q Hchild : ℕ)
    (δ P Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0) : Prop :=
    let degree := fun a => (selected a).1.val + 1
    let denom := fun a => inactiveDenominator (principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
    let torus := fun a => blockTorusFactor (Fintype.card Empty) (degree a)
      (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
    let V := fun a => (torus a : ℝ) * ((denom a : ℝ) * 2 ^ degree a) / δ ^ degree a
    let cap := fun a => uniformSpectrumAbsoluteCap (selected a).1.val 1 (degree a) P (V a) (V a)
    let cutoff := fun a => max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
      (selected a).1 (selected a).2 (Nat.ceil ((q : ℝ) / δ)))
      (denom a * 2 ^ degree a * Hchild ^ degree a + 2 * denom a)
    let R0 := fun a => (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (degree a)) : ℝ) *
      R (selected a).1
    let ε := uniformProductAccuracy (Fintype.card A) Cactual δout / 2
    let ζ := fun a => uniformBlockRetainedBias (selected a).1.val 1 (degree a) P (V a) (V a) ε
    let freq := fun a => Real.toNNReal (uniformScaledRetainedFrequencyBound (selected a).1.val 1 P (V a) (ζ a))
    (∀ a, max (cutoff a : ℝ) (cap a) ≤ Cactual) ∧
    (∀ a, R0 a + 1 / 4 ≤ Real.exp Q) ∧
    (∀ a, (ε / (cap a + 1))⁻¹ ≤ Real.exp Q) ∧
    (∀ a, (CircleFourier.characterLipConstant * freq a + 4 : ℝ≥0) ≤ Real.exp Q) ∧
    (∀ a, (cutoff a : ℝ) ≤ Real.exp Q) ∧
    (∀ a, (2 * (cutoff a : ℝ≥0) ^ 2 * (cutoff a : ℝ≥0) : ℝ≥0) ≤ Real.exp Q) ∧
    ε⁻¹ ≤ Real.exp Q ∧
    (∀ a, max ((uniformSpectrumSizeConstant (selected a).1.val 1 (degree a) P (V a) (V a) /
      ε ^ max (majorArcSpectrumExponent (selected a).1.val 1)
        (majorArcLengthExponent (selected a).1.val * degree a)) * Real.exp (4 * Q + 8))
      (Real.exp (4 * Q + 8)) ≤ Nt) ∧
    (∀ a, max (uniformScaledRetainedDenominatorBound (selected a).1.val 1 (degree a) P
      (V a) (V a) (ζ a)) 1 ≤ Vt) ∧
    (∀ a, max (cap a * Real.exp (4 * Q + 8 + Q)) (Real.exp (4 * Q + 8 + Q)) ≤ Ct) ∧
    (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4 : ℝ≥0) ≤ Lt ∧
    (∀ a, R0 a + 1 / 4 ≤ Ht)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

local instance (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

theorem exists_forecastInactive_sliced_retained_character_sites
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (poly : Out → MvPolynomial (Vact ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)
    (N : ℕ) [NeZero N] (pRat : FiniteProbabilityWeights (Vact → ZMod N))
    (T : ℕ) (_hT : 0 < T)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (coefficients : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hcoefficients : ∀ a d, coefficients a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * T : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCtNonneg : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q)
    (hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
        δ P Cactual δout Q Nt Vt Ct Ht Lt) :
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let law := p.fiberLaw map
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val
          (progressionPrincipalResidue B (layerSamplerDegree I n) step c (orderOf χ.val) r.val)
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds Nt Vt Ct Lt Ht) ∧
      (∑ χ : Ch, ∑ t : Σ r : Pos χ, ∀ a, (e χ r a).Term,
        ‖forecastSiteMixtureCoefficient (e χ) (weight χ) t‖) ≤
        (T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ) (outPoint : Out → ZMod N),
        ‖(∑ χ : Ch, ((∏ a, (height a : ℝ)) : ℂ) *
          law.complexMean (fun y => finiteImageCharacteristic pRat
            (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ.val *
            (if forecastInactiveFixedOutput B U basis S selected coefficients x y = (fun a _ => z a)
              then (1 : ℂ) else 0)) * star (χ.val outPoint)) -
          (∑ χ : Ch, (∑ r : Pos χ, weight χ r *
            siteFamilyEval (e χ r) (fun _ => z) (fun _ a => (z a : ℝ) / height a)) *
              star (χ.val outPoint))‖ ≤ (T : ℝ) ^ (Fintype.card Out + 1) * δout := by
  intro p map law Ch Pos height weight
  have horder (χ : Ch) : orderOf χ.val ≤ T := (Finset.mem_filter.mp χ.property).2
  have hn (χ : Ch) := hnumerics (orderOf χ.val) (isOfFinOrder_of_finite χ.val).orderOf_pos (horder χ)
  have hstride' (χ : Ch) (a : A) b v :
      ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * orderOf χ.val : ℕ) : ℝ) ≤ P :=
    (Nat.cast_le.mpr (Nat.mul_le_mul_left _ (horder χ))).trans (hstride a b v)
  have heach (χ : Ch) := exists_forecastInactive_sliced_fixed_residue_site
    B U basis hR hσ S (orderOf χ.val) H step c hH hsubset selected hselected
    (forecastInactiveCharacterCoefficient poly N pRat χ.val)
    (forecastInactiveCharacterCoefficient_norm_le poly N pRat χ.val)
    δ P Hchild hδ hreg hsmall hgrid coefficients hcoefficients hσ1 L hL hP
    ((scalarCubePrimitiveEnvelope_mono Empty L (le_refl (1 : ℝ≥0))
      (le_refl (0 : ℝ≥0)) (horder χ)).trans hsP)
    (hstride' χ) hB Cactual δout Q Nt Vt Ct Ht Lt hCactual hCtNonneg hδout hQ
    ((hn χ).1) ((hn χ).2.1) ((hn χ).2.2.1) ((hn χ).2.2.2.1) ((hn χ).2.2.2.2.1) ((hn χ).2.2.2.2.2.1) ((hn χ).2.2.2.2.2.2.1) ((hn χ).2.2.2.2.2.2.2.1) ((hn χ).2.2.2.2.2.2.2.2.1) ((hn χ).2.2.2.2.2.2.2.2.2.1) ((hn χ).2.2.2.2.2.2.2.2.2.2.1) ((hn χ).2.2.2.2.2.2.2.2.2.2.2)
  choose e he hmass herr using heach
  have hcard : (Fintype.card Ch : ℝ) ≤ (T : ℝ) ^ (Fintype.card Out + 1) := by
    have hb := finiteCharacter_boundedOrder_card_le (integerResidueTuple (J := Out) N)
      (integerResidueTuple_surjective N) T
    have hnat : Fintype.card Ch ≤ T ^ (Fintype.card Out + 1) := by
      simpa only [Fintype.card_coe] using hb
    exact_mod_cast hnat
  refine ⟨e, he, ?_, ?_⟩
  · calc
      _ ≤ ∑ _χ : Ch, Ct ^ Fintype.card A := Finset.sum_le_sum (fun χ _ => hmass χ)
      _ = (Fintype.card Ch : ℝ) * Ct ^ Fintype.card A := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (pow_nonneg hCtNonneg _)
  · intro x z outPoint
    rw [← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _χ : Ch, δout := by
        apply Finset.sum_le_sum
        intro χ _
        rw [← sub_mul, norm_mul, norm_star, AddChar.norm_apply, mul_one]
        simp_rw [forecastInactive_principal_characteristic_residue]
        exact herr χ x z
      _ = (Fintype.card Ch : ℝ) * δout := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hδout.le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

def slicedFixedUniformSiteLog (m : ℕ) (p E : ℝ) : ℝ :=
  p + E + 1 + ∑ j : Fin m, slicedGridSiteLog j.val 1 (j.val + 1) (j.val + 1) 1 p E

theorem slicedFixedUniformSiteLog_nonneg (m : ℕ) {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) :
    0 ≤ slicedFixedUniformSiteLog m p E := by
  unfold slicedFixedUniformSiteLog
  have hs : 0 ≤ ∑ j : Fin m, slicedGridSiteLog j.val 1 (j.val + 1) (j.val + 1) 1 p E :=
    Finset.sum_nonneg (fun j _ => (slicedGridSiteLog_bounds j.val 1 (j.val + 1) (j.val + 1)
      (by norm_num : (0 : ℝ) ≤ 1) hp hE).1)
  positivity

theorem slicedGridSiteLog_le_uniform {m : ℕ} (j : Fin m) {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) :
    slicedGridSiteLog j.val 1 (j.val + 1) (j.val + 1) 1 p E ≤ slicedFixedUniformSiteLog m p E := by
  have hs := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin m))) =>
    (slicedGridSiteLog_bounds k.val 1 (k.val + 1) (k.val + 1)
      (by norm_num : (0 : ℝ) ≤ 1) hp hE).1) (Finset.mem_univ j)
  unfold slicedFixedUniformSiteLog
  linarith

def slicedFixedUniformAccuracyLog (m : ℕ) (D p E : ℝ) : ℝ :=
  uniformProductAccuracyLog D (slicedFixedUniformSiteLog m p 0) E + 1

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R : Fin m → ℝ} {A : Type*} [Fintype A]

theorem forecastInactiveSlicedSiteNumerics_of_uniform_envelope
    (selected : A → Σ j : Fin m, Fin (n j)) (q Hchild : ℕ)
    (δ P δout D p E : ℝ) (hδ : 0 < δ) (hP : 1 ≤ P) (hδout : 0 < δout)
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hcard : (Fintype.card A : ℝ) ≤ D) (hPp : P ≤ Real.exp p)
    (hδoutE : δout⁻¹ ≤ Real.exp E) :
    let degree := fun a => (selected a).1.val + 1
    let denom := fun a => inactiveDenominator (principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
    let torus := fun a => blockTorusFactor (Fintype.card Empty) (degree a)
      (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
    let V := fun a => (torus a : ℝ) * ((denom a : ℝ) * 2 ^ degree a) / δ ^ degree a
    let cutoff := fun a => max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
      (selected a).1 (selected a).2 (Nat.ceil ((q : ℝ) / δ)))
      (denom a * 2 ^ degree a * Hchild ^ degree a + 2 * denom a)
    let R0 := fun a => (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (degree a)) : ℝ) *
      R (selected a).1
    (∀ a, V a ≤ Real.exp p) → (∀ a, (cutoff a : ℝ) ≤ Real.exp p) →
    (∀ a, R0 a + 1 / 4 ≤ Real.exp p) →
    let Cactual := Real.exp (slicedFixedUniformSiteLog m p 0)
    let Eprod := slicedFixedUniformAccuracyLog m D p E
    let Q := slicedFixedUniformSiteLog m p Eprod
    let O := siteExponentialOutputLog 1 Q
    forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild δ P Cactual δout Q
      (Real.exp O) (Real.exp O) (Real.exp O) (Real.exp p) ⟨Real.exp O, Real.exp_nonneg _⟩ := by
  intro degree denom torus V cutoff R0 hVp hKp hRp Cactual Eprod Q O
  let cap a := uniformSpectrumAbsoluteCap (selected a).1.val 1 (degree a) P (V a) (V a)
  have hV (a : A) : 0 ≤ V a := by dsimp [V]; positivity
  have hcapLog : 0 ≤ slicedFixedUniformSiteLog m p 0 := slicedFixedUniformSiteLog_nonneg m hp le_rfl
  have hEprod : 0 ≤ Eprod := by
    dsimp [Eprod, slicedFixedUniformAccuracyLog]
    exact add_nonneg (uniformProductAccuracyLog_nonneg hD hcapLog hE) zero_le_one
  have hQ : 0 ≤ Q := slicedFixedUniformSiteLog_nonneg m hp hEprod
  have hactual (a : A) : max (cutoff a : ℝ) (cap a) ≤ Cactual := by
    have h := slicedGridPointCap_exp_bound 0 (selected a).1.val 1 (degree a) (degree a) (cutoff a)
      (by norm_num : (0 : ℝ) ≤ 1) hp (by norm_num) (by norm_num) hP (hV a) (hV a) (hV a) (hV a)
      hPp (hVp a) (hVp a) (hVp a) (hVp a) (hKp a)
    have hh : max (cutoff a : ℝ) (cap a) ≤ Real.exp
        (slicedGridSiteLog (selected a).1.val 1 (degree a) (degree a) 1 p 0) := by
      refine max_le ?_ ?_
      · simpa only [pow_one] using (le_max_left _ _).trans ((le_max_right _ _).trans h)
      · exact (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans h))
    exact hh.trans (Real.exp_le_exp.mpr (slicedGridSiteLog_le_uniform (selected a).1 hp le_rfl))
  let ε := uniformProductAccuracy (Fintype.card A) Cactual δout / 2
  obtain ⟨hτ, hτ1, _⟩ := uniformProductAccuracy_spec (Fintype.card A) (Real.exp_nonneg _) hδout
  have hε : 0 < ε := half_pos hτ
  have hε1 : ε ≤ 1 := by dsimp only [ε]; linarith
  have hεE : ε⁻¹ ≤ Real.exp Eprod := by
    have h := uniformProductAccuracy_inverse_exp_bound (Fintype.card A) (Real.exp_nonneg _) hδout
      hD hcapLog hE hcard (le_refl Cactual) hδoutE
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    dsimp only [ε]
    rw [inv_div, div_eq_mul_inv]
    exact (mul_le_mul htwo h (inv_nonneg.mpr hτ.le) (Real.exp_nonneg _)).trans_eq (by
      rw [← Real.exp_add]; congr 1; dsimp [Eprod, slicedFixedUniformAccuracyLog]; ring)
  have each (a : A) := slicedGridSite_numerics 0 (selected a).1.val 1 (degree a) (degree a) (cutoff a)
    (by norm_num : (0 : ℝ) ≤ 1) hp hEprod (by norm_num) (by norm_num) hP (hV a) (hV a) (hV a) (hV a)
    hPp (hVp a) (hVp a) (hVp a) (hVp a) (hKp a) (hRp a) hε hε1 hεE
  have hle (a : A) := Real.exp_le_exp.mpr (slicedGridSiteLog_le_uniform (selected a).1 hp hEprod)
  dsimp only [forecastInactiveSlicedSiteNumerics]
  refine ⟨hactual, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hRp⟩
  · intro a; exact (each a).2.1.trans (hle a)
  · intro a; exact (each a).2.2.2.1.trans (hle a)
  · intro a
    simpa only [Nat.cast_one, one_mul, pow_zero, mul_one] using (each a).2.2.2.2.2.1.trans (hle a)
  · intro a; simpa only [pow_one] using (each a).2.2.2.2.2.2.1.trans (hle a)
  · intro a
    simpa only [Nat.cast_one, one_mul, pow_one, pow_zero, mul_one] using
      (each a).2.2.2.2.2.2.2.1.trans (hle a)
  · apply hεE.trans
    apply Real.exp_le_exp.mpr
    have hs : 0 ≤ ∑ j : Fin m, slicedGridSiteLog j.val 1 (j.val + 1) (j.val + 1) 1 p Eprod :=
      Finset.sum_nonneg (fun j _ => (slicedGridSiteLog_bounds j.val 1 (j.val + 1) (j.val + 1)
        (by norm_num : (0 : ℝ) ≤ 1) hp hEprod).1)
    dsimp [Q, slicedFixedUniformSiteLog]
    linarith
  · intro a
    have hb := (le_max_right _ _).trans ((le_max_right _ _).trans (each a).2.2.2.2.2.2.2.2.2.1)
    have h1 := Real.one_le_exp_iff.mpr hQ
    obtain ⟨hT, _, _, _, _⟩ := siteExponentialOutput_bounds 1 1 le_rfl hQ (hb.trans (hle a)) h1 h1
    obtain ⟨hT1, _, _, _, _⟩ := siteExponentialOutput_bounds 1 1 le_rfl hQ h1 h1 h1
    exact max_le (by simpa only [Nat.cast_one, one_mul] using hT)
      (by simpa only [Nat.cast_one, one_mul, one_mul] using hT1)
  · intro a
    have hb := (le_max_right _ _).trans ((le_max_right _ _).trans (each a).2.2.2.2.2.2.2.2.2.2.1)
    have h1 := Real.one_le_exp_iff.mpr hQ
    obtain ⟨_, hper, _, _, he⟩ := siteExponentialOutput_bounds 1 1 le_rfl hQ h1 (hb.trans (hle a)) h1
    exact max_le hper (h1.trans he)
  · intro a
    have hb := (le_max_right _ _).trans ((le_max_right _ _).trans (each a).2.2.2.2.2.2.2.2.2.2.2)
    have h1 := Real.one_le_exp_iff.mpr hQ
    obtain ⟨_, _, hc, _, _⟩ := siteExponentialOutput_bounds 1 1 le_rfl hQ h1 h1 (hb.trans (hle a))
    obtain ⟨_, _, hc1, _, _⟩ := siteExponentialOutput_bounds 1 1 le_rfl hQ h1 h1 h1
    exact max_le (by simpa only [Nat.cast_one, one_mul] using hc)
      (by simpa only [Nat.cast_one, one_mul, one_mul] using hc1)
  · have h1 := Real.one_le_exp_iff.mpr hQ
    have hL := (siteExponentialOutput_bounds 1 1 le_rfl hQ h1 h1 h1).2.2.2.1
    exact_mod_cast hL

theorem forecastInactiveSlicedSiteNumerics_of_primitive_uniform_budgets
    (selected : A → Σ j : Fin m, Fin (n j)) (T Hchild : ℕ)
    (δ P δout D p E v w vq vchild : ℝ)
    (hδ : 0 < δ) (hP : 1 ≤ P) (hδout : 0 < δout) (hD : 1 ≤ D)
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hvq : 0 ≤ vq) (hvc : 0 ≤ vchild)
    (hcard : (Fintype.card A : ℝ) ≤ D) (hPp : P ≤ Real.exp p)
    (hδoutE : δout⁻¹ ≤ Real.exp E) (hδw : δ⁻¹ ≤ Real.exp w)
    (hTv : (T : ℝ) ≤ Real.exp vq) (hchild : (Hchild : ℝ) ≤ Real.exp vchild)
    (hR : ∀ a, 0 < R (selected a).1)
    (hdegree : ∀ a, (((selected a).1.val + 1 : ℕ) : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hb : ∀ a, (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩) : ℝ) ≤ D)
    (hRv : ∀ a, R (selected a).1 ≤ Real.exp v)
    (hRi : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp v)
    (hcoeff : ∀ a, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1)) : ℝ) ≤ Real.exp v) :
    let pAll := p + slicedFixedZeroGeometryLog D v w vq vchild
    let Cactual := Real.exp (slicedFixedUniformSiteLog m pAll 0)
    let Eprod := slicedFixedUniformAccuracyLog m D pAll E
    let Q := slicedFixedUniformSiteLog m pAll Eprod
    let O := siteExponentialOutputLog 1 Q
    0 ≤ Q ∧ 0 ≤ O ∧ ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild δ P Cactual δout Q
        (Real.exp O) (Real.exp O) (Real.exp O) (Real.exp pAll) ⟨Real.exp O, Real.exp_nonneg _⟩ := by
  intro pAll Cactual Eprod Q O
  have hD0 := zero_le_one.trans hD
  have hg := slicedFixedZeroGeometryLog_nonneg hD0 hv hw hvq hvc
  have hpAll : 0 ≤ pAll := add_nonneg hp hg
  have hpLe : p ≤ pAll := le_add_of_nonneg_right hg
  have hgLe : slicedFixedZeroGeometryLog D v w vq vchild ≤ pAll := le_add_of_nonneg_left hp
  have hcapLog := slicedFixedUniformSiteLog_nonneg m hpAll (le_refl (0 : ℝ))
  have hEprod : 0 ≤ Eprod := by
    dsimp [Eprod, slicedFixedUniformAccuracyLog]
    exact add_nonneg (uniformProductAccuracyLog_nonneg hD0 hcapLog hE) zero_le_one
  have hQ := slicedFixedUniformSiteLog_nonneg m hpAll hEprod
  refine ⟨hQ, siteExponentialOutputLog_nonneg 1 hQ, ?_⟩
  intro q _ hqT
  have hqv : (q : ℝ) ≤ Real.exp vq := (Nat.cast_le.mpr hqT).trans hTv
  have hgeom (a : A) := forecastInactive_sliced_fixed_zero_axis_geometry_bounds
    (B := B) (R := R) (j := (selected a).1) (i := (selected a).2) (q := q) (Hchild := Hchild)
    hD hv hw hvq hvc hδ (hR a) (hdegree a) htail (hb a) (hRv a) (hRi a) hδw hqv hchild (hcoeff a)
  exact forecastInactiveSlicedSiteNumerics_of_uniform_envelope B selected q Hchild δ P δout D pAll E
    hδ hP hδout hD0 hpAll hE hcard (hPp.trans (Real.exp_le_exp.mpr hpLe)) hδoutE
    (fun a => (hgeom a).1.trans (Real.exp_le_exp.mpr hgLe))
    (fun a => (hgeom a).2.1.trans (Real.exp_le_exp.mpr hgLe))
    (fun a => (hgeom a).2.2.trans (Real.exp_le_exp.mpr hgLe))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

local instance (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

theorem exists_forecastInactive_sliced_rational_site_approximation
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (poly : Out → MvPolynomial (Vact ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)
    (N : ℕ) [NeZero N] (pRat : FiniteProbabilityWeights (Vact → ZMod N))
    (T : ℕ) (hT : 0 < T)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (coefficients : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hcoefficients : ∀ a d, coefficients a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * T : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCtNonneg : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q)
    (hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
        δ P Cactual δout Q Nt Vt Ct Ht Lt)
    {Cdecay Pdecay : ℝ} (hCdecay : 0 ≤ Cdecay)
    (hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay)
    (hdecay : ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
        (allocatedPrincipalSides B U basis S)) (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic pRat
        (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ‖ ≤
        Cdecay * (orderOf χ : ℝ) ^ (-Pdecay)) :
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let law := p.fiberLaw map
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val
          (progressionPrincipalResidue B (layerSamplerDegree I n) step c (orderOf χ.val) r.val)
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds Nt Vt Ct Lt Ht) ∧
      (∑ χ : Ch, ∑ t : Σ r : Pos χ, ∀ a, (e χ r a).Term,
        ‖forecastSiteMixtureCoefficient (e χ) (weight χ) t‖) ≤
        (T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ) (outPoint : Out → ZMod N),
        ‖(rationalInactiveForecast law (fun _ => pRat)
          (forecastInactiveFixedOutput B U basis S selected coefficients x)
          (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
          N (∏ a, (height a : ℝ)) (fun a _ => z a) outPoint : ℂ) -
          (∑ χ : Ch, (∑ r : Pos χ, weight χ r *
            siteFamilyEval (e χ r) (fun _ => z) (fun _ a => (z a : ℝ) / height a)) *
              star (χ.val outPoint))‖ ≤
          (∏ a, (height a : ℝ)) * law.fiberMean
            (forecastInactiveFixedOutput B U basis S selected coefficients x)
            (fun a _ => z a) (fun _ => 1) * (Cdecay / T) +
            (T : ℝ) ^ (Fintype.card Out + 1) * δout := by
  intro p map law Ch Pos height weight
  obtain ⟨e, he, hmass, herr⟩ := exists_forecastInactive_sliced_retained_character_sites
    B U basis hR hσ S H step c hH hsubset selected hselected poly N pRat T hT
    δ P Hchild hδ hreg hsmall hgrid coefficients hcoefficients hσ1 L hL hP hsP
    hstride hB Cactual δout Q Nt Vt Ct Ht Lt hCactual hCtNonneg hδout hQ hnumerics
  refine ⟨e, he, hmass, ?_⟩
  intro x z outPoint
  apply rationalInactiveForecast_retained_approximation law (fun _ => pRat)
    (forecastInactiveFixedOutput B U basis S selected coefficients x)
    (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
    N (show 0 ≤ ∏ a, (height a : ℝ) from
      Finset.prod_nonneg (fun a _ => Nat.cast_nonneg (height a))) hCdecay hPdecay hdecay
    T hT (fun a _ => z a) outPoint _
  simpa only [Complex.ofReal_prod, Complex.ofReal_natCast] using herr x z outPoint

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R : Fin m → ℝ} {A : Type*} [Fintype A]

theorem forecastInactiveSlicedTailCap_of_primitive_uniform_budgets
    (selected : A → Σ j : Fin m, Fin (n j)) (Hchild : ℕ)
    (δ P D p v w vchild : ℝ)
    (hδ : 0 < δ) (hP : 1 ≤ P) (hD : 1 ≤ D)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hvc : 0 ≤ vchild)
    (hcard : (Fintype.card A : ℝ) ≤ D) (hPp : P ≤ Real.exp p)
    (hδw : δ⁻¹ ≤ Real.exp w) (hchild : (Hchild : ℝ) ≤ Real.exp vchild)
    (hR : ∀ a, 0 < R (selected a).1)
    (hdegree : ∀ a, (((selected a).1.val + 1 : ℕ) : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hb : ∀ a, (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩) : ℝ) ≤ D)
    (hRv : ∀ a, R (selected a).1 ≤ Real.exp v)
    (hRi : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp v)
    (hcoeff : ∀ a, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1)) : ℝ) ≤ Real.exp v) :
    let Ctail := Real.exp (slicedFixedUniformSiteLog m
      (p + slicedFixedZeroGeometryLog D v w 0 vchild) 0)
    ∀ a,
      let degree := (selected a).1.val + 1
      let denom := inactiveDenominator (principalProfileSize (R (selected a).1)
        (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
      let torus := blockTorusFactor (Fintype.card Empty) degree
        (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
      let V := (torus : ℝ) * ((denom : ℝ) * 2 ^ degree) / δ ^ degree
      let cutoff := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
        (selected a).1 (selected a).2 (Nat.ceil ((1 : ℝ) / δ)))
        (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
      max (cutoff : ℝ)
        (uniformSpectrumAbsoluteCap (selected a).1.val 1 degree P V V) ≤ Ctail := by
  have hnum := forecastInactiveSlicedSiteNumerics_of_primitive_uniform_budgets
    B selected 1 Hchild δ P 1 D p 0 v w 0 vchild
    hδ hP (by norm_num) hD hp (le_refl 0) hv hw (le_refl 0) hvc hcard hPp
    (by simp) hδw (by simp) hchild hR hdegree htail hb hRv hRi hcoeff
  simpa only [Nat.cast_one] using (hnum.2.2 1 (by norm_num) le_rfl).1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

local instance (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

theorem exists_forecastInactive_sliced_continuous_rational_source
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (poly : Out → MvPolynomial (Vact ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)
    (N : ℕ) [NeZero N] (pRat : FiniteProbabilityWeights (Vact → ZMod N))
    (T : ℕ) (hT : 0 < T)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (coefficients : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hcoefficients : ∀ a d, coefficients a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * T : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCtNonneg : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q)
    (hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
        δ P Cactual δout Q Nt Vt Ct Ht Lt)
    {Cdecay Pdecay : ℝ} (hCdecay : 0 ≤ Cdecay)
    (hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay)
    (hdecay : ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
        (allocatedPrincipalSides B U basis S)) (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic pRat
        (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ‖ ≤
        Cdecay * (orderOf χ : ℝ) ^ (-Pdecay))
    {SmoothCoord : Type*} [PseudoMetricSpace SmoothCoord]
    (density : SmoothCoord → ℝ) (Hdensity : ℝ) (hHdensity : 1 ≤ Hdensity)
    (hdensity : ∀ y, ‖density y‖ ≤ Hdensity)
    (densityLip : ℝ≥0) (hdensityLip : LipschitzWith densityLip density) :
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let law := p.fiberLaw map
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    letI : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
      dsimp only [Pos]
      infer_instance
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val
          (progressionPrincipalResidue B (layerSamplerDegree I n) step c (orderOf χ.val) r.val)
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds Nt Vt Ct Lt Ht) ∧
      let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
      let coeff := fun t : Term => (Hdensity : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
      let factor := fun (outPoint : Out → ZMod N) (t : Term) (z : A → ℤ)
          (y : SmoothCoord × (A → ℝ)) =>
        (star (t.1.val outPoint) * ((density y.1 : ℂ) / (Hdensity : ℂ))) *
          siteFamilyFactor (e t.1 t.2.1) t.2.2 ∅
            (fun a => (z a : ZMod ((e t.1 t.2.1 a).period (t.2.2 a)))) y.2
      (∑ t : Term, ‖coeff t‖) ≤ Hdensity * ((T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A) ∧
      (∀ outPoint t z y, ‖factor outPoint t z y‖ ≤ 1) ∧
      (∀ outPoint t z, LipschitzWith (densityLip + Fintype.card A * Lt) (factor outPoint t z)) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ)
          (outPoint : Out → ZMod N) (y : SmoothCoord),
        ‖(density y : ℂ) * (rationalInactiveForecast law (fun _ => pRat)
          (forecastInactiveFixedOutput B U basis S selected coefficients x)
          (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
          N (∏ a, (height a : ℝ)) (fun a _ => z a) outPoint : ℂ) -
          ∑ t : Term, coeff t * factor outPoint t z (y, fun a => (z a : ℝ) / height a)‖ ≤
          Hdensity * ((∏ a, (height a : ℝ)) * law.fiberMean
            (forecastInactiveFixedOutput B U basis S selected coefficients x)
            (fun a _ => z a) (fun _ => 1) * (Cdecay / T) +
            (T : ℝ) ^ (Fintype.card Out + 1) * δout) := by
  intro p map law Ch Pos height weight
  let _ : ∀ χ : Ch, Fintype (Pos χ) := fun _ => by
    dsimp only [Pos]
    infer_instance
  obtain ⟨e, he, hmass, herr⟩ := exists_forecastInactive_sliced_rational_site_approximation
    B U basis hR hσ S H step c hH hsubset selected hselected poly N pRat T hT
    δ P Hchild hδ hreg hsmall hgrid coefficients hcoefficients hσ1 L hL hP hsP
    hstride hB Cactual δout Q Nt Vt Ct Ht Lt hCactual hCtNonneg hδout hQ hnumerics
    hCdecay hPdecay hdecay
  refine ⟨e, he, ?_⟩
  intro Term coeff factor
  have hext (outPoint : Out → ZMod N) := forecastRetained_continuous_expansion
    density Hdensity hHdensity hdensity densityLip hdensityLip e he weight
    (fun χ : Ch => star (χ.val outPoint))
    (fun _ => by simp only [norm_star, AddChar.norm_apply]; exact le_rfl) hmass
  refine ⟨(hext 0).1, (fun b t z => (hext b).2.1 t z),
    (fun b t z => (hext b).2.2.1 t z), ?_⟩
  intro x z outPoint y
  have hfinal := forecastRetained_continuous_error density Hdensity hHdensity hdensity y (herr x z outPoint)
  erw [(hext outPoint).2.2.2 z (y, fun a => (z a : ℝ) / height a)] at hfinal
  exact hfinal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

local instance (N : ℕ) [NeZero N] (χ : AddChar (Out → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

theorem exists_forecastInactive_sliced_capped_continuous_rational_source
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (poly : Out → MvPolynomial (Vact ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)
    (N : ℕ) [NeZero N] (pRat : FiniteProbabilityWeights (Vact → ZMod N))
    (T : ℕ) (hT : 0 < T)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (coefficients : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hcoefficients : ∀ a d, coefficients a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * T : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCtNonneg : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q)
    (hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
        δ P Cactual δout Q Nt Vt Ct Ht Lt)
    {Cdecay Pdecay : ℝ} (hCdecay : 0 ≤ Cdecay)
    (hPdecay : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ Pdecay)
    (hdecay : ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
        (allocatedPrincipalSides B U basis S)) (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic pRat
        (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ‖ ≤
        Cdecay * (orderOf χ : ℝ) ^ (-Pdecay))
    {SmoothCoord : Type*} [PseudoMetricSpace SmoothCoord]
    (density : SmoothCoord → ℝ) (Hdensity : ℝ) (hHdensity : 1 ≤ Hdensity)
    (hdensity : ∀ y, ‖density y‖ ≤ Hdensity)
    (densityLip : ℝ≥0) (hdensityLip : LipschitzWith densityLip density) :
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let law := p.fiberLaw map
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    letI : ∀ χ : Ch, Fintype (Pos χ) := fun χ => by
      dsimp only [Pos]
      infer_instance
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val
          (progressionPrincipalResidue B (layerSamplerDegree I n) step c (orderOf χ.val) r.val)
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds Nt Vt Ct Lt Ht) ∧
      let Term := Σ χ : Ch, Σ r : Pos χ, ∀ a, (e χ r a).Term
      let coeff := fun t : Term => (Hdensity : ℂ) * forecastSiteMixtureCoefficient (e t.1) (weight t.1) t.2
      let factor := fun (outPoint : Out → ZMod N) (t : Term) (z : A → ℤ)
          (y : SmoothCoord × (A → ℝ)) =>
        (star (t.1.val outPoint) * ((density y.1 : ℂ) / (Hdensity : ℂ))) *
          siteFamilyFactor (e t.1 t.2.1) t.2.2 ∅
            (fun a => (z a : ZMod ((e t.1 t.2.1 a).period (t.2.2 a)))) y.2
      (∑ t : Term, ‖coeff t‖) ≤ Hdensity * ((T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A) ∧
      (∀ outPoint t z y, ‖factor outPoint t z y‖ ≤ 1) ∧
      (∀ outPoint t z, LipschitzWith (densityLip + Fintype.card A * Lt) (factor outPoint t z)) ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ)
          (outPoint : Out → ZMod N) (y : SmoothCoord),
        ‖(density y : ℂ) * (rationalInactiveForecast law (fun _ => pRat)
          (forecastInactiveFixedOutput B U basis S selected coefficients x)
          (fun y t j => integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j)
          N (∏ a, (height a : ℝ)) (fun a _ => z a) outPoint : ℂ) -
          ∑ t : Term, coeff t * factor outPoint t z (y, fun a => (z a : ℝ) / height a)‖ ≤
          Hdensity * (Cactual ^ Fintype.card A * (Cdecay / T) +
            (T : ℝ) ^ (Fintype.card Out + 1) * δout) := by
  intro p map law Ch Pos height weight
  let _ : ∀ χ : Ch, Fintype (Pos χ) := fun _ => by
    dsimp only [Pos]
    infer_instance
  obtain ⟨e, he, hrest⟩ := exists_forecastInactive_sliced_continuous_rational_source
    B U basis hR hσ S H step c hH hsubset selected hselected poly N pRat T hT
    δ P Hchild hδ hreg hsmall hgrid coefficients hcoefficients hσ1 L hL hP hsP
    hstride hB Cactual δout Q Nt Vt Ct Ht Lt hCactual hCtNonneg hδout hQ hnumerics
    hCdecay hPdecay hdecay density Hdensity hHdensity hdensity densityLip hdensityLip
  refine ⟨e, he, ?_⟩
  intro Term coeff factor
  refine ⟨hrest.1, hrest.2.1, hrest.2.2.1, ?_⟩
  intro x z outPoint y
  have h1T : 1 ≤ T := hT
  have hprimitive1 : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ P :=
    (scalarCubePrimitiveEnvelope_mono Empty L (le_refl (1 : ℝ≥0))
      (le_refl (0 : ℝ≥0)) h1T).trans hsP
  have hstride1 (a : A) b v :
      (step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ) ≤ P := by
    have hs := (Nat.cast_le.mpr (Nat.mul_le_mul_left
      (step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩) h1T)).trans (hstride a b v)
    simpa only [mul_one] using hs
  have hnum1 := hnumerics 1 zero_lt_one h1T
  have hcap := forecastInactive_sliced_fixed_grid_mass_le
    B U basis hR hσ S H step c hH hsubset selected hselected δ P Hchild hδ hreg hsmall hgrid
    coefficients hcoefficients L hL hP hprimitive1 hstride1 hB Cactual hCactual
    (by simpa only [Nat.cast_one] using hnum1.1) x z
  exact (hrest.2.2.2 x z outPoint y).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_right hcap (div_nonneg hCdecay (Nat.cast_nonneg T))) le_rfl)
      (zero_le_one.trans hHdensity))

end Erdos3.VectorPolynomial

end

end OAI
