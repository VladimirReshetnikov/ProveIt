import OAI.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem allocatedIntegerJet_bound {J V α O : Type*} [Fintype J] [DecidableEq α]
    (P : Finset J) (j₀ : J) (h K L s : ℕ) (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
    (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
    (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
    (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
    (hgap : L^h < K → (principalSamplingGapRatio (principalProfileSize R P.card)*L)^h ≤ K)
    (hεL : 8*(probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J)*L)
    (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0) (hσ1 : σ ≤ 1)
    (hprincipal : ∀ j ∈ P, monomialScale T (e j) =
      (integerAxisSideLength h K L (principalProfileSize R P.card) : ℝ)^h)
    (a : J → ℤ) (ha : ∀ j, a j ∈ (allocatedIntegerPolynomialCoordinatePMF P j₀ h K L s
      hh hK hL T hT hTL e he R σ hR hσ hgap hεL j).support)
    (vertices : Finset α → V → ℤ) (rows : O → Finset α) (o : O) (q : ℕ)
    (hrows : (rows o).card ≤ q)
    (hx : ∀ t ∈ (rows o).powerset, ∀ v, |(vertices t v : ℝ)| ≤ T v) :
    |((integerJetMatrix (fun j => MvPolynomial.monomial (e j) (1 : ℤ)) vertices rows *ᵥ a) o : ℝ)| ≤
      2^q*(3*R/4)*(K : ℝ) := by
  let f := fun t => MvPolynomial.eval (vertices t) (integerMonomialArrayPolynomial e a)
  have hv (t) (ht : t ∈ (rows o).powerset) : |(f t : ℝ)/(K : ℝ)| ≤ 3*R/4 :=
    allocatedIntegerPolynomial_integer_box P j₀ h K L s hh hK hL T hT hTL e he
      R σ hR hσ hgap hεL hj₀ he₀ hσ1 hprincipal a ha (vertices t) (hx t ht)
  have hb := booleanCoefficient_abs_le (fun t => (f t : ℝ)/(K : ℝ)) (rows o) hv
  rw [booleanCoefficient_div] at hb
  have hc := booleanCoefficient_map (Int.castRingHom ℝ) f (rows o)
  simp only [Int.coe_castRingHom] at hc
  rw [← hc, abs_div, abs_of_pos (show (0 : ℝ) < K by exact_mod_cast hK)] at hb
  have hj : (integerJetMatrix (fun j => MvPolynomial.monomial (e j) (1 : ℤ)) vertices rows *ᵥ a) o =
      booleanCoefficient f (rows o) := by
    simpa only [f, MvPolynomial.C_mul_monomial, mul_one, integerMonomialArrayPolynomial] using
      integerJetMatrix_apply_coefficients (fun j => MvPolynomial.monomial (e j) (1 : ℤ)) vertices rows a o
  rw [hj]
  exact ((div_le_iff₀ (show (0 : ℝ) < K by exact_mod_cast hK)).mp hb).trans
    (by gcongr; norm_num)

noncomputable def allocatedIntegerJetRadius (q : ℕ) (R : ℝ) : ℕ := ⌈(2 : ℝ)^q*(3*R/4)⌉₊

theorem allocatedIntegerJetRadius_le_exp (q : ℕ) {R r : ℝ}
    (hR : 0 ≤ R) (hr : 0 ≤ r) (hRr : R ≤ Real.exp r) :
    (allocatedIntegerJetRadius q R : ℝ) ≤ Real.exp (q+r+1) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hraw : (2 : ℝ)^q*(3*R/4) ≤ Real.exp (q+r) := by
    calc
      _ ≤ (Real.exp 1)^q*Real.exp r := by
        apply mul_le_mul (pow_le_pow_left₀ (by norm_num) htwo q) (by linarith)
          (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; simp only [mul_one]
  exact natCeil_le_exp_succ (by positivity) (by positivity) hraw

namespace VectorPolynomial

theorem allocatedLayerIntegerJet_bound {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ) (hσ1 : ∀ j, σ j ≤ 1)
    (j : Fin m) (i : Fin (n j))
    (a : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    {α O : Type*} [DecidableEq α]
    (vertices : Finset α → LayerSamplerVariables G I n B → ℤ) (rows : O → Finset α)
    (o : O) (q : ℕ) (hrows : (rows o).card ≤ q)
    (hx : ∀ t ∈ (rows o).powerset, ∀ v, |(vertices t v : ℝ)| ≤ layerSamplerBox B U basis S v) :
    |((integerJetMatrix (fun d => MvPolynomial.monomial d.val (1 : ℤ)) vertices rows *ᵥ a) o : ℝ)| ≤
      2^q*(3*R j/4)*(basisAxisScale (basis j) i : ℝ) := by
  exact allocatedIntegerJet_bound (layerIntegerPrincipalSlots (G := G) B j i)
    (constantCoefficientSlot _ _) (j.val+1) (basisAxisScale (basis j) i) S.value (layerTailDegree m)
    (Nat.zero_lt_succ _) (basisAxisScale_pos (basis j) i) S.positive
    (layerSamplerBox B U basis S)
    (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
    (layerSamplerBox_le B U basis S) Subtype.val
    (fun d => d.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j i) (S.width j)
    (layerIntegerPrincipalSlots_not_constant B j i) rfl (hσ1 j)
    (layerSamplerSides_integer_principal B U basis R S.value j i) a ha vertices rows o q hrows hx

end VectorPolynomial
end Erdos3

end

end OAI
