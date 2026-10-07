import OAI.Combinatorics.Progressions.Estimates.AnchoredCoefficientCongruenceRemoval
import OAI.Combinatorics.Progressions.Lattices.AffineCoefficientAmplitudeCongruenceRemoval
import OAI.Combinatorics.Progressions.Lattices.AffineCoefficientCongruenceRemoval
import OAI.Combinatorics.Progressions.Lattices.SelectedResidueConstantMean

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem selectedResidueSmoothPMF_weighted_fourier_normalization {K I J : Type*}
    [Fintype K] [Fintype I] [Fintype J]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (w : (K × I → ℤ) → ℂ) (c : J → ℂ) (u : J → (K × I → ℤ) → ℂ)
    (keep : J → Prop) [DecidablePred keep] {C τ : ℝ}
    (hc : (∑ j, ‖c j‖) ≤ C) (hτ : 0 ≤ τ)
    (hkeep : ∀ j, keep j → ∀ x, u j x = 1)
    (hdiscard : ∀ j, ¬keep j →
      ‖∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
        (w x * u j x)‖ ≤ τ) :
    ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
        (w x * ∑ j, c j * u j x)) -
      (∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * w x) *
        (∑ j, if keep j then c j else 0)‖ ≤ C * τ := by
  have hproject := selectedResidueSmoothPMF_discard_error modulus G V hV hZ
    w c u keep hc hτ hdiscard
  have heq (x : K × I → ℤ) :
      (∑ j, if keep j then c j * u j x else 0) =
        ∑ j, if keep j then c j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : keep j
    · simp only [hj, ite_true, hkeep j hj x, mul_one]
    · simp only [hj, ite_false]
  simp_rw [heq, ← mul_assoc] at hproject
  rw [tsum_mul_right] at hproject
  simpa only [mul_assoc] using hproject

theorem selectedResidueSmoothPMF_weighted_density_normalization {K I J : Type*}
    [Fintype K] [Fintype I] [Fintype J]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (w D : (K × I → ℤ) → ℂ) (c : J → ℂ) (u : J → (K × I → ℤ) → ℂ)
    (keep : J → Prop) [DecidablePred keep] {C τ η : ℝ}
    (hc : (∑ j, ‖c j‖) ≤ C) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (hw : ∀ x ∈ rectangularWeightIndices 0 V 1, ‖w x‖ ≤ 1)
    (hkeep : ∀ j, keep j → ∀ x, u j x = 1)
    (hdiscard : ∀ j, ¬keep j →
      ‖∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
        (w x * u j x)‖ ≤ τ)
    (happrox : ∀ x ∈ rectangularWeightIndices 0 V 1,
      ‖D x - ∑ j, c j * u j x‖ ≤ η)
    (hmass : ‖(∑ j, if keep j then c j else 0) - 1‖ ≤ η) :
    ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
        (w x * D x)) -
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * w x‖ ≤
        2 * η + C * τ := by
  have hproject := selectedResidueSmoothPMF_weighted_fourier_normalization
    modulus G V hV hZ w c u keep hc hτ hkeep hdiscard
  have h := selectedResidueSmoothPMF_projection_approximation modulus G V hV hZ
    w D (fun x => ∑ j, c j * u j x)
    (fun _ => ∑ j, if keep j then c j else 0) (fun _ => 1)
    hη hw happrox (fun _ _ => hmass) (by
      simpa only [← mul_assoc, tsum_mul_right] using hproject)
  simpa only [mul_one] using h

end Erdos3

end

section

namespace Erdos3

open Polynomial

noncomputable def fourierModeError (B ε : ℝ) : ℝ := ε / (B + 1)

theorem fourierModeError_pos {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    0 < fourierModeError B ε := div_pos hε (by linarith)

theorem fourierModeError_cost_le {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    B * fourierModeError B ε ≤ ε := by
  have h := mul_le_mul_of_nonneg_right (show B ≤ B + 1 by linarith) (fourierModeError_pos hB hε).le
  have he : (B + 1) * fourierModeError B ε = ε := by
    unfold fourierModeError
    field_simp
  exact h.trans_eq he

theorem fourierModeError_inv_le_exp {P B ε : ℝ} (hP : 0 ≤ P) (_hB : 0 ≤ B)
    (hBP : B ≤ Real.exp P) (hε : 0 < ε) (hεP : 1 / ε ≤ Real.exp P) :
    1 / fourierModeError B ε ≤ Real.exp (2 * P + 2) := by
  have hb : B + 1 ≤ Real.exp (P + 1) := by
    simpa only [add_comm B 1] using one_add_le_exp_succ hP hBP
  rw [fourierModeError, one_div, inv_div]
  calc
    _ = (B + 1) * (1 / ε) := by ring
    _ ≤ Real.exp (P + 1) * Real.exp P :=
      mul_le_mul hb hεP (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (2 * P + 1) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem exists_fourier_uniform_budget (A B : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ P : ℝ, 0 ≤ P →
      Real.exp ((2 * P + 2 + A) ^ A) ≤ Real.exp ((P + C) ^ C) ∧
      Real.exp ((2 * P + 2 + B) ^ B) ≤ Real.exp ((P + C) ^ C) := by
  obtain ⟨C, hC, hp⟩ := exists_natPolynomial_eval_budget
    (((2 * X + 2 + Polynomial.C A) ^ A) + ((2 * X + 2 + Polynomial.C B) ^ B))
  refine ⟨C, hC, ?_⟩
  intro P hP
  have hh : (2 * P + 2 + A) ^ A + (2 * P + 2 + B) ^ B ≤ (P + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hp P hP
  have ha : 0 ≤ (2 * P + 2 + A) ^ A := by positivity
  have hb : 0 ≤ (2 * P + 2 + B) ^ B := by positivity
  exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith)⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem exists_affine_coefficient_amplitude_fourier_normalization (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (amplitude : (Option K × I → ℝ) → ℂ) (_hamp : ∀ x, ‖amplitude x‖ ≤ 1)
    {Lip : ℝ≥0} (_hLip : LipschitzWith Lip amplitude) (_hLipP : (Lip : ℝ) ≤ Real.exp P),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (amplitude (fun t => (z t : ℝ) / V t) * ∑ a, c a * layeredCoefficientCharacter
          (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
          p (fun k j => (z (k, j) : ℝ)))) -
      (∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        amplitude (fun t => (z t : ℝ) / V t)) *
      (∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0)‖ ≤ ε := by
  classical
  obtain ⟨A₀, _, hremove⟩ := exists_affine_coefficient_amplitude_congruence_removal m
  obtain ⟨A₁, _, hthreshold⟩ := exists_mode_residue_threshold_exp_budget m
  obtain ⟨A, hA, hbudget⟩ := exists_fourier_uniform_budget A₀ A₁
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth amplitude hamp Lip hLip hLipP
  let P' := 2 * P + 2
  let δ := fourierModeError B ε
  have hPP : P ≤ P' := by dsimp [P']; linarith
  have hEP : Real.exp P ≤ Real.exp P' := Real.exp_le_exp.mpr hPP
  have hδ : 0 < δ := fourierModeError_pos hB hε
  have hδP : 1 / δ ≤ Real.exp P' := fourierModeError_inv_le_exp hP hB hBP hε hεP
  obtain ⟨hb₀, hb₁⟩ := hbudget P hP
  obtain ⟨hside, _⟩ := hthreshold (Fintype.card I) (Fintype.card (Option K × I))
    P' C 1 S ρ δ (hP.trans hPP) (hn.trans hPP) (hd.trans hPP) hC (hCP.trans hEP)
    zero_le_one (Real.one_le_exp (hP.trans hPP)) hS (hSP.trans hEP) hρ (hρP.trans hEP) hδ hδP
  have hZ := selectedResidueSmoothWeight_pos_of_threshold m zero_le_one
    hS hρ hδ stride hs hstride H (fun j => hside.trans (hb₁.trans (hsize j))) G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  have hdiscard (a : F) (hbad : ¬affineCoefficientModeTrivial U (frequency a)) :
      ‖∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (amplitude (fun t => (z t : ℝ) / V t) * layeredCoefficientCharacter
          (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
          p (fun k j => (z (k, j) : ℝ)))‖ ≤ δ := by
    obtain ⟨_, hr⟩ := hremove (hP.trans hPP) (hn.trans hPP) (hd.trans hPP)
      U hC (hCP.trans hEP) (frequency a) (hbound a)
      ((not_affineCoefficientModeTrivial_iff U (frequency a)).mp hbad)
      p hp hm stride hs hS (hSP.trans hEP) hρ hδ (hρP.trans hEP) hδP hstride
      H (fun j => hb₀.trans (hsize j)) hrank (hb₀.trans hR) G hG V hV hwidth
      amplitude hamp hLip (hLipP.trans hEP)
    exact hr
  have hproj := selectedResidueSmoothPMF_weighted_fourier_normalization stride G V hV hZ
    (fun z => amplitude (fun t => (z t : ℝ) / V t)) c
    (fun a z => layeredCoefficientCharacter
      (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
      p (fun k j => (z (k, j) : ℝ)))
    (fun a => affineCoefficientModeTrivial U (frequency a)) hcoefficients hδ.le
    (fun a ha z => layeredCoefficientCharacter_eq_one_of_trivial U (frequency a) ha p hp hm
      (fun k j => (z (k, j) : ℝ))) hdiscard
  exact hproj.trans (fourierModeError_cost_le hB hε)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem exists_affine_coefficient_fourier_normalization (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (∑ a, c a * layeredCoefficientCharacter
          (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
          p (fun k j => (z (k, j) : ℝ)))) -
      (∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0)‖ ≤ ε := by
  classical
  obtain ⟨A₀, _, hremove⟩ := exists_affine_coefficient_congruence_removal m
  obtain ⟨A₁, _, hthreshold⟩ := exists_mode_residue_threshold_exp_budget m
  obtain ⟨A, hA, hbudget⟩ := exists_fourier_uniform_budget A₀ A₁
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
  let P' := 2 * P + 2
  let δ := fourierModeError B ε
  have hPP : P ≤ P' := by dsimp [P']; linarith
  have hEP : Real.exp P ≤ Real.exp P' := Real.exp_le_exp.mpr hPP
  have hδ : 0 < δ := fourierModeError_pos hB hε
  have hδP : 1 / δ ≤ Real.exp P' := fourierModeError_inv_le_exp hP hB hBP hε hεP
  obtain ⟨hb₀, hb₁⟩ := hbudget P hP
  obtain ⟨hside, _⟩ := hthreshold (Fintype.card I) (Fintype.card (Option K × I))
    P' C 1 S ρ δ (hP.trans hPP) (hn.trans hPP) (hd.trans hPP) hC (hCP.trans hEP)
    zero_le_one (Real.one_le_exp (hP.trans hPP)) hS (hSP.trans hEP) hρ (hρP.trans hEP) hδ hδP
  have hZ := selectedResidueSmoothWeight_pos_of_threshold m zero_le_one
    hS hρ hδ stride hs hstride H (fun j => hside.trans (hb₁.trans (hsize j))) G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  have hdiscard (a : F) (hbad : ¬affineCoefficientModeTrivial U (frequency a)) :
      ‖∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        ((1 : ℂ) * layeredCoefficientCharacter
          (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
          p (fun k j => (z (k, j) : ℝ)))‖ ≤ δ := by
    obtain ⟨_, hr⟩ := hremove (hP.trans hPP) (hn.trans hPP) (hd.trans hPP)
      U hC (hCP.trans hEP) (frequency a) (hbound a)
      ((not_affineCoefficientModeTrivial_iff U (frequency a)).mp hbad)
      p hp hm stride hs hS (hSP.trans hEP) hρ hδ (hρP.trans hEP) hδP hstride
      H (fun j => hb₀.trans (hsize j)) hrank (hb₀.trans hR) G hG V hV hwidth
    simpa only [one_mul] using hr
  have hproj := selectedResidueSmoothPMF_discard_error stride G V hV hZ (fun _ => 1) c
    (fun a z => layeredCoefficientCharacter
      (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
      p (fun k j => (z (k, j) : ℝ)))
    (fun a => affineCoefficientModeTrivial U (frequency a)) hcoefficients hδ.le hdiscard
  have hkeep (b : Option K → I → ℝ) :
      (∑ a, if affineCoefficientModeTrivial U (frequency a) then
        c a * layeredCoefficientCharacter
          (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ)))) p b
        else 0) = ∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : affineCoefficientModeTrivial U (frequency a)
    · simp only [ha, ite_true, layeredCoefficientCharacter_eq_one_of_trivial U (frequency a) ha p hp hm b,
        mul_one]
    · simp only [ha, ite_false]
  simp only [one_mul, hkeep, selectedResidueSmoothPMF_const] at hproj
  exact hproj.trans (fourierModeError_cost_le hB hε)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem exists_anchored_affine_coefficient_fourier_normalization (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    (origin : Option K → I → ℝ)
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (∑ a, c a * layeredCoefficientCharacter
          (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
          p (origin + fun k j => (z (k, j) : ℝ)))) -
      (∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0)‖ ≤ ε := by
  classical
  obtain ⟨A₀, _, hremove⟩ := exists_anchored_affine_coefficient_congruence_removal m
  obtain ⟨A₁, _, hthreshold⟩ := exists_mode_residue_threshold_exp_budget m
  obtain ⟨A, hA, hbudget⟩ := exists_fourier_uniform_budget A₀ A₁
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ origin J _ F _ P hP hn hd U C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
  let P' := 2 * P + 2
  let δ := fourierModeError B ε
  have hPP : P ≤ P' := by dsimp [P']; linarith
  have hEP : Real.exp P ≤ Real.exp P' := Real.exp_le_exp.mpr hPP
  have hδ : 0 < δ := fourierModeError_pos hB hε
  have hδP : 1 / δ ≤ Real.exp P' := fourierModeError_inv_le_exp hP hB hBP hε hεP
  obtain ⟨hb₀, hb₁⟩ := hbudget P hP
  obtain ⟨hside, _⟩ := hthreshold (Fintype.card I) (Fintype.card (Option K × I))
    P' C 1 S ρ δ (hP.trans hPP) (hn.trans hPP) (hd.trans hPP) hC (hCP.trans hEP)
    zero_le_one (Real.one_le_exp (hP.trans hPP)) hS (hSP.trans hEP) hρ (hρP.trans hEP) hδ hδP
  have hZ := selectedResidueSmoothWeight_pos_of_threshold m zero_le_one
    hS hρ hδ stride hs hstride H (fun j => hside.trans (hb₁.trans (hsize j))) G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  have hdiscard (a : F) (hbad : ¬affineCoefficientModeTrivial U (frequency a)) :
      ‖∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        ((1 : ℂ) * layeredCoefficientCharacter
          (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
          p (origin + fun k j => (z (k, j) : ℝ)))‖ ≤ δ := by
    obtain ⟨_, hr⟩ := hremove origin (hP.trans hPP) (hn.trans hPP) (hd.trans hPP)
      U hC (hCP.trans hEP) (frequency a) (hbound a)
      ((not_affineCoefficientModeTrivial_iff U (frequency a)).mp hbad)
      p hp hm stride hs hS (hSP.trans hEP) hρ hδ (hρP.trans hEP) hδP hstride
      H (fun j => hb₀.trans (hsize j)) hrank (hb₀.trans hR) G hG V hV hwidth
    simpa only [one_mul] using hr
  have hproj := selectedResidueSmoothPMF_discard_error stride G V hV hZ (fun _ => 1) c
    (fun a z => layeredCoefficientCharacter
      (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
      p (origin + fun k j => (z (k, j) : ℝ)))
    (fun a => affineCoefficientModeTrivial U (frequency a)) hcoefficients hδ.le hdiscard
  have hkeep (b : Option K → I → ℝ) :
      (∑ a, if affineCoefficientModeTrivial U (frequency a) then
        c a * layeredCoefficientCharacter
          (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ)))) p b
        else 0) = ∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : affineCoefficientModeTrivial U (frequency a)
    · simp only [ha, ite_true, layeredCoefficientCharacter_eq_one_of_trivial U (frequency a) ha p hp hm b,
        mul_one]
    · simp only [ha, ite_false]
  simp only [one_mul, hkeep, selectedResidueSmoothPMF_const] at hproj
  exact hproj.trans (fourierModeError_cost_le hB hε)

end Erdos3.VectorPolynomial

end

end OAI
