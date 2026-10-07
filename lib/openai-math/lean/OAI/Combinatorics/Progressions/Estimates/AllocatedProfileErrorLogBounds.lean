import OAI.Combinatorics.Progressions.Linear.AllocatedProbabilityProfileKernel

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

def allocatedProfileErrorLog {A : Type*} [Semiring A] (P : A) : A :=
  2 * allocatedErrorKernelLog P + 7 * P + 3

theorem allocatedProfileErrorLog_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ allocatedProfileErrorLog P := by
  have h := allocatedErrorKernelLog_nonneg hP
  unfold allocatedProfileErrorLog
  positivity

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem allocatedProfileError_exp_bounds (A Cf Cg Kf Kg : ℝ≥0) (C V : Fin m → ℝ≥0)
    {P : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P)
    (hout : (Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) : ℝ) ≤ P)
    (hO : ∀ j, (Fintype.card (O j) : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hA : (A : ℝ) ≤ Real.exp P)
    (hK : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp P)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp P) (hV : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hCf : (Cf : ℝ) ≤ Real.exp P) (hCg : (Cg : ℝ) ≤ Real.exp P)
    (hKf : (Kf : ℝ) ≤ Real.exp P) (hKg : (Kg : ℝ) ≤ Real.exp P) :
    (allocatedProfileErrorCap B U b S (O := O) A Cf Cg V : ℝ) ≤
      Real.exp (allocatedProfileErrorLog P) ∧
    (allocatedProfileErrorLip B U b S (O := O) A Cf Cg Kf Kg C V : ℝ) ≤
      Real.exp (allocatedProfileErrorLog P) := by
  have hb := allocatedErrorKernel_exp_bounds B U b S 1 A C V hP hm haxes hout hO hJ
    le_rfl hA hK hC hV
  have hlog := allocatedErrorKernelLog_nonneg hP
  have hcap : (Cf : ℝ) + Cg ≤ Real.exp (2 * P + 1) := by
    simpa only [two_mul] using add_le_exp_add_one hP hP hCf hCg
  have hlip : (Kf : ℝ) + Kg ≤ Real.exp (2 * P + 1) := by
    simpa only [two_mul] using add_le_exp_add_one hP hP hKf hKg
  have hmE : (m : ℝ) ≤ Real.exp P := hm.trans (by linarith [Real.add_one_le_exp P])
  have hsum : (∑ j, (C j : ℝ) * Fintype.card (J j)) ≤ Real.exp (3 * P) := by
    calc
      _ ≤ ∑ _j : Fin m, Real.exp (2 * P) := Finset.sum_le_sum (fun j _ => by
        calc
          _ ≤ Real.exp P * Real.exp P := mul_le_mul (hC j)
            ((hJ j).trans (by linarith [Real.add_one_le_exp P])) (by positivity) (by positivity)
          _ = _ := by rw [← Real.exp_add]; congr 1; ring)
      _ = (m : ℝ) * Real.exp (2 * P) := by simp
      _ ≤ Real.exp P * Real.exp (2 * P) := mul_le_mul_of_nonneg_right hmE (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hfirst : (allocatedErrorKernelCap B U b S (O := O) 1 A V : ℝ) *
      (((Kf : ℝ) + Kg) * (∑ j, (C j : ℝ) * Fintype.card (J j))) ≤
      Real.exp (allocatedErrorKernelLog P + 5 * P + 1) := by
    calc
      _ ≤ Real.exp (allocatedErrorKernelLog P) * (Real.exp (2 * P + 1) * Real.exp (3 * P)) := by
        gcongr
        exact hb.1
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hsecond : ((Cf : ℝ) + Cg) * (allocatedErrorKernelLip B U b S (O := O) 1 A C V : ℝ) ≤
      Real.exp (allocatedErrorKernelLog P + 2 * P + 1) := by
    calc
      _ ≤ Real.exp (2 * P + 1) * Real.exp (allocatedErrorKernelLog P) := by
        gcongr
        exact hb.2
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  constructor
  · unfold allocatedProfileErrorCap
    simp only [NNReal.coe_mul, NNReal.coe_add]
    calc
      _ ≤ Real.exp (allocatedErrorKernelLog P) * Real.exp (2 * P + 1) := by
        gcongr
        exact hb.1
      _ = Real.exp (allocatedErrorKernelLog P + (2 * P + 1)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold allocatedProfileErrorLog; linarith)
  · unfold allocatedProfileErrorLip
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_sum, NNReal.coe_natCast]
    have h := add_le_exp_add_one (by positivity) (by positivity) hfirst hsecond
    exact h.trans_eq (congrArg Real.exp (by unfold allocatedProfileErrorLog; ring))

def allocatedProfileFourierInput {A : Type*} [Semiring A] (P : A) : A :=
  P + P ^ 3 + allocatedProfileErrorLog P

def allocatedProfileFourierOutput {A : Type*} [Semiring A] (P : A) : A :=
  let L := allocatedProfileFourierInput P
  P + 2 * L * (2 * L + 2) ^ 4 + L + (2 * L + 2) ^ 4

theorem allocatedProfileError_fourier_budget (A Cf Cg Kf Kg : ℝ≥0) (C V : Fin m → ℝ≥0)
    {P δ : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P)
    (hout : (Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) : ℝ) ≤ P)
    (hO : ∀ j, (Fintype.card (O j) : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hA : (A : ℝ) ≤ Real.exp P)
    (hK : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp P)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp P) (hV : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hCf : (Cf : ℝ) ≤ Real.exp P) (hCg : (Cg : ℝ) ≤ Real.exp P)
    (hKf : (Kf : ℝ) ≤ Real.exp P) (hKg : (Kg : ℝ) ≤ Real.exp P)
    (hδ : δ⁻¹ ≤ Real.exp P) :
    let L := allocatedProfileFourierInput P
    let Q := allocatedProfileFourierOutput P
    0 ≤ L ∧ P ≤ Q ∧ (Fintype.card (JetAmbientIndex O J) : ℝ) ≤ L ∧
      δ⁻¹ ≤ Real.exp L ∧
      (allocatedProfileErrorLip B U b S (O := O) A Cf Cg Kf Kg C V : ℝ) ≤ Real.exp L ∧
      Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp Q ∧
      Real.exp (2 * L * (2 * L + 2) ^ 4) * allocatedProfileErrorCap B U b S (O := O) A Cf Cg V ≤ Real.exp Q := by
  have hl := allocatedProfileErrorLog_nonneg hP
  have hL : 0 ≤ allocatedProfileFourierInput P := by unfold allocatedProfileFourierInput; positivity
  have hPL : P ≤ allocatedProfileFourierInput P := by
    unfold allocatedProfileFourierInput; nlinarith [pow_nonneg hP 3]
  have h3L : P ^ 3 ≤ allocatedProfileFourierInput P := by unfold allocatedProfileFourierInput; linarith
  have hlogL : allocatedProfileErrorLog P ≤ allocatedProfileFourierInput P := by
    unfold allocatedProfileFourierInput; nlinarith [pow_nonneg hP 3]
  have hb := allocatedProfileError_exp_bounds B U b S A Cf Cg Kf Kg C V hP hm haxes hout hO hJ
    hA hK hC hV hCf hCg hKf hKg
  have hF0 : 0 ≤ (2 * allocatedProfileFourierInput P + 2) ^ 4 := by positivity
  have hC0 : 0 ≤ 2 * allocatedProfileFourierInput P * (2 * allocatedProfileFourierInput P + 2) ^ 4 := by positivity
  have hQ : P ≤ allocatedProfileFourierOutput P := by unfold allocatedProfileFourierOutput; linarith
  have hfreq : (2 * allocatedProfileFourierInput P + 2) ^ 4 ≤ allocatedProfileFourierOutput P := by
    unfold allocatedProfileFourierOutput; linarith
  have hcoeff : 2 * allocatedProfileFourierInput P * (2 * allocatedProfileFourierInput P + 2) ^ 4 +
      allocatedProfileFourierInput P ≤ allocatedProfileFourierOutput P := by
    unfold allocatedProfileFourierOutput; nlinarith [sq_nonneg ((2 * allocatedProfileFourierInput P + 2) ^ 2)]
  refine ⟨hL, hQ, (jetAmbientIndex_card_le O J hP hm hO hJ).trans h3L,
    hδ.trans (Real.exp_le_exp.mpr hPL), hb.2.trans (Real.exp_le_exp.mpr hlogL),
    Real.exp_le_exp.mpr hfreq, ?_⟩
  calc
    _ ≤ Real.exp (2 * allocatedProfileFourierInput P * (2 * allocatedProfileFourierInput P + 2) ^ 4) *
        Real.exp (allocatedProfileFourierInput P) :=
      mul_le_mul_of_nonneg_left (hb.1.trans (Real.exp_le_exp.mpr hlogL)) (Real.exp_pos _).le
    _ = Real.exp (2 * allocatedProfileFourierInput P * (2 * allocatedProfileFourierInput P + 2) ^ 4 +
        allocatedProfileFourierInput P) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hcoeff

theorem exists_allocatedProfileFourierOutput_bound :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ P : ℝ, 0 ≤ P → allocatedProfileFourierOutput P ≤ (P + a) ^ a := by
  let poly : Polynomial ℕ := allocatedProfileFourierOutput Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro P hP
  simpa [poly, allocatedProfileFourierOutput, allocatedProfileFourierInput,
    allocatedProfileErrorLog, allocatedErrorKernelLog, Polynomial.eval₂_pow] using hbound P hP

end Erdos3.VectorPolynomial

end

end OAI
