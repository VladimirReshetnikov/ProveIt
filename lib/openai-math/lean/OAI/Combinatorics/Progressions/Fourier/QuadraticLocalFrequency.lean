/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Fourier.QuadraticFrequencyCoordinates

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

variable {ι κ D V : Type} [Fintype ι] [Fintype κ]
  [AddCommGroup V] [Module ℝ V]

noncomputable def affineBasisCoefficient
    (B : Basis ι ℝ (κ → ℝ)) (β : κ → D → V) (i : ι) (d : D) : V :=
  ∑ j, B i j • β j d

noncomputable def affineBasisConstant
    (B : Basis ι ℝ (κ → ℝ)) (α : D → V) (β : κ → D → V) (c : ι → ℝ) (d : D) : V :=
  α d + ∑ i, c i • affineBasisCoefficient B β i d

theorem affine_basis_coordinate_sum
    (B : Basis ι ℝ (κ → ℝ)) (β : κ → D → V) (v : ι → ℝ) (d : D) :
    (∑ j, B.equivFun.symm v j • β j d) = ∑ i, v i • affineBasisCoefficient B β i d := by
  classical
  rw [Basis.equivFun_symm_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, affineBasisCoefficient,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem affine_basis_change
    (B : Basis ι ℝ (κ → ℝ)) (α : D → V) (β : κ → D → V)
    (c u : ι → ℝ) (d : D) :
    α d + ∑ j, B.equivFun.symm (c + u) j • β j d =
      affineBasisConstant B α β c d + ∑ i, u i • affineBasisCoefficient B β i d := by
  rw [affine_basis_coordinate_sum]
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, affineBasisConstant, add_assoc]

omit [Fintype ι] in
theorem affineBasisCoefficient_mem
    (B : Basis ι ℝ (κ → ℝ)) (β : κ → D → V) (U : D → Submodule ℝ V)
    (hβ : ∀ j d, β j d ∈ U d) (i : ι) (d : D) :
    affineBasisCoefficient B β i d ∈ U d :=
  Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hβ j d))

theorem affineBasisConstant_mem
    (B : Basis ι ℝ (κ → ℝ)) (α : D → V) (β : κ → D → V) (c : ι → ℝ)
    (U : D → Submodule ℝ V) (hα : ∀ d, α d ∈ U d) (hβ : ∀ j d, β j d ∈ U d) (d : D) :
    affineBasisConstant B α β c d ∈ U d :=
  Submodule.add_mem _ (hα d) (Submodule.sum_mem _
    (fun i _ => Submodule.smul_mem _ _ (affineBasisCoefficient_mem B β U hβ i d)))

theorem positiveUnivariate_affine_basis_change [Module ℚ V]
    {s : ℕ} (B : Basis ι ℝ (κ → ℝ)) (α : Fin s → V) (β : κ → Fin s → V)
    (c u : ι → ℝ) (Γ : VectorPolynomial Unit ℚ V) :
    Γ + positiveUnivariate (fun d => α d + ∑ j, B.equivFun.symm (c + u) j • β j d) =
      Γ + positiveUnivariate (fun d => affineBasisConstant B α β c d +
        ∑ i, u i • affineBasisCoefficient B β i d) := by
  congr 2
  funext d
  exact affine_basis_change B α β c u d

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem exists_local_affine_scalar_chart
    {r N : ℕ} [NeZero N] {p : ℝ} (hp : 0 ≤ p) (hr : (r : ℝ) ≤ p)
    (η : (Fin r → ℤ) →+ ZMod N) (R : Fin r → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N)) (hJ : J.Nonempty)
    (hdense : Real.exp (-p) * N ≤ (J.card : ℝ)) (x : ZMod N → Fin r → ℤ)
    (hx : ∀ h ∈ J, ∀ i, |x h i| ≤ (R i : ℤ))
    (hrep : ∀ h ∈ J, h = h₀ + η (x h)) (a : ℝ) (b : Fin r → ℝ) :
    ∃ K ⊆ J, K.Nonempty ∧ Real.exp (-((p + 4) ^ 7)) * N ≤ (K.card : ℝ) ∧
      ∃ (t c : Fin r → ℝ) (a' : ℝ) (b' : Fin r → ℝ),
        (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
        (∀ i, |c i| ≤ properCyclicCoordinateBound r (Real.exp (-p)) + 1 / 16) ∧
        ∀ h ∈ K, (∀ i, |affineCyclicTorusLocalLift t c h₀ h i| ≤ 1 / 16) ∧
          a + ∑ i, (x h i : ℝ) * b i =
            a' + ∑ i, affineCyclicTorusLocalLift t c h₀ h i * b' i := by
  obtain ⟨basis, _, t, ht, hperiod, K, hKJ, hK, hcard, c, hc, hdata⟩ :=
    exists_localized_cyclic_torus_chart η R hinj h₀ J hJ (Real.exp (-p))
      (Real.exp_pos _) hdense x hx hrep 8 (by norm_num)
  let B := basis.ofZLatticeBasis ℝ (cyclicIntegerKernel η)
  let a' := affineBasisConstant B (fun _ : Unit => a) (fun i _ => b i) c ()
  let b' (i : Fin r) := affineBasisCoefficient B (fun j (_ : Unit) => b j) i ()
  refine ⟨K, hKJ, hK, local_cyclic_torus_density hp hr J K hdense hcard,
    t, c, a', b', ht, hperiod, ?_, ?_⟩
  · simpa only [Nat.cast_ofNat, div_div, show (2 : ℝ) * 8 = 16 by norm_num] using hc
  · intro h hh
    obtain ⟨_, hsmall, hcoord⟩ := hdata h hh
    refine ⟨by norm_num at hsmall ⊢; exact hsmall, ?_⟩
    change a + ∑ i, integerVectorRealMap (x h) i * b i = _
    rw [hcoord]
    exact affine_basis_change B (fun _ : Unit => a) (fun i _ => b i) c
      (affineCyclicTorusLocalLift t c h₀ h) ()

theorem exists_quadratic_local_frequency :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ (r : ℕ) (t c b : Fin r → ℝ) (a : ℝ) (h₀ : ZMod N),
          (r : ℝ) ≤ (p + C) ^ C ∧
          (∀ i, t i ∈ Set.Ico (0 : ℝ) 1) ∧
          (∀ i, ∃ k : ℤ, (N : ℝ) * t i = (k : ℝ)) ∧
          (∀ i, |c i| ≤ Real.exp ((p + C) ^ C)) ∧
          ∀ h ∈ H, (∀ i, |affineCyclicTorusLocalLift t c h₀ h i| ≤ 1 / 16) ∧
            Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (CircleFourier.character
                  (((n.val : ℝ) * (a + ∑ i, affineCyclicTorusLocalLift t c h₀ h i * b i) : ℝ) :
                    CircleFourier.Circle))‖ := by
  obtain ⟨A, _, hfrequencies⟩ := exists_quadratic_affine_frequency_coordinates_budget
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + 4) ^ 7 + (P + 4) ^ 5 + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  classical
  obtain ⟨J, hJ, hdense, r, R, η, ξ, h₀, ξ₀, hrank, hproper, hselected⟩ :=
    hfrequencies hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : q + (q + 4) ^ 7 + (q + 4) ^ 5 + 2 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by
    have h₇ : 0 ≤ (q + 4) ^ 7 := by positivity
    have h₅ : 0 ≤ (q + 4) ^ 5 := by positivity
    linarith
  have hchartC : (q + 4) ^ 7 ≤ (p + C) ^ C := by
    have h₅ : 0 ≤ (q + 4) ^ 5 := by positivity
    linarith
  have hcenterC : (q + 4) ^ 5 + 2 ≤ (p + C) ^ C := by
    have h₇ : 0 ≤ (q + 4) ^ 7 := by positivity
    linarith
  choose x hx hrep hlarge using fun h : {h // h ∈ J} => hselected h.val h.property
  let x' (h : ZMod N) : Fin r → ℤ := if hh : h ∈ J then x ⟨h, hh⟩ else 0
  have hx' (h : ZMod N) (hh : h ∈ J) : ∀ i, |x' h i| ≤ (R i : ℤ) := by
    simpa only [x', dite_eq_left hh] using hx ⟨h, hh⟩
  have hrep' (h : ZMod N) (hh : h ∈ J) : h = h₀ + η (x' h) := by
    simpa only [x', dite_eq_left hh] using hrep ⟨h, hh⟩
  have hlarge' (h : ZMod N) (hh : h ∈ J) : Real.exp (-q) ≤
      ‖finiteFourierCoeff (multiplicativeDerivative f h) (AddChar.zmodAddEquiv (ξ₀ + ξ (x' h)))‖ := by
    simpa only [x', dite_eq_left hh] using hlarge ⟨h, hh⟩
  have hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (R i : ℤ)} := by
    simpa only [Set.InjOn, Finset.mem_coe, mem_centeredIntegerBox, Set.mem_ofPred_eq] using hproper
  obtain ⟨a, b, hphase⟩ := exists_affine_cyclic_character_phase ξ ξ₀
  obtain ⟨K, hKJ, hK, hKsize, t, c, a', b', ht, hperiod, hc, hlocal⟩ :=
    exists_local_affine_scalar_chart hq hrank η R hinj h₀ J hJ hdense x' hx' hrep' a b
  refine ⟨K, hK, ?_, r, t, c, b', a', h₀, hrank.trans hqC, ht, hperiod, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hchartC))
      (Nat.cast_nonneg _)).trans hKsize
  · intro i
    have hcoord := properCyclicCoordinateBound_le_exp hq hrank
    have hE : 1 ≤ Real.exp ((q + 4) ^ 5) := Real.one_le_exp (by positivity)
    calc
      |c i| ≤ properCyclicCoordinateBound r (Real.exp (-q)) + 1 / 16 := hc i
      _ ≤ 2 * Real.exp ((q + 4) ^ 5) := by linarith
      _ ≤ Real.exp 2 * Real.exp ((q + 4) ^ 5) := by
        gcongr
        linarith [Real.add_one_le_exp (2 : ℝ)]
      _ = Real.exp ((q + 4) ^ 5 + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hcenterC
  · intro h hh
    obtain ⟨hsmall, heq⟩ := hlocal h hh
    refine ⟨hsmall, ?_⟩
    have heval (n : ZMod N) : CircleFourier.character
        (((n.val : ℝ) * (a' + ∑ i, affineCyclicTorusLocalLift t c h₀ h i * b' i) : ℝ) :
          CircleFourier.Circle) = AddChar.zmodAddEquiv (ξ₀ + ξ (x' h)) n := by
      rw [← heq]
      exact hphase (x' h) n
    simp only [heval]
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hlarge' h (hKJ hh))

end Erdos3

end

end OAI
