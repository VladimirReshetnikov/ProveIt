import OAI.Combinatorics.Progressions.Estimates.LocalWeightedSifting
import OAI.Combinatorics.Progressions.Fourier.BohrTorusApproximation
import OAI.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing

namespace OAI

section

open Finset
open scoped BigOperators

namespace Erdos3

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def massCoeff (w : G → ℝ) (ψ : AddChar G ℂ) : ℂ :=
  ∑ x : G, (w x : ℂ) * ψ x

theorem massCoeff_realUniformMass (A : Finset G) (ψ : AddChar G ℂ) :
    massCoeff (realUniformMass A) ψ =
      ((A.card : ℝ)⁻¹ : ℂ) * Chang.spectrumSum A ψ := by
  calc
    massCoeff (realUniformMass A) ψ =
        ∑ x ∈ A, ((A.card : ℝ)⁻¹ : ℂ) * ψ x := by
      rw [massCoeff, ← Finset.sum_subset (s₁ := A) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [realUniformMass, hx]
      · simp
      · intro x hxU hxA
        simp [realUniformMass, hxA]
    _ = ((A.card : ℝ)⁻¹ : ℂ) * Chang.spectrumSum A ψ := by
      rw [Chang.spectrumSum, Finset.mul_sum]

theorem norm_massCoeff_realUniformMass_lt_half_of_not_mem_largeSpectrum
    (A : Finset G) (hA : A.Nonempty) (ψ : AddChar G ℂ)
    (hψ : ψ ∉ Chang.largeSpectrum A (1 / 2)) :
    ‖massCoeff (realUniformMass A) ψ‖ < 1 / 2 := by
  have hcard : (0 : ℝ) < A.card := by
    exact_mod_cast hA.card_pos
  have hspectrum :
      ‖Chang.spectrumSum A ψ‖ < (1 / 2 : ℝ) * A.card := by
    apply lt_of_not_ge
    intro h
    exact hψ (Chang.mem_largeSpectrum.mpr h)
  calc
    ‖massCoeff (realUniformMass A) ψ‖ =
        (A.card : ℝ)⁻¹ * ‖Chang.spectrumSum A ψ‖ := by
      rw [massCoeff_realUniformMass, norm_mul]
      simp [norm_inv]
    _ < (A.card : ℝ)⁻¹ *
        ((1 / 2 : ℝ) * A.card) :=
      mul_lt_mul_of_pos_left hspectrum (inv_pos.mpr hcard)
    _ = 1 / 2 := by field_simp

omit [DecidableEq G] in

theorem massCoeff_massConvolution (f g : G → ℝ) (ψ : AddChar G ℂ) :
    massCoeff (massConvolution f g) ψ = massCoeff f ψ * massCoeff g ψ := by
  unfold massCoeff massConvolution
  push_cast
  calc
    ∑ x : G, (∑ y : G, (f y : ℂ) * (g (x - y) : ℂ)) * ψ x =
        ∑ x : G, ∑ y : G, (f y : ℂ) * (g (x - y) : ℂ) * ψ x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_mul]
    _ = ∑ y : G, ∑ x : G, (f y : ℂ) * (g (x - y) : ℂ) * ψ x :=
      Finset.sum_comm
    _ =
        ∑ y : G, ((f y : ℂ) * ψ y) *
          ∑ z : G, (g z : ℂ) * ψ z := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight y) _ _ fun z ↦ ?_
      have hψ : ψ z = ψ y * ψ (z - y) := by
        calc
          ψ z = ψ (y + (z - y)) := congrArg ψ (by simp)
          _ = ψ y * ψ (z - y) := AddChar.map_add_eq_mul ψ y (z - y)
      simp only [Equiv.subRight_apply]
      rw [hψ]
      ring
    _ = (∑ y : G, (f y : ℂ) * ψ y) *
        ∑ z : G, (g z : ℂ) * ψ z := by
      simpa using
        (Finset.sum_mul (univ : Finset G) (fun y ↦ (f y : ℂ) * ψ y)
          (∑ z : G, (g z : ℂ) * ψ z)).symm

theorem massCoeff_convolutionPower (f : G → ℝ) (ψ : AddChar G ℂ) :
    ∀ n, massCoeff (convolutionPower f n) ψ = massCoeff f ψ ^ n := by
  intro n
  induction n with
  | zero =>
      unfold massCoeff
      rw [Fintype.sum_eq_single 0]
      · simp [realUniformMass]
      · intro y hy
        simp [realUniformMass, hy]
  | succ n ihn =>
      rw [convolutionPower_succ, massCoeff_massConvolution, ihn, pow_succ]

omit [DecidableEq G] in

theorem norm_massCoeff_le_sum {w : G → ℝ} (hw : ∀ x, 0 ≤ w x)
    (ψ : AddChar G ℂ) :
    ‖massCoeff w ψ‖ ≤ ∑ x : G, w x := by
  unfold massCoeff
  calc
    ‖∑ x : G, (w x : ℂ) * ψ x‖ ≤
        ∑ x : G, ‖(w x : ℂ) * ψ x‖ := norm_sum_le _ _
    _ = ∑ x : G, w x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [hw x]

end

end Erdos3

end

section

open Finset
open scoped BigOperators NNReal

namespace Erdos3

noncomputable section

variable {N : ℕ} [NeZero N]

theorem convolutionPower_realUniformMass_support
    (B : CyclicBohr.Set N) (σ : ℝ≥0) :
    ∀ n x, convolutionPower (realUniformMass (B.ndilate σ).carrier) n x ≠ 0 →
      x ∈ (B.ndilate ((n : ℝ≥0) * σ)).carrier := by
  intro n
  induction n with
  | zero =>
      intro x hx
      have hx0 : x = 0 := by
        simpa using
          (realUniformMass_ne_zero_iff (singleton_nonempty 0) x).mp hx
      subst x
      simpa only [Nat.cast_zero, zero_mul, CyclicBohr.Set.mem_iff,
        CyclicBohr.Set.mem_carrier] using (B.ndilate 0).zero_mem
  | succ n ihn =>
      intro x hx
      rw [convolutionPower_succ, massConvolution] at hx
      obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      have hypow : convolutionPower (realUniformMass (B.ndilate σ).carrier) n y ≠ 0 :=
        (mul_ne_zero_iff.mp hy).1
      have hysmall : realUniformMass (B.ndilate σ).carrier (x - y) ≠ 0 :=
        (mul_ne_zero_iff.mp hy).2
      have hyB := ihn y hypow
      have hxyB : x - y ∈ (B.ndilate σ).carrier :=
        (realUniformMass_ne_zero_iff
          (B.ndilate σ).carrier_nonempty (x - y)).mp hysmall
      have hadd := CyclicBohr.Set.add_mem_ndilate hyB hxyB
      have hxsum : y + (x - y) = x := by simp
      rw [hxsum] at hadd
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        CyclicBohr.Set.mem_iff, CyclicBohr.Set.mem_carrier] using hadd

def bohrSmoothingMeasure (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) : (ZMod N) → ℝ :=
  massConvolution
    (realUniformMass (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier)
    (convolutionPower (realUniformMass (B.ndilate σ).carrier) n)

theorem bohrSmoothingMeasure_nonneg (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) (x : (ZMod N)) :
    0 ≤ bohrSmoothingMeasure B σ n x := by
  exact massConvolution_nonneg
    (realUniformMass_nonneg _)
    (convolutionPower_nonneg (realUniformMass_nonneg _) n) x

theorem sum_bohrSmoothingMeasure (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) :
    ∑ x : (ZMod N), bohrSmoothingMeasure B σ n x = 1 := by
  rw [bohrSmoothingMeasure, sum_massConvolution,
    sum_realUniformMass (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier_nonempty,
    sum_convolutionPower
      (sum_realUniformMass (B.ndilate σ).carrier_nonempty), one_mul]

theorem bohrSmoothingMeasure_apply_of_mem
    (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) {x : (ZMod N)} (hx : x ∈ B.carrier) :
    bohrSmoothingMeasure B σ n x =
      (((B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
  rw [bohrSmoothingMeasure, massConvolution_comm]
  simp only [massConvolution]
  calc
    ∑ t : (ZMod N), convolutionPower (realUniformMass (B.ndilate σ).carrier) n t *
          realUniformMass (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier (x - t) =
        ∑ t : (ZMod N), convolutionPower (realUniformMass (B.ndilate σ).carrier) n t *
          (((B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hνt :
          convolutionPower (realUniformMass (B.ndilate σ).carrier) n t = 0
      · simp [hνt]
      · have htB : t ∈ (B.ndilate ((n : ℝ≥0) * σ)).carrier :=
          convolutionPower_realUniformMass_support B σ n t hνt
        have hxt : x - t ∈
            (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier := by
          exact CyclicBohr.Set.sub_mem_ndilate
            (B := B) (r := 1) (s := (n : ℝ≥0) * σ)
            (by simpa only [CyclicBohr.Set.ndilate_one, CyclicBohr.Set.mem_iff,
              CyclicBohr.Set.mem_carrier] using hx) htB
        rw [realUniformMass_apply_mem hxt]
    _ = (∑ t : (ZMod N),
          convolutionPower (realUniformMass (B.ndilate σ).carrier) n t) *
        (((B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
      rw [Finset.sum_mul]
    _ = (((B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
      rw [sum_convolutionPower
        (sum_realUniformMass (B.ndilate σ).carrier_nonempty)]
      simp

theorem card_dilate_one_add_le_two_mul
    {B : CyclicBohr.Set N} (hreg : B.IsRankRegular) {σ : ℝ≥0} (n : ℕ)
    (hsmall : (n : ℝ≥0) * σ ≤
      1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)) :
    (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card ≤
      2 * B.carrier.card := by
  let κ : ℝ≥0 := (n : ℝ≥0) * σ
  let d : ℕ := 2 * max B.rank 1
  have hcards := hreg κ (by simpa [κ, d] using hsmall)
  have hfactor : (1 + 100 * (d : ℝ) * (κ : ℝ)) ≤ 2 := by
    have hsmallR : (κ : ℝ) ≤ 1 / (100 * (d : ℝ)) := by
      exact_mod_cast (show κ ≤ 1 / (100 * (d : ℝ≥0)) by
        simpa [κ, d] using hsmall)
    have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by simp [d])
    calc
      1 + 100 * (d : ℝ) * (κ : ℝ) ≤
          1 + 100 * (d : ℝ) * (1 / (100 * (d : ℝ))) := by gcongr
      _ = 2 := by field_simp; ring
  have hcardR :
      ((B.ndilate (1 + κ)).carrier.card : ℝ) ≤
        2 * (B.carrier.card : ℝ) := by
    calc
      ((B.ndilate (1 + κ)).carrier.card : ℝ) ≤
          (1 + 100 * (d : ℝ) * (κ : ℝ)) * (B.carrier.card : ℝ) := by
        simpa [κ, d] using hcards.2
      _ ≤ 2 * (B.carrier.card : ℝ) := by gcongr
  exact_mod_cast hcardR

theorem realUniformMass_le_two_mul_bohrSmoothingMeasure
    {B : CyclicBohr.Set N} (hreg : B.IsRankRegular) {σ : ℝ≥0} (n : ℕ)
    (hsmall : (n : ℝ≥0) * σ ≤
      1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)) (x : (ZMod N)) :
    realUniformMass B.carrier x ≤ 2 * bohrSmoothingMeasure B σ n x := by
  let κ : ℝ≥0 := (n : ℝ≥0) * σ
  by_cases hx : x ∈ B.carrier
  · rw [realUniformMass_apply_mem hx,
      bohrSmoothingMeasure_apply_of_mem B σ n hx]
    have hcard := card_dilate_one_add_le_two_mul hreg n hsmall
    have hcardR :
        (((B.ndilate (1 + κ)).carrier.card : ℕ) : ℝ) ≤
          2 * (B.carrier.card : ℝ) := by
      exact_mod_cast (show (B.ndilate (1 + κ)).carrier.card ≤
        2 * B.carrier.card by simpa [κ] using hcard)
    have hBpos : (0 : ℝ) < B.carrier.card := by
      exact_mod_cast B.carrier_nonempty.card_pos
    have hOuterPos : (0 : ℝ) < (B.ndilate (1 + κ)).carrier.card := by
      exact_mod_cast (B.ndilate (1 + κ)).carrier_nonempty.card_pos
    rw [show (1 + (n : ℝ≥0) * σ) = 1 + κ by rfl]
    have hdiv : 1 / (B.carrier.card : ℝ) ≤
        2 / ((B.ndilate (1 + κ)).carrier.card : ℝ) := by
      rw [div_le_div_iff₀ hBpos hOuterPos]
      simpa [mul_comm] using hcardR
    simpa only [one_div, div_eq_mul_inv, one_mul] using hdiv
  · rw [realUniformMass_apply_not_mem hx]
    exact mul_nonneg (by norm_num) (bohrSmoothingMeasure_nonneg B σ n x)

theorem norm_massCoeff_bohrSmoothingMeasure_le
    (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) (ψ : AddChar (ZMod N) ℂ) :
    ‖massCoeff (bohrSmoothingMeasure B σ n) ψ‖ ≤
      ‖massCoeff (realUniformMass (B.ndilate σ).carrier) ψ‖ ^ n := by
  rw [bohrSmoothingMeasure, massCoeff_massConvolution,
    massCoeff_convolutionPower, norm_mul, norm_pow]
  have houter :
      ‖massCoeff (realUniformMass
        (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier) ψ‖ ≤ 1 := by
    simpa [sum_realUniformMass
      (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier_nonempty] using
      norm_massCoeff_le_sum
        (w := realUniformMass
          (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier)
        (realUniformMass_nonneg _) ψ
  exact mul_le_of_le_one_left (by positivity) houter

end

end Erdos3

end

section

open AddChar Finset
open scoped BigOperators NNReal

namespace Erdos3

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

private lemma normalizedSpectrum_eq (A : Finset G) (psi : AddChar G ℂ) :
    (∑ x : G, (realUniformMass A x : ℂ) * psi x) =
      ((A.card : ℂ)⁻¹) * Chang.spectrumSum A psi := by
  classical
  rw [Chang.spectrumSum, Finset.mul_sum]
  calc
    (∑ x : G, (realUniformMass A x : ℂ) * psi x) =
        ∑ x : G, if x ∈ A then ((A.card : ℂ)⁻¹) * psi x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [realUniformMass, hx]
    _ = ∑ x ∈ A, ((A.card : ℂ)⁻¹) * psi x := by
      rw [← Finset.sum_filter]
      have hfilter :
          (Finset.univ.filter fun x : G ↦ x ∈ A) = A := by
        ext x
        simp
      rw [hfilter]

private lemma normalizedSpectrum_translate (A : Finset G)
    (psi : AddChar G ℂ) (t : G) :
    (1 - psi t) * (∑ x : G, (realUniformMass A x : ℂ) * psi x) =
      ∑ x : G,
        ((realUniformMass A x - realUniformMass A (x - t) : ℝ) : ℂ) *
          psi x := by
  classical
  have htranslate :
      (∑ x : G, (realUniformMass A (x - t) : ℂ) * psi x) =
        psi t * ∑ x : G, (realUniformMass A x : ℂ) * psi x := by
    rw [← (Equiv.addRight t).sum_comp]
    · change
        (∑ x : G, (realUniformMass A ((x + t) - t) : ℂ) * psi (x + t)) =
          psi t * ∑ x : G, (realUniformMass A x : ℂ) * psi x
      simp_rw [add_sub_cancel_right, map_add_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    · simp
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, htranslate]
  ring

variable {N : ℕ} [NeZero N]

theorem norm_one_sub_le_of_mem_largeSpectrum
    {C : CyclicBohr.Set N} (hreg : C.IsRankRegular) {eta : ℝ} (heta : 0 < eta)
    {sigma : ℝ≥0}
    (hsigma : sigma ≤ 1 / (100 * (2 * max C.rank 1 : ℕ) : ℝ≥0))
    {psi : AddChar (ZMod N) ℂ} (hpsi : psi ∈ Chang.largeSpectrum C.carrier eta)
    {t : (ZMod N)} (ht : t ∈ (C.ndilate sigma).carrier) :
    ‖1 - psi t‖ ≤
      400 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) / eta := by
  classical
  let F : ℂ := ∑ x : (ZMod N), (realUniformMass C.carrier x : ℂ) * psi x
  have hcard : (0 : ℝ) < C.carrier.card := by
    exact_mod_cast C.carrier_nonempty.card_pos
  have hFnorm : ‖F‖ = ‖Chang.spectrumSum C.carrier psi‖ / C.carrier.card := by
    dsimp [F]
    rw [normalizedSpectrum_eq, norm_mul]
    simp [div_eq_inv_mul]
  have hlarge : eta ≤ ‖F‖ := by
    rw [hFnorm, le_div_iff₀ hcard]
    exact Chang.mem_largeSpectrum.mp hpsi
  have hphase :
      ‖1 - psi t‖ * ‖F‖ ≤
        ∑ x : (ZMod N),
          |realUniformMass C.carrier (x - t) -
            realUniformMass C.carrier x| := by
    rw [← norm_mul, normalizedSpectrum_translate C.carrier psi t]
    calc
      ‖∑ x : (ZMod N),
          ((realUniformMass C.carrier x -
              realUniformMass C.carrier (x - t) : ℝ) : ℂ) * psi x‖ ≤
          ∑ x : (ZMod N),
            ‖((realUniformMass C.carrier x -
                realUniformMass C.carrier (x - t) : ℝ) : ℂ) * psi x‖ :=
        norm_sum_le _ _
      _ = ∑ x : (ZMod N),
          |realUniformMass C.carrier (x - t) -
            realUniformMass C.carrier x| := by
        apply Finset.sum_congr rfl
        intro x _
        rw [norm_mul]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
        simp
  have htranslation :=
    CyclicBohr.Set.uniformMass_translation_le_of_rankRegular
      hreg hsigma ht
  have hmul :
      ‖1 - psi t‖ * eta ≤
        400 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := by
    calc
      ‖1 - psi t‖ * eta ≤ ‖1 - psi t‖ * ‖F‖ :=
        mul_le_mul_of_nonneg_left hlarge (norm_nonneg _)
      _ ≤ ∑ x : (ZMod N),
          |realUniformMass C.carrier (x - t) -
            realUniformMass C.carrier x| := hphase
      _ ≤ 400 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := htranslation
  exact (le_div_iff₀ heta).2 hmul

theorem norm_one_sub_le_of_mem_largeSpectrum_half
    {C : CyclicBohr.Set N} (hreg : C.IsRankRegular) {sigma : ℝ≥0}
    (hsigma : sigma ≤ 1 / (100 * (2 * max C.rank 1 : ℕ) : ℝ≥0))
    {psi : AddChar (ZMod N) ℂ} (hpsi : psi ∈ Chang.largeSpectrum C.carrier (1 / 2))
    {t : (ZMod N)} (ht : t ∈ (C.ndilate sigma).carrier) :
    ‖1 - psi t‖ ≤ 800 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := by
  classical
  have h := norm_one_sub_le_of_mem_largeSpectrum hreg (eta := (1 / 2 : ℝ))
    (by norm_num) hsigma hpsi ht
  convert h using 1
  ring

end

end Erdos3

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_dense_sets_of_bohr_correlation_moment
    (L : CyclicBohr.Set N) (hL : L.IsRankRegular) (S T K : Finset (ZMod N))
    (hS : S.Nonempty) (hT : T.Nonempty) {kappa : ℝ≥0}
    (hSL : S ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f : ZMod N → ℝ) (hfsupport : ∀ x, x ∉ L.carrier → f x = 0)
    {M alpha threshold epsilon : ℝ} (hM : 0 < M) (halpha : 0 < alpha)
    (hthreshold : 0 ≤ threshold) (hepsilon : 0 < epsilon)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (q : ℕ)
    (hmoment : alpha ^ q ≤ 𝔼 a ∈ S, 𝔼 b ∈ T, correlation L.carrier f f (a - b) ^ q)
    (hbad : ∀ a ∈ S, ∀ b ∈ T, a - b ∉ K → correlation L.carrier f f (a - b) ≤ threshold)
    (hseparation : threshold ^ q ≤ epsilon / 2 * alpha ^ q) :
    ∃ A ⊆ S, ∃ B ⊆ T, A.Nonempty ∧ B.Nonempty ∧
      ((alpha / (2 * M ^ 2)) ^ q / 2) * S.card ≤ A.card ∧
      ((alpha / (2 * M ^ 2)) ^ q / 2) * T.card ≤ B.card ∧
      1 - epsilon ≤ 𝔼 a ∈ A, 𝔼 b ∈ B, if a - b ∈ K then (1 : ℝ) else 0 := by
  let U := (L.ndilate (1 + kappa)).carrier
  have hU : U.Nonempty := (L.ndilate (1 + kappa)).carrier_nonempty
  have hUcard : U.card ≤ 2 * L.carrier.card := by
    simpa only [Nat.cast_one, one_mul] using
      Erdos3.card_dilate_one_add_le_two_mul hL 1 (by simpa only [Nat.cast_one, one_mul] using hkappa)
  have hsupport : ∀ a ∈ S, ∀ b ∈ T, ∀ x, x ∉ U → f (x + a) * f (x + b) = 0 := by
    intro a ha b _ x hx
    have hxa : x + a ∉ L.carrier := by
      intro h
      have h₁ : x + a ∈ L.ndilate (1 : ℝ≥0) := by
        simpa only [CyclicBohr.Set.ndilate_one, CyclicBohr.Set.mem_iff,
          CyclicBohr.Set.mem_carrier] using h
      have h₂ := CyclicBohr.Set.sub_mem_ndilate h₁ (hSL ha)
      exact hx (by simpa only [U, add_sub_cancel_right, CyclicBohr.Set.mem_iff,
        CyclicBohr.Set.mem_carrier] using h₂)
    rw [hfsupport _ hxa, zero_mul]
  obtain ⟨A, hAS, B, hBT, hA, hB, hAdensity, hBdensity, hprob⟩ :=
    exists_dense_sets_of_correlation_moment L.carrier U S T K L.carrier_nonempty hU hS hT
      f hM halpha hthreshold hepsilon hf hsupport q hmoment hbad hseparation
  have hLc : (0 : ℝ) < L.carrier.card := by exact_mod_cast L.card_pos
  have hUc : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have hUcardR : (U.card : ℝ) ≤ 2 * L.carrier.card := by exact_mod_cast hUcard
  have hratio : 1 / (2 * M ^ 2) ≤ (L.carrier.card : ℝ) / ((U.card : ℝ) * M ^ 2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hUcardR (sq_nonneg M)]
  have hbase : alpha / (2 * M ^ 2) ≤
      (L.carrier.card : ℝ) / ((U.card : ℝ) * M ^ 2) * alpha := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
      mul_le_mul_of_nonneg_right hratio halpha.le
  have hdensity := div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : 0 ≤ alpha / (2 * M ^ 2)) hbase q)
    (by norm_num : (0 : ℝ) ≤ 2)
  exact ⟨A, hAS, B, hBT, hA, hB,
    (mul_le_mul_of_nonneg_right hdensity (Nat.cast_nonneg S.card)).trans hAdensity,
    (mul_le_mul_of_nonneg_right hdensity (Nat.cast_nonneg T.card)).trans hBdensity, hprob⟩

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal Pointwise

variable {N : ℕ} [NeZero N]

theorem card_add_le_two_mul_of_small_bohr
    (B : Set N) (hBreg : B.IsRankRegular) {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    {A S : Finset (ZMod N)} (z : ZMod N)
    (hA : ∀ a ∈ A, a - z ∈ B.carrier) (hS : S ⊆ (B.ndilate kappa).carrier) :
    (A + S).card ≤ 2 * B.carrier.card := by
  have hsub : A + S ⊆ (B.ndilate (1 + kappa)).carrier.image (fun x => z + x) := by
    intro x hx
    obtain ⟨a, ha, s, hs, rfl⟩ := Finset.mem_add.mp hx
    have haB : a - z ∈ B.ndilate (1 : ℝ≥0) := by
      simpa only [ndilate_one, mem_iff, mem_carrier] using hA a ha
    have hadd := add_mem_ndilate haB (hS hs)
    refine Finset.mem_image.mpr ⟨(a - z) + s, hadd, ?_⟩
    abel
  have houter : (B.ndilate (1 + kappa)).carrier.card ≤ 2 * B.carrier.card := by
    simpa only [Nat.cast_one, one_mul] using
      Erdos3.card_dilate_one_add_le_two_mul hBreg 1 (by simpa only [Nat.cast_one, one_mul] using hkappa)
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans houter)

noncomputable def initialSamplingScale (B : Set N) : ℝ≥0 :=
  1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)

theorem initialSamplingScale_pos (B : Set N) : 0 < B.initialSamplingScale := by
  unfold initialSamplingScale
  positivity

theorem initialSamplingScale_le_one (B : Set N) : B.initialSamplingScale ≤ 1 := by
  unfold initialSamplingScale
  rw [div_le_one (by positivity)]
  exact_mod_cast (show 1 ≤ 100 * (2 * max B.rank 1) by omega)

theorem exists_initial_regular_sampling_bohr
    (B : Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular) :
    ∃ C : Set N, C.frequencies = B.frequencies ∧ C.IsRankRegular ∧
      (B.initialSamplingScale : ℝ) * B.radius / 2 ≤ C.radius ∧
      C.radius ≤ B.initialSamplingScale * B.radius ∧ C.carrier ⊆ B.carrier ∧
      ∀ (A : Finset (ZMod N)) (z : ZMod N),
        (∀ a ∈ A, a - z ∈ B.carrier) → (A + C.carrier).card ≤ 2 * B.carrier.card := by
  obtain ⟨C, hfreq, hreg, hlo, hhi, hsub, _⟩ :=
    exists_controlled_regular_subdilate B hBpos B.initialSamplingScale
      B.initialSamplingScale_pos B.initialSamplingScale_le_one
  have hCB : C.carrier ⊆ B.carrier := by
    apply hsub.trans
    simpa only [ndilate_one] using
      carrier_ndilate_mono (B := B) B.initialSamplingScale_le_one
  refine ⟨C, hfreq, hreg, hlo, hhi, hCB, ?_⟩
  intro A z hA
  exact card_add_le_two_mul_of_small_bohr B hBreg le_rfl z hA hsub

theorem sumset_le_exp_of_relative_density
    (B : Set N) {A S : Finset (ZMod N)} {p : ℝ}
    (hsum : (A + S).card ≤ 2 * B.carrier.card)
    (hdensity : Real.exp (-p) * B.carrier.card ≤ A.card) :
    ((A + S).card : ℝ) ≤ (2 * Real.exp p) * A.card := by
  have hsize : (B.carrier.card : ℝ) ≤ Real.exp p * A.card := by
    calc
      (B.carrier.card : ℝ) = Real.exp p * (Real.exp (-p) * B.carrier.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      _ ≤ Real.exp p * A.card :=
        mul_le_mul_of_nonneg_left hdensity (Real.exp_pos p).le
  have hsumR : ((A + S).card : ℝ) ≤ 2 * B.carrier.card := by exact_mod_cast hsum
  nlinarith

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped Pointwise NNReal

variable {N : ℕ} [NeZero N]

theorem card_sub_translated_small_le_two_mul
    (S : Set N) (hS : S.IsRankRegular) {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1 / (100 * (2 * max S.rank 1 : ℕ) : ℝ≥0))
    (C : Finset (ZMod N)) (hC : C ⊆ (S.ndilate kappa).carrier) (z : ZMod N) :
    (S.carrier - C.image (fun t => z + t)).card ≤ 2 * S.carrier.card := by
  have hsub : S.carrier - C.image (fun t => z + t) ⊆
      (S.ndilate (1 + kappa)).carrier.image (fun x => x - z) := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hb
    have haS : a ∈ S.ndilate (1 : ℝ≥0) := by
      simpa only [ndilate_one, mem_iff, mem_carrier] using ha
    have hdiff := sub_mem_ndilate haS (hC ht)
    refine Finset.mem_image.mpr ⟨a - t, hdiff, ?_⟩
    abel
  have houter : (S.ndilate (1 + kappa)).carrier.card ≤ 2 * S.carrier.card := by
    simpa only [Nat.cast_one, one_mul] using
      Erdos3.card_dilate_one_add_le_two_mul hS 1 (by simpa only [Nat.cast_one, one_mul] using hkappa)
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans houter)

end Erdos3.CyclicBohr.Set

end

end OAI
