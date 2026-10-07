/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.NormalizedTwistNativeApproximationBudget

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {Ω : Type*} [Fintype Ω]

theorem forecastAugmented_envelope_tail_le
    (p q : FiniteProbabilityWeights Ω) (hp : ∀ x, 0 < p.weight x)
    {K F C ε : ℝ} (hK : 0 ≤ K) (hF : 0 ≤ F) (hC : 1 ≤ C)
    (hexcess : p.excessMass q C ≤ ε) :
    p.mean (fun x => if x ∈ Finset.univ.filter
      (fun y => p.relativeDensity q y ≤ 2 * C)
      then 0 else K * p.relativeDensity q x + F) ≤ 2 * (K + F) * ε := by
  let G := Finset.univ.filter (fun x => p.relativeDensity q x ≤ 2 * C)
  have htail : p.mean (fun x => if x ∈ G then 0 else p.relativeDensity q x) ≤ 2 * ε := by
    rw [p.relativeDensity_tail_mass q hp]
    exact mass_above_double_cap_le_of_excess p q hexcess
  have hpoint (x : Ω) :
      (if x ∈ G then 0 else K * p.relativeDensity q x + F) ≤
        (K + F) * (if x ∈ G then 0 else p.relativeDensity q x) := by
    by_cases hx : x ∈ G
    · simp only [hx, ↓reduceIte, mul_zero, le_refl]
    · have hbad : 2 * C < p.relativeDensity q x := by
        simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hx
      simp only [hx, ↓reduceIte]
      have hFscale := mul_le_mul_of_nonneg_left (show 1 ≤ p.relativeDensity q x by linarith) hF
      nlinarith
  calc
    _ ≤ p.mean (fun x => (K + F) * (if x ∈ G then 0 else p.relativeDensity q x)) :=
      p.mean_mono hpoint
    _ = (K + F) * p.mean (fun x => if x ∈ G then 0 else p.relativeDensity q x) := by
      unfold mean
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ (K + F) * (2 * ε) := mul_le_mul_of_nonneg_left htail (add_nonneg hK hF)
    _ = 2 * (K + F) * ε := by ring

theorem forecastAugmented_envelope_le_on_good
    (p q : FiniteProbabilityWeights Ω) {K F C : ℝ} (hK : 0 ≤ K)
    (x : Ω) (hx : x ∈ Finset.univ.filter (fun y => p.relativeDensity q y ≤ 2 * C)) :
    K * p.relativeDensity q x + F ≤ 2 * K * C + F := by
  have h := mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hx).2 hK
  nlinarith

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def forecastCorrelationLinearMap {X : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast : X → ℂ) : (X → ℂ) →ₗ[ℂ] ℂ where
  toFun g := r.correlation g forecast
  map_add' g h := by
    simp [FiniteProbabilityWeights.correlation, Pi.add_apply, add_mul, mul_add,
      Finset.sum_add_distrib]
  map_smul' a g := by
    simp only [FiniteProbabilityWeights.correlation, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring

noncomputable def forecastSingleSeminorm {X : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast : X → ℂ) : Seminorm ℂ (X → ℂ) :=
  (normSeminorm ℂ ℂ).comp (forecastCorrelationLinearMap r forecast)

theorem forecastSingleSeminorm_le {X : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast g : X → ℂ) {cap : ℝ}
    (hcap : ∀ x, ‖forecast x‖ ≤ cap) :
    forecastSingleSeminorm r forecast g ≤ cap * r.mean (fun x => ‖g x‖) := by
  change ‖r.correlation g forecast‖ ≤ _
  unfold FiniteProbabilityWeights.correlation FiniteProbabilityWeights.mean
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x _
  rw [norm_mul, norm_mul, norm_star, Complex.norm_real,
    Real.norm_of_nonneg (r.nonneg x)]
  calc
    r.weight x * (‖g x‖ * ‖forecast x‖) ≤ r.weight x * (‖g x‖ * cap) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hcap x) (norm_nonneg _))
        (r.nonneg x)
    _ = cap * (r.weight x * ‖g x‖) := by ring

noncomputable def forecastFamilySeminorm {X F : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast : F → X → ℂ) : Seminorm ℂ (X → ℂ) :=
  ⨆ f, forecastSingleSeminorm r (forecast f)

theorem forecastFamilySeminorm_bddAbove {X F : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast : F → X → ℂ) {cap : ℝ}
    (hcap : ∀ f x, ‖forecast f x‖ ≤ cap) :
    BddAbove (Set.range (fun f => forecastSingleSeminorm r (forecast f))) := by
  apply Seminorm.bddAbove_range_iff.mpr
  intro g
  refine ⟨cap * r.mean (fun x => ‖g x‖), ?_⟩
  rintro _ ⟨f, rfl⟩
  exact forecastSingleSeminorm_le r (forecast f) g (hcap f)

theorem forecastFamilySeminorm_apply {X F : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast : F → X → ℂ) {cap : ℝ}
    (hcap : ∀ f x, ‖forecast f x‖ ≤ cap) (g : X → ℂ) :
    forecastFamilySeminorm r forecast g = ⨆ f, ‖r.correlation g (forecast f)‖ := by
  rw [forecastFamilySeminorm, Seminorm.iSup_apply
    (forecastFamilySeminorm_bddAbove r forecast hcap)]
  rfl

theorem forecastFamilySeminorm_le {X F : Type*} [Fintype X] [Nonempty F]
    (r : FiniteProbabilityWeights X) (forecast : F → X → ℂ) {cap : ℝ}
    (hcap : ∀ f x, ‖forecast f x‖ ≤ cap) (g : X → ℂ) :
    forecastFamilySeminorm r forecast g ≤ cap * r.mean (fun x => ‖g x‖) := by
  rw [forecastFamilySeminorm_apply r forecast hcap]
  exact ciSup_le (fun f => forecastSingleSeminorm_le r (forecast f) g (hcap f))

theorem forecast_correlation_le_family {X F : Type*} [Fintype X]
    (r : FiniteProbabilityWeights X) (forecast : F → X → ℂ) {cap : ℝ}
    (hcap : ∀ f x, ‖forecast f x‖ ≤ cap) (g : X → ℂ) (f : F) :
    ‖r.correlation g (forecast f)‖ ≤ forecastFamilySeminorm r forecast g := by
  rw [forecastFamilySeminorm_apply r forecast hcap]
  have hb : BddAbove (Set.range (fun i => ‖r.correlation g (forecast i)‖)) := by
    refine ⟨cap * r.mean (fun x => ‖g x‖), ?_⟩
    rintro _ ⟨i, rfl⟩
    exact forecastSingleSeminorm_le r (forecast i) g (hcap i)
  exact le_ciSup hb f

theorem exists_forecast_augmented_model
    {Ω T X F : Type*} [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    [Nonempty F] {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (μ : FiniteProbabilityWeights Ω) (physical : Ω → T → X)
    (slices : ∀ z, J z → Finset T) (tests : ∀ z, J z → T → ℂ)
    (r : FiniteProbabilityWeights X) (hr : ∀ x, 0 < r.weight x)
    (forecast : F → X → ℂ) {atoms : Set (X → ℂ)}
    (hbal : Balanced ℂ atoms) (hatoms : atoms.Nonempty)
    (hatom : ∀ Q ∈ atoms, ∀ x, ‖Q x‖ ≤ 1)
    {K C forecastCap B beta tau ε : ℝ}
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hforecastCap : 0 ≤ forecastCap)
    (hB : 0 < B) (hbeta : 0 < beta) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hforecast : ∀ f x, ‖forecast f x‖ ≤ forecastCap)
    (hlocal : ∀ g : X → ℂ, (∀ x, ‖g x‖ ≤ 1) →
      (tau / B ^ 2) / max 1 ((2 * K * C + forecastCap) / tau) ≤
        sampledSliceSeminorm μ physical slices tests g →
      ∃ Q ∈ atoms, beta ≤ ‖r.correlation g Q‖)
    (hglobal : ∀ g : X → ℂ, (∀ x, ‖g x‖ ≤ 1) → ∀ f,
      ((tau / B ^ 2) / max 1 ((2 * K * C + forecastCap) / tau)) / 2 ≤
        ‖r.correlation g (forecast f)‖ →
      ∃ Q ∈ atoms, beta ≤ ‖r.correlation g Q‖)
    (hexcess : r.excessMass (μ.siteLaw physical) C ≤ ε)
    (input : X → ℂ) (hinput : ∀ x, ‖input x‖ ≤ B) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (X → ℂ)) (c : Fin n → ℝ) (err : X → ℂ),
      (∀ i, Q i ∈ atoms) ∧ input = (∑ i, c i • Q i) + err ∧
      (∑ i, |c i|) ≤ 2 / beta ∧
      sampledSliceSeminorm μ physical slices tests err ≤
        2 * tau + 2 * (B + 2 / beta) * (K + forecastCap) * ε ∧
      (∀ f, ‖r.correlation err (forecast f)‖ ≤
        2 * tau + 2 * (B + 2 / beta) * (K + forecastCap) * ε) ∧
      (n : ℝ) ≤ 1 + 4 * (2 * K * C + forecastCap) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  let q := μ.siteLaw physical
  let density := fun x => K * r.relativeDensity q x + forecastCap
  let good := Finset.univ.filter (fun x => r.relativeDensity q x ≤ 2 * C)
  let seminorm := sampledSliceSeminorm μ physical slices tests ⊔
    forecastFamilySeminorm r forecast
  let cap := max 1 ((2 * K * C + forecastCap) / tau)
  have hcap : 1 ≤ cap := le_max_left _ _
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have henvelope (g : X → ℂ) :
      seminorm g ≤ 1 * r.mean (fun x => density x * ‖g x‖) := by
    have hmean : r.mean (fun x => density x * ‖g x‖) =
        K * q.mean (fun x => ‖g x‖) + forecastCap * r.mean (fun x => ‖g x‖) := by
      simp only [density, add_mul, r.mean_add, mul_assoc, r.mean_const_mul,
        r.mean_relativeDensity q hr]
    rw [one_mul, hmean]
    apply max_le
    · exact (sampledSliceSeminorm_le_siteLaw μ physical slices tests hsize htests g).trans
        (le_add_of_nonneg_right (mul_nonneg hforecastCap (r.mean_nonneg (fun _ => norm_nonneg _))))
    · exact (forecastFamilySeminorm_le r forecast hforecast g).trans
        (le_add_of_nonneg_left (mul_nonneg hK (q.mean_nonneg (fun _ => norm_nonneg _))))
  have hunit (g : X → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1)
      (hlarge : (tau / B ^ 2) / cap ≤ seminorm g) :
      ∃ Q ∈ atoms, beta ≤ ‖r.correlation g Q‖ := by
    rcases le_max_iff.mp hlarge with hl | hf
    · exact hlocal g hg hl
    · have hpos : 0 < (tau / B ^ 2) / cap := by
        apply div_pos (div_pos htau (sq_pos_of_pos hB))
        exact lt_of_lt_of_le zero_lt_one hcap
      have hex : ∃ f, ((tau / B ^ 2) / cap) / 2 ≤ ‖r.correlation g (forecast f)‖ := by
        by_contra! hnot
        have hu := forecastFamilySeminorm_apply r forecast hforecast g
        have hle : forecastFamilySeminorm r forecast g ≤ ((tau / B ^ 2) / cap) / 2 := by
          rw [hu]
          exact ciSup_le (fun f => (hnot f).le)
        linarith only [hf, hle, hpos]
      obtain ⟨f, hf⟩ := hex
      exact hglobal g hg f hf
  have hdetector (g : X → ℂ)
      (hg : ∀ x, ‖g x‖ ≤ 1 * (2 * K * C + forecastCap) / tau)
      (hlarge : tau / B ^ 2 ≤ seminorm g) :
      ∃ Q ∈ atoms, beta ≤ ‖r.correlation g Q‖ := by
    have hbounded (x : X) : ‖g x‖ ≤ (2 * K * C + forecastCap) / tau := by
      simpa only [one_mul] using hg x
    obtain ⟨Q, hQ, hc⟩ := detector_of_unit_detector r seminorm atoms
      (lt_of_lt_of_le zero_lt_one hcap) hunit g
      (fun x => (hbounded x).trans (le_max_right _ _)) hlarge
    refine ⟨Q, hQ, le_trans ?_ hc⟩
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcap hbeta.le
  obtain ⟨n, hn, Q, c, err, hQ, heq, hc, he, hnterms⟩ :=
    exists_model_with_tail_error r good seminorm density hbal hatoms hatom
      zero_le_one (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) hC0) hforecastCap)
      hB hbeta htau
      (fun x => add_nonneg (mul_nonneg hK (r.relativeDensity_nonneg q x)) hforecastCap)
      (fun x hx => r.forecastAugmented_envelope_le_on_good q hK x hx)
      henvelope hdetector input hinput
  have htail := r.forecastAugmented_envelope_tail_le q hr hK hforecastCap hC hexcess
  have herr : seminorm err ≤ 2 * tau + 2 * (B + 2 / beta) * (K + forecastCap) * ε := by
    have hmul := mul_le_mul_of_nonneg_left htail
      (show 0 ≤ B + 2 / beta by positivity)
    dsimp only [density, good] at he
    simp only [one_mul] at he
    nlinarith only [he, hmul]
  refine ⟨n, hn, Q, c, err, hQ, heq, hc, ?_, ?_, ?_⟩
  · exact (le_max_left _ _).trans herr
  · intro f
    exact (forecast_correlation_le_family r forecast hforecast err f).trans
      ((le_max_right _ _).trans herr)
  · simpa only [one_mul] using hnterms

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem forecast_detector_of_atom_approximation
    {X Term : Type*} [Fintype X] [Fintype Term]
    (r : FiniteProbabilityWeights X) (forecast g : X → ℂ)
    (coefficient : Term → ℂ) (atom : Term → X → ℂ)
    {atoms : Set (X → ℂ)} {α M beta : ℝ}
    (hα : 0 < α) (hM : 0 ≤ M) (hg : ∀ x, ‖g x‖ ≤ 1)
    (hatom : ∀ i, atom i ∈ atoms)
    (happrox : ∀ x, ‖forecast x - ∑ i, coefficient i * atom i x‖ ≤ α / 8)
    (hmass : (∑ i, ‖coefficient i‖) ≤ M)
    (hbeta : beta ≤ α / (8 * (M + 1)))
    (hlarge : α / 2 ≤ ‖r.correlation g forecast‖) :
    ∃ Q ∈ atoms, beta ≤ ‖r.correlation g Q‖ := by
  have hconj (x : X) :
      ‖star (forecast x) - ∑ i, star (coefficient i) * star (atom i x)‖ ≤
        (α / 2) / (2 * ((1 : ℝ) + 1)) := by
    have h := happrox x
    rw [← norm_star] at h
    simpa only [star_sub, star_sum, star_mul, mul_comm (star (atom _ _)), div_div, mul_assoc,
      show (2 : ℝ) * (2 * (1 + 1)) = 8 by norm_num] using h
  have hmass' : (∑ i, ‖star (coefficient i)‖) ≤ M := by
    simpa only [norm_star] using hmass
  obtain ⟨i, hi⟩ := exists_forecast_detecting_atom r (fun x => star (forecast x)) g
    (fun i => star (coefficient i)) (fun i x => star (atom i x))
    (half_pos hα) zero_le_one hM hg hconj hmass' hlarge
  change (α / 2) / (4 * (M + 1)) ≤ ‖r.correlation g (atom i)‖ at hi
  refine ⟨atom i, hatom i, hbeta.trans ?_⟩
  simpa only [div_div, show (2 : ℝ) * (4 * (M + 1)) = 8 * (M + 1) by ring] using hi

theorem exists_forecast_augmented_model_of_expansions
    {Ω T X F : Type*} [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    [Nonempty F] {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (μ : FiniteProbabilityWeights Ω) (physical : Ω → T → X)
    (slices : ∀ z, J z → Finset T) (tests : ∀ z, J z → T → ℂ)
    (r : FiniteProbabilityWeights X) (hr : ∀ x, 0 < r.weight x)
    (forecast : F → X → ℂ) {atoms : Set (X → ℂ)}
    (hbal : Balanced ℂ atoms) (hatoms : atoms.Nonempty)
    (hatom : ∀ Q ∈ atoms, ∀ x, ‖Q x‖ ≤ 1)
    {K C forecastCap B beta tau ε M : ℝ}
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hforecastCap : 0 ≤ forecastCap)
    (hB : 0 < B) (hbeta : 0 < beta) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hforecast : ∀ f x, ‖forecast f x‖ ≤ forecastCap)
    (hlocal : ∀ g : X → ℂ, (∀ x, ‖g x‖ ≤ 1) →
      (tau / B ^ 2) / max 1 ((2 * K * C + forecastCap) / tau) ≤
        sampledSliceSeminorm μ physical slices tests g →
      ∃ Q ∈ atoms, beta ≤ ‖r.correlation g Q‖)
    (Term : F → Type*) [∀ f, Fintype (Term f)]
    (coefficient : ∀ f, Term f → ℂ) (atom : ∀ f, Term f → X → ℂ)
    (hexpansionAtoms : ∀ f i, atom f i ∈ atoms)
    (hM : 0 ≤ M) (hmass : ∀ f, (∑ i, ‖coefficient f i‖) ≤ M)
    (happrox : ∀ f x, ‖forecast f x - ∑ i, coefficient f i * atom f i x‖ ≤
      ((tau / B ^ 2) / max 1 ((2 * K * C + forecastCap) / tau)) / 8)
    (hforecastGain : beta ≤
      ((tau / B ^ 2) / max 1 ((2 * K * C + forecastCap) / tau)) / (8 * (M + 1)))
    (hexcess : r.excessMass (μ.siteLaw physical) C ≤ ε)
    (input : X → ℂ) (hinput : ∀ x, ‖input x‖ ≤ B) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (X → ℂ)) (c : Fin n → ℝ) (err : X → ℂ),
      (∀ i, Q i ∈ atoms) ∧ input = (∑ i, c i • Q i) + err ∧
      (∑ i, |c i|) ≤ 2 / beta ∧
      sampledSliceSeminorm μ physical slices tests err ≤
        2 * tau + 2 * (B + 2 / beta) * (K + forecastCap) * ε ∧
      (∀ f, ‖r.correlation err (forecast f)‖ ≤
        2 * tau + 2 * (B + 2 / beta) * (K + forecastCap) * ε) ∧
      (n : ℝ) ≤ 1 + 4 * (2 * K * C + forecastCap) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  have hα : 0 < (tau / B ^ 2) / max 1 ((2 * K * C + forecastCap) / tau) :=
    div_pos (div_pos htau (sq_pos_of_pos hB))
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  apply exists_forecast_augmented_model μ physical slices tests r hr forecast
    hbal hatoms hatom hK hC hforecastCap hB hbeta htau hsize htests hforecast hlocal
    (fun g hg f hlarge => forecast_detector_of_atom_approximation r (forecast f) g
      (coefficient f) (atom f) hα hM hg (hexpansionAtoms f) (happrox f) (hmass f)
      hforecastGain hlarge) hexcess input hinput

theorem exists_forecast_augmented_native_model_of_expansions
    {Ω T X F σ I : Type*} [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    [Nonempty F] {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (μ : FiniteProbabilityWeights Ω) (physical : Ω → T → X)
    (slices : ∀ z, J z → Finset T) (tests : ∀ z, J z → T → ℂ)
    (r : FiniteProbabilityWeights X) (hr : ∀ x, 0 < r.weight x)
    (forecast : F → X → ℂ)
    (w : σ → ℕ) (degree : ℕ) (complexity : ℝ) (sample : X → σ → ℤ)
    (twist : I → X → ℂ) (htwist : ∀ i x, ‖twist i x‖ ≤ 1)
    {K C forecastCap B beta tau ε M : ℝ}
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hforecastCap : 0 ≤ forecastCap)
    (hB : 0 < B) (hbeta : 0 < beta) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hforecast : ∀ f x, ‖forecast f x‖ ≤ forecastCap)
    (hlocal : ∀ g : X → ℂ, (∀ x, ‖g x‖ ≤ 1) →
      (tau / B ^ 2) / max 1 ((2 * K * C + forecastCap) / tau) ≤
        sampledSliceSeminorm μ physical slices tests g →
      ∃ Q ∈ twistedNativeSampleFunctions w degree complexity sample twist, beta ≤ ‖r.correlation g Q‖)
    (Term : F → Type*) [∀ f, Fintype (Term f)]
    (coefficient : ∀ f, Term f → ℂ) (atom : ∀ f, Term f → X → ℂ)
    (hexpansionAtoms : ∀ f i, atom f i ∈ twistedNativeSampleFunctions w degree complexity sample twist)
    (hM : 0 ≤ M) (hmass : ∀ f, (∑ i, ‖coefficient f i‖) ≤ M)
    (happrox : ∀ f x, ‖forecast f x - ∑ i, coefficient f i * atom f i x‖ ≤
      ((tau / B ^ 2) / max 1 ((2 * K * C + forecastCap) / tau)) / 8)
    (hforecastGain : beta ≤
      ((tau / B ^ 2) / max 1 ((2 * K * C + forecastCap) / tau)) / (8 * (M + 1)))
    (hexcess : r.excessMass (μ.siteLaw physical) C ≤ ε)
    (input : X → ℂ) (hinput : ∀ x, ‖input x‖ ≤ B) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (X → ℂ)) (c : Fin n → ℝ) (err : X → ℂ),
      (∀ i, Q i ∈ twistedNativeSampleFunctions w degree complexity sample twist) ∧ input = (∑ i, c i • Q i) + err ∧
      (∑ i, |c i|) ≤ 2 / beta ∧
      sampledSliceSeminorm μ physical slices tests err ≤
        2 * tau + 2 * (B + 2 / beta) * (K + forecastCap) * ε ∧
      (∀ f, ‖r.correlation err (forecast f)‖ ≤
        2 * tau + 2 * (B + 2 / beta) * (K + forecastCap) * ε) ∧
      (n : ℝ) ≤ 1 + 4 * (2 * K * C + forecastCap) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  exact exists_forecast_augmented_model_of_expansions μ physical slices tests r hr forecast
    (twistedNativeSampleFunctions_balanced twist)
    ⟨0, twistedNativeSampleFunctions_zero twist⟩
    (fun Q hQ x => twistedNativeSampleFunctions_norm twist htwist hQ x)
    hK hC hforecastCap hB hbeta htau hsize htests hforecast hlocal
    Term coefficient atom hexpansionAtoms hM hmass happrox hforecastGain hexcess input hinput

end Erdos3

end

section

namespace Erdos3

noncomputable def forecastAugmentedUnitThreshold (u p K C Fcap : ℝ) : ℝ :=
  (Real.exp (-(u + 3)) / Real.exp p ^ 2) /
    max 1 ((2 * K * C + Fcap) / Real.exp (-(u + 3)))

theorem forecastAugmentedUnitThreshold_bounds {u p K C Fcap : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hFp : Fcap ≤ Real.exp p) :
    0 < forecastAugmentedUnitThreshold u p K C Fcap ∧
      forecastAugmentedUnitThreshold u p K C Fcap ≤ 1 ∧
      Real.exp (-(2 * u + 4 * p + 8)) ≤ forecastAugmentedUnitThreshold u p K C Fcap := by
  let τ := Real.exp (-(u + 3))
  let D := max 1 ((2 * K * C + Fcap) / τ)
  have hτ : 0 < τ := Real.exp_pos _
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hτ1 : τ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hep : 1 ≤ Real.exp p := Real.one_le_exp hp
  have hnum : τ / Real.exp p ^ 2 ≤ 1 :=
    (div_le_iff₀ (sq_pos_of_pos (Real.exp_pos p))).mpr (by nlinarith)
  have hKC : K * C ≤ Real.exp p * Real.exp p := mul_le_mul hKp hCp hC (Real.exp_nonneg p)
  have hbound : D ≤ 3 * Real.exp (2 * p + u + 3) := by
    apply max_le
    · have he := Real.one_le_exp (show 0 ≤ 2 * p + u + 3 by positivity)
      linarith
    · calc
        _ ≤ (3 * (Real.exp p * Real.exp p)) / τ := by
          apply div_le_div_of_nonneg_right _ hτ.le
          nlinarith
        _ = 3 * Real.exp (2 * p + u + 3) := by
          dsimp only [τ]
          rw [show 2 * p + u + 3 = p + p + (u + 3) by ring]
          simp only [Real.exp_add, Real.exp_neg, div_eq_mul_inv, inv_inv]
          ring
  refine ⟨div_pos (div_pos hτ (sq_pos_of_pos (Real.exp_pos p))) hD,
    (div_le_iff₀ hD).mpr (by nlinarith [le_max_left 1 ((2 * K * C + Fcap) / τ)]), ?_⟩
  change _ ≤ (τ / Real.exp p ^ 2) / D
  calc
    _ ≤ Real.exp (-(2 * u + 4 * p + 6)) / 3 := by
      rw [show -(2 * u + 4 * p + 8) = -(2 * u + 4 * p + 6) - 2 by ring, Real.exp_sub]
      exact div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num)
        (by linarith [Real.add_one_le_exp (2 : ℝ)])
    _ = (τ / Real.exp p ^ 2) / (3 * Real.exp (2 * p + u + 3)) := by
      dsimp only [τ]
      rw [show -(2 * u + 4 * p + 6) = -(u + 3) - (p + p) - (2 * p + u + 3) by ring,
        Real.exp_sub, Real.exp_sub, Real.exp_add]
      ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hD hbound

theorem forecastAugmentedUnitThreshold_source_precision {u p K C Fcap : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p) (hFp : Fcap ≤ Real.exp p) :
    Real.exp (-(2 * (u + 1) + 4 * p + 7)) ≤
      forecastAugmentedUnitThreshold u p K C Fcap :=
  (Real.exp_le_exp.mpr (by linarith)).trans
    (forecastAugmentedUnitThreshold_bounds hu hp hK hC hKp hCp hFp).2.2

theorem forecastAugmentedUnitThreshold_half_source_precision {u p K C Fcap : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p) (hFp : Fcap ≤ Real.exp p) :
    Real.exp (-(2 * (u + 1) + 4 * p + 7)) ≤
      forecastAugmentedUnitThreshold u p K C Fcap / 2 := by
  calc
    _ = Real.exp (-(2 * u + 4 * p + 8)) / Real.exp 1 := by
      rw [← Real.exp_sub]; congr 1; ring
    _ ≤ Real.exp (-(2 * u + 4 * p + 8)) / 2 :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num)
        (by linarith [Real.add_one_le_exp (1 : ℝ)])
    _ ≤ _ := div_le_div_of_nonneg_right
      (forecastAugmentedUnitThreshold_bounds hu hp hK hC hKp hCp hFp).2.2 (by norm_num)

theorem forecastAugmentedUnitThreshold_atom_gain {u p q K C Fcap M : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p) (hFp : Fcap ≤ Real.exp p)
    (hM : 0 ≤ M) (hMq : M ≤ Real.exp q) :
    Real.exp (-(2 * u + 4 * p + q + 20)) ≤
      forecastAugmentedUnitThreshold u p K C Fcap / (8 * (M + 1)) := by
  have hα := (forecastAugmentedUnitThreshold_bounds hu hp hK hC hKp hCp hFp).2.2
  have hden : 8 * (M + 1) ≤ Real.exp (q + 12) := by
    rw [Real.exp_add]
    have heq := Real.one_le_exp hq
    have he12 : (16 : ℝ) ≤ Real.exp 12 := by
      have h6 := Real.add_one_le_exp (6 : ℝ)
      have h12 : Real.exp (12 : ℝ) = Real.exp 6 * Real.exp 6 := by
        rw [← Real.exp_add]; norm_num
      rw [h12]
      nlinarith
    nlinarith [Real.exp_pos q]
  calc
    _ = Real.exp (-(2 * u + 4 * p + 8)) / Real.exp (q + 12) := by
      rw [← Real.exp_sub]; congr 1; ring
    _ ≤ Real.exp (-(2 * u + 4 * p + 8)) / (8 * (M + 1)) :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) (by positivity) hden
    _ ≤ _ := div_le_div_of_nonneg_right hα (by positivity)

end Erdos3

end

section

namespace Erdos3

theorem forecastAugmented_model_error {u p Q P K Fcap cap tau ε : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hQ : 0 ≤ Q)
    (hK : 0 ≤ K) (hF : 0 ≤ Fcap) (hcap : 0 ≤ cap)
    (hKp : K ≤ Real.exp p) (hFp : Fcap ≤ Real.exp p) (hcapP : cap ≤ Real.exp p)
    (htau : tau ≤ Real.exp (-(u + 3)))
    (hP : u + 2 * p + Q + 32 ≤ P)
    (hε : ε ≤ 6 * positiveProjectionAccuracy P) :
    2 * tau + 2 * (cap + 2 / Real.exp (-Q)) * (K + Fcap) * ε ≤ Real.exp (-u) := by
  have hKP : K + Fcap ≤ Real.exp (p + 1) := by
    rw [Real.exp_add]
    nlinarith [Real.add_one_le_exp (1 : ℝ), Real.exp_pos p]
  have hcapP' : cap ≤ Real.exp (p + 1) :=
    hcapP.trans (Real.exp_le_exp.mpr (by linarith))
  have h := allocated_native_approximation_error hu (show 0 ≤ p + 1 by linarith) hQ
    (add_nonneg hK hF) hcap hKP hcapP' htau (by linarith : u + 2 * (p + 1) + Q + 30 ≤ P) hε
  convert h using 1
  ring

theorem forecastAugmented_model_size {u p Q K C Fcap : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hQ : 0 ≤ Q)
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hF : 0 ≤ Fcap)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p) (hFp : Fcap ≤ Real.exp p) :
    2 / Real.exp (-Q) ≤ Real.exp (Q + 2) ∧
      1 + 4 * (2 * K * C + Fcap) ^ 2 /
        (Real.exp (-Q) ^ 2 * Real.exp (-(u + 3)) ^ 2) ≤
        Real.exp (2 * Q + 2 * u + 4 * p + 34) := by
  have hKP : K + Fcap ≤ Real.exp (p + 1) := by
    rw [Real.exp_add]
    nlinarith [Real.add_one_le_exp (1 : ℝ), Real.exp_pos p]
  have hCp' : C ≤ Real.exp (p + 1) := hCp.trans (Real.exp_le_exp.mpr (by linarith))
  obtain ⟨hcoeff, hterms⟩ := allocatedModel_size_bounds hu (show 0 ≤ p + 1 by linarith)
    hQ (add_nonneg hK hF) (by linarith : 0 ≤ C) hKP hCp'
  refine ⟨hcoeff, ?_⟩
  have hL : 2 * K * C + Fcap ≤ (K + Fcap) * (2 * C) := by nlinarith
  have hL0 : 0 ≤ 2 * K * C + Fcap := by positivity
  calc
    _ ≤ 1 + 4 * ((K + Fcap) * (2 * C)) ^ 2 /
        (Real.exp (-Q) ^ 2 * Real.exp (-(u + 3)) ^ 2) := by gcongr
    _ ≤ Real.exp (2 * Q + 2 * u + 4 * (p + 1) + 30) := hterms
    _ = _ := by congr 1; ring

end Erdos3

end

section

namespace Erdos3

theorem forecastAugmented_separate_source_precision {u p pSource K C Fcap : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hSource : 0 ≤ pSource)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hFp : Fcap ≤ Real.exp p) :
    0 ≤ u + 2 * p + 1 ∧
      Real.exp (-(2 * (u + 2 * p + 1) + 4 * pSource + 7)) ≤
        forecastAugmentedUnitThreshold u p K C Fcap / 2 := by
  refine ⟨by positivity, ?_⟩
  apply (Real.exp_le_exp.mpr
    (show -(2 * (u + 2 * p + 1) + 4 * pSource + 7) ≤
      -(2 * (u + 1) + 4 * p + 7) by linarith)).trans
  exact forecastAugmentedUnitThreshold_half_source_precision hu hp hK hC hKp hCp hFp

theorem forecastAugmented_approximation_precision {u p K C Fcap : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hFp : Fcap ≤ Real.exp p) :
    Real.exp (-(2 * u + 4 * p + 12)) ≤
      forecastAugmentedUnitThreshold u p K C Fcap / 8 := by
  have h8 : (8 : ℝ) ≤ Real.exp 4 := by
    have h2 := Real.add_one_le_exp (2 : ℝ)
    have he : Real.exp (4 : ℝ) = Real.exp 2 * Real.exp 2 := by
      rw [← Real.exp_add]; norm_num
    rw [he]
    nlinarith
  calc
    _ = Real.exp (-(2 * u + 4 * p + 8)) / Real.exp 4 := by
      rw [← Real.exp_sub]; congr 1; ring
    _ ≤ Real.exp (-(2 * u + 4 * p + 8)) / 8 :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) h8
    _ ≤ _ := div_le_div_of_nonneg_right
      (forecastAugmentedUnitThreshold_bounds hu hp hK hC hKp hCp hFp).2.2
      (by norm_num)

theorem forecastAugmented_model_parameters {u p q sourceGain : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hq : 0 ≤ q) (hsource : 0 ≤ sourceGain) :
    let Q := max sourceGain (2 * u + 4 * p + q + 20)
    let Ptail := u + 2 * p + Q + 32
    0 ≤ Q ∧ 0 ≤ Ptail ∧ sourceGain ≤ Q ∧
      2 * u + 4 * p + q + 20 ≤ Q ∧
      Real.exp (-Q) ≤ Real.exp (-sourceGain) ∧
      u + 2 * p + Q + 32 ≤ Ptail := by
  dsimp only
  have hQ : 0 ≤ max sourceGain (2 * u + 4 * p + q + 20) :=
    hsource.trans (le_max_left _ _)
  exact ⟨hQ, by positivity, le_max_left _ _, le_max_right _ _,
    Real.exp_le_exp.mpr (neg_le_neg (le_max_left _ _)), le_rfl⟩

theorem forecastAugmented_model_parameters_bound {u p q sourceGain B : ℝ}
    (hB : 0 ≤ B) (hu : u ≤ B) (hp : p ≤ B) (hq : q ≤ B)
    (hsource : sourceGain ≤ B) :
    let Q := max sourceGain (2 * u + 4 * p + q + 20)
    2 * u + 4 * p + 12 ≤ 6 * B + 12 ∧
      Q ≤ 7 * B + 20 ∧
      u + 2 * p + Q + 32 ≤ 10 * B + 52 ∧
      Q + 2 ≤ 7 * B + 22 ∧
      2 * Q + 2 * u + 4 * p + 34 ≤ 20 * B + 74 := by
  dsimp only
  have hQ : max sourceGain (2 * u + 4 * p + q + 20) ≤ 7 * B + 20 :=
    max_le (by linarith) (by linarith)
  exact ⟨by linarith, hQ, by linarith, by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3

theorem fixedCenterForecast_source_threshold
    {u p sourceU sourceModel : ℝ}
    (hsource : u + 2 * p + 1 ≤ sourceU) (hmodel : 0 ≤ sourceModel) :
    Real.exp (-(2 * sourceU + 4 * sourceModel + 7)) ≤
      Real.exp (-(2 * u + 4 * p + 8)) / 2 := by
  calc
    _ ≤ Real.exp (-(2 * u + 4 * p + 9)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-(2 * u + 4 * p + 8)) / Real.exp 1 := by
      rw [← Real.exp_sub]
      congr 1
      ring
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num)
      (by linarith [Real.add_one_le_exp (1 : ℝ)])

theorem fixedCenterForecast_source_threshold_half_le_one
    {u p : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p) :
    Real.exp (-(2 * u + 4 * p + 8)) / 2 ≤ 1 := by
  have h := Real.exp_le_one_iff.mpr (show -(2 * u + 4 * p + 8) ≤ 0 by linarith)
  linarith

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem exists_normalizedTwist_forecast_approximation
    {Ω T X Forecast : Type*} [Nonempty Forecast] [Fintype Ω] [Fintype T] [Nonempty T]
    [Fintype X] [DecidableEq X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) [∀ i, NeZero (N i)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    {periodCap coverCap : ℝ} {lip : ℝ≥0}
    {Tests : Ω → Type*} [∀ z, Nonempty (Tests z)]
    (μ : FiniteProbabilityWeights Ω)
    (physical : Ω → T → integerBox N)
    (site : Ω → T → X → ℤ)
    (hphysical : ∀ z t, (physical z t).val = site z t)
    (slices : ∀ z, Tests z → Finset T)
    (tests : ∀ z, Tests z → T → ℂ)
    (w : X → ℕ) (degree : ℕ) (complexity : ℝ)
    (forecast : Forecast → integerBox N → ℂ)
    {K C forecastCap cap beta tau εtail M : ℝ}
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hforecastCap : 0 ≤ forecastCap) (hcap : 0 < cap)
    (hbeta : 0 < beta) (htau : 0 < tau)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hforecast : ∀ f u, ‖forecast f u‖ ≤ forecastCap)
    (hdetect : ∀ signal : (X → ℤ) → ℂ,
      (∀ u, ‖signal u‖ ≤ 1) →
      (∀ u, u ∉ integerBox N → signal u = 0) →
      (tau / cap ^ 2) / max 1 ((2 * K * C + forecastCap) / tau) ≤
        sampledSliceSeminorm μ site slices tests signal →
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel w degree complexity
          (fun u : integerBox N => u.val) G) ∧
        beta ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun u => signal u.val)
          (fun u => star (W.eval N poly u.val) * G u)‖)
    (Term : Forecast → Type*) [∀ f, Fintype (Term f)]
    (coefficient : ∀ f, Term f → ℂ) (atom : ∀ f, Term f → integerBox N → ℂ)
    (hexpansionAtoms : ∀ f i, atom f i ∈ twistedNativeSampleFunctions w degree complexity
      (fun u : integerBox N => u.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (u : integerBox N) => W.eval N poly u.val))
    (hM : 0 ≤ M) (hmass : ∀ f, (∑ i, ‖coefficient f i‖) ≤ M)
    (happrox : ∀ f u, ‖forecast f u - ∑ i, coefficient f i * atom f i u‖ ≤
      ((tau / cap ^ 2) / max 1 ((2 * K * C + forecastCap) / tau)) / 8)
    (hforecastGain : beta ≤
      ((tau / cap ^ 2) / max 1 ((2 * K * C + forecastCap) / tau)) / (8 * (M + 1)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N)
      (integerBox_nonempty N)).excessMass (μ.siteLaw physical) C ≤ εtail)
    (input : integerBox N → ℂ) (hinput : ∀ u, ‖input u‖ ≤ cap) :
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (Q : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, Q i ∈ twistedNativeSampleFunctions w degree complexity
        (fun u : integerBox N => u.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
          (u : integerBox N) => W.eval N poly u.val)) ∧
      input = (∑ i, coeff i • Q i) + err ∧
      (∑ i, |coeff i|) ≤ 2 / beta ∧
      sampledSliceSeminorm μ physical slices tests err ≤
        2 * tau + 2 * (cap + 2 / beta) * (K + forecastCap) * εtail ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
        (integerBox_nonempty N)).correlation err (forecast f)‖ ≤
        2 * tau + 2 * (cap + 2 / beta) * (K + forecastCap) * εtail) ∧
      (nterms : ℝ) ≤ 1 + 4 * (2 * K * C + forecastCap) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  let : Nonempty (integerBox N) := (integerBox_nonempty N).to_subtype
  have htwist (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
      (u : integerBox N) : ‖W.eval N poly u.val‖ ≤ 1 := W.norm_eval_le N poly u.val
  have hdetector (g : integerBox N → ℂ) (hg : ∀ u, ‖g u‖ ≤ 1)
      (hlarge : (tau / cap ^ 2) / max 1 ((2 * K * C + forecastCap) / tau) ≤
        sampledSliceSeminorm μ physical slices tests g) :
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel w degree complexity
          (fun u : integerBox N => u.val) G) ∧
        beta ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation g
          (fun u => star (W.eval N poly u.val) * G u)‖ := by
    let ext := finiteSiteExtension (Subtype.val : integerBox N → X → ℤ) g
    let signal := zeroExtendFinset (integerBox N) ext
    have hsignal (u) : ‖signal u‖ ≤ 1 :=
      zeroExtendFinset_norm_le_one (integerBox N) ext
        (fun u _ => finiteSiteExtension_norm_le _ g hg u) u
    have hzero (u) (hu : u ∉ integerBox N) : signal u = 0 := by
      simp only [signal, zeroExtendFinset, ite_eq_right hu]
    have hvalue (u : integerBox N) : signal u.val = g u := by
      simpa only [signal, zeroExtendFinset, ite_eq_left u.property, ext] using
        finiteSiteExtension_apply Subtype.val Subtype.val_injective g u
    have hseminorm := sampledSliceSeminorm_congr_values μ site physical slices tests
      hsize htests signal g (fun z t => by rw [← hphysical z t]; exact hvalue _)
    obtain ⟨W, G, hG, hc⟩ := hdetect signal hsignal hzero
      (hseminorm.symm ▸ hlarge)
    exact ⟨W, G, hG, by simpa only [hvalue] using hc⟩
  have hr (u : integerBox N) : 0 <
      (FiniteProbabilityWeights.uniformFinset (integerBox N)
        (integerBox_nonempty N)).weight u := by
    change 0 < (Fintype.card (integerBox N) : ℝ)⁻¹
    positivity
  apply exists_forecast_augmented_native_model_of_expansions μ physical slices tests
    (FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)) hr forecast
    w degree complexity (fun u : integerBox N => u.val)
    (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
      (u : integerBox N) => W.eval N poly u.val)
    htwist hK hC hforecastCap hcap hbeta htau hsize htests hforecast ?_
    Term coefficient atom hexpansionAtoms hM hmass happrox hforecastGain hexcess input hinput
  intro g hg hlarge
  obtain ⟨W, G, hG, hc⟩ := hdetector g hg hlarge
  exact ⟨_, Or.inr ⟨W, G, hG, rfl⟩, hc⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_normalizedTwist_forecast_model
    {Ω T X Forecast : Type*} [Nonempty Forecast] [Fintype Ω] [Fintype T] [Nonempty T]
    [Fintype X] [DecidableEq X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) [∀ i, NeZero (N i)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    {periodCap coverCap : ℝ} {lip : ℝ≥0}
    {Tests : Ω → Type*} [∀ z, Nonempty (Tests z)]
    (μ : FiniteProbabilityWeights Ω)
    (physical : Ω → T → integerBox N)
    (site : Ω → T → X → ℤ)
    (hphysical : ∀ z t, (physical z t).val = site z t)
    (slices : ∀ z, Tests z → Finset T)
    (tests : ∀ z, Tests z → T → ℂ)
    (w : X → ℕ) (degree : ℕ) (complexity : ℝ)
    (forecast : Forecast → integerBox N → ℂ)
    {u p Q P q K C forecastCap εtail M : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hQ : 0 ≤ Q) (hq : 0 ≤ q)
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hforecastCap : 0 ≤ forecastCap)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hforecastCapP : forecastCap ≤ Real.exp p)
    (hQlarge : 2 * u + 4 * p + q + 20 ≤ Q)
    (hP : u + 2 * p + Q + 32 ≤ P)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hforecast : ∀ f u, ‖forecast f u‖ ≤ forecastCap)
    (hdetect : ∀ signal : (X → ℤ) → ℂ,
      (∀ u, ‖signal u‖ ≤ 1) →
      (∀ u, u ∉ integerBox N → signal u = 0) →
      forecastAugmentedUnitThreshold u p K C forecastCap ≤
        sampledSliceSeminorm μ site slices tests signal →
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel w degree complexity
          (fun u : integerBox N => u.val) G) ∧
        Real.exp (-Q) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun u => signal u.val)
          (fun u => star (W.eval N poly u.val) * G u)‖)
    (Term : Forecast → Type*) [∀ f, Fintype (Term f)]
    (coefficient : ∀ f, Term f → ℂ) (atom : ∀ f, Term f → integerBox N → ℂ)
    (hexpansionAtoms : ∀ f i, atom f i ∈ twistedNativeSampleFunctions w degree complexity
      (fun u : integerBox N => u.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (u : integerBox N) => W.eval N poly u.val))
    (hM : 0 ≤ M) (hMq : M ≤ Real.exp q) (hmass : ∀ f, (∑ i, ‖coefficient f i‖) ≤ M)
    (happrox : ∀ f v, ‖forecast f v - ∑ i, coefficient f i * atom f i v‖ ≤
      (forecastAugmentedUnitThreshold u p K C forecastCap) / 8)
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N)
      (integerBox_nonempty N)).excessMass (μ.siteLaw physical) C ≤ εtail)
    (htail : εtail ≤ 6 * positiveProjectionAccuracy P)
    (input : integerBox N → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (models : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, models i ∈ twistedNativeSampleFunctions w degree complexity
        (fun u : integerBox N => u.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
          (u : integerBox N) => W.eval N poly u.val)) ∧
      input = (∑ i, coeff i • models i) + err ∧
      (∑ i, |coeff i|) ≤ Real.exp (Q + 2) ∧
      sampledSliceSeminorm μ physical slices tests err ≤
        Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
        (integerBox_nonempty N)).correlation err (forecast f)‖ ≤
        Real.exp (-u)) ∧
      (nterms : ℝ) ≤ Real.exp (2 * Q + 2 * u + 4 * p + 34) := by
  have hgain : Real.exp (-Q) ≤
      forecastAugmentedUnitThreshold u p K C forecastCap / (8 * (M + 1)) :=
    (Real.exp_le_exp.mpr (neg_le_neg hQlarge)).trans
      (forecastAugmentedUnitThreshold_atom_gain hu hp hq hK (zero_le_one.trans hC)
        hKp hCp hforecastCapP hM hMq)
  obtain ⟨nterms, hn, models, coeff, err, hmodels, heq, hcoeff, herr, hforecasts, hterms⟩ :=
    exists_normalizedTwist_forecast_approximation N poly μ physical site hphysical slices tests
      w degree complexity forecast hK hC hforecastCap (Real.exp_pos p)
      (Real.exp_pos (-Q)) (Real.exp_pos (-(u + 3))) hsize htests hforecast
      hdetect Term coefficient atom hexpansionAtoms hM hmass happrox hgain hexcess input hinput
  have herror := forecastAugmented_model_error hu hp hQ hK hforecastCap (Real.exp_nonneg p)
    hKp hforecastCapP le_rfl (le_refl (Real.exp (-(u + 3)))) hP htail
  have hbudget := forecastAugmented_model_size hu hp hQ hK hC hforecastCap
    hKp hCp hforecastCapP
  exact ⟨nterms, hn, models, coeff, err, hmodels, heq, hcoeff.trans hbudget.1,
    herr.trans herror, fun f => (hforecasts f).trans herror, hterms.trans hbudget.2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_averaged_normalizedTwist_forecast_joint_model
    {Center Ω T X Forecast : Type*} [MeasurableSpace Center] [Nonempty Forecast] [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype T] [Nonempty T]
    [Fintype X] [DecidableEq X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) [∀ i, NeZero (N i)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    {periodCap coverCap : ℝ} {lip : ℝ≥0}
    {Tests : Ω → Type*} [∀ z, Nonempty (Tests z)]
    (μ : Measure Center) [IsProbabilityMeasure μ]
    (law : Center → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (physical : Ω → T → integerBox N)
    (site : Ω → T → X → ℤ)
    (hphysical : ∀ z t, (physical z t).val = site z t)
    (slices : ∀ z, Tests z → Finset T)
    (tests : ∀ z, Tests z → T → ℂ)
    (w : X → ℕ) (degree : ℕ) (complexity : ℝ)
    (forecast : Forecast → integerBox N → ℂ)
    {u p Q P q K C forecastCap εtail M : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hQ : 0 ≤ Q) (hq : 0 ≤ q)
    (hK : 0 ≤ K) (hC : 1 ≤ C) (hforecastCap : 0 ≤ forecastCap)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hforecastCapP : forecastCap ≤ Real.exp p)
    (hQlarge : 2 * u + 4 * p + q + 20 ≤ Q)
    (hP : u + 2 * p + Q + 32 ≤ P)
    (hslices : ∀ z j, (slices z j).Nonempty)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hforecast : ∀ f u, ‖forecast f u‖ ≤ forecastCap)
    (hdetect : ∀ signal : (X → ℤ) → ℂ,
      (∀ u, ‖signal u‖ ≤ 1) →
      (∀ u, u ∉ integerBox N → signal u = 0) →
      forecastAugmentedUnitThreshold u p K C forecastCap ≤
        sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) site slices tests signal →
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel w degree complexity
          (fun u : integerBox N => u.val) G) ∧
        Real.exp (-Q) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun u => signal u.val)
          (fun u => star (W.eval N poly u.val) * G u)‖)
    (Term : Forecast → Type*) [∀ f, Fintype (Term f)]
    (coefficient : ∀ f, Term f → ℂ) (atom : ∀ f, Term f → integerBox N → ℂ)
    (hexpansionAtoms : ∀ f i, atom f i ∈ twistedNativeSampleFunctions w degree complexity
      (fun u : integerBox N => u.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (u : integerBox N) => W.eval N poly u.val))
    (hM : 0 ≤ M) (hMq : M ≤ Real.exp q) (hmass : ∀ f, (∑ i, ‖coefficient f i‖) ≤ M)
    (happrox : ∀ f v, ‖forecast f v - ∑ i, coefficient f i * atom f i v‖ ≤
      (forecastAugmentedUnitThreshold u p K C forecastCap) / 8)
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N)
      (integerBox_nonempty N)).excessMass ((centeredFiniteMarginal μ law hweight).siteLaw physical) C ≤ εtail)
    (htail : εtail ≤ 6 * positiveProjectionAccuracy P)
    (input : integerBox N → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (models : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, models i ∈ twistedNativeSampleFunctions w degree complexity
        (fun u : integerBox N => u.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
          (u : integerBox N) => W.eval N poly u.val)) ∧
      input = (∑ i, coeff i • models i) + err ∧
      (∑ i, |coeff i|) ≤ Real.exp (Q + 2) ∧
      sampledSliceSeminorm (centeredFiniteMarginal μ law hweight) physical slices tests err ≤
        Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
        (integerBox_nonempty N)).correlation err (forecast f)‖ ≤
        Real.exp (-u)) ∧
      (nterms : ℝ) ≤ Real.exp (2 * Q + 2 * u + 4 * p + 34) ∧
      ∀ errLocal : Center × Ω → ℂ, Measurable errLocal →
        (∀ center z, ∃ j, errLocal (center, z) =
          𝔼 t ∈ slices z j, err (physical z t) * tests z j t) →
        Integrable errLocal (centeredFiniteProbabilityMeasure μ law) ∧
          (∫ y, ‖errLocal y‖ ∂centeredFiniteProbabilityMeasure μ law) ≤ Real.exp (-u) := by
  obtain ⟨nterms, hn, models, coeff, err, hmodels, heq, hcoeff, herr, hforecasts, hterms⟩ :=
    exists_normalizedTwist_forecast_model N poly (centeredFiniteMarginal μ law hweight)
      physical site hphysical slices tests w degree complexity forecast hu hp hQ hq
      hK hC hforecastCap hKp hCp hforecastCapP hQlarge hP hsize htests hforecast
      hdetect Term coefficient atom hexpansionAtoms hM hMq hmass happrox hexcess htail input hinput
  refine ⟨nterms, hn, models, coeff, err, hmodels, heq, hcoeff, herr, hforecasts, hterms, ?_⟩
  intro errLocal hmeas hselected
  obtain ⟨hintegrable, hbound⟩ := integral_selected_slice_residual_le μ law hweight
    physical slices tests hslices hsize htests err errLocal hmeas hselected
  exact ⟨hintegrable, hbound.trans herr⟩

end Erdos3.VectorPolynomial

end

end OAI
