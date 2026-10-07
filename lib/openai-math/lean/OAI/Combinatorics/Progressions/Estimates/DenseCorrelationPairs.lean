-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib.Combinatorics.Pigeonhole
import OAI.Combinatorics.Progressions.Estimates.ShiftTestingGowers
import OAI.Combinatorics.Progressions.Probability.FiniteConditionedMass
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_dense_level_set {H : Type*} [Fintype H] [Nonempty H]
    (f : H → ℝ) {a : ℝ} (ha : 0 ≤ a) (hf : ∀ h, f h ≤ 1) (hmean : a ≤ 𝔼 h, f h) :
    ∃ S : Finset H, a / 2 * Fintype.card H ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, a / 2 ≤ f h := by
  classical
  let S := Finset.univ.filter (fun h => a / 2 ≤ f h)
  have hpoint (h : H) : f h ≤ a / 2 + (if h ∈ S then (1 : ℝ) else 0) := by
    by_cases hs : h ∈ S
    · simp only [hs, ite_true]
      linarith [hf h]
    · simp only [hs, ite_false]
      have hsmall : f h < a / 2 := by simpa only [S, Finset.mem_filter,
        Finset.mem_univ, true_and, not_le] using hs
      linarith
  have hindicator : (𝔼 h, if h ∈ S then (1 : ℝ) else 0) =
      (S.card : ℝ) / Fintype.card H := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  have h := hmean.trans (Finset.expect_le_expect (fun h _ => hpoint h))
  rw [Finset.expect_add_distrib, Fintype.expect_const, hindicator] at h
  have hcard : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  refine ⟨S, ?_, fun h hh => (Finset.mem_filter.mp hh).2⟩
  apply (le_div_iff₀ hcard).mp
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_anchor_branch {I G : Type*} [Fintype I] [Fintype G] [Nonempty G]
    (anchor : I → G) (branch : I → Bool) {α : ℝ} (hα : 0 < α)
    (hsize : α * (Fintype.card G : ℝ) ^ 3 ≤ Fintype.card I) :
    ∃ (k : G) (b : Bool) (T : Finset I), T.Nonempty ∧
      α / 2 * (Fintype.card G : ℝ) ^ 2 ≤ (T.card : ℝ) ∧
      ∀ t ∈ T, anchor t = k ∧ branch t = b := by
  classical
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hb : Fintype.card (G × Bool) • (α / 2 * (Fintype.card G : ℝ) ^ 2) ≤
      (Fintype.card I : ℝ) := by
    calc
      _ = α * (Fintype.card G : ℝ) ^ 3 := by
        simp only [nsmul_eq_mul, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
        ring
      _ ≤ _ := hsize
  obtain ⟨⟨k, b⟩, hkb⟩ := Fintype.exists_le_card_fiber_of_nsmul_le_card
    (fun i => (anchor i, branch i)) hb
  let T := Finset.univ.filter (fun i => (anchor i, branch i) = (k, b))
  have hTsize : α / 2 * (Fintype.card G : ℝ) ^ 2 ≤ (T.card : ℝ) := hkb
  have hTpos : (0 : ℝ) < T.card := lt_of_lt_of_le (by positivity) hTsize
  refine ⟨k, b, T, Finset.card_pos.mp (by exact_mod_cast hTpos), hTsize, ?_⟩
  intro t ht
  exact Prod.mk.inj (Finset.mem_filter.mp ht).2

theorem exists_dense_first_fibers {I G : Type*} [Fintype G] [Nonempty G] [DecidableEq G]
    (T : Finset I) (a h : I → G) (hinj : Set.InjOn (fun i => (a i, h i)) (T : Set I))
    {ρ : ℝ} (hρ : 0 < ρ) (hsize : ρ * (Fintype.card G : ℝ) ^ 2 ≤ T.card) :
    ∃ A : Finset G, A.Nonempty ∧ ρ / 2 * (Fintype.card G : ℝ) ≤ (A.card : ℝ) ∧
      ∀ x ∈ A, ρ / 2 * (Fintype.card G : ℝ) ≤ ((T.filter (fun i => a i = x)).card : ℝ) := by
  classical
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  let F (x : G) := T.filter (fun i => a i = x)
  have hcard (x : G) : (F x).card ≤ Fintype.card G := by
    have hmap : Function.Injective (fun t : F x => h t.val) := by
      intro u v huv
      apply Subtype.ext
      apply hinj (Finset.mem_filter.mp u.property).1 (Finset.mem_filter.mp v.property).1
      exact Prod.ext ((Finset.mem_filter.mp u.property).2.trans (Finset.mem_filter.mp v.property).2.symm) huv
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective _ hmap
  have hsum : ∑ x : G, (F x).card = T.card := by
    symm
    exact Finset.card_eq_sum_card_fiberwise (f := a) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  let density (x : G) := ((F x).card : ℝ) / Fintype.card G
  have hmean : ρ ≤ 𝔼 x, density x := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [density, ← Finset.sum_div, ← Nat.cast_sum, hsum]
    apply (le_div_iff₀ hN).mpr
    apply (le_div_iff₀ hN).mpr
    nlinarith only [hsize]
  have hunit (x : G) : density x ≤ 1 := by
    apply (div_le_iff₀ hN).mpr
    simpa only [one_mul] using (Nat.cast_le.mpr (hcard x) : ((F x).card : ℝ) ≤ Fintype.card G)
  obtain ⟨A, hAsize, hA⟩ := exists_dense_level_set density hρ.le hunit hmean
  have hApos : (0 : ℝ) < A.card := lt_of_lt_of_le (by positivity) hAsize
  refine ⟨A, Finset.card_pos.mp (by exact_mod_cast hApos), hAsize, ?_⟩
  intro x hx
  exact (le_div_iff₀ hN).mp (hA x hx)

theorem exists_dense_anchored_fibers {I G : Type*} [Fintype I] [Fintype G]
    [Nonempty G] [DecidableEq G] (a h k : I → G) (branch : I → Bool)
    (hinj : Function.Injective (fun i => (a i, h i, k i)))
    {α : ℝ} (hα : 0 < α) (hsize : α * (Fintype.card G : ℝ) ^ 3 ≤ Fintype.card I) :
    ∃ (anchor : G) (b : Bool) (T : Finset I) (A : Finset G), A.Nonempty ∧
      α / 4 * (Fintype.card G : ℝ) ≤ (A.card : ℝ) ∧
      (∀ t ∈ T, k t = anchor ∧ branch t = b) ∧
      Set.InjOn (fun i => (a i, h i)) (T : Set I) ∧
      ∀ x ∈ A, α / 4 * (Fintype.card G : ℝ) ≤ ((T.filter (fun i => a i = x)).card : ℝ) := by
  classical
  obtain ⟨anchor, b, T, _, hTsize, hT⟩ := exists_large_anchor_branch k branch hα hsize
  have hpair : Set.InjOn (fun i => (a i, h i)) (T : Set I) := by
    intro u hu v hv huv
    have hau : a u = a v := congrArg (fun z : G × G => z.1) huv
    have hhu : h u = h v := congrArg (fun z : G × G => z.2) huv
    apply hinj
    exact Prod.ext hau (Prod.ext hhu ((hT u hu).1.trans (hT v hv).1.symm))
  obtain ⟨A, hA, hAsize, hAfiber⟩ := exists_dense_first_fibers T a h hpair (by positivity) hTsize
  refine ⟨anchor, b, T, A, hA, ?_, hT, hpair, ?_⟩
  · convert hAsize using 1; ring
  · intro x hx
    convert hAfiber x hx using 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {H Ω : Type*} [Fintype H] [Fintype Ω]

theorem weighted_mean_square_eq_pair_correlation
    (p : FiniteProbabilityWeights Ω) (v : H → Ω → ℂ) :
    p.mean (fun x => ‖𝔼 h, v h x‖ ^ 2) =
      𝔼 h, 𝔼 k, (p.correlation (v h) (v k)).re := by
  have h := congrArg Complex.re (p.correlation_average_left v (fun x => 𝔼 k, v k x))
  rw [p.correlation_self, Complex.ofReal_re] at h
  simpa only [p.correlation_average_right, expect_re] using h

theorem exists_weighted_common_anchor [Nonempty H]
    (p : FiniteProbabilityWeights Ω) (v : H → Ω → ℂ) {a : ℝ}
    (ha : 0 ≤ a) (hv : ∀ h x, ‖v h x‖ ≤ 1)
    (hmean : ∀ h, a ≤ (p.complexMean (v h)).re) :
    ∃ (h₀ : H) (S : Finset H), a ^ 2 / 2 * Fintype.card H ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, a ^ 2 / 2 ≤ ‖p.correlation (v h) (v h₀)‖ := by
  have hmean' : a ≤ (p.complexMean (fun x => 𝔼 h, v h x)).re := by
    rw [p.complexMean_average, expect_re]
    exact (Fintype.expect_const a).symm.trans_le (Finset.expect_le_expect (fun h _ => hmean h))
  have hnorm := hmean'.trans (Complex.re_le_norm _)
  have henergy := (pow_le_pow_left₀ ha hnorm 2).trans
    (p.norm_complexMean_sq_le (fun x => 𝔼 h, v h x))
  rw [weighted_mean_square_eq_pair_correlation] at henergy
  rw [Finset.expect_comm] at henergy
  obtain ⟨h₀, _, hslice⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty henergy
  have hcap (h : H) : (p.correlation (v h) (v h₀)).re ≤ 1 :=
    (Complex.re_le_norm _).trans (p.norm_correlation_le_one _ _ (hv h) (hv h₀))
  obtain ⟨S, hcard, hS⟩ := exists_dense_level_set
    (fun h => (p.correlation (v h) (v h₀)).re) (sq_nonneg a) hcap hslice
  exact ⟨h₀, S, hcard, fun h hh => (hS h hh).trans (Complex.re_le_norm _)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_common_anchor {H J : Type*} [Fintype H] [Nonempty H] [Fintype J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (v : H → ∀ j, Ω j → ℂ)
    {delta : ℝ} (hdelta : 0 < delta) (hv : ∀ h j x, ‖v h j x‖ ≤ 1)
    (hbias : ∀ h j, delta ≤ ‖(p j).complexMean (v h j)‖) :
    ∃ (h₀ : H) (S : Finset H),
      delta ^ (2 * Fintype.card J) / 2 * Fintype.card H ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ j, delta ^ (2 * Fintype.card J) / 2 ≤
        ‖(p j).correlation (v h j) (v h₀ j)‖ := by
  classical
  have hphase (h : H) (j : J) := exists_complex_unit_phase ((p j).complexMean (v h j))
  choose a ha hamean using hphase
  let V : H → (∀ j, Ω j) → ℂ := fun h x => ∏ j, a h j * v h j (x j)
  let q := FiniteProbabilityWeights.pi p
  have hV : ∀ h x, ‖V h x‖ ≤ 1 := by
    intro h x
    change ‖∏ j, a h j * v h j (x j)‖ ≤ 1
    rw [norm_prod]
    apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    intro j _
    rw [norm_mul, ha, one_mul]
    exact hv h j (x j)
  have hmean (h : H) : delta ^ Fintype.card J ≤ (q.complexMean (V h)).re := by
    calc
      _ = ∏ _j : J, delta := by simp
      _ ≤ ∏ j, ‖(p j).complexMean (v h j)‖ :=
        Finset.prod_le_prod₀ (fun _ _ => hdelta.le) (fun coordinate _ => hbias h coordinate)
      _ = _ := by
        dsimp only [q, V]
        rw [FiniteProbabilityWeights.complexMean_pi_product p (fun j x => a h j * v h j x)]
        simp_rw [FiniteProbabilityWeights.complexMean_mul_left, hamean]
        rw [← Complex.ofReal_prod, Complex.ofReal_re]
  have hcorr (h k : H) : ‖q.correlation (V h) (V k)‖ =
      ∏ j, ‖(p j).correlation (v h j) (v k j)‖ := by
    dsimp only [q, V]
    rw [FiniteProbabilityWeights.correlation_pi_product p
      (fun j x => a h j * v h j x) (fun j x => a k j * v k j x), norm_prod]
    apply Finset.prod_congr rfl
    intro j _
    exact (p j).norm_correlation_mul_phases (v h j) (v k j) (ha h j) (ha k j)
  obtain ⟨h₀, S, hcard, hS⟩ := exists_weighted_common_anchor q V
    (pow_nonneg hdelta.le _) hV hmean
  have hpow : (delta ^ Fintype.card J) ^ 2 = delta ^ (2 * Fintype.card J) := by
    rw [← pow_mul, Nat.mul_comm]
  rw [hpow] at hcard hS
  refine ⟨h₀, S, hcard, ?_⟩
  intro h hh j
  have hprod : (∏ k, ‖(p k).correlation (v h k) (v h₀ k)‖) ≤
      ‖(p j).correlation (v h j) (v h₀ j)‖ := by
    have h := Finset.prod_le_prod_of_subset_of_le_one₀ (s := {j}) (t := Finset.univ)
      (f := fun k => ‖(p k).correlation (v h k) (v h₀ k)‖) (by simp)
      (fun k _ => norm_nonneg _) (fun k _ _ =>
        (p k).norm_correlation_le_one (v h k) (v h₀ k) (hv h k) (hv h₀ k))
    simpa only [Finset.prod_singleton] using h
  exact ((hS h hh).trans_eq (hcorr h h₀)).trans hprod

theorem exists_common_anchor_on_finset {I J : Type*} [Fintype J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (H : Finset I) (hH : H.Nonempty)
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (v : I → ∀ j, Ω j → ℂ)
    {delta : ℝ} (hdelta : 0 < delta) (hv : ∀ h ∈ H, ∀ j x, ‖v h j x‖ ≤ 1)
    (hbias : ∀ h ∈ H, ∀ j, delta ≤ ‖(p j).complexMean (v h j)‖) :
    ∃ h₀ ∈ H, ∃ S ⊆ H,
      delta ^ (2 * Fintype.card J) / 2 * H.card ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ j, delta ^ (2 * Fintype.card J) / 2 ≤
        ‖(p j).correlation (v h j) (v h₀ j)‖ := by
  classical
  let : Nonempty H := ⟨⟨hH.choose, hH.choose_spec⟩⟩
  obtain ⟨h₀, S, hcard, hS⟩ := exists_common_anchor p (fun h : H => v h) hdelta
    (fun h => hv h h.property) (fun h => hbias h h.property)
  let S' := S.image (fun h : H => (h : I))
  have hcard' : S'.card = S.card := Finset.card_image_of_injective _ Subtype.val_injective
  refine ⟨h₀, h₀.property, S', ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hh
    exact k.property
  · simpa only [hcard', Fintype.card_coe] using hcard
  · intro h hh j
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hh
    exact hS k hk j

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def partnerAnchorWeight {G : Type*} (U V Q : G → ℂ) (x : G) : ℂ :=
  U x * star (V x) * (Q x * star (Q x))

theorem partnerAnchorWeight_eq_norm_sq {G : Type*} (U V Q : G → ℂ) (x : G) :
    partnerAnchorWeight U V Q x = U x * star (V x) * (‖Q x‖ ^ 2 : ℝ) := by
  simp only [partnerAnchorWeight, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem partnerAnchorWeight_norm_le_one {G : Type*} (U V Q : G → ℂ)
    (hU : ∀ x, ‖U x‖ ≤ 1) (hV : ∀ x, ‖V x‖ ≤ 1) (hQ : ∀ x, ‖Q x‖ ≤ 1) (x : G) :
    ‖partnerAnchorWeight U V Q x‖ ≤ 1 := by
  simp only [partnerAnchorWeight, norm_mul, norm_star]
  have hleft := (mul_le_of_le_one_left (norm_nonneg _) (hU x)).trans (hV x)
  have hright := (mul_le_of_le_one_left (norm_nonneg _) (hQ x)).trans (hQ x)
  exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hleft).trans
    hright

theorem exists_fixed_partner_anchor {G K : Type*} [AddCommGroup G] [Fintype G] [Fintype K]
    (H : Finset G) (hH : H.Nonempty) (U : G → K → G → ℂ) (Q R : K → G → ℂ)
    {delta : ℝ} (hdelta : 0 < delta)
    (hU : ∀ h ∈ H, ∀ k x, ‖U h k x‖ ≤ 1)
    (hQ : ∀ k x, ‖Q k x‖ ≤ 1) (hR : ∀ k x, ‖R k x‖ ≤ 1)
    (hcorr : ∀ h ∈ H, ∀ k, delta ≤ ‖𝔼 x, U h k x * Q k x * R k (x + h)‖) :
    ∃ h0 ∈ H, ∃ S ⊆ H, S.Nonempty ∧
      delta ^ (2 * Fintype.card K) / 2 * H.card ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k, delta ^ (2 * Fintype.card K) / 2 ≤
        ‖𝔼 x, partnerAnchorWeight (U h k) (U h0 k) (Q k) x * R k (x + h) * star (R k (x + h0))‖ := by
  let v : G → K → G → ℂ := fun h k x => U h k x * Q k x * R k (x + h)
  have hv : ∀ h ∈ H, ∀ k x, ‖v h k x‖ ≤ 1 := by
    intro h hh k x
    simp only [v, norm_mul]
    have hpair := (mul_le_of_le_one_left (norm_nonneg _) (hU h hh k x)).trans (hQ k x)
    exact (mul_le_of_le_one_left (norm_nonneg _) hpair).trans (hR k (x + h))
  obtain ⟨h0, hh0, S, hsub, hsize, hanchor⟩ := exists_common_anchor_on_finset H hH
    (fun _ : K => FiniteProbabilityWeights.uniform G) v hdelta hv
    (fun h hh k => by simpa only [FiniteProbabilityWeights.uniform_complexMean] using hcorr h hh k)
  have hpos : (0 : ℝ) < S.card := by
    have hHpos : (0 : ℝ) < H.card := by exact_mod_cast hH.card_pos
    exact (mul_pos (by positivity) hHpos).trans_le hsize
  refine ⟨h0, hh0, S, hsub, Finset.card_pos.mp (by exact_mod_cast hpos), hsize, ?_⟩
  intro h hh k
  have heq : (FiniteProbabilityWeights.uniform G).correlation (v h k) (v h0 k) =
      𝔼 x, partnerAnchorWeight (U h k) (U h0 k) (Q k) x * R k (x + h) * star (R k (x + h0)) := by
    rw [FiniteProbabilityWeights.uniform_correlation]
    apply Finset.expect_congr rfl
    intro x _
    simp only [v, partnerAnchorWeight, star_mul]
    ring
  rw [← heq]
  exact hanchor h hh k

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_fixed_partner_anchor_power {G K : Type*}
    [AddCommGroup G] [Fintype G] [Fintype K]
    (H : Finset G) (hH : H.Nonempty) (U : G → K → G → ℂ) (Q R : K → G → ℂ)
    {p : ℝ} (hp : 0 ≤ p) (hK : (Fintype.card K : ℝ) ≤ p)
    (hsize : Real.exp (-p) * Fintype.card G ≤ (H.card : ℝ))
    (hU : ∀ h ∈ H, ∀ k n, ‖U h k n‖ ≤ 1)
    (hQ : ∀ k n, ‖Q k n‖ ≤ 1) (hR : ∀ k n, ‖R k n‖ ≤ 1)
    (hcorr : ∀ h ∈ H, ∀ k, Real.exp (-p) ≤ ‖𝔼 n, U h k n * Q k n * R k (n + h)‖) :
    ∃ h₀ ∈ H, ∃ S ⊆ H, S.Nonempty ∧
      Real.exp (-(2 * p ^ 2 + p + 1)) * Fintype.card G ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k, Real.exp (-(2 * p ^ 2 + p + 1)) ≤
        ‖𝔼 n, partnerAnchorWeight (U h k) (U h₀ k) (Q k) n *
          R k (n + h) * star (R k (n + h₀))‖ := by
  obtain ⟨h₀, hh₀, S, hsub, hSn, hlarge, hanchor⟩ :=
    exists_fixed_partner_anchor H hH U Q R (Real.exp_pos _) hU hQ hR hcorr
  have hweight : Real.exp (-(2 * p ^ 2 + 1)) ≤ Real.exp (-p) ^ (2 * Fintype.card K) / 2 := by
    rw [← Real.exp_nat_mul]
    calc
      _ ≤ Real.exp (((2 * Fintype.card K : ℕ) : ℝ) * -p - 1) := by
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left hK hp]
      _ ≤ _ := exp_sub_one_le_half_exp _
  have hbias : Real.exp (-(2 * p ^ 2 + p + 1)) ≤ Real.exp (-p) ^ (2 * Fintype.card K) / 2 :=
    (Real.exp_le_exp.mpr (by linarith : -(2 * p ^ 2 + p + 1) ≤ -(2 * p ^ 2 + 1))).trans hweight
  refine ⟨h₀, hh₀, S, hsub, hSn, ?_, fun h hh k => hbias.trans (hanchor h hh k)⟩
  calc
    _ = Real.exp (-(2 * p ^ 2 + 1)) * (Real.exp (-p) * Fintype.card G) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-(2 * p ^ 2 + 1)) * H.card :=
      mul_le_mul_of_nonneg_left hsize (Real.exp_pos _).le
    _ ≤ (Real.exp (-p) ^ (2 * Fintype.card K) / 2) * H.card :=
      mul_le_mul_of_nonneg_right hweight (Nat.cast_nonneg _)
    _ ≤ S.card := hlarge

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_dense_correlation_pairs {I X : Type*} [Fintype I] [Nonempty I]
    [Fintype X] [Nonempty X] (B : X → ℂ) (v : I → X → ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hB : ∀ x, ‖B x‖ ≤ 1) (hv : ∀ i x, ‖v i x‖ ≤ 1)
    (hcorr : ∀ i, δ ≤ ‖𝔼 x, B x * v i x‖) :
    ∃ P : Finset (I × I), P.Nonempty ∧
      δ ^ 2 / 2 * (Fintype.card I : ℝ) ^ 2 ≤ (P.card : ℝ) ∧
      ∀ t ∈ P, δ ^ 2 / 2 ≤ ‖𝔼 x, v t.1 x * star (v t.2 x)‖ := by
  have hmean : δ ≤ 𝔼 i, ‖𝔼 x, B x * v i x‖ := by
    simpa only [Fintype.expect_const] using
      Finset.expect_le_expect (s := Finset.univ) (fun i _ => hcorr i)
  have hcs := finite_absolute_cauchy_schwarz B v hB
  have hcross : δ ^ 2 ≤ 𝔼 t : I × I, ‖𝔼 x, v t.1 x * star (v t.2 x)‖ := by
    have h := (pow_le_pow_left₀ hδ.le hmean 2).trans hcs
    simpa only [one_pow, one_mul, ← Finset.univ_product_univ, Finset.expect_product] using h
  have hunit (t : I × I) : ‖𝔼 x, v t.1 x * star (v t.2 x)‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply (Finset.expect_le_expect _).trans_eq (Fintype.expect_const _)
    intro x _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hv t.1 x)).trans (hv t.2 x)
  obtain ⟨P, hsize, hP⟩ := exists_dense_level_set
    (fun t : I × I => ‖𝔼 x, v t.1 x * star (v t.2 x)‖) (sq_nonneg δ) hunit hcross
  have hsize' : δ ^ 2 / 2 * (Fintype.card I : ℝ) ^ 2 ≤ (P.card : ℝ) := by
    simpa only [Fintype.card_prod, Nat.cast_mul, pow_two] using hsize
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hpos : 0 < (P.card : ℝ) := lt_of_lt_of_le (by positivity) hsize'
  exact ⟨P, Finset.card_pos.mp (by exact_mod_cast hpos), hsize', hP⟩

end Erdos3

end

end OAI
