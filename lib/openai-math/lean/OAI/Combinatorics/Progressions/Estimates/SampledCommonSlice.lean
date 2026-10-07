/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import OAI.Combinatorics.Progressions.Estimates.CenteredFiniteSliceResidualEnvelope

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem sum_mass_choice_fibers {Ω C : Type*} [Fintype Ω] [Fintype C]
    (p : FiniteProbabilityWeights Ω) (G : Finset Ω) (code : Ω → C) :
    (∑ c, p.mass (G.filter (fun z => code z = c))) = p.mass G := by
  simp only [mass, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem exists_large_mass_choice_fiber {Ω C : Type*} [Fintype Ω] [Fintype C] [Nonempty C]
    (p : FiniteProbabilityWeights Ω) (G : Finset Ω) (code : Ω → C) :
    ∃ c, p.mass G / Fintype.card C ≤ p.mass (G.filter (fun z => code z = c)) := by
  have he : (𝔼 c, p.mass (G.filter (fun z => code z = c))) =
      p.mass G / Fintype.card C := by
    rw [Fintype.expect_eq_sum_div_card, p.sum_mass_choice_fibers]
  obtain ⟨c, _, hc⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty he.ge
  exact ⟨c, hc⟩

theorem mass_superlevel_ge {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (f : Ω → ℝ) {α ρ B : ℝ}
    (hρ : 0 ≤ ρ) (hB : 0 < B) (hcap : ∀ z, f z ≤ B) (hmean : α ≤ p.mean f) :
    (α - ρ) / B ≤ p.mass (Finset.univ.filter (fun z => ρ ≤ f z)) := by
  let G := Finset.univ.filter (fun z => ρ ≤ f z)
  have hpoint (z : Ω) : f z ≤ ρ + B * (if z ∈ G then 1 else 0) := by
    by_cases hz : ρ ≤ f z
    · simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and, hz, ite_true,
        mul_one] using (hcap z).trans (by linarith)
    · simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, hz, ite_false,
        mul_zero, add_zero]
      exact le_of_not_ge hz
  have h := p.mean_mono hpoint
  rw [p.mean_add, p.mean_const, p.mean_const_mul, p.mean_indicator] at h
  apply (div_le_iff₀ hB).mpr
  change α - ρ ≤ p.mass G * B
  nlinarith only [hmean, h]

theorem mass_mul_le_mean_of_lower_bound {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (G : Finset Ω) (f : Ω → ℝ) {a : ℝ}
    (hf : ∀ z, 0 ≤ f z) (hG : ∀ z ∈ G, a ≤ f z) :
    a * p.mass G ≤ p.mean f := by
  rw [← p.mean_indicator G, ← p.mean_const_mul]
  apply p.mean_mono
  intro z
  by_cases hz : z ∈ G
  · simpa only [hz, ite_true, mul_one] using hG z hz
  · simpa only [hz, ite_false, mul_zero] using hf z

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem exists_fixed_outer_cells {Ω K C : Type*}
    [Fintype Ω] [Fintype K] [Fintype C]
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (rel : Ω → K → C → Prop) {κ : ℝ} (hκ : 0 < κ)
    (hproductive : κ ≤ outer.mass productive)
    (hlocal : ∀ ω ∈ productive, ∀ k, ∃ c, rel ω k c) :
    ∃ (cell : K → C) (retained : Finset Ω),
      retained ⊆ productive ∧ retained.Nonempty ∧ 0 < outer.mass retained ∧
      κ / (Fintype.card C : ℝ) ^ Fintype.card K ≤ outer.mass retained ∧
      ∀ ω ∈ retained, ∀ k, rel ω k (cell k) := by
  have hproductivepos : 0 < outer.mass productive := hκ.trans_le hproductive
  have hnonempty : productive.Nonempty := by
    by_contra hn
    have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [hempty, mass, Finset.sum_empty, lt_self_iff_false] at hproductivepos
  obtain ⟨ω₀, hω₀⟩ := hnonempty
  choose choice hchoice using hlocal
  let code : Ω → K → C := fun ω =>
    if hω : ω ∈ productive then choice ω hω else choice ω₀ hω₀
  let : Nonempty (K → C) := ⟨choice ω₀ hω₀⟩
  obtain ⟨cell, hcell⟩ := outer.exists_large_mass_choice_fiber productive code
  let retained := productive.filter (fun ω => code ω = cell)
  have hsub : retained ⊆ productive := Finset.filter_subset _ _
  have hcard : (Fintype.card (K → C) : ℝ) = (Fintype.card C : ℝ) ^ Fintype.card K := by
    rw [Fintype.card_fun, Nat.cast_pow]
  have hden : 0 < (Fintype.card C : ℝ) ^ Fintype.card K := by
    rw [← hcard]
    exact Nat.cast_pos.mpr Fintype.card_pos
  have hlower : κ / (Fintype.card C : ℝ) ^ Fintype.card K ≤ outer.mass retained := by
    rw [hcard] at hcell
    have hh := (div_le_div_of_nonneg_right hproductive hden.le).trans hcell
    convert hh using 1; try rfl
    congr 1
    ext ω
    simp only [retained, Finset.mem_filter]
  have hpos : 0 < outer.mass retained := (div_pos hκ hden).trans_le hlower
  have hretained : retained.Nonempty := by
    by_contra hn
    have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [hempty, mass, Finset.sum_empty, lt_self_iff_false] at hpos
  refine ⟨cell, retained, hsub, hretained, hpos, hlower, ?_⟩
  intro ω hω k
  have he := (Finset.mem_filter.mp hω).2
  rw [← he]
  simpa only [code, dite_eq_left (hsub hω)] using hchoice ω (hsub hω) k

theorem exists_fixed_outer_cells_exp {Ω K C : Type*}
    [Fintype Ω] [Fintype K] [Fintype C]
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (rel : Ω → K → C → Prop) {κ B : ℝ} (hκ : 0 < κ)
    (hproductive : κ ≤ outer.mass productive)
    (hlocal : ∀ ω ∈ productive, ∀ k, ∃ c, rel ω k c)
    (hcount : (Fintype.card C : ℝ) ≤ Real.exp B) :
    ∃ (cell : K → C) (retained : Finset Ω),
      retained ⊆ productive ∧ retained.Nonempty ∧ 0 < outer.mass retained ∧
      κ * Real.exp (-(B * Fintype.card K)) ≤ outer.mass retained ∧
      ∀ ω ∈ retained, ∀ k, rel ω k (cell k) := by
  obtain ⟨cell, retained, hsub, hn, hpos, hlower, hrel⟩ :=
    outer.exists_fixed_outer_cells productive rel hκ hproductive hlocal
  let : Nonempty (K → C) := ⟨cell⟩
  have hden : 0 < (Fintype.card C : ℝ) ^ Fintype.card K := by
    have hh : (0 : ℝ) < Fintype.card (K → C) := Nat.cast_pos.mpr Fintype.card_pos
    simpa only [Fintype.card_fun, Nat.cast_pow] using hh
  have hpow : (Fintype.card C : ℝ) ^ Fintype.card K ≤ Real.exp (B * Fintype.card K) := by
    calc
      _ ≤ (Real.exp B) ^ Fintype.card K := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount _
      _ = _ := by rw [← Real.exp_nat_mul, mul_comm]
  refine ⟨cell, retained, hsub, hn, hpos, ?_, hrel⟩
  calc
    _ = κ / Real.exp (B * Fintype.card K) := by rw [Real.exp_neg, div_eq_mul_inv]
    _ ≤ κ / (Fintype.card C : ℝ) ^ Fintype.card K :=
      div_le_div_of_nonneg_left hκ.le hden hpow
    _ ≤ outer.mass retained := hlower

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def normalizedSupportedCubeSum {A : Type*} [AddCommGroup A]
    (j : ℕ) (Q : Finset A) (F : (Fin j → Bool) → A → ℂ) : ℂ :=
  supportedCubeSum j (Q : Set A) F / Nat.card (SupportedCube j (Q : Set A))

theorem normalizedSupportedCubeSum_self_re {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Fintype B] [DecidableEq B] {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (j : ℕ) (f : A → ℂ) :
    (normalizedSupportedCubeSum (j + 1) Q (fun _ => f)).re =
      finiteSupportGowersNorm (j + 1) Q f ^ (2 ^ (j + 1)) := by
  rw [finiteSupportGowersNorm_eq_restricted hφ, restrictedGowersNorm_imageExtension_pow hφ]
  exact Complex.div_natCast_re _ _

theorem sampled_normalized_cube_lower_bound {Ω A B : Type*} [Fintype Ω]
    [AddCommGroup A] [AddCommGroup B] [Fintype B] [DecidableEq B]
    {φ : A →+ B} {Q : Finset A} (hφ : ReflectsPairSums φ (Q : Set A))
    (p : FiniteProbabilityWeights Ω) (G : Finset Ω) (j : ℕ) (f : Ω → A → ℂ)
    {τ a : ℝ} (ha : 0 ≤ a) (hmass : τ ≤ p.mass G)
    (hdetect : ∀ z ∈ G, a ≤ finiteSupportGowersNorm (j + 1) Q (f z)) :
    τ * a ^ (2 ^ (j + 1)) ≤
      (p.complexMean (fun z => normalizedSupportedCubeSum (j + 1) Q (fun _ => f z))).re := by
  rw [p.complexMean_re]
  simp_rw [normalizedSupportedCubeSum_self_re hφ]
  have hn (z) : 0 ≤ finiteSupportGowersNorm (j + 1) Q (f z) := by
    rw [finiteSupportGowersNorm_eq_restricted hφ]
    exact restrictedGowersNorm_nonneg _ _ _
  have hg := p.mass_mul_le_mean_of_lower_bound G
    (fun z => finiteSupportGowersNorm (j + 1) Q (f z) ^ (2 ^ (j + 1)))
    (fun z => pow_nonneg (hn z) _) (fun z hz => pow_le_pow_left₀ ha (hdetect z hz) _)
  exact (mul_le_mul_of_nonneg_right hmass (pow_nonneg ha _)).trans (by simpa [mul_comm] using hg)

theorem exists_large_ambient_cube_of_sampled_norm {Ω A B X Y I : Type*}
    [Fintype Ω] [AddCommGroup A] [AddCommGroup B] [Fintype B] [DecidableEq B]
    [AddCommGroup X] [AddCommGroup Y] [Fintype Y] [DecidableEq Y] [Fintype I]
    {φ : A →+ B} {Q : Finset A} (hφ : ReflectsPairSums φ (Q : Set A))
    {ψ : X →+ Y} {U : Finset X} (hψ : ReflectsPairSums ψ (U : Set X))
    (p : FiniteProbabilityWeights Ω) (G : Finset Ω) (j : ℕ) (f : Ω → A → ℂ)
    (c : I → ℂ) (F : I → (Fin (j + 1) → Bool) → X → ℂ)
    {τ a ε M : ℝ} (ha : 0 ≤ a) (hmass : τ ≤ p.mass G)
    (hdetect : ∀ z ∈ G, a ≤ finiteSupportGowersNorm (j + 1) Q (f z))
    (hM : 0 < M) (hc : (∑ i, ‖c i‖) ≤ M)
    (hpositive : ε < τ * a ^ (2 ^ (j + 1)))
    (hcompare : ‖p.complexMean (fun z => normalizedSupportedCubeSum (j + 1) Q (fun _ => f z)) -
      ∑ i, c i * normalizedSupportedCubeSum (j + 1) U (F i)‖ ≤ ε) :
    ∃ i, (τ * a ^ (2 ^ (j + 1)) - ε) / M ≤
      ‖normalizedSupportedCubeSum (j + 1) U (F i)‖ ∧
      (τ * a ^ (2 ^ (j + 1)) - ε) / M ≤
        ∏ ω, finiteSupportGowersNorm (j + 1) U (F i ω) := by
  have hlower := sampled_normalized_cube_lower_bound hφ p G j f ha hmass hdetect
  have hs : τ * a ^ (2 ^ (j + 1)) - ε ≤
      ‖∑ i, c i * normalizedSupportedCubeSum (j + 1) U (F i)‖ := by
    have hreal := Complex.re_le_norm
      (p.complexMean (fun z => normalizedSupportedCubeSum (j + 1) Q (fun _ => f z)))
    have hnorm := norm_sub_norm_le
      (p.complexMean (fun z => normalizedSupportedCubeSum (j + 1) Q (fun _ => f z)))
      (∑ i, c i * normalizedSupportedCubeSum (j + 1) U (F i))
    linarith
  obtain ⟨i, hi⟩ := exists_large_weighted_term c
    (fun i => normalizedSupportedCubeSum (j + 1) U (F i)) (sub_pos.mpr hpositive) hM hc hs
  refine ⟨i, hi, hi.trans ?_⟩
  simpa only [normalizedSupportedCubeSum, norm_div, Complex.norm_natCast] using
    norm_supportedCubeSum_le_of_embedding hψ j (F i)

end Erdos3

end

section

namespace Erdos3

theorem normalizedSupportedCubeSum_finiteSiteExtension
    {T A : Type*} [Nonempty T] [AddCommGroup A]
    (j : ℕ) (Q : Finset A) (e : T → A) (he : Function.Injective e)
    (hcover : ∀ x ∈ Q, ∃ t, e t = x) (f : A → ℂ) :
    normalizedSupportedCubeSum j Q
        (fun _ x => finiteSiteExtension e (fun t => f (e t)) x) =
      normalizedSupportedCubeSum j Q (fun _ => f) := by
  unfold normalizedSupportedCubeSum
  congr 1
  apply supportedCubeSum_congr_on
  intro ω x hx
  obtain ⟨t, rfl⟩ := hcover x hx
  exact finiteSiteExtension_apply e he (fun t => f (e t)) t

end Erdos3

end

section

namespace Erdos3

theorem normalizedSupportedCubeSum_finiteSiteExtension_on_map
    {T A Y : Type*} [Nonempty T] [AddCommGroup A]
    (j : ℕ) (Q : Finset A) (e : T → Y) (he : Function.Injective e)
    (φ : A → Y) (hcover : ∀ x ∈ Q, ∃ t, e t = φ x) (f : Y → ℂ) :
    normalizedSupportedCubeSum j Q
        (fun _ x => finiteSiteExtension e (fun t => f (e t)) (φ x)) =
      normalizedSupportedCubeSum j Q (fun _ x => f (φ x)) := by
  unfold normalizedSupportedCubeSum
  congr 1
  apply supportedCubeSum_congr_on
  intro ω x hx
  obtain ⟨t, ht⟩ := hcover x hx
  rw [← ht]
  exact finiteSiteExtension_apply e he (fun t => f (e t)) t

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_common_inner_sampled_slice {Ω T X : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype T] [Nonempty T]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ) {K : ℝ}
    (hS : ∀ z j, (S z j).Nonempty) (hsize : ∀ z j, (Fintype.card T : ℝ) / (S z j).card ≤ K)
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1)
    (C : Finset (Finset T)) {α ε η ρ : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ)
    (hlarge : ε + η + ρ < α)
    (hcover : ∀ z j, ∃ A ∈ C, A.Nonempty ∧ A ⊆ S z j ∧
      2 * (1 - (A.card : ℝ) / (S z j).card) ≤ η)
    (hmean : α ≤ sampledSliceSeminorm p F S w v) :
    ∃ A ∈ C, A.Nonempty ∧ ∃ G : Finset Ω, ∃ j : ∀ z, J z,
      (α - ε - η - ρ) / C.card ≤ p.mass G ∧
      ∀ z ∈ G, A ⊆ S z (j z) ∧
        2 * (1 - (A.card : ℝ) / (S z (j z)).card) ≤ η ∧
        ρ ≤ ‖𝔼 t ∈ A, v (F z t) * w z (j z) t‖ := by
  obtain ⟨j, hj⟩ := exists_nearly_maximizing_sampled_slice_tests p F S w hS hsize hw v hε
  choose A hAC hAn hAS hAerr using fun z => hcover z (j z)
  let code : Ω → C := fun z => ⟨A z, hAC z⟩
  let _ : Nonempty C := ⟨code (Classical.arbitrary Ω)⟩
  let f : Ω → ℝ := fun z => ‖𝔼 t ∈ A z, v (F z t) * w z (j z) t‖
  have hunit (z : Ω) (t : T) : ‖v (F z t) * w z (j z) t‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hv _)).trans (hw _ _ _)
  have happrox (z : Ω) : ‖𝔼 t ∈ S z (j z), v (F z t) * w z (j z) t‖ ≤ f z + η := by
    have he := (norm_expect_subset_sub_le (A z) (S z (j z)) (hAn z) (hAS z)
      (fun t => v (F z t) * w z (j z) t) (fun t _ => hunit z t)).trans (hAerr z)
    have ht := norm_sub_norm_le (𝔼 t ∈ S z (j z), v (F z t) * w z (j z) t)
      (𝔼 t ∈ A z, v (F z t) * w z (j z) t)
    rw [norm_sub_rev] at he
    dsimp [f]
    linarith
  have hm : α - ε - η ≤ p.mean f := by
    have hm' := p.mean_mono happrox
    rw [p.mean_add, p.mean_const] at hm'
    linarith
  let G := Finset.univ.filter (fun z => ρ ≤ f z)
  have hG : α - ε - η - ρ ≤ p.mass G := by
    simpa only [div_one] using p.mass_superlevel_ge f hρ zero_lt_one
      (fun z => norm_finset_expect_le_one _ _ (fun t _ => hunit z t)) hm
  obtain ⟨c, hc⟩ := p.exists_large_mass_choice_fiber G code
  let H := G.filter (fun z => code z = c)
  have hmass : (α - ε - η - ρ) / C.card ≤ p.mass H := by
    convert (div_le_div_of_nonneg_right hG (Nat.cast_nonneg (Fintype.card C))).trans hc using 1
    all_goals first | rfl | simp only [H, Fintype.card_coe]
    unfold FiniteProbabilityWeights.mass
    apply Finset.sum_congr
    · ext z
      simp only [Finset.mem_filter]
    · intro z _
      rfl
  have hHpos : 0 < p.mass H := lt_of_lt_of_le
    (div_pos (by linarith) (by exact_mod_cast C.card_pos.mpr ⟨c.val, c.property⟩)) hmass
  have hH : H.Nonempty := by
    by_contra h
    have he : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hHpos
    exact lt_irrefl _ hHpos
  have hcode (z : Ω) (hz : z ∈ H) : A z = c.val :=
    congrArg Subtype.val (Finset.mem_filter.mp hz).2
  obtain ⟨z₀, hz₀⟩ := hH
  refine ⟨c.val, c.property, ?_, H, j, hmass, ?_⟩
  · rw [← hcode z₀ hz₀]
    exact hAn z₀
  · intro z hz
    rw [← hcode z hz]
    exact ⟨hAS z, hAerr z, (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2⟩

end Erdos3

end

end OAI
