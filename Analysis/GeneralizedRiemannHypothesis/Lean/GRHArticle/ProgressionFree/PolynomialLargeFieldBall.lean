import GRHArticle.ProgressionFree.PolynomialWeightedCharging

/-!
# Density comparison on a single polynomial ball

Split an admissible set into preferred, nonpreferred, and deep degree
layers. Missing preferred polynomials pay for the nonexceptional charge.
The entire deep part, including zero, fits in a ball of size `q^(N-K)`.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Finset
open scoped Classical

variable {F : Type*} [Field F]

private theorem missingTarget_mem_deficit {E : Set F[X]} {C : Set ℕ} {N d : ℕ} {f p : F[X]}
    (hf : f ≠ 0) (hn : f.natDegree ≤ N) (hp : p ≠ 0) (hd : p.natDegree = d)
    (hs : PolynomialLayerStep C (N-f.natDegree) d) :
    polynomialMissingTarget E f p ∈ polynomialDeficitSet C N := by
  obtain ⟨_,h₂,ha,hb⟩ := hs
  unfold polynomialMissingTarget
  split_ifs
  · exact ⟨mul_ne_zero (mul_ne_zero hf hp) hp, by
      rw [natDegree_mul (mul_ne_zero hf hp) hp,natDegree_mul hf hp,hd]; omega, by
      simpa only [natDegree_mul (mul_ne_zero hf hp) hp,natDegree_mul hf hp,hd,
        show N-(f.natDegree+d+d) = N-f.natDegree-2*d by omega] using ha⟩
  · exact ⟨mul_ne_zero hf hp, by rw [natDegree_mul hf hp,hd]; omega, by
      simpa only [natDegree_mul hf hp,hd,
        show N-(f.natDegree+d) = N-f.natDegree-d by omega] using hb⟩

variable [Fintype F]

/-- Finite count in terms of the preferred layers, exceptional targets
by prime degree, and the exact size of the deep ball. The preferred
indices may form any progression-free set with the stated predecessors. -/
theorem card_polynomialBall_le_preferred_add_exceptional
    {E : Set F[X]} (hE : PolynomialRatioThreeGPFree E)
    {C : Set ℕ} (hC : ThreeAPFree C) (N K : ℕ)
    (I : Finset ℕ) (step : ℕ → ℕ) (S X : ℕ → Finset F[X]) (θ : ℕ → ℝ)
    (hstep : ∀ k ≤ K, k ∉ C → step k ∈ I ∧ PolynomialLayerStep C k (step k))
    (hθ : ∀ d ∈ I, 0 ≤ θ d) (hbudget : ∑ d ∈ I, θ d ≤ 1)
    (hS : ∀ d ∈ I, (S d).Nonempty ∧ ∀ p ∈ S d, p ≠ 0 ∧ p.natDegree = d)
    (hX : ∀ d ∈ I, ∀ g ∈ polynomialDeficitSet (F := F) C N, g ∉ X d →
      ((S d).filter (· ∣ g)).card ≤ θ d * (S d).card) :
    (((polynomialDegreeLTFinset F (N+1)).filter (· ∈ E)).card : ℝ) ≤
      ((polynomialDegreeLTFinset F (N+1)).filter (· ∈ polynomialDeficitSet C N)).card +
      (∑ d ∈ I, ((X d).card : ℝ)) + (Fintype.card F : ℝ)^(N-K) := by
  let ball := polynomialDegreeLTFinset F (N+1)
  let B := ball.filter (· ∈ E)
  let P := ball.filter (· ∈ polynomialDeficitSet C N)
  let A := B.filter (fun f ↦ f ≠ 0 ∧ N-f.natDegree ≤ K ∧ N-f.natDegree ∉ C)
  let G := P \ B
  let deep := polynomialDegreeLTFinset F (N-K)
  have hdeg {f : F[X]} (hf : f ∈ ball) (h0 : f ≠ 0) : f.natDegree ≤ N := by
    have h := mem_polynomialDegreeLTFinset.mp hf
    rwa [degree_eq_natDegree h0,Nat.cast_lt,Nat.lt_succ_iff] at h
  have hA (f : F[X]) (hf : f ∈ A) := mem_filter.mp hf
  have hG {g : F[X]} (hg : g ∈ G) : g ∈ polynomialDeficitSet C N :=
    (mem_filter.mp (mem_sdiff.mp hg).1).2
  have htarget {f : F[X]} (hf : f ∈ A) {p : F[X]} (hp : p ∈ S (step (N-f.natDegree))) :
      polynomialMissingTarget E f p ∈ G := by
    obtain ⟨hb,h₀,hk,hc⟩ := hA f hf
    obtain ⟨hi,hs⟩ := hstep _ hk hc
    obtain ⟨hp₀,hd⟩ := (hS _ hi).2 _ hp
    obtain ⟨hball,hmem⟩ := mem_filter.mp hb
    have ht := missingTarget_mem_deficit (E := E) h₀ (hdeg hball h₀) hp₀ hd hs
    have ht₀ := ht.1
    have htb : polynomialMissingTarget E f p ∈ ball := mem_polynomialDegreeLTFinset.mpr (by
      rw [degree_eq_natDegree ht₀,Nat.cast_lt]; exact Nat.lt_succ_of_le ht.2.1)
    exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨htb,ht⟩,fun hb ↦
      polynomialMissingTarget_notMem hE h₀ hmem (hd ▸ hs.1) (mem_filter.mp hb).2⟩
  have hcharge := card_polynomialSources_le_targets_add_exceptional (E := E) hC N A G I
    (fun f ↦ step (N-f.natDegree)) S X θ hθ hbudget (by
      intro f hf
      obtain ⟨hb,h₀,hk,hc⟩ := hA f hf
      exact ⟨h₀,hdeg (mem_filter.mp hb).1 h₀,hstep _ hk hc⟩)
    hS (fun _ hf _ hp ↦ htarget hf hp) (fun d hd g hg ↦ hX d hd g (hG hg))
  have hsub : B ⊆ ((P ∩ B) ∪ A) ∪ deep := by
    intro f hf
    have hfb := (mem_filter.mp hf).1
    by_cases hz : f = 0
    · apply mem_union_right
      apply mem_polynomialDegreeLTFinset.mpr
      simp [hz]
    have hn := hdeg hfb hz
    by_cases hc : N-f.natDegree ∈ C
    · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr
        ⟨mem_filter.mpr ⟨hfb,hz,hn,hc⟩,hf⟩))
    by_cases hk : N-f.natDegree ≤ K
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hf,hz,hk,hc⟩))
    · exact mem_union_right _ (mem_polynomialDegreeLTFinset.mpr (by
        rw [degree_eq_natDegree hz,Nat.cast_lt]; omega))
  have hcount : B.card ≤ (P ∩ B).card + A.card + deep.card :=
    (card_le_card hsub).trans ((card_union_le ..).trans (Nat.add_le_add_right (card_union_le ..) _))
  have hp : G.card + (P ∩ B).card = P.card := card_sdiff_add_card_inter P B
  have hcount' : (B.card : ℝ) ≤ (P ∩ B).card + (A.card : ℝ) + deep.card := by exact_mod_cast hcount
  have hp' : (G.card : ℝ) + (P ∩ B).card = P.card := by exact_mod_cast hp
  have hdeep : (deep.card : ℝ) = (Fintype.card F : ℝ)^(N-K) := by
    exact_mod_cast card_polynomialDegreeLTFinset (F := F) (N-K)
  change (B.card : ℝ) ≤ P.card + _ + _
  linarith only [hcharge,hp',hcount',hdeep]

end GRHArticle.ProgressionFree
