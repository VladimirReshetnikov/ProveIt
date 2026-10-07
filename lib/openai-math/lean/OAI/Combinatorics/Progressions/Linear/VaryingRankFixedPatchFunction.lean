/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.NormalizedFixedPatchFunction

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace PolynomialPatch

def castRank {X : Type*} {s d e : ℕ} (P : PolynomialPatch X s d) (h : d = e) :
    PolynomialPatch X s e := h ▸ P

theorem castRank_value {X : Type*} {s d e : ℕ} (P : PolynomialPatch X s d)
    (h : d = e) (t : X → ℝ) : (P.castRank h).value t = P.value t := by
  subst e
  rfl

theorem castRank_kernel_lip {X : Type*} {s d e : ℕ} (P : PolynomialPatch X s d)
    (h : d = e) : (P.castRank h).kernel.lip = P.kernel.lip := by
  subst e
  rfl

def formAtWeight {X : Type*} {s d : ℕ} (P : PolynomialPatch X s d)
    (w : Fin d → ℕ) (h : P.weight = w) : PolynomialSlots X d w := h ▸ P.form

theorem formAtWeight_value {X : Type*} {s d : ℕ} (P : PolynomialPatch X s d)
    (w : Fin d → ℕ) (h : P.weight = w) (t : X → ℝ) :
    ((P.formAtWeight w h).slots t).patchValue P.kernel = P.value t := by
  subst w
  rfl

def rankWeightCode {X : Type*} {s d : ℕ} (P : PolynomialPatch X s d)
    (D : ℕ) (hd : d ≤ D) : Fin (D + 1) × (Fin D → Fin (s + 1)) :=
  (⟨d, Nat.lt_succ_of_le hd⟩, fun i =>
    if hi : i.val < d then ⟨P.weight ⟨i.val, hi⟩, Nat.lt_succ_of_le (P.weight_le _)⟩ else 0)

theorem rankWeightCode_eq {X : Type*} {s d e D : ℕ}
    (P : PolynomialPatch X s d) (Q : PolynomialPatch X s e)
    (hd : d ≤ D) (he : e ≤ D)
    (hc : P.rankWeightCode D hd = Q.rankWeightCode D he) :
    ∃ h : d = e, (P.castRank h).weight = Q.weight := by
  have hde : d = e := congrArg (fun c => c.1.val) hc
  subst e
  refine ⟨rfl, ?_⟩
  funext i
  have h := congrArg (fun c => (c.2 ⟨i.val, i.isLt.trans_le hd⟩).val) hc
  simpa only [rankWeightCode, dite_eq_left i.isLt, castRank] using h

end PolynomialPatch

theorem exists_patch_rank_weight_class {X H : Type*} [Fintype H]
    (outer : FiniteProbabilityWeights H) (productive : Finset H)
    {s D : ℕ} (d : H → ℕ) (P : ∀ h, PolynomialPatch X s (d h))
    (hd : ∀ h, d h ≤ D) (hproductive : 0 < outer.mass productive) :
    ∃ (h₀ : H) (retained : Finset H), h₀ ∈ retained ∧ retained ⊆ productive ∧
      outer.mass productive / ((D + 1 : ℕ) * (s + 1) ^ D : ℕ) ≤ outer.mass retained ∧
      ∀ h ∈ retained, ∃ heq : d h = d h₀, ((P h).castRank heq).weight = (P h₀).weight := by
  let code := fun h => (P h).rankWeightCode D (hd h)
  obtain ⟨c, hc⟩ := outer.exists_code_fiber_mass productive code
  let retained := productive.filter (fun h => code h = c)
  have hmass : outer.mass productive / ((D + 1 : ℕ) * (s + 1) ^ D : ℕ) ≤
      outer.mass retained := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] at hc
    convert hc using 1
    congr 1
    ext h
    simp only [retained, Finset.mem_filter]
  have hretained : 0 < outer.mass retained :=
    (div_pos hproductive (by positivity)).trans_le hmass
  have hnonempty : retained.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    simp only [hempty, FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hretained
  obtain ⟨h₀, hh₀⟩ := hnonempty
  refine ⟨h₀, retained, hh₀, Finset.filter_subset _ _, hmass, ?_⟩
  intro h hh
  apply PolynomialPatch.rankWeightCode_eq (P h) (P h₀) (hd h) (hd h₀)
  exact (Finset.mem_filter.mp hh).2.trans (Finset.mem_filter.mp hh₀).2.symm

theorem exists_common_rank_weight_patch_family {X H : Type*} [Fintype H]
    (outer : FiniteProbabilityWeights H) (productive : Finset H)
    {s D : ℕ} (d : H → ℕ) (P : ∀ h, PolynomialPatch X s (d h))
    (hd : ∀ h, d h ≤ D) (hproductive : 0 < outer.mass productive)
    (L : ℝ) (hL : ∀ h, ((P h).kernel.lip : ℝ) ≤ L) :
    ∃ (d₀ : ℕ) (w : Fin d₀ → ℕ) (A : H → PolynomialSlots X d₀ w)
      (Φ : H → PatchKernel d₀) (retained : Finset H),
      d₀ ≤ D ∧ Monotone w ∧ (∀ i, 1 ≤ w i) ∧ (∀ i, w i ≤ s) ∧
      retained ⊆ productive ∧
      outer.mass productive / ((D + 1 : ℕ) * (s + 1) ^ D : ℕ) ≤ outer.mass retained ∧
      (∀ h, ((Φ h).lip : ℝ) ≤ L) ∧
      (∀ h ∈ retained, (Φ h).lip = (P h).kernel.lip) ∧
      ∀ h ∈ retained, ∀ t : X → ℝ, ((A h).slots t).patchValue (Φ h) = (P h).value t := by
  obtain ⟨h₀, retained, hh₀, hsub, hmass, hshape⟩ :=
    exists_patch_rank_weight_class outer productive d P hd hproductive
  let chooseIndex := fun h => if h ∈ retained then h else h₀
  have hmem (h) : chooseIndex h ∈ retained := by
    dsimp only [chooseIndex]
    split_ifs with hh
    · exact hh
    · exact hh₀
  choose rankEq weightEq using fun h => hshape (chooseIndex h) (hmem h)
  let patch := fun h => (P (chooseIndex h)).castRank (rankEq h)
  let A := fun h => (patch h).formAtWeight (P h₀).weight (weightEq h)
  let Φ := fun h => (patch h).kernel
  have hchoose (h) (hh : h ∈ retained) : chooseIndex h = h := by
    exact ite_eq_left hh
  refine ⟨d h₀, (P h₀).weight, A, Φ, retained, hd h₀, (P h₀).weight_mono,
    (P h₀).weight_pos, (P h₀).weight_le, hsub, hmass, ?_, ?_, ?_⟩
  · intro h
    simpa only [Φ, patch, PolynomialPatch.castRank_kernel_lip] using hL (chooseIndex h)
  · intro h hh
    change ((P (chooseIndex h)).castRank (rankEq h)).kernel.lip = _
    rw [PolynomialPatch.castRank_kernel_lip]
    exact congrArg (fun a => (P a).kernel.lip) (hchoose h hh)
  · intro h hh t
    change (((patch h).formAtWeight _ (weightEq h)).slots t).patchValue (patch h).kernel = _
    rw [PolynomialPatch.formAtWeight_value]
    change ((P (chooseIndex h)).castRank (rankEq h)).value t = _
    rw [PolynomialPatch.castRank_value]
    exact congrArg (fun a => (P a).value t) (hchoose h hh)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical

theorem exists_varying_rank_fixed_patch_function (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {X H T : Type*}
      [Fintype X] [Fintype H] [Nonempty H] [Fintype T]
      (outer : FiniteProbabilityWeights H) (productive : Finset H)
      (d : H → ℕ) (patch : ∀ h, PolynomialPatch X s (d h)) (D : ℕ) (p : ℝ),
      (∀ h, d h ≤ D) → 0 < outer.mass productive →
      0 ≤ p → (D : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      (∀ h, ((patch h).kernel.lip : ℝ) ≤ Real.exp p) →
      ∀ (localLaw : H → FiniteProbabilityWeights T) (point : H → T → X → ℤ)
        (score : H → T → ℝ), (∀ h t, |score h t| ≤ 1) →
      (∀ h ∈ productive, Real.exp (-p) ≤ (localLaw h).mean
        (fun t => score h t * (patch h).value (fun i => (point h t i : ℝ)))) →
      ∃ (d₀ : ℕ) (w : Fin d₀ → ℕ) (hw : Monotone w) (Ψ : PatchKernel d₀)
        (B : PolynomialSlots X d₀ w) (localForm : H → PolynomialSlots X d₀ w)
        (retained : Finset H),
        d₀ ≤ D ∧ (∀ i, 1 ≤ w i) ∧ (∀ i, w i ≤ s) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((p + 2) ^ E) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ (p + 2) ^ E) ∧
        retained ⊆ productive ∧
        (outer.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((p + 2) ^ E)) ≤ outer.mass retained ∧
        ∀ h ∈ retained, Real.exp (-((p + 2) ^ E)) ≤ (localLaw h).mean
          (fun t => score h t *
            (B.shearTransformedSlots hw
              ((localForm h).loweringAt (fun i => (point h t i : ℝ)))).patchValue Ψ) := by
  obtain ⟨E, hE, hfixed⟩ := exists_unrestricted_fixed_weight_patch_function s
  refine ⟨E, hE, ?_⟩
  intro X H T _ _ _ _ outer productive d patch D p hd hproductive hp hD hX hLip
    localLaw point score hscore hpositive
  obtain ⟨d₀, w, A, Φ, middle, hd₀, hw, hpos, hws, hsub, hmass, hΦ, _, heval⟩ :=
    exists_common_rank_weight_patch_family outer productive d patch hd hproductive (Real.exp p) hLip
  have hmiddle (h) (hh : h ∈ middle) : Real.exp (-p) ≤ (localLaw h).mean (fun t =>
      score h t * ((A h).slots (fun i => (point h t i : ℝ))).patchValue (Φ h)) := by
    simp_rw [heval h hh]
    exact hpositive h (hsub hh)
  have hdreal : (d₀ : ℝ) ≤ p := (Nat.cast_le.mpr hd₀).trans hD
  obtain ⟨Ψ, B, localForm, retained, hΨ, hB, hretained, hmass', hlocal⟩ :=
    hfixed A Φ hw hpos hws p hp hdreal hX hΦ outer middle localLaw point score hscore hmiddle
  refine ⟨d₀, w, hw, Ψ, B, localForm, retained, hd₀, hpos, hws,
    hΨ, hB, hretained.trans hsub, ?_, hlocal⟩
  exact (mul_le_mul_of_nonneg_right hmass (Real.exp_nonneg _)).trans hmass'

end Erdos3

end

end OAI
