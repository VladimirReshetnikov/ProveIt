import GowersSzemeredi.Proofs16BohrSizeFactorization
import GowersSzemeredi.Proofs16ComplexProfileQuasirandom

/-! From split relations to a quasirandom bilinear Bohr variety: [49]
Claim 34 together with Appendix B, in `ℤ/N`.

The bipartite graph has vertices `x ∈ X = B(γ; a − c)` (mixed radii) and
`y ∈ Y`, with an edge when `x ∈ B(ℓ(y); b − c)`. Its degrees and codegrees
are mixed Bohr sets of concatenated tuples (`mixedBohr_sumElim`):
* `deg y = |B(γ ⊔ ℓ(y))|`;
* `codeg(y, y′) = |B(γ ⊔ ℓ(y) ⊔ ℓ(y′))|`.

Suppose that for all but `η|Y|` vertices `y` the relations of `γ ⊔ ℓ(y)`
split with a fixed `Λ` (Claim 34's hypothesis), and that for all but
`η|Y|²` pairs those of `γ ⊔ ℓ(y) ⊔ ℓ(y′)` split with `Λ × Λ`. Suppose also
that the relevant Bohr sets are weakly regular. Then:
* typical degrees are `≈ W|X|`, with `W = latticeWeightMixed b c R Λ`;
* typical codegrees are `≈ W²|X|`, because the pair weight factorizes
  (`latticeWeightMixed_sumElim_prod`).

One typical vertex bounds `‖W‖ ≤ 2` once `20εN ≤ |X|`. The complex-profile
lemma then makes the graph quasirandom (`split_profile_quasirandom`):
`boxSum (G − δ) ≤ 3(80εN/|X| + η)|X|²|Y|²` for a real `δ ∈ [0,1]`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- Concatenated mixed Bohr sets are intersections. -/
theorem mixedBohr_sumElim {N : Nat} [NeZero N] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (γ : ι → ZMod N) (ℓ : κ → ZMod N) (a : ι → Nat) (b : κ → Nat) (c : Nat) :
    mixedBohr (Sum.elim γ ℓ) (fun q => Sum.elim a b q - c) =
      mixedBohr γ (fun i => a i - c) ∩ mixedBohr ℓ (fun j => b j - c) := by
  ext x
  simp only [Finset.mem_inter, mem_mixedBohr, Sum.forall, Sum.elim_inl, Sum.elim_inr]

/-- **The pair lattice weight factorizes.** -/
theorem latticeWeightMixed_sumElim_prod {N : Nat} [NeZero N] {κ κ' : Type*} [Fintype κ]
    [Fintype κ'] (b : κ → Nat) (b' : κ' → Nat) (c R : Nat) (Λ : Set (κ → centeredBall N R))
    (Λ' : Set (κ' → centeredBall N R)) :
    latticeWeightMixed (Sum.elim b b') c R
        {μ | (fun j => μ (Sum.inl j)) ∈ Λ ∧ (fun j => μ (Sum.inr j)) ∈ Λ'} =
      latticeWeightMixed b c R Λ * latticeWeightMixed b' c R Λ' := by
  unfold latticeWeightMixed
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Finset.sum_nbij' (fun v => (fun i => v (Sum.inl i), fun j => v (Sum.inr j)))
    (fun p => Sum.elim p.1 p.2) (by simp) (by simp)
    (fun v _ => by funext q; cases q <;> rfl) (fun p _ => rfl) (fun v _ => ?_)
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Set.mem_setOf_eq]
  by_cases h1 : (fun j => v (Sum.inl j)) ∈ Λ <;>
    by_cases h2 : (fun j => v (Sum.inr j)) ∈ Λ' <;> simp [h1, h2] <;> ring

/-- The truncation error grows with the number of frequencies. -/
theorem truncation_error_mono {N : Nat} [NeZero N] {c R m m' : Nat} (h : m ≤ m') :
    (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ m - 1 ≤
      (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ m' - 1 := by
  have hb : (1 : Real) ≤ 1 + N / ((centeredBall N c).card * (R + 1 : Real)) := by
    have : (0 : Real) ≤ N / ((centeredBall N c).card * (R + 1 : Real)) := by positivity
    linarith
  linarith [pow_le_pow_right₀ hb h]

/-- The indicator degree of a vertex is the size of an intersection. -/
theorem sum_subtype_indicator {N : Nat} (S T : Finset (ZMod N)) :
    ∑ x : ↥S, (if (x : ZMod N) ∈ T then (1 : Real) else 0) = ((S ∩ T).card : Real) := by
  rw [Finset.sum_coe_sort S (fun x => if x ∈ T then (1 : Real) else 0), Finset.sum_boole,
    Finset.filter_mem_eq_inter]

/-- **Split relations make the bilinear Bohr variety quasirandom.** -/
theorem split_profile_quasirandom {N : Nat} [NeZero N] {ι κ Y : Type*} [Fintype ι]
    [Fintype κ] [Fintype Y] [DecidableEq Y]
    (γ : ι → ZMod N) (ℓ : Y → κ → ZMod N) (a : ι → Nat) (b : κ → Nat) {c R : Nat}
    (hca : ∀ i, c ≤ a i) (hcb : ∀ j, c ≤ b j) (ha : ∀ i, 2 * a i < N)
    (hb : ∀ j, 2 * b j < N) (hc : 2 * c < N) (Λ : Set (κ → centeredBall N R))
    {ε η : Real} (hε : 0 ≤ ε)
    (htrunc : (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^
      Fintype.card (ι ⊕ (κ ⊕ κ)) - 1 ≤ ε)
    (hband : ((mixedBohr γ (fun i => a i + c)).card : Real) ≤
      (mixedBohr γ (fun i => a i - c)).card + ε * N)
    (hsize : 20 * ε * N ≤ (mixedBohr γ (fun i => a i - c)).card)
    (Ybad : Finset Y) (hYbad : (Ybad.card : Real) ≤ η * Fintype.card Y) {y₀ : Y}
    (hy₀ : y₀ ∉ Ybad)
    (hsplit1 : ∀ y ∉ Ybad, ∀ (ν : ι → centeredBall N R) (μ : κ → centeredBall N R),
      (∑ i, (ν i : ZMod N) * γ i) + (∑ j, (μ j : ZMod N) * ℓ y j) = 0 ↔
        (∑ i, (ν i : ZMod N) * γ i = 0 ∧ μ ∈ Λ))
    (hband1 : ∀ y ∉ Ybad,
      ((mixedBohr (Sum.elim γ (ℓ y)) (fun q => Sum.elim a b q + c)).card : Real) ≤
        (mixedBohr (Sum.elim γ (ℓ y)) (fun q => Sum.elim a b q - c)).card + ε * N)
    (Pbad : Finset (Y × Y)) (hPbad : (Pbad.card : Real) ≤ η * (Fintype.card Y : Real) ^ 2)
    (hsplit2 : ∀ y y', (y, y') ∉ Pbad →
      ∀ (ν : ι → centeredBall N R) (μ : κ ⊕ κ → centeredBall N R),
        (∑ i, (ν i : ZMod N) * γ i) + (∑ j, (μ j : ZMod N) * Sum.elim (ℓ y) (ℓ y') j) = 0 ↔
          (∑ i, (ν i : ZMod N) * γ i = 0 ∧
            ((fun j => μ (Sum.inl j)) ∈ Λ ∧ (fun j => μ (Sum.inr j)) ∈ Λ)))
    (hband2 : ∀ y y', (y, y') ∉ Pbad →
      ((mixedBohr (Sum.elim γ (Sum.elim (ℓ y) (ℓ y')))
          (fun q => Sum.elim a (Sum.elim b b) q + c)).card : Real) ≤
        (mixedBohr (Sum.elim γ (Sum.elim (ℓ y) (ℓ y')))
          (fun q => Sum.elim a (Sum.elim b b) q - c)).card + ε * N) :
    ∃ δ : Real, 0 ≤ δ ∧ δ ≤ 1 ∧
      boxSum (fun (x : ↥(mixedBohr γ (fun i => a i - c))) (y : Y) =>
        (if (x : ZMod N) ∈ mixedBohr (ℓ y) (fun j => b j - c) then (1 : Real) else 0) - δ) ≤
      3 * (80 * ε * N / (mixedBohr γ (fun i => a i - c)).card + η) *
        ((mixedBohr γ (fun i => a i - c)).card : Real) ^ 2 * (Fintype.card Y : Real) ^ 2 := by
  set Xs := mixedBohr γ (fun i => a i - c) with hXs
  set W := latticeWeightMixed b c R Λ with hWdef
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hXpos : 0 < Xs.card := Finset.card_pos.mpr ⟨0, by
    rw [hXs, mem_mixedBohr]; intro i; simp [centeredAbs]⟩
  have hXR : (0 : Real) < Xs.card := by exact_mod_cast hXpos
  -- truncation budgets for the smaller tuples
  have htι : (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ Fintype.card ι - 1 ≤ ε :=
    (truncation_error_mono (by simp [Fintype.card_sum])).trans htrunc
  have htικ : (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^
      Fintype.card (ι ⊕ κ) - 1 ≤ ε :=
    (truncation_error_mono (by simp [Fintype.card_sum])).trans htrunc
  -- degrees
  have hdegeq : ∀ y, ∑ x : ↥Xs,
      (if (x : ZMod N) ∈ mixedBohr (ℓ y) (fun j => b j - c) then (1 : Real) else 0) =
      ((mixedBohr (Sum.elim γ (ℓ y)) (fun q => Sum.elim a b q - c)).card : Real) := by
    intro y
    rw [sum_subtype_indicator, mixedBohr_sumElim]
  have hdegW : ∀ y ∉ Ybad,
      ‖(((mixedBohr (Sum.elim γ (ℓ y)) (fun q => Sum.elim a b q - c)).card : Real) : ℂ) -
        W * (Xs.card : Real)‖ ≤ 2 * ε * N + ‖W‖ * (2 * ε * N) := by
    intro y hy
    have h := bohr_card_factor_of_split_mixed γ (ℓ y) a b hca hcb ha hb hc Λ (hsplit1 y hy)
      hband (hband1 y hy) htι htικ
    simpa [hXs] using h
  -- `‖W‖ ≤ 2`
  have hW2 : ‖W‖ ≤ 2 := by
    have h := hdegW y₀ hy₀
    have hdeg_le : ((mixedBohr (Sum.elim γ (ℓ y₀)) (fun q => Sum.elim a b q - c)).card : Real)
        ≤ Xs.card := by
      rw [mixedBohr_sumElim]
      exact_mod_cast Finset.card_le_card Finset.inter_subset_left
    have hlow : ‖W‖ * Xs.card ≤ Xs.card + (2 * ε * N + ‖W‖ * (2 * ε * N)) := by
      have htri := norm_sub_norm_le (W * (Xs.card : Real))
        (((mixedBohr (Sum.elim γ (ℓ y₀)) (fun q => Sum.elim a b q - c)).card : Real) : ℂ)
      rw [norm_sub_rev] at htri
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hXR.le,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at htri
      linarith
    have hεN : 0 ≤ ε * N := by positivity
    nlinarith
  -- codegrees
  have hcodegeq : ∀ y y', ∑ x : ↥Xs,
      (if (x : ZMod N) ∈ mixedBohr (ℓ y) (fun j => b j - c) then (1 : Real) else 0) *
        (if (x : ZMod N) ∈ mixedBohr (ℓ y') (fun j => b j - c) then (1 : Real) else 0) =
      ((mixedBohr (Sum.elim γ (Sum.elim (ℓ y) (ℓ y')))
          (fun q => Sum.elim a (Sum.elim b b) q - c)).card : Real) := by
    intro y y'
    have hinner : mixedBohr (Sum.elim (ℓ y) (ℓ y')) (fun q => Sum.elim b b q - c) =
        mixedBohr (ℓ y) (fun j => b j - c) ∩ mixedBohr (ℓ y') (fun j => b j - c) :=
      mixedBohr_sumElim (ℓ y) (ℓ y') b b c
    have hall := mixedBohr_sumElim γ (Sum.elim (ℓ y) (ℓ y')) a (Sum.elim b b) c
    rw [hall, hinner, ← sum_subtype_indicator]
    apply Finset.sum_congr rfl; intro x _
    by_cases h1 : (x : ZMod N) ∈ mixedBohr (ℓ y) (fun j => b j - c) <;>
      by_cases h2 : (x : ZMod N) ∈ mixedBohr (ℓ y') (fun j => b j - c) <;> simp [h1, h2]
  have hcodegW : ∀ y y', (y, y') ∉ Pbad →
      ‖(((mixedBohr (Sum.elim γ (Sum.elim (ℓ y) (ℓ y')))
          (fun q => Sum.elim a (Sum.elim b b) q - c)).card : Real) : ℂ) -
        W ^ 2 * (Xs.card : Real)‖ ≤ 2 * ε * N + ‖W ^ 2‖ * (2 * ε * N) := by
    intro y y' hp
    have h := bohr_card_factor_of_split_mixed γ (Sum.elim (ℓ y) (ℓ y')) a (Sum.elim b b)
      hca (fun q => by cases q with | inl j => exact hcb j | inr j => exact hcb j) ha
      (fun q => by cases q with | inl j => exact hb j | inr j => exact hb j) hc
      {μ | (fun j => μ (Sum.inl j)) ∈ Λ ∧ (fun j => μ (Sum.inr j)) ∈ Λ}
      (fun ν μ => hsplit2 y y' hp ν μ) hband (hband2 y y' hp) htι htrunc
    rw [latticeWeightMixed_sumElim_prod b b c R Λ Λ] at h
    rw [← hWdef, ← sq] at h
    simpa [hXs] using h
  -- the complex profile lemma with `E = 20εN`
  have hE0 : 0 ≤ 20 * ε * N := by positivity
  have hcardX : Fintype.card ↥Xs = Xs.card := Fintype.card_coe Xs
  obtain ⟨hδ0, hδ1, hbox⟩ := boxSum_le_of_complex_profile
    (G := fun (x : ↥Xs) (y : Y) =>
      if (x : ZMod N) ∈ mixedBohr (ℓ y) (fun j => b j - c) then (1 : Real) else 0)
    (fun x y => by split_ifs <;> norm_num)
    (fun x y => by split_ifs <;> norm_num)
    (by rw [hcardX]; exact hXpos) (W := W) (E := 20 * ε * N) (η := η) hE0
    (by rw [hcardX]; exact hsize) Ybad hYbad hy₀
    (fun y hy => by
      rw [hdegeq y, hcardX]
      refine (hdegW y hy).trans ?_
      have hεN : 0 ≤ ε * N := by positivity
      nlinarith [norm_nonneg W])
    Pbad hPbad
    (fun y y' hp => by
      rw [hcodegeq y y', hcardX]
      refine (hcodegW y y' hp).trans ?_
      rw [norm_pow]
      have hεN : 0 ≤ ε * N := by positivity
      have hW4 : ‖W‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg W]
      nlinarith)
  refine ⟨_, hδ0, hδ1, hbox.trans (le_of_eq ?_)⟩
  rw [hcardX]
  ring

end LeanProofs.GowersSzemeredi
