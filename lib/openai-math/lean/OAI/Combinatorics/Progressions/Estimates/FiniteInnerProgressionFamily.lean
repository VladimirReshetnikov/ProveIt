import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest
import OAI.Combinatorics.Progressions.Estimates.FiniteReciprocalTenthTail
import OAI.Combinatorics.Progressions.Lattices.CommonIntegerIntervalCorrelation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_finset_expect_le_one {X : Type*} (A : Finset X) (f : X → ℂ)
    (hf : ∀ x ∈ A, ‖f x‖ ≤ 1) : ‖𝔼 x ∈ A, f x‖ ≤ 1 := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  · exact (RCLike.norm_expect_le (K := ℂ)).trans (Finset.expect_le hA hf)

theorem norm_expect_subset_sub_le {X : Type*} [DecidableEq X]
    (A B : Finset X) (hA : A.Nonempty) (hAB : A ⊆ B)
    (f : X → ℂ) (hf : ∀ x ∈ B, ‖f x‖ ≤ 1) :
    ‖(𝔼 x ∈ A, f x) - 𝔼 x ∈ B, f x‖ ≤ 2 * (1 - (A.card : ℝ) / B.card) := by
  have hB : B.Nonempty := hA.mono hAB
  have hB0 : (B.card : ℂ) ≠ 0 := by exact_mod_cast hB.card_ne_zero
  have hBR : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hmean := norm_finset_expect_le_one A f (fun x hx => hf x (hAB hx))
  have hsum : (∑ x ∈ B \ A, f x) + ∑ x ∈ A, f x = ∑ x ∈ B, f x :=
    Finset.sum_sdiff hAB
  have hc : ((B \ A).card : ℂ) + (A.card : ℂ) = B.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hAB
  have heq : (𝔼 x ∈ A, f x) - 𝔼 x ∈ B, f x =
      (∑ x ∈ B \ A, ((𝔼 a ∈ A, f a) - f x)) / (B.card : ℂ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [sub_div, mul_div_assoc, Finset.expect_eq_sum_div_card B]
    have hAeq := Finset.card_mul_expect A f
    field_simp
    linear_combination hAeq + hsum - (𝔼 a ∈ A, f a) * hc
  have hnorm : ‖∑ x ∈ B \ A, ((𝔼 a ∈ A, f a) - f x)‖ ≤
      2 * ((B \ A).card : ℝ) := by
    calc
      _ ≤ ∑ x ∈ B \ A, ‖(𝔼 a ∈ A, f a) - f x‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ B \ A, (2 : ℝ) := Finset.sum_le_sum (fun x hx =>
        (norm_sub_le _ _).trans (by linarith [hf x (Finset.mem_sdiff.mp hx).1]))
      _ = _ := by simp [mul_comm]
  rw [heq, norm_div, Complex.norm_natCast]
  apply (div_le_div_of_nonneg_right hnorm hBR.le).trans_eq
  have hcR : ((B \ A).card : ℝ) + (A.card : ℝ) = B.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hAB
  field_simp
  nlinarith

theorem norm_expect_injective_sub_le {X Y : Type*} [DecidableEq Y]
    (A : Finset X) (B : Finset Y) (hA : A.Nonempty) (g : X → Y)
    (hg : Set.InjOn g A) (hB : ∀ x ∈ A, g x ∈ B)
    (f : Y → ℂ) (hf : ∀ y ∈ B, ‖f y‖ ≤ 1) :
    ‖(𝔼 x ∈ A, f (g x)) - 𝔼 y ∈ B, f y‖ ≤ 2 * (1 - (A.card : ℝ) / B.card) := by
  have h := norm_expect_subset_sub_le (A.image g) B (hA.image g)
    (Finset.image_subset_iff.mpr hB) f hf
  simpa only [Finset.expect_image hg, Finset.card_image_of_injOn hg] using h

namespace FiniteProbabilityWeights

theorem translated_subset_mixture_compare {X Y Z : Type*} [Fintype Z] [DecidableEq Y]
    (p : FiniteProbabilityWeights Z) (A : Finset X) (B : Finset Y) (hA : A.Nonempty)
    (g : Z → X → Y) (hg : ∀ z, Set.InjOn (g z) A)
    (hB : ∀ z x, x ∈ A → g z x ∈ B)
    (f : Y → ℂ) (hf : ∀ y ∈ B, ‖f y‖ ≤ 1) :
    ‖(𝔼 x ∈ A, p.complexMean (fun z => f (g z x))) - 𝔼 y ∈ B, f y‖ ≤
      2 * (1 - (A.card : ℝ) / B.card) := by
  rw [← p.complexMean_finset_expect]
  have hc : p.complexMean (fun _ => 𝔼 y ∈ B, f y) = 𝔼 y ∈ B, f y := by
    simp only [complexMean, ← Finset.sum_mul, ← Complex.ofReal_sum, p.total,
      Complex.ofReal_one, one_mul]
  rw [← hc]
  exact (p.norm_complexMean_sub_le _ _ (fun _ => 2 * (1 - (A.card : ℝ) / B.card))
    (fun z _ => norm_expect_injective_sub_le A B hA (g z) (hg z) (hB z) f hf)).trans_eq
    (p.mean_const _)

end FiniteProbabilityWeights
end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def finiteSitePreimage {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (A : Finset X) : Finset T := Finset.univ.filter (fun t => e t ∈ A)

theorem image_finiteSitePreimage {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (A : Finset X) (hA : A ⊆ Finset.univ.image e) :
    (finiteSitePreimage e A).image e = A := by
  ext x
  simp only [Finset.mem_image, finiteSitePreimage, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp (hA hx)
    exact ⟨t, hx, rfl⟩

theorem finiteSitePreimage_card {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (he : Function.Injective e) (A : Finset X)
    (hA : A ⊆ Finset.univ.image e) : (finiteSitePreimage e A).card = A.card := by
  have h := congrArg Finset.card (image_finiteSitePreimage e A hA)
  simpa only [Finset.card_image_of_injective _ he] using h

theorem finiteSitePreimage_subset {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (he : Function.Injective e) (A : Finset X) (S : Finset T)
    (hA : A ⊆ S.image e) : finiteSitePreimage e A ⊆ S := by
  intro t ht
  have het : e t ∈ A := (Finset.mem_filter.mp ht).2
  obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp (hA het)
  exact he hst ▸ hs

noncomputable def finiteSiteInnerFamily {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (D : Finset (Finset X)) : Finset (Finset T) :=
  (D.filter (fun A => A ⊆ Finset.univ.image e)).image (finiteSitePreimage e)

theorem finiteSiteInnerFamily_card {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (D : Finset (Finset X)) : (finiteSiteInnerFamily e D).card ≤ D.card :=
  Finset.card_image_le.trans (Finset.card_filter_le _ _)

theorem mem_finiteSiteInnerFamily {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (D : Finset (Finset X)) {A : Finset X}
    (hAD : A ∈ D) (hA : A ⊆ Finset.univ.image e) :
    finiteSitePreimage e A ∈ finiteSiteInnerFamily e D :=
  Finset.mem_image.mpr ⟨A, Finset.mem_filter.mpr ⟨hAD, hA⟩, rfl⟩

theorem finiteSiteInnerFamily_image_mem {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (D : Finset (Finset X)) {A : Finset T}
    (hA : A ∈ finiteSiteInnerFamily e D) : A.image e ∈ D := by
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
  rw [image_finiteSitePreimage e B (Finset.mem_filter.mp hB).2]
  exact (Finset.mem_filter.mp hB).1

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_finite_inner_interval_family {p : ℝ} (hp : 0 ≤ p) (N : ℕ) :
    ∃ C : Finset (Finset ℤ), (C.card : ℝ) ≤ Real.exp (4 * p + 18) ∧
      (∀ S ∈ C, ∃ a b : ℕ, S = Finset.Ico (a : ℤ) (b : ℤ)) ∧
      ∀ a len : ℕ, a + len ≤ N → 0 < len → Real.exp (-p) * N ≤ (len : ℝ) →
        ∃ S ∈ C, S.Nonempty ∧ S ⊆ Finset.Ico (a : ℤ) (a + len) ∧
          (len : ℝ) ≤ 2 * S.card ∧
          2 * (1 - (S.card : ℝ) / len) ≤ Real.exp (-p) := by
  classical
  by_cases hN : Real.exp (2 * p + 8) ≤ (N : ℝ)
  · obtain ⟨L, hL, hscale, hgrid⟩ := exists_exp_integer_grid_scale hp hN
    let C := (Finset.univ : Finset (Fin (N / L + 2) × Fin (N / L + 2))).image
      (fun c => Finset.Ico (L * c.1.val : ℤ) (L * c.2.val : ℤ))
    refine ⟨C, ?_, ?_, ?_⟩
    · have hc : C.card ≤ (N / L + 2) * (N / L + 2) :=
        (Finset.card_image_le).trans_eq (by simp)
      calc
        (C.card : ℝ) ≤ (N / L + 2 : ℕ) * (N / L + 2 : ℕ) := by exact_mod_cast hc
        _ ≤ Real.exp (2 * p + 5) * Real.exp (2 * p + 5) :=
          mul_le_mul hgrid hgrid (Nat.cast_nonneg _) (Real.exp_nonneg _)
        _ = Real.exp (4 * p + 10) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    · intro S hS
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hS
      exact ⟨L * c.1.val, L * c.2.val, by simp only [Nat.cast_mul]⟩
    · intro a len hend hlen hdense
      have hrho : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hsmall : 4 * (L : ℝ) ≤ Real.exp (-p) * len := by
        calc
          _ ≤ Real.exp (-(2 * p)) * N := hscale
          _ = Real.exp (-p) * (Real.exp (-p) * N) := by
            rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      have hsN : 4 * L ≤ len := by
        exact_mod_cast hsmall.trans (mul_le_of_le_one_left (Nat.cast_nonneg _) hrho)
      obtain ⟨hstart, hstop, hne, _, hhalf, hloss⟩ := integer_grid_interval_geometry a len hL hsN
      let S := Finset.Ico (integerGridStart a L : ℤ) (integerGridEnd (a + len) L : ℤ)
      have hcard : S.card = integerGridEnd (a + len) L - integerGridStart a L := by
        simp only [S, Int.card_Ico]
        rw [← Int.natCast_sub hne.le, Int.toNat_natCast]
      have hadiv : a / L ≤ N / L := Nat.div_le_div_right (by omega)
      have hbdiv : (a + len) / L ≤ N / L := Nat.div_le_div_right hend
      refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
      · exact Finset.mem_image.mpr
          ⟨(⟨a / L + 1, by omega⟩, ⟨(a + len) / L, by omega⟩), Finset.mem_univ _, by
            simp only [S, integerGridStart, integerGridEnd, Nat.cast_mul]⟩
      · apply Finset.card_pos.mp
        rw [hcard]
        exact Nat.sub_pos_of_lt hne
      · intro x hx
        simp only [S, Finset.mem_Ico] at hx ⊢
        constructor <;> omega
      · rw [hcard]
        exact_mod_cast hhalf
      · have hlossR : (len : ℝ) ≤ S.card + 2 * L := by rw [hcard]; exact_mod_cast hloss
        have hlenR : (0 : ℝ) < len := by exact_mod_cast hlen
        have he : 2 * (1 - (S.card : ℝ) / len) = 2 * ((len : ℝ) - S.card) / len := by
          field_simp
        rw [he]
        apply (div_le_iff₀ hlenR).mpr
        linarith
  · let C := (Finset.univ : Finset (Fin (N + 1) × Fin (N + 1))).image
      (fun c => Finset.Ico (c.1.val : ℤ) (c.2.val : ℤ))
    refine ⟨C, ?_, ?_, ?_⟩
    · have h1 : (1 : ℝ) ≤ Real.exp (2 * p + 8) := Real.one_le_exp (by positivity)
      have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have hNp : (N + 1 : ℕ) ≤ Real.exp (2 * p + 9) := by
        have hs : (N : ℝ) + 1 ≤ 2 * Real.exp (2 * p + 8) := by linarith
        calc
          ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by norm_cast
          _ ≤ 2 * Real.exp (2 * p + 8) := hs
          _ ≤ Real.exp 1 * Real.exp (2 * p + 8) :=
            mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
          _ = _ := by rw [← Real.exp_add]; congr 1; ring
      have hc : C.card ≤ (N + 1) * (N + 1) :=
        (Finset.card_image_le).trans_eq (by simp)
      calc
        (C.card : ℝ) ≤ (N + 1 : ℕ) * (N + 1 : ℕ) := by exact_mod_cast hc
        _ ≤ Real.exp (2 * p + 9) * Real.exp (2 * p + 9) :=
          mul_le_mul hNp hNp (Nat.cast_nonneg _) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    · intro S hS
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hS
      exact ⟨c.1.val, c.2.val, rfl⟩
    · intro a len hend hlen _
      have hcard : (Finset.Ico (a : ℤ) (a + len)).card = len := by simp
      refine ⟨Finset.Ico (a : ℤ) (a + len), ?_, ?_, Finset.Subset.refl _, ?_, ?_⟩
      · exact Finset.mem_image.mpr
          ⟨(⟨a, by omega⟩, ⟨a + len, by omega⟩), Finset.mem_univ _, by simp⟩
      · exact Finset.card_pos.mp (by simpa only [hcard] using hlen)
      · rw [hcard]
        nlinarith [Nat.cast_nonneg (α := ℝ) len]
      · rw [hcard, div_self (by exact_mod_cast hlen.ne' : (len : ℝ) ≠ 0)]
        simpa using Real.exp_nonneg (-p)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_finset_expect_sub_const_le {X : Type*} (S : Finset X) (hS : S.Nonempty)
    (f : X → ℂ) (c : ℂ) {ε : ℝ} (hf : ∀ x ∈ S, ‖f x-c‖ ≤ ε) :
    ‖(𝔼 x ∈ S, f x)-c‖ ≤ ε := by
  calc
    _ = ‖Finset.expect S (fun x => f x-c)‖ := by
      rw [Finset.expect_sub_distrib, Finset.expect_const hS]
    _ ≤ Finset.expect S (fun x => ‖f x-c‖) := RCLike.norm_expect_le (K := ℂ)
    _ ≤ ε := Finset.expect_le hS hf

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem piFinset_inner_card_loss {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} (A B : ∀ i, Finset (X i))
    (hB : ∀ i, (B i).Nonempty) (hsub : ∀ i, A i ⊆ B i) :
    1 - ((Fintype.piFinset A).card : ℝ) / (Fintype.piFinset B).card ≤
      ∑ i, (1 - ((A i).card : ℝ) / (B i).card) := by
  let r : I → ℝ := fun i => ((A i).card : ℝ) / (B i).card
  have hr (i : I) : r i ∈ Set.Icc (0 : ℝ) 1 := by
    have hpos : (0 : ℝ) < (B i).card := by exact_mod_cast (hB i).card_pos
    refine ⟨div_nonneg (Nat.cast_nonneg _) hpos.le, ?_⟩
    exact (div_le_one hpos).mpr (by exact_mod_cast Finset.card_le_card (hsub i))
  have hprod := one_sub_sum_le_positive_prod Finset.univ r (fun i => 1 - r i)
    (fun i _ => (hr i).1) (fun i _ => ⟨by linarith [(hr i).2], by linarith [(hr i).1]⟩)
    (fun i _ => by linarith)
  have he : ((Fintype.piFinset A).card : ℝ) / (Fintype.piFinset B).card = ∏ i, r i := by
    simp only [Fintype.card_piFinset, Nat.cast_prod, Finset.prod_div_distrib, r]
  rw [he]
  change 1 - ∏ i, r i ≤ ∑ i, (1 - r i)
  linarith

theorem piFinset_inner_normalized_loss {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} (A B : ∀ i, Finset (X i))
    (hB : ∀ i, (B i).Nonempty) (hsub : ∀ i, A i ⊆ B i) (ε : I → ℝ)
    (hloss : ∀ i, 2 * (1 - ((A i).card : ℝ) / (B i).card) ≤ ε i) :
    2 * (1 - ((Fintype.piFinset A).card : ℝ) / (Fintype.piFinset B).card) ≤ ∑ i, ε i := by
  calc
    _ ≤ 2 * ∑ i, (1 - ((A i).card : ℝ) / (B i).card) :=
      mul_le_mul_of_nonneg_left (piFinset_inner_card_loss A B hB hsub) (by norm_num)
    _ = ∑ i, 2 * (1 - ((A i).card : ℝ) / (B i).card) := Finset.mul_sum ..
    _ ≤ _ := Finset.sum_le_sum (fun i _ => hloss i)

end Erdos3

end

section

namespace Erdos3

theorem exists_finite_inner_progression_family {p : ℝ} (hp : 0 ≤ p) (N M : ℕ) :
    ∃ D : Finset (Finset ℤ), (D.card : ℝ) ≤ M ^ 2 * Real.exp (4 * p + 18) ∧
      (∀ A ∈ D, ∃ m r a b : ℕ, 0 < m ∧ m ≤ M ∧ r < M ∧
        A = (Finset.Ico (a : ℤ) (b : ℤ)).image (fun x => (r : ℤ) + m * x)) ∧
      ∀ a len m r : ℕ, a + len ≤ N → 0 < len → 0 < m → m ≤ M → r < M →
        Real.exp (-p) * N ≤ (len : ℝ) →
        ∃ A ∈ D, A.Nonempty ∧
          A ⊆ (Finset.Ico (a : ℤ) (a + len)).image (fun x => (r : ℤ) + m * x) ∧
          (len : ℝ) ≤ 2 * A.card ∧
          2 * (1 - (A.card : ℝ) / len) ≤ Real.exp (-p) := by
  classical
  obtain ⟨C, hcount, hshape, hcover⟩ := exists_finite_inner_interval_family hp N
  let D := (Finset.univ : Finset (Fin M × Fin M)).biUnion (fun c =>
    C.image (fun S => S.image (fun x => (c.2.val : ℤ) + (c.1.val + 1 : ℕ) * x)))
  have hcard : D.card ≤ M ^ 2 * C.card := by
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _c : Fin M × Fin M, C.card :=
        Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
      _ = _ := by simp [pow_two, mul_assoc]
  refine ⟨D, ?_, ?_, ?_⟩
  · exact (show (D.card : ℝ) ≤ M ^ 2 * C.card by exact_mod_cast hcard).trans
      (mul_le_mul_of_nonneg_left hcount (sq_nonneg _))
  · intro A hA
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hA
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨a, b, rfl⟩ := hshape S hS
    exact ⟨c.1.val + 1, c.2.val, a, b, by omega, by omega, c.2.isLt, rfl⟩
  · intro a len m r hend hlen hm hmM hr hdense
    obtain ⟨S, hS, hSn, hsub, hhalf, herr⟩ := hcover a len hend hlen hdense
    let g : ℤ → ℤ := fun x => (r : ℤ) + m * x
    have hg : Function.Injective g := by
      intro x y he
      exact mul_left_cancel₀ (by exact_mod_cast hm.ne' : (m : ℤ) ≠ 0) (add_left_cancel he)
    refine ⟨S.image g, ?_, hSn.image g, Finset.image_subset_image hsub, ?_, ?_⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨(⟨m - 1, by omega⟩, ⟨r, hr⟩), Finset.mem_univ _, ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨S, hS, by simp only [Nat.sub_add_cancel hm, g]⟩
    · simpa only [Finset.card_image_of_injective S hg] using hhalf
    · simpa only [Finset.card_image_of_injective S hg] using herr

end Erdos3

end

end OAI
