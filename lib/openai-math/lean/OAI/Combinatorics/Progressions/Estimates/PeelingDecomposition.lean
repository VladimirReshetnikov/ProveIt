import OAI.Combinatorics.Progressions.Estimates.FlatWeightedComparison

namespace OAI


namespace Erdos3

open scoped BigOperators

theorem abs_expect_le_of_bound {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f : ι → ℝ) {epsilon : ℝ} (hf : ∀ x ∈ S, |f x| ≤ epsilon) :
    |𝔼 x ∈ S, f x| ≤ epsilon := by
  have h := RCLike.norm_expect_le (K := ℝ) (s := S) (f := f)
  calc
    _ ≤ 𝔼 x ∈ S, |f x| := by simpa only [Real.norm_eq_abs] using h
    _ ≤ 𝔼 _x ∈ S, epsilon := Finset.expect_le_expect hf
    _ = epsilon := Finset.expect_const hS epsilon

theorem abs_expect_sub_expect_le {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f g : ι → ℝ) {epsilon : ℝ} (hfg : ∀ x ∈ S, |f x - g x| ≤ epsilon) :
    |(𝔼 x ∈ S, f x) - 𝔼 x ∈ S, g x| ≤ epsilon := by
  rw [← Finset.expect_sub_distrib]
  exact abs_expect_le_of_bound S hS _ hfg

theorem abs_weighted_expect_sub_le {ι : Type*} (S : Finset ι)
    (u f g : ι → ℝ) (hu : ∀ x ∈ S, 0 ≤ u x) {epsilon : ℝ}
    (hfg : ∀ x ∈ S, |f x - g x| ≤ epsilon) :
    |(𝔼 x ∈ S, u x * f x) - 𝔼 x ∈ S, u x * g x| ≤ epsilon * (𝔼 x ∈ S, u x) := by
  rw [← Finset.expect_sub_distrib]
  have h := RCLike.norm_expect_le (K := ℝ) (s := S) (f := fun x => u x * f x - u x * g x)
  calc
    _ ≤ 𝔼 x ∈ S, |u x * f x - u x * g x| := by simpa only [Real.norm_eq_abs] using h
    _ ≤ 𝔼 x ∈ S, epsilon * u x := by
      apply Finset.expect_le_expect
      intro x hx
      rw [← mul_sub, abs_mul, abs_of_nonneg (hu x hx)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hfg x hx) (hu x hx)
    _ = _ := (Finset.mul_expect S u epsilon).symm

end Erdos3


namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

def remainder (C : Finset G) (f : G → ℝ) (x : G) : ℝ := if x ∈ C then 0 else f x

def slice (C : Finset G) (f : G → ℝ) (x : G) : ℝ := if x ∈ C then f x else 0

noncomputable def positiveSupport (f : G → ℝ) : Finset G := Finset.univ.filter (fun x => 0 < f x)

omit [Fintype G] in
theorem remainder_nonneg (C : Finset G) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (x : G) :
    0 ≤ remainder C f x := by
  by_cases hx : x ∈ C <;> simp [remainder, hx, hf x]

omit [Fintype G] in
theorem remainder_le (C : Finset G) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (x : G) :
    remainder C f x ≤ f x := by
  by_cases hx : x ∈ C <;> simp [remainder, hx, hf x]

omit [Fintype G] in
theorem remainder_supported (B C : Finset G) (f : G → ℝ)
    (hf : ∀ x, x ∉ B → f x = 0) : ∀ x, x ∉ B → remainder C f x = 0 := by
  intro x hx
  simp [remainder, hf x hx]

omit [Fintype G] in
theorem remainder_add_slice (C : Finset G) (f : G → ℝ) (x : G) :
    remainder C f x + slice C f x = f x := by
  by_cases hx : x ∈ C <;> simp [remainder, slice, hx]

theorem sum_slice (C : Finset G) (f : G → ℝ) : (∑ x, slice C f x) = ∑ x ∈ C, f x := by
  simp [slice]

theorem sum_remainder_add (C : Finset G) (f : G → ℝ) :
    (∑ x, remainder C f x) + ∑ x ∈ C, f x = ∑ x, f x := by
  rw [← sum_slice C f, ← Finset.sum_add_distrib]
  simp only [remainder_add_slice]

omit [DecidableEq G] in
theorem expect_eq_total_div (B : Finset G) (f : G → ℝ)
    (hf : ∀ x, x ∉ B → f x = 0) : (𝔼 x ∈ B, f x) = (∑ x, f x) / B.card := by
  rw [Finset.expect_eq_sum_div_card]
  congr 1
  exact Finset.sum_subset (Finset.subset_univ B) (fun x _ hx => hf x hx)

theorem expect_remainder (B C : Finset G) (f : G → ℝ)
    (hf : ∀ x, x ∉ B → f x = 0) :
    (𝔼 x ∈ B, remainder C f x) =
      (𝔼 x ∈ B, f x) - (C.card : ℝ) / B.card * (𝔼 x ∈ C, f x) := by
  have hsum := sum_remainder_add C f
  have hC : (C.card : ℝ) * (𝔼 x ∈ C, f x) = ∑ x ∈ C, f x := Finset.card_mul_expect C f
  rw [expect_eq_total_div B (remainder C f) (remainder_supported B C f hf), expect_eq_total_div B f hf]
  have hrem : (∑ x, remainder C f x) = (∑ x, f x) - ∑ x ∈ C, f x := by linarith
  rw [hrem, ← hC]
  ring

theorem positiveSupport_remainder_subset (C : Finset G) (f : G → ℝ) :
    positiveSupport (remainder C f) ⊆ positiveSupport f := by
  intro x hx
  have hpos : 0 < remainder C f x := (Finset.mem_filter.mp hx).2
  by_cases hxC : x ∈ C
  · simp [remainder, hxC] at hpos
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [remainder, hxC] using hpos⟩

theorem positiveSupport_remainder_card_lt (C : Finset G) (f : G → ℝ)
    (hmean : 0 < 𝔼 x ∈ C, f x) :
    (positiveSupport (remainder C f)).card < (positiveSupport f).card := by
  have hC : C.Nonempty := by
    by_contra h
    have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he] at hmean
  obtain ⟨x, hx, hfx⟩ := Finset.exists_lt_of_lt_expect hC hmean
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨positiveSupport_remainder_subset C f, ?_⟩
  intro heq
  have hmem : x ∈ positiveSupport f := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfx⟩
  rw [← heq] at hmem
  have hpos : 0 < remainder C f x := (Finset.mem_filter.mp hmem).2
  simp only [remainder, hx, ite_true, lt_self_iff_false] at hpos

end Erdos3.Peeling


namespace Erdos3

open scoped BigOperators

namespace Peeling

theorem expect_slice_scale {G : Type*} [Fintype G] [DecidableEq G]
    (B D : Finset G) (f : G → ℝ) (hf : ∀ x, x ∉ B → f x = 0) :
    (𝔼 x ∈ B, slice D f x) = (D.card : ℝ) / B.card * (𝔼 x ∈ D, f x) := by
  have hs : ∀ x, x ∉ B → slice D f x = 0 := by
    intro x hx
    simp [slice, hf x hx]
  rw [expect_eq_total_div B (slice D f) hs, sum_slice, ← Finset.card_mul_expect D f]
  ring

end Peeling

namespace CellRefinement

variable {G : Type*} [AddCommGroup G]

noncomputable def bilinearIntegral (A B : Finset G) (a f g : G → ℝ) : ℝ :=
  𝔼 x ∈ A, 𝔼 y ∈ B, f x * g y * a (x + y)

theorem bilinearIntegral_swap (A B : Finset G) (a f g : G → ℝ) :
    bilinearIntegral A B a f g = bilinearIntegral B A a g f := by
  unfold bilinearIntegral
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro y _
  apply Finset.expect_congr rfl
  intro x _
  rw [add_comm x y, mul_comm (f x) (g y)]

theorem bilinearIntegral_le (A B : Finset G) (a f g : G → ℝ) {M : ℝ}
    (ha : ∀ x, a x ≤ M) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    bilinearIntegral A B a f g ≤ M * (𝔼 x ∈ A, f x) * (𝔼 y ∈ B, g y) := by
  calc
    _ ≤ 𝔼 x ∈ A, 𝔼 y ∈ B, f x * g y * M := by
      apply Finset.expect_le_expect
      intro x _
      apply Finset.expect_le_expect
      intro y _
      exact mul_le_mul_of_nonneg_left (ha _) (mul_nonneg (hf x) (hg y))
    _ = _ := by
      simp_rw [← Finset.expect_mul]
      rw [← Finset.expect_mul_expect]
      ring

variable [Fintype G] [DecidableEq G]

omit [Fintype G] in
theorem bilinearIntegral_peeling (A B D : Finset G) (a f g : G → ℝ) :
    bilinearIntegral A B a f g =
      bilinearIntegral A B a (Peeling.remainder D f) g +
        bilinearIntegral A B a (Peeling.slice D f) g := by
  unfold bilinearIntegral
  rw [← Finset.expect_add_distrib]
  apply Finset.expect_congr rfl
  intro x _
  rw [← Finset.expect_add_distrib]
  apply Finset.expect_congr rfl
  intro y _
  rw [← add_mul, ← add_mul, Peeling.remainder_add_slice]

theorem bilinearIntegral_slice_scale (A B D : Finset G) (a f g : G → ℝ)
    (hf : ∀ x, x ∉ A → f x = 0) :
    bilinearIntegral A B a (Peeling.slice D f) g =
      (D.card : ℝ) / A.card * bilinearIntegral D B a f g := by
  have hs : ∀ x, x ∉ A → (𝔼 y ∈ B, f x * g y * a (x + y)) = 0 := by
    intro x hx
    simp [hf x hx]
  have hpoint (x : G) :
      (𝔼 y ∈ B, Peeling.slice D f x * g y * a (x + y)) =
        Peeling.slice D (fun x => 𝔼 y ∈ B, f x * g y * a (x + y)) x := by
    by_cases hx : x ∈ D <;> simp [Peeling.slice, hx]
  unfold bilinearIntegral
  simp_rw [hpoint]
  exact Peeling.expect_slice_scale A D _ hs

end CellRefinement
end Erdos3


namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem convolution_nonneg (L : Finset G) (f g : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (t : G) :
    0 ≤ convolution L f g t :=
  div_nonneg (Finset.sum_nonneg (fun x _ => mul_nonneg (hf x) (hg (t - x)))) (Nat.cast_nonneg _)

theorem convolution_le_of_mass (L : Finset G) (f g : G → ℝ) {M : ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ M)
    (hmass : (∑ x, f x) / (L.card : ℝ) = 1) (t : G) : convolution L f g t ≤ M := by
  unfold convolution
  calc
    _ ≤ (∑ x, f x * M) / (L.card : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hg (t - x)) (hf x))
    _ = ((∑ x, f x) / (L.card : ℝ)) * M := by rw [← Finset.sum_mul]; ring
    _ = M := by rw [hmass, one_mul]

omit [AddCommGroup G] in
theorem normalized_mass_one (L : Finset G) (f : G → ℝ)
    (hsupport : ∀ x, x ∉ L → f x = 0) {u : ℝ} (hu : 0 < u)
    (hmean : (𝔼 x ∈ L, f x) = u) : (∑ x, f x / u) / (L.card : ℝ) = 1 := by
  have hmass : (∑ x, f x) / (L.card : ℝ) = u := by
    rw [← Peeling.expect_eq_total_div L f hsupport]
    exact hmean
  rw [← Finset.sum_div]
  calc
    _ = ((∑ x, f x) / (L.card : ℝ)) / u := by ring
    _ = 1 := by rw [hmass, div_self hu.ne']

end Erdos3.LocalConvolution


namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

inductive Chain (B : Finset G) (Admissible : Finset G → Prop) (K kappa : ℝ) :
    (G → ℝ) → (G → ℝ) → List (Finset G) → Prop
  | nil (f : G → ℝ) : Chain B Admissible K kappa f f []
  | step {f g : G → ℝ} {cs : List (Finset G)} (C : Finset G)
      (active : kappa ≤ 𝔼 x ∈ B, f x)
      (admissible : Admissible C)
      (concentrated : K * (𝔼 x ∈ B, f x) < 𝔼 x ∈ C, f x)
      (tail : Chain B Admissible K kappa (remainder C f) g cs) :
      Chain B Admissible K kappa f g (C :: cs)

namespace Chain

variable {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
  {f g : G → ℝ} {cs : List (Finset G)}

omit [Fintype G] in
theorem bounds (h : Chain B Admissible K kappa f g cs) :
    (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ g x ∧ g x ≤ f x := by
  induction h with
  | nil f => intro hf x; exact ⟨hf x, le_rfl⟩
  | @step f g cs C _ _ _ _ ih =>
    intro hf x
    obtain ⟨hg, hgf⟩ := ih (remainder_nonneg C f hf) x
    exact ⟨hg, hgf.trans (remainder_le C f hf x)⟩

omit [Fintype G] in
theorem supported (h : Chain B Admissible K kappa f g cs)
    (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ B → f x = 0) :
    ∀ x, x ∉ B → g x = 0 := by
  intro x hx
  have hb := h.bounds hf x
  have hz := hsupport x hx
  linarith

omit [Fintype G] in
theorem admissible_mem (h : Chain B Admissible K kappa f g cs) : ∀ C ∈ cs, Admissible C := by
  induction h with
  | nil f => simp
  | step C _ hC _ _ ih =>
    intro D hD
    rcases List.mem_cons.mp hD with rfl | hD
    · exact hC
    · exact ih D hD

omit [Fintype G] in
theorem final_eq_foldl (h : Chain B Admissible K kappa f g cs) :
    g = cs.foldl (fun u C => remainder C u) f := by
  induction h with
  | nil f => rfl
  | step C _ _ _ _ ih => simpa only [List.foldl_cons] using ih

theorem length_le_support (h : Chain B Admissible K kappa f g cs)
    (hK : 0 < K) (hkappa : 0 < kappa) : cs.length ≤ (positiveSupport f).card := by
  induction h with
  | nil f => simp
  | @step f g cs C hactive _ hconc _ ih =>
    have hu : 0 < 𝔼 x ∈ B, f x := hkappa.trans_le hactive
    have hC : 0 < 𝔼 x ∈ C, f x := (mul_pos hK hu).trans hconc
    have hdrop := positiveSupport_remainder_card_lt C f hC
    simp only [List.length_cons]
    omega

end Chain
end Erdos3.Peeling


namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem exists_terminal_chain (B : Finset G) (Admissible : Finset G → Prop)
    {K kappa : ℝ} (hK : 0 < K) (hkappa : 0 < kappa) (f : G → ℝ) :
    ∃ g cs, Chain B Admissible K kappa f g cs ∧
      ((𝔼 x ∈ B, g x) < kappa ∨ ∀ C, Admissible C → (𝔼 x ∈ C, g x) ≤ K * (𝔼 x ∈ B, g x)) := by
  classical
  suffices h : ∀ n : ℕ, ∀ f : G → ℝ, (positiveSupport f).card = n →
      ∃ g cs, Chain B Admissible K kappa f g cs ∧
        ((𝔼 x ∈ B, g x) < kappa ∨ ∀ C, Admissible C → (𝔼 x ∈ C, g x) ≤ K * (𝔼 x ∈ B, g x)) by
    exact h _ f rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f hsize
    by_cases htiny : (𝔼 x ∈ B, f x) < kappa
    · exact ⟨f, [], Chain.nil f, Or.inl htiny⟩
    by_cases hfree : ∀ C, Admissible C → (𝔼 x ∈ C, f x) ≤ K * (𝔼 x ∈ B, f x)
    · exact ⟨f, [], Chain.nil f, Or.inr hfree⟩
    push Not at hfree
    obtain ⟨C, hC, hconc⟩ := hfree
    have hactive : kappa ≤ 𝔼 x ∈ B, f x := le_of_not_gt htiny
    have hmean : 0 < 𝔼 x ∈ C, f x := (mul_pos hK (hkappa.trans_le hactive)).trans hconc
    have hdrop : (positiveSupport (remainder C f)).card < n := by
      rw [← hsize]
      exact positiveSupport_remainder_card_lt C f hmean
    obtain ⟨g, cs, hchain, hterminal⟩ := ih _ hdrop (remainder C f) rfl
    exact ⟨g, C :: cs, Chain.step C hactive hC hconc hchain, hterminal⟩

theorem exists_bounded_terminal_chain (B : Finset G) (Admissible : Finset G → Prop)
    {K kappa : ℝ} (hK : 0 < K) (hkappa : 0 < kappa) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ B → f x = 0) :
    ∃ g cs, Chain B Admissible K kappa f g cs ∧
      cs.length ≤ (positiveSupport f).card ∧
      (∀ x, 0 ≤ g x ∧ g x ≤ f x) ∧ (∀ x, x ∉ B → g x = 0) ∧
      ((𝔼 x ∈ B, g x) < kappa ∨ ∀ C, Admissible C → (𝔼 x ∈ C, g x) ≤ K * (𝔼 x ∈ B, g x)) := by
  obtain ⟨g, cs, hchain, hterminal⟩ := exists_terminal_chain B Admissible hK hkappa f
  exact ⟨g, cs, hchain, hchain.length_le_support hK hkappa, hchain.bounds hf,
    hchain.supported hf hsupport, hterminal⟩

end Erdos3.Peeling


namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

noncomputable def removedWeight : (G → ℝ) → List (Finset G) → G → ℝ
  | _, [], _ => 0
  | f, C :: cs, x => slice C f x + removedWeight (remainder C f) cs x

omit [Fintype G] in
theorem Chain.decomposition {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
    {f g : G → ℝ} {cs : List (Finset G)} (h : Chain B Admissible K kappa f g cs) (x : G) :
    g x + removedWeight f cs x = f x := by
  induction h with
  | nil f => simp [removedWeight]
  | @step f g cs C _ _ _ _ ih =>
    have hslice := remainder_add_slice C f x
    simp only [removedWeight]
    linarith

omit [Fintype G] in
theorem removedWeight_nonneg (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (cs : List (Finset G)) (x : G) :
    0 ≤ removedWeight f cs x := by
  induction cs generalizing f with
  | nil => simp [removedWeight]
  | cons C cs ih =>
    have hslice : 0 ≤ slice C f x := by
      by_cases hx : x ∈ C <;> simp [slice, hx, hf x]
    exact add_nonneg hslice (ih (remainder C f) (remainder_nonneg C f hf))

theorem Chain.sum_mul_decomposition {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
    {f g : G → ℝ} {cs : List (Finset G)} (h : Chain B Admissible K kappa f g cs) (w : G → ℝ) :
    (∑ x, f x * w x) = (∑ x, g x * w x) + ∑ x, removedWeight f cs x * w x := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← add_mul, h.decomposition x]

end Erdos3.Peeling

end OAI
