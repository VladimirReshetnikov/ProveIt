import OAI.Combinatorics.Progressions.Estimates.BSGIndicator
import OAI.Combinatorics.Progressions.Estimates.NativeRoundedGraphEnergy
import OAI.Combinatorics.Progressions.Probability.BSGDensity

namespace OAI

section

namespace Finset
open scoped _root_.Finset

variable {G : Type*} [Fintype G] [DecidableEq G] [AddGroup G]

def addEnergy' (s t : Finset G) : ℚ≥0 :=
  #{x ∈ ((s ×ˢ s) ×ˢ t ×ˢ t) | x.1.1 + x.2.1 = x.1.2 + x.2.2} / Fintype.card G ^ 3

scoped[Combinatorics.Additive'] notation3:max "E[" s ", " t "]" => _root_.OAI.Finset.addEnergy' s t
scoped[Combinatorics.Additive'] notation3:max "E[" s "]" => _root_.OAI.Finset.addEnergy' s s

theorem addEnergy'_eq_div_energy (s t : Finset G) :
    addEnergy' s t = (_root_.Finset.addEnergy s t : ℚ≥0) / Fintype.card G ^ 3 := rfl

theorem cast_addEnergy' (s t : Finset G) :
    (addEnergy' s t : ℝ) = (_root_.Finset.addEnergy s t : ℝ) / (Fintype.card G : ℝ) ^ 3 := by
  rw [addEnergy'_eq_div_energy]
  simp

end Finset

end

section

namespace Erdos3.BSG

open _root_.Finset _root_.OAI.Finset Fintype Function
open scoped BigOperators ComplexConjugate NNReal Pointwise translate Indicator
  Combinatorics.Additive'

local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

variable {G K : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [Semifield K] [CharZero K] [StarRing K]

def dconv (f g : G → K) : G → K :=
  fun a => 𝔼 x : G × G with x.1 - x.2 = a, f x.1 * conj g x.2

scoped[BSGConvolution] infixl:71 " ○ " => _root_.OAI.Erdos3.BSG.dconv

open scoped BSGConvolution

theorem dconv_eq_expect_add (f g : G → K) (a : G) :
    (f ○ g) a = 𝔼 t, f (a + t) * conj (g t) := by
  unfold dconv
  refine expect_nbij (fun x => x.2) (fun x _ => mem_univ _) ?_ ?_ fun b _ =>
    ⟨(a + b, b), mem_filter.mpr ⟨mem_univ _, add_sub_cancel_right _ _⟩, rfl⟩
  · intro x hx
    have heq : x.1 = a + x.2 := (sub_eq_iff_eq_add).mp (mem_filter.mp hx).2
    simp only [heq, Pi.conj_apply]
  · unfold Set.InjOn
    intro x hx y hy hxy
    apply Prod.ext
    · have hx' := (sub_eq_iff_eq_add).mp (mem_filter.mp hx).2
      have hy' := (sub_eq_iff_eq_add).mp (mem_filter.mp hy).2
      simp only [hx', hy', hxy]
    · exact hxy

theorem dconv_eq_expect_sub (f g : G → K) (a : G) :
    (f ○ g) a = 𝔼 t, f t * conj (g (t - a)) := by
  rw [dconv_eq_expect_add]
  symm
  refine Fintype.expect_equiv (Equiv.subRight a) _ _ fun t => ?_
  simp only [Equiv.subRight_apply]
  rw [add_comm a, sub_add_cancel]

theorem expect_dconv_mul (f g h : G → K) :
    𝔼 a, (f ○ g) a * h a = 𝔼 a, 𝔼 b, f a * conj (g b) * h (a - b) := by
  simp_rw [dconv_eq_expect_sub, expect_mul]
  rw [expect_comm]
  exact expect_congr rfl fun x _ => Fintype.expect_equiv (Equiv.subLeft x) _ _ fun y => by simp

theorem expect_dconv (f g : G → K) :
    𝔼 a, (f ○ g) a = (𝔼 a, f a) * 𝔼 a, conj (g a) := by
  simpa only [Fintype.expect_mul_expect, Pi.one_apply, mul_one] using expect_dconv_mul f g 1

theorem dconv_indicator_one (f : G → K) (s : Finset G) :
    f ○ 𝟭_[s] = (∑ a ∈ s, τ (-a) f) /ℚ Fintype.card G := by
  ext
  simp [dconv_eq_expect_add, Set.indicator_apply, expect]

theorem indicator_one_dconv_indicator_one_eq_dens (s t : Finset G) (a : G) :
    (𝟭_[s, K] ○ 𝟭_[t]) a = (s ∩ (a +ᵥ t)).dens := by
  rw [← dens_vadd_finset (-a), inter_comm, vadd_finset_inter]
  simp [dconv_indicator_one, Set.indicator_apply, NNRat.smul_def, dens, div_eq_inv_mul,
    ← filter_mem_eq_inter, ← neg_vadd_mem_iff, sub_eq_add_neg]

theorem indicator_one_dconv_indicator_one_eq_addConvolution_div (s t : Finset G) (a : G) :
    (𝟭_[s, K] ○ 𝟭_[t]) a = s.addConvolution (-t) a / card G := by
  rw [indicator_one_dconv_indicator_one_eq_dens, dens, card_inter_vadd]
  simp

theorem expect_indicator_one_dconv_indicator_one (s t : Finset G) :
    𝔼 a, (𝟭_[(s : Set G), K] ○ 𝟭_[t]) a = s.dens * t.dens := by
  simp [expect_dconv, Set.conj_indicator_one_apply]
  simp [← Pi.one_def]

theorem expect_indicator_one_dconv_indicator_sq (s t : Finset G) :
    𝔼 x, (𝟭_[(s : Set G), K] ○ 𝟭_[t]) x ^ 2 = E[s, t] := by
  suffices
      ∑ x, #{yz ∈ s ×ˢ t | yz.1 - yz.2 = x} ^ 2 =
        #{x ∈ (s ×ˢ s) ×ˢ t ×ˢ t | x.1.1 + x.2.1 = x.1.2 + x.2.2} by
    simp only [expect, card_univ, indicator_one_dconv_indicator_one_eq_dens, dens, NNRat.cast_div,
      NNRat.cast_natCast, sq, div_mul_div_comm, ← sum_div, NNRat.smul_def, NNRat.cast_inv,
      addEnergy', NNRat.cast_pow, card_inter_vadd, ← card_sub_eq]
    field_simp
    norm_cast
  simp only [_root_.Finset.card_eq_sum_ones, sq, Finset.sum_mul_sum, sum_filter, sum_product, boole_mul,
    univ.sum_comm, Finset.sum_ite_eq, mem_univ, ite_true, sub_eq_sub_iff_add_eq_add]
  exact sum_comm

end Erdos3.BSG

end

section

namespace Erdos3.BSG

open _root_.Finset _root_.OAI.Finset Function
open scoped ComplexConjugate BSGConvolution

variable {G K : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [Semifield K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
  [StarRing K] [StarOrderedRing K] {f g : G → K}

omit [IsStrictOrderedRing K] in
theorem dconv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ○ g :=
  fun _ => expect_nonneg fun x _ => mul_nonneg (hf x.1) (star_nonneg_iff.mpr (hg x.2))

omit [IsStrictOrderedRing K] in
theorem dconv_apply_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) (a : G) : 0 ≤ (f ○ g) a :=
  dconv_nonneg hf hg a

theorem dconv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ○ g := by
  rw [Pi.lt_def] at hf hg ⊢
  obtain ⟨hf, a, ha⟩ := hf
  obtain ⟨hg, b, hb⟩ := hg
  change 0 < f a at ha
  change 0 < g b at hb
  refine ⟨dconv_nonneg hf hg, a - b, ?_⟩
  change 0 < (f ○ g) (a - b)
  rw [dconv_eq_expect_add]
  apply expect_pos' (fun x _ => mul_nonneg (hf (a - b + x)) (star_nonneg_iff.mpr (hg x)))
  refine ⟨b, mem_univ _, ?_⟩
  rw [sub_add_cancel]
  exact mul_pos ha (star_pos_iff.mpr hb)

end Erdos3.BSG

end

section

namespace Erdos3.BSG

open _root_.Finset hiding card
open _root_.OAI.Finset
open Fintype
open scoped BigOperators Pointwise Combinatorics.Additive' Indicator BSGConvolution

section
variable {α : Type*} [Fintype α] [DecidableEq α] {H : Finset (α × α)} {A B X : Finset α} {a b x : α}
  {K : ℝ}

omit [Fintype α] in
lemma oneOfPair_aux (hH : H ⊆ X ×ˢ X) : #{yz ∈ H | yz.1 = x} = #{c ∈ X | (x, c) ∈ H} := by
  refine card_nbij' Prod.snd (fun c ↦ (x, c)) ?_ (by simp [Set.MapsTo])
    (by grind [Set.LeftInvOn]) (by simp [Set.LeftInvOn])
  simpa +contextual [Set.MapsTo, eq_comm] using fun a b hab _ ↦ (mem_product.1 (hH hab)).2

noncomputable def oneOfPair (H : Finset (α × α)) (X : Finset α) : Finset α :=
  {x ∈ X | (3 / 4 : ℝ) * X.dens ≤ {c ∈ X | (x, c) ∈ H}.dens}

lemma oneOfPair_subset : oneOfPair H X ⊆ X := filter_subset ..

lemma mem_oneOfPair :
    x ∈ oneOfPair H X ↔ x ∈ X ∧ (3 / 4 : ℝ) * X.dens ≤ {c ∈ X | (x, c) ∈ H}.dens := mem_filter

lemma oneOfPair_bound_one :
    (∑ x ∈ X \ oneOfPair H X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α ≤ (3 / 4) * X.dens ^ 2 := calc
  _ ≤ (∑ _x ∈ X \ oneOfPair H X, 3 / 4 * X.dens : ℝ) / card α := by
    gcongr
    grind [oneOfPair]
  _ = (X \ oneOfPair H X).dens * (3 / 4 * X.dens) := by simp [dens]; ring
  _ ≤ X.dens * (3 / 4 * X.dens) := by grw [sdiff_subset]
  _ = _ := by ring

lemma oneOfPair_bound_two (hH : H ⊆ X ×ˢ X) (Hcard : (7 / 8 : ℝ) * X.dens ^ 2 ≤ H.dens) :
    (1 / 8 : ℝ) * X.dens ^ 2 ≤ X.dens * (oneOfPair H X).dens := calc
  _ ≤ H.dens - (3 / 4 : ℝ) * X.dens ^ 2 := by linarith
  _ ≤ H.dens - (∑ x ∈ X \ oneOfPair H X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α := by
    gcongr; exact oneOfPair_bound_one
  _ = H.dens - (∑ x ∈ X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α
    + (∑ x ∈ oneOfPair H X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α := by
    rw [sum_sdiff_eq_sub oneOfPair_subset, sub_add, sub_div]
  _ = (∑ x ∈ oneOfPair H X, {c ∈ X | (x, c) ∈ H}.dens : ℝ) / card α := by
    simp only [dens, Fintype.card_prod, Nat.cast_mul, NNRat.cast_div, NNRat.cast_natCast,
      NNRat.cast_mul, ← sum_div, div_div, add_eq_right, sub_eq_zero, ← oneOfPair_aux hH]
    norm_cast
    rw [← card_eq_sum_card_fiberwise fun x hx ↦ (mem_product.1 (hH hx)).1]
  _ ≤ (∑ _x ∈ oneOfPair H X, (X.dens : ℝ)) / card α := by gcongr with i; exact filter_subset ..
  _ = X.dens * (oneOfPair H X).dens := by simp [dens]; ring

lemma oneOfPair_bound (hH : H ⊆ X ×ˢ X) (hX : X.Nonempty)
    (Hcard : (7 / 8 : ℝ) * X.dens ^ 2 ≤ H.dens) (h : A.dens / (2 * K) ≤ X.dens) :
    A.dens / (2 ^ 4 * K : ℝ) ≤ (oneOfPair H X).dens := calc
    _ = (A.dens / (2 * K) : ℝ) / 8 := by ring
    _ ≤ (X.dens / 8 : ℝ) := by gcongr
    _ ≤ (oneOfPair H X).dens :=
      le_of_mul_le_mul_left ((oneOfPair_bound_two hH Hcard).trans_eq' (by ring)) <| by positivity

lemma quadruple_bound_c {a b : α} (ha : a ∈ oneOfPair H X) (hb : b ∈ oneOfPair H X) :
    (X.dens : ℝ) / 2 ≤ {c ∈ X | (a, c) ∈ H ∧ (b, c) ∈ H}.dens := by
  rw [mem_oneOfPair] at ha hb
  rw [filter_and, cast_dens_inter, ← filter_or]
  have : ({c ∈ X | (a, c) ∈ H ∨ (b, c) ∈ H}.dens : ℝ) ≤ X.dens := by grw [filter_subset]
  linarith [ha.2, hb.2, this]

end

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {A B : Finset G} {x : G}

omit [Fintype G] in
lemma quadruple_bound_right {a b : G} (H : Finset (G × G)) (X : Finset G) (h : x = a - b) :
    (#({c ∈ X | (a, c) ∈ H ∧ (b, c) ∈ H}.sigma fun c ↦ ((B ×ˢ B) ×ˢ B ×ˢ B).filter
        fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) : ℝ)
      ≤ #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = a - b) := by
  rw [← h, Nat.cast_le]
  refine card_le_card_of_injOn Sigma.snd (by simp +contextual [Set.MapsTo, *]) ?_
  simp +contextual [Set.InjOn]
  aesop

variable {K : Type*} [Semifield K] [CharZero K] [StarRing K]

section lemma1

lemma claim_one : 𝔼 x : G, (𝟭_[A, K] ○ 𝟭_[B]) x * (A ∩ (x +ᵥ B)).dens = E[A, B] := by
  simp only [← expect_indicator_one_dconv_indicator_sq, ← indicator_one_dconv_indicator_one_eq_dens,
    sq]

lemma claim_two :
    (E[A, B]) ^ 2 / (A.dens * B.dens) ≤
      𝔼 x, (𝟭_[(A : Set G), ℝ] ○ 𝟭_[B]) x * (A ∩ (x +ᵥ B)).dens ^ 2 := by
  let f := fun x ↦ ((𝟭_[(A : Set G), ℝ] ○ 𝟭_[B]) x).sqrt
  have hf : ∀ x, f x ^ 2 = (𝟭_[A, ℝ] ○ 𝟭_[B]) x := by
    intro x
    rw [Real.sq_sqrt]
    exact dconv_apply_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg x
  have := expect_mul_sq_le_sq_mul_sq univ f (fun x ↦ f x * (A ∩ (x +ᵥ B)).dens)
  refine div_le_of_le_mul₀ (by positivity) ?_ ?_
  · refine expect_nonneg fun i _ ↦ ?_

    exact mul_nonneg (dconv_apply_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg _)
      (by positivity)
  simp only [← sq, ← mul_assoc, hf, expect_indicator_one_dconv_indicator_one, mul_pow, claim_one]
    at this
  grind

lemma claim_three {H : Finset (G × G)} (hH : H ⊆ A ×ˢ A) :
    𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ H).dens =
      (∑ ab ∈ H, 𝔼 x, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * (𝟭_[B] (ab.1 - x) * 𝟭_[B] (ab.2 - x)))
        / card G ^ 2 := by
  simp only [dens, Fintype.card_prod, Nat.cast_mul, NNRat.cast_div, NNRat.cast_natCast,
    NNRat.cast_mul, mul_div, Fintype.expect_eq_sum_div_card, ← sum_div]
  field_simp
  simp only [sum_comm (s := H), mul_sum, _root_.Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  congr! 1 with x
  rw [inter_comm, ← filter_mem_eq_inter, sum_filter]
  congr! 1 with ⟨a, b⟩ hab
  have : a ∈ A ∧ b ∈ A := by simpa using hH hab
  simp [this, Set.indicator_apply, ← neg_vadd_mem_iff, neg_add_eq_sub]
  grind

lemma claim_four (ab : G × G) :
    𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * (𝟭_[B] (ab.1 - x) * 𝟭_[B] (ab.2 - x)) ≤
      B.dens * (𝟭_[B] ○ 𝟭_[B]) (ab.1 - ab.2) := by
  obtain ⟨a, b⟩ := ab
  have (x : G) : (𝟭_[A, ℝ] ○ 𝟭_[B]) x ≤ B.dens := by
    simp only [dconv_eq_expect_add, Set.conj_indicator_one_apply, dens,
      Fintype.expect_eq_sum_div_card, NNRat.cast_div, NNRat.cast_natCast]
    gcongr
    simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    simp only [Set.indicator_apply, mul_boole, SetLike.mem_coe,
      ← sum_filter (· ∈ B), filter_mem_eq_inter, univ_inter]
    gcongr with i
    grind
  have : 𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * (𝟭_[B] ((a, b).1 - x) * 𝟭_[B] ((a, b).2 - x)) ≤
    B.dens * 𝔼 x : G, (𝟭_[B] ((a, b).1 - x) * 𝟭_[B] ((a, b).2 - x)) := by
    rw [mul_expect]
    gcongr with s hs
    · exact mul_nonneg Set.indicator_one_apply_nonneg Set.indicator_one_apply_nonneg
    · exact this _
  refine this.trans_eq ?_
  congr 1
  simp only [dconv_eq_expect_add]
  exact Fintype.expect_equiv (Equiv.subLeft b) _ _ <| by simp

lemma claim_five {H : Finset (G × G)} (hH : H ⊆ A ×ˢ A) :
    𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ H).dens ≤
      B.dens * (∑ ab ∈ H, (𝟭_[B] ○ 𝟭_[B]) (ab.1 - ab.2)) / card G ^ 2 := by
  rw [claim_three hH, mul_sum]; gcongr; exact claim_four _

noncomputable def choiceH (A B : Finset G) (c : ℝ) : Finset (G × G) :=
  {ab ∈ A ×ˢ A |
    (𝟭_[B, ℝ] ○ 𝟭_[B]) (ab.1 - ab.2) ≤ c / 2 * (E[A, B] ^ 2 / (A.dens ^ 3 * B.dens ^ 2))}

lemma choiceH_subset {c : ℝ} : choiceH A B c ⊆ A ×ˢ A := filter_subset ..

lemma claim_six (c : ℝ) (hc : 0 ≤ c) :
    𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ choiceH A B c).dens ≤
      c / 2 * (E[A, B] ^ 2 / (A.dens * B.dens)) := by
  have : ∑ ab ∈ choiceH A B c, (𝟭_[B] ○ 𝟭_[B]) (ab.1 - ab.2) ≤
      #(choiceH A B c) * (c / 2 * (E[A, B] ^ 2 / (A.dens ^ 3 * B.dens ^ 2))) := by
    rw [← nsmul_eq_mul]
    exact sum_le_card_nsmul _ _ _ fun x hx ↦ (mem_filter.1 hx).2
  replace : (∑ ab ∈ choiceH A B c, (𝟭_[B] ○ 𝟭_[B]) (ab.1 - ab.2)) / card G ^ 2 ≤
      (choiceH A B c).dens * (c / 2 * (E[A, B] ^ 2 / (A.dens ^ 3 * B.dens ^ 2))) := by
    grw [this, mul_div_right_comm]; simp [dens, sq]
  have hH : ((choiceH A B c).dens : ℝ) ≤ A.dens ^ 2 := by grw [choiceH_subset]; simp [sq]
  grw [claim_five choiceH_subset, ← mul_div, this, hH]
  field_simp
  rfl

lemma claim_seven {c : ℝ} (hc : 0 ≤ c) :
    𝔼 x : G,
      (𝟭_[A, ℝ] ○ 𝟭_[B]) x *
          ((c / 2) * (E[A, B] ^ 2 / (A.dens ^ 2 * B.dens ^ 2)) +
            ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ choiceH A B c).dens) ≤
      𝔼 x : G, (𝟭_[A, ℝ] ○ 𝟭_[B]) x * (c * (A ∩ (x +ᵥ B)).dens ^ 2) :=
  calc
    _ = (c / 2 * (E[A, B] ^ 2 / (A.dens * B.dens))) + 𝔼 x : G,
          (𝟭_[A, ℝ] ○ 𝟭_[B]) x * ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ choiceH A B c).dens := by
        simp only [mul_add, expect_add_distrib, expect_indicator_one_dconv_indicator_one,
          ← expect_mul, ← mul_pow]
        field_simp
    _ ≤ _ := by
      grw [claim_six c hc, ← add_mul, add_halves]
      simp only [mul_left_comm _ c, ← mul_expect]
      gcongr
      exact claim_two

lemma claim_eight {c : ℝ} (hc : 0 ≤ c) (A B : Finset G) :
    ∃ x : G, ((c / 2) * (E[A, B] ^ 2 / (A.dens ^ 2 * B.dens ^ 2)) +
          ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ choiceH A B c).dens) ≤
      c * (A ∩ (x +ᵥ B)).dens ^ 2 := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  obtain rfl | hB := B.eq_empty_or_nonempty
  · simp
  by_contra!
  refine (claim_seven hc (A := A) (B := B)).not_gt <| expect_lt_expect (fun x _ ↦ ?_) ?_
  · grw [this x]
    exact dconv_apply_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg x
  have : 0 < 𝟭_[(A : Set G), ℝ] ○ 𝟭_[B] := by apply dconv_pos <;> simpa
  rw [Pi.lt_def] at this
  obtain ⟨-, i, hi : 0 < _⟩ := this
  exact ⟨i, by simp, mul_lt_mul_of_pos_left (this i) hi⟩

lemma lemma_one {c K : ℝ} (hc : 0 < c) (hK : 0 < K) (hE : K⁻¹ * (A.dens ^ 2 * B.dens) ≤ E[A, B])
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ x : G, ∃ X ⊆ A ∩ (x +ᵥ B), A.dens / (Real.sqrt 2 * K) ≤ X.dens ∧
      (1 - c) * X.dens ^ 2 ≤
      ((X ×ˢ X).filter fun ⟨a, b⟩ ↦ c / 2 * (K ^ 2)⁻¹ * A.dens ≤ (𝟭_[B] ○ 𝟭_[B]) (a - b)).dens := by
  obtain ⟨x, hx⟩ := claim_eight hc.le A B
  set X := A ∩ (x +ᵥ B)
  refine ⟨x, X, subset_rfl, ?_, ?_⟩
  · have : (2 : ℝ)⁻¹ * (E[A, B] / (A.dens * B.dens)) ^ 2 ≤ X.dens ^ 2 := by
      refine le_of_mul_le_mul_left (hx.trans' ?_) hc
      exact (le_add_of_nonneg_right <| NNRat.cast_nonneg _).trans_eq' (by ring)
    grw [← sq_le_sq₀ (by positivity) (by positivity), ← this, ← hE]

    field_simp
    norm_num
  rw [one_sub_mul, sub_le_comm]
  refine ((le_add_of_nonneg_left (by positivity)).trans hx).trans' ?_
  rw [sq, ← NNRat.cast_mul, ← dens_product, ← cast_dens_sdiff (filter_subset _ _), ← filter_not,
    ← filter_mem_eq_inter]
  gcongr ↑(dens ?_)
  rintro ⟨a, b⟩
  simp +contextual only [not_le, mem_product, mem_inter, and_imp, mem_filter, choiceH, and_self,
    true_and, X]
  rintro _ _ _ _ h
  grw [h, ← hE]
  apply le_of_eq
  field_simp [hA, hB, hK, le_div_iff₀, div_le_iff₀] at hE ⊢

lemma lemma_one' {c K : ℝ} (hc : 0 < c) (hK : 0 < K) (hE : K⁻¹ * (A.dens ^ 2 * B.dens) ≤ E[A, B])
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ x : G, ∃ X ⊆ A ∩ (x +ᵥ B), A.dens / (2 * K) ≤ X.dens ∧
      (1 - c) * X.dens ^ 2 ≤
      ((X ×ˢ X).filter fun ⟨a, b⟩ ↦ c / 2 * (K ^ 2)⁻¹ * A.dens ≤ (𝟭_[B] ○ 𝟭_[B]) (a - b)).dens := by
  obtain ⟨x, X, hX₁, hX₂, hX₃⟩ := lemma_one hc hK hE hA hB
  refine ⟨x, X, hX₁, hX₂.trans' ?_, hX₃⟩
  gcongr _ / (?_ * _)
  rw [Real.sqrt_le_iff]
  norm_num

end lemma1

section lemma2
variable {H : Finset (G × G)} {X : Finset G}

lemma quadruple_bound_other {a b c : G} {K : ℝ} {H : Finset (G × G)}
    (hac : (a, c) ∈ H) (hbc : (b, c) ∈ H)
    (hH : ∀ x ∈ H, A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2)) :
    (A.dens / (2 ^ 4 * K ^ 2)) ^ 2 ≤ #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦
        a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) / card G ^ 2 := by
  rw [filter_product (s := B ×ˢ B) (t := B ×ˢ B) (fun z ↦ z.1 - z.2 = a - c)
    (fun z ↦ z.1 - z.2 = b - c), card_product, sq, sq (card G : ℝ), Nat.cast_mul,
      mul_div_mul_comm]
  gcongr ?_ * ?_
  · grw [card_sub_eq, hH _ hac, indicator_one_dconv_indicator_one_eq_addConvolution_div]
  · grw [card_sub_eq, hH _ hbc, indicator_one_dconv_indicator_one_eq_addConvolution_div]

lemma quadruple_bound_left {a b : G} {K : ℝ} {H : Finset (G × G)}
    (ha : a ∈ oneOfPair H X) (hb : b ∈ oneOfPair H X)
    (hH : ∀ x ∈ H, A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2)) :
    X.dens / 2 * (A.dens / (2 ^ 4 * K ^ 2)) ^ 2 ≤
      #({c ∈ X | (a, c) ∈ H ∧ (b, c) ∈ H}.sigma fun c ↦
      ((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦
        a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) / card G ^ 3  :=
  calc
    _ ≤ (∑ c ∈ X with (a, c) ∈ H ∧ (b, c) ∈ H, ((A.dens / (2 ^ 4 * K ^ 2)) ^ 2 : ℝ))
      / card G := by
      grw [sum_const, quadruple_bound_c ha hb]
      apply le_of_eq
      simp [dens]
      ring
    _ ≤ (∑ c ∈ X with (a, c) ∈ H ∧ (b, c) ∈ H, #(((B ×ˢ B) ×ˢ B ×ˢ B).filter
        fun ((a₁, a₂), a₃, a₄) ↦ a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c) / card G ^ 2 : ℝ)
          / card G := by
      gcongr with i hi
      simp only [mem_filter] at hi
      convert quadruple_bound_other hi.2.1 hi.2.2 hH
    _ = _ := by rw [_root_.Finset.card_sigma, Nat.cast_sum, ← sum_div]; ring

lemma quadruple_bound {K : ℝ} {x : G} (hx : x ∈ oneOfPair H X - oneOfPair H X)
    (hH : ∀ x ∈ H, A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2)) :
    (A.dens ^ 2 * X.dens) / (2 ^ 9 * K ^ 4) ≤
      #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = x) /
      card G ^ 3 := by
  rw [mem_sub] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  grw [← quadruple_bound_right H X rfl, ← quadruple_bound_left ha hb hH]
  apply le_of_eq
  ring

lemma big_quadruple_bound {K : ℝ}
    (hH : ∀ x ∈ H, A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (x.1 - x.2))
    (hX : A.dens / (2 * K) ≤ X.dens) :
    (oneOfPair H X - oneOfPair H X).dens * (A.dens ^ 3 / (2 ^ 10 * K ^ 5)) ≤ B.dens ^ 4 :=
  calc
    _ = (oneOfPair H X - oneOfPair H X).dens * ((A.dens ^ 2 * (A.dens / (2 * K)))
      / (2 ^ 9 * K ^ 4)) := by ring
    _ ≤ (oneOfPair H X - oneOfPair H X).dens * ((A.dens ^ 2 * X.dens) / (2 ^ 9 * K ^ 4)) := by
      gcongr
    _ = (∑ _x ∈ oneOfPair H X - oneOfPair H X, (A.dens ^ 2 * X.dens) / (2 ^ 9 * K ^ 4) : ℝ)
      / card G := by simp [dens]; ring
    _ ≤ (∑ x ∈ oneOfPair H X - oneOfPair H X,
          #(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = x) /
            card G ^ 3 : ℝ)
      / card G := by gcongr (∑ _ ∈ _, ?_) / _ with x hx; exact quadruple_bound hx hH
    _ ≤ 𝔼 x, (#(((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = x) /
          card G ^ 3 : ℝ) := by grw [Fintype.expect_eq_sum_div_card, ← subset_univ]
    _ = _ := by
      rw [Fintype.expect_eq_sum_div_card, ← sum_div]
      norm_cast
      rw [← card_eq_sum_card_fiberwise (by simp [Set.mapsTo_univ])]
      simp [dens]
      field_simp

lemma BSG_aux {K : ℝ} (hK : 0 < K) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : K⁻¹ * (A.dens ^ 2 * B.dens) ≤ E[A, B]) :
    ∃ x : G, ∃ A' ⊆ A ∩ (x +ᵥ B), (2 ^ 4)⁻¹ * K⁻¹ * A.dens ≤ A'.dens ∧
      (A' - A').dens ≤ 2 ^ 10 * K ^ 5 * B.dens ^ 4 / A.dens ^ 3 := by
  obtain ⟨x, X, hX₁, hX₂, hX₃⟩ := lemma_one' (c := 1 / 8) (by norm_num) hK hAB hA hB
  set H : Finset (G × G) := (X ×ˢ X).filter
    fun ⟨a, b⟩ ↦ A.dens / (2 ^ 4 * K ^ 2) ≤ (𝟭_[B] ○ 𝟭_[B]) (a - b)
  have : (0 : ℝ) < X.dens := hX₂.trans_lt' (by positivity)
  refine ⟨x, oneOfPair H X, (filter_subset _ _).trans hX₁, ?_, ?_⟩
  · rw [← mul_inv, inv_mul_eq_div]
    refine oneOfPair_bound (filter_subset _ _) (by simpa using this) ?_ hX₂
    convert hX₃ using 2
    · norm_num
    · unfold H
      ring_nf
  have := big_quadruple_bound (H := H) (fun x hx ↦ (mem_filter.1 hx).2) hX₂
  rw [le_div_iff₀ (by positivity)]
  rw [mul_div_assoc', div_le_iff₀ (by positivity)] at this
  grind

end lemma2

theorem balogSzemerediGowers {K : ℝ} (hK : 0 ≤ K) (hB : B.Nonempty)
    (hAB : K⁻¹ * (A.dens ^ 2 * B.dens) ≤ E[A, B]) :
    ∃ A' ⊆ A, (2 ^ 4)⁻¹ * K⁻¹ * A.dens ≤ A'.dens ∧
      (A' - A').dens ≤ 2 ^ 10 * K ^ 5 * B.dens ^ 4 / A.dens ^ 3 := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  obtain rfl | hK := eq_or_lt_of_le hK
  · simp
  · grind [BSG_aux]

theorem BSG₂ {K : ℝ} (hK : 0 ≤ K) (hB : B.Nonempty)
    (hAB : K⁻¹ * (A.dens ^ 2 * B.dens) ≤ E[A, B]) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, (2 ^ 4)⁻¹ * K⁻¹ * A.dens ≤ A'.dens ∧
      (2 ^ 4)⁻¹ * K⁻¹ * A.dens ≤ B'.dens ∧
        (A' - B').dens ≤ 2 ^ 10 * K ^ 5 * B.dens ^ 4 / A.dens ^ 3 := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · exact ⟨∅, by simp, ∅, by simp⟩
  obtain rfl | hK := eq_or_lt_of_le hK
  · exact ⟨∅, by simp, ∅, by simp⟩
  obtain ⟨x, A', hA, h⟩ := BSG_aux hK (by simpa [_root_.Finset.card_pos]) (by simpa [_root_.Finset.card_pos]) hAB
  refine ⟨A', hA.trans inter_subset_left, -x +ᵥ A', ?_, h.1, ?_, ?_⟩
  · grw [hA, inter_subset_right, neg_vadd_vadd]
  · simp_all
  · simpa [sub_eq_add_neg, add_vadd_comm] using h.2

theorem BSG_self {K : ℝ} (hK : 0 ≤ K) (hA : A.Nonempty) (hAK : K⁻¹ * A.dens ^ 3 ≤ E[A]) :
    ∃ A' ⊆ A, (2 ^ 4)⁻¹ * K⁻¹ * A.dens ≤ A'.dens ∧ (A' - A').dens ≤ 2 ^ 10 * K ^ 5 * A.dens := by
  convert balogSzemerediGowers hK hA ?_ using 5 <;> grind

theorem BSG_self' {K : ℝ} (hK : 0 ≤ K) (hA : A.Nonempty) (hAK : K⁻¹ * A.dens ^ 3 ≤ E[A]) :
    ∃ A' ⊆ A, (2 ^ 4)⁻¹ * K⁻¹ * A.dens ≤ A'.dens ∧ (A' - A').dens ≤ 2 ^ 14 * K ^ 6 * A'.dens := by
  obtain ⟨A', hA', hAA', hAK'⟩ := BSG_self hK hA hAK
  refine ⟨A', hA', hAA', hAK'.trans ?_⟩
  calc
    _ = 2 ^ 14 * K ^ 6 * ((2 ^ 4)⁻¹ * K⁻¹ * A.dens) := ?_
    _ ≤ _ := by gcongr
  grind

end Erdos3.BSG

end

section

namespace Erdos3.BSG

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
theorem density_mul_le_iff_card_mul_le (s t : Finset G) (c : ℝ) :
    c * (s.dens : ℝ) ≤ t.dens ↔ c * (s.card : ℝ) ≤ t.card := by
  simp only [Finset.dens, NNRat.cast_div, NNRat.cast_natCast]
  rw [← mul_div_assoc]
  exact div_le_div_iff_of_pos_right (by exact_mod_cast Fintype.card_pos (α := G))

omit [DecidableEq G] in
theorem density_le_mul_iff_card_le_mul (s t : Finset G) (c : ℝ) :
    (s.dens : ℝ) ≤ c * t.dens ↔ (s.card : ℝ) ≤ c * t.card := by
  simp only [Finset.dens, NNRat.cast_div, NNRat.cast_natCast]
  rw [← mul_div_assoc]
  exact div_le_div_iff_of_pos_right (by exact_mod_cast Fintype.card_pos (α := G))

theorem exists_large_subset_small_difference (A : Finset G) (hA : A.Nonempty)
    {K : ℝ} (hK : 0 < K) (henergy : K⁻¹ * (A.card : ℝ) ^ 3 ≤ (Finset.addEnergy A A : ℝ)) :
    ∃ S ⊆ A, S.Nonempty ∧ (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * A.card ≤ (S.card : ℝ) ∧
      ((S - S).card : ℝ) ≤ (2 ^ 14 : ℝ) * K ^ 6 * S.card := by
  have he : K⁻¹ * (A.dens : ℝ) ^ 3 ≤ (Finset.addEnergy' A A : ℝ) := by
    rw [Finset.cast_addEnergy']
    simp only [Finset.dens, NNRat.cast_div, NNRat.cast_natCast, div_pow]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right henergy (by positivity)
  obtain ⟨S, hSA, hsize, hsmall⟩ := BSG_self' hK.le hA he
  have hsize' := (density_mul_le_iff_card_mul_le A S ((2 ^ 4 : ℝ)⁻¹ * K⁻¹)).mp
    (by simpa only [mul_assoc] using hsize)
  have hsmall' := (density_le_mul_iff_card_le_mul (S - S) S ((2 ^ 14 : ℝ) * K ^ 6)).mp
    (by simpa only [mul_assoc] using hsmall)
  have hpos : (0 : ℝ) < S.card :=
    (mul_pos (mul_pos (by positivity) (inv_pos.mpr hK))
      (by exact_mod_cast hA.card_pos)).trans_le hsize'
  exact ⟨S, hSA, Finset.card_pos.mp (by exact_mod_cast hpos), hsize', hsmall'⟩

end Erdos3.BSG

end

section

namespace Erdos3

open scoped Pointwise

variable {G V : Type*} [DecidableEq G] [DecidableEq V]

theorem mem_additiveGraph_iff (H : Finset G) (b : G → V) (x : G × V) :
    x ∈ additiveGraph H b ↔ x.1 ∈ H ∧ x.2 = b x.1 := by
  rw [additiveGraph, Finset.mem_image]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨hh, rfl⟩
  · intro hx
    exact ⟨x.1, hx.1, Prod.ext rfl hx.2.symm⟩

theorem additiveGraph_image_fst (H : Finset G) (b : G → V) (S : Finset (G × V))
    (hS : S ⊆ additiveGraph H b) : additiveGraph (S.image Prod.fst) b = S := by
  ext x
  rw [mem_additiveGraph_iff]
  constructor
  · rintro ⟨hx, he⟩
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    have hgy := (mem_additiveGraph_iff H b y).mp (hS hy)
    have hxy : x = y := Prod.ext hyx.symm (by rw [he, ← hyx, hgy.2])
    exact hxy.symm ▸ hy
  · intro hx
    exact ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩, ((mem_additiveGraph_iff H b x).mp (hS hx)).2⟩

variable [AddCommGroup G] [Fintype G] [AddCommGroup V] [Fintype V]

theorem exists_large_graph_subset_small_difference
    (H : Finset G) (hH : H.Nonempty) (b : G → V) {K : ℝ} (hK : 0 < K)
    (henergy : K⁻¹ * (H.card : ℝ) ^ 3 ≤
      (Finset.addEnergy (additiveGraph H b) (additiveGraph H b) : ℝ)) :
    ∃ J ⊆ H, J.Nonempty ∧ (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card ≤ (J.card : ℝ) ∧
      ((additiveGraph J b - additiveGraph J b).card : ℝ) ≤ (2 ^ 14 : ℝ) * K ^ 6 * J.card := by
  obtain ⟨S, hS, hSn, hsize, hdiff⟩ := BSG.exists_large_subset_small_difference
    (additiveGraph H b) (hH.image _) hK (by simpa only [additiveGraph_card] using henergy)
  let J := S.image Prod.fst
  have hgraph : additiveGraph J b = S := additiveGraph_image_fst H b S hS
  have hcard : S.card = J.card := by rw [← hgraph, additiveGraph_card]
  refine ⟨J, ?_, hSn.image _, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact ((mem_additiveGraph_iff H b y).mp (hS hy)).1
  · simpa only [additiveGraph_card, hcard] using hsize
  · rw [hgraph, ← hcard]
    exact hdiff

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped Pointwise

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem variable_coefficient_graph_energy {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    Real.exp (-(P + 13 * Fintype.card I)) * (H.card : ℝ) ^ 3 ≤
      (Finset.addEnergy (additiveGraph H (fun h => variableRoundedCoefficient M l (a h)))
        (additiveGraph H (fun h => variableRoundedCoefficient M l (a h))) : ℝ) := by
  apply variable_graph_energy_density H D.quadruples a c M l ε _ hsmall _ _
  · intro t ht
    let J := R.interval ⟨t, D.subset ht⟩
    exact ⟨J.first_mem, J.second_mem, J.third_mem, J.fourth_mem⟩
  · intro t ht
    exact hnear t ht
  · have hcard : (H.card : ℝ) ≤ Fintype.card (ZMod N) := by
      exact_mod_cast Finset.card_le_univ H
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 3)
      (Real.exp_nonneg _)).trans D.density

theorem variable_graph_small_difference {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : I → ℕ) [∀ i, NeZero (M i)] (ε : I → ℝ)
    (hsmall : ∀ i, (M i : ℝ) * l i * ε i ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ coordinateDenominatorGrid l,
      ∀ i, |c i + (a (rankQuadrupleParameters t 1) i + a (rankQuadrupleParameters t 2) i -
        a (rankQuadrupleParameters t 0) i - a (rankQuadrupleParameters t 3) i) - q i| ≤ ε i) :
    let K := Real.exp (P + 13 * Fintype.card I)
    ∃ J ⊆ H, J.Nonempty ∧ (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card ≤ (J.card : ℝ) ∧
      ((additiveGraph J (fun h => variableRoundedCoefficient M l (a h)) -
        additiveGraph J (fun h => variableRoundedCoefficient M l (a h))).card : ℝ) ≤
          (2 ^ 14 : ℝ) * K ^ 6 * J.card := by
  intro K
  classical
  obtain ⟨t, ht⟩ := D.nonempty
  have hH : H.Nonempty := ⟨t.2.1, (R.interval ⟨t, D.subset ht⟩).first_mem⟩
  apply exists_large_graph_subset_small_difference H hH (fun h => variableRoundedCoefficient M l (a h))
    (Real.exp_pos _) _
  simpa only [Real.exp_neg] using D.variable_coefficient_graph_energy a c M l ε hsmall hnear

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped Pointwise

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem rounded_graph_small_difference {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (M l : ℕ) [NeZero M] {ε : ℝ}
    (hsmall : (M : ℝ) * l * ε ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ realDenominatorGrid l,
      ‖c + (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
        a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) - q‖ ≤ ε) :
    let K := Real.exp (P + 13 * Fintype.card I)
    ∃ J ⊆ H, J.Nonempty ∧ (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card ≤ (J.card : ℝ) ∧
      ((additiveGraph J (fun h => roundedCoefficient M l (a h)) -
        additiveGraph J (fun h => roundedCoefficient M l (a h))).card : ℝ) ≤
          (2 ^ 14 : ℝ) * K ^ 6 * J.card := by
  intro K
  classical
  obtain ⟨t, ht⟩ := D.nonempty
  have hH : H.Nonempty := ⟨t.2.1, (R.interval ⟨t, D.subset ht⟩).first_mem⟩
  apply exists_large_graph_subset_small_difference H hH (fun h => roundedCoefficient M l (a h))
    (Real.exp_pos _) _
  simpa only [Real.exp_neg] using D.rounded_coefficient_graph_energy a c M l hsmall hnear

theorem exists_rounded_graph_small_difference {I : Type*} [Fintype I]
    (a : ZMod N → I → ℝ) (c : I → ℝ) (l : ℕ) (hl : 0 < l) {ε : ℝ}
    (hε : 0 < ε) (hsmall : 2 * (l : ℝ) * ε ≤ 1)
    (hnear : ∀ t ∈ D.quadruples, ∃ q ∈ realDenominatorGrid l,
      ‖c + (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
        a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) - q‖ ≤ ε) :
    let K := Real.exp (P + 13 * Fintype.card I)
    ∃ M : ℕ, 0 < M ∧ 1 / (2 * (l : ℝ) * ε) ≤ (M : ℝ) ∧
      ∃ J ⊆ H, J.Nonempty ∧ (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * H.card ≤ (J.card : ℝ) ∧
        ((additiveGraph J (fun h => roundedCoefficient M l (a h)) -
          additiveGraph J (fun h => roundedCoefficient M l (a h))).card : ℝ) ≤
            (2 ^ 14 : ℝ) * K ^ 6 * J.card := by
  intro K
  obtain ⟨M, hM, hlow, hscale⟩ := exists_rounding_modulus l hl hε hsmall
  let : NeZero M := ⟨hM.ne'⟩
  exact ⟨M, hM, hlow, D.rounded_graph_small_difference a c M l hscale hnear⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
