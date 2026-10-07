/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.CommonDenominatorMultiples
import OAI.Combinatorics.Progressions.Polynomial.AffinePhaseBias

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def NearInteger (ε x : ℝ) : Prop := ∃ m : ℤ, |x-m| ≤ ε

noncomputable def nearIntegerDensity {X : Type*} [Fintype X] (a : X → ℝ) (ε : ℝ) : ℝ :=
  𝔼 x, if NearInteger ε (a x) then (1 : ℝ) else 0

theorem nearIntegerDensity_eq_card {X : Type*} [Fintype X] (a : X → ℝ) (ε : ℝ) :
    nearIntegerDensity a ε =
      ((Finset.univ.filter (fun x => NearInteger ε (a x))).card : ℝ)/Fintype.card X := by
  simp [nearIntegerDensity, Fintype.expect_eq_sum_div_card]

theorem nearIntegerDensity_le_one {X : Type*} [Fintype X] [Nonempty X]
    (a : X → ℝ) (ε : ℝ) : nearIntegerDensity a ε ≤ 1 := by
  rw [nearIntegerDensity_eq_card]
  apply (div_le_one (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card X)).mpr
  exact_mod_cast (Finset.card_filter_le Finset.univ (fun x => NearInteger ε (a x)))

theorem card_div_le_nearIntegerDensity {X : Type*} [Fintype X]
    (a : X → ℝ) (ε : ℝ) (S : Finset X) (hS : ∀ x ∈ S, NearInteger ε (a x)) :
    (S.card : ℝ)/Fintype.card X ≤ nearIntegerDensity a ε := by
  rw [nearIntegerDensity_eq_card]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Finset.card_le_card (show S ⊆ Finset.univ.filter (fun x => NearInteger ε (a x)) from
    fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ x, hS x hx⟩))

theorem exists_constant_denominator_fiber {X : Type*} (S : Finset X) (q : X → ℕ)
    {K : ℕ} (hK : 0 < K) (hq : ∀ x ∈ S, 0 < q x ∧ q x ≤ K)
    {μ : ℝ} (hsize : (K : ℝ)*μ ≤ S.card) :
    ∃ q₀ : ℕ, 0 < q₀ ∧ q₀ ≤ K ∧ ∃ E : Finset X,
      E ⊆ S ∧ μ ≤ E.card ∧ ∀ x ∈ E, q x = q₀ := by
  have hmap : ∀ x ∈ S, q x ∈ Finset.Icc 1 K := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨(hq x hx).1, (hq x hx).2⟩
  obtain ⟨q₀, hq₀, hlarge⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    hmap (show (Finset.Icc 1 K).Nonempty from ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hK⟩⟩)
    (by simpa only [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] using hsize)
  refine ⟨q₀, (Finset.mem_Icc.mp hq₀).1, (Finset.mem_Icc.mp hq₀).2,
    S.filter (fun x => q x = q₀), Finset.filter_subset _ _, hlarge, ?_⟩
  intro x hx
  exact (Finset.mem_filter.mp hx).2

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem nearIntegerDensity_product {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → ℝ) (ε : ℝ) :
    nearIntegerDensity (fun p : X × Y => f p.1 p.2) ε =
      𝔼 x, nearIntegerDensity (f x) ε := by
  unfold nearIntegerDensity
  exact Finset.expect_product' _ _ (fun x y => if NearInteger ε (f x y) then (1 : ℝ) else 0)

theorem nearIntegerDensity_of_geometric_mean {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) {M : ℕ} (hM : 0 < M) {a : ℝ} (ha : 0 < a)
    (hbias : a ≤ 𝔼 x, ‖geometricCharacterMean M (f x : CircleFourier.Circle)‖) :
    a/2 ≤ nearIntegerDensity f (1/((M : ℝ)*a)) := by
  obtain ⟨S, hS, hgood⟩ := exists_dense_level_set
    (fun x => ‖geometricCharacterMean M (f x : CircleFourier.Circle)‖) ha.le
    (fun x => norm_geometricCharacterMean_le_one M hM _) hbias
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  apply ((le_div_iff₀ hX).mpr hS).trans
  apply card_div_le_nearIntegerDensity _ _ S
  intro x hx
  have hnear := integerDistance_le_of_geometric_mean hM (f x : CircleFourier.Circle)
    (by linarith : 0 < a/2) (hgood x hx)
  refine ⟨round (f x), ?_⟩
  rw [← integerDistance_coe]
  apply hnear.trans_eq
  congr 1
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem nearIntegerDensity_comp_injective {X Y : Type*}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (a : Y → ℝ) (ε : ℝ) (f : X → Y) (hf : Function.Injective f) :
    (Fintype.card X : ℝ)*nearIntegerDensity (fun x => a (f x)) ε ≤
      (Fintype.card Y : ℝ)*nearIntegerDensity a ε := by
  let S := Finset.univ.filter (fun x => NearInteger ε (a (f x)))
  let T := Finset.univ.filter (fun y => NearInteger ε (a y))
  have hST : S.image f ⊆ T := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  have hcard : (S.card : ℝ) ≤ T.card := by
    exact_mod_cast (Finset.card_image_of_injective S hf ▸ Finset.card_le_card hST)
  have hX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hY : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simpa only [nearIntegerDensity_eq_card, S, T, mul_div_cancel₀ _ hX,
    mul_div_cancel₀ _ hY] using hcard

theorem nearIntegerDensity_fiber_injections {X Y Z : Type*}
    [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    [Fintype Z] [Nonempty Z]
    (a : Y → ℝ) (ε : ℝ) (f : Z → X → Y) (hf : ∀ z, Function.Injective (f z))
    {η : ℝ} (hdensity : η ≤ 𝔼 z, nearIntegerDensity (fun x => a (f z x)) ε) :
    η * Fintype.card X / Fintype.card Y ≤ nearIntegerDensity a ε := by
  have hY : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hY).mpr
  have hp := Finset.expect_le_expect (fun z (_ : z ∈ (Finset.univ : Finset Z)) =>
    nearIntegerDensity_comp_injective a ε (f z) (hf z))
  rw [← Finset.mul_expect, Fintype.expect_const] at hp
  have hm := mul_le_mul_of_nonneg_left hdensity (Nat.cast_nonneg (Fintype.card X))
  nlinarith only [hm, hp]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem nearInteger_multiples {X : Type*} [Fintype X] [Nonempty X]
    (v : X → ℤ) (hv : Function.Injective v) (A H : ℕ) (hA : 1 ≤ A)
    (hH : 4*A ≤ H) (hcard : H ≤ Fintype.card X) (hbound : ∀ x, |v x| ≤ (H : ℤ))
    {θ ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/(64*(A : ℝ)^2))
    (hdensity : 1/(A : ℝ) ≤ nearIntegerDensity (fun x => (v x : ℝ)*θ) ε) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 4*A ∧ NearInteger (96*(A : ℝ)^2*ε/H) ((q : ℝ)*θ) := by
  have hAp : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have hHp : 0 < H := by omega
  have hHr : (0 : ℝ) < H := Nat.cast_pos.mpr hHp
  let S := Finset.univ.filter (fun x => NearInteger ε ((v x : ℝ)*θ))
  let D := S.image v
  have hDcard : D.card = S.card := Finset.card_image_of_injective S hv
  have hs : (1/(A : ℝ))*H ≤ (D.card : ℝ) := by
    have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
    have hden : 1/(A : ℝ) ≤ (S.card : ℝ)/Fintype.card X := by
      simpa only [nearIntegerDensity_eq_card] using hdensity
    rw [hDcard]
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by positivity)).trans
      ((le_div_iff₀ hX).mp hden)
  have hnear : ∀ n ∈ D, NearInteger ε ((n : ℝ)*θ) := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    exact (Finset.mem_filter.mp hx).2
  let p : ℤ → ℤ := fun n => if hn : NearInteger ε ((n : ℝ)*θ) then hn.choose else 0
  have hp : ∀ n ∈ D, |(n : ℝ)*θ-p n| ≤ ε := by
    intro n hn
    dsimp only [p]
    rw [dite_eq_left (hnear n hn)]
    exact (hnear n hn).choose_spec
  have hρQ : (4 : ℝ) ≤ (1/(A : ℝ))*(4*A : ℕ) := by
    push_cast
    field_simp
    norm_num
  have hρH : (4 : ℝ) ≤ (1/(A : ℝ))*H := by
    calc
      _ ≤ (1/(A : ℝ))*(4*A : ℕ) := hρQ
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hH) (by positivity)
  have hsmall' : 16*((4*A : ℕ) : ℝ)*ε ≤ 1/(A : ℝ) := by
    calc
      _ ≤ 16*((4*A : ℕ) : ℝ)*(1/(64*(A : ℝ)^2)) := by gcongr
      _ = _ := by push_cast; field_simp; ring
  have hsmall'' : 16*(((4*A : ℕ) : ℝ)*ε) ≤ 1/(A : ℝ) := by linarith [hsmall']
  have hρone : 1/(A : ℝ) ≤ 1 := (div_le_one hAp).mpr (by exact_mod_cast hA)
  have hcap : ((4*A : ℕ) : ℝ)*ε ≤ 1 := by
    have hz : 0 ≤ ((4*A : ℕ) : ℝ)*ε := by positivity
    linarith
  obtain ⟨q, hq, hqA, m, hm⟩ := many_multiples_rational_approximation D p hHp (by omega)
    (by positivity : 0 < 1/(A : ℝ)) hε hρQ hρH hsmall'' hcap hs
    (fun n hn => by obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hn; exact hbound x) hp
  refine ⟨q, hq, hqA, m, hm.trans_eq ?_⟩
  push_cast
  field_simp
  ring

end Erdos3

end

end OAI
