/-
  Finite permutation algebra behind the ultraexacting finite-choice results
  (synthesis §9, Lemma 9.1(b) "finite-family amplification", Theorem 9.8 core).

  Everything in this file is proved; there are no admitted statements.
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

namespace Cardinals.FiniteCycles

open Finset

variable {A F : Type*} [DecidableEq A]

/-- Iterating an equivariance identity `v (σ f) (τ '' B) = τ '' (v f B)`. -/
theorem equivariant_iterate (τ : A → A) (σ : F → F)
    (v : F → Finset A → Finset A)
    (heq : ∀ f B, v (σ f) (B.image τ) = (v f B).image τ) (k : ℕ) :
    ∀ f B, v (σ^[k] f) (B.image τ^[k]) = (v f B).image τ^[k] := by
  induction k with
  | zero => intro f B; simp
  | succ k ih =>
    intro f B
    have h1 : B.image τ^[k+1] = (B.image τ^[k]).image τ := by
      rw [Finset.image_image, ← Function.iterate_succ']
    have h2 : (v f B).image τ^[k+1] = ((v f B).image τ^[k]).image τ := by
      rw [Finset.image_image, ← Function.iterate_succ']
    rw [Function.iterate_succ', Function.comp_apply, h1, heq, ih, h2]

/-- A subset of `B₀` that is invariant under a map acting transitively on `B₀`
is empty or all of `B₀`. -/
theorem invariant_subset_of_transitive (ρ : A → A) (B₀ S : Finset A)
    (hS : S ⊆ B₀) (hinv : S.image ρ = S)
    (htrans : ∀ x ∈ B₀, ∀ y ∈ B₀, ∃ k : ℕ, ρ^[k] x = y) :
    S = ∅ ∨ S = B₀ := by
  rcases S.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact Or.inl h
  · right
    have hiter : ∀ k : ℕ, ∀ z ∈ S, ρ^[k] z ∈ S := by
      intro k
      induction k with
      | zero => intro z hz; simpa using hz
      | succ k ih =>
        intro z hz
        rw [Function.iterate_succ', Function.comp_apply, ← hinv]
        exact Finset.mem_image_of_mem ρ (ih z hz)
    apply Finset.Subset.antisymm hS
    intro y hy
    obtain ⟨k, hk⟩ := htrans x (hS hx) y hy
    exact hk ▸ hiter k x hx

/-- **Abstract amplification lemma.**  Suppose the candidate selectors `v f`
are permuted by `σ` compatibly with `τ`, that `σ^[L] = id`, and that `τ^[L]`
maps some `B₀` onto itself transitively.  Then every `v f B₀ ⊆ B₀` is empty or
all of `B₀`: no proper nonempty selection survives. -/
theorem selection_trivial_on_transitive_block (τ : A → A) (σ : F → F)
    (v : F → Finset A → Finset A)
    (heq : ∀ f B, v (σ f) (B.image τ) = (v f B).image τ)
    (L : ℕ) (hσ : ∀ f, σ^[L] f = f)
    (B₀ : Finset A) (hB₀ : B₀.image τ^[L] = B₀)
    (htrans : ∀ x ∈ B₀, ∀ y ∈ B₀, ∃ k : ℕ, (τ^[L])^[k] x = y)
    (f : F) (hsub : v f B₀ ⊆ B₀) :
    v f B₀ = ∅ ∨ v f B₀ = B₀ := by
  have h := equivariant_iterate τ σ v heq L f B₀
  rw [hσ, hB₀] at h
  exact invariant_subset_of_transitive (τ^[L]) B₀ (v f B₀) hsub h.symm htrans

section ZModCycle

variable {n L : ℕ}

/-- The block `{0, L, 2L, …, (n-1)L}` inside the cycle `ZMod (n * L)`. -/
def block (n L : ℕ) : Finset (ZMod (n * L)) :=
  (Finset.range n).image (fun k : ℕ => ((k * L : ℕ) : ZMod (n * L)))

theorem iterate_add_one (N : ℕ) (k : ℕ) (x : ZMod N) :
    (fun y : ZMod N => y + 1)^[k] x = x + (k : ZMod N) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ, Function.comp_apply, ih]; push_cast; ring

theorem iterate_add_nat (N : ℕ) (c k : ℕ) (x : ZMod N) :
    (fun y : ZMod N => y + (c : ZMod N))^[k] x = x + ((k * c : ℕ) : ZMod N) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ, Function.comp_apply, ih]; push_cast; ring

theorem card_block (hL : 0 < L) : (block n L).card = n := by
  unfold block
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have hab' : ((a * L : ℕ) : ZMod (n * L)) = ((b * L : ℕ) : ZMod (n * L)) := hab
  rw [ZMod.natCast_eq_natCast_iff'] at hab'
  have h1 : a * L < n * L := Nat.mul_lt_mul_of_pos_right ha hL
  have h2 : b * L < n * L := Nat.mul_lt_mul_of_pos_right hb hL
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hab'
  exact Nat.eq_of_mul_eq_mul_right hL hab'

theorem mem_block {x : ZMod (n * L)} :
    x ∈ block n L ↔ ∃ k < n, x = ((k * L : ℕ) : ZMod (n * L)) := by
  unfold block
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩

theorem cast_n_mul_L : ((n : ZMod (n * L)) * (L : ZMod (n * L))) = 0 := by
  have := ZMod.natCast_self (n * L)
  push_cast at this
  exact this

/-- Every multiple of `L` lies in the block. -/
theorem mul_mem_block (hn : 0 < n) (k : ℕ) :
    ((k * L : ℕ) : ZMod (n * L)) ∈ block n L := by
  rw [mem_block]
  refine ⟨k % n, Nat.mod_lt _ hn, ?_⟩
  have hk : k * L = (k / n) * (n * L) + (k % n) * L := by
    conv_lhs => rw [← Nat.div_add_mod k n]
    ring
  rw [hk]
  push_cast
  linear_combination ((k / n : ℕ) : ZMod (n * L)) * (cast_n_mul_L (n := n) (L := L))

theorem block_image_shift (hn : 0 < n) :
    (block n L).image (fun y : ZMod (n * L) => y + 1)^[L] = block n L := by
  have hfun : (fun y : ZMod (n * L) => y + 1)^[L] = fun y => y + (L : ZMod (n * L)) := by
    funext y; exact iterate_add_one _ _ _
  rw [hfun]
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨k, -, rfl⟩ := mem_block.mp hy
    have : ((k * L : ℕ) : ZMod (n * L)) + (L : ZMod (n * L))
        = (((k + 1) * L : ℕ) : ZMod (n * L)) := by push_cast; ring
    rw [this]; exact mul_mem_block hn _
  · intro x hx
    obtain ⟨k, -, rfl⟩ := mem_block.mp hx
    rw [Finset.mem_image]
    refine ⟨(((k + (n - 1)) * L : ℕ) : ZMod (n * L)), mul_mem_block hn _, ?_⟩
    have hn1 : ((n - 1 : ℕ) : ZMod (n * L)) = (n : ZMod (n * L)) - 1 := by
      rw [Nat.cast_sub hn]; simp
    push_cast
    rw [hn1]
    linear_combination (cast_n_mul_L (n := n) (L := L))

theorem block_transitive :
    ∀ x ∈ block n L, ∀ y ∈ block n L,
      ∃ k : ℕ, ((fun y : ZMod (n * L) => y + 1)^[L])^[k] x = y := by
  have hfun : (fun y : ZMod (n * L) => y + 1)^[L] = fun y => y + (L : ZMod (n * L)) := by
    funext y; exact iterate_add_one _ _ _
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := mem_block.mp hx
  obtain ⟨b, -, rfl⟩ := mem_block.mp hy
  refine ⟨b + (n - a), ?_⟩
  rw [hfun, iterate_add_nat]
  have hna : ((n - a : ℕ) : ZMod (n * L)) = (n : ZMod (n * L)) - a := by
    rw [Nat.cast_sub ha.le]
  push_cast
  rw [hna]
  linear_combination (cast_n_mul_L (n := n) (L := L))

end ZModCycle

/-- **Finite-family amplification (synthesis Lemma 9.1(b), report R5).**
Let `F` be a nonempty set of candidate `r`-of-`n` selectors, permuted by `σ`,
and let the cycle have length `n * L` where `σ^[L] = id` (for instance
`L = (card F)!`, or `lcm(1,…,card F)`).  If the selectors are equivariant with
respect to the rotation `y ↦ y + 1` of `ZMod (n * L)`, then they cannot select
exactly `r` elements, `0 < r < n`, from every `n`-element set. -/
theorem no_equivariant_selectors {F : Type*} (n r L : ℕ) (hr : 0 < r) (hrn : r < n)
    (hL : 0 < L) (σ : F → F) (hσ : ∀ f, σ^[L] f = f) (f₀ : F)
    (v : F → Finset (ZMod (n * L)) → Finset (ZMod (n * L)))
    (hsel : ∀ f B, B.card = n → v f B ⊆ B ∧ (v f B).card = r)
    (heq : ∀ f B, v (σ f) (B.image (fun y => y + 1)) = (v f B).image (fun y => y + 1)) :
    False := by
  have hn : 0 < n := lt_trans hr hrn
  have hcard := card_block (n := n) (L := L) hL
  obtain ⟨hsub, hcr⟩ := hsel f₀ (block n L) hcard
  rcases selection_trivial_on_transitive_block (fun y => y + 1) σ v heq L hσ
      (block n L) (block_image_shift hn) block_transitive f₀ hsub with h | h
  · rw [h, Finset.card_empty] at hcr; omega
  · rw [h, hcard] at hcr; omega

/-- For a permutation `σ` of a finite type, `L = (card F)!` works as the common
exponent in `no_equivariant_selectors`. -/
theorem perm_iterate_factorial {F : Type*} [Fintype F] [DecidableEq F]
    (σ : Equiv.Perm F) (f : F) : (σ : F → F)^[(Fintype.card F).factorial] f = f := by
  have h : σ ^ (Fintype.card (Equiv.Perm F)) = 1 := pow_card_eq_one
  rw [Fintype.card_perm] at h
  have := congrArg (fun π : Equiv.Perm F => π f) h
  simpa [Equiv.Perm.iterate_eq_pow] using this

/-! ### The finite-label fixed-point test (synthesis Theorem 9.8, report R7) -/

/-- Abstract core of the finite-label obstruction: if a labelling `Lab` is
preserved by `e`, and `e a` has the same label as `π⁻¹ • a`, and `Lab` is
equivariant, then `π` fixes the label of `a`. -/
theorem label_fixed {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
    (Lab : X → Y) (hequiv : ∀ (g : G) (x : X), Lab (g • x) = g • Lab x)
    (e : X → X) (hpres : ∀ x, Lab (e x) = Lab x)
    (π : G) (a : X) (hmod : Lab (e a) = Lab (π⁻¹ • a)) :
    π • Lab a = Lab a := by
  have h : Lab a = π⁻¹ • Lab a := by rw [← hequiv, ← hmod, hpres]
  calc π • Lab a = π • (π⁻¹ • Lab a) := by rw [← h]
    _ = Lab a := by simp

end Cardinals.FiniteCycles
