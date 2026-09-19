/-
  COMBINATORIAL CORES OF THE THIRD-ROUND RESULTS (synthesis §7.4 and §13).

  Everything here is elementary and fully proved; no set theory is involved.

  * `orbit_mem_iff`, `orbit_decided`, `orbit_value_const`,
    `regressive_const_on_critical_sequence`: the two lemmas behind the internal normal
    measure (Theorems 13.2, 13.3): a set fixed by the embedding contains all or none of an
    orbit, a fixed function with fixed initial value is constant along the orbit, and a
    fixed regressive function is constant along the critical sequence.
  * `tail_ultra`: a decided set is in the tail filter iff its complement is not.
  * `phase_balance`, `no_two_valued_phase`: a shift-invariant finitely additive phase
    distribution is uniform, hence not two-valued (Theorem 13.9(c),(d)).
  * `mean_shift`, `tail_mean_indep`: a shift-invariant mean does not see the choice of
    representative (Theorem 13.9(a)).
  * `card_le_of_disjoint_meeting`: disjoint sets meeting a set `C` are at most `|C|`
    many (the size bound for the stationary seed, Theorem 7.11).
-/
import Mathlib

universe u

namespace Cardinals.ThirdRound

open Cardinal

/-! ### Tail decisions -/

/-- If `A` is fixed by `e` (in the form `e x ∈ A ↔ x ∈ A`, which is what `j(A) = A`
gives), then membership in `A` is constant along every `e`-orbit. -/
theorem orbit_mem_iff {α : Type*} (e : α → α) (A : Set α) (hA : ∀ x, e x ∈ A ↔ x ∈ A)
    (r : α) (n : ℕ) : e^[n] r ∈ A ↔ r ∈ A := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', hA, ih]

/-- A fixed set contains the whole orbit or none of it. -/
theorem orbit_decided {α : Type*} (e : α → α) (A : Set α) (hA : ∀ x, e x ∈ A ↔ x ∈ A)
    (r : α) : (∀ n, e^[n] r ∈ A) ∨ (∀ n, e^[n] r ∉ A) := by
  by_cases h : r ∈ A
  · exact Or.inl fun n => (orbit_mem_iff e A hA r n).mpr h
  · exact Or.inr fun n hn => h ((orbit_mem_iff e A hA r n).mp hn)

/-- If `f` is fixed (`f (e x) = j (f x)`) and `j` fixes the initial value `f r`, then `f`
is constant along the orbit of `r`. -/
theorem orbit_value_const {α β : Type*} (e : α → α) (j : β → β) (f : α → β)
    (hf : ∀ x, f (e x) = j (f x)) (r : α) (hfix : j (f r) = f r) (n : ℕ) :
    f (e^[n] r) = f r := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', hf, ih, hfix]

/-- A fixed function with range below the critical point is constant along every
orbit. -/
theorem small_range_const (j : Ordinal.{u} → Ordinal.{u}) (κ : Ordinal.{u})
    (hcrit : ∀ ξ < κ, j ξ = ξ) (f : Ordinal.{u} → Ordinal.{u})
    (hf : ∀ x, f (j x) = j (f x)) (hrange : ∀ x, f x < κ) (r : Ordinal.{u}) (n : ℕ) :
    f (j^[n] r) = f r :=
  orbit_value_const j j f hf r (hcrit _ (hrange r)) n

/-- **Normality.**  A fixed function that is regressive at the critical point `κ` is
constant along the critical sequence `κ, j κ, j (j κ), ...`. -/
theorem regressive_const_on_critical_sequence (j : Ordinal.{u} → Ordinal.{u})
    (κ : Ordinal.{u}) (hcrit : ∀ ξ < κ, j ξ = ξ) (f : Ordinal.{u} → Ordinal.{u})
    (hf : ∀ x, f (j x) = j (f x)) (hreg : f κ < κ) (n : ℕ) : f (j^[n] κ) = f κ :=
  orbit_value_const j j f hf κ (hcrit _ hreg) n

/-- For a set decided by the tail of `s`, being in the tail filter is equivalent to the
complement not being in it: the tail filter is an ultrafilter on the decided sets. -/
theorem tail_ultra {α : Type*} (s : ℕ → α) (A : Set α)
    (hdec : (∀ᶠ n in Filter.atTop, s n ∈ A) ∨ (∀ᶠ n in Filter.atTop, s n ∉ A)) :
    (∀ᶠ n in Filter.atTop, s n ∈ A) ↔ ¬ ∀ᶠ n in Filter.atTop, s n ∈ Aᶜ := by
  constructor
  · intro h h'
    obtain ⟨n, h1, h2⟩ := (h.and h').exists
    exact h2 h1
  · intro h
    rcases hdec with h1 | h1
    · exact h1
    · exact absurd h1 h

/-! ### Phase balance -/

/-- A shift-invariant weight on the residues modulo `m` of total mass `1` gives each
residue mass `1 / m`. -/
theorem phase_balance (m : ℕ) [NeZero m] (μ : ZMod m → ℝ) (hshift : ∀ r, μ (r + 1) = μ r)
    (hsum : ∑ r, μ r = 1) (r : ZMod m) : μ r = 1 / m := by
  have hnat : ∀ n : ℕ, μ (n : ZMod m) = μ 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, hshift, ih]
  have hconst : ∀ r, μ r = μ 0 := fun r => by
    rw [← ZMod.natCast_zmod_val r]
    exact hnat _
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hmul : μ 0 * m = 1 := by
    rw [← hsum, Finset.sum_congr rfl (fun r _ => hconst r)]
    simp [ZMod.card, mul_comm]
  rw [hconst r, eq_div_iff hm]
  exact hmul

/-- Hence no such weight is `{0,1}`-valued when `m ≥ 2`: no definable ultrafilter. -/
theorem no_two_valued_phase (m : ℕ) [NeZero m] (hm : 2 ≤ m) (μ : ZMod m → ℝ)
    (hshift : ∀ r, μ (r + 1) = μ r) (hsum : ∑ r, μ r = 1)
    (h01 : ∀ r, μ r = 0 ∨ μ r = 1) : False := by
  have h := phase_balance m μ hshift hsum 0
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < 1 / m := div_pos one_pos (by linarith)
  have hlt : (1 : ℝ) / m < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  rcases h01 0 with h0 | h1 <;> linarith

/-! ### Shift-invariant means -/

/-- A shift-invariant functional is invariant under every finite shift. -/
theorem mean_shift (M : (ℕ → ℝ) → ℝ) (hM : ∀ f, M (fun n => f (n + 1)) = M f)
    (f : ℕ → ℝ) (k : ℕ) : M (fun n => f (n + k)) = M f := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc M (fun n => f (n + (k + 1)))
        = M (fun n => (fun i => f (i + k)) (n + 1)) := by
          congr 1
          funext n
          show f _ = f _
          congr 1
          omega
      _ = M (fun i => f (i + k)) := hM (fun i => f (i + k))
      _ = M f := ih

/-- Two sequences with synchronized tails have the same mean: the tail-mean kernel
does not depend on the representative of the class. -/
theorem tail_mean_indep (M : (ℕ → ℝ) → ℝ) (hM : ∀ f, M (fun n => f (n + 1)) = M f)
    (f g : ℕ → ℝ) (k l : ℕ) (h : ∀ n, f (n + k) = g (n + l)) : M f = M g := by
  rw [← mean_shift M hM f k, ← mean_shift M hM g l]
  congr 1
  funext n
  exact h n

/-! ### The size of a stationary seed -/

/-- Pairwise disjoint sets that all meet `C` are at most `|C|` many. -/
theorem card_le_of_disjoint_meeting {ι α : Type u} (S : ι → Set α)
    (hdis : Pairwise (Function.onFun Disjoint S)) (C : Set α)
    (h : ∀ i, (S i ∩ C).Nonempty) : #ι ≤ #C := by
  choose x hx using h
  refine Cardinal.mk_le_of_injective (f := fun i => (⟨x i, (hx i).2⟩ : C)) ?_
  intro i k hik
  by_contra hne
  have heq : x i = x k := congrArg Subtype.val hik
  exact Set.disjoint_left.mp (hdis hne) (hx i).1 (heq ▸ (hx k).1)

end Cardinals.ThirdRound
