import GowersSzemeredi.Definitions

/-! Dense graphs contain robustly connected pieces: Milićević's Lemma 4.2
(arXiv:2601.01682, p. 48, after Gowers), for walks of length six.

Let `G` be a symmetric relation on a finite type `V` with `n = |V|` and at
least `cn²` ordered edges. Write `codeg(u,v) = #{w : G u w ∧ G w v}`.

* `sum_deg_sq_eq_sum_codeg`: `Σ_w deg(w)² = Σ_{u,v} codeg(u,v)`, by symmetry.
* `exists_good_neighbourhood` (dependent random choice): there is a vertex
  `w` with `deg(w)² − M·bad(w) ≥ (c²n³ − Mεn³)/n`. Here `bad(w)` counts the
  pairs in `N(w)²` with codegree below `εn`. On average
  `Σ_w bad(w) ≤ εn³`, while `Σ_w deg(w)² ≥ (Σ_w deg(w))²/n`.

Then the vertices of `S = N(w)` with many bad partners are removed, and
any two survivors are joined by three consecutive 2-walks through good
middle vertices. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The neighbourhood of a vertex. -/
def nbhd (G : V → V → Prop) [DecidableRel G] (u : V) : Finset V := univ.filter fun v => G u v

/-- The number of walks of length two from `u` to `v`. -/
def codeg (G : V → V → Prop) [DecidableRel G] (u v : V) : Nat :=
  (univ.filter fun w => G u w ∧ G w v).card

/-- Pairs in the neighbourhood of `w` with codegree below `t`. -/
def badPairs (G : V → V → Prop) [DecidableRel G] (t : Real) (w : V) : Finset (V × V) :=
  (nbhd G w ×ˢ nbhd G w).filter fun p => (codeg G p.1 p.2 : Real) < t

/-- **Neighbourhood sizes squared count walks of length two.** -/
theorem sum_deg_sq_eq_sum_codeg (G : V → V → Prop) [DecidableRel G]
    (hsymm : ∀ u v, G u v → G v u) :
    ∑ w, ((nbhd G w).card : Real) ^ 2 = ∑ u, ∑ v, (codeg G u v : Real) := by
  have hsymm' : ∀ u v, G u v ↔ G v u := fun u v => ⟨hsymm u v, hsymm v u⟩
  have h : ∀ w, ((nbhd G w).card : Real) ^ 2 =
      ∑ u, ∑ v, (if G w u ∧ G w v then (1 : Real) else 0) := by
    intro w
    rw [sq, nbhd, Finset.card_filter, Nat.cast_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro u _
    apply Finset.sum_congr rfl; intro v _
    by_cases h1 : G w u <;> by_cases h2 : G w v <;> simp [h1, h2]
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro v _
  unfold codeg
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl; intro w _
  by_cases h1 : G u w <;> by_cases h2 : G w v <;> simp [h1, h2, hsymm' w u]

/-- Bad pairs, summed over the centre, are weighted by their codegree. -/
theorem sum_badPairs_le (G : V → V → Prop) [DecidableRel G]
    (hsymm : ∀ u v, G u v → G v u) {t : Real} (ht : 0 ≤ t) :
    ∑ w, ((badPairs G t w).card : Real) ≤ t * (Fintype.card V : Real) ^ 2 := by
  have hsymm' : ∀ u v, G u v ↔ G v u := fun u v => ⟨hsymm u v, hsymm v u⟩
  -- swap: each pair `(u,v)` with small codegree is counted `codeg(u,v)` times
  have h : ∑ w, ((badPairs G t w).card : Real) =
      ∑ p : V × V, (if (codeg G p.1 p.2 : Real) < t then (codeg G p.1 p.2 : Real) else 0) := by
    have : ∀ w, ((badPairs G t w).card : Real) = ∑ p : V × V,
        (if (codeg G p.1 p.2 : Real) < t ∧ G w p.1 ∧ G w p.2 then (1 : Real) else 0) := by
      intro w
      unfold badPairs nbhd
      rw [Finset.card_filter, Nat.cast_sum]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun p : V × V => p ∈ (univ.filter fun v => G w v) ×ˢ (univ.filter fun v => G w v))]
      have hf : (Finset.univ.filter fun p : V × V =>
          p ∈ (univ.filter fun v => G w v) ×ˢ (univ.filter fun v => G w v)) =
          (univ.filter fun v => G w v) ×ˢ (univ.filter fun v => G w v) := by
        ext p; simp
      rw [hf]
      have hzero : ∑ p ∈ Finset.univ.filter (fun p : V × V =>
          ¬ p ∈ (univ.filter fun v => G w v) ×ˢ (univ.filter fun v => G w v)),
          (if (codeg G p.1 p.2 : Real) < t ∧ G w p.1 ∧ G w p.2 then (1 : Real) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        have hp' := (Finset.mem_filter.mp hp).2
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp'
        rw [if_neg]
        tauto
      rw [hzero, add_zero]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      push_cast
      by_cases hc : (codeg G p.1 p.2 : Real) < t <;> simp [hc, hp.1, hp.2]
    simp_rw [this]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hc : (codeg G p.1 p.2 : Real) < t
    · rw [if_pos hc]
      unfold codeg at hc ⊢
      rw [Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro w _
      by_cases h1 : G w p.1 <;> by_cases h2 : G w p.2 <;> simp [hc, h1, h2, hsymm' p.1 w]
    · rw [if_neg hc]
      apply Finset.sum_eq_zero
      intro w _
      simp [hc]
  rw [h]
  calc _ ≤ ∑ _p : V × V, t := Finset.sum_le_sum fun p _ => by
        split_ifs with hc
        · exact hc.le
        · exact ht
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]; push_cast; ring

/-- **Dependent random choice.** -/
theorem exists_good_neighbourhood [Nonempty V] (G : V → V → Prop) [DecidableRel G]
    (hsymm : ∀ u v, G u v → G v u) {c t M : Real} (ht : 0 ≤ t) (hM : 0 ≤ M)
    (hedges : c * (Fintype.card V : Real) ^ 2 ≤ ∑ w, ((nbhd G w).card : Real)) (hc : 0 ≤ c) :
    ∃ w, (c ^ 2 * (Fintype.card V : Real) ^ 2 - M * t * Fintype.card V) ≤
      ((nbhd G w).card : Real) ^ 2 - M * (badPairs G t w).card := by
  have hn : (0 : Real) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  by_contra hno
  push Not at hno
  have hsum := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun w (_ : w ∈ univ) => hno w
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum] at hsum
  -- `Σ deg² ≥ (Σ deg)²/n ≥ c²n³`
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun w => ((nbhd G w).card : Real))
    (fun _ => (1 : Real))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hcs
  have hdeg0 : 0 ≤ c * (Fintype.card V : Real) ^ 2 := by positivity
  have hsq : (c * (Fintype.card V : Real) ^ 2) ^ 2 ≤ (∑ w, ((nbhd G w).card : Real)) ^ 2 :=
    pow_le_pow_left₀ hdeg0 hedges 2
  have hbad := sum_badPairs_le G hsymm ht
  have hMbad := mul_le_mul_of_nonneg_left hbad hM
  nlinarith

/-- The number of walks of length six from `u` to `v`, split at their
second and fourth vertices. -/
def walkCount6 (G : V → V → Prop) [DecidableRel G] (u v : V) : Nat :=
  ∑ z, ∑ z', codeg G u z * codeg G z z' * codeg G z' v

theorem codeg_comm (G : V → V → Prop) [DecidableRel G] (hsymm : ∀ u v, G u v → G v u)
    (u v : V) : codeg G u v = codeg G v u := by
  unfold codeg
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨hsymm _ _ h.2, hsymm _ _ h.1⟩, fun h => ⟨hsymm _ _ h.2, hsymm _ _ h.1⟩⟩

/-- Bad partners of a vertex inside a set. -/
def badPartners (G : V → V → Prop) [DecidableRel G] (t : Real) (S : Finset V) (u : V) :
    Finset V :=
  S.filter fun v => (codeg G u v : Real) < t

theorem sum_badPartners_eq (G : V → V → Prop) [DecidableRel G] (t : Real) (w : V) :
    ∑ u ∈ nbhd G w, ((badPartners G t (nbhd G w) u).card : Real) = (badPairs G t w).card := by
  unfold badPartners badPairs
  rw [Finset.card_filter, Finset.sum_product]
  push_cast
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.card_filter]
  push_cast
  rfl

/-- At least `|T| − |bad(u)|` points of `T ⊆ S` are good partners of `u`. -/
theorem card_sub_badPartners_le (G : V → V → Prop) [DecidableRel G] (t : Real) (S T : Finset V)
    (u : V) (hT : T ⊆ S) :
    (T.card : Real) - (badPartners G t S u).card ≤ (T.filter fun z => t ≤ codeg G u z).card := by
  have h : T.card ≤ (T.filter fun z => t ≤ codeg G u z).card + (badPartners G t S u).card := by
    calc T.card = (T.filter fun z => t ≤ codeg G u z).card +
          (T.filter fun z => ¬ t ≤ (codeg G u z : Real)).card :=
          (Finset.filter_card_add_filter_neg_card_eq_card _).symm
      _ ≤ _ := by
          apply Nat.add_le_add_left
          apply Finset.card_le_card
          intro z hz
          obtain ⟨hzT, hzt⟩ := Finset.mem_filter.mp hz
          exact Finset.mem_filter.mpr ⟨hT hzT, not_le.mp hzt⟩
  have : (T.card : Real) ≤ (T.filter fun z => t ≤ codeg G u z).card +
      (badPartners G t S u).card := by exact_mod_cast h
  linarith

/-- **Robust connectivity** ([Milićević, Lemma 4.2], walks of length six). -/
theorem robust_walks [Nonempty V] (G : V → V → Prop) [DecidableRel G]
    (hsymm : ∀ u v, G u v → G v u) {c : Real} (hc : 0 < c)
    (hedges : c * (Fintype.card V : Real) ^ 2 ≤ ∑ w, ((nbhd G w).card : Real)) :
    ∃ X : Finset V, c * Fintype.card V / 3 ≤ X.card ∧
      ∀ u ∈ X, ∀ v ∈ X, (9 / 64) * (c ^ 2 / 32) ^ 3 * c ^ 2 * (Fintype.card V : Real) ^ 5 ≤
        walkCount6 G u v := by
  obtain ⟨n, hn⟩ : ∃ n : Real, n = Fintype.card V := ⟨_, rfl⟩
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  rw [← hn] at hedges ⊢
  obtain ⟨t, ht⟩ : ∃ t : Real, t = c ^ 2 / 32 * n := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  obtain ⟨w, hw⟩ := exists_good_neighbourhood G hsymm ht0 (by norm_num : (0 : Real) ≤ 16)
    (by rw [← hn]; exact hedges) hc.le
  rw [← hn] at hw
  set S := nbhd G w with hS
  obtain ⟨s, hs⟩ : ∃ s : Real, s = S.card := ⟨_, rfl⟩
  rw [← hs] at hw
  have hbad0 : (0 : Real) ≤ (badPairs G t w).card := Nat.cast_nonneg _
  have h16 : 16 * t * n = c ^ 2 * n ^ 2 / 2 := by rw [ht]; ring
  have hmain : c ^ 2 * n ^ 2 / 2 + 16 * (badPairs G t w).card ≤ s ^ 2 := by
    linarith
  have hs0 : 0 ≤ s := by rw [hs]; exact Nat.cast_nonneg _
  have hsc : 2 * c * n / 3 ≤ s := by
    have h1 : (2 * c * n / 3) ^ 2 ≤ s ^ 2 := by nlinarith [sq_nonneg (c * n)]
    exact (pow_le_pow_iff_left₀ (by positivity) hs0 (by norm_num)).mp h1
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hsc
  -- the cleaned set
  let b : V → Real := fun u => ((badPartners G t S u).card : Real)
  set X := S.filter fun u => b u ≤ s / 8 with hX
  have hsumb : ∑ u ∈ S, b u ≤ s ^ 2 / 16 := by
    have := sum_badPartners_eq G t w
    rw [← hS] at this
    simp only [b]
    rw [this]
    have hcn : 0 ≤ c ^ 2 * n ^ 2 / 2 := by positivity
    linarith
  have hXcard : s / 2 ≤ X.card := by
    have hsplit := Finset.sum_filter_add_sum_filter_not S (fun u => b u ≤ s / 8) b
    have hb0 : ∀ u, 0 ≤ b u := fun u => Nat.cast_nonneg _
    have hlow : ((S.filter fun u => ¬ b u ≤ s / 8).card : Real) * (s / 8) ≤
        ∑ u ∈ S.filter (fun u => ¬ b u ≤ s / 8), b u := by
      calc ((S.filter fun u => ¬ b u ≤ s / 8).card : Real) * (s / 8) =
            ∑ _u ∈ S.filter (fun u => ¬ b u ≤ s / 8), s / 8 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun u hu => le_of_lt (not_le.mp (Finset.mem_filter.mp hu).2)
    have hfirst : 0 ≤ ∑ u ∈ S.filter (fun u => b u ≤ s / 8), b u :=
      Finset.sum_nonneg fun u _ => hb0 u
    have hcount : (X.card : Real) + (S.filter fun u => ¬ b u ≤ s / 8).card = s := by
      have hnat := Finset.card_filter_add_card_filter_not (s := S) (fun u => b u ≤ s / 8)
      have hreal : ((S.filter fun u => b u ≤ s / 8).card : Real) +
          (S.filter fun u => ¬ b u ≤ s / 8).card = S.card := by exact_mod_cast hnat
      rw [hX]
      linarith
    have hrest : ((S.filter fun u => ¬ b u ≤ s / 8).card : Real) ≤ s / 2 := by
      have : ((S.filter fun u => ¬ b u ≤ s / 8).card : Real) * (s / 8) ≤ s ^ 2 / 16 := by
        linarith
      nlinarith
    linarith
  refine ⟨X, by linarith, fun u hu v hv => ?_⟩
  obtain ⟨huS, hub⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvS, hvb⟩ := Finset.mem_filter.mp hv
  -- middle vertices
  set A := X.filter fun z => t ≤ codeg G u z with hA
  have hAcard : 3 * s / 8 ≤ A.card := by
    have := card_sub_badPartners_le G t S X u (Finset.filter_subset _ _)
    simp only [b] at hub
    linarith
  have hB : ∀ z ∈ A, 3 * s / 4 ≤
      ((S.filter fun y => t ≤ codeg G z y ∧ t ≤ codeg G y v).card : Real) := by
    intro z hz
    have hzX := (Finset.mem_filter.mp hz).1
    have hzb := (Finset.mem_filter.mp hzX).2
    simp only [b] at hzb hvb
    have h1 := card_sub_badPartners_le G t S S z subset_rfl
    have h2 := card_sub_badPartners_le G t S (S.filter fun y => t ≤ codeg G z y) v
      (Finset.filter_subset _ _)
    have heq : ((S.filter fun y => t ≤ codeg G z y).filter fun y => t ≤ codeg G v y) =
        S.filter fun y => t ≤ codeg G z y ∧ t ≤ codeg G y v := by
      ext y
      simp only [Finset.mem_filter, codeg_comm G hsymm v y]
      tauto
    rw [heq] at h2
    rw [← hs] at h1
    linarith
  -- the walk count
  have hterm : ∀ z ∈ A, ∀ y ∈ S.filter (fun y => t ≤ codeg G z y ∧ t ≤ codeg G y v),
      t ^ 3 ≤ ((codeg G u z * codeg G z y * codeg G y v : Nat) : Real) := by
    intro z hz y hy
    have h1 : t ≤ codeg G u z := (Finset.mem_filter.mp hz).2
    obtain ⟨h2, h3⟩ := (Finset.mem_filter.mp hy).2
    push_cast
    have hc1 : (0 : Real) ≤ codeg G u z := Nat.cast_nonneg _
    have hc2 : (0 : Real) ≤ codeg G z y := Nat.cast_nonneg _
    calc t ^ 3 = t * t * t := by ring
      _ ≤ (codeg G u z : Real) * codeg G z y * codeg G y v :=
          mul_le_mul (mul_le_mul h1 h2 ht0 hc1) h3 ht0 (by positivity)
  have hwalk : (A.card : Real) * (3 * s / 4) * t ^ 3 ≤ walkCount6 G u v := by
    unfold walkCount6
    push_cast
    calc (A.card : Real) * (3 * s / 4) * t ^ 3 = ∑ _z ∈ A, (3 * s / 4) * t ^ 3 := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ z ∈ A, ∑ _y ∈ S.filter (fun y => t ≤ codeg G z y ∧ t ≤ codeg G y v), t ^ 3 := by
          apply Finset.sum_le_sum; intro z hz
          rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (hB z hz) (by positivity)
      _ ≤ ∑ z ∈ A, ∑ y ∈ S.filter (fun y => t ≤ codeg G z y ∧ t ≤ codeg G y v),
            ((codeg G u z * codeg G z y * codeg G y v : Nat) : Real) :=
          Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun y hy => hterm z hz y hy
      _ ≤ ∑ z, ∑ y, ((codeg G u z * codeg G z y * codeg G y v : Nat) : Real) := by
          apply le_trans (Finset.sum_le_sum fun z _ =>
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun _ _ _ => Nat.cast_nonneg _))
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
      _ = _ := by push_cast; rfl
  have hts : (9 / 64) * (c ^ 2 / 32) ^ 3 * c ^ 2 * n ^ 5 ≤ (3 * s / 8) * (3 * s / 4) * t ^ 3 := by
    rw [ht]
    have hs2 : c ^ 2 * n ^ 2 / 2 ≤ s ^ 2 := by linarith
    have hK : (0 : Real) ≤ (c ^ 2 / 32 * n) ^ 3 := by positivity
    nlinarith
  have ht3 : (0 : Real) ≤ t ^ 3 := by positivity
  calc _ ≤ (3 * s / 8) * (3 * s / 4) * t ^ 3 := hts
    _ ≤ (A.card : Real) * (3 * s / 4) * t ^ 3 := by
        apply mul_le_mul_of_nonneg_right _ ht3
        exact mul_le_mul_of_nonneg_right hAcard (by positivity)
    _ ≤ _ := hwalk

/-- The explicit walks of length six from `u` to `v`, as tuples of their
five inner vertices `(a, z, b, y, e)`. -/
def walks6 (G : V → V → Prop) [DecidableRel G] (u v : V) : Finset (V × V × V × V × V) :=
  univ.filter fun q => G u q.1 ∧ G q.1 q.2.1 ∧ G q.2.1 q.2.2.1 ∧ G q.2.2.1 q.2.2.2.1 ∧
    G q.2.2.2.1 q.2.2.2.2 ∧ G q.2.2.2.2 v

/-- **The walk count is the number of explicit walks.** -/
theorem card_walks6 (G : V → V → Prop) [DecidableRel G] (u v : V) :
    (walks6 G u v).card = walkCount6 G u v := by
  -- regroup the five inner vertices as the split points `(z, y)` and the rest
  let e : (V × V) × (V × V × V) ≃ V × V × V × V × V :=
    { toFun := fun p => (p.2.2.2, p.1.1, p.2.2.1, p.1.2, p.2.1)
      invFun := fun q => ((q.2.1, q.2.2.2.1), (q.2.2.2.2, q.2.2.1, q.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold walks6 walkCount6 codeg
  rw [Finset.card_filter, ← Equiv.sum_comp e]
  simp only [Fintype.sum_prod_type, Finset.card_filter, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z _
  apply Finset.sum_congr rfl; intro y _
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro bb _
  apply Finset.sum_congr rfl; intro ee _
  simp only [e, Equiv.coe_fn_mk]
  by_cases h1 : G u ee <;> by_cases h2 : G ee z <;> by_cases h3 : G z bb <;>
    by_cases h4 : G bb y <;> by_cases h5 : G y a <;> by_cases h6 : G a v <;>
    simp [h1, h2, h3, h4, h5, h6]

/-- **Robust connectivity with explicit walks.** -/
theorem robust_walks_explicit [Nonempty V] (G : V → V → Prop) [DecidableRel G]
    (hsymm : ∀ u v, G u v → G v u) {c : Real} (hc : 0 < c)
    (hedges : c * (Fintype.card V : Real) ^ 2 ≤ ∑ w, ((nbhd G w).card : Real)) :
    ∃ X : Finset V, c * Fintype.card V / 3 ≤ X.card ∧
      ∀ u ∈ X, ∀ v ∈ X, (9 / 64) * (c ^ 2 / 32) ^ 3 * c ^ 2 * (Fintype.card V : Real) ^ 5 ≤
        (walks6 G u v).card := by
  obtain ⟨X, hX, hwalk⟩ := robust_walks G hsymm hc hedges
  exact ⟨X, hX, fun u hu v hv => by rw [card_walks6]; exact hwalk u hu v hv⟩

end LeanProofs.GowersSzemeredi
