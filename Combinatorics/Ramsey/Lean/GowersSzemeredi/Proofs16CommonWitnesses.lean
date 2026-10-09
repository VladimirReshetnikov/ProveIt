import GowersSzemeredi.Proofs16MilicevicColumns

/-! Additive quadruples of columns sharing many witnesses: the counting core
of Milićević's Proposition 5.1 (iii) (arXiv:2601.01682, p. 54).

Each index `x ∈ X ⊆ ℤ/N` carries a witness set `T x` in a finite type `W`
of size `M`, with `|T x| ≥ cM`. In Proposition 5.1 the witnesses are the
quadruples `(z₁, z₂, z₃, z₄)` through which `φ_x` is represented. Milićević
uses a chain of Cauchy–Schwarz inequalities. Here the same bound comes
from a double count:
* summing over witnesses `w`, the number of pairs (additive quadruple `q`
  in `X`, witness common to all `q i`) is `Σ_w E(S_w)`, where
  `S_w = {x ∈ X : w ∈ T x}` and `E` counts additive quadruples
  (`commonWitness_sum_eq`);
* `E(S) ≥ |S|⁴/N` (`additiveCount_ge`, the constant case of
  `phiAdditiveCount_ge_of_freimanHom2`), and the power mean inequality
  `(Σ a)⁴ ≤ M³ Σ a⁴` (`sum_pow_four_le`) give the total
  `≥ c⁴|X|⁴M/N` (`commonWitness_sum_ge`);
* there are at most `N³` additive quadruples (`additive_quadruples_card_le`).
  So at least `c⁴|X|⁴/N − θN³` of them share `θM` common witnesses
  (`many_quadruples_common_witnesses`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The number of additive quadruples in a set. -/
def additiveCount {N : Nat} [NeZero N] (S : Finset (ZMod N)) : Nat :=
  phiAdditiveCount S (fun _ : ZMod N => (0 : ZMod N))

theorem freimanHom2_const_zero {N : Nat} (S : Finset (ZMod N)) :
    FreimanHom 2 S (fun _ : ZMod N => (0 : ZMod N)) := by
  rw [FreimanHom, isAddFreimanHom_two]
  exact ⟨Set.mapsTo_univ _ _, fun _ _ _ _ _ _ _ _ _ => rfl⟩

/-- **`E(S) ≥ |S|⁴/N`.** -/
theorem additiveCount_ge {N : Nat} [NeZero N] (S : Finset (ZMod N)) :
    (S.card : Real) ^ 4 ≤ N * additiveCount S := by
  unfold additiveCount
  exact phiAdditiveCount_ge_of_freimanHom2 S _ (freimanHom2_const_zero S)

/-- **Power mean.** -/
theorem sum_pow_four_le {W : Type*} [Fintype W] (a : W → Real) :
    (∑ w, a w) ^ 4 ≤ (Fintype.card W : Real) ^ 3 * ∑ w, a w ^ 4 := by
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun _ => (1 : Real))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun w => a w ^ 2) (fun _ => (1 : Real))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1 h2
  have hM : (0 : Real) ≤ Fintype.card W := Nat.cast_nonneg _
  have hsq0 : 0 ≤ ∑ w, a w ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc (∑ w, a w) ^ 4 = ((∑ w, a w) ^ 2) ^ 2 := by ring
    _ ≤ ((∑ w, a w ^ 2) * Fintype.card W) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = (Fintype.card W : Real) ^ 2 * (∑ w, a w ^ 2) ^ 2 := by ring
    _ ≤ (Fintype.card W : Real) ^ 2 * ((∑ w, (a w ^ 2) ^ 2) * Fintype.card W) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by
        rw [show (∑ w, (a w ^ 2) ^ 2) = ∑ w, a w ^ 4 from
          Finset.sum_congr rfl fun w _ => by ring]
        ring

/-- Witnesses common to all entries of a quadruple. -/
def commonWitnesses {N : Nat} {W : Type*} [Fintype W] (T : ZMod N → Finset W)
    (q : Fin 4 → ZMod N) : Finset W :=
  Finset.univ.filter fun w => ∀ i, w ∈ T (q i)

/-- The weighted count of additive quadruples in `X` with their common
witnesses. -/
def commonWitnessSum {N : Nat} [NeZero N] {W : Type*} [Fintype W] (X : Finset (ZMod N))
    (T : ZMod N → Finset W) : Nat :=
  ∑ q : Fin 4 → ZMod N,
    if (∀ i, q i ∈ X) ∧ IsAdditiveQuadruple q then (commonWitnesses T q).card else 0

/-- **The double count.** -/
theorem commonWitness_sum_eq {N : Nat} [NeZero N] {W : Type*} [Fintype W]
    (X : Finset (ZMod N)) (T : ZMod N → Finset W) :
    commonWitnessSum X T = ∑ w, additiveCount (X.filter fun x => w ∈ T x) := by
  unfold commonWitnessSum additiveCount phiAdditiveCount countWhere commonWitnesses
  simp_rw [Finset.card_filter]
  have h : ∀ q : Fin 4 → ZMod N,
      (if (∀ i, q i ∈ X) ∧ IsAdditiveQuadruple q then
        ∑ w : W, (if ∀ i, w ∈ T (q i) then 1 else 0) else 0) =
      ∑ w : W, (if IsPhiAdditive (X.filter fun x => w ∈ T x)
        (fun _ : ZMod N => (0 : ZMod N)) q then 1 else 0) := by
    intro q
    unfold IsPhiAdditive
    simp only [Finset.mem_filter, add_zero, and_true]
    split_ifs with hq
    · apply Finset.sum_congr rfl
      intro w _
      by_cases hw : ∀ i, w ∈ T (q i)
      · rw [if_pos hw, if_pos ⟨fun i => ⟨hq.1 i, hw i⟩, hq.2⟩]
      · rw [if_neg hw, if_neg (fun h => hw fun i => (h.1 i).2)]
    · symm
      apply Finset.sum_eq_zero
      intro w _
      rw [if_neg (fun h => hq ⟨fun i => (h.1 i).1, h.2⟩)]
  rw [Finset.sum_congr rfl fun q _ => h q, Finset.sum_comm]

/-- **Many common witnesses on average.** -/
theorem commonWitness_sum_ge {N : Nat} [NeZero N] {W : Type*} [Fintype W]
    (X : Finset (ZMod N)) (T : ZMod N → Finset W) {c : Real} (hc : 0 ≤ c)
    (hT : ∀ x ∈ X, c * Fintype.card W ≤ (T x).card) :
    c ^ 4 * (X.card : Real) ^ 4 * Fintype.card W ≤ N * commonWitnessSum X T := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  set M : Real := (Fintype.card W : Real) with hM
  -- `Σ_w |S_w| = Σ_{x∈X} |T x|`
  have hsum : (∑ w, ((X.filter fun x => w ∈ T x).card : Real)) =
      ∑ x ∈ X, ((T x).card : Real) := by
    have : ∑ w : W, (X.filter fun x => w ∈ T x).card = ∑ x ∈ X, (T x).card := by
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact_mod_cast this
  have hlow : (X.card : Real) * (c * M) ≤ ∑ w, ((X.filter fun x => w ∈ T x).card : Real) := by
    rw [hsum]
    calc (X.card : Real) * (c * M) = ∑ _x ∈ X, c * M := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun x hx => hT x hx
  have hpm := sum_pow_four_le (fun w => ((X.filter fun x => w ∈ T x).card : Real))
  have hE : ∀ w, ((X.filter fun x => w ∈ T x).card : Real) ^ 4 ≤
      N * additiveCount (X.filter fun x => w ∈ T x) := fun w => additiveCount_ge _
  have hEsum : ∑ w, ((X.filter fun x => w ∈ T x).card : Real) ^ 4 ≤
      N * commonWitnessSum X T := by
    rw [commonWitness_sum_eq]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => hE w
  have hA0 : 0 ≤ (X.card : Real) * (c * M) := by positivity
  have h4 : ((X.card : Real) * (c * M)) ^ 4 ≤ M ^ 3 * (N * commonWitnessSum X T) :=
    (pow_le_pow_left₀ hA0 hlow 4).trans (hpm.trans
      (mul_le_mul_of_nonneg_left hEsum (by positivity)))
  rcases (show (0 : Real) ≤ M by positivity).eq_or_lt with hM0 | hMpos
  · rw [← hM0]; simp only [mul_zero]; positivity
  · have : c ^ 4 * (X.card : Real) ^ 4 * M * M ^ 3 ≤ (N * commonWitnessSum X T) * M ^ 3 := by
      nlinarith
    exact le_of_mul_le_mul_right this (by positivity)

/-- **At most `N³` additive quadruples.** -/
theorem additive_quadruples_card_le {N : Nat} [NeZero N] :
    (Finset.univ.filter fun q : Fin 4 → ZMod N => IsAdditiveQuadruple q).card ≤ N ^ 3 := by
  have hinj : Set.InjOn (fun q : Fin 4 → ZMod N => (q 0, q 1, q 2))
      (Finset.univ.filter fun q : Fin 4 → ZMod N => IsAdditiveQuadruple q : Set _) := by
    intro q hq r hr h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hq hr
    simp only [Prod.mk.injEq] at h
    obtain ⟨h0, h1, h2⟩ := h
    have hq' : q 0 + q 1 = q 2 + q 3 := hq
    have hr' : r 0 + r 1 = r 2 + r 3 := hr
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · show q 3 = r 3
      linear_combination hr' - hq' + h0 + h1 - h2
  have h := Finset.card_le_card_of_injOn _ (fun q _ => Finset.mem_univ (q 0, q 1, q 2)) hinj
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, ZMod.card] at h
  calc _ ≤ N * (N * N) := h
    _ = N ^ 3 := by ring

/-- **Many additive quadruples share many witnesses.** -/
theorem many_quadruples_common_witnesses {N : Nat} [NeZero N] {W : Type*} [Fintype W]
    [Nonempty W] (X : Finset (ZMod N)) (T : ZMod N → Finset W) {c θ : Real} (hc : 0 ≤ c)
    (hθ : 0 ≤ θ) (hT : ∀ x ∈ X, c * Fintype.card W ≤ (T x).card) :
    c ^ 4 * (X.card : Real) ^ 4 ≤
      N * ((Finset.univ.filter fun q : Fin 4 → ZMod N => (∀ i, q i ∈ X) ∧
        IsAdditiveQuadruple q ∧ θ * Fintype.card W ≤ (commonWitnesses T q).card).card : Real) +
        θ * (N : Real) ^ 4 := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hMpos : (0 : Real) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  set M : Real := (Fintype.card W : Real) with hM
  set G := Finset.univ.filter fun q : Fin 4 → ZMod N => (∀ i, q i ∈ X) ∧
    IsAdditiveQuadruple q ∧ θ * M ≤ (commonWitnesses T q).card with hG
  have hsum := commonWitness_sum_ge X T hc hT
  have hle : ∀ q : Fin 4 → ZMod N,
      (if (∀ i, q i ∈ X) ∧ IsAdditiveQuadruple q then ((commonWitnesses T q).card : Real)
        else 0) ≤ (if q ∈ G then M else 0) + (if IsAdditiveQuadruple q then θ * M else 0) := by
    intro q
    have hcard : ((commonWitnesses T q).card : Real) ≤ M := by
      rw [hM]; exact_mod_cast Finset.card_le_univ _
    have hθM : 0 ≤ θ * M := by positivity
    by_cases hq : (∀ i, q i ∈ X) ∧ IsAdditiveQuadruple q
    · rw [if_pos hq, if_pos hq.2]
      by_cases hθq : θ * M ≤ (commonWitnesses T q).card
      · rw [if_pos (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq.1, hq.2, hθq⟩)]
        linarith
      · rw [if_neg (fun h => hθq (Finset.mem_filter.mp h).2.2.2)]
        push Not at hθq
        linarith
    · rw [if_neg hq]
      have h1 : (0 : Real) ≤ (if q ∈ G then M else 0) := by split_ifs <;> linarith
      have h2 : (0 : Real) ≤ (if IsAdditiveQuadruple q then θ * M else 0) := by
        split_ifs <;> linarith
      linarith
  have hsplit : (commonWitnessSum X T : Real) ≤ G.card * M + θ * M * (N : Real) ^ 3 := by
    unfold commonWitnessSum
    push_cast
    calc _ ≤ ∑ q : Fin 4 → ZMod N, ((if q ∈ G then M else 0) +
          (if IsAdditiveQuadruple q then θ * M else 0)) := Finset.sum_le_sum fun q _ => hle q
      _ = G.card * M + θ * M *
          ((Finset.univ.filter fun q : Fin 4 → ZMod N => IsAdditiveQuadruple q).card : Real) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
            Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
            Finset.filter_mem_eq_inter, Finset.univ_inter]
          ring
      _ ≤ _ := by
          have h := additive_quadruples_card_le (N := N)
          have h' : ((Finset.univ.filter fun q : Fin 4 → ZMod N =>
              IsAdditiveQuadruple q).card : Real) ≤ (N : Real) ^ 3 := by exact_mod_cast h
          have hθM : 0 ≤ θ * M := by positivity
          nlinarith
  have hfinal : c ^ 4 * (X.card : Real) ^ 4 * M ≤ (N * G.card + θ * (N : Real) ^ 4) * M := by
    calc c ^ 4 * (X.card : Real) ^ 4 * M ≤ N * commonWitnessSum X T := hsum
      _ ≤ N * (G.card * M + θ * M * (N : Real) ^ 3) :=
          mul_le_mul_of_nonneg_left hsplit hNR.le
      _ = _ := by ring
  exact le_of_mul_le_mul_right hfinal hMpos

end LeanProofs.GowersSzemeredi
