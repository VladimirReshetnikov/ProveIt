import OAI.Combinatorics.Progressions.Estimates.FiniteProductCellMean

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_fiber_mean_square {Ω R : Type*} [Fintype Ω] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (F : Ω → R) (e : Ω → ℝ) (r : R) :
    (p.mean (fun x => if F x = r then e x else 0)) ^ 2 ≤
      p.eventProbability (fun x => F x = r) *
        p.mean (fun x => if F x = r then e x ^ 2 else 0) := by
  have h := p.mean_mul_sq_le (fun x => if F x = r then (1 : ℝ) else 0)
    (fun x => if F x = r then e x else 0)
  have h1 : (fun x => (if F x = r then (1 : ℝ) else 0) *
      (if F x = r then e x else 0)) = (fun x => if F x = r then e x else 0) := by
    funext x; split_ifs <;> simp
  have h2 : (fun x => (if F x = r then (1 : ℝ) else 0) ^ 2) =
      (fun x => if F x = r then (1 : ℝ) else 0) := by
    funext x; split_ifs <;> norm_num
  have h3 : (fun x => (if F x = r then e x else 0) ^ 2) =
      (fun x => if F x = r then e x ^ 2 else 0) := by
    funext x; split_ifs <;> norm_num
  rw [h1, h2, h3] at h
  have hmass : p.mean (fun x => if F x = r then (1 : ℝ) else 0) =
      p.eventProbability (fun x => F x = r) := by
    unfold FiniteProbabilityWeights.eventProbability
    apply congrArg p.mean
    funext x
    split_ifs <;> rfl
  rw [hmass] at h
  exact h

theorem finite_fiber_energy_sum {Ω R : Type*} [Fintype Ω] [Fintype R] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (F : Ω → R) (e : Ω → ℝ) :
    (∑ r, p.mean (fun x => if F x = r then e x ^ 2 else 0)) =
      p.mean (fun x => e x ^ 2) := by
  rw [← p.mean_sum]
  congr 1
  funext x
  simp

theorem finite_fiber_square_sum_le {Ω R : Type*}
    [Fintype Ω] [Fintype R] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (F : Ω → R) (e : Ω → ℝ) {c : ℝ}
    (hmass : ∀ r, p.eventProbability (fun x => F x = r) ≤ c) :
    (∑ r, (p.mean (fun x => if F x = r then e x else 0)) ^ 2) ≤
      c * p.mean (fun x => e x ^ 2) := by
  calc
    _ ≤ ∑ r, c * p.mean (fun x => if F x = r then e x ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro r _
      apply (finite_fiber_mean_square p F e r).trans
      exact mul_le_mul_of_nonneg_right (hmass r)
        (p.mean_nonneg (fun x => by split_ifs; exact sq_nonneg _; exact le_rfl))
    _ = _ := by rw [← Finset.mul_sum, finite_fiber_energy_sum]

theorem finite_residue_energy_bound {Ω R : Type*}
    [Fintype Ω] [Fintype R] [Nonempty R] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (F : Ω → R) (e : Ω → ℝ) {K : ℝ}
    (hmass : ∀ r, p.eventProbability (fun x => F x = r) ≤ K / Fintype.card R) :
    (Fintype.card R : ℝ) *
        (∑ r, (p.mean (fun x => if F x = r then |e x| else 0)) ^ 2) ≤
      K * p.mean (fun x => e x ^ 2) := by
  have hcard : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have h := finite_fiber_square_sum_le p F (fun x => |e x|) hmass
  simp only [sq_abs] at h
  calc
    _ ≤ (Fintype.card R : ℝ) * ((K / Fintype.card R) * p.mean (fun x => e x ^ 2)) :=
      mul_le_mul_of_nonneg_left h hcard.le
    _ = _ := by field_simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_matching_residue_mean {X Y R : Type*}
    [Fintype X] [Fintype Y] [Fintype R] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (F : X → R) (G : Y → R) (e : X → ℝ) (d : Y → ℝ) :
    p.mean (fun x => q.mean (fun y => if F x = G y then |e x| * |d y| else 0)) =
      ∑ r, p.mean (fun x => if F x = r then |e x| else 0) *
        q.mean (fun y => if G y = r then |d y| else 0) := by
  have hpoint (x : X) (y : Y) :
      (if F x = G y then |e x| * |d y| else 0) =
        ∑ r, (if F x = r then |e x| else 0) * (if G y = r then |d y| else 0) := by
    symm
    rw [Finset.sum_eq_single (F x)]
    · by_cases h : F x = G y <;> simp [h, eq_comm]
    · intro r _ hr
      simp [Ne.symm hr]
    · simp
  simp_rw [hpoint, q.mean_sum, p.mean_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [q.mean_const_mul, p.mean_mul_const]

theorem finite_matching_residue_energy {X Y R : Type*}
    [Fintype X] [Fintype Y] [Fintype R] [Nonempty R] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (F : X → R) (G : Y → R) (e : X → ℝ) (d : Y → ℝ) {K : ℝ}
    (hp : ∀ r, p.eventProbability (fun x => F x = r) ≤ K / Fintype.card R)
    (hq : ∀ r, q.eventProbability (fun y => G y = r) ≤ K / Fintype.card R) :
    (Fintype.card R : ℝ) *
        p.mean (fun x => q.mean (fun y => if F x = G y then |e x| * |d y| else 0)) ≤
      K / 2 * (p.mean (fun x => e x ^ 2) + q.mean (fun y => d y ^ 2)) := by
  rw [finite_matching_residue_mean]
  have he := finite_residue_energy_bound p F e hp
  have hd := finite_residue_energy_bound q G d hq
  have hs : 2 * (∑ r, p.mean (fun x => if F x = r then |e x| else 0) *
      q.mean (fun y => if G y = r then |d y| else 0)) ≤
      (∑ r, (p.mean (fun x => if F x = r then |e x| else 0)) ^ 2) +
      (∑ r, (q.mean (fun y => if G y = r then |d y| else 0)) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    nlinarith [sq_nonneg (p.mean (fun x => if F x = r then |e x| else 0) -
      q.mean (fun y => if G y = r then |d y| else 0))]
  have hscaled := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) (Fintype.card R))
  nlinarith only [hscaled, he, hd]

theorem finite_matching_kernel_error {X Y R : Type*}
    [Fintype X] [Fintype Y] [Fintype R] [Nonempty R] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (F : X → R) (G : Y → R) (e : X → ℝ) (d : Y → ℝ) (k : X → Y → ℝ)
    {K epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hp : ∀ r, p.eventProbability (fun x => F x = r) ≤ K / Fintype.card R)
    (hq : ∀ r, q.eventProbability (fun y => G y = r) ≤ K / Fintype.card R)
    (hk : ∀ x y, F x = G y → |k x y| ≤ epsilon) :
    (Fintype.card R : ℝ) *
        |p.mean (fun x => q.mean (fun y => if F x = G y then k x y * e x * d y else 0))| ≤
      epsilon * (K / 2 * (p.mean (fun x => e x ^ 2) + q.mean (fun y => d y ^ 2))) := by
  have ha : |p.mean (fun x => q.mean (fun y => if F x = G y then k x y * e x * d y else 0))| ≤
      epsilon * p.mean (fun x => q.mean (fun y => if F x = G y then |e x| * |d y| else 0)) := by
    apply (p.abs_mean_le_mean_abs _).trans
    rw [← p.mean_const_mul]
    apply p.mean_mono
    intro x
    apply (q.abs_mean_le_mean_abs _).trans
    rw [← q.mean_const_mul]
    apply q.mean_mono
    intro y
    by_cases h : F x = G y
    · simp only [h, ite_true, abs_mul]
      calc
        _ = |k x y| * (|e x| * |d y|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hk x y h) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · simp [h]
  calc
    _ ≤ (Fintype.card R : ℝ) * (epsilon *
        p.mean (fun x => q.mean (fun y => if F x = G y then |e x| * |d y| else 0))) :=
      mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg _)
    _ = epsilon * ((Fintype.card R : ℝ) *
        p.mean (fun x => q.mean (fun y => if F x = G y then |e x| * |d y| else 0))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_matching_residue_energy p q F G e d hp hq) hepsilon

theorem finite_matching_kernel_approximation {X Y R : Type*}
    [Fintype X] [Fintype Y] [Fintype R] [Nonempty R] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (F : X → R) (G : Y → R) (e : X → ℝ) (d : Y → ℝ) (k l : X → Y → ℝ)
    {K epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hp : ∀ r, p.eventProbability (fun x => F x = r) ≤ K / Fintype.card R)
    (hq : ∀ r, q.eventProbability (fun y => G y = r) ≤ K / Fintype.card R)
    (hk : ∀ x y, F x = G y → |k x y - l x y| ≤ epsilon) :
    |(Fintype.card R : ℝ) *
        p.mean (fun x => q.mean (fun y => if F x = G y then k x y * e x * d y else 0)) -
      (Fintype.card R : ℝ) *
        p.mean (fun x => q.mean (fun y => if F x = G y then l x y * e x * d y else 0))| ≤
      epsilon * (K / 2 * (p.mean (fun x => e x ^ 2) + q.mean (fun y => d y ^ 2))) := by
  have hid : p.mean (fun x => q.mean (fun y =>
      if F x = G y then (k x y - l x y) * e x * d y else 0)) =
      p.mean (fun x => q.mean (fun y => if F x = G y then k x y * e x * d y else 0)) -
      p.mean (fun x => q.mean (fun y => if F x = G y then l x y * e x * d y else 0)) := by
    rw [← p.mean_sub]
    apply congrArg p.mean
    funext x
    rw [← q.mean_sub]
    apply congrArg q.mean
    funext y
    split_ifs <;> ring
  rw [← mul_sub, ← hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact finite_matching_kernel_error p q F G e d (fun x y => k x y - l x y) hepsilon hp hq hk

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_cell_residue_kernel_expand {X Y A B R : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (C : X → A) (D : Y → B) (F : X → R) (G : Y → R)
    (e : X → ℝ) (d : Y → ℝ) (k : A → B → R → ℝ) :
    p.mean (fun x => q.mean (fun y => if F x = G y then k (C x) (D y) (F x) * e x * d y else 0)) =
      ∑ r, ∑ a, ∑ b, k a b r * finiteCellResidueMean p C F e a r * finiteCellResidueMean q D G d b r := by
  have hpoint (x : X) (y : Y) :
      (if F x = G y then k (C x) (D y) (F x) * e x * d y else 0) =
      ∑ r, ∑ a, ∑ b, k a b r * (if C x = a ∧ F x = r then e x else 0) *
        (if D y = b ∧ G y = r then d y else 0) := by
    symm
    rw [Finset.sum_eq_single (F x)]
    · rw [Finset.sum_eq_single (C x)]
      · rw [Finset.sum_eq_single (D y)]
        · by_cases h : F x = G y <;> simp [h, eq_comm]
        · intro b _ hb
          simp [Ne.symm hb]
        · simp
      · intro a _ ha
        simp [Ne.symm ha]
      · simp
    · intro r _ hr
      simp [Ne.symm hr]
    · simp
  simp_rw [hpoint, q.mean_sum, p.mean_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [finiteCellResidueMean, q.mean_const_mul, p.mean_mul_const, p.mean_const_mul]

theorem weighted_cell_residue_cancellation {A B R : Type*}
    [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    (p : FiniteProbabilityWeights A) (q : FiniteProbabilityWeights B)
    (e : A → R → ℝ) (d : B → R → ℝ) (k : A → B → R → ℝ)
    {delta gamma L : ℝ} (hdelta : 0 ≤ delta) (hL : 0 ≤ L)
    (he : ∀ a r, |e a r| ≤ p.weight a * delta / Fintype.card R)
    (hd : ∀ b r, |d b r| ≤ q.weight b * gamma / Fintype.card R)
    (hk : ∀ a b r, |k a b r| ≤ L) :
    |(Fintype.card R : ℝ) * ∑ r, ∑ a, ∑ b, k a b r * e a r * d b r| ≤ L * delta * gamma := by
  let N : ℝ := Fintype.card R
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast Fintype.card_pos
  have hterm (a : A) (b : B) (r : R) :
      |k a b r * e a r * d b r| ≤ (L * delta * gamma / N ^ 2) * (p.weight a * q.weight b) := by
    rw [abs_mul, abs_mul]
    have h := mul_le_mul (mul_le_mul (hk a b r) (he a r) (abs_nonneg _) hL)
      (hd b r) (abs_nonneg _) (mul_nonneg hL (div_nonneg (mul_nonneg (p.nonneg a) hdelta) hN.le))
    apply h.trans_eq
    dsimp only [N]
    ring
  have hs : |∑ r, ∑ a, ∑ b, k a b r * e a r * d b r| ≤
      ∑ _r : R, ∑ a, ∑ b, (L * delta * gamma / N ^ 2) * (p.weight a * q.weight b) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro r _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro a _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun b _ => hterm a b r)
  have hsum : (∑ _r : R, ∑ a, ∑ b, (L * delta * gamma / N ^ 2) * (p.weight a * q.weight b)) =
      N * (L * delta * gamma / N ^ 2) := by
    simp only [← mul_assoc, ← Finset.mul_sum, q.total, p.total, mul_one,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, N]
  change |N * _| ≤ _
  rw [abs_mul, abs_of_pos hN]
  calc
    _ ≤ N * (N * (L * delta * gamma / N ^ 2)) :=
      mul_le_mul_of_nonneg_left (hs.trans_eq hsum) hN.le
    _ = _ := by field_simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_cell_kernel_cancellation {X Y A B R : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (C : X → A) (D : Y → B) (F : X → R) (G : Y → R)
    (e : X → ℝ) (d : Y → ℝ) (k : A → B → R → ℝ)
    {delta gamma L : ℝ} (hdelta : 0 ≤ delta) (hL : 0 ≤ L)
    (he : ∀ a r, |finiteCellResidueMean p C F e a r| ≤
      (finiteCellWeights p C).weight a * delta / Fintype.card R)
    (hd : ∀ b r, |finiteCellResidueMean q D G d b r| ≤
      (finiteCellWeights q D).weight b * gamma / Fintype.card R)
    (hk : ∀ a b r, |k a b r| ≤ L) :
    |(Fintype.card R : ℝ) * p.mean
      (fun x => q.mean (fun y => if F x = G y then k (C x) (D y) (F x) * e x * d y else 0))| ≤
      L * delta * gamma := by
  rw [finite_cell_residue_kernel_expand]
  exact weighted_cell_residue_cancellation (finiteCellWeights p C) (finiteCellWeights q D)
    (finiteCellResidueMean p C F e) (finiteCellResidueMean q D G d) k hdelta hL he hd hk

theorem finite_cell_kernel_correlation {X Y A B R : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (C : X → A) (D : Y → B) (F : X → R) (G : Y → R)
    (e : X → ℝ) (d : Y → ℝ) (k : X → Y → ℝ) (cell : A → B → R → ℝ)
    {delta gamma L K zeta : ℝ} (hdelta : 0 ≤ delta) (hL : 0 ≤ L) (hzeta : 0 ≤ zeta)
    (hp : ∀ r, p.eventProbability (fun x => F x = r) ≤ K / Fintype.card R)
    (hq : ∀ r, q.eventProbability (fun y => G y = r) ≤ K / Fintype.card R)
    (he : ∀ a r, |finiteCellResidueMean p C F e a r| ≤
      (finiteCellWeights p C).weight a * delta / Fintype.card R)
    (hd : ∀ b r, |finiteCellResidueMean q D G d b r| ≤
      (finiteCellWeights q D).weight b * gamma / Fintype.card R)
    (hcell : ∀ a b r, |cell a b r| ≤ L)
    (hgrid : ∀ x y, F x = G y → |k x y - cell (C x) (D y) (F x)| ≤ zeta) :
    |(Fintype.card R : ℝ) * p.mean
      (fun x => q.mean (fun y => if F x = G y then k x y * e x * d y else 0))| ≤
      L * delta * gamma + zeta * (K / 2 * (p.mean (fun x => e x ^ 2) + q.mean (fun y => d y ^ 2))) := by
  have herror := finite_matching_kernel_approximation p q F G e d k
    (fun x y => cell (C x) (D y) (F x)) hzeta hp hq hgrid
  have hmain := finite_cell_kernel_cancellation p q C D F G e d cell hdelta hL he hd hcell
  have htriangle := abs_add_le
    ((Fintype.card R : ℝ) * p.mean
      (fun x => q.mean (fun y => if F x = G y then k x y * e x * d y else 0)) -
      (Fintype.card R : ℝ) * p.mean
      (fun x => q.mean (fun y => if F x = G y then cell (C x) (D y) (F x) * e x * d y else 0)))
    ((Fintype.card R : ℝ) * p.mean
      (fun x => q.mean (fun y => if F x = G y then cell (C x) (D y) (F x) * e x * d y else 0)))
  rw [sub_add_cancel] at htriangle
  exact (htriangle.trans (add_le_add herror hmain)).trans_eq (add_comm _ _)

end Erdos3

end

end OAI
