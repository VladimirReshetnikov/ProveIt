import DiophantineConsistency.ArithmeticPacking
import DiophantineConsistency.ArithmeticControllerChoice

/-! **K7c — exact rank variation of the dummy bits** (construction spec §7 K1),
in every model of IΣ1.

For two packings with the same tiling word, whose cell words differ only by
dummy bits at safe blocks (`X1 j = X0 j + ρ·δ j`, `δ j ≠ 0 → j+1 < N, j+s < N`):

* `F_formula` — every packing satisfies the exact (non-modular) identity
  `F + (q−1)·(H / B^(N−1) + C / B^(N−s)) = (K + B^s)·C`, where `H = Σ B^j Hi_j`:
  the two cyclic wraps are the rotations of `ArithmeticCyclicWord.rot`;
* `variation` — the wrap terms read only blocks `≥ N−1` and `≥ N−s`, which safe
  dummies never touch, so `C1 = C0 + ρ·P` and `F1 = F0 + (K + B^s)·ρ·P`,
  `P = Σ B^j δ_j`;
* `rank_shift` — hence `R1 + (q²−1)(1 + q·(K + B^s))·ρP = R0` for the window rank
  `R = ((q−1)(q−F)+α)(q²−1) + c`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticConstructionVariation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticBinaryCarry ArithmeticRepunit
  ArithmeticPackingBlocks ArithmeticPacking

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Block sums: high parts and congruence -/

theorem bsum_congr {w : V} {f g : V → V} [𝚺₁-Function₁ f] [𝚺₁-Function₁ g] {n : V}
    (hf : ∀ j < n, f j < Exp.exp w) (hfg : ∀ j < n, f j = g j) : bsum w f n = bsum w g n := by
  have hg : ∀ j < n, g j < Exp.exp w := fun j hj => hfg j hj ▸ hf j hj
  exact bsum_unique hf ⟨bsum_lt hg, fun j hj => by rw [dig_bsum hg hj, hfg j hj]⟩

/-- The high part of a block sum is the block sum of the shifted digits. -/
theorem bsum_div {w : V} {f : V → V} [𝚺₁-Function₁ f] {n k : V} (hk : k ≤ n)
    (hf : ∀ j < n, f j < Exp.exp w) :
    bsum w f n / Exp.exp (w * k) = bsum w (fun j => f (k + j)) (n - k) := by
  haveI : 𝚺₁-Function₁ (fun j => f (k + j)) := by definability
  have hf' : ∀ j < n - k, f (k + j) < Exp.exp w := fun j hj =>
    hf _ (lt_tsub_iff_left.mp hj)
  symm
  apply bsum_unique hf'
  refine ⟨?_, fun j hj => ?_⟩
  · have hY := bsum_lt hf
    rw [show Exp.exp (w * n) = Exp.exp (w * (n - k)) * Exp.exp (w * k) by
      rw [← exp_mul_add, tsub_add_cancel_of_le hk]] at hY
    exact div_lt_of_lt_mul hY
  · unfold dig
    rw [← Arithmetic.div_mul, ← exp_mul_add]
    exact dig_bsum hf (lt_tsub_iff_left.mp hj)

/-- `rot X e + (B^n − 1)·(X / B^(n−e)) = B^e·X`. -/
theorem rot_identity (w n X e : V) (he : e ≤ n) :
    rot w n X e + (Exp.exp (w * n) - 1) * (X / Exp.exp (w * (n - e))) =
      Exp.exp (w * e) * X := ArithmeticPacking.rot_identity w n X e he

/-! ## The exact transport identity -/

section formula
variable {d K MC HP N s : V} {X : V → V} [𝚺₁-Function₁ X]
  (h : PackingInput d K MC HP N s X)
include h

theorem F_formula :
    Fw d K N s X + (Exp.exp (d * N) - 1) *
        (bsum d (hi d K X) N / Exp.exp (d * (N - 1)) + Cw d N X / Exp.exp (d * (N - s))) =
      (K + Exp.exp (d * s)) * Cw d N X := ArithmeticPacking.transport_formula h

end formula

/-! ## Safe dummy bits -/

theorem variation {d K MC HP N s ρ : V} {X0 X1 δ : V → V}
    [𝚺₁-Function₁ X0] [𝚺₁-Function₁ X1] [𝚺₁-Function₁ δ] (hd : 0 < d)
    (h0 : PackingInput d K MC HP N s X0) (h1 : PackingInput d K MC HP N s X1)
    (hρ : ρ < Exp.exp d) (hX : ∀ j < N, X1 j = X0 j + ρ * δ j) (hδ : ∀ j, δ j ≤ 1)
    (hsafe : ∀ j, δ j ≠ 0 → j + 1 < N ∧ j + s < N) :
    Cw d N X1 = Cw d N X0 + ρ * bsum d δ N ∧
      Fw d K N s X1 = Fw d K N s X0 + (K + Exp.exp (d * s)) * (ρ * bsum d δ N) := by
  have hX1 := X_lt h1
  have hρδ : ∀ j, ρ * δ j < Exp.exp d := fun j =>
    lt_of_le_of_lt (le_trans (mul_le_mul_of_nonneg_left (hδ j) (Arithmetic.zero_le _))
      (by rw [mul_one])) hρ
  haveI : 𝚺₁-Function₁ (fun j => ρ * δ j) := by definability
  haveI : 𝚺₁-Function₁ (fun _ : V => (0 : V)) := by definability
  -- C
  have hC1 : Cw d N X1 = Cw d N X0 + bsum d (fun j => ρ * δ j) N :=
    bsum_add (fun j hj => by rw [← hX j hj]; exact hX1 j hj) hX
  have hP : ρ * bsum d δ N = bsum d (fun j => ρ * δ j) N := by
    have e := bsum_mul_split (w := d) (f := δ) (n := N) ρ (lo := fun j => ρ * δ j)
      (hi := fun _ => (0 : V))
      (fun j _ => lt_of_le_of_lt (hδ j) (ArithmeticControllerData.one_lt_exp hd))
      (fun j _ => hρδ j) (fun _ _ => exp_pos d) (fun j _ => by simp)
    rw [e, ArithmeticControllerChoice.bsum_zero_fn hd (fun _ _ => rfl), mul_zero, add_zero]
  have hC : Cw d N X1 = Cw d N X0 + ρ * bsum d δ N := by rw [hC1, hP]
  refine ⟨hC, ?_⟩
  -- the wrap terms agree
  have hXtail (k : V) (hk : k ≤ N) (hs : ∀ j, δ j ≠ 0 → j + k < N)
      (j : V) (hj : j < N - (N - k)) : X1 (N - k + j) = X0 (N - k + j) := by
    have hz : δ (N - k + j) = 0 := by
      by_contra hn
      have hlt := hs (N - k + j) hn
      have hge : N ≤ N - k + j + k := by
        calc N = N - k + k := (tsub_add_cancel_of_le hk).symm
          _ ≤ N - k + j + k := add_le_add (le_add_of_nonneg_right (Arithmetic.zero_le j)) le_rfl
      exact (not_lt.mpr hge) hlt
    rw [hX (N - k + j) (lt_tsub_iff_left.mp hj), hz, mul_zero, add_zero]
  have hwrapH : bsum d (hi d K X1) N / Exp.exp (d * (N - 1)) =
      bsum d (hi d K X0) N / Exp.exp (d * (N - 1)) := by
    have hb1 : ∀ j < N, hi d K X1 j < Exp.exp d := fun j hj => by
      unfold hi; exact div_lt_of_lt_mul (h1.hi_lt j hj)
    have hb0 : ∀ j < N, hi d K X0 j < Exp.exp d := fun j hj => by
      unfold hi; exact div_lt_of_lt_mul (h0.hi_lt j hj)
    rw [bsum_div tsub_le_self hb1, bsum_div tsub_le_self hb0]
    haveI : 𝚺₁-Function₁ (fun j => hi d K X1 (N - 1 + j)) := by definability
    haveI : 𝚺₁-Function₁ (fun j => hi d K X0 (N - 1 + j)) := by definability
    apply bsum_congr (fun j hj => hb1 _ (lt_tsub_iff_left.mp hj))
    intro j hj
    unfold hi
    rw [show X1 (N - 1 + j) = X0 (N - 1 + j) from
      hXtail 1 h0.N_gt.le (fun j hj => (hsafe j hj).1) j hj]
  have hwrapC : Cw d N X1 / Exp.exp (d * (N - s)) = Cw d N X0 / Exp.exp (d * (N - s)) := by
    unfold Cw
    rw [bsum_div tsub_le_self hX1, bsum_div tsub_le_self (X_lt h0)]
    haveI : 𝚺₁-Function₁ (fun j => X1 (N - s + j)) := by definability
    haveI : 𝚺₁-Function₁ (fun j => X0 (N - s + j)) := by definability
    apply bsum_congr (fun j hj => hX1 _ (lt_tsub_iff_left.mp hj))
    intro j hj
    exact hXtail s h0.s_lt.le (fun j hj => (hsafe j hj).2) j hj
  have f1 := F_formula h1
  have f0 := F_formula h0
  rw [hwrapH, hwrapC, hC] at f1
  set W0 := bsum d (hi d K X0) N / Exp.exp (d * (N - 1)) + Cw d N X0 / Exp.exp (d * (N - s))
  apply add_right_cancel (b := (Exp.exp (d * N) - 1) * W0)
  calc Fw d K N s X1 + (Exp.exp (d * N) - 1) * W0
      = (K + Exp.exp (d * s)) * (Cw d N X0 + ρ * bsum d δ N) := f1
    _ = (K + Exp.exp (d * s)) * Cw d N X0 + (K + Exp.exp (d * s)) * (ρ * bsum d δ N) := mul_add _ _ _
    _ = Fw d K N s X0 + (Exp.exp (d * N) - 1) * W0 + (K + Exp.exp (d * s)) * (ρ * bsum d δ N) := by
        rw [← f0]
    _ = _ := by ring

/-! ## The window rank -/

/-- `R1 + (q²−1)(1+qA)·D = R0` for the window rank `R = ((q−1)(q−F)+α)(q²−1) + c`. -/
theorem rank_shift {q C0 F0 α0 C1 F1 α1 D A c : V} (hq : 1 ≤ q)
    (h0 : C0 + F0 + α0 = q) (h1 : C1 + F1 + α1 = q)
    (hC : C1 = C0 + D) (hF : F1 = F0 + A * D) :
    ((q - 1) * (q - F1) + α1) * (q ^ 2 - 1) + c + (q ^ 2 - 1) * (1 + q * A) * D =
      ((q - 1) * (q - F0) + α0) * (q ^ 2 - 1) + c := by
  have hF1q : F1 ≤ q := by
    rw [← h1, add_assoc, add_comm C1, add_assoc]
    exact le_add_of_nonneg_right (Arithmetic.zero_le _)
  have hqF : q - F0 = (q - F1) + A * D := by
    apply tsub_eq_of_eq_add
    calc q = F1 + (q - F1) := (add_tsub_cancel_of_le hF1q).symm
      _ = (q - F1) + A * D + F0 := by rw [hF]; ring
  have hα : α0 = α1 + D + A * D := by
    apply add_left_cancel (a := C0 + F0)
    calc C0 + F0 + α0 = q := h0
      _ = C1 + F1 + α1 := h1.symm
      _ = C0 + F0 + (α1 + D + A * D) := by rw [hC, hF]; ring
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, (tsub_add_cancel_of_le hq).symm⟩
  rw [hqF, hα, add_tsub_cancel_right]
  ring

end DiophantineConsistency.ArithmeticConstructionVariation
