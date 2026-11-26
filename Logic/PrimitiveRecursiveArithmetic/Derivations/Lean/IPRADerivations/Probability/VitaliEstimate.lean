import IPRADerivations.Probability.Expectation
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Fubini

/-!
# The Vitali truncation estimate and bounded convergence

Packet: `probability/expected_value_ipra_2026-11-16`, `paper/sections/12_convergence.tex`, Theorem `thm:vitali`
("Effective convergence in probability plus effective uniform integrability of `(X_n)` and the limit `X` implies
effective `L¹` convergence"), whose proof uses `lem:truncation` "with separate tail bounds for `X_n` and `X`":
`|X_n − X| ≤ |X_n − X| 1_{|X_n| ≤ K, |X| ≤ K} + |X_n| 1_{|X_n| > K} + |X| 1_{|X| > K}`; and Corollary
`cor:bounded-convergence`: "Directly, `E|X_n − X| ≤ η + 2M P(|X_n − X| > η)`".

For a finite weighted law with weights `w(i, x)`, the distance `d = |X_n − X|`, the sizes `a = |X_n|`, `b = |X|`
with `d ≤ a + b`, and bodies `e₁, e₂, e₃` that are `1` on `{d > η}`, `{a > K}`, `{b > K}` (in particular the
indicators):

* `vitali_pt`: `w d ≤ η w + 2K w e₁ + w a e₂ + w b e₃`, by the regions `d ≤ η` and, for `d > η`, the four
  combinations of `a ≶ K`, `b ≶ K`;
* `vitali`: `Σ w d ≤ η Σ w + 2K Σ w e₁ + Σ w a e₂ + Σ w b e₃`, i.e.
  `E|X_n − X| ≤ η + 2K P(|X_n − X| > η) + E[|X_n| 1_{|X_n|>K}] + E[|X| 1_{|X|>K}]`: the two uniform-integrability
  tails and the convergence-in-probability term control the `L¹` distance;
* `bounded_convergence` (`cor:bounded-convergence`): if `a, b ≤ M` then `Σ w d ≤ η Σ w + 2M Σ w e₁`.

The division by the total weight and the refinement argument for effective names are not derived (as for
`TruncationEstimate`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.VitaliEstimate

open_ipra
open LeanProofs.IPRA.Probability.Expectation (inst2_mul')

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The pointwise Vitali inequality, by the regions `d ≤ η` and the four tail combinations. -/
theorem vitali_pt {w d a b η K e₁ e₂ e₃ : PTm n}
    (hd : Γ ⊢[PRAAx] le d (a + b))
    (h₁ : Γ ⊢[PRAAx] lt η d ⟶ (e₁ ≐ one))
    (h₂ : Γ ⊢[PRAAx] lt K a ⟶ (e₂ ≐ one))
    (h₃ : Γ ⊢[PRAAx] lt K b ⟶ (e₃ ≐ one)) :
    Γ ⊢[PRAAx] le (w * d) (η * w + two * K * (w * e₁) + w * (a * e₂) + w * (b * e₃)) := by
  refine .orE (lt_or_le η d) ?_ ?_
  · let C : List (Fm PTm n) := lt η d :: Γ
    have E₁ : C ⊢[PRAAx] e₁ ≐ one := Prf.impE h₁.wk Prf.hyp0
    have hd₁ : C ⊢[PRAAx] le d (a + b) := hd.wk
    have h₂₁ : C ⊢[PRAAx] lt K a ⟶ (e₂ ≐ one) := h₂.wk
    have h₃₁ : C ⊢[PRAAx] lt K b ⟶ (e₃ ≐ one) := h₃.wk
    refine .orE (lt_or_le K a) ?_ ?_
    · let C₂ : List (Fm PTm n) := lt K a :: C
      have E₂ : C₂ ⊢[PRAAx] e₂ ≐ one := Prf.impE h₂₁.wk Prf.hyp0
      have E₁' : C₂ ⊢[PRAAx] e₁ ≐ one := E₁.wk
      have hd₂ : C₂ ⊢[PRAAx] le d (a + b) := hd₁.wk
      have h₃₂ : C₂ ⊢[PRAAx] lt K b ⟶ (e₃ ≐ one) := h₃₁.wk
      refine .orE (lt_or_le K b) ?_ ?_
      · have E₃ := natEq (Prf.impE h₃₂.wk Prf.hyp0 : (lt K b :: C₂) ⊢[PRAAx] e₃ ≐ one)
        have a₂ := natEq (E₂.wk : (lt K b :: C₂) ⊢[PRAAx] e₂ ≐ one)
        have hd₃ : (lt K b :: C₂) ⊢[PRAAx] le d (a + b) := hd₂.wk
        ipra_le 𝔟 η * 𝔟 w + 2 * 𝔟 K * (𝔟 w * 𝔟 e₁) + 𝔟 w * sl hd₃ using
          linear_combination 𝔟 w * 𝔟 a * a₂ + 𝔟 w * 𝔟 b * E₃
      · have hbK : (le b K :: C₂) ⊢[PRAAx] le b K := Prf.hyp0
        have a₁ := natEq (E₁'.wk : (le b K :: C₂) ⊢[PRAAx] e₁ ≐ one)
        have a₂ := natEq (E₂.wk : (le b K :: C₂) ⊢[PRAAx] e₂ ≐ one)
        have hd₃ : (le b K :: C₂) ⊢[PRAAx] le d (a + b) := hd₂.wk
        ipra_le 𝔟 η * 𝔟 w + 𝔟 w * sl hd₃ + 𝔟 w * sl hbK + 𝔟 K * 𝔟 w + 𝔟 w * (𝔟 b * 𝔟 e₃) using
          linear_combination 2 * 𝔟 K * 𝔟 w * a₁ + 𝔟 w * 𝔟 a * a₂
    · let C₂ : List (Fm PTm n) := le a K :: C
      have haK : C₂ ⊢[PRAAx] le a K := Prf.hyp0
      have E₁' : C₂ ⊢[PRAAx] e₁ ≐ one := E₁.wk
      have hd₂ : C₂ ⊢[PRAAx] le d (a + b) := hd₁.wk
      have h₃₂ : C₂ ⊢[PRAAx] lt K b ⟶ (e₃ ≐ one) := h₃₁.wk
      refine .orE (lt_or_le K b) ?_ ?_
      · have E₃ := natEq (Prf.impE h₃₂.wk Prf.hyp0 : (lt K b :: C₂) ⊢[PRAAx] e₃ ≐ one)
        have a₁ := natEq (E₁'.wk : (lt K b :: C₂) ⊢[PRAAx] e₁ ≐ one)
        have hd₃ : (lt K b :: C₂) ⊢[PRAAx] le d (a + b) := hd₂.wk
        have haK' : (lt K b :: C₂) ⊢[PRAAx] le a K := haK.wk
        ipra_le 𝔟 η * 𝔟 w + 𝔟 w * sl hd₃ + 𝔟 w * sl haK' + 𝔟 K * 𝔟 w + 𝔟 w * (𝔟 a * 𝔟 e₂) using
          linear_combination 2 * 𝔟 K * 𝔟 w * a₁ + 𝔟 w * 𝔟 b * E₃
      · have hbK : (le b K :: C₂) ⊢[PRAAx] le b K := Prf.hyp0
        have a₁ := natEq (E₁'.wk : (le b K :: C₂) ⊢[PRAAx] e₁ ≐ one)
        have hd₃ : (le b K :: C₂) ⊢[PRAAx] le d (a + b) := hd₂.wk
        have haK' : (le b K :: C₂) ⊢[PRAAx] le a K := haK.wk
        ipra_le 𝔟 η * 𝔟 w + 𝔟 w * sl hd₃ + 𝔟 w * sl haK' + 𝔟 w * sl hbK + 𝔟 w * (𝔟 a * 𝔟 e₂) +
            𝔟 w * (𝔟 b * 𝔟 e₃) using
          linear_combination 2 * 𝔟 K * 𝔟 w * a₁
  · have hdη : (le d η :: Γ) ⊢[PRAAx] le d η := Prf.hyp0
    ipra_le 𝔟 w * sl hdη + 2 * 𝔟 K * (𝔟 w * 𝔟 e₁) + 𝔟 w * (𝔟 a * 𝔟 e₂) + 𝔟 w * (𝔟 b * 𝔟 e₃)

section Sums

variable (w d a b e₁ e₂ e₃ : PTm 2)

/-- The invariant at the length `J`. -/
abbrev VInv (η K J x : PTm n) : Fm PTm n :=
  le (ap2 (sumF (w * d)) J x)
    (η * ap2 (sumF w) J x + two * K * ap2 (sumF (w * e₁)) J x + ap2 (sumF (w * (a * e₂))) J x +
      ap2 (sumF (w * (b * e₃))) J x)

theorem vitali_base (η K x : PTm n) : Γ ⊢[PRAAx] VInv w d a b e₁ e₂ e₃ η K zero x := by
  have z₀ := natEq (sum_zero (Γ := Γ) (w * d) x)
  have z₁ := natEq (sum_zero (Γ := Γ) w x)
  have z₂ := natEq (sum_zero (Γ := Γ) (w * e₁) x)
  have z₃ := natEq (sum_zero (Γ := Γ) (w * (a * e₂)) x)
  have z₄ := natEq (sum_zero (Γ := Γ) (w * (b * e₃)) x)
  ipra_le 0 using linear_combination 𝔟 η * z₁ + 2 * 𝔟 K * z₂ + z₃ + z₄ - z₀

theorem vitali_step {η K J x : PTm n}
    (hpt : Γ ⊢[PRAAx] le (inst2 w J x * inst2 d J x)
      (η * inst2 w J x + two * K * (inst2 w J x * inst2 e₁ J x) +
        inst2 w J x * (inst2 a J x * inst2 e₂ J x) + inst2 w J x * (inst2 b J x * inst2 e₃ J x)))
    (ih : Γ ⊢[PRAAx] VInv w d a b e₁ e₂ e₃ η K J x) :
    Γ ⊢[PRAAx] VInv w d a b e₁ e₂ e₃ η K (succ J) x := by
  have s₀ := sum_succ' (Γ := Γ) (w * d) J x
  rw [inst2_mul'] at s₀
  have s₂ := sum_succ' (Γ := Γ) (w * e₁) J x
  rw [inst2_mul'] at s₂
  have s₃ := sum_succ' (Γ := Γ) (w * (a * e₂)) J x
  rw [inst2_mul', inst2_mul'] at s₃
  have s₄ := sum_succ' (Γ := Γ) (w * (b * e₃)) J x
  rw [inst2_mul', inst2_mul'] at s₄
  have a₀ := natEq s₀
  have a₁ := natEq (sum_succ' (Γ := Γ) w J x)
  have a₂ := natEq s₂
  have a₃ := natEq s₃
  have a₄ := natEq s₄
  ipra_le sl ih + sl hpt using linear_combination 𝔟 η * a₁ + 2 * 𝔟 K * a₂ + a₃ + a₄ - a₀

theorem vitali_guard {η K J N x : PTm n}
    (hJ : Γ ⊢[PRAAx] le (succ J) N)
    (hd : Γ ⊢[PRAAx] lt J N ⟶ le (inst2 d J x) (inst2 a J x + inst2 b J x))
    (h₁ : Γ ⊢[PRAAx] lt J N ⟶ (lt η (inst2 d J x) ⟶ (inst2 e₁ J x ≐ one)))
    (h₂ : Γ ⊢[PRAAx] lt J N ⟶ (lt K (inst2 a J x) ⟶ (inst2 e₂ J x ≐ one)))
    (h₃ : Γ ⊢[PRAAx] lt J N ⟶ (lt K (inst2 b J x) ⟶ (inst2 e₃ J x ≐ one)))
    (ih : Γ ⊢[PRAAx] le J N ⟶ VInv w d a b e₁ e₂ e₃ η K J x) :
    Γ ⊢[PRAAx] VInv w d a b e₁ e₂ e₃ η K (succ J) x :=
  vitali_step w d a b e₁ e₂ e₃
    (vitali_pt (Prf.impE hd hJ) (Prf.impE h₁ hJ) (Prf.impE h₂ hJ) (Prf.impE h₃ hJ))
    (Prf.impE ih (le_trans (le_succ_self J) hJ))

theorem vitali_all {η K N x : PTm n}
    (hd : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 d (var 0) (Syn.shift x)) (inst2 a (var 0) (Syn.shift x) + inst2 b (var 0) (Syn.shift x))))
    (h₁ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (lt (Syn.shift η) (inst2 d (var 0) (Syn.shift x)) ⟶ (inst2 e₁ (var 0) (Syn.shift x) ≐ one))))
    (h₂ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (lt (Syn.shift K) (inst2 a (var 0) (Syn.shift x)) ⟶ (inst2 e₂ (var 0) (Syn.shift x) ≐ one))))
    (h₃ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (lt (Syn.shift K) (inst2 b (var 0) (Syn.shift x)) ⟶ (inst2 e₃ (var 0) (Syn.shift x) ≐ one)))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      VInv w d a b e₁ e₂ e₃ (Syn.shift η) (Syn.shift K) (var 0) (Syn.shift x)) := by
  refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
  · have e : (le (var 0) (Syn.shift N) ⟶
          VInv w d a b e₁ e₂ e₃ (Syn.shift η) (Syn.shift K) (var 0) (Syn.shift x)).subst (Syn.inst zero) =
        (le zero N ⟶ VInv w d a b e₁ e₂ e₃ η K zero x) := by
      simp
    rw [e]
    exact .impI (vitali_base w d a b e₁ e₂ e₃ η K x)
  · have e : (le (var 0) (Syn.shift N) ⟶
          VInv w d a b e₁ e₂ e₃ (Syn.shift η) (Syn.shift K) (var 0) (Syn.shift x)).subst
          (Syn.repl (succ (var 0))) =
        (le (succ (var 0)) (Syn.shift N) ⟶
          VInv w d a b e₁ e₂ e₃ (Syn.shift η) (Syn.shift K) (succ (var 0)) (Syn.shift x)) := by
      simp
    rw [e]
    exact .impI (vitali_guard w d a b e₁ e₂ e₃ Prf.hyp0 hd.allOpen.wk.wk h₁.allOpen.wk.wk h₂.allOpen.wk.wk
      h₃.allOpen.wk.wk Prf.hyp1)

/-- `thm:vitali`, finite core: `Σ w d ≤ η Σ w + 2K Σ w e₁ + Σ w a e₂ + Σ w b e₃`, the sums over `i < N`. -/
theorem vitali {η K N x : PTm n}
    (hd : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 d (var 0) (Syn.shift x)) (inst2 a (var 0) (Syn.shift x) + inst2 b (var 0) (Syn.shift x))))
    (h₁ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (lt (Syn.shift η) (inst2 d (var 0) (Syn.shift x)) ⟶ (inst2 e₁ (var 0) (Syn.shift x) ≐ one))))
    (h₂ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (lt (Syn.shift K) (inst2 a (var 0) (Syn.shift x)) ⟶ (inst2 e₂ (var 0) (Syn.shift x) ≐ one))))
    (h₃ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (lt (Syn.shift K) (inst2 b (var 0) (Syn.shift x)) ⟶ (inst2 e₃ (var 0) (Syn.shift x) ≐ one)))) :
    Γ ⊢[PRAAx] VInv w d a b e₁ e₂ e₃ η K N x := by
  have h := Prf.allE N (vitali_all w d a b e₁ e₂ e₃ hd h₁ h₂ h₃)
  have e : (le (var 0) (Syn.shift N) ⟶
        VInv w d a b e₁ e₂ e₃ (Syn.shift η) (Syn.shift K) (var 0) (Syn.shift x)).subst (Syn.inst N) =
      (le N N ⟶ VInv w d a b e₁ e₂ e₃ η K N x) := by
    simp
  rw [e] at h
  exact Prf.impE h (le_refl N)

end Sums

/-! ## Bounded convergence -/

/-- `cor:bounded-convergence`: with `|X_n|, |X| ≤ M` (`a, b ≤ M`), `Σ w d ≤ η Σ w + 2M Σ w e₁`. -/
theorem bounded_convergence (w d a b e₁ : PTm 2) {η M N x : PTm n}
    (hd : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 d (var 0) (Syn.shift x)) (inst2 a (var 0) (Syn.shift x) + inst2 b (var 0) (Syn.shift x))))
    (h₁ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (lt (Syn.shift η) (inst2 d (var 0) (Syn.shift x)) ⟶ (inst2 e₁ (var 0) (Syn.shift x) ≐ one))))
    (ha : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 a (var 0) (Syn.shift x)) (Syn.shift M)))
    (hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 b (var 0) (Syn.shift x)) (Syn.shift M))) :
    Γ ⊢[PRAAx] le (ap2 (sumF (w * d)) N x) (η * ap2 (sumF w) N x + two * M * ap2 (sumF (w * e₁)) N x) := by
  -- with `K = M` the tail events are empty, so the tail bodies can be the constant `0`
  have t₂ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (lt (Syn.shift M) (inst2 a (var 0) (Syn.shift x)) ⟶ (inst2 (zero : PTm 2) (var 0) (Syn.shift x) ≐ one))) :=
    .allI (.impI (.impI (le_lt_absurd _ (Prf.impE ha.allOpen.wk.wk Prf.hyp1) Prf.hyp0)))
  have t₃ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (lt (Syn.shift M) (inst2 b (var 0) (Syn.shift x)) ⟶ (inst2 (zero : PTm 2) (var 0) (Syn.shift x) ≐ one))) :=
    .allI (.impI (.impI (le_lt_absurd _ (Prf.impE hb.allOpen.wk.wk Prf.hyp1) Prf.hyp0)))
  have v := vitali w d a b e₁ zero zero hd h₁ t₂ t₃
  -- the two tail sums vanish
  have z : ∀ c : PTm 2, Γ ⊢[PRAAx] ap2 (sumF (w * (c * zero))) N x ≐ zero := fun c => by
    refine (sum_congr_bounded (w * (c * zero)) (zero : PTm 2) x x N (.allI (.impI ?_))).eqTrans (sum_zeroB _ _)
    have e : inst2 (zero : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift x) = zero := by simp [inst2]
    rw [inst2_mul', inst2_mul', e]
    exact (congrMul (.eqRefl _) (mul_zero _)).eqTrans (mul_zero _)
  have z₂ := natEq (z a)
  have z₃ := natEq (z b)
  ipra_le sl v using linear_combination -z₂ - z₃

end LeanProofs.IPRA.Probability.VitaliEstimate
