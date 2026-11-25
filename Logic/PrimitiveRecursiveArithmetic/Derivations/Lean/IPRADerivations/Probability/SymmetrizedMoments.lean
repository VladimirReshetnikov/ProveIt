import IPRADerivations.Probability.Independence
import IPRADerivations.Probability.Variance
import IPRADerivations.Analysis.PowerSums
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination

/-!
# Moments of the symmetrization `Y − Y′`

Packet: `probability/central_limit_ipra_2026-11-15`, the finite moment facts in the proofs of Lemma
`lem:bounded-damping` ("Damping from an independent copy") and Lemma `lem:truncated-damping`
("Truncated damping"), for `Z = Y_j − Y′_j` with `Y′_j` an independent copy:

* (6.4): `E (Y_j − Y′_j)² = 2 v_j`;
* (7.6): `E[Z² 1_{|tZ|>1}] ≤ |t| E|Z|³ ≤ 8 |t| β_j`, "because `|u − v|³ ≤ 4(|u|³ + |v|³)`".

For a finite law with weights `w(i, x)` and the product law `w_i w_j` of two independent copies
(`Probability/Independence`), with `W = ∑ w`:

* `dsum_le`: pointwise smaller bodies have smaller double sums;
* `symm_second_moment`: `∑∑ w_i w_j |Y_i − Y_j|² + 2 S² = 2 W Q` for `S = ∑ w Y`, `Q = ∑ w Y²`, i.e.
  `E (Y − Y′)² = 2 Var(Y)`;
* `cube_le`: `z ≤ a + b` gives `z³ ≤ 4 (a³ + b³)`, from `4(a³ + b³) − (a + b)³ = 3 (a + b)(a − b)²`;
* `symm_third_moment`: for a distance body `d(i, j) ≤ a_i + a_j` (as `|Y_i − Y_j| ≤ |Y_i| + |Y_j|`),
  `∑∑ w_i w_j d³ ≤ A W + W A` with `A = ∑ 4 w a³`, i.e. `E|Z|³ ≤ 8 E|Y|³`;
* `discard_pt`, `discarded_moment`: for a threshold `t = p/q` given by bodies and any body `e ≤ 1` that
  vanishes when `p d ≤ q`, `∑∑ w_i w_j q d² e ≤ ∑∑ w_i w_j p d³`, i.e.
  `E[Z² 1_{|tZ|>1}] ≤ |t| E|Z|³`.

The characteristic functions and the exponential bounds of the two lemmas are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.SymmetrizedMoments

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Expectation (inst2_mul')
open LeanProofs.IPRA.Probability.Independence
  (dsum dsum_congr dsum_add pmB inst3_pmB sum_mul_sum inst3_mul' inst3_add')
open LeanProofs.IPRA.Probability.Variance (ad ad_sq)
open LeanProofs.IPRA.Analysis.PowerSums (sum_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Monotonicity of double sums -/

/-- Pointwise smaller bodies have smaller double sums. -/
theorem dsum_le (a b : PTm 3)
    (h : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (i j x : PTm m),
      Δ ⊢[PRAAx] le (inst3 a i j x) (inst3 b i j x))
    (M N x : PTm n) : Γ ⊢[PRAAx] le (dsum a M N x) (dsum b M N x) := by
  refine sum_le (oB a) (oB b) (pairT N x) M (.allI (.impI ?_))
  rw [inst2_oB, inst2_oB]
  refine sum_le (rowB a) (rowB b) _ _ (.allI (.impI ?_))
  rw [inst2_rowB, inst2_rowB]
  exact h _ _ _

/-! ## Bodies in two indices -/

/-- `f` at the first index and at the second index; variables `0 = i`, `1 = j`, `2 = x`. -/
def fst3 (f : PTm 2) : PTm 3 := Syn.subst ![var 0, var 2] f
def snd3 (f : PTm 2) : PTm 3 := Syn.subst ![var 1, var 2] f

theorem inst3_fst3 (f : PTm 2) (i j x : PTm n) : inst3 (fst3 f) i j x = inst2 f i x := by
  simp only [inst3, fst3, inst2, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> rfl

theorem inst3_snd3 (f : PTm 2) (i j x : PTm n) : inst3 (snd3 f) i j x = inst2 f j x := by
  simp only [inst3, snd3, inst2, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> rfl

/-- `|Y_i − Y_j|`. -/
def dB (Y : PTm 2) : PTm 3 := monus (fst3 Y) (snd3 Y) + monus (snd3 Y) (fst3 Y)

theorem inst3_dB (Y : PTm 2) (i j x : PTm n) :
    inst3 (dB Y) i j x = ad (inst2 Y i x) (inst2 Y j x) := by
  have e : inst3 (dB Y) i j x =
      monus (inst3 (fst3 Y) i j x) (inst3 (snd3 Y) i j x) +
        monus (inst3 (snd3 Y) i j x) (inst3 (fst3 Y) i j x) := by
    simp [inst3, dB]
  rw [e, inst3_fst3, inst3_snd3]

/-! ## The second moment -/

section Second

variable (w Y : PTm 2)

/-- The two sides of the pointwise identity `w_i w_j |Y_i − Y_j|² + 2 (w_i Y_i)(w_j Y_j) =
(w_i Y_i²) w_j + w_i (w_j Y_j²)`. -/
abbrev LA : PTm 3 := pmB w w * (dB Y * dB Y) + (pmB (w * Y) (w * Y) + pmB (w * Y) (w * Y))
abbrev RA : PTm 3 := pmB (w * (Y * Y)) w + pmB w (w * (Y * Y))

theorem second_pt (i j x : PTm n) : Γ ⊢[PRAAx] inst3 (LA w Y) i j x ≐ inst3 (RA w Y) i j x := by
  have el : inst3 (LA w Y) i j x =
      inst2 w i x * inst2 w j x * (ad (inst2 Y i x) (inst2 Y j x) * ad (inst2 Y i x) (inst2 Y j x)) +
        (inst2 w i x * inst2 Y i x * (inst2 w j x * inst2 Y j x) +
          inst2 w i x * inst2 Y i x * (inst2 w j x * inst2 Y j x)) := by
    simp only [LA, inst3_add', inst3_mul', inst3_pmB, inst3_dB, inst2_mul']
  have er : inst3 (RA w Y) i j x =
      inst2 w i x * (inst2 Y i x * inst2 Y i x) * inst2 w j x +
        inst2 w i x * (inst2 w j x * (inst2 Y j x * inst2 Y j x)) := by
    simp only [RA, inst3_add', inst3_mul', inst3_pmB, inst2_mul']
  rw [el, er]
  ipra_lc 𝔟(inst2 w i x) * 𝔟(inst2 w j x) * natEq (ad_sq (Γ := Γ) (inst2 Y i x) (inst2 Y j x))

/-- (6.4): `∑∑ w_i w_j |Y_i − Y_j|² + 2 S² = 2 W Q`, i.e. `E (Y − Y′)² = 2 Var(Y)`. -/
theorem symm_second_moment (N x : PTm n) :
    Γ ⊢[PRAAx] dsum (pmB w w * (dB Y * dB Y)) N N x +
        (ap2 (sumF (w * Y)) N x * ap2 (sumF (w * Y)) N x +
          ap2 (sumF (w * Y)) N x * ap2 (sumF (w * Y)) N x) ≐
      ap2 (sumF (w * (Y * Y))) N x * ap2 (sumF w) N x +
        ap2 (sumF w) N x * ap2 (sumF (w * (Y * Y))) N x := by
  ipra_lc -natEq (dsum_add (Γ := Γ) (pmB w w * (dB Y * dB Y)) (pmB (w * Y) (w * Y) + pmB (w * Y) (w * Y)) N N x) +
    natEq (dsum_congr (Γ := Γ) (LA w Y) (RA w Y) (fun i j x => second_pt w Y i j x) N N x) +
    natEq (dsum_add (Γ := Γ) (pmB (w * (Y * Y)) w) (pmB w (w * (Y * Y))) N N x) +
    natEq (sum_mul_sum (Γ := Γ) (w * (Y * Y)) w N N x) + natEq (sum_mul_sum (Γ := Γ) w (w * (Y * Y)) N N x) -
    natEq (dsum_add (Γ := Γ) (pmB (w * Y) (w * Y)) (pmB (w * Y) (w * Y)) N N x) -
    2 * natEq (sum_mul_sum (Γ := Γ) (w * Y) (w * Y) N N x)

end Second

/-! ## The third moment -/

/-- `z ≤ a + b` gives `z³ ≤ 4 (a³ + b³)`. -/
theorem cube_le {z a b : PTm n} (h : Γ ⊢[PRAAx] le z (a + b)) :
    Γ ⊢[PRAAx] le (z * z * z) (num 4 * (a * a * a + b * b * b)) := by
  refine .orE (le_total a b) ?_ ?_
  · have hab : (le a b :: Γ) ⊢[PRAAx] le a b := Prf.hyp0
    have h' := h.wk (ψ := le a b)
    ipra_le 3 * (𝔟 a + 𝔟 b) * sl hab * sl hab +
      sl h' * ((𝔟 a + 𝔟 b) * (𝔟 a + 𝔟 b) + (𝔟 a + 𝔟 b) * 𝔟 z + 𝔟 z * 𝔟 z)
  · have hba : (le b a :: Γ) ⊢[PRAAx] le b a := Prf.hyp0
    have h' := h.wk (ψ := le b a)
    ipra_le 3 * (𝔟 a + 𝔟 b) * sl hba * sl hba +
      sl h' * ((𝔟 a + 𝔟 b) * (𝔟 a + 𝔟 b) + (𝔟 a + 𝔟 b) * 𝔟 z + 𝔟 z * 𝔟 z)

section Third

variable (w a : PTm 2) (d : PTm 3)

/-- `w_i w_j d³` and `(4 w_i a_i³) w_j + w_i (4 w_j a_j³)`. -/
abbrev LB : PTm 3 := pmB w w * (d * d * d)
abbrev RB : PTm 3 := pmB (num 4 * (w * (a * a * a))) w + pmB w (num 4 * (w * (a * a * a)))

theorem inst2_four (i x : PTm n) : inst2 (num 4 : PTm 2) i x = num 4 := by
  simp [inst2]

theorem third_pt (hd : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (i j x : PTm m),
      Δ ⊢[PRAAx] le (inst3 d i j x) (inst2 a i x + inst2 a j x))
    (i j x : PTm n) : Γ ⊢[PRAAx] le (inst3 (LB w d) i j x) (inst3 (RB w a) i j x) := by
  have el : inst3 (LB w d) i j x =
      inst2 w i x * inst2 w j x * (inst3 d i j x * inst3 d i j x * inst3 d i j x) := by
    simp only [LB, inst3_mul', inst3_pmB]
  have er : inst3 (RB w a) i j x =
      num 4 * (inst2 w i x * (inst2 a i x * inst2 a i x * inst2 a i x)) * inst2 w j x +
        inst2 w i x * (num 4 * (inst2 w j x * (inst2 a j x * inst2 a j x * inst2 a j x))) := by
    simp only [RB, inst3_add', inst3_pmB, inst2_mul', inst2_four]
  rw [el, er]
  have c := cube_le (hd (Δ := Γ) i j x)
  ipra_le 𝔟(inst2 w i x) * 𝔟(inst2 w j x) * sl c

/-- (7.6), second inequality: `∑∑ w_i w_j d³ ≤ A W + W A` with `A = ∑ 4 w a³`, i.e.
`E|Y − Y′|³ ≤ 8 E|Y|³`. -/
theorem symm_third_moment (hd : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (i j x : PTm m),
      Δ ⊢[PRAAx] le (inst3 d i j x) (inst2 a i x + inst2 a j x))
    (N x : PTm n) :
    Γ ⊢[PRAAx] le (dsum (pmB w w * (d * d * d)) N N x)
      (ap2 (sumF (num 4 * (w * (a * a * a)))) N x * ap2 (sumF w) N x +
        ap2 (sumF w) N x * ap2 (sumF (num 4 * (w * (a * a * a)))) N x) := by
  have l := dsum_le (Γ := Γ) (LB w d) (RB w a) (fun i j x => third_pt w a d hd i j x) N N x
  have a₃ := natEq (dsum_add (Γ := Γ) (pmB (num 4 * (w * (a * a * a))) w)
    (pmB w (num 4 * (w * (a * a * a)))) N N x)
  have m₄ := natEq (sum_mul_sum (Γ := Γ) (num 4 * (w * (a * a * a))) w N N x)
  have m₅ := natEq (sum_mul_sum (Γ := Γ) w (num 4 * (w * (a * a * a))) N N x)
  ipra_le sl l using linear_combination -a₃ - m₄ - m₅

end Third

/-! ## The discarded second moment -/

/-- `q z² e ≤ p z³` when `e ≤ 1` and `e = 0` unless `q < p z`. -/
theorem discard_pt {z p q e : PTm n} (h₀ : Γ ⊢[PRAAx] le e one)
    (h₁ : Γ ⊢[PRAAx] le (p * z) q ⟶ (e ≐ zero)) :
    Γ ⊢[PRAAx] le (q * (z * z) * e) (p * (z * z * z)) := by
  refine .orE (lt_or_le q (p * z)) ?_ ?_
  · have hlt : (lt q (p * z) :: Γ) ⊢[PRAAx] le (succ q) (p * z) := Prf.hyp0
    have h₀' := h₀.wk (ψ := lt q (p * z))
    ipra_le 𝔟 z * 𝔟 z * (𝔟 q * sl h₀' + 1 + sl hlt)
  · have E := natEq (Prf.impE (h₁.wk (ψ := le (p * z) q)) Prf.hyp0)
    ipra_le 𝔟 p * (𝔟 z * 𝔟 z * 𝔟 z) using linear_combination -𝔟 q * 𝔟 z * 𝔟 z * E

section Discard

variable (w : PTm 2) (d p q e : PTm 3)

abbrev LC : PTm 3 := pmB w w * (q * (d * d) * e)
abbrev RC : PTm 3 := pmB w w * (p * (d * d * d))

/-- (7.6), first inequality: `∑∑ w_i w_j q d² e ≤ ∑∑ w_i w_j p d³`, i.e.
`E[Z² 1_{|tZ|>1}] ≤ |t| E|Z|³` for `t = p/q`. -/
theorem discarded_moment
    (h₀ : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (i j x : PTm m), Δ ⊢[PRAAx] le (inst3 e i j x) one)
    (h₁ : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (i j x : PTm m),
      Δ ⊢[PRAAx] le (inst3 p i j x * inst3 d i j x) (inst3 q i j x) ⟶ (inst3 e i j x ≐ zero))
    (N x : PTm n) :
    Γ ⊢[PRAAx] le (dsum (pmB w w * (q * (d * d) * e)) N N x) (dsum (pmB w w * (p * (d * d * d))) N N x) := by
  refine dsum_le (LC w d q e) (RC w d p) (fun {m} {Δ} i j x => ?_) N N x
  have el : inst3 (LC w d q e) i j x =
      inst2 w i x * inst2 w j x *
        (inst3 q i j x * (inst3 d i j x * inst3 d i j x) * inst3 e i j x) := by
    simp only [LC, inst3_mul', inst3_pmB]
  have er : inst3 (RC w d p) i j x =
      inst2 w i x * inst2 w j x *
        (inst3 p i j x * (inst3 d i j x * inst3 d i j x * inst3 d i j x)) := by
    simp only [RC, inst3_mul', inst3_pmB]
  rw [el, er]
  have c := discard_pt (h₀ (Δ := Δ) i j x) (h₁ (Δ := Δ) i j x)
  ipra_le 𝔟(inst2 w i x) * 𝔟(inst2 w j x) * sl c

end Discard

end LeanProofs.IPRA.Probability.SymmetrizedMoments
