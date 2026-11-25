import IPRADerivations.Combinatorics.CoefficientLogConcave
import IPRADerivations.Combinatorics.BellBounds
import IPRADerivations.Combinatorics.BellTriangle
import IPRADerivations.Combinatorics.CatalanBallot
import IPRADerivations.Probability.Independence
import IPRADerivations.Core.CertificateTactics

/-!
# Normalized log-concavity of the Bell numbers

Packet: `combinatorics/bell_numbers_ipra`, `thm:normalized-logconcavity`:

"For every `n ≥ 1`, `n B_{n−1} B_{n+1} ≤ (n + 1) B_n²`. Equivalently, `B_n/n!` is log-concave.
Moreover, `B_m B_n ≤ B_{m+n} ≤ C(m + n, m) B_m B_n`."

The proof sets `a_n = B_n/n!`, `x_0 = 1`, `x_j = 1/(j − 1)!` and applies
`lem:coefficient-logconcave` (`Combinatorics/CoefficientLogConcave`). Here the sequences are
cleared by the common denominator `N!`: with `N!/i! = C(N, i) (N − i)!` (the term `fq i N`, no
division),

* `X(j, N) = N!/(j − 1)!` for `j ≥ 1` and `X(0, N) = N!` (`XB`, uniformly `fq (pred j) N`);
* `A(r, N) = B_r · N!/r!` (`AB`).

* `fq_fact`, `fq_succ`, `fq_mul`: `(N!/i!) i! = N!`, `N!/i! = (i + 1) · N!/(i + 1)!` and
  `(N!/i!)(N!/(r − i)!) = N! · (N!/r!) · C(r, i)`;
* `bell_hyp`: the hypotheses `CoefficientLogConcave.Hyp` hold: `x_0 = N! ≥ 1`; the recurrence
  `x_0 (r + 1) a_{r+1} = Σ_{i ≤ r} x_{i+1} a_{r−i}` is the Bell recurrence
  `B_{r+1} = Σ_k C(r, k) B_k` (`Combinatorics/Bell.bell_succ`) reflected; and
  `x_j x_{k+1} ≤ x_{j+1} x_k` holds because "the successive ratios `x_j/x_{j−1}` are
  `1, 1, 1/2, 1/3, …`, a decreasing sequence";
* `bell_logconcave`: `m B_{m−1} B_{n+1} ≤ (n + 1) B_m B_n` for `1 ≤ m ≤ n` (with `m = μ + 1`,
  `n = μ + δ + 1`), the lemma at `N = n + 1` after cancelling `N!/m!`;
* `bell_normalized`, `bell_normalized_closed`: `n B_{n−1} B_{n+1} ≤ (n + 1) B_n²`
  (`eq:normalized-logconcavity`), the case `m = n`;
* `absorb`, `bell_product_upper`, `bell_product_upper_closed`:
  `B_{n+m} ≤ C(n + m, m) B_n B_m`, the upper bound of `eq:bell-product-bounds`, by induction on
  `m` from `bell_logconcave` ("normalized log-concavity makes `a_{j+1}/a_j` decrease"). The
  lower bound is `Combinatorics/BellSpivey.bell_product`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BellLogConcave

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (binom bden)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel binom_eq binom_zero' binom_self'
  pascal_at)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrBinom)
open LeanProofs.IPRA.Combinatorics.Bell (bell bell_succ bell_zero)
open LeanProofs.IPRA.Combinatorics.BellBounds (congrBell bell_pos)
open LeanProofs.IPRA.Combinatorics.BellTriangle (binom_symm)
open LeanProofs.IPRA.Combinatorics.CatalanBallot (binom_ratio)
open LeanProofs.IPRA.Combinatorics.BellTouchardPower (le_of_lt_succ)
open LeanProofs.IPRA.Combinatorics.CatalanPowers (shift_pair shift_succ monus_le_left)
open LeanProofs.IPRA.Combinatorics.CoefficientLogConcave (Hyp bd rec_at coefficient_logconcave)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos eq_succ_pred)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The quotient `N!/i!` -/

/-- `N!/i! = C(N, i) (N − i)!`. -/
def fq (i N : PTm n) : PTm n := binom N i * fact (monus N i)

theorem congrFq {i i' N N' : PTm n} (hi : Γ ⊢[PRAAx] i ≐ i') (hN : Γ ⊢[PRAAx] N ≐ N') :
    Γ ⊢[PRAAx] fq i N ≐ fq i' N' := by
  unfold fq
  exact congrMul (congrBinom hN hi) (congrAp2 factF (congrMonus hN hi) (.eqRefl _))

theorem shift_fq (i N : PTm n) : Syn.shift (fq i N) = fq (Syn.shift i) (Syn.shift N) := by
  simp [Syn.shift, fq]

theorem shift_fact (N : PTm n) : Syn.shift (fact N) = fact (Syn.shift N) := by simp [Syn.shift]

theorem shift_mul (a b : PTm n) : Syn.shift (a * b) = Syn.shift a * Syn.shift b := by
  simp [Syn.shift]

/-- `(N!/i!) i! = N!` for `i ≤ N`. -/
theorem fq_fact {i N : PTm n} (h : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] fq i N * fact i ≐ fact N := by
  unfold fq
  ipra_lc -natEq (binom_eq h)

/-- `N!/i! = (i + 1) · N!/(i + 1)!` for `i < N`. -/
theorem fq_succ {i N : PTm n} (h : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] fq i N ≐ succ i * fq (succ i) N := by
  refine mul_cancel (fact_pos i) ?_
  ipra_lc natEq (fq_fact (le_of_lt h)) - natEq (fq_fact (i := succ i) (N := N) h) +
    𝔞 (fq (succ i) N) * natEq (fact_succ (Γ := Γ) i zero)

theorem fq_self (N : PTm n) : Γ ⊢[PRAAx] fq N N ≐ one := by
  unfold fq
  exact (congrMul (binom_self' N) ((congrAp2 factF (monus_self N) (.eqRefl _)).eqTrans
    (fact_zero _))).eqTrans (one_mul _)

theorem fq_zero (N : PTm n) : Γ ⊢[PRAAx] fq zero N ≐ fact N := by
  unfold fq
  exact (congrMul (binom_zero' N) (congrAp2 factF (monus_zero N) (.eqRefl _))).eqTrans
    (one_mul _)

/-- `N!/i! ≥ 1` for `i ≤ N`. -/
theorem fq_pos {i N : PTm n} (h : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] fq i N ≐ succ (pred (fq i N)) := by
  refine .orE (zero_or_succ (fq i N)) ?_ Prf.hyp0
  have z : ((fq i N ≐ zero) :: Γ) ⊢[PRAAx] fact N ≐ zero :=
    (fq_fact h).wk.eqSymm.eqTrans ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))
  exact succ_ne_zero' _ ((fact_pos N).eqSymm.eqTrans z)

/-- `(N!/i!)(N!/(r − i)!) = N! · (N!/r!) · C(r, i)` for `i ≤ r ≤ N`. -/
theorem fq_mul {i r N : PTm n} (hi : Γ ⊢[PRAAx] le i r) (hr : Γ ⊢[PRAAx] le r N) :
    Γ ⊢[PRAAx] fq i N * fq (monus r i) N ≐ fact N * (fq r N * binom r i) := by
  refine mul_cancel (fact_pos i) (mul_cancel (fact_pos (monus r i)) ?_)
  ipra_lc (𝔞 (fq (monus r i) N) * 𝔞 (fact (monus r i))) * natEq (fq_fact (le_trans hi hr)) +
    𝔞 (fact N) * natEq (fq_fact (le_trans (monus_le_left r i) hr)) - 𝔞 (fact N) * natEq (fq_fact hr) +
    (𝔞 (fact N) * 𝔞 (fq r N)) * natEq (binom_eq hi)

/-! ## The scaled sequences -/

/-- `x_j = N!/(j − 1)!` (`x_0 = N!`), over `0 = j`, `1 = N`. -/
def XB : PTm 2 := fq (pred (var 0)) (var 1)
/-- `a_r = B_r · N!/r!`, over `0 = r`, `1 = N`. -/
def AB : PTm 2 := bell (var 0) * fq (var 0) (var 1)
/-- The bound is the parameter `N`. -/
abbrev NbB : PTm 1 := var 0

theorem inst2_XB (j y : PTm n) : inst2 XB j y = fq (pred j) y := by simp [inst2, XB, fq]

theorem inst2_AB (r y : PTm n) : inst2 AB r y = bell r * fq r y := by simp [inst2, AB, fq]

theorem X_zero (y : PTm n) : Γ ⊢[PRAAx] inst2 XB zero y ≐ fact y := by
  rw [inst2_XB]
  exact (congrFq pred_zero (.eqRefl _)).eqTrans (fq_zero y)

theorem X_succ (j y : PTm n) : Γ ⊢[PRAAx] inst2 XB (succ j) y ≐ fq j y := by
  rw [inst2_XB]
  exact congrFq (pred_succ j) (.eqRefl _)

/-- `x_i = i x_{i+1}` for `1 ≤ i < N`. -/
theorem X_dec {i y : PTm n} (hi : Γ ⊢[PRAAx] i ≐ succ (pred i)) (h : Γ ⊢[PRAAx] lt i y) :
    Γ ⊢[PRAAx] inst2 XB i y ≐ i * inst2 XB (succ i) y := by
  rw [inst2_XB, inst2_XB]
  have a := fq_succ (i := pred i) (N := y) (le_congr hi (.eqRefl _) (le_of_lt h))
  exact a.eqTrans (congrMul hi.eqSymm
    (congrFq (hi.eqSymm.eqTrans (pred_succ i).eqSymm) (.eqRefl _)))

/-! ## The hypotheses -/

/-- One term of the recurrence. -/
theorem rec_point {i r y : PTm n} (hi : Γ ⊢[PRAAx] le i r) (hr : Γ ⊢[PRAAx] le r y) :
    Γ ⊢[PRAAx] inst2 (CoefficientLogConcave.recB XB AB) i (pairT r y) ≐
      (fact y * fq r y) * inst2 (rflBody Bell.recB) i (pairT (succ r) r) := by
  have l := rec_at (Γ := Γ) XB AB i r y
  rw [inst2_AB] at l
  have l' := l.eqTrans (congrMul (X_succ i y) (.eqRefl _))
  have rr : Γ ⊢[PRAAx] inst2 (rflBody Bell.recB) i (pairT (succ r) r) ≐
      binom r i * bell (monus r i) := by
    rw [inst2_rflBody, Bell.inst2_rec]
    have m : Γ ⊢[PRAAx] monus (fstT (pairT (succ r) r)) (succ i) ≐ monus r i :=
      (congrMonus (fst_pair _ _) (.eqRefl _)).eqTrans (succ_monus_succ r i)
    exact (congrMul (congrBinom (snd_pair _ _) m) (congrBell m)).eqTrans
      (congrMul (binom_symm hi) (.eqRefl _))
  ipra_lc natEq l' - (𝔞 (fact y) * 𝔞 (fq r y)) * natEq rr + 𝔞 (bell (monus r i)) * natEq (fq_mul hi hr)

theorem bell_recur {r y : PTm n} (h : Γ ⊢[PRAAx] lt r y) :
    Γ ⊢[PRAAx] inst2 XB zero y * (succ r * inst2 AB (succ r) y) ≐
      ap2 (sumF (CoefficientLogConcave.recB XB AB)) (succ r) (pairT r y) := by
  have s : Γ ⊢[PRAAx] ap2 (sumF (CoefficientLogConcave.recB XB AB)) (succ r) (pairT r y) ≐
      (fact y * fq r y) * ap2 (sumF (rflBody Bell.recB)) (succ r) (pairT (succ r) r) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    have hr' : (Γ.map Fm.shift) ⊢[PRAAx] lt (Syn.shift r) (Syn.shift y) := by
      simpa [Fm.shift, Syn.shift] using h.shift
    simp only [shift_pair, shift_succ, shift_mul, shift_fact, shift_fq]
    exact rec_point (le_of_lt_succ Prf.hyp0) (le_of_lt hr'.wk)
  rw [inst2_AB]
  ipra_lc ((𝔞 r + 1) * 𝔞 (bell (succ r)) * 𝔞 (fq (succ r) y)) * natEq (X_zero (Γ := Γ) y) - natEq s -
    (𝔞 (fact y) * 𝔞 (bell (succ r))) * natEq (fq_succ h) +
    (𝔞 (fact y) * 𝔞 (fq r y)) * natEq ((bell_succ (Γ := Γ) r).eqTrans (sum_reflect Bell.recB (succ r) r))

theorem bell_xlc {j k y : PTm n} (hjk : Γ ⊢[PRAAx] lt j k) (hk : Γ ⊢[PRAAx] lt k y) :
    Γ ⊢[PRAAx] le (inst2 XB j y * inst2 XB (succ k) y) (inst2 XB (succ j) y * inst2 XB k y) := by
  have kpos : Γ ⊢[PRAAx] k ≐ succ (pred k) :=
    .orE (zero_or_succ k) (lt_zero_absurd _ (lt_congr (.eqRefl _) Prf.hyp0 hjk.wk)) Prf.hyp0
  refine .orE (zero_or_succ j) ?_ ?_
  · -- `x_0 = x_1`
    have xj : ((j ≐ zero) :: Γ) ⊢[PRAAx] inst2 XB j y ≐ inst2 XB (succ j) y := by
      rw [inst2_XB, inst2_XB]
      exact congrFq ((congrPred Prf.hyp0).eqTrans
        (pred_zero.eqTrans ((pred_succ j).eqTrans Prf.hyp0).eqSymm)) (.eqRefl _)
    have dk := natEq ((X_dec kpos hk).wk (ψ := j ≐ zero))
    refine le_of_eq_add (d := inst2 XB (succ j) y * (pred k * inst2 XB (succ k) y)) ?_
    ipra_lc 𝔞 (inst2 XB (succ j) y) * dk +
      (𝔞 (inst2 XB (succ j) y) * 𝔞 (inst2 XB (succ k) y)) * natEq (kpos.wk (ψ := j ≐ zero)) -
      𝔞 (inst2 XB (succ k) y) * natEq xj
  · have hj : ((j ≐ succ (pred j)) :: Γ) ⊢[PRAAx] lt j y :=
      (lt_of_lt_of_le hjk (le_of_lt hk)).wk
    have dk := natEq ((X_dec kpos hk).wk (ψ := j ≐ succ (pred j)))
    refine le_of_eq_add (d := succ (monus k (succ j)) *
      (inst2 XB (succ j) y * inst2 XB (succ k) y)) ?_
    ipra_lc 𝔞 (inst2 XB (succ j) y) * dk - 𝔞 (inst2 XB (succ k) y) * natEq (X_dec Prf.hyp0 hj) +
      (𝔞 (inst2 XB (succ j) y) * 𝔞 (inst2 XB (succ k) y)) * natEq ((eq_add_of_le hjk).wk (ψ := j ≐ succ (pred j)))

/-- The hypotheses of `lem:coefficient-logconcave` for `x_j = N!/(j − 1)!`, `a_r = B_r N!/r!`. -/
theorem bell_hyp : Hyp XB AB NbB where
  pos := by
    intro n Γ y
    exact le_of_eq_add (d := pred (fact y))
      ((X_zero y).eqTrans ((fact_pos y).eqTrans (by ipra_ring)))
  recur := by
    intro n Γ r y h
    exact bell_recur h
  xlc := by
    intro n Γ j k y hjk hk
    exact bell_xlc hjk hk

/-! ## Log-concavity of `B_n/n!` -/

/-- `m B_{m−1} B_{n+1} ≤ (n + 1) B_m B_n` for `1 ≤ m ≤ n`, with `m = μ + 1`, `n = μ + δ + 1`. -/
theorem bell_logconcave (μ δ : PTm n) :
    Γ ⊢[PRAAx] le (succ μ * (bell μ * bell (succ (succ (μ + δ)))))
      (succ (succ (μ + δ)) * (bell (succ μ) * bell (succ (μ + δ)))) := by
  have c := coefficient_logconcave (Γ := Γ) bell_hyp μ δ (succ (succ (μ + δ))) (le_refl _)
  simp only [inst2_AB] at c
  have hμ : Γ ⊢[PRAAx] lt μ (succ (succ (μ + δ))) :=
    le_of_eq_add (d := succ δ) (by ipra_ring)
  have hsμ : Γ ⊢[PRAAx] le (succ μ) (succ (succ (μ + δ))) := hμ
  have big : Γ ⊢[PRAAx]
      le (succ (pred (fq (succ μ) (succ (succ (μ + δ))))) *
          (succ μ * (bell μ * bell (succ (succ (μ + δ))))))
        (succ (pred (fq (succ μ) (succ (succ (μ + δ))))) *
          (succ (succ (μ + δ)) * (bell (succ μ) * bell (succ (μ + δ))))) := by
    refine le_congr ?_ ?_ c
    · ipra_lc (𝔞 (bell μ) * 𝔞 (bell (succ (succ (μ + δ)))) * 𝔞 (fq μ (succ (succ (μ + δ))))) * natEq (fq_self (Γ := Γ) (succ (succ (μ + δ)))) +
        (𝔞 (bell μ) * 𝔞 (bell (succ (succ (μ + δ))))) * natEq (fq_succ hμ) +
        (𝔞 (bell μ) * 𝔞 (bell (succ (succ (μ + δ)))) * (𝔞 μ + 1)) * natEq (fq_pos hsμ)
    · ipra_lc (𝔞 (bell (succ μ)) * 𝔞 (bell (succ (μ + δ))) * 𝔞 (fq (succ μ) (succ (succ (μ + δ))))) * natEq (fq_succ (Γ := Γ) (i := succ (μ + δ)) (N := succ (succ (μ + δ))) (le_refl _)) +
        (𝔞 (bell (succ μ)) * 𝔞 (bell (succ (μ + δ))) * 𝔞 (fq (succ μ) (succ (succ (μ + δ)))) * (𝔞 μ + 𝔞 δ + 1 + 1)) * natEq (fq_self (Γ := Γ) (succ (succ (μ + δ)))) +
        (𝔞 (bell (succ μ)) * 𝔞 (bell (succ (μ + δ))) * (𝔞 μ + 𝔞 δ + 1 + 1)) * natEq (fq_pos hsμ)
  exact mul_le_cancel big

/-- `eq:normalized-logconcavity`: `n B_{n−1} B_{n+1} ≤ (n + 1) B_n²` for `n = μ + 1 ≥ 1`. -/
theorem bell_normalized (μ : PTm n) :
    Γ ⊢[PRAAx] le (succ μ * (bell μ * bell (succ (succ μ))))
      (succ (succ μ) * (bell (succ μ) * bell (succ μ))) :=
  le_congr
    (congrMul (.eqRefl _) (congrMul (.eqRefl _) (congrBell (congrSucc (congrSucc (add_zero μ))))))
    (congrMul (congrSucc (congrSucc (add_zero μ)))
      (congrMul (.eqRefl _) (congrBell (congrSucc (add_zero μ)))))
    (bell_logconcave μ zero)

/-- `eq:normalized-logconcavity` as a closed sentence; variable `0 = n − 1`. -/
theorem bell_normalized_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le (succ (var 0) * (bell (var 0) * bell (succ (succ (var 0)))))
      (succ (succ (var 0)) * (bell (succ (var 0)) * bell (succ (var 0))))) :=
  closeUniv 1 (bell_normalized _)

/-! ## The upper product bound -/

/-- Absorption: `(N + 1) C(N, j) = (j + 1) C(N + 1, j + 1)` for `j < N`. -/
theorem absorb {j N : PTm n} (h : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] succ N * binom N j ≐ succ j * binom (succ N) (succ j) := by
  ipra_lc -(𝔞 j + 1) * natEq (pascal_at h) + 𝔞 (binom N j) * natEq (eq_add_of_le (le_of_lt h)) + natEq (binom_ratio h)

/-- One more factor: from `m` to `m + 1`, for `n = n' + 1 ≥ 1`. -/
theorem upper_step {n' m : PTm n}
    (ih : Γ ⊢[PRAAx] le (bell (succ n' + m))
      (binom (succ n' + m) m * (bell (succ n') * bell m))) :
    Γ ⊢[PRAAx] le (bell (succ n' + succ m))
      (binom (succ n' + succ m) (succ m) * (bell (succ n') * bell (succ m))) := by
  have hlt : Γ ⊢[PRAAx] lt m (succ n' + m) :=
    le_of_eq_add (d := n') (by ipra_ring)
  have eY := natEq (congrBell (Γ := Γ) (a := succ (m + n')) (b := succ n' + m)
    (by ipra_ring))
  have eX := natEq (congrBell (Γ := Γ) (a := succ (succ (m + n'))) (b := succ n' + succ m)
    (by ipra_ring))
  have eC := natEq (congrBinom (Γ := Γ) (a := succ n' + succ m) (a' := succ (succ n' + m))
    (b := succ m) (b' := succ m) (by ipra_ring) (.eqRefl _))
  have bpos : Γ ⊢[PRAAx] bell m ≐ succ (pred (bell m)) :=
    eq_succ_pred ((eq_add_of_le (bell_pos m)).eqTrans
      (by ipra_ring :
        Γ ⊢[PRAAx] one + monus (bell m) one ≐ succ (monus (bell m) one)))
  have big : Γ ⊢[PRAAx] le (succ m * (succ (pred (bell m)) * bell (succ n' + succ m)))
      (succ m * (succ (pred (bell m)) *
        (binom (succ n' + succ m) (succ m) * (bell (succ n') * bell (succ m))))) := by
    refine le_of_eq_add (d := monus (succ (succ (m + n')) * (bell (succ m) * bell (succ (m + n'))))
        (succ m * (bell m * bell (succ (succ (m + n'))))) +
      succ (succ (m + n')) * (bell (succ m) *
        monus (binom (succ n' + m) m * (bell (succ n') * bell m)) (bell (succ n' + m)))) ?_
    ipra_lc -((𝔞 m + 1) * (𝔞 (binom (succ n' + succ m) (succ m)) * (𝔞 (bell (succ n')) * 𝔞 (bell (succ m))) - 𝔞 (bell (succ n' + succ m)))) * natEq bpos +
      ((𝔞 m + 1) * 𝔞 (bell m) * 𝔞 (bell (succ n')) * 𝔞 (bell (succ m))) * eC -
      (𝔞 (bell m) * 𝔞 (bell (succ n')) * 𝔞 (bell (succ m))) * natEq (absorb hlt) +
      ((𝔞 n' + 1 + 𝔞 m + 1) * 𝔞 (bell (succ m))) * natEq (eq_add_of_le ih) -
      ((𝔞 n' + 1 + 𝔞 m + 1) * 𝔞 (bell (succ m))) * eY + natEq (eq_add_of_le (bell_logconcave (Γ := Γ) m n')) +
      ((𝔞 m + 1) * 𝔞 (bell m)) * eX
  exact mul_le_cancel (mul_le_cancel big)

/-- The induction formula of `bell_product_upper`; variable `0 = m`. -/
abbrev upF (n' : PTm n) : Fm PTm (n + 1) :=
  le (bell (succ (Syn.shift n') + var 0))
    (binom (succ (Syn.shift n') + var 0) (var 0) * (bell (succ (Syn.shift n')) * bell (var 0)))

/-- `eq:bell-product-bounds`, upper bound, for `n = n' + 1 ≥ 1`:
`B_{n+m} ≤ C(n + m, m) B_n B_m`. -/
theorem bell_product_upper (n' m : PTm n) :
    Γ ⊢[PRAAx] le (bell (succ n' + m)) (binom (succ n' + m) m * (bell (succ n') * bell m)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (upF n') := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · have b : Γ ⊢[PRAAx] le (bell (succ n' + zero))
          (binom (succ n' + zero) zero * (bell (succ n') * bell zero)) := by
        refine le_of_eq_add (d := zero) ?_
        ipra_lc (𝔞 (bell (succ n')) * 𝔞 (bell zero)) * natEq (binom_zero' (Γ := Γ) (succ n' + zero)) +
          𝔞 (bell (succ n')) * natEq (bell_zero (Γ := Γ)) - natEq (congrBell (Γ := Γ) (add_zero (succ n')))
      simpa using b
    · have st : (upF n' :: Γ.map Fm.shift) ⊢[PRAAx]
          le (bell (succ (Syn.shift n') + succ (var 0)))
            (binom (succ (Syn.shift n') + succ (var 0)) (succ (var 0)) *
              (bell (succ (Syn.shift n')) * bell (succ (var 0)))) :=
        upper_step Prf.hyp0
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE m hall
  simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2

/-- `eq:bell-product-bounds`, upper bound, as a closed sentence; variables `0 = n − 1`,
`1 = m`. -/
theorem bell_product_upper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (bell (succ (var 0) + var 1))
      (binom (succ (var 0) + var 1) (var 1) * (bell (succ (var 0)) * bell (var 1)))) :=
  closeUniv 2 (bell_product_upper _ _)

end LeanProofs.IPRA.Combinatorics.BellLogConcave
