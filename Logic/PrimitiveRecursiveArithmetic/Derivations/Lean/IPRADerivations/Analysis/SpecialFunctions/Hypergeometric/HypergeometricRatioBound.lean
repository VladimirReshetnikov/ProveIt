import IPRADerivations.Analysis.SpecialFunctions.Hypergeometric.HypergeometricThreshold
import IPRADerivations.Core.OrderCertificates

/-!
# The ratio bound for hypergeometric terms with `r = s + 1`

Packet: `analysis/meijer_g_ipra_2026-11-16`, `paper/sections/03_hypergeometric_engine.tex`, Theorem `thm:hyp-conv`
("Primitive-recursive convergence"), case (b): "if `r = s + 1` and a squared-modulus certificate proves
`|w| ≤ R < 1`, choose `R < ρ < 1`; a primitive-recursive search produces `N` satisfying the ratio bound". Its proof:
"the desired ratio inequality is a polynomial inequality in `k` … in case (b) the leading-coefficient ratio is bounded
by `R < ρ`."

For natural parameter lists `as`, `bs` with `|as| ≤ |bs| + 1` and a rational argument `w = p/q`, the terms are
`T_k = (p/q)^k ∏ (a_i)_k / (k! ∏ (b_j)_k)`; the powers of `q` cancel in the ratio, so the bound
`T_{k+1} ≤ ρ T_k` with `ρ = (p + q)/(2q)` (the midpoint of `p/q` and `1`) is
`2 Num_{k+1} Den_k ≤ (p + q) Num_k Den_{k+1}` for the numerators `Num_k = p^k ∏ (a_i)_k` of `HypergeometricRatio`.

* `kL`, `kpow_le`, `kpow_succ_le`: `k^{|as|} ≤ (k + 1) ∏_j (b_j + k)` for `k ≥ 1`;
* `ratio_b`: the polynomial inequality `2 p ∏_i (a_i + k) ≤ (p + q) k^{|as|}` gives the ratio bound at `k`;
* `cL`, `shift_upper`: for parameters `a_i ≤ A ≤ k`, `k ∏_i (a_i + k) ≤ k^{|as|} (k + (2^{|as|} − 1) A)`;
* `threshold_b`: hence the ratio bound holds at every `k ≥ max(1, A)` with `2 p (k + (2^{|as|} − 1) A) ≤ (p + q) k`,
  i.e. `k ≥ 2 p (2^r − 1) A / (q − p)`: an explicit threshold in place of the search.

Signed or non-integer parameters are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.HypergeometricRatioBound

open_ipra
open LeanProofs.IPRA.Analysis.HypergeometricRatio (prodL pochL shiftL pochL_succ Num Den pfq_ratio)
open LeanProofs.IPRA.Analysis.HypergeometricThreshold (one_le_shift)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `k^{|l|}`. -/
def kL (l : List (PTm n)) (k : PTm n) : PTm n := prodL (l.map fun _ => k)

/-- `2^{|l|} − 1`. -/
def cL : List (PTm n) → PTm n
  | [] => zero
  | _ :: l => two * cL l + one

/-- `k^{|l|} ≤ ∏_j (b_j + k)` for `|l| ≤ |bs|`, `k ≥ 1`. -/
theorem kpow_le (l : List (PTm n)) {k : PTm n} (hk : Γ ⊢[PRAAx] le one k) :
    ∀ bs : List (PTm n), l.length ≤ bs.length → (Γ ⊢[PRAAx] le (kL l k) (shiftL bs k)) := by
  induction l with
  | nil => intro bs _; exact one_le_shift bs hk
  | cons a l ih =>
    intro bs hlen
    cases bs with
    | nil => exact absurd hlen (by simp)
    | cons b bs' =>
      have h1 : Γ ⊢[PRAAx] le k (b + k) := le_congr (.eqRefl _) (add_comm k b) (le_add_right k b)
      have h : Γ ⊢[PRAAx] le (k * kL l k) ((b + k) * shiftL bs' k) :=
        le_mul_mono h1 (ih bs' (Nat.le_of_succ_le_succ hlen))
      exact h

/-- `k^{|as|} ≤ (k + 1) ∏_j (b_j + k)` for `|as| ≤ |bs| + 1`, `k ≥ 1`. -/
theorem kpow_succ_le (as bs : List (PTm n)) (hlen : as.length ≤ bs.length + 1) {k : PTm n}
    (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx] le (kL as k) (succ k * shiftL bs k) := by
  cases as with
  | nil =>
    have h : Γ ⊢[PRAAx] le (one * one) (succ k * shiftL bs k) :=
      le_mul_mono (le_trans hk (le_succ_self k)) (one_le_shift bs hk)
    have h' : Γ ⊢[PRAAx] le one (succ k * shiftL bs k) := le_congr (one_mul one) (.eqRefl _) h
    exact h'
  | cons a l =>
    have h : Γ ⊢[PRAAx] le (k * kL l k) (succ k * shiftL bs k) :=
      le_mul_mono (le_succ_self k) (kpow_le l hk bs (Nat.le_of_succ_le_succ hlen))
    exact h

/-- From `S X = u Y` and `c S = 2u + D`: `u (c Y) = u (2X) + D X`. -/
theorem cancel_b {S X Y u D c : PTm n} (pf : Γ ⊢[PRAAx] S * X ≐ u * Y) (e : Γ ⊢[PRAAx] c * S ≐ two * u + D) :
    Γ ⊢[PRAAx] u * (c * Y) ≐ u * (two * X) + D * X := by
  have p' := natEq pf
  have e' := natEq e
  apply deriveNat; ipra_simps
  linear_combination (-Groth.ι (Q.mk Γ c)) * p' + Groth.ι (Q.mk Γ X) * e'

/-- `thm:hyp-conv` (b), the ratio step: `2 p ∏ (a_i + k) ≤ (p + q) k^{|as|}` gives
`2 T_{k+1} ≤ ((p + q)/q) T_k` for `w = p/q`. -/
theorem ratio_b (as bs : List (PTm n)) (hlen : as.length ≤ bs.length + 1) {p q k : PTm n}
    (hk : Γ ⊢[PRAAx] le one k)
    (H : Γ ⊢[PRAAx] le (two * (p * shiftL as k)) ((p + q) * kL as k)) :
    Γ ⊢[PRAAx] le (two * (Num as p (succ k) * Den bs k)) ((p + q) * (Num as p k * Den bs (succ k))) := by
  have H2 : Γ ⊢[PRAAx] le (two * (p * shiftL as k)) ((p + q) * (succ k * shiftL bs k)) :=
    le_trans H (le_mul_mono (le_refl (p + q)) (kpow_succ_le as bs hlen hk))
  have pf := pfq_ratio (Γ := Γ) as bs p k
  refine .orE (zero_or_succ (p * shiftL as k)) ?_ ?_
  · have hz : ((p * shiftL as k ≐ zero) :: Γ) ⊢[PRAAx] p * shiftL as k ≐ zero := Prf.hyp0
    have nE : ((p * shiftL as k ≐ zero) :: Γ) ⊢[PRAAx] Num as p (succ k) ≐
        (pw p k * p) * (pochL as k * shiftL as k) := congrMul (pw_succ p k) (pochL_succ as k)
    have re : ((p * shiftL as k ≐ zero) :: Γ) ⊢[PRAAx] (pw p k * p) * (pochL as k * shiftL as k) ≐
        (pw p k * pochL as k) * (p * shiftL as k) := by ipra_ring
    have n0 := nE.eqTrans (re.eqTrans ((congrMul (.eqRefl _) hz).eqTrans (mul_zero _)))
    have x0 : ((p * shiftL as k ≐ zero) :: Γ) ⊢[PRAAx] two * (Num as p (succ k) * Den bs k) ≐ zero :=
      (congrMul (.eqRefl _) ((congrMul n0 (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (mul_zero _)
    exact le_congr x0.eqSymm (.eqRefl _) (zero_le _)
  · have hpos : ((p * shiftL as k ≐ succ (pred (p * shiftL as k))) :: Γ) ⊢[PRAAx]
        p * shiftL as k ≐ succ (pred (p * shiftL as k)) := Prf.hyp0
    have c := cancel_b (pf.wk (ψ := p * shiftL as k ≐ succ (pred (p * shiftL as k))))
      (eq_add_of_le (H2.wk (ψ := p * shiftL as k ≐ succ (pred (p * shiftL as k)))))
    have hle := le_of_eq_add c
    exact mul_le_cancel (le_congr (congrMul hpos (.eqRefl _)) (congrMul hpos (.eqRefl _)) hle)

/-- For `a_i ≤ A ≤ k`: `k ∏ (a_i + k) ≤ k · k^{|as|} + (2^{|as|} − 1) A k^{|as|}`. -/
theorem shift_upper (as : List (PTm n)) {A k : PTm n} (hAk : Γ ⊢[PRAAx] le A k) :
    (∀ a ∈ as, Γ ⊢[PRAAx] le a A) →
      (Γ ⊢[PRAAx] le (k * shiftL as k) (k * kL as k + cL as * A * kL as k)) := by
  induction as with
  | nil =>
    intro _
    have h : Γ ⊢[PRAAx] le (k * one) (k * one + zero * A * one) := by ipra_le 0
    exact h
  | cons a l ih =>
    intro hA
    have ih' := ih fun x hx => hA x (List.mem_cons_of_mem _ hx)
    have ha : Γ ⊢[PRAAx] le a A := hA a (by simp)
    have h : Γ ⊢[PRAAx] le (k * ((a + k) * shiftL l k))
        (k * (k * kL l k) + (two * cL l + one) * A * (k * kL l k)) := by
      ipra_le (𝔟 a + 𝔟 k) * sl ih' + sl ha * 𝔟 k * 𝔟 (kL l k) + 𝔟 (cL l) * 𝔟 A * 𝔟 (kL l k) * (sl hAk + sl ha)
    exact h

/-- `k ≥ 1` as positivity. -/
alias pos_of_one_le' := Common.pos_of_one_le

/-- `thm:hyp-conv` (b) with an explicit threshold: for `|as| ≤ |bs| + 1`, parameters `a_i ≤ A ≤ k`, `k ≥ 1` and
`2 p (k + (2^{|as|} − 1) A) ≤ (p + q) k`, the ratio bound `2 T_{k+1} ≤ ((p + q)/q) T_k` holds at `k`. -/
theorem threshold_b (as bs : List (PTm n)) (hlen : as.length ≤ bs.length + 1) {p q A k : PTm n}
    (hk : Γ ⊢[PRAAx] le one k) (hA : ∀ a ∈ as, Γ ⊢[PRAAx] le a A) (hAk : Γ ⊢[PRAAx] le A k)
    (hq : Γ ⊢[PRAAx] le (two * p * (k + cL as * A)) ((p + q) * k)) :
    Γ ⊢[PRAAx] le (two * (Num as p (succ k) * Den bs k)) ((p + q) * (Num as p k * Den bs (succ k))) := by
  have su := shift_upper as hAk hA
  have h1 := le_mul_mono (le_refl (two * p)) su
  have h2 := le_mul_mono hq (le_refl (kL as k))
  have Hk : Γ ⊢[PRAAx] le (k * (two * (p * shiftL as k))) (k * ((p + q) * kL as k)) :=
    le_trans (le_congr (by ipra_ring) (by ipra_ring) h1)
      (le_congr (.eqRefl _) (by ipra_ring) h2)
  have kpos := pos_of_one_le' hk
  exact ratio_b as bs hlen hk
    (mul_le_cancel (le_congr (congrMul kpos (.eqRefl _)) (congrMul kpos (.eqRefl _)) Hk))

end LeanProofs.IPRA.Analysis.HypergeometricRatioBound
