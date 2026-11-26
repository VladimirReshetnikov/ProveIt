import IPRADerivations.AnalyticNumberTheory.TotientTermStep
import IPRADerivations.AnalyticNumberTheory.QuotientBlocks
import IPRADerivations.AnalyticNumberTheory.SieveRecursion
import IPRADerivations.AnalyticNumberTheory.Fermat
import IPRADerivations.Probability.Independence
import IPRADerivations.Core.Header

/-!
# The prime step for the sums `∑_{d ≤ t} [d ∣ a] z!/φ(d)`

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, the proof of the
denominator bound `eq:sieve-denominator`.

With the terms `g_a(d) = [d ≥ 1][d ∣ a] ⌊z!/φ(d)⌋` of `TotientTermStep` and the truncated sums

    G_a(N) = ∑_{d < N} g_a(d)                                                     (`Gs`),

for a prime `p` with `gcd(p, a) = 1`:

* **`G_split`**: `G_{ap}(t + 1) = G_a(t + 1) + W(t)`, where `W(t) = ∑_{k ≤ ⌊t/p⌋} g_{ap}(p k)` collects the
  multiples of `p` (`TotientTermStep.split_pt`, reindexed by `SumReindex.reindex_eq`);
* **`W_scale`**: `G_a(⌊t/p⌋ + 1) = (p − 1) W(t)` for `t ≤ z` (`TotientTermStep.scale_pt`);
* `Gs_mono`: `G_a` is nondecreasing in the range.

Together: `G_{ap}(t) = G_a(t) + (p − 1)^{−1} G_a(⌊t/p⌋)` for `t ≤ z`, with `G_a(t)` standing for `G_a(t + 1)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.TotientSumStep

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrSg congrEqb' zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos not_dvd_one)
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (prime_shift)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (riB inst2_riB reindex_eq cM sum_le_bound)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveRecursion (cM_succ shift_cop shift_mul')
open LeanProofs.IPRA.AnalyticNumberTheory.QuotientBlocks (mul_le_of_le_quo)
open LeanProofs.IPRA.AnalyticNumberTheory.TotientTermStep (gt split_pt scale_pt)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' gcd_greatest' dvd_self')
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Signum (sg)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The bodies -/

/-- `g_a(d)` with `F = z!`, over `0 = d`, `1 = ⟨a, z⟩`. -/
abbrev GtB : PTm 2 := gt (fstT (var 1)) (fact (sndT (var 1))) (var 0)

theorem inst2_GtB (d y : PTm n) : inst2 GtB d y = gt (fstT y) (fact (sndT y)) d := by simp [inst2]

theorem congrGt {a a' z z' d d' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hz : Γ ⊢[PRAAx] z ≐ z')
    (hd : Γ ⊢[PRAAx] d ≐ d') : Γ ⊢[PRAAx] gt a (fact z) d ≐ gt a' (fact z') d' :=
  congrMul (congrSg hd) (congrMul (congrEqb' (congrAp2 remF ha hd) (.eqRefl _))
    (congrAp2 quoF (congrAp2 factF hz (.eqRefl _)) (congrAp2 (sumF totBody) hd hd)))

theorem Gt_at (d a z : PTm n) : Γ ⊢[PRAAx] inst2 GtB d (pairT a z) ≐ gt a (fact z) d := by
  rw [inst2_GtB]
  exact congrGt (fst_pair a z) (snd_pair a z) (.eqRefl _)

/-- `G_a(N) = ∑_{d < N} g_a(d)`. -/
abbrev Gs (a z N : PTm n) : PTm n := ap2 (sumF GtB) N (pairT a z)

/-- `g_{ap}(p k)`, over `0 = k`, `1 = ⟨p, ⟨a, z⟩⟩`. -/
abbrev HB : PTm 2 :=
  gt (fstT (sndT (var 1)) * fstT (var 1)) (fact (sndT (sndT (var 1)))) (fstT (var 1) * var 0)

theorem inst2_HB (k x : PTm n) :
    inst2 HB k x = gt (fstT (sndT x) * fstT x) (fact (sndT (sndT x))) (fstT x * k) := by simp [inst2]

/-- The parameter `⟨p, ⟨a, z⟩⟩`. -/
abbrev par (p a z : PTm n) : PTm n := pairT p (pairT a z)

theorem H_at (k p a z : PTm n) : Γ ⊢[PRAAx] inst2 HB k (par p a z) ≐ gt (a * p) (fact z) (p * k) := by
  rw [inst2_HB]
  have f1 : Γ ⊢[PRAAx] fstT (par p a z) ≐ p := fst_pair _ _
  have s1 : Γ ⊢[PRAAx] sndT (par p a z) ≐ pairT a z := snd_pair _ _
  exact congrGt (congrMul ((congrFst s1).eqTrans (fst_pair a z)) f1)
    ((congrSnd s1).eqTrans (snd_pair a z)) (congrMul f1 (.eqRefl _))

/-- `W(t) = ∑_{k ≤ ⌊t/p⌋} g_{ap}(p k)`. -/
abbrev Ws (p a z t : PTm n) : PTm n := ap2 (sumF HB) (succ (quo t p)) (par p a z)

/-! ## The split -/

theorem ndvd_of_cop {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hc : Γ ⊢[PRAAx] gcd p a ≐ one) :
    Γ ⊢[PRAAx] neg (dvd p a) := by
  have hp2 := prime_two hp
  have hp1 := p_pos hp2
  refine .impI (.impE (not_dvd_one hp2.wk) ?_)
  exact dvd_congr hc.wk (gcd_greatest' hp1.wk (dvd_self' hp1.wk) Prf.hyp0)

theorem split_term {p a z : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hc : Γ ⊢[PRAAx] gcd p a ≐ one) (d : PTm n) :
    Γ ⊢[PRAAx] inst2 GtB d (pairT (a * p) z) ≐
      inst2 GtB d (pairT a z) + inst2 (riB HB) d (pairT p (par p a z)) := by
  have hp1 := p_pos (prime_two hp)
  have rH : Γ ⊢[PRAAx] inst2 (riB HB) d (pairT p (par p a z)) ≐
      eqb (rem d p) zero * gt (a * p) (fact z) (p * quo d p) := by
    rw [inst2_riB]
    exact congrMul (congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (.eqRefl _))
      ((congrInst2 HB (congrAp2 quoF (.eqRefl _) (fst_pair _ _)) (snd_pair _ _)).eqTrans (H_at _ p a z))
  refine (Gt_at d (a * p) z).eqTrans (.eqTrans ?_ (congrAdd (Gt_at d a z) rH).eqSymm)
  refine (split_pt hp (ndvd_of_cop hp hc) d).eqTrans (congrAdd (.eqRefl _) ?_)
  refine .orE (eq_or_ne (rem d p) zero) ?_ ?_
  · have hd : ((rem d p ≐ zero) :: Γ) ⊢[PRAAx] dvd p d := Prf.hyp0
    exact congrMul (.eqRefl _) (congrGt (.eqRefl _) (.eqRefl _) (eq_of_dvd' hp1.wk hd))
  · have hn : (neg (rem d p ≐ zero) :: Γ) ⊢[PRAAx] neg (rem d p ≐ zero) := Prf.hyp0
    exact (zero_mul_l (eqb_of_ne hn) _).eqTrans (zero_mul_l (eqb_of_ne hn) _).eqSymm

/-- **The split**: `G_{ap}(t + 1) = G_a(t + 1) + W(t)` for a prime `p` with `gcd(p, a) = 1`. -/
theorem G_split {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hc : Γ ⊢[PRAAx] gcd p a ≐ one) (z t : PTm n) :
    Γ ⊢[PRAAx] Gs (a * p) z (succ t) ≐ Gs a z (succ t) + Ws p a z t := by
  have hp1 := p_pos (prime_two hp)
  have hp' := prime_shift hp
  have hc' := shift_cop hc
  have s : Γ ⊢[PRAAx] ap2 (sumF GtB) (succ t) (pairT (a * p) z) ≐
      ap2 (sumF GtB) (succ t) (pairT a z) + ap2 (sumF (riB HB)) (succ t) (pairT p (par p a z)) := by
    refine sum_add2 GtB (riB HB) GtB (.allI (.impI ?_))
    simp only [shift_pairT, shift_mul']
    exact split_term hp'.wk hc'.wk _
  exact s.eqTrans (congrAdd (.eqRefl _)
    ((reindex_eq HB (succ t) hp1).eqTrans (congrAp2 (sumF HB) (cM_succ hp1) (.eqRefl _))))

/-! ## The scaling -/

theorem shift_le' {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift b) := by
  simpa [Fm.shift, Syn.shift] using h.shift

/-- **The scaling**: `G_a(⌊t/p⌋ + 1) = (p − 1) W(t)` for `t ≤ z`. -/
theorem W_scale {p a z t : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hc : Γ ⊢[PRAAx] gcd p a ≐ one)
    (htz : Γ ⊢[PRAAx] le t z) :
    Γ ⊢[PRAAx] Gs a z (succ (quo t p)) ≐ pred p * Ws p a z t := by
  have hp' := prime_shift hp
  have hc' := shift_cop hc
  have htz' := shift_le' htz
  refine sum_scale GtB HB (succ (quo t p)) (pred p) (par p a z) (pairT a z) (.allI (.impI ?_))
  simp only [shift_pairT]
  have sp : Syn.shift (pred p) = pred (Syn.shift p) := by simp [Syn.shift]
  have sq : Syn.shift (succ (quo t p)) = succ (quo (Syn.shift t) (Syn.shift p)) := by simp [Syn.shift]
  rw [sp]
  let C : List (Fm PTm (n + 1)) :=
    lt (var 0) (Syn.shift (succ (quo t p))) :: Γ.map Fm.shift
  have hlt : C ⊢[PRAAx] lt (var 0) (succ (quo (Syn.shift t) (Syn.shift p))) := by
    have h0 : C ⊢[PRAAx] lt (var 0) (Syn.shift (succ (quo t p))) := Prf.hyp0
    rw [sq] at h0
    exact h0
  have hk : C ⊢[PRAAx] le (var 0) (quo (Syn.shift t) (Syn.shift p)) :=
    (succ_monus_succ _ _).eqSymm.eqTrans hlt
  have hp1' : C ⊢[PRAAx] Syn.shift p ≐ succ (pred (Syn.shift p)) := p_pos (prime_two hp'.wk)
  have hpk : C ⊢[PRAAx] le (Syn.shift p * var 0) (Syn.shift z) :=
    le_trans (mul_le_of_le_quo hp1' hk) htz'.wk
  exact (Gt_at _ _ _).eqTrans
    ((scale_pt hp'.wk (ndvd_of_cop hp'.wk hc'.wk) hpk).eqSymm.eqTrans (congrMul (.eqRefl _) (H_at _ _ _ _).eqSymm))

/-- `G_a` is nondecreasing in the range. -/
theorem Gs_mono {a z N N' : PTm n} (h : Γ ⊢[PRAAx] le N N') : Γ ⊢[PRAAx] le (Gs a z N) (Gs a z N') :=
  sum_le_bound GtB h

/-- `W` is nondecreasing in `t`. -/
theorem Ws_mono {p a z t t' : PTm n} (h : Γ ⊢[PRAAx] le (quo t p) (quo t' p)) :
    Γ ⊢[PRAAx] le (Ws p a z t) (Ws p a z t') :=
  sum_le_bound HB ((succ_monus_succ _ _).eqTrans h)

end LeanProofs.IPRA.AnalyticNumberTheory.TotientSumStep
