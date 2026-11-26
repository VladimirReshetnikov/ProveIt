import IPRADerivations.AnalyticNumberTheory.Totatives
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.InductionTactic

/-!
# Gcd fibers

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:gcd-fiber`:
for `d ≥ 1` and `m ≥ 1`, `#{k < dm : gcd(k, dm) = d} = φ(m)`.

* `reindex`: summing over multiples, `∑_{k<K} [d ∣ k] g(k/d) = ∑_{a<⌈K/d⌉} g(a)` (generalizing
  `Totient.count_multiples`, by induction on `K` with `Totient.quo_step`);
* `fiber_point`: `[gcd(k, dm) = d] = [d ∣ k] · [gcd(k/d, m) = 1]`, from
  `gcd(da, dm) = d ⟺ gcd(a, m) = 1` (`fiber_fwd`, `fiber_bwd`), via the cancellation
  `dh ∣ da → h ∣ a`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody inst2_tot quo_eq pred_lt quo_step)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (gcd_pos_right)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Division facts -/

theorem div_eq {j p : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) : Γ ⊢[PRAAx] j ≐ p * quo j p + rem j p :=
  (Prf.andE₁ (div_mod j (pred p))).eqTrans (congrAdd (congrMul hp.eqSymm (congrAp2 quoF (.eqRefl _) hp.eqSymm))
    (congrAp2 remF (.eqRefl _) hp.eqSymm))

/-- `⌈K/d⌉ = K/d` when `d ∣ K`. -/
theorem quo_exact {K d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (h : Γ ⊢[PRAAx] rem K d ≐ zero) :
    Γ ⊢[PRAAx] quo (K + pred d) d ≐ quo K d := by
  refine quo_eq hd (r := pred d) ?_ (pred_lt hd)
  ipra_lc natEq (div_eq (j := K) hd) + natEq h

theorem quo_mul_ceil {d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (m : PTm n) :
    Γ ⊢[PRAAx] quo (d * m + pred d) d ≐ m :=
  quo_eq hd (q := m) (r := pred d) (.eqRefl _) (pred_lt hd)

/-! ## Summing over multiples -/

/-- `[d ∣ k] g(k/d, x)`, over `0 = k`, `1 = d`, `2 = x`. -/
def rB (g : PTm 2) : PTm 3 := eqb (rem (var 0) (var 1)) zero * Syn.subst ![quo (var 0) (var 1), var 2] g

theorem inst3_rB (g : PTm 2) (k d x : PTm n) :
    inst3 (rB g) k d x = eqb (rem k d) zero * inst2 g (quo k d) x := by
  simp only [inst3, inst2, rB, PTm.subst_mul, subst_eqb, subst_ap2, Syn.subst_subst, Syn.subst_var,
    ConciseIPRA.PTm.subst_zero]
  congr 2; funext i; fin_cases i <;> simp

theorem reindex_step {g : PTm 2} {K d x : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (ih : Γ ⊢[PRAAx] ap3 (sum2F (rB g)) K d x ≐ ap2 (sumF g) (quo (K + pred d) d) x) :
    Γ ⊢[PRAAx] ap3 (sum2F (rB g)) (succ K) d x ≐ ap2 (sumF g) (quo (succ K + pred d) d) x := by
  refine (sum2_succ _ _ _ _).eqTrans ?_
  rw [inst3_rB]
  refine .eqTrans ?_ (congrAp2 (sumF g) (quo_step hd).eqSymm (.eqRefl x))
  refine .orE (eq_or_ne (rem K d) zero) ?_ ?_
  · have h : ((rem K d ≐ zero) :: Γ) ⊢[PRAAx] rem K d ≐ zero := Prf.hyp0
    have hq := quo_exact hd.wk h
    have e₁ := eqb_of_eq h
    refine (congrAdd ih.wk (congrMul e₁ (congrInst2 g hq.eqSymm (.eqRefl x)))).eqTrans ?_
    refine .eqTrans ?_ (congrAp2 (sumF g) (congrAdd (.eqRefl _) e₁.eqSymm) (.eqRefl x))
    have es : ((rem K d ≐ zero) :: Γ) ⊢[PRAAx] quo (K + pred d) d + succ zero ≐ succ (quo (K + pred d) d) := by
      ipra_ring
    refine .eqTrans ?_ (congrAp2 (sumF g) es.eqSymm (.eqRefl x))
    exact (congrAdd (.eqRefl _) (one_mul _)).eqTrans (sum_succ' g _ x).eqSymm
  · have e₀ := eqb_of_ne (Prf.hyp0 : (neg (rem K d ≐ zero) :: Γ) ⊢[PRAAx] neg (rem K d ≐ zero))
    refine (congrAdd ih.wk (congrMul e₀ (.eqRefl _))).eqTrans ?_
    refine .eqTrans ?_ (congrAp2 (sumF g) (congrAdd (.eqRefl _) e₀.eqSymm) (.eqRefl x))
    refine .eqTrans ?_ (congrAp2 (sumF g) (add_zero _).eqSymm (.eqRefl x))
    ipra_ring

/-- Variables: `0 = K`, `1 = d`, `2 = x`. -/
private abbrev reF (g : PTm 2) : Fm PTm 3 :=
  (var 1 ≐ succ (pred (var 1))) ⟶
    ap3 (sum2F (rB g)) (var 0) (var 1) (var 2) ≐ ap2 (sumF g) (quo (var 0 + pred (var 1)) (var 1)) (var 2)

private theorem reindex₀ (g : PTm 2) : ([] : List (Fm PTm 3)) ⊢[PRAAx] reF g := by
  ipra_ind (⟨trivial, trivial⟩) [subst_ap2, subst_ap3]
  · refine .impI ((sum2_zero _ _ _).eqTrans ((congrAp2 (sumF g)
      (quo_eq Prf.hyp0 (z := zero + pred (var 0)) (q := zero) (r := pred (var 0)) (by ipra_ring) (pred_lt Prf.hyp0))
      (.eqRefl _)).eqTrans (sum_zero _ _)).eqSymm)
  · exact .impI (reindex_step Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))

/-- `∑_{k<K} [d ∣ k] g(k/d, x) = ∑_{a<⌈K/d⌉} g(a, x)` for `d ≥ 1`. -/
theorem reindex (g : PTm 2) {K d x : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] ap3 (sum2F (rB g)) K d x ≐ ap2 (sumF g) (quo (K + pred d) d) x := by
  have h := inst (Γ := Γ) (reindex₀ g) (![K, d, x] : Fin 3 → PTm n)
  simp only [Fm.subst_imp, Fm.subst_eq, subst_ap2, subst_ap3, PTm.subst_add, PTm.subst_pred, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    ConciseIPRA.PTm.subst_succ] at h
  exact .impE h hd

/-! ## The pointwise identity -/

theorem eqb_iff {A B C D : PTm n} (h₁ : Γ ⊢[PRAAx] (A ≐ B) ⟶ (C ≐ D)) (h₂ : Γ ⊢[PRAAx] (C ≐ D) ⟶ (A ≐ B)) :
    Γ ⊢[PRAAx] eqb A B ≐ eqb C D :=
  Permutation.eqb_swap (.impI (.impI (.impE Prf.hyp1 (.impE h₂.wk.wk Prf.hyp0)))) h₁

theorem dvd_mul_both {d h a : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hh : Γ ⊢[PRAAx] h ≐ succ (pred h))
    (H : Γ ⊢[PRAAx] dvd h a) : Γ ⊢[PRAAx] dvd (d * h) (d * a) := by
  refine dvd_of_eq' (pos_mul hd hh) (w := quo a h) ?_
  ipra_lc Groth.ι (Q.mk _ d) * natEq (eq_of_dvd' hh H)

theorem dvd_cancel {d h a : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hh : Γ ⊢[PRAAx] h ≐ succ (pred h))
    (H : Γ ⊢[PRAAx] dvd (d * h) (d * a)) : Γ ⊢[PRAAx] dvd h a := by
  refine dvd_of_eq' hh (w := quo (d * a) (d * h)) (mul_cancel hd ?_)
  ipra_lc natEq (eq_of_dvd' (pos_mul hd hh) H)

section Point

variable {d m : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
include hd hm

/-- `gcd(da, dm) = d → gcd(a, m) = 1`. -/
theorem fiber_fwd {k a : PTm n} (hk : Γ ⊢[PRAAx] k ≐ d * a) (H : Γ ⊢[PRAAx] gcd k (d * m) ≐ d) :
    Γ ⊢[PRAAx] gcd a m ≐ one := by
  have hh := gcd_pos_right (a := a) hm
  have hdv := gcd_dvd_at hh
  have d₁ := dvd_congr hk.eqSymm (dvd_mul_both hd hh (Prf.andE₁ hdv))
  have d₂ := dvd_mul_both hd hh (Prf.andE₂ hdv)
  have dg := dvd_congr H (gcd_greatest' (pos_mul hd hh) d₁ d₂)
  have dg' : Γ ⊢[PRAAx] dvd (d * gcd a m) (d * one) :=
    dvd_congr (by ipra_ring) dg
  exact eq_one_of_dvd_one hh (dvd_cancel hd hh dg')

/-- `gcd(a, m) = 1 → gcd(da, dm) = d`. -/
theorem fiber_bwd {k a : PTm n} (hk : Γ ⊢[PRAAx] k ≐ d * a) (H : Γ ⊢[PRAAx] gcd a m ≐ one) :
    Γ ⊢[PRAAx] gcd k (d * m) ≐ d := by
  have hdm := pos_mul hd hm
  have hG := gcd_pos_right (a := k) hdm
  have hGd := gcd_dvd_at hG
  have ddk : Γ ⊢[PRAAx] dvd d k := dvd_of_eq' hd (w := a) hk
  have ddm : Γ ⊢[PRAAx] dvd d (d * m) := dvd_of_eq' hd (w := m) (.eqRefl _)
  have eG := eq_of_dvd' hd (gcd_greatest' hd ddk ddm)
  have hh : Γ ⊢[PRAAx] quo (gcd k (d * m)) d ≐ succ (pred (quo (gcd k (d * m)) d)) := by
    refine .orE (zero_or_succ (quo (gcd k (d * m)) d)) ?_ Prf.hyp0
    exact succ_ne_zero' _ (hG.wk.eqSymm.eqTrans (eG.wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans
      (mul_zero _))))
  have dhk := dvd_congr hk (dvd_congr_left eG (Prf.andE₁ hGd))
  have dhm := dvd_congr_left eG (Prf.andE₂ hGd)
  have h₁ := eq_one_of_dvd_one hh (dvd_congr H (gcd_greatest' hh (dvd_cancel hd hh dhk) (dvd_cancel hd hh dhm)))
  exact eG.eqTrans ((congrMul (.eqRefl _) h₁).eqTrans (by ipra_ring))

/-- `[gcd(k, dm) = d] = [d ∣ k] · [gcd(k/d, m) = 1]`. -/
theorem fiber_point (k : PTm n) :
    Γ ⊢[PRAAx] eqb (gcd k (d * m)) d ≐ eqb (rem k d) zero * eqb (gcd (quo k d) m) one := by
  refine .orE (eq_or_ne (rem k d) zero) ?_ ?_
  · have hr : ((rem k d ≐ zero) :: Γ) ⊢[PRAAx] rem k d ≐ zero := Prf.hyp0
    have hk : ((rem k d ≐ zero) :: Γ) ⊢[PRAAx] k ≐ d * quo k d :=
      (div_eq hd.wk).eqTrans ((congrAdd (.eqRefl _) hr).eqTrans (add_zero _))
    have e := eqb_iff (.impI (fiber_fwd hd.wk.wk hm.wk.wk hk.wk Prf.hyp0))
      (.impI (fiber_bwd hd.wk.wk hm.wk.wk hk.wk Prf.hyp0))
    exact e.eqTrans ((one_mul _).eqSymm.eqTrans (congrMul (eqb_of_eq hr).eqSymm (.eqRefl _)))
  · have hn : (neg (rem k d ≐ zero) :: Γ) ⊢[PRAAx] neg (rem k d ≐ zero) := Prf.hyp0
    have e₀ : (neg (rem k d ≐ zero) :: Γ) ⊢[PRAAx] eqb (gcd k (d * m)) d ≐ zero := by
      refine eqb_of_ne (.impI ?_)
      have hG := gcd_pos_right (a := k) (pos_mul hd.wk.wk hm.wk.wk)
        (Γ := (gcd k (d * m) ≐ d) :: neg (rem k d ≐ zero) :: Γ)
      have dk : ((gcd k (d * m) ≐ d) :: neg (rem k d ≐ zero) :: Γ) ⊢[PRAAx] dvd d k :=
        dvd_congr_left Prf.hyp0 (Prf.andE₁ (gcd_dvd_at hG))
      exact .impE hn.wk dk
    exact e₀.eqTrans ((zero_mul _).eqSymm.eqTrans (congrMul (eqb_of_ne hn).eqSymm (.eqRefl _)))

end Point

/-! ## The theorem -/

/-- `[gcd(k, n) = d]`, over `0 = k`, `1 = n`, `2 = d`. -/
abbrev gB : PTm 3 := eqb (gcd (var 0) (var 1)) (var 2)

theorem inst3_gB (k N d : PTm n) : inst3 gB k N d = eqb (gcd k N) d := by
  simp only [inst3, subst_eqb, subst_ex2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero]

theorem shift_pos {d : PTm n} (h : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ.map Fm.shift ⊢[PRAAx] Syn.shift d ≐ succ (pred (Syn.shift d)) := by
  have e := h.shift
  simp only [Fm.shift, Fm.subst_eq, PTm.subst_pred, ConciseIPRA.PTm.subst_succ] at e
  exact e

/-- `thm:gcd-fiber` at arbitrary `d, m ≥ 1`: `#{k < dm : gcd(k, dm) = d} = φ(m)`. -/
theorem gcd_fiber_at {d m : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] ap3 (sum2F gB) (d * m) (d * m) d ≐ phi m := by
  refine (sum2_congr_bounded gB (rB totBody) (d * m) d d m (d * m) (.allI (.impI ?_))).eqTrans
    ((reindex totBody hd).eqTrans (congrAp2 (sumF totBody) (quo_mul_ceil hd m) (.eqRefl _)))
  have e : Syn.shift (d * m) = Syn.shift d * Syn.shift m := by simp [Syn.shift]
  rw [inst3_gB, inst3_rB, inst2_tot, e]
  exact fiber_point (shift_pos hd).wk (shift_pos hm).wk _

/-- `thm:gcd-fiber`: variables `0 = d − 1`, `1 = m − 1`. -/
abbrev gcdFiberFormula : Fm PTm 2 :=
  ap3 (sum2F gB) (succ (var 0) * succ (var 1)) (succ (var 0) * succ (var 1)) (succ (var 0)) ≐ phi (succ (var 1))

theorem gcd_fiber : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 gcdFiberFormula :=
  closeUniv 2 (gcd_fiber_at (congrSucc (pred_succ _).eqSymm) (congrSucc (pred_succ _).eqSymm))

end LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber
