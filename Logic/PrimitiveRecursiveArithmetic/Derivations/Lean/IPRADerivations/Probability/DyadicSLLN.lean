import IPRADerivations.Probability.DyadicBlock
import IPRADerivations.Probability.DyadicUnion
import IPRADerivations.Geometry.HypercubeSplit
import IPRADerivations.AnalyticNumberTheory.Valuation
import IPRADerivations.Core.CertificateTactics

/-!
# The dyadic eventual-uniform bound (dyadic strong law), the block parameters

Packet: `probability/expected_value_ipra_2026-11-16`, `paper/sections/08_samples_lln.tex`, Theorem `thm:dyadic-slln`.

The threshold of block `r` is `a_r = 2 e 2^r W` (for `ε = e`, values in the units of `X`; a rational `ε = e/f` is the
case `X = f X₀`). It depends on the block, so it is read from the parameter of the law, `xx = ⟨⟨r, e⟩, x⟩`, while the
law itself reads only `x`:

* `lw`, `lift_at`: the lifted bodies `w(i, ⟨⟨r, e⟩, x⟩) = w₀(i, x)`;
* `pr_lift`: the `H`-fold product weight of the lifted law is that of the original law, for every block parameter;
* `aB`, `aB_at`: the threshold body `a(M, ⟨⟨r, e⟩, x⟩) = 2 e 2^r W(M, x)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.DyadicSLLN

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.ProductPower (TB Tt Pr Sr TB_at dB_at dg wdB xdB)
open LeanProofs.IPRA.Probability.KolmogorovIid (DB DB_at)
open LeanProofs.IPRA.Probability.DyadicBlock (pcB Pc Cc block_cross crossing_witness)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Lifting the law to the block parameter -/

/-- `f(i, snd xx)`. -/
def lw (f : PTm 2) : PTm 2 := Syn.subst ![var 0, sndT (var 1)] f

theorem inst2_lw (f : PTm 2) (i xx : PTm n) : inst2 (lw f) i xx = inst2 f i (sndT xx) := by
  simp only [lw, inst2, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

theorem lift_at (f : PTm 2) (i r e x : PTm n) : Γ ⊢[PRAAx] inst2 (lw f) i (pairT (pairT r e) x) ≐ inst2 f i x := by
  rw [inst2_lw]; exact congrInst2 f (.eqRefl _) (snd_pair _ _)

/-- The product weight of the lifted law is that of the original law. -/
theorem pr_lift (w0 : PTm 2) (H t M r e x : PTm n) :
    Γ ⊢[PRAAx] Pr (lw w0) H t M (pairT (pairT r e) x) ≐ Pr w0 H t M x := by
  refine prod_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  exact (dB_at (lw w0) _ _ _ _).eqTrans ((lift_at w0 _ _ _ _).eqTrans (dB_at w0 _ _ _ _).eqSymm)

/-- The lifted weight body at any block parameter. -/
theorem tb_lift (w0 : PTm 2) (t H M r e x : PTm n) :
    Γ ⊢[PRAAx] inst2 (TB (lw w0)) t (pairT H (pairT M (pairT (pairT r e) x))) ≐ Pr w0 H t M x :=
  (TB_at (lw w0) t H M _).eqTrans (pr_lift w0 H t M r e x)

/-! ## The threshold -/

/-- `a(M, ⟨⟨r, e⟩, x⟩) = 2 e 2^r W(M, ⟨⟨r, e⟩, x⟩)`, over `0 = M`, `1 = xx`. -/
def aB (w0 : PTm 2) : PTm 2 :=
  two * sndT (fstT (var 1)) * pw two (fstT (fstT (var 1))) * ap2 (sumF (lw w0)) (var 0) (var 1)

theorem aB_at (w0 : PTm 2) (M r e x : PTm n) :
    Γ ⊢[PRAAx] inst2 (aB w0) M (pairT (pairT r e) x) ≐ two * e * pw two r * ap2 (sumF (lw w0)) M (pairT (pairT r e) x) := by
  have h : inst2 (aB w0) M (pairT (pairT r e) x) = two * sndT (fstT (pairT (pairT r e) x)) *
      pw two (fstT (fstT (pairT (pairT r e) x))) * ap2 (sumF (lw w0)) M (pairT (pairT r e) x) := by
    simp [aB, inst2]
  rw [h]
  have f1 : Γ ⊢[PRAAx] fstT (pairT (pairT r e) x) ≐ pairT r e := fst_pair _ _
  exact congrMul (congrMul (congrMul (.eqRefl _) ((congrSnd f1).eqTrans (snd_pair _ _)))
    (congrAp2 powF ((congrFst f1).eqTrans (fst_pair _ _)) (.eqRefl _))) (.eqRefl _)

/-! ## The lifted sums -/

theorem sum_lift (f : PTm 2) (M r e x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (lw f)) M (pairT (pairT r e) x) ≐ ap2 (sumF f) M x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  exact lift_at f _ _ _ _

theorem sum_lift2 (f g : PTm 2) (M r e x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (lw f * lw g)) M (pairT (pairT r e) x) ≐ ap2 (sumF (f * g)) M x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  rw [Expectation.inst2_mul', Expectation.inst2_mul']
  exact congrMul (lift_at f _ _ _ _) (lift_at g _ _ _ _)

theorem sum_lift3 (f g : PTm 2) (M r e x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (lw f * (lw g * lw g))) M (pairT (pairT r e) x) ≐ ap2 (sumF (f * (g * g))) M x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  rw [Expectation.inst2_mul', Expectation.inst2_mul', Expectation.inst2_mul', Expectation.inst2_mul']
  exact congrMul (lift_at f _ _ _ _) (congrMul (lift_at g _ _ _ _) (lift_at g _ _ _ _))

theorem tt_lift (w0 : PTm 2) (H M r e x : PTm n) :
    Γ ⊢[PRAAx] Tt (lw w0) H M (pairT (pairT r e) x) ≐ Tt w0 H M x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  exact (tb_lift w0 _ _ _ _ _ _).eqTrans (TB_at w0 _ _ _ _).eqSymm

/-! ## The block bound at a symbolic block -/

/-- `min(2^{r+1}, H)`. -/
abbrev Nm (r H : PTm n) : PTm n := monus (pw two (succ r)) (monus (pw two (succ r)) H)

theorem monus_le_self (a b : PTm n) : Γ ⊢[PRAAx] le (monus a b) a := by
  refine .orE (le_total b a) ?_ ?_
  · exact le_of_eq_add (d := b) ((eq_add_of_le Prf.hyp0).eqTrans (add_comm _ _))
  · exact le_congr (Prf.hyp0 : (le a b :: Γ) ⊢[PRAAx] monus a b ≐ zero).eqSymm (.eqRefl _) (zero_le a)

theorem Nm_le_pw (r H : PTm n) : Γ ⊢[PRAAx] le (Nm r H) (pw two (succ r)) := monus_le_self _ _

theorem Nm_le_H (r H : PTm n) : Γ ⊢[PRAAx] le (Nm r H) H := by
  refine .orE (le_total (pw two (succ r)) H) ?_ ?_
  · have z : (le (pw two (succ r)) H :: Γ) ⊢[PRAAx] monus (pw two (succ r)) H ≐ zero := Prf.hyp0
    exact le_congr ((congrMonus (.eqRefl _) z).eqTrans (monus_zero _)).eqSymm (.eqRefl _) Prf.hyp0
  · have e := eq_add_of_le (Prf.hyp0 : (le H (pw two (succ r)) :: Γ) ⊢[PRAAx] le H (pw two (succ r)))
    have q : (le H (pw two (succ r)) :: Γ) ⊢[PRAAx] Nm r H ≐ H :=
      (congrMonus e (.eqRefl _)).eqTrans (add_monus _ _)
    exact le_congr q.eqSymm (.eqRefl _) (le_refl H)

/-- Abstract algebra of one block: `A = 2eRW`, `A²P + TNS² ≤ TNWQ`, `N ≤ 2R`, `R ≥ 1` give
`2 e² W² R P ≤ (WQ ∸ S²) T`. -/
theorem blk_alg {A e R W P T N S Q : PTm n} (hA : Γ ⊢[PRAAx] A ≐ two * e * R * W)
    (bc : Γ ⊢[PRAAx] le (A * A * P + T * (N * (S * S))) (T * (N * (W * Q))))
    (hN : Γ ⊢[PRAAx] le N (two * R)) (hR : Γ ⊢[PRAAx] R ≐ succ (pred R)) :
    Γ ⊢[PRAAx] le (two * (e * e * (W * W)) * R * P) (monus (W * Q) (S * S) * T) := by
  have st1 : Γ ⊢[PRAAx] le (A * A * P) (T * N * monus (W * Q) (S * S)) := by
    refine le_of_eq_add (d := T * N * monus (S * S) (W * Q) +
      monus (T * (N * (W * Q))) (A * A * P + T * (N * (S * S)))) ?_
    ipra_lc (𝔞 T * 𝔞 N) * natEq (monus_max (Γ := Γ) (W * Q) (S * S)) + natEq (eq_add_of_le bc)
  have st2 : Γ ⊢[PRAAx] le (T * N * monus (W * Q) (S * S)) (T * (two * R) * monus (W * Q) (S * S)) :=
    le_mul_mono (le_mul_mono (le_refl T) hN) (le_refl _)
  have two_pos : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := congrSucc (pred_succ _).eqSymm
  refine le_cancel_pos (Combinatorics.Binomial.pos_mul two_pos hR) (le_congr ?_ ?_ (le_trans st1 st2))
  · ipra_lc (𝔞 A + 2 * 𝔞 e * 𝔞 R * 𝔞 W) * 𝔞 P * natEq hA
  · ipra_ring

/-- The sample sum of the lifted values is that of the original values. -/
theorem sr_lift (X0 : PTm 2) (l t M r e x : PTm n) :
    Γ ⊢[PRAAx] Sr (lw X0) l t M (pairT (pairT r e) x) ≐ Sr X0 l t M x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  exact (dB_at (lw X0) _ _ _ _).eqTrans ((lift_at X0 _ _ _ _).eqTrans (dB_at X0 _ _ _ _).eqSymm)

/-- The lifted level `D_l` at any block parameter is the original level. -/
theorem db_lift (w0 X0 : PTm 2) (l t M r e x : PTm n) :
    Γ ⊢[PRAAx] inst2 (DB (lw w0) (lw X0)) l (pairT t (pairT M (pairT (pairT r e) x))) ≐
      inst2 (DB w0 X0) l (pairT t (pairT M x)) := by
  refine (DB_at (lw w0) (lw X0) l t M _).eqTrans (.eqTrans ?_ (DB_at w0 X0 l t M x).eqSymm)
  have a := KolmogorovIid.congrAd (congrMul (sum_lift (Γ := Γ) w0 M r e x) (sr_lift X0 l t M r e x))
    (congrMul (.eqRefl l) (sum_lift2 (Γ := Γ) w0 X0 M r e x))
  exact congrMul a a

variable (w0 X0 : PTm 2)

/-- The crossing mass of block `r` in the `H`-fold law, read at the block parameter `⟨⟨r, e⟩, x⟩`. -/
abbrev Pblk (r e H M x : PTm n) : PTm n := Pc (lw w0) (lw X0) (aB w0) (Nm r H) H M (pairT (pairT r e) x)

/-- Kolmogorov for block `r`: `2 e² W² 2^r P_r ≤ (WQ ∸ S²) T_H`, with `W, S, Q, T_H` of the original law. -/
theorem block_hyp {M x H : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hW : Γ ⊢[PRAAx] ap2 (sumF w0) M x ≐ succ (pred (ap2 (sumF w0) M x))) (r e : PTm n) :
    Γ ⊢[PRAAx] le (two * (e * e * (ap2 (sumF w0) M x * ap2 (sumF w0) M x)) * pw two r * Pblk w0 X0 r e H M x)
      (monus (ap2 (sumF w0) M x * ap2 (sumF (w0 * (X0 * X0))) M x)
        (ap2 (sumF (w0 * X0)) M x * ap2 (sumF (w0 * X0)) M x) * Tt w0 H M x) := by
  have sW := sum_lift (Γ := Γ) w0 M r e x
  have hWl : Γ ⊢[PRAAx] ap2 (sumF (lw w0)) M (pairT (pairT r e) x) ≐
      succ (pred (ap2 (sumF (lw w0)) M (pairT (pairT r e) x))) :=
    sW.eqTrans (hW.eqTrans (congrSucc (congrPred sW.eqSymm)))
  have bc := block_cross (lw w0) (lw X0) (aB w0) hM hWl (Nm_le_H r H) (x := pairT (pairT r e) x)
  have sS := sum_lift2 (Γ := Γ) w0 X0 M r e x
  have sQ := sum_lift3 (Γ := Γ) w0 X0 M r e x
  have tT := tt_lift (Γ := Γ) w0 H M r e x
  have bc' := le_congr (congrAdd (.eqRefl _) (congrMul tT (congrMul (.eqRefl _) (congrMul sS sS))))
    (congrMul tT (congrMul (.eqRefl _) (congrMul sW sQ))) bc
  have hA := (aB_at (Γ := Γ) w0 M r e x).eqTrans (congrMul (.eqRefl _) sW)
  have hN : Γ ⊢[PRAAx] le (Nm r H) (two * pw two r) :=
    le_congr (.eqRefl _) ((pw_succ two r).eqTrans (mul_comm _ _)) (Nm_le_pw r H)
  have hR := AnalyticNumberTheory.Valuation.pw_pos' (congrSucc (pred_succ _).eqSymm : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two)) r
  exact blk_alg hA bc' hN hR

end LeanProofs.IPRA.Probability.DyadicSLLN
