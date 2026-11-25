import IPRADerivations.Probability.DyadicAssembly
import IPRADerivations.AnalyticNumberTheory.RobinLogInterval
import IPRADerivations.Core.LinearCombination

/-!
# The bad event is covered by the dyadic blocks

Packet: `probability/expected_value_ipra_2026-11-16`, `paper/sections/08_samples_lln.tex`, proof of `thm:dyadic-slln`:
"If for some `n ∈ [2^r, 2^{r+1})` we have `|S_n| ≥ 2ε n`, then certainly `max_{k ≤ 2^{r+1}} |S_k| ≥ 2ε 2^r`."

For an outcome `t` of the `H`-fold law, with the levels `D_n(t) = |W S_n(t) − n S|²` of the original law:

* `bdB`, `inst2_bd`: the bad indicator at `n`, `[2^K ≤ n] [(2 e n W)² ≤ D_n(t)]`;
* `cjB`, `inst2_cj`: the crossing count of block `K + j` (threshold `a = 2e2^{K+j}W`, range `min(2^{K+j+1}, H)`);
* `cover_pt`: `1 ∸ ∏_{n≤H} (1 ∸ bad_n(t)) ≤ Σ_{j<J} C_j(t)` with `J = (⌊log₂ H⌋ + 1) ∸ K` — if no block crosses, no
  `n ∈ [2^K, H]` is bad: such an `n` lies in the block `r = ⌊log₂ n⌋` (`RobinLogInterval.eb`), `K ≤ r ≤ ⌊log₂ H⌋`,
  `n ≤ min(2^{r+1}, H)`, and `a_r² ≤ (2enW)² ≤ D_n`, so `DyadicBlock.crossing_witness` makes `C_{r−K}(t) = 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.DyadicCover

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.FirstCrossing (ge ge_of_le ge_of_lt)
open LeanProofs.IPRA.Probability.KolmogorovIid (DB IB)
open LeanProofs.IPRA.Probability.KolmogorovIidGlue (Cv Cv_at)
open LeanProofs.IPRA.Probability.DyadicBlock (Cc crossing_witness)
open LeanProofs.IPRA.Probability.DyadicSLLN (lw aB aB_at Nm sum_lift db_lift monus_le_self)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval (eb eb_spec exp_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Order facts -/

theorem two_pos : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := congrSucc (pred_succ _).eqSymm

/-- `2^E ≤ a → E ≤ ⌊log₂ a⌋` for `a ≥ 1`. -/
theorem eb_ge {a E : PTm n} (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le (one * pw two E) a) :
    Γ ⊢[PRAAx] le E (eb a one) := by
  have h2 := Prf.andE₂ (eb_spec (le_refl one) ha)
  refine .orE (lt_or_le (eb a one) E) ?_ Prf.hyp0
  have l : (lt (eb a one) E :: Γ) ⊢[PRAAx] le (succ (eb a one)) E := Prf.hyp0
  have p := le_mul_mono (le_refl one) (AnalyticNumberTheory.PowerCleared.pw_le_exp two_pos l)
  exact le_lt_absurd _ (le_trans p hE.wk) h2.wk

/-- `n ≤ 2^{r+1}` and `n ≤ H` give `n ≤ min(2^{r+1}, H)`. -/
theorem le_Nm {m r H : PTm n} (h1 : Γ ⊢[PRAAx] le m (pw two (succ r))) (h2 : Γ ⊢[PRAAx] le m H) :
    Γ ⊢[PRAAx] le m (Nm r H) := by
  refine .orE (le_total (pw two (succ r)) H) ?_ ?_
  · have z : (le (pw two (succ r)) H :: Γ) ⊢[PRAAx] monus (pw two (succ r)) H ≐ zero := Prf.hyp0
    exact le_congr (.eqRefl _) ((congrMonus (.eqRefl _) z).eqTrans (monus_zero _)).eqSymm h1.wk
  · have e := eq_add_of_le (Prf.hyp0 : (le H (pw two (succ r)) :: Γ) ⊢[PRAAx] le H (pw two (succ r)))
    have q : (le H (pw two (succ r)) :: Γ) ⊢[PRAAx] Nm r H ≐ H := (congrMonus e (.eqRefl _)).eqTrans (add_monus _ _)
    exact le_congr (.eqRefl _) q.eqSymm h2.wk

section Cover

variable (w0 X0 : PTm 2)

/-! ## The bodies -/

/-- The parameter `⟨t, ⟨M, ⟨⟨K, e⟩, x⟩⟩⟩` of the bad indicator. -/
abbrev Zc (t M K e x : PTm n) : PTm n := pairT t (pairT M (pairT (pairT K e) x))

/-- `[2^K ≤ n] [(2 e n W)² ≤ D_n(t)]` over `(n, ⟨t, ⟨M, ⟨⟨K, e⟩, x⟩⟩⟩)`. -/
def bdB : PTm 2 :=
  ge (pw two (fstT (fstT (sndT (sndT (var 1)))))) (var 0) *
    ge ((two * sndT (fstT (sndT (sndT (var 1)))) * var 0 * ap2 (sumF (lw w0)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))) *
        (two * sndT (fstT (sndT (sndT (var 1)))) * var 0 * ap2 (sumF (lw w0)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))))
      (DB (lw w0) (lw X0))

/-- The lifted total weight at the bad-event parameter. -/
abbrev Wk (M K e x : PTm n) : PTm n := ap2 (sumF (lw w0)) M (pairT (pairT K e) x)

theorem inst2_bd (m t M K e x : PTm n) :
    Γ ⊢[PRAAx] inst2 (bdB w0 X0) m (Zc t M K e x) ≐
      ge (pw two K) m * ge ((two * e * m * Wk w0 M K e x) * (two * e * m * Wk w0 M K e x))
        (inst2 (DB (lw w0) (lw X0)) m (Zc t M K e x)) := by
  have h : inst2 (bdB w0 X0) m (Zc t M K e x) =
      ge (pw two (fstT (fstT (sndT (sndT (Zc t M K e x)))))) m *
        ge ((two * sndT (fstT (sndT (sndT (Zc t M K e x)))) * m *
              ap2 (sumF (lw w0)) (fstT (sndT (Zc t M K e x))) (sndT (sndT (Zc t M K e x)))) *
            (two * sndT (fstT (sndT (sndT (Zc t M K e x)))) * m *
              ap2 (sumF (lw w0)) (fstT (sndT (Zc t M K e x))) (sndT (sndT (Zc t M K e x)))))
          (inst2 (DB (lw w0) (lw X0)) m (Zc t M K e x)) := by
    simp [bdB, inst2]
  rw [h]
  have s1 : Γ ⊢[PRAAx] sndT (Zc t M K e x) ≐ pairT M (pairT (pairT K e) x) := snd_pair _ _
  have s2 : Γ ⊢[PRAAx] sndT (sndT (Zc t M K e x)) ≐ pairT (pairT K e) x := (congrSnd s1).eqTrans (snd_pair _ _)
  have hM : Γ ⊢[PRAAx] fstT (sndT (Zc t M K e x)) ≐ M := (congrFst s1).eqTrans (fst_pair _ _)
  have f2 : Γ ⊢[PRAAx] fstT (sndT (sndT (Zc t M K e x))) ≐ pairT K e := (congrFst s2).eqTrans (fst_pair _ _)
  have hK : Γ ⊢[PRAAx] fstT (fstT (sndT (sndT (Zc t M K e x)))) ≐ K := (congrFst f2).eqTrans (fst_pair _ _)
  have he : Γ ⊢[PRAAx] sndT (fstT (sndT (sndT (Zc t M K e x)))) ≐ e := (congrSnd f2).eqTrans (snd_pair _ _)
  have hW : Γ ⊢[PRAAx] ap2 (sumF (lw w0)) (fstT (sndT (Zc t M K e x))) (sndT (sndT (Zc t M K e x))) ≐ Wk w0 M K e x :=
    congrAp2 _ hM s2
  have hc := congrMul (congrMul (congrMul (.eqRefl two) he) (.eqRefl m)) hW
  exact congrMul (congrMonus (.eqRefl _) (congrMonus (congrAp2 powF hK (.eqRefl _)) (.eqRefl _)))
    (congrMonus (.eqRefl _) (congrMonus (congrMul hc hc) (.eqRefl _)))

/-- The parameter `⟨⟨t, H⟩, ⟨M, ⟨⟨K, e⟩, x⟩⟩⟩` of the block crossing counts. -/
abbrev Yc (t H M K e x : PTm n) : PTm n := pairT (pairT t H) (pairT M (pairT (pairT K e) x))

/-- The crossing count of block `K + j` over `(j, ⟨⟨t, H⟩, ⟨M, ⟨⟨K, e⟩, x⟩⟩⟩)`. -/
def cjB : PTm 2 :=
  ap2 (sumF (IB (lw w0) (lw X0) (Cv (aB w0))))
    (succ (Nm (fstT (fstT (sndT (sndT (var 1)))) + var 0) (sndT (fstT (var 1)))))
    (pairT (fstT (fstT (var 1))) (pairT (fstT (sndT (var 1)))
      (pairT (pairT (fstT (fstT (sndT (sndT (var 1)))) + var 0) (sndT (fstT (sndT (sndT (var 1))))))
        (sndT (sndT (sndT (var 1)))))))

theorem inst2_cj (j t H M K e x : PTm n) :
    Γ ⊢[PRAAx] inst2 (cjB w0 X0) j (Yc t H M K e x) ≐
      Cc (lw w0) (lw X0) (aB w0) (Nm (K + j) H) t M (pairT (pairT (K + j) e) x) := by
  have h : inst2 (cjB w0 X0) j (Yc t H M K e x) =
      ap2 (sumF (IB (lw w0) (lw X0) (Cv (aB w0))))
        (succ (Nm (fstT (fstT (sndT (sndT (Yc t H M K e x)))) + j) (sndT (fstT (Yc t H M K e x)))))
        (pairT (fstT (fstT (Yc t H M K e x))) (pairT (fstT (sndT (Yc t H M K e x)))
          (pairT (pairT (fstT (fstT (sndT (sndT (Yc t H M K e x)))) + j) (sndT (fstT (sndT (sndT (Yc t H M K e x))))))
            (sndT (sndT (sndT (Yc t H M K e x))))))) := by
    simp [cjB, inst2]
  rw [h]
  have f1 : Γ ⊢[PRAAx] fstT (Yc t H M K e x) ≐ pairT t H := fst_pair _ _
  have s1 : Γ ⊢[PRAAx] sndT (Yc t H M K e x) ≐ pairT M (pairT (pairT K e) x) := snd_pair _ _
  have s2 : Γ ⊢[PRAAx] sndT (sndT (Yc t H M K e x)) ≐ pairT (pairT K e) x := (congrSnd s1).eqTrans (snd_pair _ _)
  have f2 : Γ ⊢[PRAAx] fstT (sndT (sndT (Yc t H M K e x))) ≐ pairT K e := (congrFst s2).eqTrans (fst_pair _ _)
  have ht : Γ ⊢[PRAAx] fstT (fstT (Yc t H M K e x)) ≐ t := (congrFst f1).eqTrans (fst_pair _ _)
  have hH : Γ ⊢[PRAAx] sndT (fstT (Yc t H M K e x)) ≐ H := (congrSnd f1).eqTrans (snd_pair _ _)
  have hM : Γ ⊢[PRAAx] fstT (sndT (Yc t H M K e x)) ≐ M := (congrFst s1).eqTrans (fst_pair _ _)
  have hK : Γ ⊢[PRAAx] fstT (fstT (sndT (sndT (Yc t H M K e x)))) ≐ K := (congrFst f2).eqTrans (fst_pair _ _)
  have he : Γ ⊢[PRAAx] sndT (fstT (sndT (sndT (Yc t H M K e x)))) ≐ e := (congrSnd f2).eqTrans (snd_pair _ _)
  have hx : Γ ⊢[PRAAx] sndT (sndT (sndT (Yc t H M K e x))) ≐ x := (congrSnd s2).eqTrans (snd_pair _ _)
  have hr := congrAdd hK (.eqRefl j)
  exact congrAp2 _ (congrSucc (DyadicAssembly.Nm_congr hr hH))
    (congrPairT ht (congrPairT hM (congrPairT (congrPairT hr he) hx)))

/-! ## No crossing, no bad index -/

/-- The block count `J = (⌊log₂ H⌋ + 1) ∸ K`. -/
abbrev Jb (H K : PTm n) : PTm n := monus (succ (eb H one)) K

/-- If no block crosses, the bad indicator vanishes at every `m ≤ H`. -/
theorem bad_zero {m t H M K e x : PTm n}
    (hS : Γ ⊢[PRAAx] ap2 (sumF (cjB w0 X0)) (Jb H K) (Yc t H M K e x) ≐ zero) (hm : Γ ⊢[PRAAx] lt m (succ H)) :
    Γ ⊢[PRAAx] inst2 (bdB w0 X0) m (Zc t M K e x) ≐ zero := by
  refine (inst2_bd w0 X0 m t M K e x).eqTrans ?_
  refine .orE (lt_or_le m (pw two K)) ((congrMul (ge_of_lt Prf.hyp0) (.eqRefl _)).eqTrans (zero_mul _)) ?_
  let C : List (Fm PTm n) := le (pw two K) m :: Γ
  have h2K : C ⊢[PRAAx] le (pw two K) m := Prf.hyp0
  refine .orE (lt_or_le (inst2 (DB (lw w0) (lw X0)) m (Zc t M K e x))
      ((two * e * m * Wk w0 M K e x) * (two * e * m * Wk w0 M K e x)))
    ((congrMul (.eqRefl _) (ge_of_lt Prf.hyp0)).eqTrans (mul_zero _)) ?_
  let C2 : List (Fm PTm n) := le ((two * e * m * Wk w0 M K e x) * (two * e * m * Wk w0 M K e x))
    (inst2 (DB (lw w0) (lw X0)) m (Zc t M K e x)) :: C
  have hcD : C2 ⊢[PRAAx] le ((two * e * m * Wk w0 M K e x) * (two * e * m * Wk w0 M K e x))
      (inst2 (DB (lw w0) (lw X0)) m (Zc t M K e x)) := Prf.hyp0
  have h2K' : C2 ⊢[PRAAx] le (pw two K) m := h2K.wk
  have hm' : C2 ⊢[PRAAx] lt m (succ H) := hm.wk.wk
  have hS' : C2 ⊢[PRAAx] ap2 (sumF (cjB w0 X0)) (Jb H K) (Yc t H M K e x) ≐ zero := hS.wk.wk
  -- the block of `m`
  have hm1 : C2 ⊢[PRAAx] le one m :=
    le_trans (AnalyticNumberTheory.PhiLower.one_le_pos (AnalyticNumberTheory.Valuation.pw_pos' two_pos K)) h2K'
  have sp := eb_spec (le_refl one) hm1
  have hKr : C2 ⊢[PRAAx] le K (eb m one) := eb_ge hm1 (le_congr (one_mul _).eqSymm (.eqRefl _) h2K')
  have hmH : C2 ⊢[PRAAx] le m H := (succ_monus_succ _ _).eqSymm.eqTrans hm'
  have hH1 : C2 ⊢[PRAAx] le one H := le_trans hm1 hmH
  have spH := eb_spec (le_refl one) hH1
  have hq : C2 ⊢[PRAAx] le (m * one) (H * one) :=
    le_congr (by ipra_ring) (by ipra_ring) hmH
  have hrH : C2 ⊢[PRAAx] le (eb m one) (eb H one) := exp_le (le_refl one) (Prf.andE₁ sp) (Prf.andE₂ spH) hq
  -- the block index `j = r ∸ K < J`
  have eK := eq_add_of_le hKr
  have eH := eq_add_of_le hrH
  have hjJ : C2 ⊢[PRAAx] lt (monus (eb m one) K) (Jb H K) := by
    have e1 : C2 ⊢[PRAAx] succ (eb H one) ≐ K + (succ (monus (eb m one) K) + monus (eb H one) (eb m one)) := by
      ipra_lc natEq eH + natEq eK
    have e2 : C2 ⊢[PRAAx] Jb H K ≐ succ (monus (eb m one) K) + monus (eb H one) (eb m one) :=
      (congrMonus e1 (.eqRefl _)).eqTrans (add_monus' _ _)
    exact le_of_eq_add (d := monus (eb H one) (eb m one)) e2
  have c0 := (inst2_cj (Γ := C2) w0 X0 (monus (eb m one) K) t H M K e x).eqSymm.eqTrans
    (sum_zero_elim (cjB w0 X0) hS' hjJ)
  -- the crossing at `m` in block `r = K + j`
  have er : C2 ⊢[PRAAx] K + monus (eb m one) K ≐ eb m one := eK.eqSymm
  have h1 : C2 ⊢[PRAAx] le m (pw two (succ (K + monus (eb m one) K))) :=
    le_congr (.eqRefl _) ((one_mul _).eqTrans (congrAp2 powF (congrSucc er.eqSymm) (.eqRefl _))) (le_of_lt (Prf.andE₂ sp))
  have hi : C2 ⊢[PRAAx] lt m (succ (Nm (K + monus (eb m one) K) H)) := (succ_monus_succ _ _).eqTrans (le_Nm h1 hmH)
  have hc : C2 ⊢[PRAAx] le (inst2 (Cv (aB w0) * Cv (aB w0)) m (pairT t (pairT M (pairT (pairT (K + monus (eb m one) K) e) x))))
      (inst2 (DB (lw w0) (lw X0)) m (pairT t (pairT M (pairT (pairT (K + monus (eb m one) K) e) x)))) := by
    rw [Expectation.inst2_mul']
    have ca := (Cv_at (Γ := C2) (aB w0) m t M (pairT (pairT (K + monus (eb m one) K) e) x)).eqTrans
      ((aB_at w0 M _ e x).eqTrans (congrMul (.eqRefl _) (sum_lift w0 M _ e x)))
    have dD := (db_lift (Γ := C2) w0 X0 m t M (K + monus (eb m one) K) e x).eqTrans
      (db_lift (Γ := C2) w0 X0 m t M K e x).eqSymm
    have wk := sum_lift (Γ := C2) w0 M K e x
    have p2 : C2 ⊢[PRAAx] le (pw two (K + monus (eb m one) K)) m :=
      le_congr ((one_mul _).eqTrans (congrAp2 powF er.eqSymm (.eqRefl _))) (.eqRefl _) (Prf.andE₁ sp)
    have q : C2 ⊢[PRAAx] le (two * e * pw two (K + monus (eb m one) K) * ap2 (sumF w0) M x)
        (two * e * m * Wk w0 M K e x) :=
      le_congr (.eqRefl _) (congrMul (.eqRefl _) wk.eqSymm)
        (le_mul_mono (le_mul_mono (le_refl _) p2) (le_refl _))
    refine le_congr (congrMul ca ca).eqSymm dD.eqSymm (le_trans (le_mul_mono q q) hcD)
  have cw := crossing_witness (Cv (aB w0) * Cv (aB w0)) (DB (lw w0) (lw X0)) hi hc
  exact succ_ne_zero' _ (cw.eqSymm.eqTrans c0)

/-- `cover_pt`: `1 ∸ ∏_{n≤H}(1 ∸ bad_n(t)) ≤ Σ_{j<J} C_j(t)`. -/
theorem cover_pt (t H M K e x : PTm n) :
    Γ ⊢[PRAAx] le (monus one (ap2 (prodF (monus one (bdB w0 X0))) (succ H) (Zc t M K e x)))
      (ap2 (sumF (cjB w0 X0)) (Jb H K) (Yc t H M K e x)) := by
  refine .orE (zero_or_succ (ap2 (sumF (cjB w0 X0)) (Jb H K) (Yc t H M K e x))) ?_ ?_
  · let C : List (Fm PTm n) := (ap2 (sumF (cjB w0 X0)) (Jb H K) (Yc t H M K e x) ≐ zero) :: Γ
    have hS : C ⊢[PRAAx] ap2 (sumF (cjB w0 X0)) (Jb H K) (Yc t H M K e x) ≐ zero := Prf.hyp0
    have hS' : (C.map Fm.shift) ⊢[PRAAx] ap2 (sumF (cjB w0 X0)) (Jb (Syn.shift H) (Syn.shift K))
        (Yc (Syn.shift t) (Syn.shift H) (Syn.shift M) (Syn.shift K) (Syn.shift e) (Syn.shift x)) ≐ zero := by
      simpa [Fm.shift, Syn.shift] using hS.shift
    have hp : C ⊢[PRAAx] ap2 (prodF (monus one (bdB w0 X0))) (succ H) (Zc t M K e x) ≐ one := by
      refine (prod_congr_bounded (monus one (bdB w0 X0)) (one : PTm 2) (Zc t M K e x) (Zc t M K e x) (succ H) (.allI (.impI ?_))).eqTrans (prod_one _ _)
      have sz : Syn.shift (Zc t M K e x) = Zc (Syn.shift t) (Syn.shift M) (Syn.shift K) (Syn.shift e) (Syn.shift x) := by
        simp [Syn.shift]
      have hm : (lt (var 0) (Syn.shift (succ H)) :: C.map Fm.shift) ⊢[PRAAx] lt (var 0) (succ (Syn.shift H)) := Prf.hyp0
      have bz := bad_zero (Γ := lt (var 0) (Syn.shift (succ H)) :: C.map Fm.shift) w0 X0 hS'.wk hm
      have e1 : inst2 (monus one (bdB w0 X0)) (var 0) (Syn.shift (Zc t M K e x)) =
          monus one (inst2 (bdB w0 X0) (var 0) (Syn.shift (Zc t M K e x))) := by simp [inst2]
      have e2 : inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift (Zc t M K e x)) = one := by simp [inst2]
      rw [e1, e2, sz]
      exact (congrMonus (.eqRefl _) bz).eqTrans (monus_zero _)
    refine le_congr ((congrMonus (.eqRefl _) hp).eqTrans (monus_self _)).eqSymm (.eqRefl _) (zero_le _)
  · let C : List (Fm PTm n) := (ap2 (sumF (cjB w0 X0)) (Jb H K) (Yc t H M K e x) ≐
      succ (pred (ap2 (sumF (cjB w0 X0)) (Jb H K) (Yc t H M K e x)))) :: Γ
    exact le_trans (monus_le_self one _) (AnalyticNumberTheory.PhiLower.one_le_pos (Prf.hyp0 : C ⊢[PRAAx] _))

end Cover

end LeanProofs.IPRA.Probability.DyadicCover
