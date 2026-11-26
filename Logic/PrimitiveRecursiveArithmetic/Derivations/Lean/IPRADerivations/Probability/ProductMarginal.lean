import IPRADerivations.Probability.KolmogorovIidGlue

/-!
# The marginal of the first coordinates of the product law

Packet: `probability/expected_value_ipra_2026-11-16` (used by `thm:kolmogorov` and `thm:dyadic-slln`): an
observable of the first `k` coordinates of an iid sample has the same expectation under the `(k + m)`-fold law
as under the `k`-fold law. For the code `t < M^{k+m}` the first `k` coordinates are the low block
`t mod M^k`, so such an observable is `h(t mod M^k)`.

With the parameter `Y = ⟨k, ⟨m, ⟨M, x⟩⟩⟩` of `Probability/KolmogorovIid`:

* `ρn`, `rpn_at`: the selector `⟨k + m, ⟨M, x⟩⟩`;
* `hr`, `hr_at`: the observable `h(t mod M^k, ⟨k, ⟨M, x⟩⟩)` of the low block;
* `marginal`: `∑_{t<M^{k+m}} P_{k+m}(t) h(t mod M^k) = T_m · ∑_{j<M^k} P_k(j) h(j)`, i.e.
  `E_{k+m}[h(t mod M^k)] = E_k[h]` after division by the total weights `T_{k+m} = T_k T_m`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.ProductMarginal

open_ipra
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul' inst2_add')
open LeanProofs.IPRA.Probability.Independence (sum_scale shift_sum)
open LeanProofs.IPRA.Probability.ProductPower (Pr TB TB_at Tt wdB)
open LeanProofs.IPRA.Probability.ProductSplit (pr_split)
open LeanProofs.IPRA.Probability.KolmogorovIid (rp inst2_rp ρk Yp rpk_at)
open LeanProofs.IPRA.Probability.KolmogorovIidGlue (shift_pw shift_mulpw shift_Pr)
open LeanProofs.IPRA.BlockSum (blk_at block_sum blkB qr_block)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `⟨k + m, ⟨M, x⟩⟩` from `⟨k, ⟨m, ⟨M, x⟩⟩⟩`. -/
abbrev ρn : PTm 2 := pairT (fstT (var 1) + fstT (sndT (var 1))) (sndT (sndT (var 1)))

theorem rpn_at (f : PTm 2) (j k m M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (rp f ρn) j (Yp k m M x) ≐ inst2 f j (pairT (k + m) (pairT M x)) := by
  rw [inst2_rp]
  have e : inst2 ρn j (Yp k m M x) =
      pairT (fstT (Yp k m M x) + fstT (sndT (Yp k m M x))) (sndT (sndT (Yp k m M x))) := by simp [inst2]
  rw [e]
  exact congrInst2 f (.eqRefl _) (congrPairT
    (congrAdd (fst_pair _ _) (snd_pair _ _).fstE)
    (snd_pair _ _).sndE)

/-- The observable `h(t mod M^k, ⟨k, ⟨M, x⟩⟩)` over `(t, ⟨k, ⟨m, ⟨M, x⟩⟩⟩)`. -/
def hr (h : PTm 2) : PTm 2 :=
  Syn.subst ![rem (var 0) (pw (fstT (sndT (sndT (var 1)))) (fstT (var 1))), ρk] h

theorem hr_at (h : PTm 2) (t k m M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (hr h) t (Yp k m M x) ≐ inst2 h (rem t (pw M k)) (pairT k (pairT M x)) := by
  have e : inst2 (hr h) t (Yp k m M x) =
      inst2 h (rem t (pw (fstT (sndT (sndT (Yp k m M x)))) (fstT (Yp k m M x))))
        (pairT (fstT (Yp k m M x)) (sndT (sndT (Yp k m M x)))) := by
    simp only [inst2, hr, Syn.subst_subst]
    congr 1; funext i; fin_cases i <;> simp
  rw [e]
  have hM : Γ ⊢[PRAAx] fstT (sndT (sndT (Yp k m M x))) ≐ M :=
    (snd_pair _ _).sndE.fstE
  exact congrInst2 h (congrAp2 remF (.eqRefl t) (Combinatorics.BinomialTheorem.congrPw hM (fst_pair _ _)))
    (congrPairT (fst_pair _ _) (snd_pair _ _).sndE)

section Marginal

variable (w h : PTm 2)

/-- The summand at `t = i M^k + j`: `P_{k+m}(t) h(t mod M^k) = P_m(i) · P_k(j) h(j)`. -/
theorem summand_at {M i j k m x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hj : Γ ⊢[PRAAx] lt j (pw M k)) :
    Γ ⊢[PRAAx] inst2 (rp (TB w) ρn * hr h) (i * pw M k + j) (Yp k m M x) ≐
      Pr w m i M x * inst2 (TB w * h) j (pairT k (pairT M x)) := by
  rw [inst2_mul', inst2_mul']
  have p := (rpn_at (Γ := Γ) (TB w) (i * pw M k + j) k m M x).eqTrans
    ((TB_at w _ (k + m) M x).eqTrans (pr_split w hM hj))
  have r := Prf.andE₂ (qr_block (i := i) (pw_pos' hM k) hj)
  have q := (hr_at (Γ := Γ) h (i * pw M k + j) k m M x).eqTrans (congrInst2 h r (.eqRefl _))
  have t := TB_at (Γ := Γ) w j k M x
  have pN := natEq p; have qN := natEq q; have tN := natEq t
  apply deriveNat; ipra_simps
  rw [pN, qN, tN]; ring

theorem inner_block {M k m x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (i : PTm n) :
    Γ ⊢[PRAAx] inst2 (blkB (rp (TB w) ρn * hr h)) i (pairT (pw M k) (Yp k m M x)) ≐
      Pr w m i M x * ap2 (sumF (TB w * h)) (pw M k) (pairT k (pairT M x)) := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
    simpa [Fm.shift, Syn.shift] using hM.shift
  refine (blk_at _ i (pw M k) _).eqTrans (sum_scale _ _ (pw M k) (Pr w m i M x) (pairT k (pairT M x)) _
    (.allI (.impI ?_)))
  simp only [Yp, shift_pairT, shift_mulpw, shift_Pr, shift_pw]
  rw [inst2_offB]
  refine (congrInst2 _ (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans ?_
  exact summand_at w h hM'.wk Prf.hyp0

/-- `∑_{t<M^{k+m}} P_{k+m}(t) h(t mod M^k) = T_m · ∑_{j<M^k} P_k(j) h(j)`. -/
theorem marginal {M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (k m x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (rp (TB w) ρn * hr h)) (pw M (k + m)) (Yp k m M x) ≐
      Tt w m M x * ap2 (sumF (TB w * h)) (pw M k) (pairT k (pairT M x)) := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
    simpa [Fm.shift, Syn.shift] using hM.shift
  have b₀ : Γ ⊢[PRAAx] pw M (k + m) ≐ pw M m * pw M k := (pw_add M k m).eqTrans (mul_comm _ _)
  refine (congrAp2 (sumF (rp (TB w) ρn * hr h)) b₀ (.eqRefl _)).eqTrans
    ((block_sum _ (pw M m) (pw M k) _).eqTrans ((sum_scale _ (TB w) (pw M m)
      (ap2 (sumF (TB w * h)) (pw M k) (pairT k (pairT M x))) (pairT m (pairT M x)) _ (.allI (.impI ?_))).eqTrans
      (mul_comm _ _)))
  simp only [Yp, shift_pairT, shift_pw, shift_sum]
  exact (inner_block w h hM'.wk (var 0)).eqTrans
    ((mul_comm _ _).eqTrans (congrMul (.eqRefl _) (TB_at w (var 0) _ _ _).eqSymm))

end Marginal

end LeanProofs.IPRA.Probability.ProductMarginal
