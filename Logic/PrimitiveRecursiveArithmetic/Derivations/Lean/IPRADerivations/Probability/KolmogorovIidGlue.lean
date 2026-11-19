import IPRADerivations.Probability.KolmogorovIid

/-!
# Kolmogorov's maximal inequality for an iid sample: the low-digit invariance of the crossing events

Packet: `probability/expected_value_ipra_2026-11-16`, `thm:kolmogorov`: "`A_k` depends only on the first `k`
coordinates". For the code `t = i M^k + j` (`j < M^k`) of the product law, the partial sums `S_l` with
`l ≤ k`, hence the levels `D_l`, and hence the first-crossing indicator `I_k`, are those of the low block `j`.
The threshold is a body `a(M, x)` read from the parameter (`Cv a`), the same at every index.

* `Cv`, `Cv_at`: the constant body `g(M, x)` over `(j, ⟨r, ⟨M, x⟩⟩)`;
* `S_low`: `S_l(i M^k + j) = S_l(j)` for `l ≤ k`;
* `D_low`: `D_l(i M^k + j) = D_l(j)` for `l ≤ k`;
* `I_low`: `I_k(i M^k + j) = I_k(j)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.KolmogorovIidGlue

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul' inst2_add')
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.ProductPower (Pr Sr TB SB TB_at SB_at Tt dg wdB xdB low_congr)
open LeanProofs.IPRA.Probability.FirstCrossing (Ib nbB inst2_Ib inst2_nbB disjoint)
open LeanProofs.IPRA.Probability.KolmogorovIid (congrAd DB DB_at IB)
open LeanProofs.IPRA.Probability.KolmogorovIid (kB kB_at wP vF Pp Np Pf Nf aP Yp wP_at vF_at Pp_at Np_at Pf_at Nf_at
  aP_at past_hyp future_mean)
open LeanProofs.IPRA.Probability.KolmogorovStep (Zf crossing_step inst3_monus)
open LeanProofs.IPRA.Probability.KolmogorovAssembly (lift inst3_lift assembly)
open LeanProofs.IPRA.Probability.Independence (dsum inst3_mul' inst3_add' inst3_pmB inst3_spB sum_scale shift_sum)
open LeanProofs.IPRA.Probability.ProductSplit (pr_split sr_split)
open LeanProofs.IPRA.BlockSum (blk_at block_sum blkB)
open LeanProofs.IPRA.Foundations.MixedRadix (shift_le')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The constant body `g(M, x)` over `(j, ⟨r, ⟨M, x⟩⟩)`. -/
def Cv (g : PTm 2) : PTm 2 := Syn.subst ![fstT (sndT (var 1)), sndT (sndT (var 1))] g

theorem Cv_at (g : PTm 2) (j r M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (Cv g) j (pairT r (pairT M x)) ≐ inst2 g M x := by
  have e : inst2 (Cv g) j (pairT r (pairT M x)) =
      inst2 g (fstT (sndT (pairT r (pairT M x)))) (sndT (sndT (pairT r (pairT M x)))) := by
    simp only [inst2, Cv, Syn.subst_subst]
    congr 1; funext i; fin_cases i <;> simp
  rw [e]
  exact congrInst2 g ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))

section Low

variable (w X a : PTm 2)

theorem shift_code (i j k M : PTm n) :
    Syn.shift (i * pw M k + j) = Syn.shift i * pw (Syn.shift M) (Syn.shift k) + Syn.shift j := by
  simp [Syn.shift]

/-- `S_l(i M^k + j) = S_l(j)` for `l ≤ k`. -/
theorem S_low {M i j k l x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hl : Γ ⊢[PRAAx] le l k) :
    Γ ⊢[PRAAx] Sr X l (i * pw M k + j) M x ≐ Sr X l j M x := by
  have lc := (low_congr X (a := i) (u := j) (r := k) (x := x) hM).allOpen
  exact sum_congr_bounded _ _ _ _ _ (.allI (.impI (Prf.impE lc.wk (lt_of_lt_of_le Prf.hyp0 (shift_le' hl).wk))))

/-- `D_l(i M^k + j) = D_l(j)` for `l ≤ k`. -/
theorem D_low {M i j k l x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hl : Γ ⊢[PRAAx] le l k) :
    Γ ⊢[PRAAx] inst2 (DB w X) l (pairT (i * pw M k + j) (pairT M x)) ≐ inst2 (DB w X) l (pairT j (pairT M x)) := by
  have s := S_low X (i := i) (j := j) (x := x) hM hl
  have u := congrAd (congrMul (.eqRefl (ap2 (sumF w) M x)) s) (.eqRefl (l * ap2 (sumF (w * X)) M x))
  exact (DB_at w X l _ M x).eqTrans ((congrMul u u).eqTrans (DB_at w X l j M x).eqSymm)

/-- The threshold `a(M, x)²` does not depend on the outcome. -/
theorem c_any (l t u M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (Cv a * Cv a) l (pairT t (pairT M x)) ≐ inst2 (Cv a * Cv a) l (pairT u (pairT M x)) := by
  rw [inst2_mul', inst2_mul']
  have e₁ := Cv_at (Γ := Γ) a l t M x
  have e₂ := Cv_at (Γ := Γ) a l u M x
  exact congrMul (e₁.eqTrans e₂.eqSymm) (e₁.eqTrans e₂.eqSymm)

/-- `I_k(i M^k + j) = I_k(j)`: the first-crossing event at `k` depends only on the low block. -/
theorem I_low {M i j k x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) :
    Γ ⊢[PRAAx] inst2 (IB w X (Cv a)) k (pairT (i * pw M k + j) (pairT M x)) ≐
      inst2 (IB w X (Cv a)) k (pairT j (pairT M x)) := by
  rw [inst2_Ib, inst2_Ib]
  refine congrMul (congrMonus (.eqRefl _) (congrMonus (c_any a k _ _ M x) (D_low w X hM (le_refl k)))) ?_
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
    simpa [Fm.shift, Syn.shift] using hM.shift
  refine prod_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT, shift_code]
  rw [inst2_nbB, inst2_nbB]
  have hl : (lt (var 0) (Syn.shift k) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift k) :=
    le_trans (le_succ_self _) Prf.hyp0
  exact congrMonus (.eqRefl _) (congrMonus (.eqRefl _)
    (congrMonus (c_any a _ _ _ _ _) (D_low w X hM'.wk hl)))

end Low

/-! ## One crossing step on the `n`-fold law -/

section Step

variable (w X a : PTm 2)

theorem shift_pw (u v : PTm n) : Syn.shift (pw u v) = pw (Syn.shift u) (Syn.shift v) := by simp [Syn.shift]

theorem shift_mulpw (i k M : PTm n) :
    Syn.shift (i * pw M k) = Syn.shift i * pw (Syn.shift M) (Syn.shift k) := by simp [Syn.shift]

theorem shift_Pr (r t M x : PTm n) :
    Syn.shift (Pr w r t M x) = Pr w (Syn.shift r) (Syn.shift t) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]

/-- The indicator `I(k, t, ⟨n, z⟩) = I_k(⟨t, z⟩)` as a body of the crossing index and the outcome. -/
def I3 : PTm 3 := Syn.subst ![var 0, pairT (var 1) (sndT (var 2))] (IB w X (Cv a))

theorem inst3_I3 (k t y : PTm n) :
    inst3 (I3 w X a) k t y = inst2 (IB w X (Cv a)) k (pairT t (sndT y)) := by
  simp only [inst3, inst2, I3, Syn.subst_subst]
  congr 1; funext i; fin_cases i <;> simp

/-- `I_k(t) P_n(t) a²`. -/
abbrev A1 : PTm 3 := I3 w X a * lift (TB w * Cv (a * a))
/-- `I_k(t) P_n(t) D_n(t)`. -/
abbrev A2 : PTm 3 := I3 w X a * lift (TB w * kB (DB w X))

theorem shift_hn {k m n' : PTm n} (hn : Γ ⊢[PRAAx] n' ≐ k + m) :
    Γ.map Fm.shift ⊢[PRAAx] Syn.shift n' ≐ Syn.shift k + Syn.shift m := by
  simpa [Fm.shift, Syn.shift] using hn.shift

/-- `P_n(i M^k + j) = P_k(j) P_m(i)` for `n = k + m`. -/
theorem P_val {M i j k m n' x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hn : Γ ⊢[PRAAx] n' ≐ k + m)
    (hj : Γ ⊢[PRAAx] lt j (pw M k)) :
    Γ ⊢[PRAAx] inst2 (TB w) (i * pw M k + j) (pairT n' (pairT M x)) ≐ Pr w k j M x * Pr w m i M x :=
  (TB_at w _ n' M x).eqTrans ((congrAp2 (prodF (wdB w)) hn (.eqRefl _)).eqTrans (pr_split w hM hj))

/-- The summand of the left side at `t = i M^k + j`. -/
theorem A1_val {M i j k m n' x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hn : Γ ⊢[PRAAx] n' ≐ k + m)
    (hj : Γ ⊢[PRAAx] lt j (pw M k)) :
    Γ ⊢[PRAAx] inst3 (A1 w X a) k (i * pw M k + j) (pairT n' (pairT M x)) ≐
      Pr w m i M x * inst2 (wP w X (Cv a) * (aP (Cv a) * aP (Cv a))) j (Yp k m M x) := by
  rw [inst3_mul', inst3_I3, inst3_lift, inst2_mul' (TB w) (Cv (a * a)),
    inst2_mul' (wP w X (Cv a)) (aP (Cv a) * aP (Cv a)), inst2_mul' (aP (Cv a)) (aP (Cv a))]
  have eI := (congrInst2 (IB w X (Cv a)) (.eqRefl k) (congrPairT (.eqRefl _) (snd_pair n' (pairT M x)))).eqTrans
    (I_low w X a (i := i) (j := j) (k := k) (x := x) hM)
  have eP := P_val w (i := i) (x := x) hM hn hj
  have eC : Γ ⊢[PRAAx] inst2 (Cv (a * a)) (i * pw M k + j) (pairT n' (pairT M x)) ≐ inst2 a M x * inst2 a M x := by
    have c := Cv_at (Γ := Γ) (a * a) (i * pw M k + j) n' M x
    rw [inst2_mul'] at c
    exact c
  have ew := wP_at (Γ := Γ) w X (Cv a) j k m M x
  have ea := (aP_at (Γ := Γ) (Cv a) j k m M x).eqTrans (Cv_at a k j M x)
  refine (congrMul eI (congrMul eP eC)).eqTrans (.eqTrans ?_ (congrMul (.eqRefl _) (congrMul ew (congrMul ea ea))).eqSymm)
  apply deriveNat; ipra_simps; ring

/-- The summand of the right side at `t = i M^k + j`, against the cleared square of `crossing_step`. -/
theorem A2_val {M i j k m n' x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hn : Γ ⊢[PRAAx] n' ≐ k + m)
    (hj : Γ ⊢[PRAAx] lt j (pw M k)) :
    Γ ⊢[PRAAx] inst3 (A2 w X a) k (i * pw M k + j) (pairT n' (pairT M x)) ≐
      inst3 (Zf (wP w X (Cv a)) (vF w) (Pp w X) (Np w X) (Pf w X) (Nf w X)) j i (Yp k m M x) := by
  simp only [Zf, inst3_mul', inst3_add', inst3_pmB, inst3_spB, inst3_monus]
  rw [inst3_I3, inst3_lift, inst2_mul' (TB w) (kB (DB w X))]
  have eI := (congrInst2 (IB w X (Cv a)) (.eqRefl k) (congrPairT (.eqRefl _) (snd_pair n' (pairT M x)))).eqTrans
    (I_low w X a (i := i) (j := j) (k := k) (x := x) hM)
  have eP := P_val w (i := i) (x := x) hM hn hj
  have eD := (kB_at (Γ := Γ) (DB w X) (i * pw M k + j) n' (pairT M x)).eqTrans (DB_at w X n' _ M x)
  have es := (congrAp2 (sumF (xdB X)) hn (.eqRefl _)).eqTrans (sr_split X (i := i) (x := x) hM hj)
  have esN := natEq es
  have hnN := natEq hn
  have h₁ : Γ ⊢[PRAAx] inst2 (Pp w X) j (Yp k m M x) + inst2 (Pf w X) i (Yp k m M x) ≐
      ap2 (sumF w) M x * Sr X n' (i * pw M k + j) M x := by
    have p₁ := natEq (Pp_at (Γ := Γ) w X j k m M x)
    have p₂ := natEq (Pf_at (Γ := Γ) w X i k m M x)
    apply deriveNat; ipra_simps
    rw [p₁, p₂]
    linear_combination -(𝔟 (ap2 (sumF w) M x)) * esN
  have h₂ : Γ ⊢[PRAAx] inst2 (Np w X) j (Yp k m M x) + inst2 (Nf w X) i (Yp k m M x) ≐
      n' * ap2 (sumF (w * X)) M x := by
    have p₁ := natEq (Np_at (Γ := Γ) w X j k m M x)
    have p₂ := natEq (Nf_at (Γ := Γ) w X i k m M x)
    apply deriveNat; ipra_simps
    rw [p₁, p₂]
    linear_combination -(𝔟 (ap2 (sumF (w * X)) M x)) * hnN
  have U := congrAd h₁ h₂
  have ew := wP_at (Γ := Γ) w X (Cv a) j k m M x
  have ev := vF_at (Γ := Γ) w i k m M x
  refine (congrMul eI (congrMul eP eD)).eqTrans (.eqTrans ?_ (congrMul (congrMul ew ev) (congrMul U U)).eqSymm)
  apply deriveNat; ipra_simps; ring

/-- The block `i` of the left side: `∑_{j<M^k} I_k P_n a² (i M^k + j) = P_m(i) · ∑_j P_k I_k a²`. -/
theorem inner_L {M k m n' x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hn : Γ ⊢[PRAAx] n' ≐ k + m) (i : PTm n) :
    Γ ⊢[PRAAx] inst2 (blkB (rowB (A1 w X a))) i (pairT (pw M k) (pairT k (pairT n' (pairT M x)))) ≐
      Pr w m i M x * Ew (wP w X (Cv a)) (aP (Cv a) * aP (Cv a)) (pw M k) (Yp k m M x) := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
    simpa [Fm.shift, Syn.shift] using hM.shift
  refine (blk_at _ i (pw M k) _).eqTrans (sum_scale _ _ (pw M k) (Pr w m i M x) (Yp k m M x) _ (.allI (.impI ?_)))
  simp only [Yp, shift_pairT, shift_mulpw, shift_Pr, shift_pw]
  rw [inst2_offB, inst2_rowB]
  refine (congrInst3 (A1 w X a) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    (congrAdd (fst_pair _ _) (.eqRefl _)) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans ?_
  exact A1_val w X a hM'.wk (shift_hn hn).wk Prf.hyp0

/-- The left side of the step: `∑_{t<M^n} I_k P_n a² = T_m ∑_{j<M^k} P_k I_k a²`. -/
theorem LT_eq {M k m n' x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hn : Γ ⊢[PRAAx] n' ≐ k + m) :
    Γ ⊢[PRAAx] inst2 (oB (A1 w X a)) k (pairT (pw M n') (pairT n' (pairT M x))) ≐
      Ew (wP w X (Cv a)) (aP (Cv a) * aP (Cv a)) (pw M k) (Yp k m M x) * Tt w m M x := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
    simpa [Fm.shift, Syn.shift] using hM.shift
  have b₀ : Γ ⊢[PRAAx] pw M n' ≐ pw M m * pw M k :=
    (Combinatorics.BinomialTheorem.congrPw (.eqRefl M) hn).eqTrans ((pw_add M k m).eqTrans (mul_comm _ _))
  refine (oB_at _ k _ _).eqTrans ((congrAp2 (sumF (rowB (A1 w X a))) b₀ (.eqRefl _)).eqTrans
    ((block_sum _ (pw M m) (pw M k) _).eqTrans (sum_scale _ (TB w) (pw M m) _ (pairT m (pairT M x)) _
      (.allI (.impI ?_)))))
  simp only [Ew, Yp, shift_pairT, shift_pw, shift_sum]
  exact (inner_L w X a hM'.wk (shift_hn hn).wk (var 0)).eqTrans
    ((mul_comm _ _).eqTrans (congrMul (.eqRefl _) (TB_at w (var 0) _ _ _).eqSymm))

/-- The block `i` of the right side. -/
theorem inner_R {M k m n' x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hn : Γ ⊢[PRAAx] n' ≐ k + m) (i : PTm n) :
    Γ ⊢[PRAAx] inst2 (blkB (rowB (A2 w X a))) i (pairT (pw M k) (pairT k (pairT n' (pairT M x)))) ≐
      inst2 (pB (Zf (wP w X (Cv a)) (vF w) (Pp w X) (Np w X) (Pf w X) (Nf w X))) i (pairT (pw M k) (Yp k m M x)) := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
    simpa [Fm.shift, Syn.shift] using hM.shift
  have pB_eq : Γ ⊢[PRAAx] inst2 (pB (Zf (wP w X (Cv a)) (vF w) (Pp w X) (Np w X) (Pf w X) (Nf w X))) i
      (pairT (pw M k) (Yp k m M x)) ≐
      ap2 (sumF (colB (Zf (wP w X (Cv a)) (vF w) (Pp w X) (Np w X) (Pf w X) (Nf w X)))) (pw M k)
        (pairT i (Yp k m M x)) := by
    rw [inst2_pB]
    exact congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))
  refine (blk_at _ i (pw M k) _).eqTrans (.eqTrans (sum_congr_bounded _ _ _ _ (pw M k) (.allI (.impI ?_))) pB_eq.eqSymm)
  simp only [Yp, shift_pairT, shift_mulpw, shift_pw]
  rw [inst2_offB, inst2_rowB, inst2_colB]
  refine (congrInst3 (A2 w X a) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    (congrAdd (fst_pair _ _) (.eqRefl _)) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))).eqTrans
    (.eqTrans ?_ (congrInst3 _ (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqSymm)
  exact A2_val w X a hM'.wk (shift_hn hn).wk Prf.hyp0

/-- The right side of the step: `∑_{t<M^n} I_k P_n D_n` is the double sum of `crossing_step`. -/
theorem RT_eq {M k m n' x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hn : Γ ⊢[PRAAx] n' ≐ k + m) :
    Γ ⊢[PRAAx] inst2 (oB (A2 w X a)) k (pairT (pw M n') (pairT n' (pairT M x))) ≐
      dsum (Zf (wP w X (Cv a)) (vF w) (Pp w X) (Np w X) (Pf w X) (Nf w X)) (pw M k) (pw M m) (Yp k m M x) := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
    simpa [Fm.shift, Syn.shift] using hM.shift
  have b₀ : Γ ⊢[PRAAx] pw M n' ≐ pw M m * pw M k :=
    (Combinatorics.BinomialTheorem.congrPw (.eqRefl M) hn).eqTrans ((pw_add M k m).eqTrans (mul_comm _ _))
  refine (oB_at _ k _ _).eqTrans ((congrAp2 (sumF (rowB (A2 w X a))) b₀ (.eqRefl _)).eqTrans
    ((block_sum _ (pw M m) (pw M k) _).eqTrans (.eqTrans (sum_congr_bounded _ _ _ _ (pw M m) (.allI (.impI ?_)))
      (fubini _ (pw M k) (pw M m) _).eqSymm)))
  simp only [Yp, shift_pairT, shift_pw]
  exact inner_R w X a hM'.wk (shift_hn hn).wk (var 0)

/-- One crossing step of `thm:kolmogorov` on the `n`-fold law:
`∑_{t<M^n} I_k P_n a² ≤ ∑_{t<M^n} I_k P_n D_n` for `n = k + m`. -/
theorem step_k {M k m n' x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hn : Γ ⊢[PRAAx] n' ≐ k + m) :
    Γ ⊢[PRAAx] le (inst2 (oB (A1 w X a)) k (pairT (pw M n') (pairT n' (pairT M x))))
      (inst2 (oB (A2 w X a)) k (pairT (pw M n') (pairT n' (pairT M x)))) := by
  have cs := crossing_step (wP w X (Cv a)) (vF w) (Pp w X) (Np w X) (Pf w X) (Nf w X) (aP (Cv a))
    (pw M k) (pw M m) (Yp k m M x) (past_hyp w X (Cv a) k m M x) (future_mean w X hM k m)
  have ew : Γ ⊢[PRAAx] Wt (vF w) (pw M m) (Yp k m M x) ≐ Tt w m M x := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [Yp, shift_pairT]
    exact (vF_at w (var 0) _ _ _ _).eqTrans (TB_at w (var 0) _ _ _).eqSymm
  exact le_congr ((congrMul ew (.eqRefl _)).eqTrans ((mul_comm _ _).eqTrans (LT_eq w X a hM hn).eqSymm))
    (RT_eq w X a hM hn).eqSymm cs

/-! ## The maximal inequality -/

/-- `thm:kolmogorov` for an iid sample: with `D_l = |W S_l − l S|²` and the first-crossing indicators `I_k`
of the threshold `a²`,
`∑_{k≤n} ∑_{t<M^n} P_n(t) a² I_k(t) ≤ ∑_{t<M^n} P_n(t) D_n(t)`,
i.e. `a² P(max_{k≤n} W² (S_k − k μ)² ≥ a²) ≤ E[W² (S_n − n μ)²]`. -/
theorem kolmogorov_iid {M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (n' x : PTm n) :
    Γ ⊢[PRAAx] le (dsum (A1 w X a) (succ n') (pw M n') (pairT n' (pairT M x)))
      (Ew (TB w) (kB (DB w X)) (pw M n') (pairT n' (pairT M x))) := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
    simpa [Fm.shift, Syn.shift] using hM.shift
  refine assembly (I3 w X a) (TB w) (Cv (a * a)) (kB (DB w X)) (succ n') (pw M n') _ (.allI (.impI ?_))
    (.allI (.impI ?_))
  · simp only [shift_pairT, shift_pw, shift_succ'']
    have h₀ : (lt (var 0) (succ (Syn.shift n')) :: Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (succ (Syn.shift n')) :=
      Prf.hyp0
    have hk : (lt (var 0) (succ (Syn.shift n')) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift n') := by
      ipra_le sl h₀
    exact step_k w X a hM'.wk (eq_add_of_le hk)
  · simp only [shift_pairT, shift_succ'']
    rw [inst2_pB]
    have e : (lt (var 0) (Syn.shift (pw M n')) :: Γ.map Fm.shift) ⊢[PRAAx]
        ap2 (sumF (colB (I3 w X a))) (fstT (pairT (succ (Syn.shift n')) (pairT (Syn.shift n') (pairT (Syn.shift M) (Syn.shift x)))))
          (pairT (var 0) (sndT (pairT (succ (Syn.shift n')) (pairT (Syn.shift n') (pairT (Syn.shift M) (Syn.shift x)))))) ≐
        ap2 (sumF (IB w X (Cv a))) (succ (Syn.shift n')) (pairT (var 0) (pairT (Syn.shift M) (Syn.shift x))) := by
      refine (congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans
        (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))
      simp only [shift_pairT]
      rw [inst2_colB, inst3_I3]
      exact congrInst2 _ (.eqRefl _) (congrPairT (fst_pair _ _) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))
    exact le_congr e.eqSymm (.eqRefl _) (disjoint (Cv a * Cv a) (DB w X) _ _)

end Step

end LeanProofs.IPRA.Probability.KolmogorovIidGlue
