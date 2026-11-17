import IPRADerivations.Core.BlockSum
import IPRADerivations.Probability.Expectation
import IPRADerivations.Probability.Independence
import IPRADerivations.Probability.ProductReplacement
import IPRADerivations.Combinatorics.BinomialIdentities

/-!
# The iterated product law and the sample variance

Packet: `probability/expected_value_ipra_2026-11-16` (`thm:sample-var`, `thm:residual`). An `r`-tuple of
outcomes `i_0, …, i_{r−1} < M` of a weighted law `w` is coded by `t = ∑_j i_j M^j < M^r`, with digits
`dg_j(t) = ⌊t / M^j⌋ mod M`; the product law has weights `P_r(t) = ∏_{j<r} w(dg_j(t))` and the sample sum is
`S_r(t) = ∑_{j<r} X(dg_j(t))`.

* `dg_low`, `dg_top`: peeling `t = a M^r + u` (`a < M`, `u < M^r`) keeps the low digits of `u` and gives
  top digit `a`; hence `P_{r+1}(a M^r + u) = P_r(u) w(a)` and `S_{r+1} = S_r(u) + X(a)` (`pr_peel`, `sr_peel`);
* `peel_sum` (from `Core/BlockSum.block_sum`) and `lin3` (linear combinations of three sums) give the
  recursions `T_{r+1} = T_r W`, `A_{r+1} = T_r S + A_r W`, `B_{r+1} = T_r Q + 2 A_r S + B_r W` for
  `T = ∑_t P_r`, `A = ∑_t P_r S_r`, `B = ∑_t P_r S_r²` (`total_succ`, `A_succ`, `B_succ`);
* `total_pow`: `T_r = W^r`;
* `sample_moments` (`thm:sample-var`): `W A = r S T` and `W² T B + r S² T² = W² A² + r W Q T²`,
  i.e. `E[S_r] = r μ`, `Var(S_r) = r σ²` and `Var(X̄_r) = σ²/r`;
* `residual` (`thm:residual`): `W² (r A₂ − B) = r (r − 1) T (W Q − S²)` for `W ≥ 1`, i.e.
  `E[∑_j (X_j − X̄)²] = (r − 1) σ²`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.ProductPower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.BlockSum (qr_block)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The `j`-th base-`M` digit of `t`. -/
abbrev dg (M j t : PTm n) : PTm n := rem (quo t (pw M j)) M

theorem div_eq' {t K : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) : Γ ⊢[PRAAx] t ≐ quo t K * K + rem t K :=
  ((Prf.andE₁ (div_mod t (pred K))).eqTrans (congrAdd (congrMul hK.eqSymm (congrAp2 quoF (.eqRefl _) hK.eqSymm))
    (congrAp2 remF (.eqRefl _) hK.eqSymm))).eqTrans (congrAdd (mul_comm _ _) (.eqRefl _))

theorem rem_lt'' {K : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) (y : PTm n) : Γ ⊢[PRAAx] lt (rem y K) K :=
  lt_congr (congrAp2 remF (.eqRefl _) hK.eqSymm) hK.eqSymm (Prf.andE₂ (div_mod y (pred K)))

/-- `rem (c M + q) M = rem q M`. -/
theorem rem_shift {M c q : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) :
    Γ ⊢[PRAAx] rem (c * M + q) M ≐ rem q M := by
  have dq := natEq (div_eq' (t := q) hM)
  have r := Prf.andE₂ (qr_block (i := c + quo q M) (j := rem q M) hM (rem_lt'' hM q))
  refine .eqTrans ?_ r
  exact congrAp2 remF (by apply deriveNat; ipra_simps; linear_combination dq) (.eqRefl _)

/-- `dg_j(a M^r + u) = dg_j(u)` for `j < r`. -/
theorem dg_low {M a u j r : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hj : Γ ⊢[PRAAx] lt j r) :
    Γ ⊢[PRAAx] dg M j (a * pw M r + u) ≐ dg M j u := by
  have hMj := pw_pos' hM j
  have er : Γ ⊢[PRAAx] r ≐ succ j + monus r (succ j) := eq_add_of_le hj
  -- `M^r = M^j · (M^e · M)` with `e = r − (j + 1)`
  have pr : Γ ⊢[PRAAx] pw M r ≐ pw M j * (pw M (monus r (succ j)) * M) := by
    refine (Combinatorics.BinomialTheorem.congrPw (.eqRefl _) (er.eqTrans (by apply deriveNat; ipra_simps; ring :
      Γ ⊢[PRAAx] succ j + monus r (succ j) ≐ j + succ (monus r (succ j))))).eqTrans ?_
    exact (pw_add _ _ _).eqTrans (congrMul (.eqRefl _) (pw_succ _ _))
  have du := natEq (div_eq' (t := u) hMj)
  have p := natEq pr
  -- `⌊(a M^r + u) / M^j⌋ = a M^e M + ⌊u / M^j⌋`
  have q1 := Prf.andE₁ (qr_block (i := a * (pw M (monus r (succ j)) * M) + quo u (pw M j)) (j := rem u (pw M j)) hMj
    (rem_lt'' hMj u))
  have e1 : Γ ⊢[PRAAx] quo (a * pw M r + u) (pw M j) ≐ (a * pw M (monus r (succ j))) * M + quo u (pw M j) := by
    refine .eqTrans ?_ (q1.eqTrans (by apply deriveNat; ipra_simps; ring))
    exact congrAp2 quoF (by apply deriveNat; ipra_simps; linear_combination 𝔞 a * p + du) (.eqRefl _)
  exact (congrAp2 remF e1 (.eqRefl _)).eqTrans (rem_shift hM)

/-- `dg_r(a M^r + u) = a` for `a < M` and `u < M^r`. -/
theorem dg_top {M a u r : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (ha : Γ ⊢[PRAAx] lt a M)
    (hu : Γ ⊢[PRAAx] lt u (pw M r)) : Γ ⊢[PRAAx] dg M r (a * pw M r + u) ≐ a := by
  have q := Prf.andE₁ (qr_block (i := a) (j := u) (pw_pos' hM r) hu)
  have r0 := Prf.andE₂ (qr_block (i := zero) (j := a) hM ha)
  exact (congrAp2 remF q (.eqRefl _)).eqTrans
    ((congrAp2 remF (by apply deriveNat; ipra_simps; ring : Γ ⊢[PRAAx] a ≐ zero * M + a) (.eqRefl _)).eqTrans r0)

/-! ## The product weight and the sample sum -/

section Peel

variable (w X : PTm 2)

/-- `w(dg_j(t), x)`, over `0 = j`, `1 = ⟨t, ⟨M, x⟩⟩`. -/
abbrev wdB : PTm 2 := Syn.subst ![dg (fstT (sndT (var 1))) (var 0) (fstT (var 1)), sndT (sndT (var 1))] w
/-- `X(dg_j(t), x)`. -/
abbrev xdB : PTm 2 := Syn.subst ![dg (fstT (sndT (var 1))) (var 0) (fstT (var 1)), sndT (sndT (var 1))] X

/-- The product weight `P_r(t) = ∏_{j<r} w(dg_j(t))`. -/
abbrev Pr (r t M x : PTm n) : PTm n := ap2 (prodF (wdB w)) r (pairT t (pairT M x))
/-- The sample sum `S_r(t) = ∑_{j<r} X(dg_j(t))`. -/
abbrev Sr (r t M x : PTm n) : PTm n := ap2 (sumF (xdB X)) r (pairT t (pairT M x))

theorem dB_at (f : PTm 2) (j t M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (Syn.subst ![dg (fstT (sndT (var 1))) (var 0) (fstT (var 1)), sndT (sndT (var 1))] f) j
      (pairT t (pairT M x)) ≐ inst2 f (dg M j t) x := by
  have e : inst2 (Syn.subst ![dg (fstT (sndT (var 1))) (var 0) (fstT (var 1)), sndT (sndT (var 1))] f) j (pairT t (pairT M x)) =
      inst2 f (dg (fstT (sndT (pairT t (pairT M x)))) j (fstT (pairT t (pairT M x)))) (sndT (sndT (pairT t (pairT M x)))) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  rw [e]
  have hM : Γ ⊢[PRAAx] fstT (sndT (pairT t (pairT M x))) ≐ M := (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have ht : Γ ⊢[PRAAx] fstT (pairT t (pairT M x)) ≐ t := fst_pair _ _
  have hx : Γ ⊢[PRAAx] sndT (sndT (pairT t (pairT M x))) ≐ x := (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  exact congrInst2 f (congrAp2 remF (congrAp2 quoF ht (Combinatorics.BinomialTheorem.congrPw hM (.eqRefl _))) hM) hx

/-- The low digits do not see the top coordinate: `∏_{j<r} w(dg_j(a M^r + u)) = P_r(u)`, and the same for the
sum, when `M ≥ 1`. -/
theorem low_congr (f : PTm 2) {M a u r x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift r) ⟶
      (inst2 (Syn.subst ![dg (fstT (sndT (var 1))) (var 0) (fstT (var 1)), sndT (sndT (var 1))] f) (var 0)
        (Syn.shift (pairT (a * pw M r + u) (pairT M x))) ≐
      inst2 (Syn.subst ![dg (fstT (sndT (var 1))) (var 0) (fstT (var 1)), sndT (sndT (var 1))] f) (var 0)
        (Syn.shift (pairT u (pairT M x))))) := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
    simpa [Fm.shift, Syn.shift] using hM.shift
  refine .allI (.impI ?_)
  simp only [shift_pairT]
  rw [show Syn.shift (a * pw M r + u) = Syn.shift a * pw (Syn.shift M) (Syn.shift r) + Syn.shift u by simp [Syn.shift]]
  refine (dB_at f _ _ _ _).eqTrans (.eqTrans ?_ (dB_at f _ _ _ _).eqSymm)
  exact congrInst2 f (dg_low hM'.wk Prf.hyp0) (.eqRefl _)

theorem pr_peel {M a u r x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (ha : Γ ⊢[PRAAx] lt a M)
    (hu : Γ ⊢[PRAAx] lt u (pw M r)) :
    Γ ⊢[PRAAx] Pr w (succ r) (a * pw M r + u) M x ≐ Pr w r u M x * inst2 w a x := by
  refine (Probability.ProductReplacement.prod_succ' _ _ _).eqTrans (congrMul ?_ ?_)
  · exact prod_congr_bounded _ _ _ _ _ (low_congr w hM)
  · exact (dB_at w _ _ _ _).eqTrans (congrInst2 w (dg_top hM ha hu) (.eqRefl _))

theorem sr_peel {M a u r x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (ha : Γ ⊢[PRAAx] lt a M)
    (hu : Γ ⊢[PRAAx] lt u (pw M r)) :
    Γ ⊢[PRAAx] Sr X (succ r) (a * pw M r + u) M x ≐ Sr X r u M x + inst2 X a x := by
  refine (sum_succ' _ _ _).eqTrans (congrAdd ?_ ?_)
  · exact sum_congr_bounded _ _ _ _ _ (low_congr X hM)
  · exact (dB_at X _ _ _ _).eqTrans (congrInst2 X (dg_top hM ha hu) (.eqRefl _))

end Peel

/-! ## Totals of the `r`-fold law -/

theorem shift_inst2' (g : PTm 2) (a b : PTm n) : Syn.shift (inst2 g a b) = inst2 g (Syn.shift a) (Syn.shift b) := by
  simp only [inst2, Syn.shift, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

section Totals

variable (w X : PTm 2)

/-- `P_r(t)`, over `0 = t`, `1 = ⟨r, ⟨M, x⟩⟩`. -/
abbrev TB : PTm 2 := ap2 (prodF (wdB w)) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))
/-- `S_r(t)`. -/
abbrev SB : PTm 2 := ap2 (sumF (xdB X)) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))

/-- `T_r = ∑_{t<M^r} P_r(t)`. -/
abbrev Tt (r M x : PTm n) : PTm n := ap2 (sumF (TB w)) (pw M r) (pairT r (pairT M x))

theorem TB_at (t r M x : PTm n) : Γ ⊢[PRAAx] inst2 (TB w) t (pairT r (pairT M x)) ≐ Pr w r t M x := by
  have e : inst2 (TB w) t (pairT r (pairT M x)) = ap2 (prodF (wdB w)) (fstT (pairT r (pairT M x)))
      (pairT t (sndT (pairT r (pairT M x)))) := by simp [inst2]
  rw [e]; exact congrAp2 (prodF (wdB w)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))

theorem SB_at (t r M x : PTm n) : Γ ⊢[PRAAx] inst2 (SB X) t (pairT r (pairT M x)) ≐ Sr X r t M x := by
  have e : inst2 (SB X) t (pairT r (pairT M x)) = ap2 (sumF (xdB X)) (fstT (pairT r (pairT M x)))
      (pairT t (sndT (pairT r (pairT M x)))) := by simp [inst2]
  rw [e]; exact congrAp2 (sumF (xdB X)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))

/-- Peeling the top coordinate of a sum over `t < M^{r+1}` into `M` blocks of length `M^r`. -/
theorem peel_sum (G : PTm 2) (r M p : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF G) (pw M (succ r)) p ≐ ap2 (sumF (BlockSum.blkB G)) M (pairT (pw M r) p) :=
  (congrAp2 (sumF G) ((pw_succ _ _).eqTrans (mul_comm _ _)) (.eqRefl _)).eqTrans (BlockSum.block_sum G M (pw M r) p)

/-- One block of the total: `∑_{u<M^r} P_{r+1}(a M^r + u) = w(a) T_r` for `a < M`. -/
theorem block_T {a r M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (ha : Γ ⊢[PRAAx] lt a M) :
    Γ ⊢[PRAAx] inst2 (BlockSum.blkB (TB w)) a (pairT (pw M r) (pairT (succ r) (pairT M x))) ≐ inst2 w a x * Tt w r M x := by
  refine (BlockSum.blk_at _ _ _ _).eqTrans ?_
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have ha' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift a) (Syn.shift M) := by
    have e := ha.shift; simp only [Fm.shift, subst_lt, subst_le, ConciseIPRA.PTm.subst_succ] at e; simpa [Syn.shift] using e
  refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_offB, shift_inst2']
  simp only [shift_pairT]
  have hp : Syn.shift (pw M r) = pw (Syn.shift M) (Syn.shift r) := by simp [Syn.shift]
  have hs : Syn.shift (a * pw M r) = Syn.shift a * pw (Syn.shift M) (Syn.shift r) := by simp [Syn.shift]
  rw [hs]
  let C : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (pw M r)) :: Γ.map Fm.shift
  have hu : C ⊢[PRAAx] lt (var 0) (pw (Syn.shift M) (Syn.shift r)) := by rw [← hp]; exact Prf.hyp0
  refine (congrInst2 (TB w) (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans ?_
  refine (TB_at w _ _ _ _).eqTrans ((pr_peel w hM'.wk ha'.wk hu).eqTrans ?_)
  refine (mul_comm _ _).eqTrans (congrMul (.eqRefl _) (TB_at w _ _ _ _).eqSymm)

/-- `T_{r+1} = W T_r`. -/
theorem total_succ {r M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) :
    Γ ⊢[PRAAx] Tt w (succ r) M x ≐ Tt w r M x * ap2 (sumF w) M x := by
  refine (peel_sum (TB w) r M _).eqTrans (sum_scale _ _ _ _ _ _ (.allI (.impI ?_)))
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  simp only [shift_pairT]
  have ht : Syn.shift (Tt w r M x) = Tt w (Syn.shift r) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  have hp : Syn.shift (pw M r) = pw (Syn.shift M) (Syn.shift r) := by simp [Syn.shift]
  rw [ht, hp]
  have hs : Syn.shift (succ r) = succ (Syn.shift r) := by simp [Syn.shift]
  rw [hs]
  have hl : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift M) := Prf.hyp0
  exact (block_T w hM'.wk hl).eqTrans (mul_comm _ _)

end Totals

/-! ## Linear combinations of three sums -/

section Lin

variable (f₁ f₂ f₃ : PTm 2)

abbrev sbp (f : PTm 2) : PTm 2 := Syn.subst ![var 0, sndT (var 1)] f

/-- `K₁ f₁`, `K₂ f₂`, `K₃ f₃`, over `0 = v`, `1 = ⟨⟨K₁, ⟨K₂, K₃⟩⟩, p⟩`. -/
abbrev A1 : PTm 2 := fstT (fstT (var 1)) * sbp f₁
abbrev A2 : PTm 2 := fstT (sndT (fstT (var 1))) * sbp f₂
abbrev A3 : PTm 2 := sndT (sndT (fstT (var 1))) * sbp f₃

theorem inst2_sbp (f : PTm 2) (v z : PTm n) : Syn.subst ![v, z] (sbp f) = inst2 f v (sndT z) := by
  simp only [inst2, sbp, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

theorem A1_at (v K₁ K₂ K₃ p : PTm n) :
    Γ ⊢[PRAAx] inst2 (A1 f₁) v (pairT (pairT K₁ (pairT K₂ K₃)) p) ≐ K₁ * inst2 f₁ v p := by
  have e : inst2 (A1 f₁) v (pairT (pairT K₁ (pairT K₂ K₃)) p) =
      fstT (fstT (pairT (pairT K₁ (pairT K₂ K₃)) p)) * inst2 f₁ v (sndT (pairT (pairT K₁ (pairT K₂ K₃)) p)) := by
    simp only [inst2, A1, PTm.subst_mul, inst2_sbp, subst_fstT]; simp
  rw [e]
  exact congrMul ((congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)) (congrInst2 f₁ (.eqRefl _) (snd_pair _ _))

theorem A2_at (v K₁ K₂ K₃ p : PTm n) :
    Γ ⊢[PRAAx] inst2 (A2 f₂) v (pairT (pairT K₁ (pairT K₂ K₃)) p) ≐ K₂ * inst2 f₂ v p := by
  have e : inst2 (A2 f₂) v (pairT (pairT K₁ (pairT K₂ K₃)) p) =
      fstT (sndT (fstT (pairT (pairT K₁ (pairT K₂ K₃)) p))) * inst2 f₂ v (sndT (pairT (pairT K₁ (pairT K₂ K₃)) p)) := by
    simp only [inst2, A2, PTm.subst_mul, inst2_sbp, subst_fstT, subst_sndT]; simp
  rw [e]
  exact congrMul ((congrFst ((congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _))
    (congrInst2 f₂ (.eqRefl _) (snd_pair _ _))

theorem A3_at (v K₁ K₂ K₃ p : PTm n) :
    Γ ⊢[PRAAx] inst2 (A3 f₃) v (pairT (pairT K₁ (pairT K₂ K₃)) p) ≐ K₃ * inst2 f₃ v p := by
  have e : inst2 (A3 f₃) v (pairT (pairT K₁ (pairT K₂ K₃)) p) =
      sndT (sndT (fstT (pairT (pairT K₁ (pairT K₂ K₃)) p))) * inst2 f₃ v (sndT (pairT (pairT K₁ (pairT K₂ K₃)) p)) := by
    simp only [inst2, A3, PTm.subst_mul, inst2_sbp, subst_fstT, subst_sndT]; simp
  rw [e]
  exact congrMul ((congrSnd ((congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))
    (congrInst2 f₃ (.eqRefl _) (snd_pair _ _))

/-- `∑_{v<N} G(v) = K₁ ∑ f₁ + K₂ ∑ f₂ + K₃ ∑ f₃` when `G = K₁ f₁ + K₂ f₂ + K₃ f₃` pointwise. -/
theorem lin3 (G : PTm 2) {N y K₁ K₂ K₃ p : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ (inst2 G (var 0) (Syn.shift y) ≐
      Syn.shift K₁ * inst2 f₁ (var 0) (Syn.shift p) + (Syn.shift K₂ * inst2 f₂ (var 0) (Syn.shift p) +
        Syn.shift K₃ * inst2 f₃ (var 0) (Syn.shift p))))) :
    Γ ⊢[PRAAx] ap2 (sumF G) N y ≐ K₁ * ap2 (sumF f₁) N p + (K₂ * ap2 (sumF f₂) N p + K₃ * ap2 (sumF f₃) N p) := by
  have hz : Syn.shift (pairT (pairT K₁ (pairT K₂ K₃)) p) =
      pairT (pairT (Syn.shift K₁) (pairT (Syn.shift K₂) (Syn.shift K₃))) (Syn.shift p) := by simp [Syn.shift]
  have c : Γ ⊢[PRAAx] ap2 (sumF G) N y ≐
      ap2 (sumF (addBody (A1 f₁) (addBody (A2 f₂) (A3 f₃)))) N (pairT (pairT K₁ (pairT K₂ K₃)) p) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    refine (Prf.impE h.allOpen.wk Prf.hyp0).eqTrans ?_
    rw [inst2_addBody, inst2_addBody, hz]
    exact (congrAdd (A1_at f₁ _ _ _ _ _) (congrAdd (A2_at f₂ _ _ _ _ _) (A3_at f₃ _ _ _ _ _))).eqSymm
  have s1 : Γ ⊢[PRAAx] ap2 (sumF (A1 f₁)) N (pairT (pairT K₁ (pairT K₂ K₃)) p) ≐ K₁ * ap2 (sumF f₁) N p := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_)); rw [hz]; exact A1_at f₁ _ _ _ _ _
  have s2 : Γ ⊢[PRAAx] ap2 (sumF (A2 f₂)) N (pairT (pairT K₁ (pairT K₂ K₃)) p) ≐ K₂ * ap2 (sumF f₂) N p := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_)); rw [hz]; exact A2_at f₂ _ _ _ _ _
  have s3 : Γ ⊢[PRAAx] ap2 (sumF (A3 f₃)) N (pairT (pairT K₁ (pairT K₂ K₃)) p) ≐ K₃ * ap2 (sumF f₃) N p := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_)); rw [hz]; exact A3_at f₃ _ _ _ _ _
  exact c.eqTrans ((sum_add _ _ _ _).eqTrans (congrAdd s1 ((sum_add _ _ _ _).eqTrans (congrAdd s2 s3))))

end Lin

/-! ## First and second moments of the sample sum -/

section Moments

variable (w X : PTm 2)

/-- `P_r(t) S_r(t)` and `P_r(t) S_r(t)²`, over `0 = t`, `1 = ⟨r, ⟨M, x⟩⟩`. -/
abbrev AB : PTm 2 := TB w * SB X
abbrev BB : PTm 2 := TB w * (SB X * SB X)

abbrev At (r M x : PTm n) : PTm n := ap2 (sumF (AB w X)) (pw M r) (pairT r (pairT M x))
abbrev Bt (r M x : PTm n) : PTm n := ap2 (sumF (BB w X)) (pw M r) (pairT r (pairT M x))

theorem shift_mul'' (a b : PTm n) : Syn.shift (a * b) = Syn.shift a * Syn.shift b := by simp [Syn.shift]
theorem shift_zero' : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
theorem shift_two' : Syn.shift (two : PTm n) = two := by simp [Syn.shift]

theorem inst2_AB (t p : PTm n) : inst2 (AB w X) t p = inst2 (TB w) t p * inst2 (SB X) t p := by simp [inst2]
theorem inst2_BB (t p : PTm n) : inst2 (BB w X) t p = inst2 (TB w) t p * (inst2 (SB X) t p * inst2 (SB X) t p) := by
  simp [inst2]

/-- The value of a block body at `u`: with `y = ⟨a M^r, ⟨r+1, ⟨M, x⟩⟩⟩`, the peeled weight and sum. -/
theorem block_pt (G : PTm 2) {u a r M x : PTm n} :
    Γ ⊢[PRAAx] inst2 (offB G) u (pairT (a * pw M r) (pairT (succ r) (pairT M x))) ≐
      inst2 G (a * pw M r + u) (pairT (succ r) (pairT M x)) :=
  by rw [inst2_offB]; exact congrInst2 G (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

/-- One block of the first moment: `∑_u P_{r+1} S_{r+1} = (w_a X_a) T_r + w_a A_r + 0 · B_r`. -/
theorem block_A {a r M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (ha : Γ ⊢[PRAAx] lt a M) :
    Γ ⊢[PRAAx] inst2 (BlockSum.blkB (AB w X)) a (pairT (pw M r) (pairT (succ r) (pairT M x))) ≐
      (inst2 w a x * inst2 X a x) * Tt w r M x + (inst2 w a x * At w X r M x + zero * Bt w X r M x) := by
  refine (BlockSum.blk_at _ _ _ _).eqTrans (lin3 (TB w) (AB w X) (BB w X) (offB (AB w X)) (.allI (.impI ?_)))
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have ha' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift a) (Syn.shift M) := by
    have e := ha.shift; simp only [Fm.shift, subst_lt, subst_le, ConciseIPRA.PTm.subst_succ] at e; simpa [Syn.shift] using e
  simp only [shift_pairT, shift_mul'', shift_inst2', shift_zero']
  have hp : Syn.shift (pw M r) = pw (Syn.shift M) (Syn.shift r) := by simp [Syn.shift]
  have hs : Syn.shift (succ r) = succ (Syn.shift r) := by simp [Syn.shift]
  rw [hp, hs]
  let C : List (Fm PTm (n + 1)) := lt (var 0) (pw (Syn.shift M) (Syn.shift r)) :: Γ.map Fm.shift
  have hu : C ⊢[PRAAx] lt (var 0) (pw (Syn.shift M) (Syn.shift r)) := Prf.hyp0
  refine (block_pt (AB w X)).eqTrans ?_
  rw [inst2_AB, inst2_AB, inst2_BB]
  have p1 := (TB_at (Γ := C) w _ _ _ (Syn.shift x)).eqTrans (pr_peel w (x := Syn.shift x) hM'.wk ha'.wk hu)
  have s1 := (SB_at (Γ := C) X _ _ _ (Syn.shift x)).eqTrans (sr_peel X (x := Syn.shift x) hM'.wk ha'.wk hu)
  have t0 := TB_at (Γ := C) w (var 0) (Syn.shift r) (Syn.shift M) (Syn.shift x)
  have u0 := SB_at (Γ := C) X (var 0) (Syn.shift r) (Syn.shift M) (Syn.shift x)
  refine (congrMul p1 s1).eqTrans (.eqTrans ?_ (congrAdd (congrMul (.eqRefl _) t0)
    (congrAdd (congrMul (.eqRefl _) (congrMul t0 u0)) (congrMul (.eqRefl _) (congrMul t0 (congrMul u0 u0))))).eqSymm)
  apply deriveNat; ipra_simps; ring

/-- One block of the second moment: `∑_u P_{r+1} S_{r+1}² = (w_a X_a²) T_r + 2 w_a X_a A_r + w_a B_r`. -/
theorem block_B {a r M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (ha : Γ ⊢[PRAAx] lt a M) :
    Γ ⊢[PRAAx] inst2 (BlockSum.blkB (BB w X)) a (pairT (pw M r) (pairT (succ r) (pairT M x))) ≐
      (inst2 w a x * (inst2 X a x * inst2 X a x)) * Tt w r M x +
        (two * (inst2 w a x * inst2 X a x) * At w X r M x + inst2 w a x * Bt w X r M x) := by
  refine (BlockSum.blk_at _ _ _ _).eqTrans (lin3 (TB w) (AB w X) (BB w X) (offB (BB w X)) (.allI (.impI ?_)))
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have ha' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift a) (Syn.shift M) := by
    have e := ha.shift; simp only [Fm.shift, subst_lt, subst_le, ConciseIPRA.PTm.subst_succ] at e; simpa [Syn.shift] using e
  simp only [shift_pairT, shift_mul'', shift_inst2', shift_two']
  have hp : Syn.shift (pw M r) = pw (Syn.shift M) (Syn.shift r) := by simp [Syn.shift]
  have hs : Syn.shift (succ r) = succ (Syn.shift r) := by simp [Syn.shift]
  rw [hp, hs]
  let C : List (Fm PTm (n + 1)) := lt (var 0) (pw (Syn.shift M) (Syn.shift r)) :: Γ.map Fm.shift
  have hu : C ⊢[PRAAx] lt (var 0) (pw (Syn.shift M) (Syn.shift r)) := Prf.hyp0
  refine (block_pt (BB w X)).eqTrans ?_
  rw [inst2_BB, inst2_AB, inst2_BB]
  have p1 := (TB_at (Γ := C) w _ _ _ (Syn.shift x)).eqTrans (pr_peel w (x := Syn.shift x) hM'.wk ha'.wk hu)
  have s1 := (SB_at (Γ := C) X _ _ _ (Syn.shift x)).eqTrans (sr_peel X (x := Syn.shift x) hM'.wk ha'.wk hu)
  have t0 := TB_at (Γ := C) w (var 0) (Syn.shift r) (Syn.shift M) (Syn.shift x)
  have u0 := SB_at (Γ := C) X (var 0) (Syn.shift r) (Syn.shift M) (Syn.shift x)
  refine (congrMul p1 (congrMul s1 s1)).eqTrans (.eqTrans ?_ (congrAdd (congrMul (.eqRefl _) t0)
    (congrAdd (congrMul (.eqRefl _) (congrMul t0 u0)) (congrMul (.eqRefl _) (congrMul t0 (congrMul u0 u0))))).eqSymm)
  apply deriveNat; ipra_simps; ring

theorem shift_Tt (r M x : PTm n) : Syn.shift (Tt w r M x) = Tt w (Syn.shift r) (Syn.shift M) (Syn.shift x) := by
  simp [Syn.shift]
theorem shift_At (r M x : PTm n) : Syn.shift (At w X r M x) = At w X (Syn.shift r) (Syn.shift M) (Syn.shift x) := by
  simp [Syn.shift]
theorem shift_Bt (r M x : PTm n) : Syn.shift (Bt w X r M x) = Bt w X (Syn.shift r) (Syn.shift M) (Syn.shift x) := by
  simp [Syn.shift]

/-- `A_{r+1} = T_r S + A_r W` (with a vanishing third term). -/
theorem A_succ {r M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) :
    Γ ⊢[PRAAx] At w X (succ r) M x ≐ Tt w r M x * ap2 (sumF (w * X)) M x +
      (At w X r M x * ap2 (sumF w) M x + zero * ap2 (sumF w) M x) := by
  refine (peel_sum (AB w X) r M _).eqTrans (lin3 (w * X) w w _ (.allI (.impI ?_)))
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  simp only [shift_pairT, shift_Tt, shift_At, shift_zero']
  have hp : Syn.shift (pw M r) = pw (Syn.shift M) (Syn.shift r) := by simp [Syn.shift]
  have hs : Syn.shift (succ r) = succ (Syn.shift r) := by simp [Syn.shift]
  rw [hp, hs, Expectation.inst2_mul']
  refine (block_A w X hM'.wk Prf.hyp0).eqTrans ?_
  apply deriveNat; ipra_simps; ring

/-- `B_{r+1} = T_r Q + 2 A_r S + B_r W`. -/
theorem B_succ {r M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) :
    Γ ⊢[PRAAx] Bt w X (succ r) M x ≐ Tt w r M x * ap2 (sumF (w * (X * X))) M x +
      (two * At w X r M x * ap2 (sumF (w * X)) M x + Bt w X r M x * ap2 (sumF w) M x) := by
  refine (peel_sum (BB w X) r M _).eqTrans (lin3 (w * (X * X)) (w * X) w _ (.allI (.impI ?_)))
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  simp only [shift_pairT, shift_Tt, shift_At, shift_Bt, shift_mul'', shift_two']
  have hp : Syn.shift (pw M r) = pw (Syn.shift M) (Syn.shift r) := by simp [Syn.shift]
  have hs : Syn.shift (succ r) = succ (Syn.shift r) := by simp [Syn.shift]
  rw [hp, hs, Expectation.inst2_mul', Expectation.inst2_mul', Expectation.inst2_mul']
  refine (block_B w X hM'.wk Prf.hyp0).eqTrans ?_
  apply deriveNat; ipra_simps; ring

end Moments

/-! ## The sample mean and the sample variance -/

section Sample

variable (w X : PTm 2)

theorem tb_zero (M x : PTm n) : Γ ⊢[PRAAx] inst2 (TB w) zero (pairT zero (pairT M x)) ≐ one :=
  (TB_at w _ _ _ _).eqTrans (prod_zero _ _)

theorem one_bound (G : PTm 2) (M p : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF G) (pw M zero) p ≐ inst2 G zero p :=
  (congrAp2 (sumF G) (pw_zero M) (.eqRefl _)).eqTrans ((sum_succ' _ _ _).eqTrans
    ((congrAdd (sum_zero _ _) (.eqRefl _)).eqTrans (zero_add _)))

theorem tt_zero (M x : PTm n) : Γ ⊢[PRAAx] Tt w zero M x ≐ one := (one_bound _ _ _).eqTrans (tb_zero w _ _)

theorem at_zero (M x : PTm n) : Γ ⊢[PRAAx] At w X zero M x ≐ zero := by
  refine (one_bound _ _ _).eqTrans ?_
  rw [inst2_AB]
  exact (congrMul (.eqRefl _) ((SB_at X _ _ _ _).eqTrans (sum_zero _ _))).eqTrans (mul_zero _)

theorem bt_zero (M x : PTm n) : Γ ⊢[PRAAx] Bt w X zero M x ≐ zero := by
  refine (one_bound _ _ _).eqTrans ?_
  rw [inst2_BB]
  exact (congrMul (.eqRefl _) ((congrMul ((SB_at X _ _ _ _).eqTrans (sum_zero _ _)) (.eqRefl _)).eqTrans (zero_mul _))).eqTrans
    (mul_zero _)

/-- The invariants, over `0 = r` with `M`, `x` shifted. -/
abbrev invF (M x : PTm n) : Fm PTm (n + 1) :=
  (ap2 (sumF w) (Syn.shift M) (Syn.shift x) * At w X (var 0) (Syn.shift M) (Syn.shift x) ≐
      var 0 * ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x) * Tt w (var 0) (Syn.shift M) (Syn.shift x)) ⋏
    (ap2 (sumF w) (Syn.shift M) (Syn.shift x) * ap2 (sumF w) (Syn.shift M) (Syn.shift x) *
        (Tt w (var 0) (Syn.shift M) (Syn.shift x) * Bt w X (var 0) (Syn.shift M) (Syn.shift x)) +
      var 0 * (ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x) * ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x)) *
        (Tt w (var 0) (Syn.shift M) (Syn.shift x) * Tt w (var 0) (Syn.shift M) (Syn.shift x)) ≐
    ap2 (sumF w) (Syn.shift M) (Syn.shift x) * ap2 (sumF w) (Syn.shift M) (Syn.shift x) *
        (At w X (var 0) (Syn.shift M) (Syn.shift x) * At w X (var 0) (Syn.shift M) (Syn.shift x)) +
      var 0 * ap2 (sumF w) (Syn.shift M) (Syn.shift x) * ap2 (sumF (w * (X * X))) (Syn.shift M) (Syn.shift x) *
        (Tt w (var 0) (Syn.shift M) (Syn.shift x) * Tt w (var 0) (Syn.shift M) (Syn.shift x)))

/-- `thm:sample-var` (with the sample mean): for the `r`-fold product law, with `W = ∑ w`, `S = ∑ w X`,
`Q = ∑ w X²`, `T = ∑_t P_r`, `A = ∑_t P_r S_r`, `B = ∑_t P_r S_r²`:
`W A = r S T` (i.e. `E[S_r] = r μ`) and `W² T B + r S² T² = W² A² + r W Q T²`
(i.e. `T B − A² = r T² (W Q − S²)/W²`: `Var(S_r) = r σ²`, `Var(X̄_r) = σ²/r`). -/
theorem sample_moments {M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (r : PTm n) :
    Γ ⊢[PRAAx] (ap2 (sumF w) M x * At w X r M x ≐ r * ap2 (sumF (w * X)) M x * Tt w r M x) ⋏
      (ap2 (sumF w) M x * ap2 (sumF w) M x * (Tt w r M x * Bt w X r M x) +
          r * (ap2 (sumF (w * X)) M x * ap2 (sumF (w * X)) M x) * (Tt w r M x * Tt w r M x) ≐
        ap2 (sumF w) M x * ap2 (sumF w) M x * (At w X r M x * At w X r M x) +
          r * ap2 (sumF w) M x * ap2 (sumF (w * (X * X))) M x * (Tt w r M x * Tt w r M x)) := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have hall : Γ ⊢[PRAAx] Fm.all (invF w X M x) := by
    refine PRA.qfInd _ ⟨trivial, trivial⟩ ?_ ?_
    · simp only [invF, Tt, At, Bt, Fm.subst_and, Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_pairT,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      have a := natEq (at_zero (Γ := Γ) w X M x); have b := natEq (bt_zero (Γ := Γ) w X M x)
      refine .andI ?_ ?_ <;> (apply deriveNat; ipra_simps)
      · linear_combination 𝔞 (ap2 (sumF w) M x) * a
      · linear_combination (𝔞 (ap2 (sumF w) M x) * 𝔞 (ap2 (sumF w) M x) * 𝔞 (Tt w zero M x)) * b -
          (𝔞 (ap2 (sumF w) M x) * 𝔞 (ap2 (sumF w) M x)) * (𝔞 (At w X zero M x) + 0) * a
    · simp only [invF, Tt, At, Bt, Fm.subst_and, Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_pairT,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      let D : List (Fm PTm (n + 1)) := invF w X M x :: Γ.map Fm.shift
      have i2 := natEq (Prf.andE₁ (Prf.hyp0 : D ⊢[PRAAx] invF w X M x))
      have i3 := natEq (Prf.andE₂ (Prf.hyp0 : D ⊢[PRAAx] invF w X M x))
      have tS := total_succ (Γ := D) w (r := var 0) (x := Syn.shift x) hM'.wk
      have aS := A_succ (Γ := D) w X (r := var 0) (x := Syn.shift x) hM'.wk
      have bS := B_succ (Γ := D) w X (r := var 0) (x := Syn.shift x) hM'.wk
      refine .andI ?_ ?_
      · refine (congrMul (.eqRefl _) aS).eqTrans (.eqTrans ?_ (congrMul (.eqRefl _) tS).eqSymm)
        apply deriveNat; ipra_simps
        linear_combination 𝔞 (ap2 (sumF w) (Syn.shift M) (Syn.shift x)) * i2
      · refine (congrAdd (congrMul (.eqRefl _) (congrMul tS bS)) (congrMul (.eqRefl _) (congrMul tS tS))).eqTrans
          (.eqTrans ?_ (congrAdd (congrMul (.eqRefl _) (congrMul aS aS)) (congrMul (.eqRefl _) (congrMul tS tS))).eqSymm)
        apply deriveNat; ipra_simps
        linear_combination 𝔞 (ap2 (sumF w) (Syn.shift M) (Syn.shift x)) * 𝔞 (ap2 (sumF w) (Syn.shift M) (Syn.shift x)) * i3
  have h := Prf.allE r hall
  simp only [invF, Tt, At, Bt, Fm.subst_and, Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_pairT,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h
  exact h

/-- The product law is normalized: `T_r = W^r`. -/
theorem total_pow {M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (r : PTm n) :
    Γ ⊢[PRAAx] Tt w r M x ≐ pw (ap2 (sumF w) M x) r := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have hall : Γ ⊢[PRAAx] Fm.all (Tt w (var 0) (Syn.shift M) (Syn.shift x) ≐
      pw (ap2 (sumF w) (Syn.shift M) (Syn.shift x)) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Tt, Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero]
      exact (tt_zero w M x).eqTrans (pw_zero _).eqSymm
    · simp only [Tt, Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact (total_succ w (r := var 0) (x := Syn.shift x) hM'.wk).eqTrans
        ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (pw_succ _ _).eqSymm)
  have h := Prf.allE r hall
  simp only [Tt, Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero] at h
  exact h

/-- `thm:residual`: for `W ≥ 1`, `E[∑_j (X_j − X̄)²] = (r − 1) σ²`, cleared: with `A₂ = ∑_t P_r ∑_j X_j²`
(the first moment of the observable `X²`),
`W² r A₂ + r² T S² + r T W Q = W² B + r² T W Q + r T S²`, i.e.
`W² (r A₂ − B) = r (r − 1) T (W Q − S²)`. -/
theorem residual {M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hW : Γ ⊢[PRAAx] ap2 (sumF w) M x ≐ succ (pred (ap2 (sumF w) M x))) (r : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF w) M x * ap2 (sumF w) M x * r * At w (X * X) r M x +
        r * r * Tt w r M x * (ap2 (sumF (w * X)) M x * ap2 (sumF (w * X)) M x) +
        r * Tt w r M x * ap2 (sumF w) M x * ap2 (sumF (w * (X * X))) M x ≐
      ap2 (sumF w) M x * ap2 (sumF w) M x * Bt w X r M x +
        r * r * Tt w r M x * ap2 (sumF w) M x * ap2 (sumF (w * (X * X))) M x +
        r * Tt w r M x * (ap2 (sumF (w * X)) M x * ap2 (sumF (w * X)) M x) := by
  have m := sample_moments (Γ := Γ) w X (x := x) hM r
  have m2 := Prf.andE₁ (sample_moments (Γ := Γ) w (X * X) (x := x) hM r)
  have i2 := natEq (Prf.andE₁ m); have i3 := natEq (Prf.andE₂ m); have j2 := natEq m2
  have tpos : Γ ⊢[PRAAx] Tt w r M x ≐ succ (pred (Tt w r M x)) :=
    (total_pow w (x := x) hM r).eqTrans ((pw_pos' hW r).eqTrans (congrSucc (congrPred (total_pow w (x := x) hM r).eqSymm)))
  refine Combinatorics.BinomialIdentities.mul_cancel tpos ?_
  apply deriveNat; ipra_simps
  linear_combination 𝔞 r * 𝔞 (Tt w r M x) * 𝔞 (ap2 (sumF w) M x) * j2 - i3 -
    (𝔞 (ap2 (sumF w) M x) * 𝔞 (At w X r M x) + 𝔞 r * 𝔞 (ap2 (sumF (w * X)) M x) * 𝔞 (Tt w r M x)) * i2

end Sample

end LeanProofs.IPRA.Probability.ProductPower
