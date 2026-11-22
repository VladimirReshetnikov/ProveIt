import IPRADerivations.Probability.ProductMarginal
import IPRADerivations.Probability.KolmogorovVariance

/-!
# Kolmogorov's inequality for the first coordinates of a longer iid sample

Packet: `probability/expected_value_ipra_2026-11-16`, Theorem `thm:dyadic-slln` ("Dyadic eventual-uniform
bound"), the block step of its proof: "If for some `n ∈ [2^r, 2^{r+1})` we have `|S_n| ≥ 2ε n`, then certainly
`max_{k ≤ 2^{r+1}} |S_k| ≥ 2ε 2^r`. Kolmogorov's inequality gives `P(bad block r) ≤ 2^{r+1} σ²/(2ε 2^r)²`",
where the probability is taken in the law of the whole sample of length `H`. The crossings within the first
`N` coordinates are an observable of the low block, so the marginal law reduces the statement to
`Probability/KolmogorovVariance` at length `N`.

* `I_low_gen`: for a crossing index `c ≤ N`, `I_c(i M^N + j) = I_c(j)`;
* `hB`, `hB_at`: the block observable `a² ∑_{c≤N} I_c(j)` (the threshold `a(M, x)` squared times the
  indicator of a crossing among the first `N` partial sums, by `FirstCrossing.cover`);
* `block_dsum`: `∑_{j<M^N} P_N(j) hB(j)` is the left side of `kolmogorov_variance` (Fubini);
* `block_kolmogorov`: in the `(N + m)`-fold law,
  `∑_t P_{N+m}(t) hB(t mod M^N) + T_m (N S² T_N) ≤ T_m (N W Q T_N)`, i.e.
  `a² P_{N+m}(max_{c≤N} W² (S_c − c μ)² ≥ a²) ≤ N W² σ²`;
* `hB_low`: `hB(t mod M^N) = a² ∑_{c≤N} I_c(t)`, so the observable is the crossing indicator of the sample
  itself.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.KolmogorovBlock

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul' inst2_add')
open LeanProofs.IPRA.Probability.Independence (dsum sum_scale shift_sum)
open LeanProofs.IPRA.Probability.ProductPower (Pr Sr TB TB_at Tt dg wdB xdB div_eq' rem_lt'')
open LeanProofs.IPRA.Probability.FirstCrossing (Ib nbB inst2_Ib inst2_nbB)
open LeanProofs.IPRA.Probability.KolmogorovIid (IB DB Yp rp)
open LeanProofs.IPRA.Probability.KolmogorovIidGlue (Cv Cv_at c_any D_low I3 inst3_I3 A1 shift_code)
open LeanProofs.IPRA.Probability.KolmogorovAssembly (lift inst3_lift col_scale)
open LeanProofs.IPRA.Probability.KolmogorovVariance (kolmogorov_variance)
open LeanProofs.IPRA.Probability.ProductMarginal (ρn hr marginal)
open LeanProofs.IPRA.Foundations.MixedRadix (shift_le')
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

section Block

variable (w X a : PTm 2)

/-- For a crossing index `c ≤ N`, `I_c(i M^N + j) = I_c(j)`. -/
theorem I_low_gen {M i j N c x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hc : Γ ⊢[PRAAx] le c N) :
    Γ ⊢[PRAAx] inst2 (IB w X (Cv a)) c (pairT (i * pw M N + j) (pairT M x)) ≐
      inst2 (IB w X (Cv a)) c (pairT j (pairT M x)) := by
  rw [inst2_Ib, inst2_Ib]
  refine congrMul (congrMonus (.eqRefl _) (congrMonus (c_any a c _ _ M x) (D_low w X hM hc))) ?_
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
    simpa [Fm.shift, Syn.shift] using hM.shift
  refine prod_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT, shift_code]
  rw [inst2_nbB, inst2_nbB]
  have hl : (lt (var 0) (Syn.shift c) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
    le_trans (le_trans (le_succ_self _) Prf.hyp0) (shift_le' hc).wk
  exact congrMonus (.eqRefl _) (congrMonus (.eqRefl _)
    (congrMonus (c_any a _ _ _ _ _) (D_low w X hM'.wk hl)))

/-- The block observable `a² ∑_{c≤N} I_c(j)` over `(j, ⟨N, ⟨M, x⟩⟩)`. -/
def hB : PTm 2 := Cv (a * a) * Syn.subst ![var 0, pairT (succ (fstT (var 1))) (var 1)] (pB (I3 w X a))

theorem inst2_hB (j z : PTm n) :
    inst2 (hB w X a) j z = inst2 (Cv (a * a)) j z * inst2 (pB (I3 w X a)) j (pairT (succ (fstT z)) z) := by
  simp only [hB, inst2_mul']
  congr 1
  simp only [inst2, Syn.subst_subst]
  congr 1; funext i; fin_cases i <;> simp

theorem hB_at (j N M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (hB w X a) j (pairT N (pairT M x)) ≐
      inst2 (Cv (a * a)) j (pairT N (pairT M x)) * inst2 (pB (I3 w X a)) j (pairT (succ N) (pairT N (pairT M x))) := by
  rw [inst2_hB]
  exact congrMul (.eqRefl _) (congrInst2 _ (.eqRefl _) (congrPairT (congrSucc (fst_pair _ _)) (.eqRefl _)))

/-- `∑_{j<M^N} P_N(j) hB(j)` is the left side of `kolmogorov_variance`. -/
theorem block_dsum (N M x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (TB w * hB w X a)) (pw M N) (pairT N (pairT M x)) ≐
      dsum (A1 w X a) (succ N) (pw M N) (pairT N (pairT M x)) := by
  refine .eqTrans ?_ (fubini (A1 w X a) (succ N) (pw M N) (pairT N (pairT M x))).eqSymm
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  have e : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  rw [e, inst2_mul']
  have h₁ := natEq (hB_at (Γ := lt (var 0) (Syn.shift (pw M N)) :: Γ.map Fm.shift) w X a (var 0)
    (Syn.shift N) (Syn.shift M) (Syn.shift x))
  have h₂ := natEq (col_scale (Γ := lt (var 0) (Syn.shift (pw M N)) :: Γ.map Fm.shift) (I3 w X a)
    (TB w * Cv (a * a)) (var 0) (succ (Syn.shift N)) (pairT (Syn.shift N) (pairT (Syn.shift M) (Syn.shift x))))
  rw [inst2_mul'] at h₂
  apply deriveNat; ipra_simps
  rw [h₁, h₂]; ring

/-- In the `(N + m)`-fold law: `∑_t P_{N+m}(t) hB(t mod M^N) + T_m (N S² T_N) ≤ T_m (N W Q T_N)`. -/
theorem block_kolmogorov {M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hW : Γ ⊢[PRAAx] ap2 (sumF w) M x ≐ succ (pred (ap2 (sumF w) M x))) (N m : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF (rp (TB w) ρn * hr (hB w X a))) (pw M (N + m)) (Yp N m M x) +
        Tt w m M x * (N * (ap2 (sumF (w * X)) M x * ap2 (sumF (w * X)) M x) * Tt w N M x))
      (Tt w m M x * (N * (ap2 (sumF w) M x * ap2 (sumF (w * (X * X))) M x) * Tt w N M x)) := by
  have mg := natEq (marginal (Γ := Γ) w (hB w X a) hM N m x)
  have bd := natEq (block_dsum (Γ := Γ) w X a N M x)
  have kv := kolmogorov_variance w X a hM hW N (x := x) (Γ := Γ)
  ipra_le 𝔟 (Tt w m M x) * sl kv using rw [mg, bd]; ring

/-- `hB(t mod M^N) = a² ∑_{c≤N} I_c(t)`: the block observable is the crossing indicator of the sample. -/
theorem hB_low {M t N x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) :
    Γ ⊢[PRAAx] inst2 (hB w X a) (rem t (pw M N)) (pairT N (pairT M x)) ≐
      inst2 (Cv (a * a)) t (pairT N (pairT M x)) * ap2 (sumF (IB w X (Cv a))) (succ N) (pairT t (pairT M x)) := by
  refine (hB_at w X a _ N M x).eqTrans (congrMul ?_ ?_)
  · exact (Cv_at (a * a) _ N M x).eqTrans (Cv_at (a * a) t N M x).eqSymm
  · rw [LeanProofs.IPRA.inst2_pB]
    refine (congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
      simpa [Fm.shift, Syn.shift] using hM.shift
    simp only [shift_pairT]
    rw [inst2_colB, inst3_I3]
    have hc : (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) := by
      have h₀ : (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (succ (Syn.shift N)) := by
        have e : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
        rw [← e]; exact Prf.hyp0
      ipra_le sl h₀
    have hP : (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx]
        pw (Syn.shift M) (Syn.shift N) ≐ succ (pred (pw (Syn.shift M) (Syn.shift N))) := pw_pos' hM'.wk _
    have dv := div_eq' (t := Syn.shift t) hP
    have er : Syn.shift (rem t (pw M N)) = rem (Syn.shift t) (pw (Syn.shift M) (Syn.shift N)) := by simp [Syn.shift]
    rw [er]
    refine (congrInst2 _ (.eqRefl _) (congrPairT (fst_pair _ _) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))).eqTrans ?_
    refine .eqTrans ?_ (congrInst2 _ (.eqRefl _) (congrPairT dv.eqSymm (.eqRefl _)))
    exact (I_low_gen w X a (i := quo (Syn.shift t) (pw (Syn.shift M) (Syn.shift N))) hM'.wk hc).eqSymm

end Block

end LeanProofs.IPRA.Probability.KolmogorovBlock
