import IPRADerivations.AnalyticNumberTheory.WeightedSplit
import IPRADerivations.AnalyticNumberTheory.AbsDiff
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# The first weighted bound (`pnt_ipra_constructive_2026-11-14`, `sb:first-weighted-bound`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma `sb:weighted-sum`:
"The last line has absolute value at most `4096x(log x + Σ Λ(n)/n)` … The arithmetic function
`a(n) = Λ(n) log n + (Λ * Λ)(n)` is nonnegative. Taking absolute values gives
`|R(x)|(log x)² ≤ Σ_{n≤x} a(n)|R(x/n)| + 32768 x log x` (`sb:first-weighted-bound`)."

Here `R(m) = ψ(m) − Fm` at integers, `|·|` is the natural distance of `AbsDiff`, and the weighted identity of
`WeightedSplit` is applied to `f = ψ` (`psiB`) and `f = F · id` (`qB`) and subtracted (`combine`):

  `|ψ(x) − Fx| u_x² ≤ Σ_{n≤x} (Λ * Λ)(n)|R(⌊x/n⌋)| + Σ_{n≤x} Λ(n) u_n |R(⌊x/n⌋)| + 8192 F² x u_x + 40 F³ x`

(`first_weighted`). The error terms: `|E_ψ(m) − E_{F·id}(m)| ≤ 4096 F² m` at every `m ≤ x` (`e_absd`, from
`FactorialError`), its Λ-weighted sum `≤ 4096 F² L_w(x!) ≤ 4096 F² x u_x` (`lq_le`), and the logarithm-splitting
remainders `≤ 8F² ψ(x)` and `≤ 2F² ψ(x)` (`errP_le`, `errQ_le`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LeanProofs.IPRA.AnalyticNumberTheory.WeightedBound

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono wt psi_le)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi LamB inst2_LamB pos_of_lt_zero lt_zero_of_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (Lam Lw)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (FLB FL_at lam_zero factorial_lambda)
open LeanProofs.IPRA.AnalyticNumberTheory.SummatoryCompose (Mono hRB inst2_hRB)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedReorder (S1B inst2_S1)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedSplit (lamW uw luB fuB EfB dqB errB sz uw_at dq_at hRB_at
  inst2_mul inst2_add inst2_EfB fid_lo fid_hi shiftK)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialError (Lq ferr_upper ferr_lower lfact_upper S_le)
open LeanProofs.IPRA.AnalyticNumberTheory.ErrorEquation (T2)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevAbel (pw_exp_le psi_k dlt_k)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryPointwise (quo_mul_le le_Q4 Q4_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryInstances (bs_shift)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryBound (quo_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd absd_le le_absd_l le_absd_r absd_scale adB inst2_adB absd_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.FourthRootSum (Q4)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (RB inst2_RB Bs)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (cvF)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHyperbola (quo_le_self)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (sg_le_one)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHarmonic (shift_fact')
open LeanProofs.IPRA.AnalyticNumberTheory.ComparisonEnvelope (le_mul2)
open LeanProofs.IPRA.Probability.Lotus (cmB sum_const_mul)
open LeanProofs.IPRA.Probability.Independence (cm_pt sum_scale)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The two monotone functions -/

/-- `ψ(m)`. -/
abbrev psiB : PTm 2 := ap2 (sumF (LamB wt)) (succ (var 0)) (var 1)
/-- `F m`, `F = snd y`. -/
abbrev qB : PTm 2 := sndT (var 1) * var 0

theorem inst2_psiB (k y : PTm n) : inst2 psiB k y = Psi wt k y := by simp [inst2]
theorem inst2_qB (k y : PTm n) : inst2 qB k y = sndT y * k := by simp [inst2]

theorem lamB0 {m : ℕ} {Δ : List (Fm PTm m)} (y : PTm m) : Δ ⊢[PRAAx] inst2 (LamB wt) zero y ≐ zero := by
  rw [inst2_LamB]; exact lam_zero wt _

theorem psi_mono : Mono psiB := by
  unfold Mono; intro m Δ k y
  rw [inst2_psiB, inst2_psiB]
  have s := natEq (sum_succ' (Γ := Δ) (LamB wt) (succ k) y)
  ipra_le 𝔞 (inst2 (LamB wt) (succ k) y) with s

theorem psi_zero {m : ℕ} {Δ : List (Fm PTm m)} (y : PTm m) : Δ ⊢[PRAAx] inst2 psiB zero y ≐ zero := by
  rw [inst2_psiB]
  exact (sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) (lamB0 y)).eqTrans (add_zero _))

theorem q_mono : Mono qB := by
  unfold Mono; intro m Δ k y
  rw [inst2_qB, inst2_qB]
  exact le_scale _ (le_succ_self k)

theorem q_zero {m : ℕ} {Δ : List (Fm PTm m)} (y : PTm m) : Δ ⊢[PRAAx] inst2 qB zero y ≐ zero := by
  rw [inst2_qB]; exact mul_zero _

/-! ## The inner sums in closed form -/

/-- `ψ(q) = Σ_{k<q} Λ(k + 1)`. -/
theorem psi_bs (q y : PTm n) : Γ ⊢[PRAAx] inst2 psiB q y ≐ Bs lamW q y := by
  rw [inst2_psiB]
  exact (bs_shift (LamB wt) q y).eqTrans ((congrAdd (lamB0 y) (.eqRefl _)).eqTrans (zero_add _))

/-- `Σ_{d≤m} Λ(d) ψ(⌊m/d⌋) = T₂(m)`. -/
theorem s1P (m K L : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (hRB psiB lamW)) (succ m) (pairT m (pairT K (fact L))) ≐ T2 m K L := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_hRB, inst2_RB]
  exact congrMul (.eqRefl _) (psi_bs _ _)

theorem inst2_lamW (d y : PTm n) : inst2 lamW d y = Lam wt d y := by simp [inst2]

/-- `[d ≥ 1] Λ(d) = Λ(d)`. -/
theorem sg_lam (d y : PTm n) : Γ ⊢[PRAAx] sg d * Lam wt d y ≐ Lam wt d y := by
  refine .orE (zero_or_succ d) ?_ ?_
  · have l0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] Lam wt d y ≐ zero := by
      have h := (congrInst2 (Γ := ((d ≐ zero) :: Γ)) (LamB wt) Prf.hyp0 (.eqRefl y)).eqTrans (lamB0 y)
      rw [inst2_LamB] at h; exact h
    exact (zero_mul_l ((congrSg Prf.hyp0).eqTrans sg_zero) _).eqTrans l0.eqSymm
  · exact (congrMul ((congrSg Prf.hyp0).eqTrans (sg_succ _)) (.eqRefl _)).eqTrans (one_mul _)

/-- `Σ_{d≤m} Λ(d) F⌊m/d⌋ = F Σ_{d≤m} Λ(d)⌊m/d⌋`. -/
theorem s1Q (m K L : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (hRB qB lamW)) (succ m) (pairT m (pairT K (fact L))) ≐ fact L * Lq m K L := by
  refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT, shift_fact']
  refine (hRB_at qB lamW _ _ _).eqTrans ?_
  rw [inst2_qB, inst2_lamW]
  ipra_lc (𝔞 (sndT (pairT (Syn.shift K) (fact (Syn.shift L)))) * 𝔞 (quo (Syn.shift m) (var 0))) * natEq (sg_lam (Γ := (lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift)) (var 0) (pairT (Syn.shift K) (fact (Syn.shift L)))) +
    𝔞 (Lam wt (var 0) (pairT (Syn.shift K) (fact (Syn.shift L)))) * 𝔞 (quo (Syn.shift m) (var 0)) * natEq (snd_pair (Γ := (lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift)) (Syn.shift K) (fact (Syn.shift L))) -
    𝔞 (fact (Syn.shift L)) * natEq (FL_at (Γ := (lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift)) wt (var 0) (Syn.shift m) (pairT (Syn.shift K) (fact (Syn.shift L))))

/-! ## The error equation at every inner point -/

section Inner
variable {m x K L : PTm n} (hm : Γ ⊢[PRAAx] le one m) (hmx : Γ ⊢[PRAAx] le m x) (hK : Γ ⊢[PRAAx] le one K)
  (hx4 : Γ ⊢[PRAAx] le (Q4 x) K) (hL : Γ ⊢[PRAAx] le (K * Q4 x) L)
  (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
include hm hmx hK hx4 hL hP

theorem ePe : Γ ⊢[PRAAx] inst2 psiB m (pairT K (fact L)) * U m K (fact L) +
      ap2 (sumF (hRB psiB lamW)) (succ m) (pairT m (pairT K (fact L))) ≐
    Psi wt m (pairT K (fact L)) * U m K (fact L) + T2 m K L := by
  rw [inst2_psiB]; exact congrAdd (.eqRefl _) (s1P m K L)

theorem eQe : Γ ⊢[PRAAx] inst2 qB m (pairT K (fact L)) * U m K (fact L) +
      ap2 (sumF (hRB qB lamW)) (succ m) (pairT m (pairT K (fact L))) ≐
    fact L * (m * U m K (fact L)) + fact L * Lq m K L := by
  rw [inst2_qB]
  ipra_lc 𝔞 m * 𝔞 (U m K (fact L)) * natEq (snd_pair (Γ := Γ) K (fact L)) + natEq (s1Q (Γ := Γ) m K L)

/-- `|E_ψ(m) − E_{F·id}(m)| ≤ 4096 F² m` for `1 ≤ m ≤ x`. -/
theorem e_absd :
    Γ ⊢[PRAAx] le (absd (inst2 psiB m (pairT K (fact L)) * U m K (fact L) +
        ap2 (sumF (hRB psiB lamW)) (succ m) (pairT m (pairT K (fact L))))
      (inst2 qB m (pairT K (fact L)) * U m K (fact L) +
        ap2 (sumF (hRB qB lamW)) (succ m) (pairT m (pairT K (fact L)))))
      (num 4096 * (fact L * fact L * m)) := by
  have hm4 : Γ ⊢[PRAAx] le (Q4 m) (Q4 x) := Q4_mono hmx
  have h4 := le_trans hm4 hx4
  have hL4 := le_trans (le_scale K hm4) hL
  have hP4 := le_trans (le_scale K (pw_exp_le (le_scale two (le_scale two hmx)))) hP
  have u := ferr_upper hm hK h4 hL4 hP4
  have l := ferr_lower hm hK h4 hL4 hP4
  have a := natEq (ePe hm hmx hK hx4 hL hP); have b := natEq (eQe hm hmx hK hx4 hL hP)
  exact absd_le (by ipra_le sl u with a - b) (by ipra_le sl l with b - a)

end Inner

/-! ## Combining `f = ψ` and `f = F · id` -/

theorem combine {AP AQ BP BQ CP CQ DP DQ EP EQ ErP ErQ : PTm n}
    (loP : Γ ⊢[PRAAx] le (AP + BP + CP) (EP + DP)) (hiP : Γ ⊢[PRAAx] le (EP + DP) (AP + BP + CP + ErP))
    (loQ : Γ ⊢[PRAAx] le (AQ + BQ + CQ) (EQ + DQ)) (hiQ : Γ ⊢[PRAAx] le (EQ + DQ) (AQ + BQ + CQ + ErQ)) :
    Γ ⊢[PRAAx] le (absd AP AQ) (absd EP EQ + absd DP DQ + absd BP BQ + absd CP CQ + ErP + ErQ) := by
  have a1 := le_absd_l (Γ := Γ) EP EQ; have a2 := le_absd_l (Γ := Γ) DP DQ
  have a3 := le_absd_r (Γ := Γ) BP BQ; have a4 := le_absd_r (Γ := Γ) CP CQ
  have b1 := le_absd_r (Γ := Γ) EP EQ; have b2 := le_absd_r (Γ := Γ) DP DQ
  have b3 := le_absd_l (Γ := Γ) BP BQ; have b4 := le_absd_l (Γ := Γ) CP CQ
  exact absd_le (by ipra_le sl loP + sl a1 + sl a2 + sl hiQ + sl a3 + sl a4 + 𝔞 ErP)
    (by ipra_le sl loQ + sl b1 + sl b2 + sl hiP + sl b3 + sl b4 + 𝔞 ErQ)

/-- `|Σ c(d) f(⌊x/d⌋) − Σ c(d) g(⌊x/d⌋)| ≤ Σ c(d) |f − g|(⌊x/d⌋)`. -/
theorem absd_hRB (f g a : PTm 2) (N z : PTm n) :
    Γ ⊢[PRAAx] le (absd (ap2 (sumF (hRB f a)) N z) (ap2 (sumF (hRB g a)) N z)) (ap2 (sumF (hRB (adB f g) a)) N z) := by
  refine le_trans (absd_sum _ _ _ _) (sum_le_params _ _ _ _ _ (.allI (.impI ?_)))
  rw [inst2_adB, inst2_hRB, inst2_hRB, inst2_hRB, inst2_adB]
  exact absd_scale _ _ _

/-- The context of one summand with `d ≥ 1`. -/
abbrev Cd (x : PTm n) (Γ : List (Fm PTm n)) : List (Fm PTm (n + 1)) :=
  ((var 0) ≐ succ (pred (var 0))) :: lt (var 0) (succ (Syn.shift x)) :: Γ.map Fm.shift

theorem absd_congr {m : ℕ} {a a' b b' : PTm m} {Δ : List (Fm PTm m)} (h₁ : Δ ⊢[PRAAx] a ≐ a') (h₂ : Δ ⊢[PRAAx] b ≐ b') :
    Δ ⊢[PRAAx] absd a b ≐ absd a' b' :=
  congrAdd (congrMonus h₁ h₂) (congrMonus h₂ h₁)

/-! ## The error sums -/

section Sums
variable {x K L : PTm n} (hx : Γ ⊢[PRAAx] le one x) (hK : Γ ⊢[PRAAx] le one K) (hx4 : Γ ⊢[PRAAx] le (Q4 x) K)
  (hL : Γ ⊢[PRAAx] le (K * Q4 x) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
include hx hK hx4 hL hP

theorem hxK : Γ ⊢[PRAAx] le x K := le_trans (le_Q4 x) hx4

theorem hL2 : Γ ⊢[PRAAx] le (K * (two * x)) L := by
  have h : Γ ⊢[PRAAx] le (two * x) (Q4 x) := by
    ipra_le 𝔞 x * 𝔞 x * 𝔞 x * 𝔞 x + 4 * (𝔞 x * 𝔞 x * 𝔞 x) + 6 * (𝔞 x * 𝔞 x) + 2 * 𝔞 x + 1
  exact le_trans (le_scale K h) hL

theorem xq : Γ ⊢[PRAAx] le (x * quo (fact L) K) (fact L) := by
  have q1 := mul_le_mul_right (quo (fact L) K) (hxK hx hK hx4 hL hP)
  have q2 := quo_mul_le (Γ := Γ) (x := fact L) (pos_of_lt_zero hK)
  ipra_le sl q1 + sl q2

/-- One error term of `f = ψ`: `ψ(m)(Δ_m + ⌊F/K⌋) ≤ 8F²` for `m ≤ x`. -/
theorem errP_pt {m : PTm n} (hmx : Γ ⊢[PRAAx] le m x) :
    Γ ⊢[PRAAx] le (Psi wt m (pairT K (fact L)) *
        (monus (S (K * succ m) (fact L)) (S (K * m) (fact L)) + quo (fact L) K))
      (two * (two * (two * (fact L * fact L)))) := by
  have p := psi_k hK hP hmx
  have p1 := mul_le_mul_right (monus (S (K * succ m) (fact L)) (S (K * m) (fact L))) p
  have d := le_scale (two * (two * fact L)) (dlt_k hK m (fact L))
  have p2 := mul_le_mul_right (quo (fact L) K) p
  have mq := mul_le_mul_right (quo (fact L) K) hmx
  have q := le_scale (two * (two * fact L)) (le_trans mq (xq hx hK hx4 hL hP))
  ipra_le sl p1 + sl d + sl p2 + sl q

/-- One error term of `f = F · id`: `Fm(Δ_m + ⌊F/K⌋) ≤ 2F²` for `m ≤ x`. -/
theorem errQ_pt {m : PTm n} (hmx : Γ ⊢[PRAAx] le m x) :
    Γ ⊢[PRAAx] le (fact L * m * (monus (S (K * succ m) (fact L)) (S (K * m) (fact L)) + quo (fact L) K))
      (two * (fact L * fact L)) := by
  have d := le_scale (fact L) (dlt_k hK m (fact L))
  have mq := mul_le_mul_right (quo (fact L) K) hmx
  have q := le_scale (fact L) (le_trans mq (xq hx hK hx4 hL hP))
  ipra_le sl d + sl q

omit hx hK hx4 hL hP in
/-- `Σ_{d≤x} Λ(d) f(⌊x/d⌋)(Δ + ⌊F/K⌋) ≤ c ψ(x)` from the pointwise bound `f(m)(Δ_m + ⌊F/K⌋) ≤ c`. -/
theorem err_le (f : PTm 2) (c : PTm n)
    (hpt : Cd x Γ ⊢[PRAAx] le (inst2 (f * dqB) (quo (Syn.shift x) (var 0)) (pairT (Syn.shift K) (fact (Syn.shift L))))
      (Syn.shift c)) :
    Γ ⊢[PRAAx] le (sz (errB f) x K L) (c * Psi wt x (pairT K (fact L))) := by
  have p := sum_le_params (Γ := Γ) (errB f) (cmB (LamB wt)) (pairT x (pairT K (fact L)))
    (pairT c (pairT K (fact L))) (succ x) (.allI (.impI (by
      simp only [ConvSummatory.shift_succ_x, shift_pairT, shift_fact']
      refine le_congr (hRB_at _ _ _ _ _).eqSymm (cm_pt _ _ _ _).eqSymm ?_
      simp only [inst2_LamB, inst2_lamW]
      refine .orE (zero_or_succ (var 0)) ?_ ?_
      · exact le_congr (zero_mul_l (zero_mul_l ((congrSg Prf.hyp0).eqTrans sg_zero) _) _).eqSymm (.eqRefl _)
          (zero_le _)
      · have s1 := sg_le_one (Γ := Cd x Γ) (var 0)
        have r := mul_le_mul_right (Lam wt (var 0) (pairT (Syn.shift K) (fact (Syn.shift L))) *
          inst2 (f * dqB) (quo (Syn.shift x) (var 0)) (pairT (Syn.shift K) (fact (Syn.shift L)))) s1
        have l := le_scale (Lam wt (var 0) (pairT (Syn.shift K) (fact (Syn.shift L)))) hpt
        ipra_le sl r + sl l)))
  have c := natEq (sum_const_mul (Γ := Γ) (LamB wt) (succ x) c (pairT K (fact L)))
  ipra_le sl p with -c

omit hx hK hx4 hL hP in
theorem qx_le : Cd x Γ ⊢[PRAAx] le (quo (Syn.shift x) (var 0)) (Syn.shift x) :=
  le_congr (congrAp2 quoF (.eqRefl _) Prf.hyp0).eqSymm (.eqRefl _) (quo_le_self _ _)

theorem shifts :
    (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift x) ⋏ (le one (Syn.shift K) ⋏ (le (Q4 (Syn.shift x)) (Syn.shift K) ⋏
      (le (Syn.shift K * Q4 (Syn.shift x)) (Syn.shift L) ⋏
        le (Syn.shift K * pw two (two * (two * Syn.shift x))) (Syn.shift L)))) := by
  have a : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift x) := by simpa [Fm.shift, Syn.shift] using hx.shift
  have b : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hK.shift
  have c : (Γ.map Fm.shift) ⊢[PRAAx] le (Q4 (Syn.shift x)) (Syn.shift K) := by
    simpa [Fm.shift, Syn.shift] using hx4.shift
  have d : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * Q4 (Syn.shift x)) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hL.shift
  have e : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * pw two (two * (two * Syn.shift x))) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hP.shift
  exact .andI a (.andI b (.andI c (.andI d e)))

/-- `Σ_{d≤x} Λ(d) ψ(⌊x/d⌋)(Δ + ⌊F/K⌋) ≤ 8F² ψ(x)`. -/
theorem errP_le :
    Γ ⊢[PRAAx] le (sz (errB psiB) x K L) (two * (two * (two * (fact L * fact L))) * Psi wt x (pairT K (fact L))) := by
  have sh := ((shifts hx hK hx4 hL hP).wk (ψ := lt (var 0) (succ (Syn.shift x)))).wk
    (ψ := (var 0) ≐ succ (pred (var 0)))
  refine err_le psiB _ ?_
  rw [inst2_mul, inst2_psiB, show Syn.shift (two * (two * (two * (fact L * fact L))) : PTm n) =
    two * (two * (two * (fact (Syn.shift L) * fact (Syn.shift L)))) by simp [Syn.shift]]
  refine le_congr (congrMul (.eqRefl _) (dq_at _ _ _)).eqSymm (.eqRefl _) ?_
  exact errP_pt (Prf.andE₁ sh) (Prf.andE₁ (Prf.andE₂ sh)) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ sh)))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ sh)))) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ sh)))) qx_le

/-- `Σ_{d≤x} Λ(d) F⌊x/d⌋(Δ + ⌊F/K⌋) ≤ 2F² ψ(x)`. -/
theorem errQ_le :
    Γ ⊢[PRAAx] le (sz (errB qB) x K L) (two * (fact L * fact L) * Psi wt x (pairT K (fact L))) := by
  have sh := ((shifts hx hK hx4 hL hP).wk (ψ := lt (var 0) (succ (Syn.shift x)))).wk
    (ψ := (var 0) ≐ succ (pred (var 0)))
  refine err_le qB _ ?_
  rw [inst2_mul, inst2_qB, show Syn.shift (two * (fact L * fact L) : PTm n) =
    two * (fact (Syn.shift L) * fact (Syn.shift L)) by simp [Syn.shift]]
  refine le_congr (congrMul (congrMul (snd_pair _ _) (.eqRefl _)) (dq_at _ _ _)).eqSymm (.eqRefl _) ?_
  exact errQ_pt (Prf.andE₁ sh) (Prf.andE₁ (Prf.andE₂ sh)) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ sh)))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ sh)))) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ sh)))) qx_le

/-- `Σ_{d≤x} Λ(d) |E_ψ(⌊x/d⌋) − E_{F·id}(⌊x/d⌋)| ≤ 4096 F · F Σ_d Λ(d)⌊x/d⌋`. -/
theorem dC_le :
    Γ ⊢[PRAAx] le (sz (hRB (adB (EfB psiB) (EfB qB)) lamW) x K L) (num 4096 * fact L * (fact L * Lq x K L)) := by
  have sh := ((shifts hx hK hx4 hL hP).wk (ψ := lt (var 0) (succ (Syn.shift x)))).wk
    (ψ := (var 0) ≐ succ (pred (var 0)))
  have p := sum_le_params (Γ := Γ) (hRB (adB (EfB psiB) (EfB qB)) lamW) (cmB (hRB qB lamW))
    (pairT x (pairT K (fact L))) (pairT (num 4096 * fact L) (pairT x (pairT K (fact L)))) (succ x)
    (.allI (.impI (by
      simp only [ConvSummatory.shift_succ_x, shift_pairT, shift_fact']
      rw [show Syn.shift (num 4096 * fact L : PTm n) = num 4096 * fact (Syn.shift L) by simp [Syn.shift]]
      refine le_congr (hRB_at _ _ _ _ _).eqSymm ((cm_pt _ _ _ _).eqTrans (congrMul (.eqRefl _)
        (hRB_at _ _ _ _ _))).eqSymm ?_
      rw [inst2_adB, inst2_EfB, inst2_EfB, inst2_S1, inst2_S1, inst2_lamW]
      refine .orE (zero_or_succ (var 0)) ?_ ?_
      · exact le_congr (zero_mul_l (zero_mul_l ((congrSg Prf.hyp0).eqTrans sg_zero) _) _).eqSymm (.eqRefl _)
          (zero_le _)
      · have hv : Cd x Γ ⊢[PRAAx] le (var 0) (Syn.shift x) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp1
        have hm := lt_zero_of_pos (quo_pos (Γ := Cd x Γ) Prf.hyp0 hv)
        have e := e_absd hm qx_le (Prf.andE₁ (Prf.andE₂ sh)) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ sh)))
          (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ sh)))) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ sh))))
        have ea := absd_congr (Δ := Cd x Γ)
          (congrAdd (congrMul (.eqRefl (inst2 psiB (quo (Syn.shift x) (var 0)) (pairT (Syn.shift K) (fact (Syn.shift L)))))
            (uw_at (quo (Syn.shift x) (var 0)) (Syn.shift K) (fact (Syn.shift L))))
            (.eqRefl (ap2 (sumF (hRB psiB lamW)) (succ (quo (Syn.shift x) (var 0)))
              (pairT (quo (Syn.shift x) (var 0)) (pairT (Syn.shift K) (fact (Syn.shift L)))))))
          (congrAdd (congrMul (.eqRefl (inst2 qB (quo (Syn.shift x) (var 0)) (pairT (Syn.shift K) (fact (Syn.shift L)))))
            (uw_at (quo (Syn.shift x) (var 0)) (Syn.shift K) (fact (Syn.shift L))))
            (.eqRefl (ap2 (sumF (hRB qB lamW)) (succ (quo (Syn.shift x) (var 0)))
              (pairT (quo (Syn.shift x) (var 0)) (pairT (Syn.shift K) (fact (Syn.shift L)))))))
        have e' := le_congr ea.eqSymm (.eqRefl _) e
        have sc := le_scale (sg (var 0) * Lam wt (var 0) (pairT (Syn.shift K) (fact (Syn.shift L)))) e'
        have eq : Cd x Γ ⊢[PRAAx] inst2 qB (quo (Syn.shift x) (var 0)) (pairT (Syn.shift K) (fact (Syn.shift L))) ≐
            fact (Syn.shift L) * quo (Syn.shift x) (var 0) := by
          rw [inst2_qB]; exact congrMul (snd_pair _ _) (.eqRefl _)
        have q := natEq eq
        ipra_le sl sc with 4096 * 𝔞 (fact (Syn.shift L)) * 𝔞 (sg (var 0)) *
          𝔞 (Lam wt (var 0) (pairT (Syn.shift K) (fact (Syn.shift L)))) * q)))
  have c := natEq (sum_const_mul (Γ := Γ) (hRB qB lamW) (succ x) (num 4096 * fact L) (pairT x (pairT K (fact L))))
  have s := natEq (s1Q (Γ := Γ) x K L)
  ipra_le sl p with c + 4096 * 𝔞 (fact L) * s

/-- `Σ_{j≤x} Λ(j)⌊x/j⌋ = L_w(x!) ≤ x u_x`. -/
theorem lq_le : Γ ⊢[PRAAx] le (Lq x K L) (x * U x K (fact L)) := by
  have lu := lfact_upper hx hK (le_trans (le_scale K (le_Q4 x)) hL)
  have sx := S_le (Γ := Γ) x (fact L)
  have fe := natEq (factorial_lambda (Γ := Γ) wt x (pairT K (fact L)))
  ipra_le sl lu + sl sx with fe

/-- `sb:first-weighted-bound`, scaled: `|ψ(x) − Fx| u_x² ≤ Σ_{n≤x} a(n) |R(⌊x/n⌋)| + 8192 F² x u_x + 40 F³ x`,
`a = Λ * Λ + Λ u`. -/
theorem first_weighted :
    Γ ⊢[PRAAx] le (absd (inst2 psiB x (pairT K (fact L)) * U x K (fact L) * U x K (fact L))
        (inst2 qB x (pairT K (fact L)) * U x K (fact L) * U x K (fact L)))
      (sz (hRB (adB psiB qB) (cvF lamW lamW)) x K L + sz (hRB (adB psiB qB) luB) x K L +
        num 8192 * (fact L * fact L * (x * U x K (fact L))) + num 40 * (fact L * fact L * fact L * x)) := by
  have h2 := hL2 hx hK hx4 hL hP
  have cmb := combine (fid_lo psiB psi_mono psi_zero hK h2) (fid_hi psiB psi_mono psi_zero hK h2)
    (fid_lo qB q_mono q_zero hK h2) (fid_hi qB q_mono q_zero hK h2)
  -- `|ΔE|`
  have eE := e_absd hx (le_refl x) hK hx4 hL hP
  have sE := le_trans (le_congr (absd_congr (mul_comm _ _) (mul_comm _ _)).eqSymm (.eqRefl _)
    (absd_scale (Γ := Γ) (U x K (fact L)) _ _)) (le_scale (U x K (fact L)) eE)
  have dD := absd_hRB (Γ := Γ) psiB qB (cvF lamW lamW) (succ x) (pairT x (pairT K (fact L)))
  have dB := absd_hRB (Γ := Γ) psiB qB luB (succ x) (pairT x (pairT K (fact L)))
  have dC := le_trans (absd_hRB (Γ := Γ) (EfB psiB) (EfB qB) lamW (succ x) (pairT x (pairT K (fact L))))
    (dC_le hx hK hx4 hL hP)
  have lq := le_scale (num 4096 * fact L * fact L) (lq_le hx hK hx4 hL hP)
  have eP := errP_le hx hK hx4 hL hP
  have eQ := errQ_le hx hK hx4 hL hP
  have ps := psi_k hK hP (le_refl x)
  have pP := le_scale (two * (two * (two * (fact L * fact L)))) ps
  have pQ := le_scale (two * (fact L * fact L)) ps
  ipra_le sl cmb + sl sE + sl dD + sl dB + sl dC + sl lq + sl eP + sl eQ + sl pP + sl pQ

end Sums

end LeanProofs.IPRA.AnalyticNumberTheory.WeightedBound
