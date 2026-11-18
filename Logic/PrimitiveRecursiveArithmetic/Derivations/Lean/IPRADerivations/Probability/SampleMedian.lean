import IPRADerivations.Probability.ProductPower
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.AnalyticNumberTheory.EulerProduct
import IPRADerivations.AnalyticNumberTheory.WeightedMangoldt
import IPRADerivations.Probability.Histogram

/-!
# The binomial count law and the exact odd-sample median CDF

Packet: `probability/median_ipra_constructive_proofs`, Theorem `thm:sample-cdf`.

## The closed form

`G(r, k) = [k ≤ r] C(r, k) a^k c^{r−k}` (with a guard, so that no vanishing of `C(r, k)` above the
diagonal is needed) satisfies `G(0, k) = [k = 0]`, `G(r + 1, 0) = c G(r, 0)` and
`G(r + 1, k + 1) = c G(r, k + 1) + a G(r, k)` (`G_zero`, `G_succ_zero`, `G_succ_succ`, by Pascal's rule).

## The count law

On the `r`-fold product law of `Probability/ProductPower` (weights `P_r(t)`, sample sum `S_r(t)` of an
indicator `X ≤ 1`, `a = ∑ w X`, `c = ∑ w (1 − X)`), the count weights `F_r(k) = ∑_t P_r(t) [S_r(t) = k]`
(the pushforward of the product law along the count) satisfy `F_0(k) = [k = 0]` and
`F_{r+1}(k) = c F_r(k) + a F'_r(k)` with `F'_r(0) = 0`, `F'_r(k + 1) = F_r(k)` (`block_F`, `F_succ`, by
peeling the top coordinate and `eqb_split`). The two recurrences agree, so `F_r(k) = G(r, k)` for every
`k` (`count_law`): the induction on `r` is on the quantifier-free vanishing of the violation count
`∑_{k<B} [F_r(k) ≠ G(r, k)]` (`V_zero`, `V_succ`).

## The median CDF

`sample_cdf` (`thm:sample-cdf`): with `X(i) = [v_i ≤ v_j]`, `a = P_j`, `c = W − P_j`,
`∑_{t<M^N} P_N(t) [S_N(t) ≥ ⌊N/2⌋ + 1] = ∑_{k ≤ N} [k ≥ ⌊N/2⌋ + 1] C(N, k) P_j^k (W − P_j)^{N−k}`, by the
finite LOTUS along the count (`Histogram.lotus_bounded`, `S_N ≤ N` by `Sr_le`) and the count law. For odd
`N = 2n + 1`, `S_N ≥ n + 1` (at least `n + 1` observations are `≤ v_j`) is exactly `M_N ≤ v_j`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.SampleMedian

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_zero' binom_self' pascal_at)
open LeanProofs.IPRA.Probability.ProductPower (TB SB Pr Sr TB_at SB_at pr_peel sr_peel peel_sum lin3 shift_mul'' shift_zero'
  shift_inst2' one_bound tb_zero)
open LeanProofs.IPRA.Probability.Lotus (vB inst2_vB)
open LeanProofs.IPRA.Probability.Expectation (inst2_mul')
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (eqb_succ_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The guarded closed form -/

/-- `[k ≤ r]`. -/
abbrev ind (k r : PTm n) : PTm n := monus one (monus k r)

theorem ind_le {k r : PTm n} (h : Γ ⊢[PRAAx] le k r) : Γ ⊢[PRAAx] ind k r ≐ one :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_zero _)

theorem ind_gt {k r : PTm n} (h : Γ ⊢[PRAAx] lt r k) : Γ ⊢[PRAAx] ind k r ≐ zero := by
  have e := eq_add_of_le h
  have m : Γ ⊢[PRAAx] monus k r ≐ succ (monus k (succ r)) :=
    (congrMonus e (.eqRefl _)).eqTrans ((congrMonus (by apply deriveNat; ipra_simps; ring) (.eqRefl _)).eqTrans
      (add_monus' _ _))
  exact (congrMonus (.eqRefl _) m).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _))

/-- `G(r, k) = [k ≤ r] C(r, k) a^k c^{r−k}`. -/
abbrev G (a c r k : PTm n) : PTm n := ind k r * (binom r k * (pw a k * pw c (monus r k)))

theorem G_zero (a c k : PTm n) : Γ ⊢[PRAAx] G a c zero k ≐ eqb zero k := by
  refine .orE (zero_or_succ k) ?_ ?_
  · let C := (k ≐ zero) :: Γ
    have hk : C ⊢[PRAAx] k ≐ zero := Prf.hyp0
    have i := ind_le (Γ := C) (k := k) (r := zero) (le_congr hk.eqSymm (.eqRefl _) (le_refl _))
    have b : C ⊢[PRAAx] binom zero k ≐ one := (Combinatorics.BinomialTheorem.congrBinom (.eqRefl _) hk).eqTrans (binom_zero' _)
    have p1 : C ⊢[PRAAx] pw a k ≐ one := (congrAp2 powF hk (.eqRefl _)).eqTrans (pw_zero _)
    have p2 : C ⊢[PRAAx] pw c (monus zero k) ≐ one := (congrAp2 powF (zero_monus _) (.eqRefl _)).eqTrans (pw_zero _)
    refine (congrMul i (congrMul b (congrMul p1 p2))).eqTrans ?_
    refine .eqTrans ?_ (eqb_of_eq hk.eqSymm).eqSymm
    apply deriveNat; ipra_simps; ring
  · let C := (k ≐ succ (pred k)) :: Γ
    have hk : C ⊢[PRAAx] lt zero k := le_congr (.eqRefl _) Prf.hyp0.eqSymm
      (le_of_eq_add (d := pred k) (by apply deriveNat; ipra_simps; ring))
    refine (congrMul (ind_gt hk) (.eqRefl _)).eqTrans ((zero_mul _).eqTrans ?_)
    exact (eqb_zero_of_lt hk).eqSymm

theorem G_succ_zero (a c r : PTm n) : Γ ⊢[PRAAx] G a c (succ r) zero ≐ c * G a c r zero := by
  have i1 := ind_le (Γ := Γ) (zero_le (succ r))
  have i0 := ind_le (Γ := Γ) (zero_le r)
  have e1 : Γ ⊢[PRAAx] pw c (monus (succ r) zero) ≐ pw c r * c :=
    (congrAp2 powF (monus_zero _) (.eqRefl _)).eqTrans (pw_succ _ _)
  have e0 : Γ ⊢[PRAAx] pw c (monus r zero) ≐ pw c r := congrAp2 powF (monus_zero _) (.eqRefl _)
  refine (congrMul i1 (congrMul (binom_zero' _) (congrMul (pw_zero _) e1))).eqTrans (.eqTrans ?_
    (congrMul (.eqRefl _) (congrMul i0 (congrMul (binom_zero' _) (congrMul (pw_zero _) e0)))).eqSymm)
  apply deriveNat; ipra_simps; ring

theorem G_succ_succ (a c r k : PTm n) :
    Γ ⊢[PRAAx] G a c (succ r) (succ k) ≐ c * G a c r (succ k) + a * G a c r k := by
  have ea : Γ ⊢[PRAAx] pw a (succ k) ≐ pw a k * a := pw_succ _ _
  have em : Γ ⊢[PRAAx] monus (succ r) (succ k) ≐ monus r k := succ_monus_succ _ _
  refine .orE (lt_or_le k r) ?_ ?_
  · -- `k < r`: Pascal's rule, all guards are `1`.
    let C := lt k r :: Γ
    have h : C ⊢[PRAAx] lt k r := Prf.hyp0
    have g1 := ind_le (Γ := C) (le_trans (show C ⊢[PRAAx] le (succ k) r from h) (le_succ_self r))
    have g2 := ind_le (Γ := C) (show C ⊢[PRAAx] le (succ k) r from h)
    have g3 := ind_le (Γ := C) (le_of_lt h)
    have er : C ⊢[PRAAx] monus r k ≐ succ (monus r (succ k)) := by
      have e := eq_add_of_le h
      exact (congrMonus e (.eqRefl _)).eqTrans ((congrMonus (by apply deriveNat; ipra_simps; ring) (.eqRefl _)).eqTrans
        (add_monus' _ _))
    have pc : C ⊢[PRAAx] pw c (monus r k) ≐ pw c (monus r (succ k)) * c := (congrAp2 powF er (.eqRefl _)).eqTrans (pw_succ _ _)
    have pa := pascal_at (Γ := C) h
    refine (congrMul g1 (congrMul pa (congrMul ea.wk ((congrAp2 powF em.wk (.eqRefl _)).eqTrans pc)))).eqTrans (.eqTrans ?_
      (congrAdd (congrMul (.eqRefl _) (congrMul g2 (congrMul (.eqRefl _) (congrMul ea.wk (.eqRefl _))))) (congrMul (.eqRefl _) (congrMul g3 (congrMul (.eqRefl _)
        (congrMul (.eqRefl _) pc))))).eqSymm)
    apply deriveNat; ipra_simps; ring
  · let C := le r k :: Γ
    refine .orE (lt_or_eq_of_le (Prf.hyp0 : C ⊢[PRAAx] le r k)) ?_ ?_
    · -- `r < k`: every term vanishes.
      let C' := lt r k :: C
      have h : C' ⊢[PRAAx] lt r k := Prf.hyp0
      have z1 := ind_gt (Γ := C') (show C' ⊢[PRAAx] lt (succ r) (succ k) from (succ_monus_succ _ _).eqTrans h)
      have z2 := ind_gt (Γ := C') (lt_of_lt_of_le h (le_succ_self k))
      have z3 := ind_gt (Γ := C') h
      refine (congrMul z1 (.eqRefl _)).eqTrans ((zero_mul _).eqTrans (.eqTrans ?_
        (congrAdd (congrMul (.eqRefl _) (congrMul z2 (.eqRefl _))) (congrMul (.eqRefl _) (congrMul z3 (.eqRefl _)))).eqSymm))
      apply deriveNat; ipra_simps; ring
    · -- `r = k`: only `a G(r, r)` survives.
      let C' := (r ≐ k) :: C
      have h : C' ⊢[PRAAx] r ≐ k := Prf.hyp0
      have g1 := ind_le (Γ := C') (le_congr (congrSucc h) (.eqRefl _) (le_refl (succ r)))
      have z2 := ind_gt (Γ := C') (le_congr (.eqRefl _) (congrSucc h) (le_refl (succ r)))
      have g3 := ind_le (Γ := C') (le_congr h (.eqRefl _) (le_refl r))
      have b1 : C' ⊢[PRAAx] binom (succ r) (succ k) ≐ one :=
        (Combinatorics.BinomialTheorem.congrBinom (.eqRefl _) (congrSucc h.eqSymm)).eqTrans (binom_self' _)
      have b3 : C' ⊢[PRAAx] binom r k ≐ one := (Combinatorics.BinomialTheorem.congrBinom (.eqRefl _) h.eqSymm).eqTrans (binom_self' _)
      have m0 : C' ⊢[PRAAx] pw c (monus r k) ≐ one :=
        (congrAp2 powF ((congrMonus (.eqRefl _) h.eqSymm).eqTrans (monus_self _)) (.eqRefl _)).eqTrans (pw_zero _)
      refine (congrMul g1 (congrMul b1 (congrMul ea.wk.wk ((congrAp2 powF em.wk.wk (.eqRefl _)).eqTrans m0)))).eqTrans (.eqTrans ?_
        (congrAdd (congrMul (.eqRefl _) (congrMul z2 (.eqRefl _))) (congrMul (.eqRefl _) (congrMul g3 (congrMul b3
          (congrMul (.eqRefl _) m0))))).eqSymm)
      apply deriveNat; ipra_simps; ring

/-! ## The count law on the product space -/

/-- An indicator value splits `[s + x = k]` for `x ≤ 1`. -/
theorem eqb_split {s x k : PTm n} (hx : Γ ⊢[PRAAx] le x one) :
    Γ ⊢[PRAAx] eqb (s + x) k ≐ monus one x * eqb s k + x * eqb (succ s) k := by
  refine .orE (zero_or_succ x) ?_ ?_
  · let C := (x ≐ zero) :: Γ
    have hz : C ⊢[PRAAx] x ≐ zero := Prf.hyp0
    refine (congrEqb ((congrAdd (.eqRefl _) hz).eqTrans (add_zero _)) (.eqRefl _)).eqTrans ?_
    refine .eqTrans ?_ (congrAdd (congrMul ((congrMonus (.eqRefl _) hz.eqSymm).eqSymm.eqTrans (monus_zero _) |>.eqSymm) (.eqRefl _))
      (congrMul hz.eqSymm (.eqRefl _)))
    apply deriveNat; ipra_simps; ring
  · let C := (x ≐ succ (pred x)) :: Γ
    have h1 : C ⊢[PRAAx] x ≐ one := by
      have l : C ⊢[PRAAx] le (pred x) zero := (succ_monus_succ _ _).eqSymm.eqTrans (congrMonus Prf.hyp0.eqSymm (.eqRefl _) |>.eqTrans hx.wk)
      have z : C ⊢[PRAAx] pred x ≐ zero := le_antisymm l (zero_le _)
      exact Prf.hyp0.eqTrans (congrSucc z)
    refine (congrEqb ((congrAdd (.eqRefl _) h1).eqTrans (succ_eq_add_one _).eqSymm) (.eqRefl _)).eqTrans ?_
    refine .eqTrans ?_ (congrAdd (congrMul ((congrMonus (.eqRefl _) h1.eqSymm).eqSymm.eqTrans (monus_self _) |>.eqSymm) (.eqRefl _))
      (congrMul h1.eqSymm (.eqRefl _)))
    apply deriveNat; ipra_simps; ring

section Count

variable (w X : PTm 2)

/-- `P_r(t) [S_r(t) = k]`, over `0 = t`, `1 = ⟨k, ⟨r, ⟨M, x⟩⟩⟩` (the pushforward weight of the count). -/
abbrev fB : PTm 2 := vB (TB w) (SB X)
/-- `P_r(t) [S_r(t) + 1 = k]`. -/
abbrev fB' : PTm 2 := Syn.subst ![var 0, sndT (var 1)] (TB w) * eqb (succ (Syn.subst ![var 0, sndT (var 1)] (SB X))) (fstT (var 1))

/-- `F_r(k) = ∑_{t<M^r} P_r(t) [S_r(t) = k]`. -/
abbrev Ft (k r M x : PTm n) : PTm n := ap2 (sumF (fB w X)) (pw M r) (pairT k (pairT r (pairT M x)))
abbrev Ft' (k r M x : PTm n) : PTm n := ap2 (sumF (fB' w X)) (pw M r) (pairT k (pairT r (pairT M x)))

theorem fB_at (t k r M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (fB w X) t (pairT k (pairT r (pairT M x))) ≐ Pr w r t M x * eqb (Sr X r t M x) k := by
  rw [inst2_vB]
  have s : Γ ⊢[PRAAx] sndT (pairT k (pairT r (pairT M x))) ≐ pairT r (pairT M x) := snd_pair _ _
  exact congrMul ((congrInst2 _ (.eqRefl _) s).eqTrans (TB_at w _ _ _ _))
    (congrEqb ((congrInst2 _ (.eqRefl _) s).eqTrans (SB_at X _ _ _ _)) (fst_pair _ _))

theorem fB'_at (t k r M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (fB' w X) t (pairT k (pairT r (pairT M x))) ≐ Pr w r t M x * eqb (succ (Sr X r t M x)) k := by
  have e : inst2 (fB' w X) t (pairT k (pairT r (pairT M x))) =
      inst2 (TB w) t (sndT (pairT k (pairT r (pairT M x)))) *
        eqb (succ (inst2 (SB X) t (sndT (pairT k (pairT r (pairT M x)))))) (fstT (pairT k (pairT r (pairT M x)))) := by
    simp only [inst2, fB', PTm.subst_mul, subst_eqb, subst_fstT, ConciseIPRA.PTm.subst_succ, Syn.subst_subst]
    congr 1
    · congr 1; funext j; fin_cases j <;> simp
    · congr 1
      congr 2; funext j; fin_cases j <;> simp
  rw [e]
  have s : Γ ⊢[PRAAx] sndT (pairT k (pairT r (pairT M x))) ≐ pairT r (pairT M x) := snd_pair _ _
  exact congrMul ((congrInst2 _ (.eqRefl _) s).eqTrans (TB_at w _ _ _ _))
    (congrEqb (congrSucc ((congrInst2 _ (.eqRefl _) s).eqTrans (SB_at X _ _ _ _))) (fst_pair _ _))

/-- One block of `F_{r+1}(k)`: `∑_u P_{r+1}(a M^r + u) [S_{r+1} = k] = w_a (1 − X_a) F_r(k) + w_a X_a F'_r(k)`. -/
theorem block_F {a k r M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (ha : Γ ⊢[PRAAx] lt a M)
    (hX : Γ ⊢[PRAAx] le (inst2 X a x) one) :
    Γ ⊢[PRAAx] inst2 (BlockSum.blkB (fB w X)) a (pairT (pw M r) (pairT k (pairT (succ r) (pairT M x)))) ≐
      (inst2 w a x * monus one (inst2 X a x)) * Ft w X k r M x +
        ((inst2 w a x * inst2 X a x) * Ft' w X k r M x + zero * Ft w X k r M x) := by
  refine (BlockSum.blk_at _ _ _ _).eqTrans (lin3 (fB w X) (fB' w X) (fB w X) (offB (fB w X)) (.allI (.impI ?_)))
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have ha' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift a) (Syn.shift M) := by
    have e := ha.shift; simp only [Fm.shift, subst_lt, subst_le, ConciseIPRA.PTm.subst_succ] at e; simpa [Syn.shift] using e
  have hX' : Γ.map Fm.shift ⊢[PRAAx] le (inst2 X (Syn.shift a) (Syn.shift x)) one := by
    have e := hX.shift; simp only [Fm.shift, subst_le] at e; simpa [Syn.shift, shift_inst2'] using e
  simp only [shift_pairT, shift_mul'', shift_inst2', shift_zero']
  have hp : Syn.shift (pw M r) = pw (Syn.shift M) (Syn.shift r) := by simp [Syn.shift]
  have hs : Syn.shift (succ r) = succ (Syn.shift r) := by simp [Syn.shift]
  have hm1 : Syn.shift (monus one (inst2 X a x)) = monus one (inst2 X (Syn.shift a) (Syn.shift x)) := by
    simp [Syn.shift, shift_inst2']
  rw [hp, hs, hm1]
  let C : List (Fm PTm (n + 1)) := lt (var 0) (pw (Syn.shift M) (Syn.shift r)) :: Γ.map Fm.shift
  have hu : C ⊢[PRAAx] lt (var 0) (pw (Syn.shift M) (Syn.shift r)) := Prf.hyp0
  rw [inst2_offB]
  have s : C ⊢[PRAAx] sndT (pairT (Syn.shift a * pw (Syn.shift M) (Syn.shift r))
      (pairT (Syn.shift k) (pairT (succ (Syn.shift r)) (pairT (Syn.shift M) (Syn.shift x))))) ≐
      pairT (Syn.shift k) (pairT (succ (Syn.shift r)) (pairT (Syn.shift M) (Syn.shift x))) := snd_pair _ _
  refine (congrInst2 _ (congrAdd (fst_pair _ _) (.eqRefl _)) s).eqTrans ?_
  refine (fB_at w X _ _ _ _ _).eqTrans ?_
  have p1 := pr_peel w (x := Syn.shift x) hM'.wk ha'.wk hu
  have s1 := sr_peel X (x := Syn.shift x) hM'.wk ha'.wk hu
  refine (congrMul p1 ((congrEqb s1 (.eqRefl _)).eqTrans (eqb_split hX'.wk))).eqTrans ?_
  refine .eqTrans ?_ (congrAdd (congrMul (.eqRefl _) (fB_at w X _ _ _ _ _)) (congrAdd (congrMul (.eqRefl _) (fB'_at w X _ _ _ _ _))
    (congrMul (.eqRefl _) (fB_at w X _ _ _ _ _)))).eqSymm
  apply deriveNat; ipra_simps; ring

/-- `F_{r+1}(k) = F_r(k) c + F'_r(k) a`, with `c = ∑ w (1 − X)`, `a = ∑ w X`. -/
theorem F_succ {k r M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hX : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶ le (inst2 X (var 0) (Syn.shift x)) one)) :
    Γ ⊢[PRAAx] Ft w X k (succ r) M x ≐ Ft w X k r M x * ap2 (sumF (w * monus one X)) M x +
      (Ft' w X k r M x * ap2 (sumF (w * X)) M x + zero * ap2 (sumF w) M x) := by
  refine (peel_sum (fB w X) r M _).eqTrans (lin3 (w * monus one X) (w * X) w _ (.allI (.impI ?_)))
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have hX' := Prf.impE hX.allOpen.wk (Prf.hyp0 : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx] _)
  simp only [shift_pairT, shift_zero']
  have hp : Syn.shift (pw M r) = pw (Syn.shift M) (Syn.shift r) := by simp [Syn.shift]
  have hs : Syn.shift (succ r) = succ (Syn.shift r) := by simp [Syn.shift]
  have hF : Syn.shift (Ft w X k r M x) = Ft w X (Syn.shift k) (Syn.shift r) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  have hF' : Syn.shift (Ft' w X k r M x) = Ft' w X (Syn.shift k) (Syn.shift r) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  rw [hp, hs, hF, hF', inst2_mul', inst2_mul']
  have hm : inst2 (monus one X) (var 0) (Syn.shift x) = monus one (inst2 X (var 0) (Syn.shift x)) := by simp [inst2]
  rw [hm]
  refine (block_F w X hM'.wk Prf.hyp0 hX').eqTrans ?_
  apply deriveNat; ipra_simps; ring

theorem F'_zero (r M x : PTm n) : Γ ⊢[PRAAx] Ft' w X zero r M x ≐ zero := by
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  rw [shift_pairT, shift_pairT, shift_pairT]
  refine (fB'_at w X _ _ _ _ _).eqTrans ?_
  have z : (lt (var 0) (Syn.shift (pw M r)) :: Γ.map Fm.shift) ⊢[PRAAx]
      eqb (succ (Sr X (Syn.shift r) (var 0) (Syn.shift M) (Syn.shift x))) (Syn.shift zero) ≐ zero := by
    rw [ConciseIPRA.PTm.shift_zero]
    exact eqb_zero_of_gt (le_of_eq_add (d := Sr X (Syn.shift r) (var 0) (Syn.shift M) (Syn.shift x))
      (by apply deriveNat; ipra_simps; ring))
  exact (congrMul (.eqRefl _) z).eqTrans (mul_zero _)

theorem F'_succ (k r M x : PTm n) : Γ ⊢[PRAAx] Ft' w X (succ k) r M x ≐ Ft w X k r M x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_pairT, shift_pairT, shift_pairT, shift_pairT, shift_pairT, shift_pairT]
  refine (fB'_at w X _ _ _ _ _).eqTrans (.eqTrans ?_ (fB_at w X _ _ _ _ _).eqSymm)
  have hs : Syn.shift (succ k) = succ (Syn.shift k) := by simp [Syn.shift]
  rw [hs]
  exact congrMul (.eqRefl _) (eqb_succ_succ _ _)

theorem F_zero (k M x : PTm n) : Γ ⊢[PRAAx] Ft w X k zero M x ≐ eqb zero k := by
  refine (one_bound _ _ _).eqTrans ((fB_at w X _ _ _ _ _).eqTrans ?_)
  have p : Γ ⊢[PRAAx] Pr w zero zero M x ≐ one := (TB_at w _ _ _ _).eqSymm.eqTrans (tb_zero w M x)
  have sz : Γ ⊢[PRAAx] Sr X zero zero M x ≐ zero := sum_zero _ _
  exact (congrMul p (congrEqb sz (.eqRefl _))).eqTrans (one_mul _)

/-! ## `F = G` by induction on `r` -/

theorem G_congr {a a' c c' r r' k k' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hc : Γ ⊢[PRAAx] c ≐ c')
    (hr : Γ ⊢[PRAAx] r ≐ r') (hk : Γ ⊢[PRAAx] k ≐ k') : Γ ⊢[PRAAx] G a c r k ≐ G a' c' r' k' :=
  congrMul (congrMonus (.eqRefl _) (congrMonus hk hr))
    (congrMul (Combinatorics.BinomialTheorem.congrBinom hr hk)
      (congrMul (congrAp2 powF hk ha) (congrAp2 powF (congrMonus hr hk) hc)))

/-- The violation body `1 ∸ [F_r(k) = G(r, k)]`, over `0 = k`, `1 = ⟨⟨a, c⟩, ⟨r, ⟨M, x⟩⟩⟩`. -/
abbrev vB2 : PTm 2 :=
  monus one (eqb (ap2 (sumF (fB w X)) (pw (fstT (sndT (sndT (var 1)))) (fstT (sndT (var 1)))) (pairT (var 0) (sndT (var 1))))
    (G (fstT (fstT (var 1))) (sndT (fstT (var 1))) (fstT (sndT (var 1))) (var 0)))

theorem vB2_at (k a c r M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (vB2 w X) k (pairT (pairT a c) (pairT r (pairT M x))) ≐
      monus one (eqb (Ft w X k r M x) (G a c r k)) := by
  have e : inst2 (vB2 w X) k (pairT (pairT a c) (pairT r (pairT M x))) =
      monus one (eqb (ap2 (sumF (fB w X)) (pw (fstT (sndT (sndT (pairT (pairT a c) (pairT r (pairT M x))))))
          (fstT (sndT (pairT (pairT a c) (pairT r (pairT M x)))))) (pairT k (sndT (pairT (pairT a c) (pairT r (pairT M x))))))
        (G (fstT (fstT (pairT (pairT a c) (pairT r (pairT M x))))) (sndT (fstT (pairT (pairT a c) (pairT r (pairT M x)))))
          (fstT (sndT (pairT (pairT a c) (pairT r (pairT M x))))) k)) := by simp [inst2]
  rw [e]
  have s : Γ ⊢[PRAAx] sndT (pairT (pairT a c) (pairT r (pairT M x))) ≐ pairT r (pairT M x) := snd_pair _ _
  have f : Γ ⊢[PRAAx] fstT (pairT (pairT a c) (pairT r (pairT M x))) ≐ pairT a c := fst_pair _ _
  have hr : Γ ⊢[PRAAx] fstT (sndT (pairT (pairT a c) (pairT r (pairT M x)))) ≐ r := (congrFst s).eqTrans (fst_pair _ _)
  have hM : Γ ⊢[PRAAx] fstT (sndT (sndT (pairT (pairT a c) (pairT r (pairT M x))))) ≐ M :=
    (congrFst ((congrSnd s).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
  refine congrMonus (.eqRefl _) (congrEqb (congrAp2 _ (congrAp2 powF hr hM) (congrPairT (.eqRefl _) s)) ?_)
  exact G_congr ((congrFst f).eqTrans (fst_pair _ _)) ((congrSnd f).eqTrans (snd_pair _ _)) hr (.eqRefl _)

/-- The violation count `V_B(r) = ∑_{k<B} [F_r(k) ≠ G(r, k)]`. -/
abbrev Vc (B a c r M x : PTm n) : PTm n := ap2 (sumF (vB2 w X)) B (pairT (pairT a c) (pairT r (pairT M x)))

theorem V_zero (B a c M x : PTm n) : Γ ⊢[PRAAx] Vc w X B a c zero M x ≐ zero := by
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  refine (vB2_at w X _ _ _ _ _ _).eqTrans (AnalyticNumberTheory.EulerProduct.viol_of_eq ?_)
  have z : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
  rw [z]
  exact (F_zero w X _ _ _).eqTrans (G_zero _ _ _).eqSymm

/-- The induction step for the violation count. -/
theorem V_succ {B r M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hX : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶ le (inst2 X (var 0) (Syn.shift x)) one))
    (hV : Γ ⊢[PRAAx] Vc w X B (ap2 (sumF (w * X)) M x) (ap2 (sumF (w * monus one X)) M x) r M x ≐ zero) :
    Γ ⊢[PRAAx] Vc w X B (ap2 (sumF (w * X)) M x) (ap2 (sumF (w * monus one X)) M x) (succ r) M x ≐ zero := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have hX' : Γ.map Fm.shift ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (Syn.shift M)) ⟶
      le (inst2 X (var 0) (Syn.shift (Syn.shift x))) one) := by
    simpa [Fm.shift, Syn.shift, Syn.subst_subst] using hX.shift
  have eV : Syn.shift (Vc w X B (ap2 (sumF (w * X)) M x) (ap2 (sumF (w * monus one X)) M x) r M x) =
      Vc w X (Syn.shift B) (ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x)) (ap2 (sumF (w * monus one X)) (Syn.shift M) (Syn.shift x))
        (Syn.shift r) (Syn.shift M) (Syn.shift x) := by
    simp [Syn.shift]
  have hV' : Γ.map Fm.shift ⊢[PRAAx] Vc w X (Syn.shift B) (ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x))
      (ap2 (sumF (w * monus one X)) (Syn.shift M) (Syn.shift x)) (Syn.shift r) (Syn.shift M) (Syn.shift x) ≐ zero := by
    have h : Γ.map Fm.shift ⊢[PRAAx] Syn.shift (Vc w X B (ap2 (sumF (w * X)) M x) (ap2 (sumF (w * monus one X)) M x) r M x) ≐
        Syn.shift zero := hV.shift
    rw [eV, show Syn.shift (zero : PTm n) = zero by simp [Syn.shift]] at h
    exact h
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  have hsr : Syn.shift (succ r) = succ (Syn.shift r) := by simp [Syn.shift]
  have ea : Syn.shift (ap2 (sumF (w * X)) M x) = ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  have ec : Syn.shift (ap2 (sumF (w * monus one X)) M x) = ap2 (sumF (w * monus one X)) (Syn.shift M) (Syn.shift x) := by
    simp [Syn.shift]
  rw [hsr, ea, ec]
  refine (vB2_at w X _ _ _ _ _ _).eqTrans (AnalyticNumberTheory.EulerProduct.viol_of_eq ?_)
  let A := ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x)
  let Cc := ap2 (sumF (w * monus one X)) (Syn.shift M) (Syn.shift x)
  let Δ := lt (var 0) (Syn.shift B) :: Γ.map Fm.shift
  have hk : Δ ⊢[PRAAx] lt (var 0) (Syn.shift B) := Prf.hyp0
  have atk : ∀ {Δ' : List (Fm PTm (n + 1))} {k : PTm (n + 1)},
      (Δ' ⊢[PRAAx] Vc w X (Syn.shift B) A Cc (Syn.shift r) (Syn.shift M) (Syn.shift x) ≐ zero) →
      (Δ' ⊢[PRAAx] lt k (Syn.shift B)) → (Δ' ⊢[PRAAx] Ft w X k (Syn.shift r) (Syn.shift M) (Syn.shift x) ≐ G A Cc (Syn.shift r) k) :=
    fun hV hk => AnalyticNumberTheory.EulerProduct.eq_of_viol ((vB2_at w X _ _ _ _ _ _).eqSymm.eqTrans (sum_zero_elim _ hV hk))
  have fs := F_succ (Γ := Δ) w X (k := var 0) (r := Syn.shift r) hM'.wk hX'.wk
  refine fs.eqTrans ?_
  refine .orE (zero_or_succ (var 0 : PTm (n + 1))) ?_ ?_
  · let Δ' := ((var 0 : PTm (n + 1)) ≐ zero) :: Δ
    have z : Δ' ⊢[PRAAx] (var 0 : PTm (n + 1)) ≐ zero := Prf.hyp0
    have f0 := atk (Δ' := Δ') hV'.wk.wk hk.wk
    have f'0 : Δ' ⊢[PRAAx] Ft' w X (var 0) (Syn.shift r) (Syn.shift M) (Syn.shift x) ≐ zero :=
      (congrAp2 _ (.eqRefl _) (congrPairT z (.eqRefl _))).eqTrans (F'_zero w X _ _ _)
    have g := G_succ_zero (Γ := Δ') A Cc (Syn.shift r)
    have gz : Δ' ⊢[PRAAx] G A Cc (succ (Syn.shift r)) (var 0) ≐ G A Cc (succ (Syn.shift r)) zero :=
      G_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) z
    have gz' : Δ' ⊢[PRAAx] G A Cc (Syn.shift r) (var 0) ≐ G A Cc (Syn.shift r) zero :=
      G_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) z
    refine .eqTrans ?_ (gz.eqTrans g).eqSymm
    have x1 := natEq f0; have x2 := natEq f'0; have x3 := natEq gz'
    apply deriveNat; ipra_simps
    linear_combination 𝔞 Cc * (x1 + x3) + 𝔞 A * x2
  · let Δ' := ((var 0 : PTm (n + 1)) ≐ succ (pred (var 0))) :: Δ
    have z : Δ' ⊢[PRAAx] (var 0 : PTm (n + 1)) ≐ succ (pred (var 0)) := Prf.hyp0
    have hk' : Δ' ⊢[PRAAx] lt (pred (var 0)) (Syn.shift B) :=
      lt_of_lt_of_le (le_congr (.eqRefl _) z.eqSymm (le_refl _)) (le_of_lt hk.wk)
    have f1 := atk (Δ' := Δ') hV'.wk.wk hk.wk
    have f0 := atk (Δ' := Δ') hV'.wk.wk hk'
    have f' : Δ' ⊢[PRAAx] Ft' w X (var 0) (Syn.shift r) (Syn.shift M) (Syn.shift x) ≐
        Ft w X (pred (var 0)) (Syn.shift r) (Syn.shift M) (Syn.shift x) :=
      (congrAp2 _ (.eqRefl _) (congrPairT z (.eqRefl _))).eqTrans (F'_succ w X _ _ _ _)
    have g := G_succ_succ (Γ := Δ') A Cc (Syn.shift r) (pred (var 0))
    have gk : Δ' ⊢[PRAAx] G A Cc (succ (Syn.shift r)) (var 0) ≐ G A Cc (succ (Syn.shift r)) (succ (pred (var 0))) :=
      G_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) z
    have gk' : Δ' ⊢[PRAAx] G A Cc (Syn.shift r) (var 0) ≐ G A Cc (Syn.shift r) (succ (pred (var 0))) :=
      G_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) z
    refine .eqTrans ?_ (gk.eqTrans g).eqSymm
    have x1 := natEq f1; have x2 := natEq f0; have x3 := natEq f'; have x4 := natEq gk'
    apply deriveNat; ipra_simps
    linear_combination 𝔞 Cc * (x1 + x4) + 𝔞 A * (x3 + x2)

/-- The binomial count law: `F_r(k) = ∑_{t<M^r} P_r(t) [S_r(t) = k] = [k ≤ r] C(r, k) a^k c^{r−k}` with
`a = ∑ w X`, `c = ∑ w (1 − X)`, for an indicator `X ≤ 1`. -/
theorem count_law {k r M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hX : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶ le (inst2 X (var 0) (Syn.shift x)) one)) :
    Γ ⊢[PRAAx] Ft w X k r M x ≐ G (ap2 (sumF (w * X)) M x) (ap2 (sumF (w * monus one X)) M x) r k := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have hX' : Γ.map Fm.shift ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (Syn.shift M)) ⟶
      le (inst2 X (var 0) (Syn.shift (Syn.shift x))) one) := by
    simpa [Fm.shift, Syn.shift, Syn.subst_subst] using hX.shift
  have hall : Γ ⊢[PRAAx] Fm.all (Vc w X (Syn.shift (succ k)) (ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x))
      (ap2 (sumF (w * monus one X)) (Syn.shift M) (Syn.shift x)) (var 0) (Syn.shift M) (Syn.shift x) ≐ zero) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Vc, Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact V_zero w X _ _ _ _ _
    · simp only [Vc, Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact V_succ w X hM'.wk hX'.wk Prf.hyp0
  have h := Prf.allE r hall
  simp only [Vc, Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h
  exact AnalyticNumberTheory.EulerProduct.eq_of_viol ((vB2_at w X _ _ _ _ _ _).eqSymm.eqTrans
    (sum_zero_elim _ h (le_refl (succ k))))

/-! ## The odd-sample median CDF -/

/-- `[j ≥ ⌊N/2⌋ + 1]`, over `0 = j`, `1 = ⟨N, ⟨M, x⟩⟩`. -/
abbrev gB : PTm 2 := Expectation.geI (succ (half (fstT (var 1)))) (var 0)

/-- The right side `[j ≥ ⌊N/2⌋ + 1] G(N, j)`, over `0 = j`, `1 = ⟨⟨a, c⟩, N⟩`. -/
abbrev hB : PTm 2 := Expectation.geI (succ (half (sndT (var 1)))) (var 0) *
  G (fstT (fstT (var 1))) (sndT (fstT (var 1))) (sndT (var 1)) (var 0)

/-- The sample count is at most the number of observations. -/
theorem Sr_le {r t M x : PTm n} (hX : Γ ⊢[PRAAx] Fm.all (le (inst2 X (var 0) (Syn.shift x)) one)) :
    Γ ⊢[PRAAx] le (Sr X r t M x) r := by
  refine le_congr (.eqRefl _) (AnalyticNumberTheory.SumPhi.sum_ones _ _)
    (Analysis.PowerSums.sum_le _ _ _ _ (.allI (.impI ?_)))
  simp only [shift_pairT]
  have e1 : inst2 (one : PTm 2) (var 0) (pairT (Syn.shift t) (pairT (Syn.shift M) (Syn.shift x))) = (one : PTm (n + 1)) := by
    simp [inst2]
  rw [e1]
  refine le_congr (ProductPower.dB_at X _ _ _ _).eqSymm (.eqRefl _) ?_
  have hXs : Γ.map Fm.shift ⊢[PRAAx] Fm.all (le (inst2 X (var 0) (Syn.shift (Syn.shift x))) one) := by
    simpa [Fm.shift, Syn.shift, Syn.subst_subst] using hX.shift
  have h := Prf.allE (ProductPower.dg (Syn.shift M) (var 0) (Syn.shift t)) (hXs.wk : (lt (var 0) (Syn.shift r) :: Γ.map Fm.shift) ⊢[PRAAx] _)
  simpa [Syn.subst_inst_shift] using h

theorem sample_cdf {N M x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hX : Γ ⊢[PRAAx] Fm.all (le (inst2 X (var 0) (Syn.shift x)) one)) :
    Γ ⊢[PRAAx] ap2 (sumF (TB w * Lotus.gσ (SB X) gB)) (pw M N) (pairT N (pairT M x)) ≐
      ap2 (sumF hB) (succ N) (pairT (pairT (ap2 (sumF (w * X)) M x) (ap2 (sumF (w * monus one X)) M x)) N) := by
  have hXb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶ le (inst2 X (var 0) (Syn.shift x)) one) :=
    .allI (.impI hX.allOpen.wk)
  have hX' : Γ.map Fm.shift ⊢[PRAAx] Fm.all (le (inst2 X (var 0) (Syn.shift (Syn.shift x))) one) := by
    simpa [Fm.shift, Syn.shift, Syn.subst_subst] using hX.shift
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by simpa [Fm.shift, Syn.shift] using hM.shift
  have hXb' : Γ.map Fm.shift ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (Syn.shift M)) ⟶
      le (inst2 X (var 0) (Syn.shift (Syn.shift x))) one) :=
    .allI (.impI hX'.allOpen.wk)
  -- The count is at most `N`.
  have hr : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (pw M N)) ⟶
      lt (inst2 (SB X) (var 0) (Syn.shift (pairT N (pairT M x)))) (Syn.shift (succ N))) := by
    refine .allI (.impI ?_)
    simp only [shift_pairT]
    have hs : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
    rw [hs]
    refine lt_congr (SB_at X _ _ _ _).eqSymm (.eqRefl _) ?_
    exact (succ_monus_succ _ _).eqTrans (Sr_le X hX'.wk)
  refine (Histogram.lotus_bounded (TB w) (SB X) gB hr).eqTrans ?_
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  rw [Lotus.inst2_rB]
  let Δ := lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift
  have sy : Δ ⊢[PRAAx] sndT (pairT (pw (Syn.shift M) (Syn.shift N)) (pairT (Syn.shift N) (pairT (Syn.shift M) (Syn.shift x)))) ≐
      pairT (Syn.shift N) (pairT (Syn.shift M) (Syn.shift x)) := snd_pair _ _
  have fy : Δ ⊢[PRAAx] fstT (pairT (pw (Syn.shift M) (Syn.shift N)) (pairT (Syn.shift N) (pairT (Syn.shift M) (Syn.shift x)))) ≐
      pw (Syn.shift M) (Syn.shift N) := fst_pair _ _
  have hpw : Syn.shift (pw M N) = pw (Syn.shift M) (Syn.shift N) := by simp [Syn.shift]
  have ha : Syn.shift (ap2 (sumF (w * X)) M x) = ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  have hc : Syn.shift (ap2 (sumF (w * monus one X)) M x) = ap2 (sumF (w * monus one X)) (Syn.shift M) (Syn.shift x) := by
    simp [Syn.shift]
  rw [hpw, ha, hc]
  have cl := count_law (Γ := Δ) w X (k := var 0) (r := Syn.shift N) hM'.wk hXb'.wk
  have gL : inst2 gB (var 0) (sndT (pairT (pw (Syn.shift M) (Syn.shift N)) (pairT (Syn.shift N) (pairT (Syn.shift M) (Syn.shift x))))) =
      Expectation.geI (succ (half (fstT (sndT (pairT (pw (Syn.shift M) (Syn.shift N))
        (pairT (Syn.shift N) (pairT (Syn.shift M) (Syn.shift x)))))))) (var 0) := by simp [inst2]
  have hR : inst2 hB (var 0) (pairT (pairT (ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x))
      (ap2 (sumF (w * monus one X)) (Syn.shift M) (Syn.shift x))) (Syn.shift N)) =
      Expectation.geI (succ (half (sndT (pairT (pairT (ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x))
        (ap2 (sumF (w * monus one X)) (Syn.shift M) (Syn.shift x))) (Syn.shift N))))) (var 0) *
      G (fstT (fstT (pairT (pairT (ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x))
        (ap2 (sumF (w * monus one X)) (Syn.shift M) (Syn.shift x))) (Syn.shift N))))
        (sndT (fstT (pairT (pairT (ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x))
        (ap2 (sumF (w * monus one X)) (Syn.shift M) (Syn.shift x))) (Syn.shift N))))
        (sndT (pairT (pairT (ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x))
        (ap2 (sumF (w * monus one X)) (Syn.shift M) (Syn.shift x))) (Syn.shift N))) (var 0) := by simp [inst2]
  rw [gL, hR]
  have nN : Δ ⊢[PRAAx] fstT (sndT (pairT (pw (Syn.shift M) (Syn.shift N)) (pairT (Syn.shift N) (pairT (Syn.shift M) (Syn.shift x))))) ≐
      Syn.shift N := (congrFst sy).eqTrans (fst_pair _ _)
  have pf : Δ ⊢[PRAAx] pairT (pairT (ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x))
      (ap2 (sumF (w * monus one X)) (Syn.shift M) (Syn.shift x))) (Syn.shift N) ≐
      pairT (pairT (ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x))
      (ap2 (sumF (w * monus one X)) (Syn.shift M) (Syn.shift x))) (Syn.shift N) := .eqRefl _
  have s2 : Δ ⊢[PRAAx] sndT (pairT (pairT (ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x))
      (ap2 (sumF (w * monus one X)) (Syn.shift M) (Syn.shift x))) (Syn.shift N)) ≐ Syn.shift N := snd_pair _ _
  have f2 : Δ ⊢[PRAAx] fstT (pairT (pairT (ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x))
      (ap2 (sumF (w * monus one X)) (Syn.shift M) (Syn.shift x))) (Syn.shift N)) ≐
      pairT (ap2 (sumF (w * X)) (Syn.shift M) (Syn.shift x)) (ap2 (sumF (w * monus one X)) (Syn.shift M) (Syn.shift x)) :=
    fst_pair _ _
  have geC : ∀ {u v : PTm (n + 1)}, (Δ ⊢[PRAAx] u ≐ v) →
      (Δ ⊢[PRAAx] Expectation.geI (succ (half u)) (var 0) ≐ Expectation.geI (succ (half v)) (var 0)) :=
    fun h => congrMonus (.eqRefl _) (congrMonus (congrSucc (congrAp1 _ h)) (.eqRefl _))
  refine congrMul ((geC nN).eqTrans (geC s2).eqSymm) ?_
  refine (congrAp2 _ fy (congrPairT (.eqRefl _) sy)).eqTrans (cl.eqTrans ?_)
  exact G_congr ((congrFst f2).eqTrans (fst_pair _ _)).eqSymm ((congrSnd f2).eqTrans (snd_pair _ _)).eqSymm s2.eqSymm (.eqRefl _)

end Count

end LeanProofs.IPRA.Probability.SampleMedian
