import IPRADerivations.Combinatorics.Stirling
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Core.Fubini
import IPRADerivations.Core.LinearCombination

/-!
# Vandermonde's identity

`∑_{k ≤ r} C(m, k) C(n, r − k) = C(m + n, r)`, the step used twice in the square-sum theorem and
in the Narayana / hypergeometric evaluation of `combinatorics/catalan_numbers_ipra_2026-11-16`
((2.13)–(2.14), "Square sum" (2.20)).

The exact coefficient `binom m k` of `Combinatorics/Binomial` is meaningful only for `k ≤ m`, so
the identity is stated for the guarded coefficient `gb m k = [k ≤ m] · C(m, k)`, which vanishes
for `k > m` (the packet's convention).

* `gb_zero`, `gb_self`, `gb_above`: `C(m, 0) = C(m, m) = 1`, and `C(m, k) = 0` for `k > m`;
* `gb_pascal`: `C(m + 1, k + 1) = C(m, k + 1) + C(m, k)` for every `k`;
* `vs_succ_r`: the convolution with its first term split off;
* `vs_step`: `V(m + 1, n, r + 1) = V(m, n, r + 1) + V(m, n, r)`;
* `vandermonde`: the identity for all `m, n, r`. The induction is on `m`, and its formula is that
  the violation count over `r < R` vanishes, because the step at `r` uses the hypothesis at `r` and
  at `r − 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.Vandermonde

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_zero' binom_self' pascal_at)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrBinom)
open LeanProofs.IPRA.Combinatorics.Stirling (gle gle_of_le gle_above)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (eq_of_viol viol_of_eq)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The guarded binomial coefficient -/

/-- `C(m, k)`, zero for `k > m`. -/
abbrev gb {n : ℕ} (m k : PTm n) : PTm n := gle k m * binom m k

theorem congrGb {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] gb a b ≐ gb a' b' :=
  congrMul (congrMonus (.eqRefl _) (congrMonus hb ha)) (congrBinom ha hb)

theorem gb_zero (m : PTm n) : Γ ⊢[PRAAx] gb m zero ≐ one :=
  (congrMul (gle_of_le (zero_le m)) (binom_zero' m)).eqTrans (one_mul one)

theorem gb_self (m : PTm n) : Γ ⊢[PRAAx] gb m m ≐ one :=
  (congrMul (gle_of_le (le_refl m)) (binom_self' m)).eqTrans (one_mul one)

theorem gb_above {m k : PTm n} (h : Γ ⊢[PRAAx] le (succ m) k) : Γ ⊢[PRAAx] gb m k ≐ zero :=
  (congrMul (gle_above h) (.eqRefl _)).eqTrans (zero_mul _)

/-- Pascal's rule for every `k`. -/
theorem gb_pascal (m k : PTm n) : Γ ⊢[PRAAx] gb (succ m) (succ k) ≐ gb m (succ k) + gb m k := by
  refine .orE (lt_or_le k m) ?_ ?_
  · have hk : (lt k m :: Γ) ⊢[PRAAx] le (succ k) m := Prf.hyp0
    ipra_lc 𝔞(binom (succ m) (succ k)) * natEq (gle_of_le (le_trans hk (le_succ_self m)) : (lt k m :: Γ) ⊢[PRAAx] gle (succ k) (succ m) ≐ one) -
      𝔞(binom m (succ k)) * natEq (gle_of_le hk) - 𝔞(binom m k) * natEq (gle_of_le (le_trans (le_succ_self k) hk)) +
      natEq (pascal_at (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := lt k m)))
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · have h : (lt m k :: le m k :: Γ) ⊢[PRAAx] le (succ m) k := Prf.hyp0
      have z₁ := gb_above ((succ_monus_succ _ _).eqTrans h : (lt m k :: le m k :: Γ) ⊢[PRAAx]
        le (succ (succ m)) (succ k))
      have z₂ := gb_above (le_trans h (le_succ_self k))
      have z₃ := gb_above h
      exact z₁.eqTrans ((add_zero _).eqSymm.eqTrans (congrAdd z₂ z₃).eqSymm)
    · have e : ((m ≐ k) :: le m k :: Γ) ⊢[PRAAx] m ≐ k := Prf.hyp0
      have o₁ := (congrGb (congrSucc e) (.eqRefl _)).eqTrans (gb_self (succ k))
      have z := gb_above (le_congr (.eqRefl _) (congrSucc e) (le_refl (succ m)))
      have o₂ := (congrGb e (.eqRefl _)).eqTrans (gb_self k)
      exact o₁.eqTrans ((zero_add _).eqSymm.eqTrans (congrAdd z o₂).eqSymm)

/-! ## The convolution; parameter `⟨⟨m, n⟩, r⟩` -/

/-- `C(m, k) C(n, r − k)`. -/
abbrev vsB : PTm 2 :=
  gb (fstT (fstT (var 1))) (var 0) * gb (sndT (fstT (var 1))) (monus (sndT (var 1)) (var 0))
/-- `C(m, k + 1) C(n, r − k)`. -/
abbrev sB : PTm 2 :=
  gb (fstT (fstT (var 1))) (succ (var 0)) * gb (sndT (fstT (var 1))) (monus (sndT (var 1)) (var 0))

/-- `V(m, n, r) = ∑_{k ≤ r} C(m, k) C(n, r − k)`. -/
abbrev VS {n : ℕ} (m nn r : PTm n) : PTm n := ap2 (sumF vsB) (succ r) (pairT (pairT m nn) r)

theorem inst2_vs (k y : PTm n) :
    inst2 vsB k y = gb (fstT (fstT y)) k * gb (sndT (fstT y)) (monus (sndT y) k) := by simp [inst2]
theorem inst2_s (k y : PTm n) :
    inst2 sB k y = gb (fstT (fstT y)) (succ k) * gb (sndT (fstT y)) (monus (sndT y) k) := by simp [inst2]

theorem ff_p (m nn r : PTm n) : Γ ⊢[PRAAx] fstT (fstT (pairT (pairT m nn) r)) ≐ m :=
  (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
theorem sf_p (m nn r : PTm n) : Γ ⊢[PRAAx] sndT (fstT (pairT (pairT m nn) r)) ≐ nn :=
  (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)

theorem vs_at (k m nn r : PTm n) :
    Γ ⊢[PRAAx] inst2 vsB k (pairT (pairT m nn) r) ≐ gb m k * gb nn (monus r k) := by
  rw [inst2_vs]
  exact congrMul (congrGb (ff_p _ _ _) (.eqRefl _)) (congrGb (sf_p _ _ _) (congrMonus (snd_pair _ _) (.eqRefl _)))

theorem s_at (k m nn r : PTm n) :
    Γ ⊢[PRAAx] inst2 sB k (pairT (pairT m nn) r) ≐ gb m (succ k) * gb nn (monus r k) := by
  rw [inst2_s]
  exact congrMul (congrGb (ff_p _ _ _) (.eqRefl _)) (congrGb (sf_p _ _ _) (congrMonus (snd_pair _ _) (.eqRefl _)))

theorem congrVS {m m' nn nn' r r' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m') (hn : Γ ⊢[PRAAx] nn ≐ nn')
    (hr : Γ ⊢[PRAAx] r ≐ r') : Γ ⊢[PRAAx] VS m nn r ≐ VS m' nn' r' :=
  congrAp2 (sumF vsB) (congrSucc hr) (congrPairT (congrPairT hm hn) hr)

theorem shift_y (m nn r : PTm n) :
    Syn.shift (pairT (pairT m nn) r) = pairT (pairT (Syn.shift m) (Syn.shift nn)) (Syn.shift r) := by
  simp [Syn.shift]

theorem sh_pt (k m nn r : PTm n) :
    Γ ⊢[PRAAx] inst2 (shiftBody vsB) k (pairT (pairT m nn) (succ r)) ≐ inst2 sB k (pairT (pairT m nn) r) := by
  rw [inst2_shiftBody]
  exact (vs_at _ _ _ _).eqTrans ((congrMul (.eqRefl _) (congrGb (.eqRefl _) (succ_monus_succ _ _))).eqTrans
    (s_at _ _ _ _).eqSymm)

/-- `V(m, n, r + 1) = C(n, r + 1) + ∑_{k ≤ r} C(m, k + 1) C(n, r − k)`. -/
theorem vs_succ_r (m nn r : PTm n) :
    Γ ⊢[PRAAx] VS m nn (succ r) ≐ gb nn (succ r) + ap2 (sumF sB) (succ r) (pairT (pairT m nn) r) := by
  refine (sum_shift vsB (succ r) _).eqTrans (congrAdd ?_ ?_)
  · exact (vs_at _ _ _ _).eqTrans ((congrMul (gb_zero m) (congrGb (.eqRefl _) (monus_zero _))).eqTrans
      (one_mul _))
  · refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_y, shift_y]
    exact sh_pt _ _ _ _

theorem pas_pt (k m nn r : PTm n) :
    Γ ⊢[PRAAx] inst2 sB k (pairT (pairT (succ m) nn) r) ≐ inst2 (addBody sB vsB) k (pairT (pairT m nn) r) := by
  rw [inst2_addBody]
  refine (s_at _ _ _ _).eqTrans (.eqTrans ?_ (congrAdd (s_at _ _ _ _) (vs_at _ _ _ _)).eqSymm)
  ipra_lc 𝔞(gle (monus r k) nn) * 𝔞(binom nn (monus r k)) * natEq (gb_pascal (Γ := Γ) m k)

/-- `V(m + 1, n, r + 1) = C(m + n + 1, r + 1)` from the identity at `(m, r + 1)` and `(m, r)`. -/
theorem vs_step {m nn r : PTm n} (h₁ : Γ ⊢[PRAAx] VS m nn (succ r) ≐ gb (m + nn) (succ r))
    (h₀ : Γ ⊢[PRAAx] VS m nn r ≐ gb (m + nn) r) :
    Γ ⊢[PRAAx] VS (succ m) nn (succ r) ≐ gb (succ m + nn) (succ r) := by
  have A := natEq (vs_succ_r (Γ := Γ) (succ m) nn r)
  have B' : Γ ⊢[PRAAx] ap2 (sumF sB) (succ r) (pairT (pairT (succ m) nn) r) ≐
      ap2 (sumF (addBody sB vsB)) (succ r) (pairT (pairT m nn) r) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_y, shift_y]
    exact pas_pt _ _ _ _
  have B := natEq B'
  have C := natEq (sum_add (Γ := Γ) sB vsB (succ r) (pairT (pairT m nn) r))
  have D := natEq (vs_succ_r (Γ := Γ) m nn r)
  have e₁ := natEq h₁; have e₀ := natEq h₀
  have P := natEq (gb_pascal (Γ := Γ) (m + nn) r)
  have Q := natEq (congrGb (Γ := Γ) (succ_add m nn) (.eqRefl (succ r)))
  apply deriveNat; ipra_simps
  linear_combination A + B + C - D + e₁ + e₀ - P - Q

theorem vs_r0 (m nn : PTm n) : Γ ⊢[PRAAx] VS m nn zero ≐ gb (m + nn) zero := by
  ipra_lc natEq (sum_succ' (Γ := Γ) vsB zero (pairT (pairT m nn) zero)) +
    natEq (sum_zero (Γ := Γ) vsB (pairT (pairT m nn) zero)) +
    natEq ((vs_at (Γ := Γ) zero m nn zero).eqTrans ((congrMul (gb_zero m) ((congrGb (.eqRefl nn) (monus_zero zero)).eqTrans (gb_zero nn))).eqTrans (one_mul one))) -
    natEq (gb_zero (Γ := Γ) (m + nn))

/-! ## The base `m = 0` -/

abbrev zB : PTm 2 := zero

theorem inst2_z (i x : PTm n) : inst2 zB i x = zero := by simp [inst2]

theorem zsum (N x : PTm n) : Γ ⊢[PRAAx] ap2 (sumF zB) N x ≐ zero :=
  sum_zero_of_all zB x (.allI (by rw [inst2_z]; exact .eqRefl _)) N

theorem vs_base (nn r : PTm n) : Γ ⊢[PRAAx] VS zero nn r ≐ gb (zero + nn) r := by
  refine .orE (zero_or_succ r) ?_ ?_
  · have e : ((r ≐ zero) :: Γ) ⊢[PRAAx] r ≐ zero := Prf.hyp0
    exact (congrVS (.eqRefl _) (.eqRefl _) e).eqTrans ((vs_r0 _ _).eqTrans (congrGb (.eqRefl _) e.eqSymm))
  · have e : ((r ≐ succ (pred r)) :: Γ) ⊢[PRAAx] r ≐ succ (pred r) := Prf.hyp0
    refine (congrVS (.eqRefl _) (.eqRefl _) e).eqTrans ((vs_succ_r _ _ _).eqTrans ?_)
    have zs : ((r ≐ succ (pred r)) :: Γ) ⊢[PRAAx]
        ap2 (sumF sB) (succ (pred r)) (pairT (pairT zero nn) (pred r)) ≐ zero := by
      refine (sum_congr_bounded sB zB (pairT (pairT zero nn) (pred r)) (pairT (pairT zero nn) (pred r))
        (succ (pred r)) (.allI (.impI ?_))).eqTrans (zsum _ _)
      have ez : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
      rw [shift_y, inst2_z, ez]
      refine (s_at _ _ _ _).eqTrans ((congrMul (gb_above ?_) (.eqRefl _)).eqTrans (zero_mul _))
      exact (succ_monus_succ _ _).eqTrans (zero_le _)
    refine (congrAdd (.eqRefl _) zs).eqTrans ((add_zero _).eqTrans ?_)
    exact congrGb (zero_add _).eqSymm e.eqSymm

/-! ## The induction on `m` -/

/-- `1 ∸ [V(m, n, r) = C(m + n, r)]`, over `0 = r`, `1 = ⟨m, n⟩`. -/
abbrev violB : PTm 2 :=
  monus one (eqb (VS (fstT (var 1)) (sndT (var 1)) (var 0)) (gb (fstT (var 1) + sndT (var 1)) (var 0)))

theorem inst2_viol (r y : PTm n) :
    inst2 violB r y = monus one (eqb (VS (fstT y) (sndT y) r) (gb (fstT y + sndT y) r)) := by simp [inst2]

theorem viol_at (r m nn : PTm n) :
    Γ ⊢[PRAAx] inst2 violB r (pairT m nn) ≐ monus one (eqb (VS m nn r) (gb (m + nn) r)) := by
  rw [inst2_viol]
  exact congrMonus (.eqRefl _) (AnalyticNumberTheory.Euler.congrEqb
    (congrVS (fst_pair _ _) (snd_pair _ _) (.eqRefl _))
    (congrGb (congrAdd (fst_pair _ _) (snd_pair _ _)) (.eqRefl _)))

theorem eq_at {m nn s R : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF violB) R (pairT m nn) ≐ zero)
    (hs : Γ ⊢[PRAAx] lt s R) : Γ ⊢[PRAAx] VS m nn s ≐ gb (m + nn) s :=
  eq_of_viol ((viol_at s m nn).eqSymm.eqTrans (sum_zero_elim violB ih hs))

theorem viol_point {m nn r R : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF violB) R (pairT m nn) ≐ zero)
    (hr : Γ ⊢[PRAAx] lt r R) : Γ ⊢[PRAAx] inst2 violB r (pairT (succ m) nn) ≐ zero := by
  refine (viol_at r (succ m) nn).eqTrans (viol_of_eq ?_)
  refine .orE (zero_or_succ r) ?_ ?_
  · have e : ((r ≐ zero) :: Γ) ⊢[PRAAx] r ≐ zero := Prf.hyp0
    exact (congrVS (.eqRefl _) (.eqRefl _) e).eqTrans ((vs_r0 _ _).eqTrans (congrGb (.eqRefl _) e.eqSymm))
  · have e : ((r ≐ succ (pred r)) :: Γ) ⊢[PRAAx] r ≐ succ (pred r) := Prf.hyp0
    have l₁ : ((r ≐ succ (pred r)) :: Γ) ⊢[PRAAx] lt (succ (pred r)) R := lt_congr e (.eqRefl _) hr.wk
    have l₀ : ((r ≐ succ (pred r)) :: Γ) ⊢[PRAAx] lt (pred r) R := le_trans (le_succ_self _) l₁
    have st := vs_step (eq_at ih.wk l₁) (eq_at ih.wk l₀)
    exact (congrVS (.eqRefl _) (.eqRefl _) e).eqTrans (st.eqTrans (congrGb (.eqRefl _) e.eqSymm))

theorem viol_step {m nn R : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF violB) R (pairT m nn) ≐ zero) :
    Γ ⊢[PRAAx] ap2 (sumF violB) R (pairT (succ m) nn) ≐ zero := by
  refine (sum_congr_bounded violB zB (pairT (succ m) nn) (pairT m nn) R (.allI (.impI ?_))).eqTrans (zsum _ _)
  have ih' : Γ.map Fm.shift ⊢[PRAAx]
      ap2 (sumF violB) (Syn.shift R) (pairT (Syn.shift m) (Syn.shift nn)) ≐ zero := by
    simpa [Fm.shift, Syn.shift] using ih.shift
  have e₁ : Syn.shift (pairT (succ m) nn) = pairT (succ (Syn.shift m)) (Syn.shift nn) := by simp [Syn.shift]
  rw [e₁, inst2_z]
  exact viol_point ih'.wk Prf.hyp0

theorem viol_base (nn R : PTm n) : Γ ⊢[PRAAx] ap2 (sumF violB) R (pairT zero nn) ≐ zero := by
  refine (sum_congr_bounded violB zB (pairT zero nn) (pairT zero nn) R (.allI (.impI ?_))).eqTrans (zsum _ _)
  have e₁ : Syn.shift (pairT (zero : PTm n) nn) = pairT zero (Syn.shift nn) := by simp [Syn.shift]
  rw [e₁, inst2_z]
  exact (viol_at _ _ _).eqTrans (viol_of_eq (vs_base _ _))

/-- Variables: `0 = m` (induction), `1 = n`, `2 = R`. -/
private abbrev vF : Fm PTm 3 := ap2 (sumF violB) (var 2) (pairT (var 0) (var 1)) ≐ zero

private theorem v₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] vF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact viol_base _ _
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero, repl_one, repl_two,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact viol_step Prf.hyp0

/-- Vandermonde: `∑_{k ≤ r} C(m, k) C(n, r − k) = C(m + n, r)`. -/
theorem vandermonde (m nn r : PTm n) : Γ ⊢[PRAAx] VS m nn r ≐ gb (m + nn) r := by
  have h := inst (Γ := Γ) v₀ (![m, nn, succ r] : Fin 3 → PTm n)
  simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] at h
  exact eq_at h ((succ_monus_succ _ _).eqTrans (le_refl _))

end LeanProofs.IPRA.Combinatorics.Vandermonde
