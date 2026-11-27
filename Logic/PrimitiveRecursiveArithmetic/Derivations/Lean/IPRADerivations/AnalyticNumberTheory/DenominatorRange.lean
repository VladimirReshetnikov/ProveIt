import IPRADerivations.AnalyticNumberTheory.DenominatorPrimeStep
import IPRADerivations.AnalyticNumberTheory.LcmBridgeTransfer

/-!
# The comparison `S_a ≤ G_a` on a whole range, one prime at a time

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, the proof of the
denominator bound `eq:sieve-denominator`.

`DenominatorPrimeStep.prime_step` passes from the ranges `t` (for `a`) and `⌊t/p⌋` (for `a p`) to the range `t`
(for `a p`). Here it is iterated over the range. The statement "`S_a(t) ≤ G_a(t)` for every `t ≤ z`" is the
quantifier-free equation

    C_z(a) = ∑_{t ≤ z} (S_a(t) ∸ G_a(t)) = 0                                       (`Cz`),

and for a prime `p` with `gcd(p, a) = 1`:

    C_z(a) = 0   gives   C_z(a p) = 0                                              (**`range_step`**).

The proof is a course-of-values induction on the range, written as the ordinary induction on `N` for
`∑_{t < N} [t ≤ z] (S_{ap}(t) ∸ G_{ap}(t)) = 0`: the term at `N` uses the term at `⌊N/p⌋ < N` of the same sum
(`Core.sum_zero_elim`) and the term at `N` of `C_z(a)`.

* `VaB`, `Cz`, `Va_at`; `WB`, `W_at`: the two bodies;
* `quo_lt`: `⌊N/p⌋ < N` for `N ≥ 1`, `p ≥ 2`;
* `W_succ`: the step; `rng_open`, `range_all`: the induction;
* **`range_step`**; `le_of_Cz`: `C_z(a) = 0` gives `S_a(t) ≤ G_a(t)` for `t ≤ z`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.DenominatorRange

open_ipra exports
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (subst_isP one_le_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (Sm gB Sm_succ term_zero le_zero_of)
open LeanProofs.IPRA.AnalyticNumberTheory.TotientSumStep (Gs GtB)
open LeanProofs.IPRA.AnalyticNumberTheory.DenominatorPrimeStep (prime_step quo_le)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeTransfer (inst2_mul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The violation bodies -/

/-- `S_a(t) ∸ G_a(t)`, over `0 = t`, `1 = ⟨a, ⟨L, z⟩⟩`. -/
abbrev VaB : PTm 2 :=
  monus (ap2 (sumF gB) (succ (var 0))
      (pairT (fstT (var 1)) (pairT (fstT (sndT (var 1))) (fact (sndT (sndT (var 1)))))))
    (ap2 (sumF GtB) (succ (var 0)) (pairT (fstT (var 1)) (sndT (sndT (var 1)))))

theorem inst2_VaB (t y : PTm n) : inst2 VaB t y =
    monus (ap2 (sumF gB) (succ t) (pairT (fstT y) (pairT (fstT (sndT y)) (fact (sndT (sndT y))))))
      (ap2 (sumF GtB) (succ t) (pairT (fstT y) (sndT (sndT y)))) := by
  simp only [inst2, PTm.subst_monus, subst_ap2, subst_pairT, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

/-- The parameter `⟨a, ⟨L, z⟩⟩`. -/
abbrev P3 (a L z : PTm n) : PTm n := pairT a (pairT L z)

theorem P3_L (a L z : PTm n) : Γ ⊢[PRAAx] fstT (sndT (P3 a L z)) ≐ L :=
  (congrFst (snd_pair a (pairT L z))).eqTrans (fst_pair L z)

theorem P3_z (a L z : PTm n) : Γ ⊢[PRAAx] sndT (sndT (P3 a L z)) ≐ z :=
  (congrSnd (snd_pair a (pairT L z))).eqTrans (snd_pair L z)

theorem Va_at (t a L z : PTm n) :
    Γ ⊢[PRAAx] inst2 VaB t (P3 a L z) ≐ monus (Sm a L (fact z) (succ t)) (Gs a z (succ t)) := by
  rw [inst2_VaB]
  have f1 : Γ ⊢[PRAAx] fstT (P3 a L z) ≐ a := fst_pair _ _
  exact congrMonus
    (congrAp2 (sumF gB) (.eqRefl _)
      (congrPairT f1 (congrPairT (P3_L a L z) (congrAp2 factF (P3_z a L z) (.eqRefl _)))))
    (congrAp2 (sumF GtB) (.eqRefl _) (congrPairT f1 (P3_z a L z)))

/-- `C_z(a) = ∑_{t ≤ z} (S_a(t) ∸ G_a(t))`. -/
abbrev Cz (a L z : PTm n) : PTm n := ap2 (sumF VaB) (succ z) (P3 a L z)

/-- `C_z(a) = 0` gives `S_a(t) ≤ G_a(t)` for `t ≤ z`. -/
theorem le_of_Cz {a L z t : PTm n} (hA : Γ ⊢[PRAAx] Cz a L z ≐ zero) (ht : Γ ⊢[PRAAx] le t z) :
    Γ ⊢[PRAAx] le (Sm a L (fact z) (succ t)) (Gs a z (succ t)) :=
  (Va_at t a L z).eqSymm.eqTrans (sum_zero_elim VaB hA ((succ_monus_succ _ _).eqTrans ht))

/-- `[t ≤ z] (S_a(t) ∸ G_a(t))`, over `0 = t`, `1 = ⟨a, ⟨L, z⟩⟩`. -/
abbrev WB : PTm 2 := monus one (monus (var 0) (sndT (sndT (var 1)))) * VaB

theorem inst2_WB (t y : PTm n) :
    inst2 WB t y = monus one (monus t (sndT (sndT y))) * inst2 VaB t y := by
  have e : inst2 (monus one (monus (var 0) (sndT (sndT (var 1)))) : PTm 2) t y =
      monus one (monus t (sndT (sndT y))) := by
    simp only [inst2, PTm.subst_monus, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
      ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
  rw [inst2_mul, e]

theorem W_at (t a L z : PTm n) :
    Γ ⊢[PRAAx] inst2 WB t (P3 a L z) ≐
      monus one (monus t z) * monus (Sm a L (fact z) (succ t)) (Gs a z (succ t)) := by
  rw [inst2_WB]
  exact congrMul (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (P3_z a L z))) (Va_at t a L z)

/-! ## Small facts -/

theorem leI_one {t z : PTm n} (h : Γ ⊢[PRAAx] le t z) : Γ ⊢[PRAAx] monus one (monus t z) ≐ one :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_zero one)

theorem lt_alg {t z d : PTm n} (e : Γ ⊢[PRAAx] t ≐ succ z + d) : Γ ⊢[PRAAx] t ≐ z + succ d := by
  ipra_lc natEq e

theorem leI_zero {t z : PTm n} (h : Γ ⊢[PRAAx] lt z t) : Γ ⊢[PRAAx] monus one (monus t z) ≐ zero := by
  have m : Γ ⊢[PRAAx] monus t z ≐ succ (monus t (succ z)) := monus_of_eq (lt_alg (eq_add_of_le h))
  exact (congrMonus (.eqRefl _) m).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _))

/-- `⌊N/p⌋ < N` for `N ≥ 1` and `p ≥ 2`. -/
theorem quo_lt {N p : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hp2 : Γ ⊢[PRAAx] le two p) :
    Γ ⊢[PRAAx] lt (quo N p) N := by
  apply Division.quo_lt_of_lt_mul (p_pos hp2)
  change Γ ⊢[PRAAx] le (succ N) (p * N)
  ipra_le sl hp2 * 𝔞 N + sl (one_le_pos hN)

theorem S_zero (a L F : PTm n) : Γ ⊢[PRAAx] Sm a L F (succ zero) ≐ zero :=
  (Sm_succ a L F zero).eqTrans ((congrAdd (sum_zero gB _) (term_zero (.eqRefl _))).eqTrans (zero_add zero))

theorem one_mul_zero {b X : PTm n} (hb : Γ ⊢[PRAAx] b ≐ one) (h : Γ ⊢[PRAAx] b * X ≐ zero) :
    Γ ⊢[PRAAx] X ≐ zero := by
  ipra_lc natEq h - 𝔞 X * natEq hb

/-! ## The step of the range induction -/

/-- If the terms below `N` vanish, the term at `N` vanishes. -/
theorem W_succ {p a L z N : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hc : Γ ⊢[PRAAx] gcd p a ≐ one)
    (hA : Γ ⊢[PRAAx] Cz a L z ≐ zero)
    (ih : Γ ⊢[PRAAx] ap2 (sumF WB) N (P3 (a * p) L z) ≐ zero) :
    Γ ⊢[PRAAx] ap2 (sumF WB) (succ N) (P3 (a * p) L z) ≐ zero := by
  have hp2 := prime_two hp
  have hp1 := p_pos hp2
  refine (sum_succ' WB N _).eqTrans ((congrAdd ih ?_).eqTrans (zero_add zero))
  refine (W_at N (a * p) L z).eqTrans ?_
  refine .orE (lt_or_le z N) ?_ ?_
  · exact zero_mul_l (leI_zero Prf.hyp0) _
  · let C : List (Fm PTm n) := le N z :: Γ
    have hNz : C ⊢[PRAAx] le N z := Prf.hyp0
    have h2 := le_of_Cz hA.wk hNz
    have hqz : C ⊢[PRAAx] le (quo N p) z := le_trans (quo_le hp1.wk N) hNz
    have h3 : C ⊢[PRAAx] le (Sm (a * p) L (fact z) (succ (quo N p))) (Gs (a * p) z (succ (quo N p))) := by
      refine .orE (zero_or_succ N) ?_ ?_
      · have h0 : ((N ≐ zero) :: C) ⊢[PRAAx] N ≐ zero := Prf.hyp0
        have q0 : ((N ≐ zero) :: C) ⊢[PRAAx] quo N p ≐ zero :=
          le_antisymm (le_congr (.eqRefl _) h0 (quo_le hp1.wk.wk N)) (zero_le _)
        exact le_zero_of ((congrAp2 (sumF gB) (congrSucc q0) (.eqRefl _)).eqTrans (S_zero _ _ _))
      · have hN : ((N ≐ succ (pred N)) :: C) ⊢[PRAAx] N ≐ succ (pred N) := Prf.hyp0
        have t := sum_zero_elim WB ih.wk.wk (quo_lt hN hp2.wk.wk)
        have w := (W_at (quo N p) (a * p) L z).eqSymm.eqTrans t
        exact one_mul_zero (leI_one hqz.wk) w
    exact (congrMul (.eqRefl _) (prime_step hp.wk hc.wk hNz h2 h3)).eqTrans (mul_zero _)

/-! ## The induction -/

/-- Variables: `0 = N`, `1 = p`, `2 = a`, `3 = L`, `4 = z`. -/
abbrev rngF : Fm PTm 5 :=
  (isP (var 1) ≐ one) ⟶ (gcd (var 1) (var 2) ≐ one) ⟶
    (ap2 (sumF VaB) (succ (var 4)) (pairT (var 2) (pairT (var 3) (var 4))) ≐ zero) ⟶
    (ap2 (sumF WB) (var 0) (pairT (var 2 * var 1) (pairT (var 3) (var 4))) ≐ zero)

theorem rng_open : ([] : List (Fm PTm 5)) ⊢[PRAAx] rngF := by
  refine ind _ ⟨trivial, trivial, trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_isP, Syn.subst_var, Syn.inst_one]
    simp only [subst_ex2, subst_ap2, subst_pairT, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      inst_two, inst_three, inst_four, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (.impI (sum_zero WB _)))
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_isP, Syn.subst_var, repl_one]
    simp only [subst_ex2, subst_ap2, subst_pairT, PTm.subst_mul, Syn.subst_var, Syn.repl_zero, repl_one,
      repl_two, repl_three, repl_four, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (.impI (.impI (W_succ (prime_of_isP hyp2) Prf.hyp1 Prf.hyp0
      (.impE (.impE (.impE (Prf.hyp0 (Γ := []) (φ := rngF)).wk.wk.wk hyp2) Prf.hyp1) Prf.hyp0))))

/-- All the terms vanish. -/
theorem range_all {p a L z : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hc : Γ ⊢[PRAAx] gcd p a ≐ one)
    (hA : Γ ⊢[PRAAx] Cz a L z ≐ zero) (N : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF WB) N (P3 (a * p) L z) ≐ zero := by
  have i := inst (Γ := Γ) rng_open (![N, p, a, L, z] : Fin 5 → PTm n)
  simp only [rngF, Fm.subst_imp, Fm.subst_eq, subst_isP, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] at i
  simp only [subst_ex2, subst_ap2, subst_pairT, PTm.subst_mul, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at i
  exact .impE (.impE (.impE i (isP_of_prime hp)) hc) hA

theorem one_mul_l {b X : PTm n} (hb : Γ ⊢[PRAAx] b ≐ one) : Γ ⊢[PRAAx] X ≐ b * X := by
  ipra_lc -𝔞 X * natEq hb

/-- **The range step**: `C_z(a) = 0` gives `C_z(a p) = 0`, for a prime `p` with `gcd(p, a) = 1`. -/
theorem range_step {p a L z : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hc : Γ ⊢[PRAAx] gcd p a ≐ one)
    (hA : Γ ⊢[PRAAx] Cz a L z ≐ zero) : Γ ⊢[PRAAx] Cz (a * p) L z ≐ zero := by
  refine .eqTrans ?_ (range_all hp hc hA (succ z))
  refine sum_congr_bounded VaB WB (P3 (a * p) L z) (P3 (a * p) L z) (succ z) (.allI (.impI ?_))
  rw [inst2_WB]
  have sz : Syn.shift (P3 (a * p) L z) = P3 (Syn.shift (a * p)) (Syn.shift L) (Syn.shift z) := by
    simp [Syn.shift]
  have ss : Syn.shift (succ z) = succ (Syn.shift z) := by simp [Syn.shift]
  rw [sz]
  have hlt : (lt (var 0) (Syn.shift (succ z)) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (var 0) (succ (Syn.shift z)) := by
    have h0 : (lt (var 0) (Syn.shift (succ z)) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (var 0) (Syn.shift (succ z)) := Prf.hyp0
    rw [ss] at h0
    exact h0
  have hle : (lt (var 0) (Syn.shift (succ z)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift z) :=
    (succ_monus_succ _ _).eqSymm.eqTrans hlt
  exact one_mul_l ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (P3_z _ _ _))).eqTrans (leI_one hle))

end LeanProofs.IPRA.AnalyticNumberTheory.DenominatorRange
