import IPRADerivations.AnalyticNumberTheory.SymmetricMoment
import IPRADerivations.AnalyticNumberTheory.BlockTests
import IPRADerivations.Core.Header

/-!
# The product test on a whole prefix (`riemann_ipra_prime_criteria_2026-11-20`, `thm:symmetric-prefix`, eq:sym-char)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-uniform.tex`, Theorem
`thm:symmetric-prefix`, test (eq:sym-char) `Π_{s=1}^{U} Π_{i<m} |s + b_i − a_i| > 0`, `U = Σ_{i<m} a_i`: "For the
product test, `a_i ≤ b_i` makes every factor at least `s ≥ 1`. If `a_i > b_i`, its positive difference
`s = a_i − b_i` satisfies `1 ≤ s ≤ a_i ≤ U` and gives a zero factor." Here `|s + b − a|` is `absd (s + b) a`.

* `prod_pos`: a product of factors `≥ 1` is `≥ 1`; `prod_zero_at`: one zero factor makes the product `0`
  ("a product is positive precisely when each factor is positive by the product recursion");
* `inner_pos`, `prod_forward`, `prod_backward`, `sym_char`: `(∀i<m a_i ≤ b_i) ↔ 1 ≤ Π_{t<U} Π_{i<m} |t+1+b_i−a_i|`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SymmetricProduct

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd le_absd_l)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockTests (one_le_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetricPrefix (term_le_sum Below)
open LeanProofs.IPRA.AnalyticNumberTheory.CubeScan (inst2_subst)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (zero_mul_l)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Products of factors -/

theorem inst2_shift (f : PTm 2) (a b : PTm n) :
    Fm.shift (inst2 f a b ≐ zero) = (inst2 f (Syn.shift a) (Syn.shift b) ≐ zero) := by
  simp only [Fm.shift, Fm.subst_eq, inst2_subst f, ConciseIPRA.PTm.subst_zero] <;> rfl

/-- Factors `≥ 1` give a product `≥ 1`. -/
theorem prod_pos {f : PTm 2} {N x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le one (inst2 f (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le one (ap2 (prodF f) N x) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶ le one (ap2 (prodF f) (var 0) (Syn.shift x))) := by
    refine PRA.qfInd _ (by simp [Fm.QF, le_QF]) ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      exact .impI (le_congr (.eqRefl _) (prod_zero f x).eqSymm (le_refl _))
    · simp only [Fm.subst_imp, subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      let Δ : List (Fm PTm (n + 1)) := le (succ (var 0)) (Syn.shift N) ::
        (le (var 0) (Syn.shift N) ⟶ le one (ap2 (prodF f) (var 0) (Syn.shift x))) :: Γ.map Fm.shift
      have hv : Δ ⊢[PRAAx] le (succ (var 0)) (Syn.shift N) := Prf.hyp0
      have ih := Prf.impE (Prf.hyp1 : Δ ⊢[PRAAx] _) (le_trans (le_succ_self _) hv)
      have hf := Prf.impE (h.allOpen.wk.wk : Δ ⊢[PRAAx] _) hv
      have ps : Δ ⊢[PRAAx] ap2 (prodF f) (succ (var 0)) (Syn.shift x) ≐
          ap2 (prodF f) (var 0) (Syn.shift x) * inst2 f (var 0) (Syn.shift x) := prod_succ f (var 0) (Syn.shift x)
      exact le_congr (.eqRefl _) ps.eqSymm (one_le_mul ih hf)
  have a := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at a
  exact .impE a (le_refl _)

/-- One zero factor makes the product zero. -/
theorem prod_zero_at {f : PTm 2} {N x j : PTm n} (hj : Γ ⊢[PRAAx] lt j N)
    (hf : Γ ⊢[PRAAx] inst2 f j x ≐ zero) : Γ ⊢[PRAAx] ap2 (prodF f) N x ≐ zero := by
  have hf' : (Γ.map Fm.shift) ⊢[PRAAx] inst2 f (Syn.shift j) (Syn.shift x) ≐ zero := by
    have a := hf.shift
    rw [inst2_shift] at a
    exact a
  have hall : Γ ⊢[PRAAx] Fm.all (lt (Syn.shift j) (var 0) ⟶ ap2 (prodF f) (var 0) (Syn.shift x) ≐ zero) := by
    refine PRA.qfInd _ (by simp [Fm.QF, le_QF, lt_QF]) ?_ ?_
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      exact .impI (lt_zero_absurd _ Prf.hyp0)
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      let Δ : List (Fm PTm (n + 1)) := lt (Syn.shift j) (succ (var 0)) ::
        (lt (Syn.shift j) (var 0) ⟶ ap2 (prodF f) (var 0) (Syn.shift x) ≐ zero) :: Γ.map Fm.shift
      have hv : Δ ⊢[PRAAx] le (Syn.shift j) (var 0) :=
        (succ_monus_succ _ _).eqSymm.eqTrans (Prf.hyp0 : Δ ⊢[PRAAx] lt (Syn.shift j) (succ (var 0)))
      have ps : Δ ⊢[PRAAx] ap2 (prodF f) (succ (var 0)) (Syn.shift x) ≐
          ap2 (prodF f) (var 0) (Syn.shift x) * inst2 f (var 0) (Syn.shift x) := prod_succ f (var 0) (Syn.shift x)
      refine .orE (lt_or_eq_of_le hv) ?_ ?_
      · have ih := Prf.impE ((Prf.hyp1 : Δ ⊢[PRAAx]
          (lt (Syn.shift j) (var 0) ⟶ ap2 (prodF f) (var 0) (Syn.shift x) ≐ zero)).wk) Prf.hyp0
        exact ps.wk.eqTrans (zero_mul_l ih _)
      · have hfv : ((Syn.shift j ≐ var 0) :: Δ) ⊢[PRAAx] inst2 f (var 0) (Syn.shift x) ≐ zero :=
          (congrInst2 f (Prf.hyp0 : ((Syn.shift j ≐ var 0) :: Δ) ⊢[PRAAx] Syn.shift j ≐ var 0).eqSymm
            (.eqRefl _)).eqTrans hf'.wk.wk.wk
        exact ps.wk.eqTrans ((congrMul (.eqRefl _) hfv).eqTrans (mul_zero _))
  have a := Prf.allE N hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at a
  exact .impE a hj

/-! ## The test -/

variable (aB bB : PTm 2)

/-- The factor `|s + b_i − a_i|` over `0 = i`, `1 = ⟨s, y⟩`. -/
def fB : PTm 2 :=
  absd (fstT (var 1) + Syn.subst ![var 0, sndT (var 1)] bB) (Syn.subst ![var 0, sndT (var 1)] aB)

theorem inst2_fB (i P : PTm n) :
    inst2 (fB aB bB) i P = absd (fstT P + inst2 bB i (sndT P)) (inst2 aB i (sndT P)) := by
  have ha : Syn.subst ![i, P] (Syn.subst ![var 0, sndT (var 1)] aB) = inst2 aB i (sndT P) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  have hb : Syn.subst ![i, P] (Syn.subst ![var 0, sndT (var 1)] bB) = inst2 bB i (sndT P) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, fB, PTm.subst_add, PTm.subst_monus, ha, hb]
  simp

theorem fB_at (i s y : PTm n) :
    Γ ⊢[PRAAx] inst2 (fB aB bB) i (pairT s y) ≐ absd (s + inst2 bB i y) (inst2 aB i y) := by
  rw [inst2_fB]
  have e1 : Γ ⊢[PRAAx] fstT (pairT s y) + inst2 bB i (sndT (pairT s y)) ≐ s + inst2 bB i y :=
    congrAdd (fst_pair _ _) (congrInst2 bB (.eqRefl _) (snd_pair _ _))
  have e2 : Γ ⊢[PRAAx] inst2 aB i (sndT (pairT s y)) ≐ inst2 aB i y := congrInst2 aB (.eqRefl _) (snd_pair _ _)
  exact congrAdd (congrMonus e1 e2) (congrMonus e2 e1)

/-- The inner product `Π_{i<m} |t + 1 + b_i − a_i|` over `0 = t`, `1 = ⟨m, y⟩`. -/
def oB : PTm 2 := ap2 (prodF (fB aB bB)) (fstT (var 1)) (pairT (succ (var 0)) (sndT (var 1)))

theorem oB_at (t m y : PTm n) :
    Γ ⊢[PRAAx] inst2 (oB aB bB) t (pairT m y) ≐ ap2 (prodF (fB aB bB)) m (pairT (succ t) y) := by
  have h : inst2 (oB aB bB) t (pairT m y) =
      ap2 (prodF (fB aB bB)) (fstT (pairT m y)) (pairT (succ t) (sndT (pairT m y))) := by
    simp [inst2, oB]
  rw [h]
  exact congrAp2 (prodF (fB aB bB)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))

/-- The test (eq:sym-char): `1 ≤ Π_{t<U} Π_{i<m} |t + 1 + b_i − a_i|`, `U = Σ_{i<m} a_i`. -/
abbrev ProdTest (m y : PTm n) : Fm PTm n :=
  le one (ap2 (prodF (oB aB bB)) (ap2 (sumF aB) m y) (pairT m y))

theorem below_shift (m y : PTm n) : Fm.shift (Below aB bB m y) = Below aB bB (Syn.shift m) (Syn.shift y) := by
  simp only [Below, Fm.shift, Fm.subst_all, Fm.subst_imp, subst_lt, subst_le, inst2_subst, Syn.subst_var,
    Syn.up_zero, subst_up_shift_pal] <;> rfl

/-- Under the hypothesis every inner product at `s ≥ 1` is `≥ 1`. -/
theorem inner_pos {m y s : PTm n} (hb : Γ ⊢[PRAAx] Below aB bB m y) (hs : Γ ⊢[PRAAx] le one s) :
    Γ ⊢[PRAAx] le one (ap2 (prodF (fB aB bB)) m (pairT s y)) := by
  have hs' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift s) := by simpa [Fm.shift, Syn.shift] using hs.shift
  refine prod_pos (.allI (.impI ?_))
  rw [show Syn.shift (pairT s y) = pairT (Syn.shift s) (Syn.shift y) by simp [Syn.shift]]
  let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have hab : Θ ⊢[PRAAx] le (inst2 aB (var 0) (Syn.shift y)) (inst2 bB (var 0) (Syn.shift y)) :=
    Prf.impE hb.allOpen.wk Prf.hyp0
  have l := le_absd_l (Γ := Θ) (Syn.shift s + inst2 bB (var 0) (Syn.shift y)) (inst2 aB (var 0) (Syn.shift y))
  have e := natEq (fB_at (Γ := Θ) aB bB (var 0) (Syn.shift s) (Syn.shift y))
  ipra_le sl l + sl hab + sl hs'.wk with e

theorem prod_forward {m y : PTm n} (hb : Γ ⊢[PRAAx] Below aB bB m y) : Γ ⊢[PRAAx] ProdTest aB bB m y := by
  have hb' : (Γ.map Fm.shift) ⊢[PRAAx] Below aB bB (Syn.shift m) (Syn.shift y) := by
    have a := hb.shift
    rw [below_shift] at a
    exact a
  refine prod_pos (.allI (.impI ?_))
  rw [show Syn.shift (pairT m y) = pairT (Syn.shift m) (Syn.shift y) by simp [Syn.shift]]
  exact le_congr (.eqRefl _) (oB_at aB bB (var 0) (Syn.shift m) (Syn.shift y)).eqSymm
    (inner_pos aB bB hb'.wk (by ipra_le 𝔞 (var 0)))

theorem prod_backward {m y : PTm n} (ht : Γ ⊢[PRAAx] ProdTest aB bB m y) : Γ ⊢[PRAAx] Below aB bB m y := by
  have ht' : (Γ.map Fm.shift) ⊢[PRAAx] ProdTest aB bB (Syn.shift m) (Syn.shift y) := by
    simpa [Fm.shift, Syn.shift] using ht.shift
  refine SymmetricPrefix.below_of_violation_absurd aB bB (fun hv hbad => ?_)
  let Θ' := lt (inst2 bB (var 0) (Syn.shift y)) (inst2 aB (var 0) (Syn.shift y)) ::
    lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have gap := monus_succ (Γ := Θ') (inst2 aB (var 0) (Syn.shift y)) (inst2 bB (var 0) (Syn.shift y))
  have ps := (Common.monus_succ_of_lt hbad).eqTrans (congrSucc gap)
  have htU := lt_of_lt_of_le (lt_congr gap (.eqRefl _) (Common.monus_succ_lt _ _ hbad))
    (term_le_sum aB hv)
  have hz : Θ' ⊢[PRAAx] inst2 (fB aB bB) (var 0)
      (pairT (succ (pred (monus (inst2 aB (var 0) (Syn.shift y)) (inst2 bB (var 0) (Syn.shift y))))) (Syn.shift y)) ≐
      zero := by
    have q : Θ' ⊢[PRAAx] succ (pred (monus (inst2 aB (var 0) (Syn.shift y)) (inst2 bB (var 0) (Syn.shift y)))) +
        inst2 bB (var 0) (Syn.shift y) ≐ inst2 aB (var 0) (Syn.shift y) := by
      exact (congrAdd ps.eqSymm (.eqRefl _)).eqTrans
        (((eq_add_of_le (le_of_lt hbad)).eqTrans (add_comm _ _)).eqSymm)
    refine (fB_at aB bB _ _ _).eqTrans ?_
    refine (congrAdd (congrMonus q (.eqRefl _)) (congrMonus (.eqRefl _) q)).eqTrans ?_
    exact (congrAdd (le_refl _) (le_refl _)).eqTrans (add_zero _)
  have hin := prod_zero_at (f := fB aB bB) hv hz
  have hout := prod_zero_at (f := oB aB bB) (x := pairT (Syn.shift m) (Syn.shift y)) htU
    ((oB_at aB bB _ _ _).eqTrans hin)
  have c : Θ' ⊢[PRAAx] le one zero := le_congr (.eqRefl _) hout ht'.wk.wk
  exact lt_zero_absurd _ c

theorem sym_char (m y : PTm n) : Γ ⊢[PRAAx] Fm.iff (Below aB bB m y) (ProdTest aB bB m y) :=
  .andI (.impI (prod_forward aB bB Prf.hyp0)) (.impI (prod_backward aB bB Prf.hyp0))

end LeanProofs.IPRA.AnalyticNumberTheory.SymmetricProduct
