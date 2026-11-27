import IPRADerivations.AnalyticNumberTheory.CubeScan
import IPRADerivations.AnalyticNumberTheory.HarmonicMertens
import IPRADerivations.DiophantineNumberTheory.KhinchinBlock

/-!
# Symmetric tests on a whole prefix (`riemann_ipra_prime_criteria_2026-11-20`, Theorem `thm:symmetric-prefix`)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-uniform.tex`, Theorem
`thm:symmetric-prefix`: "Fix a horizon `m ≥ 0`. Define `h = 1 + Σ_{i<m} b_i`, `z_i = a_i + (h − b_i)` … Each of the
following tests is equivalent to `a_i ≤ b_i` for every `i < m`: … `Σ_{i<m} (m+1)^{z_i} ≤ m (m+1)^h` (eq:sym-exp)."

For arbitrary data bodies `a(i, y)`, `b(i, y)` (parameters packed into `y`):

* `term_le_sum`: a single summand is at most the partial sum containing it ("A single summand is at most the
  partial sum containing it, by induction on the prefix length with its index free" — here by one split);
* `exp_forward`, `exp_backward`, `sym_exp`: the exponential test. Forward, every `z_i ≤ h`; backward, a violation
  `a_j > b_j` gives `z_j ≥ h + 1`, and its single term `(m+1)^{h+1} = (m+1)(m+1)^h` already exceeds the allowance.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SymmetricPrefix

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum_ones)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A summand is at most the partial sum containing it. -/
theorem term_le_sum (f : PTm 2) {j m x : PTm n} (h : Γ ⊢[PRAAx] lt j m) :
    Γ ⊢[PRAAx] le (inst2 f j x) (ap2 (sumF f) m x) := by
  have sp := natEq ((congrAp2 (sumF f) (eq_add_of_le h) (.eqRefl x)).eqTrans
    (sum_split (Γ := Γ) f (succ j) (monus m (succ j)) x))
  have ss' : Γ ⊢[PRAAx] ap2 (sumF f) (succ j) x ≐ ap2 (sumF f) j x + inst2 f j x := sum_succ f j x
  have ss := natEq ss'
  ipra_le 𝔞 (ap2 (sumF f) j x) + 𝔞 (ap2 (sumF (offB f)) (monus m (succ j)) (pairT (succ j) x)) with sp + ss

variable (aB bB : PTm 2)

/-- The exponential summand `(m+1)^{z_i}` over `0 = i`, `1 = ⟨⟨h, m+1⟩, y⟩`. -/
def eB : PTm 2 := pw (sndT (fstT (var 1)))
  (Syn.subst ![var 0, sndT (var 1)] aB + monus (fstT (fstT (var 1))) (Syn.subst ![var 0, sndT (var 1)] bB))

theorem inst2_eB (i P : PTm n) : inst2 (eB aB bB) i P =
    pw (sndT (fstT P)) (inst2 aB i (sndT P) + monus (fstT (fstT P)) (inst2 bB i (sndT P))) := by
  have ha : Syn.subst ![i, P] (Syn.subst ![var 0, sndT (var 1)] aB) = inst2 aB i (sndT P) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  have hb : Syn.subst ![i, P] (Syn.subst ![var 0, sndT (var 1)] bB) = inst2 bB i (sndT P) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, eB, subst_ap2, PTm.subst_add, PTm.subst_monus, ha, hb]
  simp

/-- `h = 1 + Σ_{i<m} b_i`. -/
abbrev hP (m y : PTm n) : PTm n := succ (ap2 (sumF bB) m y)
/-- The parameter `⟨⟨h, m+1⟩, y⟩` of the exponential summand. -/
abbrev Par (m y : PTm n) : PTm n := pairT (pairT (hP bB m y) (succ m)) y
/-- The test (eq:sym-exp). -/
abbrev ExpTest (m y : PTm n) : Fm PTm n :=
  le (ap2 (sumF (eB aB bB)) m (Par bB m y)) (m * pw (succ m) (hP bB m y))
/-- The hypothesis `a_i ≤ b_i` for every `i < m`. -/
abbrev Below (m y : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift m) ⟶ le (inst2 aB (var 0) (Syn.shift y)) (inst2 bB (var 0) (Syn.shift y)))

/-- A bounded pointwise comparison follows when every strict violation is contradictory. -/
theorem below_of_violation_absurd {m y : PTm n}
    (contradiction :
      let bad := lt (inst2 bB (var 0) (Syn.shift y)) (inst2 aB (var 0) (Syn.shift y))
      let Δ := bad :: lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
      (Δ ⊢[PRAAx] lt (var 0) (Syn.shift m)) → (Δ ⊢[PRAAx] bad) → (Δ ⊢[PRAAx] Fm.bot)) :
    Γ ⊢[PRAAx] Below aB bB m y := by
  refine .allI (.impI ?_)
  refine .orE (lt_or_le (inst2 bB (var 0) (Syn.shift y)) (inst2 aB (var 0) (Syn.shift y))) ?_ Prf.hyp0
  exact .botE _ (contradiction Prf.hyp1 Prf.hyp0)

/-- Translating both entries by the same padding compares the left entry to the prefix bound. -/
theorem shifted_entry_bounds (i m y : PTm n) (hi : Γ ⊢[PRAAx] lt i m) :
    let a := inst2 aB i y
    let b := inst2 bB i y
    let H := hP bB m y
    Γ ⊢[PRAAx] (le a b ⟶ le (a + monus H b) H) ⋏ (lt b a ⟶ lt H (a + monus H b)) := by
  let b := inst2 bB i y
  let H := hP bB m y
  let padding := monus H b
  have shape : Γ ⊢[PRAAx] H ≐ b + padding := eq_add_of_le (le_trans (term_le_sum bB hi) (le_succ_self _))
  refine .andI (.impI ?_) (.impI ?_)
  · exact le_congr (.eqRefl _) shape.wk.eqSymm (add_le_add_right padding Prf.hyp0)
  · exact le_congr ((succ_add b padding).eqTrans (congrSucc shape.wk.eqSymm)) (.eqRefl _)
      (add_le_add_right padding Prf.hyp0)

theorem eB_at (i m y : PTm n) :
    Γ ⊢[PRAAx] inst2 (eB aB bB) i (Par bB m y) ≐
      pw (succ m) (inst2 aB i y + monus (hP bB m y) (inst2 bB i y)) := by
  rw [inst2_eB]
  exact congrAp2 powF (congrAdd (congrInst2 aB (.eqRefl _) (snd_pair _ _))
    (congrMonus ((congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)) (congrInst2 bB (.eqRefl _) (snd_pair _ _))))
    ((congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _))

theorem shift_par (m y : PTm n) : Syn.shift (Par bB m y) = Par bB (Syn.shift m) (Syn.shift y) := by
  simp [Syn.shift]

/-- Forward: every `z_i ≤ h`, so the sum is at most `m (m+1)^h`. -/
theorem exp_forward {m y : PTm n} (hb : Γ ⊢[PRAAx] Below aB bB m y) : Γ ⊢[PRAAx] ExpTest aB bB m y := by
  have h := sum_le_lin1 (Γ := Γ) (eB aB bB) one one (pw (succ m) (hP bB m y)) (Par bB m y) (Par bB m y) m
    (.allI (.impI (by
      rw [shift_par, show Syn.shift (one : PTm n) = one by simp [Syn.shift],
        show Syn.shift (pw (succ m) (hP bB m y)) = pw (succ (Syn.shift m)) (hP bB (Syn.shift m) (Syn.shift y)) by
          simp [Syn.shift],
        show inst2 (one : PTm 2) (var 0) (Par bB (Syn.shift m) (Syn.shift y)) = one by simp [inst2]]
      let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
      have hv : Θ ⊢[PRAAx] lt (var 0) (Syn.shift m) := Prf.hyp0
      have hab : Θ ⊢[PRAAx] le (inst2 aB (var 0) (Syn.shift y)) (inst2 bB (var 0) (Syn.shift y)) :=
        Prf.impE hb.allOpen.wk hv
      have hz := Prf.impE (shifted_entry_bounds aB bB (var 0) (Syn.shift m) (Syn.shift y) hv).andE₁ hab
      have hp := pw_le_exp (congrSucc (pred_succ (Syn.shift m)).eqSymm) hz
      have ea := natEq (eB_at (Γ := Θ) aB bB (var 0) (Syn.shift m) (Syn.shift y))
      ipra_le sl hp with ea)))
  have so := natEq (sum_ones (Γ := Γ) m (Par bB m y))
  ipra_le sl h with 𝔞 (pw (succ m) (hP bB m y)) * so

/-- Backward: a violation `a_j > b_j` makes its single term exceed the allowance. -/
theorem exp_backward {m y : PTm n} (ht : Γ ⊢[PRAAx] ExpTest aB bB m y) : Γ ⊢[PRAAx] Below aB bB m y := by
  have ht' : (Γ.map Fm.shift) ⊢[PRAAx] ExpTest aB bB (Syn.shift m) (Syn.shift y) := by
    simpa [Fm.shift, Syn.shift] using ht.shift
  refine below_of_violation_absurd aB bB (fun hv hbad => ?_)
  let Θ' := lt (inst2 bB (var 0) (Syn.shift y)) (inst2 aB (var 0) (Syn.shift y)) ::
    lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have hz := Prf.impE (shifted_entry_bounds aB bB (var 0) (Syn.shift m) (Syn.shift y) hv).andE₂ hbad
  have hp := pw_le_exp (congrSucc (pred_succ (Syn.shift m)).eqSymm) hz
  have es := natEq (pw_succ (Γ := Θ') (succ (Syn.shift m)) (hP bB (Syn.shift m) (Syn.shift y)))
  have ea := natEq (eB_at (Γ := Θ') aB bB (var 0) (Syn.shift m) (Syn.shift y))
  have hts := term_le_sum (Γ := Θ') (x := Par bB (Syn.shift m) (Syn.shift y)) (eB aB bB) hv
  have one_le : Θ' ⊢[PRAAx] le one (pw (succ (Syn.shift m)) (hP bB (Syn.shift m) (Syn.shift y))) :=
    le_congr (LeanProofs.IPRA.AnalyticNumberTheory.Order.pw_one_base _) (.eqRefl _)
      (pw_le_pw _ (show Θ' ⊢[PRAAx] le one (succ (Syn.shift m)) by ipra_le 𝔞 (Syn.shift m)))
  have c : Θ' ⊢[PRAAx] lt (Syn.shift m * pw (succ (Syn.shift m)) (hP bB (Syn.shift m) (Syn.shift y)))
      (Syn.shift m * pw (succ (Syn.shift m)) (hP bB (Syn.shift m) (Syn.shift y))) := by
    ipra_le sl hp + sl hts + sl ht'.wk.wk + sl one_le with es + ea
  exact lt_irrefl _ _ c

theorem sym_exp (m y : PTm n) : Γ ⊢[PRAAx] Fm.iff (Below aB bB m y) (ExpTest aB bB m y) :=
  .andI (.impI (exp_forward aB bB Prf.hyp0)) (.impI (exp_backward aB bB Prf.hyp0))

end LeanProofs.IPRA.AnalyticNumberTheory.SymmetricPrefix
