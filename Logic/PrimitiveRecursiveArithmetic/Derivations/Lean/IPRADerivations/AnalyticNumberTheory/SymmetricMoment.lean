import IPRADerivations.AnalyticNumberTheory.SymmetricPrefix

/-!
# The moment test on a whole prefix (`riemann_ipra_prime_criteria_2026-11-20`, `thm:symmetric-prefix`, eq:sym-mom)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-uniform.tex`, Theorem
`thm:symmetric-prefix`, test (eq:sym-mom) `Σ_{i<m} z_i^r ≤ m h^r` with `r = mh + 1`: "For positive `h` and every
`j ≥ 0`, `(h + 1 + j) h^j ≤ (h + 1)^{j+1}` … Take `j = mh` … `m h^{mh+1} < (h + 1)^{mh+1}`. If `a_i > b_i`, its single
term `z_i^r` already exceeds the entire allowance `m h^r`."

* `pow_gap`: `(h + 1 + j) h^j ≤ (h + 1)^{j+1}`, by quantifier-free induction on `j`;
* `allowance_lt`: `m h^{mh+1} + 1 ≤ (h + 1)^{mh+1}` for `h ≥ 1`;
* `mom_forward`, `mom_backward`, `sym_mom`: `(∀i<m a_i ≤ b_i) ↔ Σ_{i<m} z_i^{mh+1} ≤ m h^{mh+1}`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SymmetricMoment

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetricPrefix (term_le_sum hP Below)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The power gap -/

/-- `(h + 1 + j) h^j ≤ (h + 1)^{j+1}`. -/
theorem pow_gap (h j : PTm n) : Γ ⊢[PRAAx] le ((succ h + j) * pw h j) (pw (succ h) (succ j)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le ((succ (Syn.shift h) + var 0) * pw (Syn.shift h) (var 0))
      (pw (succ (Syn.shift h)) (succ (var 0)))) := by
    ipra_qfind (le_QF _ _) [subst_le, subst_ap2]
    · have a := natEq (pw_zero (Γ := Γ) h)
      have b := natEq (pw_one (Γ := Γ) (succ h))
      ipra_le 0 with (𝔞 h + 1) * a - b
    · let Δ : List (Fm PTm (n + 1)) := le ((succ (Syn.shift h) + var 0) * pw (Syn.shift h) (var 0))
          (pw (succ (Syn.shift h)) (succ (var 0))) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] le ((succ (Syn.shift h) + var 0) * pw (Syn.shift h) (var 0))
          (pw (succ (Syn.shift h)) (succ (var 0))) := Prf.hyp0
      have a := natEq (pw_succ (Γ := Δ) (succ (Syn.shift h)) (succ (var 0)))
      have b := natEq (pw_succ (Γ := Δ) (Syn.shift h) (var 0))
      ipra_le (𝔞 (Syn.shift h) + 1) * sl ih + (𝔞 (var 0) + 1) * 𝔞 (pw (Syn.shift h) (var 0)) with
        a - (𝔞 (Syn.shift h) + 𝔞 (var 0) + 2) * b
  have h1 := Prf.allE j hall
  simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ] at h1
  exact h1

/-- `m h^{mh+1} + 1 ≤ (h + 1)^{mh+1}` for `h ≥ 1`. -/
theorem allowance_lt {m h : PTm n} (h1 : Γ ⊢[PRAAx] le one h) :
    Γ ⊢[PRAAx] le (succ (m * pw h (succ (m * h)))) (pw (succ h) (succ (m * h))) := by
  have pg := pow_gap (Γ := Γ) h (m * h)
  have e := natEq (pw_succ (Γ := Γ) h (m * h))
  have one_le : Γ ⊢[PRAAx] le one (pw h (m * h)) :=
    le_congr (LeanProofs.IPRA.AnalyticNumberTheory.Order.pw_one_base _) (.eqRefl _) (pw_le_pw _ h1)
  ipra_le sl pg + 𝔞 h * 𝔞 (pw h (m * h)) + sl one_le with 𝔞 m * e

/-! ## The test -/

variable (aB bB : PTm 2)

/-- The moment summand `z_i^r` over `0 = i`, `1 = ⟨⟨h, r⟩, y⟩`. -/
def momB : PTm 2 :=
  pw (Syn.subst ![var 0, sndT (var 1)] aB + monus (fstT (fstT (var 1))) (Syn.subst ![var 0, sndT (var 1)] bB))
    (sndT (fstT (var 1)))

theorem inst2_momB (i P : PTm n) : inst2 (momB aB bB) i P =
    pw (inst2 aB i (sndT P) + monus (fstT (fstT P)) (inst2 bB i (sndT P))) (sndT (fstT P)) := by
  have ha : Syn.subst ![i, P] (Syn.subst ![var 0, sndT (var 1)] aB) = inst2 aB i (sndT P) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  have hb : Syn.subst ![i, P] (Syn.subst ![var 0, sndT (var 1)] bB) = inst2 bB i (sndT P) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, momB, subst_ap2, PTm.subst_add, PTm.subst_monus, ha, hb]
  simp

/-- `r = mh + 1`. -/
abbrev rP (m y : PTm n) : PTm n := succ (m * hP bB m y)
/-- The parameter `⟨⟨h, r⟩, y⟩`. -/
abbrev ParM (m y : PTm n) : PTm n := pairT (pairT (hP bB m y) (rP bB m y)) y
/-- The test (eq:sym-mom). -/
abbrev MomTest (m y : PTm n) : Fm PTm n :=
  le (ap2 (sumF (momB aB bB)) m (ParM bB m y)) (m * pw (hP bB m y) (rP bB m y))

theorem mom_at (i m y : PTm n) :
    Γ ⊢[PRAAx] inst2 (momB aB bB) i (ParM bB m y) ≐
      pw (inst2 aB i y + monus (hP bB m y) (inst2 bB i y)) (rP bB m y) := by
  rw [inst2_momB]
  exact congrAp2 powF ((congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _))
    (congrAdd (congrInst2 aB (.eqRefl _) (snd_pair _ _))
      (congrMonus ((congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)) (congrInst2 bB (.eqRefl _) (snd_pair _ _))))

theorem shift_parm (m y : PTm n) : Syn.shift (ParM bB m y) = ParM bB (Syn.shift m) (Syn.shift y) := by
  simp [Syn.shift]

theorem mom_forward {m y : PTm n} (hb : Γ ⊢[PRAAx] Below aB bB m y) : Γ ⊢[PRAAx] MomTest aB bB m y := by
  refine sum_le_uniform_bound (momB aB bB) (.allI (.impI ?_))
  rw [shift_parm, show Syn.shift (pw (hP bB m y) (rP bB m y)) = pw (hP bB (Syn.shift m) (Syn.shift y))
    (rP bB (Syn.shift m) (Syn.shift y)) by simp [Syn.shift]]
  have hv : (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift m) := Prf.hyp0
  have hab := Prf.impE hb.allOpen.wk hv
  have hz := Prf.impE (SymmetricPrefix.shifted_entry_bounds aB bB (var 0) (Syn.shift m) (Syn.shift y) hv).andE₁ hab
  have hp := pw_le_pw (rP bB (Syn.shift m) (Syn.shift y)) hz
  exact le_congr (mom_at aB bB (var 0) (Syn.shift m) (Syn.shift y)).eqSymm (.eqRefl _) hp

theorem mom_backward {m y : PTm n} (ht : Γ ⊢[PRAAx] MomTest aB bB m y) : Γ ⊢[PRAAx] Below aB bB m y := by
  have ht' : (Γ.map Fm.shift) ⊢[PRAAx] MomTest aB bB (Syn.shift m) (Syn.shift y) := by
    simpa [Fm.shift, Syn.shift] using ht.shift
  refine SymmetricPrefix.below_of_violation_absurd aB bB (fun hv hbad => ?_)
  let Θ' := lt (inst2 bB (var 0) (Syn.shift y)) (inst2 aB (var 0) (Syn.shift y)) ::
    lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have hz := Prf.impE (SymmetricPrefix.shifted_entry_bounds aB bB (var 0) (Syn.shift m) (Syn.shift y) hv).andE₂ hbad
  have hp := pw_le_pw (rP bB (Syn.shift m) (Syn.shift y)) hz
  have gap := allowance_lt (Γ := Θ') (m := Syn.shift m) (h := hP bB (Syn.shift m) (Syn.shift y))
    (by ipra_le 𝔞 (ap2 (sumF bB) (Syn.shift m) (Syn.shift y)))
  have ea := natEq (mom_at (Γ := Θ') aB bB (var 0) (Syn.shift m) (Syn.shift y))
  have hts := term_le_sum (Γ := Θ') (x := ParM bB (Syn.shift m) (Syn.shift y)) (momB aB bB) hv
  have c : Θ' ⊢[PRAAx] lt (Syn.shift m * pw (hP bB (Syn.shift m) (Syn.shift y)) (rP bB (Syn.shift m) (Syn.shift y)))
      (Syn.shift m * pw (hP bB (Syn.shift m) (Syn.shift y)) (rP bB (Syn.shift m) (Syn.shift y))) := by
    ipra_le sl gap + sl hp + sl hts + sl ht'.wk.wk with ea
  exact lt_irrefl _ _ c

theorem sym_mom (m y : PTm n) : Γ ⊢[PRAAx] Fm.iff (Below aB bB m y) (MomTest aB bB m y) :=
  .andI (.impI (mom_forward aB bB Prf.hyp0)) (.impI (mom_backward aB bB Prf.hyp0))

end LeanProofs.IPRA.AnalyticNumberTheory.SymmetricMoment
