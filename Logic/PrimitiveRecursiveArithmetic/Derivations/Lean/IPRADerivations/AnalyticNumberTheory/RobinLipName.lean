import IPRADerivations.AnalyticNumberTheory.RobinLogDiff

/-!
# Lipschitz bounds for the artanh truncations (`robin_ipra_research_2026-11-19`, §"Explicit interval arithmetic")

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/report.tex`: the composed `2^{-k}` widths and the
loss `D(m²) ≤ 8/m` of `paper/lcm_bridge.tex` compare logarithm names of *different* arguments. iPRA has no "true log",
so the comparisons are rational inequalities about the truncations `S_K(z) = 2 Σ_{j<K} z^{2j+1}/(2j+1)` themselves
(`RobinLogName`: `S_K(p/s) = N_K/(L_K s^{2K+1})`).

* `pd1`, `pd2`: for `a = b + δ`, `b^{j+1} + (j+1)δ b^j ≤ a^{j+1} ≤ b^{j+1} + (j+1)δ a^j` (the two mean-value bounds of
  `a^{j+1} − b^{j+1}`);
* `lip_up_gen`: for `z = p/s ≤ z' = p'/s'` and every `K`,
  `S_K(z') − S_K(z) + 2(z' − z)z'^{2K}/(1 − z'²) ≤ 2(z' − z)/(1 − z'²)`;
  `lip_up`: in particular `S_K(z') − S_K(z) ≤ 2(z' − z)/(1 − z'²)` — the brief's item (1a);
* `lip_low`: `S_K(z') − S_K(z) ≥ 2(z' − z)(1 − z^{2K})/(1 − z²)` — the matching lower bound, with the explicit
  truncation error `2(z' − z)z^{2K}/(1 − z²)`.

Cleared: `z' − z = δ/(ss')` with `p's = ps' + δ`, `1 − z² = W/s²` with `s² = W + p²`, `1 − z'² = W'/s'²`, and
`z^{2K} = p^{2K}/s^{2K}` (`Rv K p = p^{2K}`).

The upper names `U_K = S_K + 2z^{2K+1}/((2K+1)(1−z²))` do **not** satisfy the same bound: at `z' → z` their slope is
`2/(1−z²) + 4z^{2K+2}/((2K+1)(1−z²)²) > 2/(1−z²)` for `z > 0` (at `K = 0`, `U_0 = 2z/(1−z²)`). The cross-argument
comparisons of `RobinLipLog` therefore use `S_K` for both directions and reach the upper names through the widths.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinLipName

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma (Lv L_zero L_succ Pv P_succ P_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (Nz Nz_zero Nz_succ Dz Lz)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Power differences -/

/-- `a^{j+1} ≤ b^{j+1} + (j+1) δ a^j`. -/
abbrev PD1 (j a b d : PTm n) : Fm PTm n := le (pw a (succ j)) (pw b (succ j) + succ j * d * pw a j)
/-- `b^{j+1} + (j+1) δ b^j ≤ a^{j+1}`. -/
abbrev PD2 (j a b d : PTm n) : Fm PTm n := le (pw b (succ j) + succ j * d * pw b j) (pw a (succ j))

theorem pd1_step {j a b d : PTm n} (he : Γ ⊢[PRAAx] a ≐ b + d) (ih : Γ ⊢[PRAAx] PD1 j a b d) :
    Γ ⊢[PRAAx] PD1 (succ j) a b d := by
  have hba : Γ ⊢[PRAAx] le b a := le_of_eq_add he
  have w := pw_le_pw (Γ := Γ) (succ j) hba
  have e1 := natEq (pw_succ (Γ := Γ) a (succ j))
  have e2 := natEq (pw_succ (Γ := Γ) a j)
  have e3 := natEq (pw_succ (Γ := Γ) b (succ j))
  have he' := natEq he
  ipra_le 𝔞 a * sl ih + 𝔞 d * sl w with -e1 + (𝔞 d * 𝔞 j + 𝔞 d) * e2 + e3 - 𝔞 (pw b (succ j)) * he'

theorem pd2_step {j a b d : PTm n} (he : Γ ⊢[PRAAx] a ≐ b + d) (ih : Γ ⊢[PRAAx] PD2 j a b d) :
    Γ ⊢[PRAAx] PD2 (succ j) a b d := by
  have e1 := natEq (pw_succ (Γ := Γ) a (succ j))
  have e3 := natEq (pw_succ (Γ := Γ) b (succ j))
  have e4 := natEq (pw_succ (Γ := Γ) b j)
  have he' := natEq he
  ipra_le 𝔞 a * sl ih + 𝔞 (succ j * d * d * pw b j) with e1 - e3 + (𝔞 a - 𝔞 b - 𝔞 d * 𝔞 j - 2 * 𝔞 d) * e4 +
    (𝔞 (pw b j) * 𝔞 b + 𝔞 (pw b j) * 𝔞 d * 𝔞 j + 𝔞 (pw b j) * 𝔞 d) * he'

theorem pd_base_eqs (a : PTm n) : Γ ⊢[PRAAx] pw a (succ zero) ≐ a :=
  (pw_succ a zero).eqTrans ((congrMul (pw_zero a) (.eqRefl _)).eqTrans (one_mul _))

theorem pd1 {a b d : PTm n} (he : Γ ⊢[PRAAx] a ≐ b + d) (j : PTm n) : Γ ⊢[PRAAx] PD1 j a b d := by
  have hall : Γ ⊢[PRAAx] Fm.all (PD1 (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift d)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift]
      have eA1 := natEq (pd_base_eqs (Γ := Γ) a)
      have eB1 := natEq (pd_base_eqs (Γ := Γ) b)
      have eA0 := natEq (pw_zero (Γ := Γ) a)
      have he' := natEq he
      ipra_le 0 with eB1 + 𝔞 d * eA0 - eA1 - he'
    · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift]
      have he' : (PD1 (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift d) :: Γ.map Fm.shift) ⊢[PRAAx]
          Syn.shift a ≐ Syn.shift b + Syn.shift d := by
        have b := he.shift
        simp only [Fm.shift, Fm.subst_eq, PTm.subst_add] at b
        exact b.wk
      exact pd1_step he' Prf.hyp0
  have r := Prf.allE j hall
  simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] at r
  exact r

theorem pd2 {a b d : PTm n} (he : Γ ⊢[PRAAx] a ≐ b + d) (j : PTm n) : Γ ⊢[PRAAx] PD2 j a b d := by
  have hall : Γ ⊢[PRAAx] Fm.all (PD2 (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift d)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift]
      have eA1 := natEq (pd_base_eqs (Γ := Γ) a)
      have eB1 := natEq (pd_base_eqs (Γ := Γ) b)
      have eB0 := natEq (pw_zero (Γ := Γ) b)
      have he' := natEq he
      ipra_le 0 with eA1 - eB1 - 𝔞 d * eB0 + he'
    · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift]
      have he' : (PD2 (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift d) :: Γ.map Fm.shift) ⊢[PRAAx]
          Syn.shift a ≐ Syn.shift b + Syn.shift d := by
        have b := he.shift
        simp only [Fm.shift, Fm.subst_eq, PTm.subst_add] at b
        exact b.wk
      exact pd2_step he' Prf.hyp0
  have r := Prf.allE j hall
  simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] at r
  exact r

/-! ## Even powers -/

/-- `p^{2K}`. -/
abbrev Rv (K p : PTm n) : PTm n := pw p (two * K)

theorem R_zero (p : PTm n) : Γ ⊢[PRAAx] Rv zero p ≐ one :=
  (congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] (two : PTm n) * zero ≐ zero) (.eqRefl _)).eqTrans (pw_zero _)

theorem R_succ (K p : PTm n) : Γ ⊢[PRAAx] Rv (succ K) p ≐ Rv K p * p * p :=
  (congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] two * succ K ≐ succ (succ (two * K))) (.eqRefl _)).eqTrans
    ((pw_succ _ _).eqTrans (congrMul (pw_succ _ _) (.eqRefl _)))

/-- `(p's)^{2K+1} ≤ (ps')^{2K+1} + (2K+1) δ (p's)^{2K}`, split into the four powers. -/
theorem pow_up {p s p' s' d : PTm n} (hd : Γ ⊢[PRAAx] p' * s ≐ p * s' + d) (K : PTm n) :
    Γ ⊢[PRAAx] le (Pv K p' * Pv K s) (Pv K p * Pv K s' + succ (two * K) * d * (Rv K p' * Rv K s)) :=
  le_congr (LocalFactor.pw_mul_base _ _ _)
    (congrAdd (LocalFactor.pw_mul_base _ _ _) (congrMul (.eqRefl _) (LocalFactor.pw_mul_base _ _ _))) (pd1 hd (two * K))

/-- `(ps')^{2K+1} + (2K+1) δ (ps')^{2K} ≤ (p's)^{2K+1}`. -/
theorem pow_low {p s p' s' d : PTm n} (hd : Γ ⊢[PRAAx] p' * s ≐ p * s' + d) (K : PTm n) :
    Γ ⊢[PRAAx] le (Pv K p * Pv K s' + succ (two * K) * d * (Rv K p * Rv K s')) (Pv K p' * Pv K s) :=
  le_congr (congrAdd (LocalFactor.pw_mul_base _ _ _) (congrMul (.eqRefl _) (LocalFactor.pw_mul_base _ _ _)))
    (LocalFactor.pw_mul_base _ _ _) (pd2 hd (two * K))

/-! ## The upper Lipschitz bound -/

/-- `S_K(z') − S_K(z) + 2(z'−z)z'^{2K}/(1−z'²) ≤ 2(z'−z)/(1−z'²)`, cleared over `L_K s^{2K+1} s'^{2K+1} s W'`. -/
abbrev SUF (K p s p' s' W' d : PTm n) : Fm PTm n :=
  le (Nz K p' s' * Pv K s * s * W' + two * d * (s' * s') * Rv K p' * Lz K p s * Pv K s)
    (Nz K p s * Pv K s' * s * W' + two * d * s' * Lz K p s * Pv K s * Pv K s')

theorem su_step {K p s p' s' W' d : PTm n} (hW' : Γ ⊢[PRAAx] s' * s' ≐ W' + p' * p')
    (hd : Γ ⊢[PRAAx] p' * s ≐ p * s' + d) (ih : Γ ⊢[PRAAx] SUF K p s p' s' W' d) :
    Γ ⊢[PRAAx] SUF (succ K) p s p' s' W' d := by
  have eN := natEq (Nz_succ (Γ := Γ) K p s)
  have eN' := natEq (Nz_succ (Γ := Γ) K p' s')
  have eL := natEq (L_succ (Γ := Γ) K (zero : PTm n))
  have eQ := natEq (P_succ (Γ := Γ) K s)
  have eQ' := natEq (P_succ (Γ := Γ) K s')
  have eR := natEq (R_succ (Γ := Γ) K p')
  have eQ0 := natEq (pw_succ (Γ := Γ) s (two * K))
  have eW := natEq hW'
  have p1 := pow_up hd K
  ipra_le 𝔞 (succ (two * K) * (s * s) * (s' * s')) * sl ih + 𝔞 (two * Lz K p s * (s * s) * (s' * s') * W' * s) * sl p1 with
    ((𝔞 (Pv (succ K) s') * 𝔞 W' * 𝔞 s)) * eN + ((-𝔞 (Pv (succ K) s) * 𝔞 W' * 𝔞 s)) * eN' + ((2 * 𝔞 (Pv (succ K) s) * 𝔞 (Pv (succ K) s') * 𝔞 d * 𝔞 s') + (-2 * 𝔞 (Pv (succ K) s) * 𝔞 (Rv (succ K) p') * 𝔞 d * (𝔞 s') ^ 2)) * eL + ((4 * 𝔞 K * 𝔞 (Lv K zero) * 𝔞 (Pv (succ K) s') * 𝔞 d * 𝔞 s') + (-4 * 𝔞 K * 𝔞 (Lv K zero) * 𝔞 (Rv (succ K) p') * 𝔞 d * (𝔞 s') ^ 2) + (-2 * 𝔞 K * 𝔞 (Nz K p' s') * 𝔞 W' * 𝔞 s * (𝔞 s') ^ 2) + (-2 * 𝔞 (Lv K zero) * 𝔞 (Pv K p') * 𝔞 W' * 𝔞 s * (𝔞 s') ^ 2) + (2 * 𝔞 (Lv K zero) * 𝔞 (Pv (succ K) s') * 𝔞 d * 𝔞 s') + (-2 * 𝔞 (Lv K zero) * 𝔞 (Rv (succ K) p') * 𝔞 d * (𝔞 s') ^ 2) + (-𝔞 (Nz K p' s') * 𝔞 W' * 𝔞 s * (𝔞 s') ^ 2)) * eQ + ((4 * 𝔞 K * 𝔞 (Lv K zero) * 𝔞 (Pv K s) * 𝔞 d * (𝔞 s) ^ 2 * 𝔞 s') + (2 * 𝔞 K * 𝔞 (Nz K p s) * 𝔞 W' * (𝔞 s) ^ 3) + (2 * 𝔞 (Lv K zero) * 𝔞 (Pv K p) * 𝔞 W' * (𝔞 s) ^ 3) + (2 * 𝔞 (Lv K zero) * 𝔞 (Pv K s) * 𝔞 d * (𝔞 s) ^ 2 * 𝔞 s') + (𝔞 (Nz K p s) * 𝔞 W' * (𝔞 s) ^ 3)) * eQ' + ((-4 * 𝔞 K * 𝔞 (Lv K zero) * 𝔞 (Pv K s) * 𝔞 d * (𝔞 s) ^ 2 * (𝔞 s') ^ 2) + (-2 * 𝔞 (Lv K zero) * 𝔞 (Pv K s) * 𝔞 d * (𝔞 s) ^ 2 * (𝔞 s') ^ 2)) * eR + ((-4 * 𝔞 K * 𝔞 (Lv K zero) * 𝔞 (Rv K p') * 𝔞 d * (𝔞 p') ^ 2 * (𝔞 s) ^ 2 * (𝔞 s') ^ 2) + (4 * 𝔞 K * 𝔞 (Lv K zero) * 𝔞 (Rv K p') * 𝔞 d * (𝔞 s) ^ 2 * (𝔞 s') ^ 4) + (-2 * 𝔞 (Lv K zero) * 𝔞 (Rv K p') * 𝔞 d * (𝔞 p') ^ 2 * (𝔞 s) ^ 2 * (𝔞 s') ^ 2) + (2 * 𝔞 (Lv K zero) * 𝔞 (Rv K p') * 𝔞 d * (𝔞 s) ^ 2 * (𝔞 s') ^ 4)) * eQ0 + ((4 * 𝔞 K * 𝔞 (Lv K zero) * 𝔞 (Rv K p') * 𝔞 (Rv K s) * 𝔞 d * (𝔞 s) ^ 3 * (𝔞 s') ^ 2) + (2 * 𝔞 (Lv K zero) * 𝔞 (Rv K p') * 𝔞 (Rv K s) * 𝔞 d * (𝔞 s) ^ 3 * (𝔞 s') ^ 2)) * eW

theorem su_zero (p s p' s' W' d : PTm n) : Γ ⊢[PRAAx] SUF zero p s p' s' W' d := by
  have a := natEq (Nz_zero (Γ := Γ) p s)
  have b := natEq (Nz_zero (Γ := Γ) p' s')
  have c := natEq (L_zero (Γ := Γ) (zero : PTm n))
  have e := natEq (P_zero (Γ := Γ) s)
  have f := natEq (P_zero (Γ := Γ) s')
  have g := natEq (R_zero (Γ := Γ) p')
  ipra_le 0 with ((𝔞 (Pv zero s') * 𝔞 W' * 𝔞 s)) * a + ((-𝔞 (Pv zero s) * 𝔞 W' * 𝔞 s)) * b + ((2 * 𝔞 (Pv zero s) * 𝔞 (Pv zero s') * 𝔞 d * 𝔞 s') + (-2 * 𝔞 (Pv zero s) * 𝔞 (Rv zero p') * 𝔞 d * (𝔞 s') ^ 2)) * c + ((2 * 𝔞 (Pv zero s') * 𝔞 d * 𝔞 s') + (-2 * 𝔞 (Rv zero p') * 𝔞 d * (𝔞 s') ^ 2)) * e + ((2 * 𝔞 d * 𝔞 s * 𝔞 s')) * f + ((-2 * 𝔞 d * 𝔞 s * (𝔞 s') ^ 2)) * g

theorem lip_up_gen {p s p' s' W' d : PTm n} (hW' : Γ ⊢[PRAAx] s' * s' ≐ W' + p' * p')
    (hd : Γ ⊢[PRAAx] p' * s ≐ p * s' + d) (K : PTm n) : Γ ⊢[PRAAx] SUF K p s p' s' W' d := by
  have hall : Γ ⊢[PRAAx] Fm.all (SUF (var 0) (Syn.shift p) (Syn.shift s) (Syn.shift p') (Syn.shift s')
      (Syn.shift W') (Syn.shift d)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact su_zero p s p' s' W' d
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ : List (Fm PTm (n + 1)) := SUF (var 0) (Syn.shift p) (Syn.shift s) (Syn.shift p') (Syn.shift s')
        (Syn.shift W') (Syn.shift d) :: Γ.map Fm.shift
      have hW'' : Δ ⊢[PRAAx] Syn.shift s' * Syn.shift s' ≐ Syn.shift W' + Syn.shift p' * Syn.shift p' := by
        have b := hW'.shift
        simp only [Fm.shift, Fm.subst_eq, PTm.subst_mul, PTm.subst_add] at b
        exact b.wk
      have hd' : Δ ⊢[PRAAx] Syn.shift p' * Syn.shift s ≐ Syn.shift p * Syn.shift s' + Syn.shift d := by
        have b := hd.shift
        simp only [Fm.shift, Fm.subst_eq, PTm.subst_mul, PTm.subst_add] at b
        exact b.wk
      exact su_step hW'' hd' Prf.hyp0
  have r := Prf.allE K hall
  simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at r
  exact r

/-- Item (1a): `S_K(z') − S_K(z) ≤ 2(z' − z)/(1 − z'²)` for `z = p/s ≤ z' = p'/s'`, `p's = ps' + δ`, `s'² = W' + p'²`,
cleared over `L_K s^{2K+1} s'^{2K+1} s W'`. -/
theorem lip_up {p s p' s' W' d : PTm n} (hW' : Γ ⊢[PRAAx] s' * s' ≐ W' + p' * p')
    (hd : Γ ⊢[PRAAx] p' * s ≐ p * s' + d) (K : PTm n) :
    Γ ⊢[PRAAx] le (Nz K p' s' * Pv K s * s * W') (Nz K p s * Pv K s' * s * W' + two * d * s' * Lz K p s * Pv K s * Pv K s') := by
  have h := lip_up_gen hW' hd K
  ipra_le sl h + 𝔞 (two * d * (s' * s') * Rv K p' * Lz K p s * Pv K s)

/-! ## The lower Lipschitz bound -/

/-- `S_K(z) + 2(z'−z)/(1−z²) ≤ S_K(z') + 2(z'−z)z^{2K}/(1−z²)`, cleared over `L_K s^{2K+1} s'^{2K+1} s' W`. -/
abbrev SLF (K p s p' s' W d : PTm n) : Fm PTm n :=
  le (Nz K p s * Pv K s' * s' * W + two * d * s * Lz K p s * Pv K s * Pv K s')
    (Nz K p' s' * Pv K s * s' * W + two * d * (s * s) * Rv K p * Lz K p s * Pv K s')

theorem sl_step {K p s p' s' W d : PTm n} (hW : Γ ⊢[PRAAx] s * s ≐ W + p * p)
    (hd : Γ ⊢[PRAAx] p' * s ≐ p * s' + d) (ih : Γ ⊢[PRAAx] SLF K p s p' s' W d) :
    Γ ⊢[PRAAx] SLF (succ K) p s p' s' W d := by
  have eN := natEq (Nz_succ (Γ := Γ) K p s)
  have eN' := natEq (Nz_succ (Γ := Γ) K p' s')
  have eL := natEq (L_succ (Γ := Γ) K (zero : PTm n))
  have eQ := natEq (P_succ (Γ := Γ) K s)
  have eQ' := natEq (P_succ (Γ := Γ) K s')
  have eR := natEq (R_succ (Γ := Γ) K p)
  have eQ0 := natEq (pw_succ (Γ := Γ) s' (two * K))
  have eW := natEq hW
  have p2 := pow_low hd K
  ipra_le 𝔞 (succ (two * K) * (s * s) * (s' * s')) * sl ih + 𝔞 (two * Lz K p s * (s * s) * (s' * s') * W * s') * sl p2 with
    ((-𝔞 (Pv (succ K) s') * 𝔞 W * 𝔞 s')) * eN + ((𝔞 (Pv (succ K) s) * 𝔞 W * 𝔞 s')) * eN' + ((-2 * 𝔞 (Pv (succ K) s) * 𝔞 (Pv (succ K) s') * 𝔞 d * 𝔞 s) + (2 * 𝔞 (Pv (succ K) s') * 𝔞 (Rv (succ K) p) * 𝔞 d * (𝔞 s) ^ 2)) * eL + ((-4 * 𝔞 K * 𝔞 (Lv K zero) * 𝔞 (Pv (succ K) s') * 𝔞 d * 𝔞 s) + (2 * 𝔞 K * 𝔞 (Nz K p' s') * 𝔞 W * (𝔞 s') ^ 3) + (2 * 𝔞 (Lv K zero) * 𝔞 (Pv K p') * 𝔞 W * (𝔞 s') ^ 3) + (-2 * 𝔞 (Lv K zero) * 𝔞 (Pv (succ K) s') * 𝔞 d * 𝔞 s) + (𝔞 (Nz K p' s') * 𝔞 W * (𝔞 s') ^ 3)) * eQ + ((-4 * 𝔞 K * 𝔞 (Lv K zero) * 𝔞 (Pv K s) * 𝔞 d * (𝔞 s) ^ 3) + (4 * 𝔞 K * 𝔞 (Lv K zero) * 𝔞 (Rv (succ K) p) * 𝔞 d * (𝔞 s) ^ 2) + (-2 * 𝔞 K * 𝔞 (Nz K p s) * 𝔞 W * (𝔞 s) ^ 2 * 𝔞 s') + (-2 * 𝔞 (Lv K zero) * 𝔞 (Pv K p) * 𝔞 W * (𝔞 s) ^ 2 * 𝔞 s') + (-2 * 𝔞 (Lv K zero) * 𝔞 (Pv K s) * 𝔞 d * (𝔞 s) ^ 3) + (2 * 𝔞 (Lv K zero) * 𝔞 (Rv (succ K) p) * 𝔞 d * (𝔞 s) ^ 2) + (-𝔞 (Nz K p s) * 𝔞 W * (𝔞 s) ^ 2 * 𝔞 s')) * eQ' + ((4 * 𝔞 K * 𝔞 (Lv K zero) * 𝔞 (Pv K s') * 𝔞 d * (𝔞 s) ^ 2 * (𝔞 s') ^ 2) + (2 * 𝔞 (Lv K zero) * 𝔞 (Pv K s') * 𝔞 d * (𝔞 s) ^ 2 * (𝔞 s') ^ 2)) * eR + ((4 * 𝔞 K * 𝔞 (Lv K zero) * 𝔞 (Rv K p) * 𝔞 d * (𝔞 p) ^ 2 * (𝔞 s) ^ 2 * (𝔞 s') ^ 2) + (-4 * 𝔞 K * 𝔞 (Lv K zero) * 𝔞 (Rv K p) * 𝔞 d * (𝔞 s) ^ 4 * (𝔞 s') ^ 2) + (2 * 𝔞 (Lv K zero) * 𝔞 (Rv K p) * 𝔞 d * (𝔞 p) ^ 2 * (𝔞 s) ^ 2 * (𝔞 s') ^ 2) + (-2 * 𝔞 (Lv K zero) * 𝔞 (Rv K p) * 𝔞 d * (𝔞 s) ^ 4 * (𝔞 s') ^ 2)) * eQ0 + ((-4 * 𝔞 K * 𝔞 (Lv K zero) * 𝔞 (Rv K p) * 𝔞 (Rv K s') * 𝔞 d * (𝔞 s) ^ 2 * (𝔞 s') ^ 3) + (-2 * 𝔞 (Lv K zero) * 𝔞 (Rv K p) * 𝔞 (Rv K s') * 𝔞 d * (𝔞 s) ^ 2 * (𝔞 s') ^ 3)) * eW

theorem sl_zero (p s p' s' W d : PTm n) : Γ ⊢[PRAAx] SLF zero p s p' s' W d := by
  have a := natEq (Nz_zero (Γ := Γ) p s)
  have b := natEq (Nz_zero (Γ := Γ) p' s')
  have c := natEq (L_zero (Γ := Γ) (zero : PTm n))
  have e := natEq (P_zero (Γ := Γ) s)
  have f := natEq (P_zero (Γ := Γ) s')
  have g := natEq (R_zero (Γ := Γ) p)
  ipra_le 0 with ((-𝔞 (Pv zero s') * 𝔞 W * 𝔞 s')) * a + ((𝔞 (Pv zero s) * 𝔞 W * 𝔞 s')) * b + ((-2 * 𝔞 (Pv zero s) * 𝔞 (Pv zero s') * 𝔞 d * 𝔞 s) + (2 * 𝔞 (Pv zero s') * 𝔞 (Rv zero p) * 𝔞 d * (𝔞 s) ^ 2)) * c + ((-2 * 𝔞 (Pv zero s') * 𝔞 d * 𝔞 s)) * e + ((2 * 𝔞 (Rv zero p) * 𝔞 d * (𝔞 s) ^ 2) + (-2 * 𝔞 d * (𝔞 s) ^ 2)) * f + ((2 * 𝔞 d * (𝔞 s) ^ 2 * 𝔞 s')) * g

/-- `S_K(z') − S_K(z) ≥ 2(z' − z)(1 − z^{2K})/(1 − z²)` for `z = p/s ≤ z' = p'/s'`, `p's = ps' + δ`, `s² = W + p²`. -/
theorem lip_low {p s p' s' W d : PTm n} (hW : Γ ⊢[PRAAx] s * s ≐ W + p * p)
    (hd : Γ ⊢[PRAAx] p' * s ≐ p * s' + d) (K : PTm n) : Γ ⊢[PRAAx] SLF K p s p' s' W d := by
  have hall : Γ ⊢[PRAAx] Fm.all (SLF (var 0) (Syn.shift p) (Syn.shift s) (Syn.shift p') (Syn.shift s')
      (Syn.shift W) (Syn.shift d)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact sl_zero p s p' s' W d
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ : List (Fm PTm (n + 1)) := SLF (var 0) (Syn.shift p) (Syn.shift s) (Syn.shift p') (Syn.shift s')
        (Syn.shift W) (Syn.shift d) :: Γ.map Fm.shift
      have hW'' : Δ ⊢[PRAAx] Syn.shift s * Syn.shift s ≐ Syn.shift W + Syn.shift p * Syn.shift p := by
        have b := hW.shift
        simp only [Fm.shift, Fm.subst_eq, PTm.subst_mul, PTm.subst_add] at b
        exact b.wk
      have hd' : Δ ⊢[PRAAx] Syn.shift p' * Syn.shift s ≐ Syn.shift p * Syn.shift s' + Syn.shift d := by
        have b := hd.shift
        simp only [Fm.shift, Fm.subst_eq, PTm.subst_mul, PTm.subst_add] at b
        exact b.wk
      exact sl_step hW'' hd' Prf.hyp0
  have r := Prf.allE K hall
  simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at r
  exact r

end LeanProofs.IPRA.AnalyticNumberTheory.RobinLipName
