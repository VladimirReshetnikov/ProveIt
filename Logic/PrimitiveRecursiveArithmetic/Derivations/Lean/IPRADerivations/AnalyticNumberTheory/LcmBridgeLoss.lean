import IPRADerivations.AnalyticNumberTheory.PrimorialLower
import IPRADerivations.AnalyticNumberTheory.SymmetryPointwise
import IPRADerivations.Analysis.FiniteOperations.FiniteProducts.WeierstrassProduct

/-!
# The prime-power reciprocal loss of the lcm bridge: `Σ_{p≤m²} p^{−a_p−1} ≤ 2/m`

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/lcm_bridge.tex`, Lemma "Losses at a square
frontier", the estimate of `T(P) = Σ_{p≤P} −log(1 − p^{−a_p(P)−1})`: "If `p ≤ m`, maximality of `a_p(P)` implies
`p^{a_p(P)+1} > P` … These at most `m` summands contribute at most … If `m < p ≤ P`, then `a_p(P) = 1`, so the remaining
summands contribute at most `2 Σ_{j=m+1}^{P} 1/(j(j−1)) = 2(1/m − 1/P)`."

The logarithm enters the bridge only through `∏_{p≤P}(1 − p^{−a_p−1})`, which the Weierstrass product inequality
(`Analysis/WeierstrassProduct`) bounds below by `1 − Σ_p p^{−a_p−1}`; the finite content of the `T` estimate is the
rational bound on that sum, derived here. With `L = lcm(1, …, P)` (`LcmUpto.lcmu`), `a_p = v_p(L)` and the common
denominator `L²`, the terms are `u_i = [i prime] ⌊L²/i^{v_i(L)+1}⌋` (`uB`), and `U(N) = Σ_{i<N} u_i`:

* `uA`: `P u_i ≤ L²` for every `i` (since `i^{v_i(L)+1} > P`);
* `uB_sq`: `i² u_i ≤ L²` for `i ≤ P` (a prime `i ≤ P` has `v_i(L) ≥ 1`);
* `phase1`: `P · U(N) ≤ N L²`;
* `jbase`, `jstep`, `phase2`: the telescoping invariant
  `J(N): m N P U(N+1) + m P L² ≤ N P L² + m N (m+1) L²` for `m ≤ N ≤ P`;
* `loss_sum`: `m · U(m² + 1) ≤ 2 L²` for `m ≥ 1`, i.e. `Σ_{p≤m²} ⌊L²/p^{a_p+1}⌋/L² ≤ 2/m`;
* `prod_lower`: with `c_i = L² − u_i` (`cB`), the Weierstrass inequality and `loss_sum` give
  `m L^{2(P+1)} ≤ m ∏_{i≤P} c_i + 2 L^{2(P+1)}`, i.e. `∏_{p≤m²}(1 − p^{−a_p−1}) ≥ 1 − 2/m`: the product form of
  `T(m²) ≤ 4/m` through which the loss enters the bridge.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeLoss

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP isP_01 prime_of_isP pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The terms -/

/-- `L² = lcm(1, …, P)²`. -/
abbrev LD (P : PTm n) : PTm n := lcmu P * lcmu P
/-- `i^{v_i(L)+1}`. -/
abbrev ex (i P : PTm n) : PTm n := pw i (succ (val i (lcmu P)))
/-- `u_i = [i prime] ⌊L²/i^{v_i(L)+1}⌋`, over `0 = i`, `1 = P`. -/
abbrev uB : PTm 2 := isP (var 0) * quo (lcmu (var 1) * lcmu (var 1)) (pw (var 0) (succ (val (var 0) (lcmu (var 1)))))
/-- `U(N) = Σ_{i<N} u_i`. -/
abbrev U (N P : PTm n) : PTm n := ap2 (sumF uB) N P

theorem inst2_uB (i P : PTm n) : inst2 uB i P = isP i * quo (LD P) (ex i P) := by simp [inst2]

theorem u_zero {i P : PTm n} (h : Γ ⊢[PRAAx] isP i ≐ zero) (c : PTm n) :
    Γ ⊢[PRAAx] c * (isP i * quo (LD P) (ex i P)) ≐ zero :=
  (congrMul (.eqRefl _) ((congrMul h (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (mul_zero _)

/-- `P u_i ≤ L²`. -/
theorem uA (i P : PTm n) : Γ ⊢[PRAAx] le (P * (isP i * quo (LD P) (ex i P))) (LD P) := by
  refine .orE (isP_01 i) (le_congr (u_zero Prf.hyp0 P).eqSymm (.eqRefl _) (zero_le _)) ?_
  let C : List (Fm PTm n) := (isP i ≐ one) :: Γ
  have hi : C ⊢[PRAAx] prime i := prime_of_isP Prf.hyp0
  have I2 := Prf.andE₂ (lcm_valuation hi P)
  have dpos := pw_pos' (p_pos (prime_two hi)) (succ (val i (lcmu P)))
  have q := SymmetryPointwise.quo_mul_le (x := LD P) dpos
  have a := le_mul_mono (le_refl (quo (LD P) (ex i P))) (le_of_lt I2)
  refine le_congr ?_ (.eqRefl _) (le_trans a q)
  ipra_lc (-(𝔞 P * 𝔞 (quo (LD P) (ex i P)))) * natEq (Prf.hyp0 : C ⊢[PRAAx] isP i ≐ one)

/-- `i² u_i ≤ L²` for `i ≤ P`. -/
theorem uB_sq {i P : PTm n} (hiP : Γ ⊢[PRAAx] le i P) :
    Γ ⊢[PRAAx] le (i * i * (isP i * quo (LD P) (ex i P))) (LD P) := by
  refine .orE (isP_01 i) (le_congr (u_zero Prf.hyp0 (i * i)).eqSymm (.eqRefl _) (zero_le _)) ?_
  let C : List (Fm PTm n) := (isP i ≐ one) :: Γ
  have hi : C ⊢[PRAAx] prime i := prime_of_isP Prf.hyp0
  have ipos := p_pos (prime_two hi)
  have I2 := Prf.andE₂ (lcm_valuation hi P)
  have dpos := pw_pos' ipos (succ (val i (lcmu P)))
  have q := SymmetryPointwise.quo_mul_le (x := LD P) dpos
  -- `v_i(L) ≥ 1`, so `i² ≤ i^{v+1}`
  have ii : C ⊢[PRAAx] le (i * i) (ex i P) := by
    refine .orE (zero_or_succ (val i (lcmu P))) ?_ ?_
    · have e1 : ((val i (lcmu P) ≐ zero) :: C) ⊢[PRAAx] ex i P ≐ i :=
        (congrAp2 powF (congrSucc Prf.hyp0) (.eqRefl i)).eqTrans
          ((pw_succ i zero).eqTrans ((congrMul (pw_zero i) (.eqRefl _)).eqTrans (one_mul i)))
      exact le_lt_absurd _ hiP.wk.wk (le_congr (.eqRefl _) e1 I2.wk)
    · let C' : List (Fm PTm n) := (val i (lcmu P) ≐ succ (pred (val i (lcmu P)))) :: C
      have h2 : C' ⊢[PRAAx] le (succ (succ zero)) (succ (val i (lcmu P))) :=
        Order.succ_le_succ (Common.one_le_of_pos Prf.hyp0)
      have p2 : C' ⊢[PRAAx] pw i (succ (succ zero)) ≐ i * i :=
        (pw_succ i (succ zero)).eqTrans (congrMul ((pw_succ i zero).eqTrans
          ((congrMul (pw_zero i) (.eqRefl _)).eqTrans (one_mul i))) (.eqRefl _))
      exact le_congr p2 (.eqRefl _) (PowerCleared.pw_le_exp ipos.wk h2)
  have a := le_mul_mono ii (le_refl (quo (LD P) (ex i P)))
  refine le_congr ?_ (.eqRefl _) (le_trans a (le_congr (mul_comm _ _) (.eqRefl _) q))
  ipra_lc (-(𝔞 i * 𝔞 i * 𝔞 (quo (LD P) (ex i P)))) * natEq (Prf.hyp0 : C ⊢[PRAAx] isP i ≐ one)

/-! ## The running bound -/

theorem p1_step {N P : PTm n} (ih : Γ ⊢[PRAAx] le (P * U N P) (N * LD P)) :
    Γ ⊢[PRAAx] le (P * U (succ N) P) (succ N * LD P) := by
  have sU := sum_succ' (Γ := Γ) uB N P
  rw [inst2_uB] at sU
  refine le_of_eq_add (d := monus (N * LD P) (P * U N P) +
    monus (LD P) (P * (isP N * quo (LD P) (ex N P)))) ?_
  ipra_lc natEq (eq_add_of_le ih) + natEq (eq_add_of_le (uA (Γ := Γ) N P)) - 𝔞 P * natEq sU

/-- `P · U(N) ≤ N L²`. -/
theorem phase1 (N P : PTm n) : Γ ⊢[PRAAx] le (P * U N P) (N * LD P) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (Syn.shift P * U (var 0) (Syn.shift P)) (var 0 * LD (Syn.shift P))) := by
    ipra_qfind (trivial) [subst_le, subst_ap2]
    · refine le_of_eq_add (d := zero) ?_
      ipra_lc (-(𝔞 P)) * natEq (sum_zero uB P)
    · let D : List (Fm PTm (n + 1)) :=
        le (Syn.shift P * U (var 0) (Syn.shift P)) (var 0 * LD (Syn.shift P)) :: Γ.map Fm.shift
      exact p1_step (Prf.hyp0 : D ⊢[PRAAx] _)
  have r := Prf.allE N hall
  simp only [subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero] at r
  exact r

/-! ## The telescoping invariant -/

/-- `J(N): m N P U(N+1) + m P L² ≤ N P L² + m N (m+1) L²`. -/
abbrev J (m N P : PTm n) : Fm PTm n :=
  le (m * N * P * U (succ N) P + m * P * LD P) (N * P * LD P + m * N * succ m * LD P)

theorem jbase {m N P : PTm n} (hmN : Γ ⊢[PRAAx] m ≐ N) : Γ ⊢[PRAAx] J m N P := by
  have p := phase1 (Γ := Γ) (succ N) P
  refine le_of_eq_add (d := m * N * monus (succ N * LD P) (P * U (succ N) P)) ?_
  ipra_lc 𝔞 m * 𝔞 N * natEq (eq_add_of_le p) -
    (𝔞 P * (𝔞 (lcmu P) * 𝔞 (lcmu P)) - 𝔞 m * 𝔞 N * (𝔞 (lcmu P) * 𝔞 (lcmu P))) * natEq hmN

theorem jstep {m N P : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hNP : Γ ⊢[PRAAx] le (succ N) P)
    (ih : Γ ⊢[PRAAx] J m N P) : Γ ⊢[PRAAx] J m (succ N) P := by
  have sU := sum_succ' (Γ := Γ) uB (succ N) P
  rw [inst2_uB] at sU
  refine le_cancel_pos hN (le_of_eq_add (d := succ N * monus (N * P * LD P + m * N * succ m * LD P)
      (m * N * P * U (succ N) P + m * P * LD P) +
    m * P * (monus (LD P) (succ N * succ N * (isP (succ N) * quo (LD P) (ex (succ N) P))) +
      succ N * (isP (succ N) * quo (LD P) (ex (succ N) P)))) ?_)
  ipra_lc (𝔞 N + 1) * natEq (eq_add_of_le ih) + 𝔞 m * 𝔞 P * natEq (eq_add_of_le (uB_sq (Γ := Γ) hNP)) -
    𝔞 N * 𝔞 m * (𝔞 N + 1) * 𝔞 P * natEq sU

/-- `Φ(N): m ≤ N → N ≤ P → J(N)`. -/
abbrev Phi (m N P : PTm n) : Fm PTm n := le m N ⟶ (le N P ⟶ J m N P)

theorem phi_step {m N P : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (ih : Γ ⊢[PRAAx] Phi m N P) :
    Γ ⊢[PRAAx] Phi m (succ N) P := by
  refine .impI (.impI ?_)
  let C : List (Fm PTm n) := le (succ N) P :: le m (succ N) :: Γ
  have hNP : C ⊢[PRAAx] le (succ N) P := Prf.hyp0
  have hmN : C ⊢[PRAAx] le m (succ N) := Prf.hyp1
  refine .orE (lt_or_eq_of_le hmN) ?_ (jbase Prf.hyp0)
  let C1 : List (Fm PTm n) := lt m (succ N) :: C
  have hmN' : C1 ⊢[PRAAx] le m N := Order.le_of_lt_succ Prf.hyp0
  have hNP' : C1 ⊢[PRAAx] le N P := le_of_lt hNP.wk
  have j := Prf.impE (Prf.impE (ih.wk.wk.wk : C1 ⊢[PRAAx] _) hmN') hNP'
  -- `N ≥ m ≥ 1`
  have hN : C1 ⊢[PRAAx] N ≐ succ (pred N) := by
    have h1 : C1 ⊢[PRAAx] le one N := le_trans (FactorVector.one_le_pos hm.wk.wk.wk) hmN'
    exact BinomialThree.pos_of_one_le h1
  exact jstep hN hNP.wk j

theorem phase2 {m P : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (N : PTm n) : Γ ⊢[PRAAx] Phi m N P := by
  have hall : Γ ⊢[PRAAx] Fm.all (Phi (Syn.shift m) (var 0) (Syn.shift P)) := by
    ipra_qfind (⟨le_QF _ _, le_QF _ _, le_QF _ _⟩) [subst_le, subst_ap2]
    · refine .impI (.impI ?_)
      have hm0 : (le zero P :: le m zero :: Γ) ⊢[PRAAx] le m zero := Prf.hyp1
      have h1 := le_trans (FactorVector.one_le_pos (hm.wk.wk : (le zero P :: le m zero :: Γ) ⊢[PRAAx] _)) hm0
      exact not_succ_le_self zero _ h1
    · let D : List (Fm PTm (n + 1)) := Phi (Syn.shift m) (var 0) (Syn.shift P) :: Γ.map Fm.shift
      have hm' : D ⊢[PRAAx] Syn.shift m ≐ succ (pred (Syn.shift m)) := by
        have b := hm.shift
        simp only [Fm.shift, Fm.subst_eq, ConciseIPRA.PTm.subst_succ, LeanProofs.IPRA.PTm.subst_pred] at b
        exact b.wk
      exact phi_step hm' (Prf.hyp0 : D ⊢[PRAAx] _)
  have r := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_mul, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at r
  exact r

/-! ## The bound -/

/-- `Σ_{p≤m²} p^{−a_p−1} ≤ 2/m`, cleared by `L²`: `m · U(m² + 1) ≤ 2 L²` for `m ≥ 1`. -/
theorem loss_sum {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] le (m * U (succ (m * m)) (m * m)) (two * LD (m * m)) := by
  have hP := Combinatorics.Binomial.pos_mul hm hm
  have hmP : Γ ⊢[PRAAx] le m (m * m) := by
    exact le_of_eq_add (d := m * pred m) (by ipra_lc 𝔞 m * natEq hm)
  have j := Prf.impE (Prf.impE (phase2 (P := m * m) hm (m * m)) hmP) (le_refl _)
  refine le_cancel_pos (Combinatorics.Binomial.pos_mul hP hP) (le_of_eq_add
    (d := monus ((m * m) * (m * m) * LD (m * m) + m * (m * m) * succ m * LD (m * m))
      (m * (m * m) * (m * m) * U (succ (m * m)) (m * m) + m * (m * m) * LD (m * m))) ?_)
  ipra_lc natEq (eq_add_of_le j)

/-! ## The product form -/

/-- `c_i = L² − u_i`. -/
abbrev cB : PTm 2 := monus (lcmu (var 1) * lcmu (var 1)) uB

theorem inst2_cB (i P : PTm n) : inst2 cB i P = monus (LD P) (isP i * quo (LD P) (ex i P)) := by simp [inst2]

/-- `u_i ≤ L²` for `P ≥ 1`. -/
theorem u_le {P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) (i : PTm n) :
    Γ ⊢[PRAAx] le (isP i * quo (LD P) (ex i P)) (LD P) := by
  have a : Γ ⊢[PRAAx] le (isP i * quo (LD P) (ex i P)) (P * (isP i * quo (LD P) (ex i P))) :=
    le_congr (one_mul _) (.eqRefl _) (le_mul_mono (FactorVector.one_le_pos hP) (le_refl (isP i * quo (LD P) (ex i P))))
  exact le_trans a (uA i P)

/-- `∏_{p≤m²}(1 − p^{−a_p−1}) ≥ 1 − 2/m`, cleared: `m L^{2(P+1)} ≤ m ∏_{i≤P} c_i + 2 L^{2(P+1)}`, `P = m²`. -/
theorem prod_lower {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] le (m * pw (LD (m * m)) (succ (m * m)))
      (m * ap2 (prodF cB) (succ (m * m)) (m * m) + two * pw (LD (m * m)) (succ (m * m))) := by
  have hP := Combinatorics.Binomial.pos_mul hm hm
  have hs : Syn.shift (LD (m * m)) = LD (Syn.shift m * Syn.shift m) := by simp [Syn.shift]
  have hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ (m * m))) ⟶
      (inst2 uB (var 0) (Syn.shift (m * m)) + inst2 cB (var 0) (Syn.shift (m * m)) ≐ Syn.shift (LD (m * m)))) := by
    refine .allI (.impI ?_)
    rw [inst2_uB, inst2_cB, hs]
    have hP' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift m * Syn.shift m ≐ succ (pred (Syn.shift m * Syn.shift m)) := by
      have b := hP.shift
      simp only [Fm.shift, Fm.subst_eq, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, LeanProofs.IPRA.PTm.subst_pred] at b
      exact b
    have hsm : Syn.shift (m * m) = Syn.shift m * Syn.shift m := by simp [Syn.shift]
    rw [hsm]
    exact (eq_add_of_le (u_le hP'.wk (var 0))).eqSymm
  have W := Analysis.WeierstrassProduct.weierstrass_lower (a := uB) (c := cB) (D := LD (m * m)) (x := m * m)
    (N := succ (m * m)) hb
  have L := loss_sum hm
  have Dpos := Combinatorics.Binomial.pos_mul (LcmUpto.lcmu_pos (Γ := Γ) (m * m)) (LcmUpto.lcmu_pos (m * m))
  refine le_cancel_pos Dpos (le_of_eq_add (d := m * monus (pw (LD (m * m)) (succ (m * m)) * U (succ (m * m)) (m * m) +
      LD (m * m) * ap2 (prodF cB) (succ (m * m)) (m * m)) (pw (LD (m * m)) (succ (succ (m * m)))) +
    pw (LD (m * m)) (succ (m * m)) * monus (two * LD (m * m)) (m * U (succ (m * m)) (m * m))) ?_)
  ipra_lc 𝔞 m * natEq (eq_add_of_le W) + 𝔞 (pw (LD (m * m)) (succ (m * m))) * natEq (eq_add_of_le L) +
    𝔞 m * natEq (pw_succ (LD (m * m)) (succ (m * m)))

end LeanProofs.IPRA.AnalyticNumberTheory.LcmBridgeLoss
