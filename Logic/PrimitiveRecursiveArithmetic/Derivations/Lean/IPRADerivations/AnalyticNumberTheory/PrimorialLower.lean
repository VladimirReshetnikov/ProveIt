import IPRADerivations.AnalyticNumberTheory.ChebyshevBounds

/-!
# The rough Chebyshev lower bound for the primorial, integer form

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, the lcm bridge of `thm:three`
(`lcm_bridge.tex`). With `P = m²`, the rough bound `ϑ(P) ≥ (P − 1) log 2 − log(P + 1) − m log P`
is the exponentiated integer inequality

  `2^{P−1} ≤ (P + 1) · P^m · ∏_{p ≤ P prime} p`        (`primorial_lower`),

assembled from

* `lcm_primorial`: `lcm(1, …, m²) ≤ (m²)^m · ∏_{p ≤ m²} p` (`ψ − ϑ ≤ m log P`): by valuations
  `lcm(1, …, m²) ∣ ∏_{i ≤ m} i^{[i prime] v_i(lcm)} · ∏_{p ≤ m²} p`, since a prime `q > m` has
  `q² > m²`, hence `v_q(lcm(1, …, m²)) ≤ 1` (`val_small`, `lcm_dvd`); each prime power factor
  `i^{v_i(lcm(1, …, P))}` is `≤ P` (`factor_le`), so the first product is `≤ P^m` (`small_le`);
* `two_pow_lcm`: `2^{P−1} ≤ (P + 1) · lcm(1, …, P)` for every `P`: with `h = ⌊P/2⌋`,
  `2^{P−1} ≤ 4^h ≤ (2h + 1) C(2h, h)` and `C(2h, h) ∣ lcm(1, …, 2h)` (`thm:binomial-lcm`).

The logarithmic side (`log 2`, `log P` enclosures) is the interval layer of the Robin modules.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PrimorialLower

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP isP_01 prime_of_isP isP_of_prime pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (f_zero f_one f_pos one_le_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.BinomialLcm (dvd_of_val_le PE XE val_PE inst2_XE inst2_PE PE_pos
  central_dvd_lcm)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (lcmu_le two_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrSg)
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The two products -/

/-- `v_i(lcm(1, …, x))`, over `0 = i`, `1 = x`. -/
abbrev vB : PTm 2 := val (var 0) (lcmu (var 1))

theorem inst2_vB (i x : PTm n) : inst2 vB i x = val i (lcmu x) := by simp [inst2]

theorem inst2_one (i x : PTm n) : inst2 (one : PTm 2) i x = one := by simp [inst2]

/-- `∏_{i ≤ m} i^{[i prime] v_i(lcm(1, …, P))}`: the prime powers of `lcm(1, …, P)` at primes `≤ m`. -/
abbrev Sm (m P : PTm n) : PTm n := ap2 (prodF (PE vB)) (succ m) P

/-- The primorial `∏_{p ≤ P prime} p = ∏_{i ≤ P} i^{[i prime]}`. -/
abbrev prim (P : PTm n) : PTm n := ap2 (prodF (PE one)) (succ P) P

theorem prim_pos (P : PTm n) : Γ ⊢[PRAAx] prim P ≐ succ (pred (prim P)) := PE_pos _ _ _

/-! ## Valuations -/

/-- A prime `q` has `v_q(lcm(1, …, m²)) ≤ [q ≤ m] v_q(lcm(1, …, m²)) + [q ≤ m²]`, both brackets
multiplied by `[q prime]`: for `q > m` the exponent is at most `1`, since `q² > m²`. -/
theorem val_small {q m : PTm n} (hq : Γ ⊢[PRAAx] prime q) :
    Γ ⊢[PRAAx] le (val q (lcmu (m * m)))
      (isP q * val q (lcmu (m * m)) * sg (monus (succ m) q) +
        isP q * one * sg (monus (succ (m * m)) q)) := by
  have hq2 := prime_two hq
  have qpos := p_pos hq2
  have ip := isP_of_prime hq
  have I := lcm_valuation hq (m * m)
  have A1 := Prf.andE₁ I
  refine .orE (zero_or_succ (val q (lcmu (m * m)))) (le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le _)) ?_
  let C : List (Fm PTm n) := (val q (lcmu (m * m)) ≐ succ (pred (val q (lcmu (m * m))))) :: Γ
  have Ep : C ⊢[PRAAx] val q (lcmu (m * m)) ≐ succ (pred (val q (lcmu (m * m)))) := Prf.hyp0
  have sE : C ⊢[PRAAx] sg (val q (lcmu (m * m))) ≐ one := (congrSg Ep).eqTrans (sg_succ _)
  have pE : C ⊢[PRAAx] le (pw q (val q (lcmu (m * m)))) (m * m) :=
    le_congr ((congrMul sE (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _) A1.wk
  have l1E : C ⊢[PRAAx] le one (val q (lcmu (m * m))) := one_le_pos Ep
  have qE : C ⊢[PRAAx] le q (pw q (val q (lcmu (m * m)))) :=
    le_congr (pw_one q) (.eqRefl _) (PowerCleared.pw_le_exp qpos.wk l1E)
  have s2 : C ⊢[PRAAx] sg (monus (succ (m * m)) q) ≐ one :=
    sg_lt ((succ_monus_succ _ _).eqTrans (le_trans qE pE))
  refine .orE (lt_or_le q (succ m)) ?_ ?_
  · -- `q ≤ m`: the first bracket is the whole exponent
    let C1 : List (Fm PTm n) := lt q (succ m) :: C
    refine le_of_eq_add (d := isP q * one * sg (monus (succ (m * m)) q)) ?_
    ipra_lc (𝔞 (val q (lcmu (m * m))) * 𝔞 (sg (monus (succ m) q))) * natEq (ip.wk.wk : C1 ⊢[PRAAx] _) +
      𝔞 (val q (lcmu (m * m))) * natEq (sg_lt (Prf.hyp0 : C1 ⊢[PRAAx] lt q (succ m)))
  · -- `m < q`: the exponent is at most `1`
    let C2 : List (Fm PTm n) := le (succ m) q :: C
    have hm : C2 ⊢[PRAAx] le (succ m) q := Prf.hyp0
    have one_rhs : C2 ⊢[PRAAx] le one (isP q * val q (lcmu (m * m)) * sg (monus (succ m) q) +
        isP q * one * sg (monus (succ (m * m)) q)) := by
      refine le_of_eq_add (d := isP q * val q (lcmu (m * m)) * sg (monus (succ m) q)) ?_
      ipra_lc 𝔞 (sg (monus (succ (m * m)) q)) * natEq (ip.wk.wk : C2 ⊢[PRAAx] _) + natEq (s2.wk : C2 ⊢[PRAAx] _)
    refine .orE (lt_or_le one (val q (lcmu (m * m)))) ?_ (le_trans Prf.hyp0 one_rhs.wk)
    -- `2 ≤ v`: `(m + 1)² ≤ q² ≤ q^v ≤ m²`, absurd
    let C3 : List (Fm PTm n) := lt one (val q (lcmu (m * m))) :: C2
    have h2 : C3 ⊢[PRAAx] le two (val q (lcmu (m * m))) := Prf.hyp0
    have p1 := le_trans (PowerCleared.pw_le_exp qpos.wk.wk.wk h2) pE.wk.wk
    have p2 : C3 ⊢[PRAAx] le (q * q) (m * m) :=
      le_congr ((pw_succ q one).eqTrans (congrMul (pw_one q) (.eqRefl _))) (.eqRefl _) p1
    have p3 := le_trans (le_mul_mono hm.wk hm.wk) p2
    have p4 : C3 ⊢[PRAAx] le (succ (m * m)) (succ m * succ m) :=
      le_of_eq_add (d := two * m) (by ipra_ring)
    exact not_succ_le_self _ _ (le_trans p4 p3)

/-- `lcm(1, …, m²) ∣ ∏_{i ≤ m} i^{[i prime] v_i(lcm(1, …, m²))} · ∏_{p ≤ m²} p`. -/
theorem lcm_dvd (m : PTm n) : Γ ⊢[PRAAx] dvd (lcmu (m * m)) (Sm m (m * m) * prim (m * m)) := by
  have pp := Combinatorics.Binomial.pos_mul (PE_pos (Γ := Γ) vB (succ m) (m * m)) (prim_pos (Γ := Γ) (m * m))
  have hs1 : Syn.shift (lcmu (m * m)) = lcmu (Syn.shift m * Syn.shift m) := by simp [Syn.shift]
  have hs2 : Syn.shift (Sm m (m * m) * prim (m * m)) =
      Sm (Syn.shift m) (Syn.shift m * Syn.shift m) * prim (Syn.shift m * Syn.shift m) := by simp [Syn.shift]
  refine dvd_of_val_le (N := succ (lcmu (m * m) + Sm m (m * m) * prim (m * m))) (lcmu_pos _) pp
    ((succ_monus_succ _ _).eqTrans (le_add_right _ _)) ((succ_monus_succ _ _).eqTrans (le_add_left _ _))
    (.allI (.impI (.impI ?_)))
  rw [hs1, hs2]
  let Q : List (Fm PTm (n + 1)) :=
    (isP (var 0) ≐ one) :: lt (var 0) (Syn.shift (succ (lcmu (m * m) + Sm m (m * m) * prim (m * m)))) ::
      Γ.map Fm.shift
  have hv : Q ⊢[PRAAx] prime (var 0) := prime_of_isP Prf.hyp0
  have vm := val_mul hv (PE_pos vB (succ (Syn.shift m)) (Syn.shift m * Syn.shift m))
    (prim_pos (Syn.shift m * Syn.shift m))
  have v1 := val_PE hv vB (succ (Syn.shift m)) (Syn.shift m * Syn.shift m)
  have v2 := val_PE hv one (succ (Syn.shift m * Syn.shift m)) (Syn.shift m * Syn.shift m)
  rw [inst2_XE, inst2_vB] at v1
  rw [inst2_XE, inst2_one] at v2
  exact le_congr (.eqRefl _) (vm.eqTrans (congrAdd v1 v2)).eqSymm (val_small hv)

/-! ## The bound on the small-prime product -/

/-- Each factor `i^{[i prime] v_i(lcm(1, …, P))}` is at most `P`, for `P ≥ 1`. -/
theorem factor_le {P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) (i : PTm n) :
    Γ ⊢[PRAAx] le (pw i (isP i * val i (lcmu P))) P := by
  have o := one_le_pos hP
  refine .orE (isP_01 i) (le_congr (f_zero Prf.hyp0).eqSymm (.eqRefl _) o.wk) ?_
  let C : List (Fm PTm n) := (isP i ≐ one) :: Γ
  have hi : C ⊢[PRAAx] prime i := prime_of_isP Prf.hyp0
  refine le_congr (f_one Prf.hyp0).eqSymm (.eqRefl _) ?_
  have A1 := Prf.andE₁ (lcm_valuation hi P)
  refine .orE (zero_or_succ (val i (lcmu P))) ?_ ?_
  · exact le_congr ((congrAp2 powF Prf.hyp0 (.eqRefl i)).eqTrans (pw_zero i)).eqSymm (.eqRefl _) o.wk.wk
  · have sE : ((val i (lcmu P) ≐ succ (pred (val i (lcmu P)))) :: C) ⊢[PRAAx] sg (val i (lcmu P)) ≐ one :=
      (congrSg Prf.hyp0).eqTrans (sg_succ _)
    exact le_congr ((congrMul sE (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _) A1.wk

/-- Bound the valuation product by an envelope that absorbs the next factor at each step. -/
theorem valuation_prod_le_of_step (bound : PTm 2) (P j : PTm n)
    (h0 : Γ ⊢[PRAAx] le one (inst2 bound zero P))
    (hs : Γ.map Fm.shift ⊢[PRAAx]
      le (inst2 bound (var 0) (Syn.shift P) * inst2 (PE vB) (succ (var 0)) (Syn.shift P))
        (inst2 bound (succ (var 0)) (Syn.shift P))) :
    Γ ⊢[PRAAx] le (ap2 (prodF (PE vB)) (succ j) P) (inst2 bound j P) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (ap2 (prodF (PE vB)) (succ (var 0)) (Syn.shift P))
      (inst2 bound (var 0) (Syn.shift P))) := by
    ipra_qfind [subst_le, subst_ap2, subst_inst2]
    · have e := (prod_succ (Γ := Γ) (PE vB) zero P).eqTrans
        (congrMul (prod_zero _ _) (.eqRefl _))
      change Γ ⊢[PRAAx] _ ≐ one * inst2 (PE vB) zero P at e
      rw [inst2_PE, inst2_XE, inst2_vB] at e
      have f0 : Γ ⊢[PRAAx] pw zero (isP zero * val zero (lcmu P)) ≐ one := f_zero Mobius.isP_zero
      exact le_congr (e.eqTrans ((one_mul _).eqTrans f0)).eqSymm (.eqRefl _) h0
    · exact le_congr (prod_succ (PE vB) (succ (var 0)) (Syn.shift P)).eqSymm (.eqRefl _)
        (le_trans (mul_le_mul_right _ Prf.hyp0) hs.wk)
  simpa only [subst_le, subst_ap2, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ] using Prf.allE j hall

/-- `∏_{i ≤ j} i^{[i prime] v_i(lcm(1, …, P))} ≤ P^j` for `P ≥ 1`: the factor at `i = 0` is `1`. -/
theorem small_le {P : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) (j : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (prodF (PE vB)) (succ j) P) (pw P j) := by
  have h := valuation_prod_le_of_step (Γ := Γ) (pw (var 1) (var 0)) P j (by
    simp [inst2]
    exact le_congr (.eqRefl _) (pw_zero P).eqSymm (le_refl _)) (by
    rw [inst2_PE, inst2_XE, inst2_vB]
    simp [inst2]
    exact le_congr (.eqRefl _) (pw_succ _ _).eqSymm
      (le_mul_mono (le_refl _) (factor_le (Common.pos_shift hP) (succ (var 0)))))
  simpa [inst2] using h

/-! ## The three bounds -/

/-- `ψ(m²) − ϑ(m²) ≤ m log m²`: `lcm(1, …, m²) ≤ (m²)^m · ∏_{p ≤ m²} p` for `m ≥ 1`. -/
theorem lcm_primorial {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] le (lcmu (m * m)) (pw (m * m) m * prim (m * m)) := by
  have hP := Combinatorics.Binomial.pos_mul hm hm
  have pp := Combinatorics.Binomial.pos_mul (PE_pos (Γ := Γ) vB (succ m) (m * m)) (prim_pos (Γ := Γ) (m * m))
  have l1 := dvd_le' (lcmu_pos _) (lcm_dvd m) pp
  exact le_trans l1 (le_mul_mono (small_le hP m) (le_refl _))

/-- `ψ(P) ≥ (P − 1) log 2 − log(P + 1)`: `2^{P−1} ≤ (P + 1) · lcm(1, …, P)` for every `P`. -/
theorem two_pow_lcm (P : PTm n) : Γ ⊢[PRAAx] le (pw two (pred P)) (succ P * lcmu P) := by
  have dvP : Γ ⊢[PRAAx] P ≐ two * quo P two + rem P two := GcdFiber.div_eq two_pos'
  have rl : Γ ⊢[PRAAx] le (rem P two) one :=
    (succ_monus_succ _ _).eqSymm.eqTrans (Multiplicative.rem_lt' two_pos' P)
  have l2 : Γ ⊢[PRAAx] le (two * quo P two) P := le_of_eq_add (d := rem P two) dvP
  have hp : Γ ⊢[PRAAx] le (pred P) (two * quo P two) := by
    refine .orE (zero_or_succ P) ?_ ?_
    · exact le_congr ((congrPred Prf.hyp0).eqTrans pred_zero).eqSymm (.eqRefl _) (zero_le _)
    · let C : List (Fm PTm n) := (P ≐ succ (pred P)) :: Γ
      refine le_of_eq_add (d := monus one (rem P two)) ?_
      ipra_lc natEq (Prf.hyp0 : C ⊢[PRAAx] P ≐ succ (pred P)) - natEq (dvP.wk : C ⊢[PRAAx] _) +
        natEq (eq_add_of_le (rl.wk : C ⊢[PRAAx] _))
  have a1 := PowerCleared.pw_le_exp two_pos' hp
  have a2 := Combinatorics.CentralBinomial.central_lower (Γ := Γ) (quo P two)
  have cpos := BinomialThree.pos_of_one_le (Combinatorics.CentralBinomial.central_pos (Γ := Γ) (quo P two))
  have a3 : Γ ⊢[PRAAx] le (binom (two * quo P two) (quo P two)) (lcmu P) :=
    le_trans (dvd_le' cpos (central_dvd_lcm (quo P two)) (lcmu_pos _)) (lcmu_le l2)
  have a4 : Γ ⊢[PRAAx] le (succ (two * quo P two)) (succ P) := (succ_monus_succ _ _).eqTrans l2
  exact le_trans a1 (le_trans a2 (le_mul_mono a4 a3))

/-- The rough Chebyshev bound of the lcm bridge, `ϑ(m²) ≥ (m² − 1) log 2 − log(m² + 1) − m log m²`:
`2^{m²−1} ≤ (m² + 1) · (m²)^m · ∏_{p ≤ m²} p` for `m ≥ 1`. -/
theorem primorial_lower {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] le (pw two (pred (m * m))) (succ (m * m) * (pw (m * m) m * prim (m * m))) :=
  le_trans (two_pow_lcm _) (le_mul_mono (le_refl _) (lcm_primorial hm))

end LeanProofs.IPRA.AnalyticNumberTheory.PrimorialLower

export_ipra AnalyticNumberTheory.PrimorialLower (prim prim_pos)
