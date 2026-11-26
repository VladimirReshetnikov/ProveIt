import IPRADerivations.Analysis.Series.Basel.BaselAverages
import IPRADerivations.Analysis.RationalArithmetic.PowerSums
import IPRADerivations.Core.LinearCombination

/-!
# The crucial finite comparison of the Basel packet

Packet: `analysis/basel_ipra`, `paper/basel_ipra.tex`, Sections `sec:triangle` and `sec:difference`:
`A_N = ∑_{j<N} (−1)^j/(2j+1)`, `O_N = ∑_{j<N} 1/(2j+1)²`, `H_N = ∑_{j<N} 1/(2j+1)`.

Everything is cleared by `F = L!` (with `2N + 1 ≤ L`), `g_j = F/(2j+1)`, and signed sums are kept as pairs of
natural numbers split by parity: `A⁺(N) = ∑_{j<N} (1 ∸ par j) g_j`, `A⁻(N) = ∑_{j<N} par j · g_j`, so that
`F A_N = A⁺ − A⁻`.

The chain:

* `lift3`, `inst2_lift3`: a body over `(i, N, L)` read as a body over `(i, ⟨N, L⟩)`;
* `p_add`, `q_add`: the parity of a sum, `par (a + b) = (1 ∸ par a) par b + par a (1 ∸ par b)`;
* `shift_rel`, `tail_bound`: `|A_{K+m+1} − A_K| ≤ 1/(2K+1)`, from `lem:decreasing` applied to the weights
  `g_{K+i}`;
* `diagonal` (`eq:diagonal` at `d = N`): `N ∑_{i<N} g_i g_{N−1−i} = F H(N)`;
* `sum_lin`: `∑ f + c ∑ h = ∑ k` from the pointwise identity, for bodies with different parameters;
* `refl`: `(−1)^M ∑_{i<M} (−1)^i g_{M−i} = A(M + 1) − g_0`;
* `b_step` (`eq:pfminus`): `b_d(N + 1) + 2 g_N g_{N−d} = b_d(N)`, and `E_step`, `T_step`: the increments of
  `E_N` and of the triangle `T_N = ∑_{i<N} s_i A_{N−1−i}` (`s_i = (−1)^i/(2i+1)`), the latter being
  `(−1)^{N−1} ∑_{i<N} g_i g_{N−1−i}`;
* `second` (`eq:second`): `A_N² + T_N = O_N + E_N`, by induction on `N`; the step is the ring identity
  `phi_ring`, so that the paper's two diagonal decompositions of the square are never formed;
* `omitted`, `omitted_bound` (`lem:D`, `eq:D`): `D_N = A_N² − T_N = ∑_{i<N} s_i (A_N − A_{N−1−i})`, each term
  bounded by `g_i g_{N−1−i}` (`tail_bound`), so `|D_N| ≤ H_N/N` by the diagonal identity;
* `E_bound` (`lem:E` for every `N ≥ 1`) and `core` (`prop:core`, `eq:core`): `2A_N² − O_N = D_N + E_N`, so
  `|2A_N² − O_N| ≤ 2H_N/N`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BaselCore

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.BaselFinite (odd_pos tB inst2_t T Ev Od Ev_succ Od_succ Dec alt_decreasing
  par_sum par_prod compl_succ)
open LeanProofs.IPRA.Analysis.BaselAverages (g H)
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (quo_anti)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Bodies with two parameters -/

/-- A body over `0 = i`, `1 = N`, `2 = L`, read over `0 = i`, `1 = ⟨N, L⟩`. -/
def lift3 (K : PTm 3) : PTm 2 := Syn.subst ![var 0, fstT (var 1), sndT (var 1)] K

theorem inst2_lift3 (K : PTm 3) (i N L : PTm n) :
    Γ ⊢[PRAAx] inst2 (lift3 K) i (pairT N L) ≐ Syn.subst ![i, N, L] K := by
  have e : inst2 (lift3 K) i (pairT N L) = Syn.subst ![i, fstT (pairT N L), sndT (pairT N L)] K := by
    simp only [inst2, lift3, Syn.subst_subst]
    congr 1; funext j; fin_cases j <;> simp
  rw [e]
  exact Prf.eqCongr K fun j => by
    fin_cases j
    · exact .eqRefl _
    · exact fst_pair _ _
    · exact snd_pair _ _

/-! ## The parity of a sum -/

/-- Variables: `0 = b`, `1 = a`. `par (a + b) + 2 par a par b = par a + par b`. -/
private abbrev paF : Fm PTm 2 :=
  par (var 1 + var 0) + two * (par (var 1) * par (var 0)) ≐ par (var 1) + par (var 0)

private theorem pa₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] paF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap1, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have a := natEq (congrAp1 parF (add_zero (Γ := []) (var 0 : PTm 1)))
    have z := natEq (par_zero (Γ := ([] : List (Fm PTm 1))))
    apply deriveNat; ipra_simps
    linear_combination a + (2 * 𝔞 (par (var 0 : PTm 1)) - 1) * z
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, subst_ap1, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have ih := natEq (Prf.hyp0 : [paF] ⊢[PRAAx] paF)
    have a := natEq ((congrAp1 parF (add_succ (Γ := [paF]) (var 1 : PTm 2) (var 0))).eqTrans (par_succ _))
    have b := natEq (par_succ (Γ := [paF]) (var 0 : PTm 2))
    have s1 := natEq (par_sum (Γ := [paF]) ((var 1 : PTm 2) + var 0))
    have s2 := natEq (par_sum (Γ := [paF]) (var 0 : PTm 2))
    apply deriveNat; ipra_simps
    linear_combination a + (2 * 𝔞 (par (var 1 : PTm 2)) - 1) * b + s1 + (2 * 𝔞 (par (var 1 : PTm 2)) - 1) * s2 - ih

theorem par_add (a b : PTm n) : Γ ⊢[PRAAx] par (a + b) + two * (par a * par b) ≐ par a + par b := by
  have i := inst (Γ := Γ) pa₀ (![b, a] : Fin 2 → PTm n)
  simpa using i

theorem p_add (a b : PTm n) :
    Γ ⊢[PRAAx] par (a + b) ≐ monus one (par a) * par b + par a * monus one (par b) := by
  ipra_lc natEq (par_add (Γ := Γ) a b) - 𝔞 (par b) * natEq (par_sum (Γ := Γ) a) -
    𝔞 (par a) * natEq (par_sum (Γ := Γ) b)

theorem q_add (a b : PTm n) :
    Γ ⊢[PRAAx] monus one (par (a + b)) ≐ monus one (par a) * monus one (par b) + par a * par b := by
  ipra_lc natEq (par_sum (Γ := Γ) (a + b)) - natEq (par_add (Γ := Γ) a b) +
    (𝔞 (par b) - 1) * natEq (par_sum (Γ := Γ) a) - 𝔞 (monus one (par a)) * natEq (par_sum (Γ := Γ) b)

/-! ## Signed prefix sums and shifted weights -/

/-- `A⁺(M) = ∑_{j<M} (1 ∸ par j) g_j`, `A⁻(M) = ∑_{j<M} par j · g_j`. -/
abbrev Ap (M L : PTm n) : PTm n := Ev tB M (fact L)
abbrev Am (M L : PTm n) : PTm n := Od tB M (fact L)

theorem Ap_succ (M L : PTm n) : Γ ⊢[PRAAx] Ap (succ M) L ≐ Ap M L + monus one (par M) * g M L := by
  have h := Ev_succ (Γ := Γ) tB M (fact L)
  rw [inst2_t] at h
  exact h

theorem Am_succ (M L : PTm n) : Γ ⊢[PRAAx] Am (succ M) L ≐ Am M L + par M * g M L := by
  have h := Od_succ (Γ := Γ) tB M (fact L)
  rw [inst2_t] at h
  exact h

/-- `g_{K+i}` over `0 = i`, `1 = K`, `2 = L`. -/
abbrev wSK : PTm 3 := quo (fact (var 2)) (succ (two * (var 1 + var 0)))
abbrev wS : PTm 2 := lift3 wSK

theorem inst_wS (i K L : PTm n) : Γ ⊢[PRAAx] inst2 wS i (pairT K L) ≐ g (K + i) L := by
  have h := inst2_lift3 (Γ := Γ) wSK i K L
  simp at h
  exact h

/-- The parity parts `E'(j)`, `O'(j)` of `∑_{i<j} (−1)^i g_{K+i}`. -/
abbrev Ep (j K L : PTm n) : PTm n := Ev wS j (pairT K L)
abbrev Om (j K L : PTm n) : PTm n := Od wS j (pairT K L)

theorem rel_step {j K L : PTm n}
    (ih : Γ ⊢[PRAAx] (Ap (K + j) L ≐ Ap K L + monus one (par K) * Ep j K L + par K * Om j K L) ⋏
      (Am (K + j) L ≐ Am K L + monus one (par K) * Om j K L + par K * Ep j K L)) :
    Γ ⊢[PRAAx] (Ap (K + succ j) L ≐ Ap K L + monus one (par K) * Ep (succ j) K L + par K * Om (succ j) K L) ⋏
      (Am (K + succ j) L ≐ Am K L + monus one (par K) * Om (succ j) K L + par K * Ep (succ j) K L) := by
  have i1 := natEq (Prf.andE₁ ih); have i2 := natEq (Prf.andE₂ ih)
  have A1 := natEq ((congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.eB tB)) (add_succ (Γ := Γ) K j)
    (.eqRefl (fact L))).eqTrans (Ap_succ (K + j) L))
  have A2 := natEq ((congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.oB tB)) (add_succ (Γ := Γ) K j)
    (.eqRefl (fact L))).eqTrans (Am_succ (K + j) L))
  have E1 := natEq (Ev_succ (Γ := Γ) wS j (pairT K L)); have O1 := natEq (Od_succ (Γ := Γ) wS j (pairT K L))
  have qa := natEq (q_add (Γ := Γ) K j); have pa := natEq (p_add (Γ := Γ) K j)
  refine .andI ?_ ?_
  · ipra_lc A1 + i1 - 𝔞 (monus one (par K)) * E1 - 𝔞 (par K) * O1 -
      (𝔞 (monus one (par K)) * 𝔞 (monus one (par j)) + 𝔞 (par K) * 𝔞 (par j)) * natEq (inst_wS (Γ := Γ) j K L) +
      𝔞 (g (K + j) L) * qa
  · ipra_lc A2 + i2 - 𝔞 (monus one (par K)) * O1 - 𝔞 (par K) * E1 -
      (𝔞 (monus one (par K)) * 𝔞 (par j) + 𝔞 (par K) * 𝔞 (monus one (par j))) * natEq (inst_wS (Γ := Γ) j K L) +
      𝔞 (g (K + j) L) * pa

/-- Variables: `0 = j`, `1 = K`, `2 = L`. -/
private abbrev relF : Fm PTm 3 :=
  (Ap (var 1 + var 0) (var 2) ≐ Ap (var 1) (var 2) + monus one (par (var 1)) * Ep (var 0) (var 1) (var 2) +
      par (var 1) * Om (var 0) (var 1) (var 2)) ⋏
    (Am (var 1 + var 0) (var 2) ≐ Am (var 1) (var 2) + monus one (par (var 1)) * Om (var 0) (var 1) (var 2) +
      par (var 1) * Ep (var 0) (var 1) (var 2))

theorem rel_zero (K L : PTm n) :
    Γ ⊢[PRAAx] (Ap (K + zero) L ≐ Ap K L + monus one (par K) * Ep zero K L + par K * Om zero K L) ⋏
      (Am (K + zero) L ≐ Am K L + monus one (par K) * Om zero K L + par K * Ep zero K L) := by
  have a := natEq (congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.eB tB)) (add_zero (Γ := Γ) K)
    (.eqRefl (fact L)))
  have b := natEq (congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.oB tB)) (add_zero (Γ := Γ) K)
    (.eqRefl (fact L)))
  refine .andI ?_ ?_
  · ipra_lc a -
      𝔞 (monus one (par K)) * natEq (sum_zero (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.eB wS) (pairT K L)) -
      𝔞 (par K) * natEq (sum_zero (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.oB wS) (pairT K L))
  · ipra_lc b -
      𝔞 (monus one (par K)) * natEq (sum_zero (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.oB wS) (pairT K L)) -
      𝔞 (par K) * natEq (sum_zero (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.eB wS) (pairT K L))

private theorem rel₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] relF := by
  refine ind _ ⟨trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_and, Fm.subst_eq, subst_ap2, subst_ap1, subst_pairT, PTm.subst_add, PTm.subst_mul,
      PTm.subst_monus, Syn.subst_var, Syn.inst_zero, Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact rel_zero _ _
  · simp only [Fm.subst_and, Fm.subst_eq, subst_ap2, subst_ap1, subst_pairT, PTm.subst_add, PTm.subst_mul,
      PTm.subst_monus, Syn.subst_var, Syn.repl_zero, repl_one, repl_two, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact rel_step Prf.hyp0

/-- `shift_rel`: `A^±(K + j) = A^±(K) + (1 ∸ par K) E'^±(j) + par K · E'^∓(j)`. -/
theorem shift_rel (j K L : PTm n) :
    Γ ⊢[PRAAx] (Ap (K + j) L ≐ Ap K L + monus one (par K) * Ep j K L + par K * Om j K L) ⋏
      (Am (K + j) L ≐ Am K L + monus one (par K) * Om j K L + par K * Ep j K L) := by
  have i := inst (Γ := Γ) rel₀ (![j, K, L] : Fin 3 → PTm n)
  simp at i
  exact i

/-! ## The alternating tail bound -/

theorem dec_wS (m K L : PTm n) : Γ ⊢[PRAAx] Dec wS (succ m) (pairT K L) := by
  refine .allI (.impI ?_)
  rw [shift_pairT]
  refine le_congr (inst_wS _ _ _).eqSymm (inst_wS _ _ _).eqSymm ?_
  refine quo_anti (odd_pos _) (le_of_eq_add (d := two) ?_)
  ipra_ring

/-- `tail_bound`: `|A_{K+m+1} − A_K| ≤ 1/(2K+1)`, cleared:
`A⁺(K+m+1) + A⁻(K) ≤ A⁻(K+m+1) + A⁺(K) + g_K` and symmetrically. -/
theorem tail_bound (K m L : PTm n) :
    Γ ⊢[PRAAx] le (Ap (K + succ m) L + Am K L) (Am (K + succ m) L + Ap K L + g K L) ⋏
      le (Am (K + succ m) L + Ap K L) (Ap (K + succ m) L + Am K L + g K L) := by
  have r := shift_rel (Γ := Γ) (succ m) K L
  have ad := alt_decreasing wS (dec_wS (Γ := Γ) m K L)
  have w0P : Γ ⊢[PRAAx] inst2 wS zero (pairT K L) ≐ g K L := (inst_wS (Γ := Γ) zero K L).eqTrans
    (congrAp2 quoF (.eqRefl _) (congrSucc (congrMul (.eqRefl two) (add_zero K))))
  refine .orE (par_cases K) ?_ ?_
  · have hp := natEq (Prf.hyp0 : ((par K ≐ zero) :: Γ) ⊢[PRAAx] _)
    have w0 := natEq (w0P.wk (ψ := par K ≐ zero))
    have c := natEq ((congrMonus (.eqRefl one) (Prf.hyp0 : ((par K ≐ zero) :: Γ) ⊢[PRAAx] _)).eqTrans (monus_zero _))
    have r1 := natEq ((Prf.andE₁ r).wk (ψ := par K ≐ zero)); have r2 := natEq ((Prf.andE₂ r).wk (ψ := par K ≐ zero))
    have d1 := natEq ((eq_add_of_le (Prf.andE₁ ad)).wk (ψ := par K ≐ zero))
    have d2 := natEq ((eq_add_of_le (Prf.andE₂ ad)).wk (ψ := par K ≐ zero))
    refine .andI (le_of_eq_add (d := monus (Om (succ m) K L + inst2 wS zero (pairT K L)) (Ep (succ m) K L)) ?_)
      (le_of_eq_add (d := monus (Ep (succ m) K L) (Om (succ m) K L) + g K L) ?_)
    · ipra_lc r2 - r1 + (𝔞 (Om (succ m) K L) - 𝔞 (Ep (succ m) K L)) * c +
        (𝔞 (Ep (succ m) K L) - 𝔞 (Om (succ m) K L)) * hp + d2 - w0
    · ipra_lc r1 - r2 + (𝔞 (Ep (succ m) K L) - 𝔞 (Om (succ m) K L)) * c +
        (𝔞 (Om (succ m) K L) - 𝔞 (Ep (succ m) K L)) * hp + d1
  · have hp := natEq (Prf.hyp0 : ((par K ≐ one) :: Γ) ⊢[PRAAx] _)
    have w0 := natEq (w0P.wk (ψ := par K ≐ one))
    have c := natEq ((congrMonus (.eqRefl one) (Prf.hyp0 : ((par K ≐ one) :: Γ) ⊢[PRAAx] _)).eqTrans (monus_self _))
    have r1 := natEq ((Prf.andE₁ r).wk (ψ := par K ≐ one)); have r2 := natEq ((Prf.andE₂ r).wk (ψ := par K ≐ one))
    have d1 := natEq ((eq_add_of_le (Prf.andE₁ ad)).wk (ψ := par K ≐ one))
    have d2 := natEq ((eq_add_of_le (Prf.andE₂ ad)).wk (ψ := par K ≐ one))
    refine .andI (le_of_eq_add (d := monus (Ep (succ m) K L) (Om (succ m) K L) + g K L) ?_)
      (le_of_eq_add (d := monus (Om (succ m) K L + inst2 wS zero (pairT K L)) (Ep (succ m) K L)) ?_)
    · ipra_lc r2 - r1 + (𝔞 (Ep (succ m) K L) - 𝔞 (Om (succ m) K L)) * hp +
        (𝔞 (Om (succ m) K L) - 𝔞 (Ep (succ m) K L)) * c + d1
    · ipra_lc r1 - r2 + (𝔞 (Om (succ m) K L) - 𝔞 (Ep (succ m) K L)) * hp +
        (𝔞 (Ep (succ m) K L) - 𝔞 (Om (succ m) K L)) * c + d2 - w0

/-! ## The diagonal identity for `F = L!` -/

/-- `g_i` and `g_{N−1−i}` over `0 = i`, `1 = N`, `2 = L`. -/
abbrev gK : PTm 3 := quo (fact (var 2)) (succ (two * var 0))
abbrev rK : PTm 3 := quo (fact (var 2)) (succ (two * monus (var 1) (succ (var 0))))
/-- `g_i g_{N−1−i}`, `2N g_i g_{N−1−i}`, `g_i + g_{N−1−i}`. -/
abbrev cv : PTm 2 := lift3 (gK * rK)
abbrev dc : PTm 2 := lift3 ((two * var 1) * (gK * rK))
abbrev ad : PTm 2 := addBody (lift3 gK) (lift3 rK)

/-- `Conv(N) = ∑_{i<N} g_i g_{N−1−i}`. -/
abbrev Conv (N L : PTm n) : PTm n := ap2 (sumF cv) N (pairT N L)

theorem inst_g (i N L : PTm n) : Γ ⊢[PRAAx] inst2 (lift3 gK) i (pairT N L) ≐ g i L := by
  have h := inst2_lift3 (Γ := Γ) gK i N L
  simp at h
  exact h

theorem inst_r (i N L : PTm n) : Γ ⊢[PRAAx] inst2 (lift3 rK) i (pairT N L) ≐ g (monus N (succ i)) L := by
  have h := inst2_lift3 (Γ := Γ) rK i N L
  simp at h
  exact h

theorem inst_cv (i N L : PTm n) : Γ ⊢[PRAAx] inst2 cv i (pairT N L) ≐ g i L * g (monus N (succ i)) L := by
  have h := inst2_lift3 (Γ := Γ) (gK * rK) i N L
  simp at h
  exact h

theorem inst_dc (i N L : PTm n) :
    Γ ⊢[PRAAx] inst2 dc i (pairT N L) ≐ (two * N) * (g i L * g (monus N (succ i)) L) := by
  have h := inst2_lift3 (Γ := Γ) ((two * var 1) * (gK * rK)) i N L
  simp at h
  exact h

/-- `2i + 1 ∣ L!` for `i < N`, `2N ≤ L`. -/
theorem odd_dvd_L {i N L : PTm n} (hi : Γ ⊢[PRAAx] lt i N) (hL : Γ ⊢[PRAAx] le (two * N) L) :
    Γ ⊢[PRAAx] dvd (succ (two * i)) (fact L) := by
  refine LeanProofs.IPRA.AnalyticNumberTheory.Primes.dvd_fact (le_trans ?_ hL)
  refine le_of_eq_add (d := succ (two * monus N (succ i))) ?_
  ipra_lc 2 * natEq (eq_add_of_le hi)

theorem dc_pt {i N L : PTm n} (hi : Γ ⊢[PRAAx] lt i N) (hL : Γ ⊢[PRAAx] le (two * N) L) :
    Γ ⊢[PRAAx] (two * N) * (g i L * g (monus N (succ i)) L) ≐ fact L * (g i L + g (monus N (succ i)) L) := by
  have hk : Γ ⊢[PRAAx] lt (monus N (succ i)) N :=
    le_of_eq_add (d := i) ((eq_add_of_le hi).eqTrans (by ipra_ring))
  refine LeanProofs.IPRA.Analysis.BaselDiagonal.pair_pt (odd_pos _) (odd_pos _) (odd_dvd_L hi hL)
    (odd_dvd_L hk hL) ?_
  ipra_lc -2 * natEq (eq_add_of_le hi)

/-- The diagonal identity `(eq:diagonal)` at `d = N`, cleared by `F = L!` with `2N ≤ L`:
`N ∑_{i<N} g_i g_{N−1−i} = F H(N)`, i.e. `∑_{i<N} 1/((2i+1)(2N−2i−1)) = H_N/N`. -/
theorem diagonal {N L : PTm n} (hL : Γ ⊢[PRAAx] le (two * N) L) : Γ ⊢[PRAAx] N * Conv N L ≐ fact L * H N L := by
  have hLs := (LeanProofs.IPRA.Analysis.BaselAverages.shift_le hL).wk (ψ := lt (var 0) (Syn.shift N))
  simp only [Syn.shift, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at hLs
  have s₁ : Γ ⊢[PRAAx] ap2 (sumF dc) N (pairT N L) ≐ fact L * ap2 (sumF ad) N (pairT N L) := by
    refine LeanProofs.IPRA.Probability.Independence.sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, inst2_addBody]
    have e : Syn.shift (fact L) = fact (Syn.shift L) := by simp [Syn.shift]
    rw [e]
    refine (inst_dc _ _ _).eqTrans ((dc_pt Prf.hyp0 ?_).eqTrans
      (congrMul (.eqRefl _) (congrAdd (inst_g _ _ _) (inst_r _ _ _)).eqSymm))
    simpa [Syn.shift] using hLs
  have s₂ : Γ ⊢[PRAAx] ap2 (sumF dc) N (pairT N L) ≐ (two * N) * Conv N L := by
    refine LeanProofs.IPRA.Probability.Independence.sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT]
    have e : Syn.shift (two * N) = two * Syn.shift N := by simp [Syn.shift]
    rw [e]
    exact (inst_dc _ _ _).eqTrans (congrMul (.eqRefl _) (inst_cv _ _ _).eqSymm)
  have c₁ : Γ ⊢[PRAAx] ap2 (sumF (lift3 gK)) N (pairT N L) ≐ H N L := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, inst2_t]
    exact (inst_g _ _ _).eqTrans (by simp [Syn.shift]; exact .eqRefl _)
  have r := sum_reflect (Γ := Γ) tB N (fact L)
  have c₂ : Γ ⊢[PRAAx] ap2 (sumF (lift3 rK)) N (pairT N L) ≐ ap2 (sumF (rflBody tB)) N (pairT N (fact L)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, shift_pairT, inst2_rflBody, inst2_t]
    refine (inst_r _ _ _).eqTrans ?_
    have e : Syn.shift (fact L) = fact (Syn.shift L) := by simp [Syn.shift]
    rw [e]
    exact congrAp2 quoF (snd_pair _ _).eqSymm
      (congrSucc (congrMul (.eqRefl _) (congrMonus (fst_pair _ _).eqSymm (.eqRefl _))))
  have e₁ := natEq s₁; have e₂ := natEq s₂; have e₃ := natEq c₁; have e₄ := natEq c₂; have e₅ := natEq r
  refine LeanProofs.IPRA.Combinatorics.BinomialIdentities.mul_cancel (D := two)
    LeanProofs.IPRA.AnalyticNumberTheory.PhiDouble.two_pos' ?_
  ipra_lc e₁ - e₂ + 𝔞 (fact L) * (natEq (sum_add (Γ := Γ) (lift3 gK) (lift3 rK) N (pairT N L)) + e₃ + e₄ - e₅)

/-! ## Linear combinations of sums -/

/-- If `f(i, x) + c h(i, y) = k(i, z)` for `i < K`, then `∑_{i<K} f(i, x) + c ∑_{i<K} h(i, y) = ∑_{i<K} k(i, z)`. -/
theorem sum_lin (f h k : PTm 2) (K x y z c : PTm n)
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift K) ⟶
      (inst2 f (var 0) (Syn.shift x) + Syn.shift c * inst2 h (var 0) (Syn.shift y) ≐ inst2 k (var 0) (Syn.shift z)))) :
    Γ ⊢[PRAAx] ap2 (sumF f) K x + c * ap2 (sumF h) K y ≐ ap2 (sumF k) K z := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift K) ⟶
      (ap2 (sumF f) (var 0) (Syn.shift x) + Syn.shift c * ap2 (sumF h) (var 0) (Syn.shift y) ≐
        ap2 (sumF k) (var 0) (Syn.shift z))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      ipra_lc natEq (sum_zero (Γ := le zero K :: Γ) f x) + 𝔞 c * natEq (sum_zero (Γ := le zero K :: Γ) h y) -
        natEq (sum_zero (Γ := le zero K :: Γ) k z)
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      have hle : (le (succ (var 0)) (Syn.shift K) ::
          (le (var 0) (Syn.shift K) ⟶ (ap2 (sumF f) (var 0) (Syn.shift x) + Syn.shift c * ap2 (sumF h) (var 0) (Syn.shift y) ≐
            ap2 (sumF k) (var 0) (Syn.shift z))) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift K) :=
        le_trans (le_succ_self _) Prf.hyp0
      refine withEq (Prf.impE Prf.hyp1 hle) fun i => withEq (Prf.impE hp.allOpen.wk.wk Prf.hyp0) fun p =>
        withEq (sum_succ' f (var 0) (Syn.shift x)) fun s1 => withEq (sum_succ' h (var 0) (Syn.shift y)) fun s2 =>
        withEq (sum_succ' k (var 0) (Syn.shift z)) fun s3 => ?_
      ipra_lc s1 + 𝔞 (Syn.shift c) * s2 - s3 + i + p
  have h2 := Prf.allE K hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl K)

/-! ## The signed reflection -/

/-- `g_{M−i}` over `0 = i`, `1 = M`, `2 = L`. -/
abbrev rf : PTm 2 := lift3 (quo (fact (var 2)) (succ (two * monus (var 1) (var 0))))

theorem inst_rf (i M L : PTm n) : Γ ⊢[PRAAx] inst2 rf i (pairT M L) ≐ g (monus M i) L := by
  have h := inst2_lift3 (Γ := Γ) (quo (fact (var 2)) (succ (two * monus (var 1) (var 0)))) i M L
  simp at h
  exact h

/-- The parity parts of `R(M) = ∑_{i<M} (−1)^i g_{M−i}`. -/
abbrev Rp (M L : PTm n) : PTm n := Ev rf M (pairT M L)
abbrev Rm (M L : PTm n) : PTm n := Od rf M (pairT M L)

theorem R_succ (M L : PTm n) :
    Γ ⊢[PRAAx] (Rp (succ M) L ≐ g (succ M) L + Rm M L) ⋏ (Rm (succ M) L ≐ Rp M L) := by
  have h1 := sum_shift (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.eB rf) M (pairT (succ M) L)
  have h2 := sum_shift (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.oB rf) M (pairT (succ M) L)
  rw [LeanProofs.IPRA.Analysis.BaselFinite.inst2_eB] at h1
  rw [LeanProofs.IPRA.Analysis.BaselFinite.inst2_oB] at h2
  have c1 : Γ ⊢[PRAAx] ap2 (sumF (shiftBody (LeanProofs.IPRA.Analysis.BaselFinite.eB rf))) M (pairT (succ M) L) ≐ Rm M L := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_shiftBody, LeanProofs.IPRA.Analysis.BaselFinite.inst2_eB, LeanProofs.IPRA.Analysis.BaselFinite.inst2_oB,
      shift_pairT, shift_pairT]
    refine congrMul (compl_succ _) ((inst_rf _ _ _).eqTrans ((congrAp2 quoF (.eqRefl _)
      (congrSucc (congrMul (.eqRefl _) (succ_monus_succ _ _)))).eqTrans (inst_rf _ _ _).eqSymm))
  have c2 : Γ ⊢[PRAAx] ap2 (sumF (shiftBody (LeanProofs.IPRA.Analysis.BaselFinite.oB rf))) M (pairT (succ M) L) ≐ Rp M L := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_shiftBody, LeanProofs.IPRA.Analysis.BaselFinite.inst2_eB, LeanProofs.IPRA.Analysis.BaselFinite.inst2_oB,
      shift_pairT, shift_pairT]
    refine congrMul (par_succ _) ((inst_rf _ _ _).eqTrans ((congrAp2 quoF (.eqRefl _)
      (congrSucc (congrMul (.eqRefl _) (succ_monus_succ _ _)))).eqTrans (inst_rf _ _ _).eqSymm))
  have i0 := natEq ((inst_rf (Γ := Γ) zero (succ M) L).eqTrans (congrAp2 quoF (.eqRefl _)
    (congrSucc (congrMul (.eqRefl _) (monus_zero _)))))
  have a := natEq h1; have b := natEq h2; have c := natEq c1; have d := natEq c2
  refine .andI ?_ ?_
  · ipra_lc a +
      𝔞 (inst2 rf zero (pairT (succ M) L)) * natEq ((congrMonus (.eqRefl one) (par_zero (Γ := Γ))).eqTrans (monus_zero _)) +
      i0 + c
  · ipra_lc b + 𝔞 (inst2 rf zero (pairT (succ M) L)) * natEq (par_zero (Γ := Γ) (n := n)) + d

theorem refl_zero (L : PTm n) :
    Γ ⊢[PRAAx] monus one (par zero) * Rp zero L + par zero * Rm zero L + Am (succ zero) L + fact L ≐
      monus one (par zero) * Rm zero L + par zero * Rp zero L + Ap (succ zero) L := by
  have a := natEq (sum_zero (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.eB rf) (pairT zero L))
  have b := natEq (sum_zero (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.oB rf) (pairT zero L))
  have c := natEq (Ap_succ (Γ := Γ) zero L); have d := natEq (Am_succ (Γ := Γ) zero L)
  have c0 := natEq (sum_zero (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.eB tB) (fact L))
  have d0 := natEq (sum_zero (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.oB tB) (fact L))
  have z0 := natEq ((congrMonus (.eqRefl one) (par_zero (Γ := Γ))).eqTrans (monus_zero _))
  have z1 := natEq (par_zero (Γ := Γ) (n := n))
  have q := natEq (LeanProofs.IPRA.Analysis.BaselAverages.quo_one' (Γ := Γ) (fact L))
  apply deriveNat; ipra_simps
  rw [a, b, c, d, c0, d0, z0, z1, q]
  ring

theorem refl_step {M L : PTm n}
    (ih : Γ ⊢[PRAAx] monus one (par M) * Rp M L + par M * Rm M L + Am (succ M) L + fact L ≐
      monus one (par M) * Rm M L + par M * Rp M L + Ap (succ M) L) :
    Γ ⊢[PRAAx] monus one (par (succ M)) * Rp (succ M) L + par (succ M) * Rm (succ M) L + Am (succ (succ M)) L +
        fact L ≐ monus one (par (succ M)) * Rm (succ M) L + par (succ M) * Rp (succ M) L + Ap (succ (succ M)) L := by
  have r := R_succ (Γ := Γ) M L
  have r1 := natEq (Prf.andE₁ r); have r2 := natEq (Prf.andE₂ r)
  have ap := natEq (Ap_succ (Γ := Γ) (succ M) L); have am := natEq (Am_succ (Γ := Γ) (succ M) L)
  have p1 := natEq (par_succ (Γ := Γ) M); have q1 := natEq (compl_succ (Γ := Γ) M)
  have i := natEq ih
  apply deriveNat; ipra_simps
  rw [r1, r2, ap, am, p1, q1]
  linear_combination i

/-- Variables: `0 = M`, `1 = L`. -/
private abbrev reflF : Fm PTm 2 :=
  monus one (par (var 0)) * Rp (var 0) (var 1) + par (var 0) * Rm (var 0) (var 1) + Am (succ (var 0)) (var 1) +
    fact (var 1) ≐ monus one (par (var 0)) * Rm (var 0) (var 1) + par (var 0) * Rp (var 0) (var 1) +
    Ap (succ (var 0)) (var 1)

private theorem refl₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] reflF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, subst_ap1, subst_pairT, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact refl_zero _
  · simp only [Fm.subst_eq, subst_ap2, subst_ap1, subst_pairT, PTm.subst_add, PTm.subst_mul, PTm.subst_monus,
      Syn.subst_var, Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact refl_step Prf.hyp0

/-- The signed reflection: `(−1)^M R(M) = ∑_{j=1}^{M} (−1)^j g_j = A(M + 1) − g_0`, with `g_0 = F`. -/
theorem refl (M L : PTm n) :
    Γ ⊢[PRAAx] monus one (par M) * Rp M L + par M * Rm M L + Am (succ M) L + fact L ≐
      monus one (par M) * Rm M L + par M * Rp M L + Ap (succ M) L := by
  have i := inst (Γ := Γ) refl₀ (![M, L] : Fin 2 → PTm n)
  simpa using i

/-! ## The increment of the averages -/

/-- For `1 ≤ d = d₀ + 1 ≤ N` and `2N + 1 ≤ L`: `b_d(N + 1) + 2 g_N g_{N−d} = b_d(N)`, i.e.
`b_d(N+1) − b_d(N) = (h_N − h_{N−d})/d = −2 h_N h_{N−d}` (`eq:pfminus`). -/
theorem b_step {d₀ N L : PTm n} (hd : Γ ⊢[PRAAx] le (succ d₀) N) (hL : Γ ⊢[PRAAx] le (succ (two * N)) L) :
    Γ ⊢[PRAAx] LeanProofs.IPRA.Analysis.BaselAverages.b (succ d₀) (succ N) L +
      two * (g N L * g (monus N (succ d₀)) L) ≐ LeanProofs.IPRA.Analysis.BaselAverages.b (succ d₀) N L := by
  have hdL : Γ ⊢[PRAAx] le (succ d₀) L :=
    le_trans hd (le_trans (le_of_eq_add (d := succ N) (by ipra_ring)) hL)
  have h1L : Γ ⊢[PRAAx] le (succ (two * monus N (succ d₀))) L := by
    refine le_trans (le_of_eq_add (d := two * succ d₀) ?_) hL
    ipra_lc 2 * natEq (eq_add_of_le hd)
  have em : Γ ⊢[PRAAx] monus (succ N) (succ d₀) ≐ succ (monus N (succ d₀)) :=
    (succ_monus_succ _ _).eqTrans (LeanProofs.IPRA.Analysis.BaselAverages.monus_succ_eq hd)
  have hm := natEq ((congrAp2 (sumF tB) em (.eqRefl (fact L))).eqTrans
    (LeanProofs.IPRA.Analysis.BaselAverages.H_succ (Γ := Γ) (monus N (succ d₀)) L))
  refine LeanProofs.IPRA.Combinatorics.BinomialIdentities.mul_cancel (D := succ (two * N)) (odd_pos _)
    (LeanProofs.IPRA.Combinatorics.BinomialIdentities.mul_cancel (D := succ (two * monus N (succ d₀))) (odd_pos _) ?_)
  ipra_lc 2 * 𝔞 (fact L) * natEq (LeanProofs.IPRA.Analysis.BaselSquares.fact_eq hdL) -
    2 * 𝔞 (quo (fact L) (succ d₀)) * 𝔞 (fact L) * natEq (eq_add_of_le hd) -
    ((2 * 𝔞 (monus N (succ d₀)) + 1) * 𝔞 (quo (fact L) (succ d₀)) + 2 * (2 * 𝔞 (monus N (succ d₀)) + 1) * 𝔞 (g (monus N (succ d₀)) L)) * natEq (LeanProofs.IPRA.Analysis.BaselSquares.fact_eq hL) +
    ((2 * 𝔞 N + 1) * 𝔞 (quo (fact L) (succ d₀)) - 2 * 𝔞 (fact L)) * natEq (LeanProofs.IPRA.Analysis.BaselSquares.fact_eq h1L) +
    (2 * 𝔞 (monus N (succ d₀)) + 1) * (2 * 𝔞 N + 1) * 𝔞 (quo (fact L) (succ d₀)) * (-natEq (LeanProofs.IPRA.Analysis.BaselAverages.C_split (Γ := Γ) (succ d₀) (succ N) L) + natEq (LeanProofs.IPRA.Analysis.BaselAverages.C_split (Γ := Γ) (succ d₀) N L) + natEq (LeanProofs.IPRA.Analysis.BaselAverages.H_succ (Γ := Γ) N L) - hm)

open LeanProofs.IPRA.Analysis.BaselAverages (b wB inst2_w) in
theorem b_congr {d N N' L L' : PTm n} (eN : Γ ⊢[PRAAx] N' ≐ N) (eL : Γ ⊢[PRAAx] L' ≐ L) :
    Γ ⊢[PRAAx] b d N' L' ≐ b d N L :=
  congrMul (congrAp2 quoF (congrAp2 factF eL (.eqRefl _)) (.eqRefl _))
    (congrMonus (congrAp2 (sumF tB) eN (congrAp2 factF eL (.eqRefl _)))
      (congrAp2 (sumF tB) (congrMonus eN (.eqRefl _)) (congrAp2 factF eL (.eqRefl _))))

open LeanProofs.IPRA.Analysis.BaselAverages (b wB inst2_w) in
/-- The parity parts of `E(N) = ∑_{d=1}^{N−1} (−1)^{d−1} b_d(N)`, `N = M + 1`. -/
abbrev Ep' (M L : PTm n) : PTm n := Ev wB M (pairT (succ M) L)
open LeanProofs.IPRA.Analysis.BaselAverages (b wB inst2_w) in
abbrev Em' (M L : PTm n) : PTm n := Od wB M (pairT (succ M) L)

open LeanProofs.IPRA.Analysis.BaselAverages (b wB inst2_w) in
/-- The increment of `E`: for `N = M + 1`, `2N + 1 ≤ L`,
`E^±(N + 1) + 2 g_N R^±(M) = E^±(N) + [(1 ∸ par M) or par M] b_N(N + 1)`. -/
theorem E_step {M L : PTm n} (hL : Γ ⊢[PRAAx] le (succ (two * succ M)) L) :
    Γ ⊢[PRAAx] (Ep' (succ M) L + two * g (succ M) L * Rp M L ≐
        Ep' M L + monus one (par M) * b (succ M) (succ (succ M)) L) ⋏
      (Em' (succ M) L + two * g (succ M) L * Rm M L ≐ Em' M L + par M * b (succ M) (succ (succ M)) L) := by
  have h1 := sum_succ' (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.eB wB) M (pairT (succ (succ M)) L)
  have h2 := sum_succ' (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.oB wB) M (pairT (succ (succ M)) L)
  rw [LeanProofs.IPRA.Analysis.BaselFinite.inst2_eB, inst2_w] at h1
  rw [LeanProofs.IPRA.Analysis.BaselFinite.inst2_oB, inst2_w] at h2
  have hLs := (LeanProofs.IPRA.Analysis.BaselAverages.shift_le hL).wk (ψ := lt (var 0) (Syn.shift M))
  have es : Syn.shift (succ (two * succ M)) = succ (two * succ (Syn.shift M)) := by simp [Syn.shift]
  rw [es] at hLs
  have esc : Syn.shift (two * g (succ M) L) = two * g (succ (Syn.shift M)) (Syn.shift L) := by simp [Syn.shift]
  have es2 : Syn.shift (succ (succ M)) = succ (succ (Syn.shift M)) := by simp [Syn.shift]
  have es1 : Syn.shift (succ M) = succ (Syn.shift M) := by simp [Syn.shift]
  have pt : ∀ (w : PTm n → PTm n), (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx]
      b (succ (var 0)) (succ (succ (Syn.shift M))) (Syn.shift L) +
        two * (g (succ (Syn.shift M)) (Syn.shift L) * g (monus (Syn.shift M) (var 0)) (Syn.shift L)) ≐
      b (succ (var 0)) (succ (Syn.shift M)) (Syn.shift L) := fun _ => by
    have hd : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (succ (Syn.shift M)) :=
      le_trans Prf.hyp0 (le_succ_self _)
    exact (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (congrMul (.eqRefl _)
      (congrAp2 quoF (.eqRefl _) (congrSucc (congrMul (.eqRefl _) (succ_monus_succ _ _))))))).eqSymm.eqTrans
      (b_step hd hLs)
  have s1 := sum_lin (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.eB wB) (LeanProofs.IPRA.Analysis.BaselFinite.eB rf)
    (LeanProofs.IPRA.Analysis.BaselFinite.eB wB) M (pairT (succ (succ M)) L) (pairT M L) (pairT (succ M) L)
    (two * g (succ M) L) (.allI (.impI (by
      rw [LeanProofs.IPRA.Analysis.BaselFinite.inst2_eB, LeanProofs.IPRA.Analysis.BaselFinite.inst2_eB,
        LeanProofs.IPRA.Analysis.BaselFinite.inst2_eB, inst2_w, inst2_w, shift_pairT, shift_pairT, shift_pairT,
        esc, es2, es1]
      have c2 := natEq (b_congr (d := succ (var 0)) (fst_pair (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift)
        (succ (succ (Syn.shift M))) (Syn.shift L)) (snd_pair (succ (succ (Syn.shift M))) (Syn.shift L)))
      have c1 := natEq (b_congr (d := succ (var 0)) (fst_pair (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift)
        (succ (Syn.shift M)) (Syn.shift L)) (snd_pair (succ (Syn.shift M)) (Syn.shift L)))
      have cr := natEq (inst_rf (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) (var 0) (Syn.shift M) (Syn.shift L))
      have bs := natEq (pt id)
      apply deriveNat; ipra_simps
      linear_combination 𝔞 (monus one (par (var 0))) * c2 + 𝔞 (monus one (par (var 0))) * bs +
        2 * 𝔞 (g (succ (Syn.shift M)) (Syn.shift L)) * 𝔞 (monus one (par (var 0))) * cr -
        𝔞 (monus one (par (var 0))) * c1)))
  have s2 := sum_lin (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.oB wB) (LeanProofs.IPRA.Analysis.BaselFinite.oB rf)
    (LeanProofs.IPRA.Analysis.BaselFinite.oB wB) M (pairT (succ (succ M)) L) (pairT M L) (pairT (succ M) L)
    (two * g (succ M) L) (.allI (.impI (by
      rw [LeanProofs.IPRA.Analysis.BaselFinite.inst2_oB, LeanProofs.IPRA.Analysis.BaselFinite.inst2_oB,
        LeanProofs.IPRA.Analysis.BaselFinite.inst2_oB, inst2_w, inst2_w, shift_pairT, shift_pairT, shift_pairT,
        esc, es2, es1]
      have c2 := natEq (b_congr (d := succ (var 0)) (fst_pair (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift)
        (succ (succ (Syn.shift M))) (Syn.shift L)) (snd_pair (succ (succ (Syn.shift M))) (Syn.shift L)))
      have c1 := natEq (b_congr (d := succ (var 0)) (fst_pair (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift)
        (succ (Syn.shift M)) (Syn.shift L)) (snd_pair (succ (Syn.shift M)) (Syn.shift L)))
      have cr := natEq (inst_rf (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) (var 0) (Syn.shift M) (Syn.shift L))
      have bs := natEq (pt id)
      apply deriveNat; ipra_simps
      linear_combination 𝔞 (par (var 0)) * c2 + 𝔞 (par (var 0)) * bs +
        2 * 𝔞 (g (succ (Syn.shift M)) (Syn.shift L)) * 𝔞 (par (var 0)) * cr -
        𝔞 (par (var 0)) * c1)))
  have a1 := natEq h1; have a2 := natEq h2; have t1 := natEq s1; have t2 := natEq s2
  refine .andI ?_ ?_
  · ipra_lc a1 + t1 +
      𝔞 (monus one (par M)) * natEq (b_congr (d := succ M) (fst_pair (Γ := Γ) (succ (succ M)) L) (snd_pair (Γ := Γ) (succ (succ M)) L))
  · ipra_lc a2 + t2 +
      𝔞 (par M) * natEq (b_congr (d := succ M) (fst_pair (Γ := Γ) (succ (succ M)) L) (snd_pair (Γ := Γ) (succ (succ M)) L))

/-! ## The triangle `T(N) = ∑_{i<N} s_i A_{N−1−i}` -/

/-- `A^±(N − 1 − i)` over `0 = i`, `1 = N`, `2 = L`. -/
abbrev ApK : PTm 3 := Ev tB (monus (var 1) (succ (var 0))) (fact (var 2))
abbrev AmK : PTm 3 := Od tB (monus (var 1) (succ (var 0))) (fact (var 2))
/-- The positive and negative parts of `s_i A_{N−1−i}`. -/
abbrev tP : PTm 2 := lift3 (monus one (par (var 0)) * gK * ApK + par (var 0) * gK * AmK)
abbrev tM : PTm 2 := lift3 (monus one (par (var 0)) * gK * AmK + par (var 0) * gK * ApK)

abbrev Tp (N L : PTm n) : PTm n := ap2 (sumF tP) N (pairT N L)
abbrev Tm (N L : PTm n) : PTm n := ap2 (sumF tM) N (pairT N L)

theorem inst_tP (i N L : PTm n) : Γ ⊢[PRAAx] inst2 tP i (pairT N L) ≐
    monus one (par i) * g i L * Ap (monus N (succ i)) L + par i * g i L * Am (monus N (succ i)) L := by
  have h := inst2_lift3 (Γ := Γ) (monus one (par (var 0)) * gK * ApK + par (var 0) * gK * AmK) i N L
  simp at h
  exact h

theorem inst_tM (i N L : PTm n) : Γ ⊢[PRAAx] inst2 tM i (pairT N L) ≐
    monus one (par i) * g i L * Am (monus N (succ i)) L + par i * g i L * Ap (monus N (succ i)) L := by
  have h := inst2_lift3 (Γ := Γ) (monus one (par (var 0)) * gK * AmK + par (var 0) * gK * ApK) i N L
  simp at h
  exact h

/-- The pointwise increment: for `i < N = M + 1`, with `k = N − 1 − i`,
`s_i A^±(N − i) = s_i A^±(N − 1 − i) + [i + k even or odd] g_i g_k`. -/
theorem t_pt {i M L : PTm n} (hi : Γ ⊢[PRAAx] lt i (succ M)) :
    Γ ⊢[PRAAx] (inst2 tP i (pairT (succ M) L) + monus one (par M) * inst2 cv i (pairT (succ M) L) ≐
        inst2 tP i (pairT (succ (succ M)) L)) ⋏
      (inst2 tM i (pairT (succ M) L) + par M * inst2 cv i (pairT (succ M) L) ≐ inst2 tM i (pairT (succ (succ M)) L)) := by
  have i1 := natEq (inst_tP (Γ := Γ) i (succ M) L); have i2 := natEq (inst_tP (Γ := Γ) i (succ (succ M)) L)
  have j1 := natEq (inst_tM (Γ := Γ) i (succ M) L); have j2 := natEq (inst_tM (Γ := Γ) i (succ (succ M)) L)
  have ic := natEq (inst_cv (Γ := Γ) i (succ M) L)
  have em : Γ ⊢[PRAAx] monus (succ (succ M)) (succ i) ≐ succ (monus (succ M) (succ i)) :=
    (succ_monus_succ _ _).eqTrans (LeanProofs.IPRA.Analysis.BaselAverages.monus_succ_eq hi)
  have ap := natEq ((congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.eB tB)) em (.eqRefl (fact L))).eqTrans
    (Ap_succ (Γ := Γ) (monus (succ M) (succ i)) L))
  have am := natEq ((congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.oB tB)) em (.eqRefl (fact L))).eqTrans
    (Am_succ (Γ := Γ) (monus (succ M) (succ i)) L))
  have eik : Γ ⊢[PRAAx] i + monus (succ M) (succ i) ≐ M := by
    ipra_lc -natEq (eq_add_of_le hi)
  have qa := natEq (q_add (Γ := Γ) i (monus (succ M) (succ i)))
  have pa := natEq (p_add (Γ := Γ) i (monus (succ M) (succ i)))
  have qc := natEq (congrMonus (.eqRefl one) (congrAp1 parF eik))
  have pc := natEq (congrAp1 parF eik)
  refine .andI ?_ ?_
  · apply deriveNat; ipra_simps
    rw [i1, i2, ic, ap, am]
    linear_combination 𝔞 (g i L) * 𝔞 (g (monus (succ M) (succ i)) L) * (qa - qc)
  · apply deriveNat; ipra_simps
    rw [j1, j2, ic, ap, am]
    linear_combination 𝔞 (g i L) * 𝔞 (g (monus (succ M) (succ i)) L) * (pa - pc)

/-- The increment of `T`: `T^±(N + 1) = T^±(N) + [N − 1 even or odd] Conv(N)` for `N = M + 1`. -/
theorem T_step (M L : PTm n) :
    Γ ⊢[PRAAx] (Tp (succ (succ M)) L ≐ Tp (succ M) L + monus one (par M) * Conv (succ M) L) ⋏
      (Tm (succ (succ M)) L ≐ Tm (succ M) L + par M * Conv (succ M) L) := by
  have e0 : Γ ⊢[PRAAx] monus (succ (succ M)) (succ (succ M)) ≐ zero := monus_self _
  have a0 := natEq ((congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.eB tB)) e0 (.eqRefl (fact L))).eqTrans
    (sum_zero _ _))
  have b0 := natEq ((congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.oB tB)) e0 (.eqRefl (fact L))).eqTrans
    (sum_zero _ _))
  have l1 := natEq (inst_tP (Γ := Γ) (succ M) (succ (succ M)) L)
  have l2 := natEq (inst_tM (Γ := Γ) (succ M) (succ (succ M)) L)
  have h1 := natEq (sum_succ' (Γ := Γ) tP (succ M) (pairT (succ (succ M)) L))
  have h2 := natEq (sum_succ' (Γ := Γ) tM (succ M) (pairT (succ (succ M)) L))
  have es1 : Syn.shift (succ M) = succ (Syn.shift M) := by simp [Syn.shift]
  have es2 : Syn.shift (succ (succ M)) = succ (succ (Syn.shift M)) := by simp [Syn.shift]
  have esq : Syn.shift (monus one (par M)) = monus one (par (Syn.shift M)) := by simp [Syn.shift]
  have esp : Syn.shift (par M) = par (Syn.shift M) := by simp [Syn.shift]
  have s1 := natEq (sum_lin (Γ := Γ) tP cv tP (succ M) (pairT (succ M) L) (pairT (succ M) L) (pairT (succ (succ M)) L)
    (monus one (par M)) (.allI (.impI (by
      simp only [shift_pairT, es1, es2, esq]
      exact Prf.andE₁ (t_pt Prf.hyp0)))))
  have s2 := natEq (sum_lin (Γ := Γ) tM cv tM (succ M) (pairT (succ M) L) (pairT (succ M) L) (pairT (succ (succ M)) L)
    (par M) (.allI (.impI (by
      simp only [shift_pairT, es1, es2, esp]
      exact Prf.andE₂ (t_pt Prf.hyp0)))))
  refine .andI ?_ ?_
  · apply deriveNat; ipra_simps
    rw [h1, l1, a0, b0]
    linear_combination -s1
  · apply deriveNat; ipra_simps
    rw [h2, l2, a0, b0]
    linear_combination -s2

/-! ## The second decomposition `A² + T = O + E` (`eq:second`) -/

/-- The ring form of the induction step of `eq:second`. -/
theorem phi_ring {R : Type*} [CommRing R] (Ap Am Tp Tm Ep Em O ApN AmN TpN TmN EpN EmN ON p q g F u H C Rp Rm N : R)
    (ih : Ap * Ap + Am * Am + Tp + Em = O + Ep + Tm + 2 * (Ap * Am))
    (hap : ApN = Ap + p * g) (ham : AmN = Am + q * g) (ho : ON = O + g * g)
    (htp : TpN = Tp + q * (u * H)) (htm : TmN = Tm + p * (u * H))
    (hep : EpN + 2 * g * Rp = Ep + q * (u * C)) (hem : EmN + 2 * g * Rm = Em + p * (u * C))
    (hrefl : q * Rp + p * Rm + Am + F = q * Rm + p * Rp + Ap)
    (hc : C + F = H + g) (hfu : F = N * u) (hg : F = (2 * N + 1) * g) (hps : p + q = 1) (hpp : p * q = 0) :
    ApN * ApN + AmN * AmN + TpN + EmN = ON + EpN + TmN + 2 * (ApN * AmN) := by
  have hep' : EpN = Ep + q * (u * C) - 2 * g * Rp := by linear_combination hep
  have hem' : EmN = Em + p * (u * C) - 2 * g * Rm := by linear_combination hem
  subst hap ham ho htp htm hep' hem'
  linear_combination ih + (g ^ 2 * (p + q + 1) - 2 * g * (Rp - Rm) * (p + q + 1)) * hps +
    (-4 * g ^ 2 + 8 * g * (Rp - Rm)) * hpp + 2 * g * (q - p) * hrefl + (q - p) * u * hg -
    2 * (q - p) * g * hfu - (q - p) * u * hc

open LeanProofs.IPRA.Analysis.BaselSquares (O O_succ fact_eq) in
/-- `eq:second` at `N = M + 1`, as an equation of naturals:
`A⁺² + A⁻² + T⁺ + E⁻ = O + E⁺ + T⁻ + 2 A⁺ A⁻`, i.e. `A_N² + T_N = O_N + E_N` (`T_N` the triangle). -/
abbrev Phi (M L : PTm n) : Fm PTm n :=
  Ap (succ M) L * Ap (succ M) L + Am (succ M) L * Am (succ M) L + Tp (succ M) L + Em' M L ≐
    O (succ M) L + Ep' M L + Tm (succ M) L + two * (Ap (succ M) L * Am (succ M) L)

open LeanProofs.IPRA.Analysis.BaselSquares (O O_succ fact_eq) in
theorem phi_zero (L : PTm n) : Γ ⊢[PRAAx] Phi zero L := by
  have q := natEq (LeanProofs.IPRA.Analysis.BaselAverages.quo_one' (Γ := Γ) (fact L))
  have a1 := natEq (Ap_succ (Γ := Γ) zero L); have a2 := natEq (Am_succ (Γ := Γ) zero L)
  have a0 := natEq (sum_zero (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.eB tB) (fact L))
  have b0 := natEq (sum_zero (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.oB tB) (fact L))
  have z0 := natEq ((congrMonus (.eqRefl one) (par_zero (Γ := Γ))).eqTrans (monus_zero _))
  have z1 := natEq (par_zero (Γ := Γ) (n := n))
  have o1 := natEq (O_succ (Γ := Γ) zero L)
  have o0 := natEq (sum_zero (Γ := Γ) LeanProofs.IPRA.Analysis.BaselSquares.oB L)
  have e0 : Γ ⊢[PRAAx] monus (succ zero) (succ zero) ≐ zero := monus_self _
  have c0 := natEq ((congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.eB tB)) e0 (.eqRefl (fact L))).eqTrans
    (sum_zero _ _))
  have d0 := natEq ((congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.oB tB)) e0 (.eqRefl (fact L))).eqTrans
    (sum_zero _ _))
  have t1 := natEq ((sum_succ' (Γ := Γ) tP zero (pairT (succ zero) L)).eqTrans
    (congrAdd (sum_zero _ _) (inst_tP zero (succ zero) L)))
  have t2 := natEq ((sum_succ' (Γ := Γ) tM zero (pairT (succ zero) L)).eqTrans
    (congrAdd (sum_zero _ _) (inst_tM zero (succ zero) L)))
  have e1 := natEq (sum_zero (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.eB LeanProofs.IPRA.Analysis.BaselAverages.wB)
    (pairT (succ zero) L))
  have e2 := natEq (sum_zero (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.oB LeanProofs.IPRA.Analysis.BaselAverages.wB)
    (pairT (succ zero) L))
  apply deriveNat; ipra_simps
  rw [a1, a2, a0, b0, t1, t2, c0, d0, e1, e2, o1, o0, z0, z1]
  rw [q]
  ring

open LeanProofs.IPRA.Analysis.BaselSquares (O O_succ fact_eq) in
open LeanProofs.IPRA.Analysis.BaselAverages (C C_split H_succ quo_one') in
theorem phi_step {M L : PTm n} (ih : Γ ⊢[PRAAx] le (succ (two * succ M)) L ⟶ Phi M L)
    (h : Γ ⊢[PRAAx] le (succ (two * succ (succ M))) L) : Γ ⊢[PRAAx] Phi (succ M) L := by
  have h' : Γ ⊢[PRAAx] le (succ (two * succ M)) L :=
    le_trans (le_of_eq_add (d := two) (by ipra_ring)) h
  have h2 : Γ ⊢[PRAAx] le (two * succ M) L := le_trans (le_succ_self _) h'
  have h1 : Γ ⊢[PRAAx] le (succ M) L :=
    le_trans (le_of_eq_add (d := succ M) (by ipra_ring)) h2
  have i := natEq (Prf.impE ih h')
  have ap := natEq (Ap_succ (Γ := Γ) (succ M) L); have am := natEq (Am_succ (Γ := Γ) (succ M) L)
  have cs := natEq (compl_succ (Γ := Γ) M); have ps := natEq (par_succ (Γ := Γ) M)
  have o := natEq (O_succ (Γ := Γ) (succ M) L)
  have t := T_step (Γ := Γ) M L
  have tp := natEq (Prf.andE₁ t); have tm := natEq (Prf.andE₂ t)
  have fu := natEq (fact_eq h1)
  have cv : Γ ⊢[PRAAx] Conv (succ M) L ≐ quo (fact L) (succ M) * H (succ M) L := by
    have d := natEq (diagonal h2); have f := natEq (fact_eq h1)
    refine LeanProofs.IPRA.Combinatorics.BinomialIdentities.mul_cancel (D := succ M) (odd_pos _) ?_
    ipra_lc d + 𝔞 (H (succ M) L) * f
  have cv' := natEq cv
  have e := E_step (Γ := Γ) h'
  have ep := natEq (Prf.andE₁ e); have em := natEq (Prf.andE₂ e)
  have rf := natEq (refl (Γ := Γ) M L)
  have c1 := natEq (C_split (Γ := Γ) (succ M) (succ (succ M)) L)
  have m1 : Γ ⊢[PRAAx] monus (succ (succ M)) (succ M) ≐ succ zero :=
    LeanProofs.IPRA.Combinatorics.BellDobinski.monus_of_eq (by ipra_ring)
  have hh1 := natEq ((congrAp2 (sumF tB) m1 (.eqRefl (fact L))).eqTrans ((H_succ (Γ := Γ) zero L).eqTrans
    ((congrAdd (sum_zero _ _) (quo_one' _)).eqTrans (zero_add _))))
  have hs := natEq (H_succ (Γ := Γ) (succ M) L)
  have fg := natEq (fact_eq h')
  have sp := natEq (par_sum (Γ := Γ) M); have pp := natEq (par_prod (Γ := Γ) M)
  apply deriveNat; ipra_simps
  linear_combination phi_ring (𝔞 (Ap (succ M) L)) (𝔞 (Am (succ M) L)) (𝔞 (Tp (succ M) L)) (𝔞 (Tm (succ M) L))
    (𝔞 (Ep' M L)) (𝔞 (Em' M L)) (𝔞 (O (succ M) L)) (𝔞 (Ap (succ (succ M)) L)) (𝔞 (Am (succ (succ M)) L))
    (𝔞 (Tp (succ (succ M)) L)) (𝔞 (Tm (succ (succ M)) L)) (𝔞 (Ep' (succ M) L)) (𝔞 (Em' (succ M) L))
    (𝔞 (O (succ (succ M)) L)) (𝔞 (par M)) (𝔞 (monus one (par M))) (𝔞 (g (succ M) L)) (𝔞 (fact L))
    (𝔞 (quo (fact L) (succ M))) (𝔞 (H (succ M) L)) (𝔞 (C (succ M) (succ (succ M)) L)) (𝔞 (Rp M L)) (𝔞 (Rm M L))
    (𝔞 M + 1)
    (by linear_combination i) (by linear_combination ap + 𝔞 (g (succ M) L) * cs)
    (by linear_combination am + 𝔞 (g (succ M) L) * ps) (by linear_combination o)
    (by linear_combination tp + 𝔞 (monus one (par M)) * cv') (by linear_combination tm + 𝔞 (par M) * cv')
    (by linear_combination ep) (by linear_combination em) (by linear_combination rf)
    (by linear_combination -c1 - hh1 + hs) (by linear_combination fu) (by linear_combination fg)
    (by linear_combination sp) (by linear_combination pp)

/-- Variables: `0 = M`, `1 = L`. -/
private abbrev phiF : Fm PTm 2 := le (succ (two * succ (var 0))) (var 1) ⟶ Phi (var 0) (var 1)

private theorem phi₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] phiF := by
  refine ind _ ⟨le_QF _ _, trivial⟩ ?_ ?_
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, subst_ap1, subst_pairT, PTm.subst_add,
      PTm.subst_mul, PTm.subst_monus, Syn.subst_var, Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact .impI (phi_zero _)
  · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, subst_ap1, subst_pairT, PTm.subst_add,
      PTm.subst_mul, PTm.subst_monus, Syn.subst_var, Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact .impI (phi_step Prf.hyp1 Prf.hyp0)

/-- `eq:second`, cleared by `F = L!`: for `N = M + 1` and `2N + 1 ≤ L`, `A_N² + T_N = O_N + E_N`. -/
theorem second {M L : PTm n} (h : Γ ⊢[PRAAx] le (succ (two * succ M)) L) : Γ ⊢[PRAAx] Phi M L := by
  have i := inst (Γ := Γ) phi₀ (![M, L] : Fin 2 → PTm n)
  simp at i
  exact Prf.impE i h

/-! ## The omitted triangle `D_N = A_N² − T_N` (`lem:D`) -/

/-- The pointwise bound: for `i < N`, `k = N − 1 − i`, the parts of `s_i (A_N − A_k)` differ by at most
`g_i g_k`. -/
theorem d_pt {i N L : PTm n} (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] le (monus one (par i) * g i L * Ap N L + par i * g i L * Am N L +
        (monus one (par i) * g i L * Am (monus N (succ i)) L + par i * g i L * Ap (monus N (succ i)) L))
      (monus one (par i) * g i L * Am N L + par i * g i L * Ap N L +
        (monus one (par i) * g i L * Ap (monus N (succ i)) L + par i * g i L * Am (monus N (succ i)) L) +
        g i L * g (monus N (succ i)) L) ⋏
    le (monus one (par i) * g i L * Am N L + par i * g i L * Ap N L +
        (monus one (par i) * g i L * Ap (monus N (succ i)) L + par i * g i L * Am (monus N (succ i)) L))
      (monus one (par i) * g i L * Ap N L + par i * g i L * Am N L +
        (monus one (par i) * g i L * Am (monus N (succ i)) L + par i * g i L * Ap (monus N (succ i)) L) +
        g i L * g (monus N (succ i)) L) := by
  have e : Γ ⊢[PRAAx] monus N (succ i) + succ i ≐ N := by
    ipra_lc -natEq (eq_add_of_le hi)
  have tb := tail_bound (Γ := Γ) (monus N (succ i)) i L
  have ea := natEq (congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.eB tB)) e (.eqRefl (fact L)) (Γ := Γ))
  have eb := natEq (congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.oB tB)) e (.eqRefl (fact L)) (Γ := Γ))
  have w1P := eq_add_of_le (Prf.andE₁ tb); have w2P := eq_add_of_le (Prf.andE₂ tb)
  refine .orE (par_cases i) ?_ ?_
  · have hp := natEq (Prf.hyp0 : ((par i ≐ zero) :: Γ) ⊢[PRAAx] _)
    have c := natEq ((congrMonus (.eqRefl one) (Prf.hyp0 : ((par i ≐ zero) :: Γ) ⊢[PRAAx] _)).eqTrans (monus_zero _))
    have w1 := natEq (w1P.wk (ψ := par i ≐ zero)); have w2 := natEq (w2P.wk (ψ := par i ≐ zero))
    have ea' := natEq ((congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.eB tB)) e (.eqRefl (fact L))).wk
      (ψ := par i ≐ zero))
    have eb' := natEq ((congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.oB tB)) e (.eqRefl (fact L))).wk
      (ψ := par i ≐ zero))
    refine .andI (le_of_eq_add (d := g i L * monus (Am (monus N (succ i) + succ i) L + Ap (monus N (succ i)) L +
        g (monus N (succ i)) L) (Ap (monus N (succ i) + succ i) L + Am (monus N (succ i)) L)) ?_)
      (le_of_eq_add (d := g i L * monus (Ap (monus N (succ i) + succ i) L + Am (monus N (succ i)) L +
        g (monus N (succ i)) L) (Am (monus N (succ i) + succ i) L + Ap (monus N (succ i)) L)) ?_)
    · apply deriveNat; ipra_simps
      rw [hp, c]
      linear_combination 𝔞 (g i L) * w1 + 𝔞 (g i L) * ea' - 𝔞 (g i L) * eb'
    · apply deriveNat; ipra_simps
      rw [hp, c]
      linear_combination 𝔞 (g i L) * w2 - 𝔞 (g i L) * ea' + 𝔞 (g i L) * eb'
  · have hp := natEq (Prf.hyp0 : ((par i ≐ one) :: Γ) ⊢[PRAAx] _)
    have c := natEq ((congrMonus (.eqRefl one) (Prf.hyp0 : ((par i ≐ one) :: Γ) ⊢[PRAAx] _)).eqTrans (monus_self _))
    have w1 := natEq (w1P.wk (ψ := par i ≐ one)); have w2 := natEq (w2P.wk (ψ := par i ≐ one))
    have ea' := natEq ((congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.eB tB)) e (.eqRefl (fact L))).wk
      (ψ := par i ≐ one))
    have eb' := natEq ((congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.oB tB)) e (.eqRefl (fact L))).wk
      (ψ := par i ≐ one))
    refine .andI (le_of_eq_add (d := g i L * monus (Ap (monus N (succ i) + succ i) L + Am (monus N (succ i)) L +
        g (monus N (succ i)) L) (Am (monus N (succ i) + succ i) L + Ap (monus N (succ i)) L)) ?_)
      (le_of_eq_add (d := g i L * monus (Am (monus N (succ i) + succ i) L + Ap (monus N (succ i)) L +
        g (monus N (succ i)) L) (Ap (monus N (succ i) + succ i) L + Am (monus N (succ i)) L)) ?_)
    · apply deriveNat; ipra_simps
      rw [hp, c]
      linear_combination 𝔞 (g i L) * w2 - 𝔞 (g i L) * ea' + 𝔞 (g i L) * eb'
    · apply deriveNat; ipra_simps
      rw [hp, c]
      linear_combination 𝔞 (g i L) * w1 + 𝔞 (g i L) * ea' - 𝔞 (g i L) * eb'

/-- `q_i g_i A^±(N)` and `p_i g_i A^±(N)` over `0 = i`, `1 = N`, `2 = L`. -/
abbrev qAp : PTm 2 := lift3 (monus one (par (var 0)) * gK * Ev tB (var 1) (fact (var 2)))
abbrev pAm : PTm 2 := lift3 (par (var 0) * gK * Od tB (var 1) (fact (var 2)))
abbrev qAm : PTm 2 := lift3 (monus one (par (var 0)) * gK * Od tB (var 1) (fact (var 2)))
abbrev pAp : PTm 2 := lift3 (par (var 0) * gK * Ev tB (var 1) (fact (var 2)))
/-- The parts of `s_i (A_N − A_{N−1−i})`. -/
abbrev dPb : PTm 2 := addBody (addBody qAp pAm) tM
abbrev dMb : PTm 2 := addBody (addBody qAm pAp) tP

theorem inst_qAp (i N L : PTm n) : Γ ⊢[PRAAx] inst2 qAp i (pairT N L) ≐ monus one (par i) * g i L * Ap N L := by
  have h := inst2_lift3 (Γ := Γ) (monus one (par (var 0)) * gK * Ev tB (var 1) (fact (var 2))) i N L
  simp at h; exact h
theorem inst_pAm (i N L : PTm n) : Γ ⊢[PRAAx] inst2 pAm i (pairT N L) ≐ par i * g i L * Am N L := by
  have h := inst2_lift3 (Γ := Γ) (par (var 0) * gK * Od tB (var 1) (fact (var 2))) i N L
  simp at h; exact h
theorem inst_qAm (i N L : PTm n) : Γ ⊢[PRAAx] inst2 qAm i (pairT N L) ≐ monus one (par i) * g i L * Am N L := by
  have h := inst2_lift3 (Γ := Γ) (monus one (par (var 0)) * gK * Od tB (var 1) (fact (var 2))) i N L
  simp at h; exact h
theorem inst_pAp (i N L : PTm n) : Γ ⊢[PRAAx] inst2 pAp i (pairT N L) ≐ par i * g i L * Ap N L := by
  have h := inst2_lift3 (Γ := Γ) (par (var 0) * gK * Ev tB (var 1) (fact (var 2))) i N L
  simp at h; exact h

/-- `∑_{i<N} c(i) g_i A(N) = A(N) ∑_{i<N} c(i) g_i`. -/
theorem sum_qAp (N L : PTm n) : Γ ⊢[PRAAx] ap2 (sumF qAp) N (pairT N L) ≐ Ap N L * Ap N L := by
  refine LeanProofs.IPRA.Probability.Independence.sum_scale _ (LeanProofs.IPRA.Analysis.BaselFinite.eB tB) N
    (Ap N L) (fact L) (pairT N L) (.allI (.impI ?_))
  rw [shift_pairT, LeanProofs.IPRA.Analysis.BaselFinite.inst2_eB, inst2_t]
  have e : Syn.shift (Ap N L) = Ap (Syn.shift N) (Syn.shift L) := by simp [Syn.shift]
  have e' : Syn.shift (fact L) = fact (Syn.shift L) := by simp [Syn.shift]
  rw [e, e']
  refine (inst_qAp _ _ _).eqTrans ?_
  ipra_ring
theorem sum_pAm (N L : PTm n) : Γ ⊢[PRAAx] ap2 (sumF pAm) N (pairT N L) ≐ Am N L * Am N L := by
  refine LeanProofs.IPRA.Probability.Independence.sum_scale _ (LeanProofs.IPRA.Analysis.BaselFinite.oB tB) N
    (Am N L) (fact L) (pairT N L) (.allI (.impI ?_))
  rw [shift_pairT, LeanProofs.IPRA.Analysis.BaselFinite.inst2_oB, inst2_t]
  have e : Syn.shift (Am N L) = Am (Syn.shift N) (Syn.shift L) := by simp [Syn.shift]
  have e' : Syn.shift (fact L) = fact (Syn.shift L) := by simp [Syn.shift]
  rw [e, e']
  refine (inst_pAm _ _ _).eqTrans ?_
  ipra_ring
theorem sum_qAm (N L : PTm n) : Γ ⊢[PRAAx] ap2 (sumF qAm) N (pairT N L) ≐ Am N L * Ap N L := by
  refine LeanProofs.IPRA.Probability.Independence.sum_scale _ (LeanProofs.IPRA.Analysis.BaselFinite.eB tB) N
    (Am N L) (fact L) (pairT N L) (.allI (.impI ?_))
  rw [shift_pairT, LeanProofs.IPRA.Analysis.BaselFinite.inst2_eB, inst2_t]
  have e : Syn.shift (Am N L) = Am (Syn.shift N) (Syn.shift L) := by simp [Syn.shift]
  have e' : Syn.shift (fact L) = fact (Syn.shift L) := by simp [Syn.shift]
  rw [e, e']
  refine (inst_qAm _ _ _).eqTrans ?_
  ipra_ring
theorem sum_pAp (N L : PTm n) : Γ ⊢[PRAAx] ap2 (sumF pAp) N (pairT N L) ≐ Ap N L * Am N L := by
  refine LeanProofs.IPRA.Probability.Independence.sum_scale _ (LeanProofs.IPRA.Analysis.BaselFinite.oB tB) N
    (Ap N L) (fact L) (pairT N L) (.allI (.impI ?_))
  rw [shift_pairT, LeanProofs.IPRA.Analysis.BaselFinite.inst2_oB, inst2_t]
  have e : Syn.shift (Ap N L) = Ap (Syn.shift N) (Syn.shift L) := by simp [Syn.shift]
  have e' : Syn.shift (fact L) = fact (Syn.shift L) := by simp [Syn.shift]
  rw [e, e']
  refine (inst_pAp _ _ _).eqTrans ?_
  ipra_ring

/-- `lem:D` (`eq:D`), before clearing `N`: with `D⁺ = A⁺² + A⁻² + T⁻` and `D⁻ = 2 A⁺ A⁻ + T⁺`
(so `D_N = A_N² − T_N = D⁺ − D⁻`), `|D⁺ − D⁻| ≤ Conv(N)`. -/
theorem omitted (N L : PTm n) :
    Γ ⊢[PRAAx] le (Ap N L * Ap N L + Am N L * Am N L + Tm N L) (two * (Ap N L * Am N L) + Tp N L + Conv N L) ⋏
      le (two * (Ap N L * Am N L) + Tp N L) (Ap N L * Ap N L + Am N L * Am N L + Tm N L + Conv N L) := by
  have l1 := LeanProofs.IPRA.Analysis.PowerSums.sum_le (Γ := Γ) dPb (addBody dMb cv) (pairT N L) N (.allI (.impI (by
    rw [shift_pairT, inst2_addBody, inst2_addBody, inst2_addBody, inst2_addBody, inst2_addBody]
    refine le_congr ?_ ?_ (Prf.andE₁ (d_pt (L := Syn.shift L) Prf.hyp0))
    · exact (congrAdd (congrAdd (inst_qAp _ _ _) (inst_pAm _ _ _)) (inst_tM _ _ _)).eqSymm
    · exact (congrAdd (congrAdd (congrAdd (inst_qAm _ _ _) (inst_pAp _ _ _)) (inst_tP _ _ _)) (inst_cv _ _ _)).eqSymm)))
  have l2 := LeanProofs.IPRA.Analysis.PowerSums.sum_le (Γ := Γ) dMb (addBody dPb cv) (pairT N L) N (.allI (.impI (by
    rw [shift_pairT, inst2_addBody, inst2_addBody, inst2_addBody, inst2_addBody, inst2_addBody]
    refine le_congr ?_ ?_ (Prf.andE₂ (d_pt (L := Syn.shift L) Prf.hyp0))
    · exact (congrAdd (congrAdd (inst_qAm _ _ _) (inst_pAp _ _ _)) (inst_tP _ _ _)).eqSymm
    · exact (congrAdd (congrAdd (congrAdd (inst_qAp _ _ _) (inst_pAm _ _ _)) (inst_tM _ _ _)) (inst_cv _ _ _)).eqSymm)))
  have s1 := natEq (sum_qAp (Γ := Γ) N L); have s2 := natEq (sum_pAm (Γ := Γ) N L)
  have s3 := natEq (sum_qAm (Γ := Γ) N L); have s4 := natEq (sum_pAp (Γ := Γ) N L)
  have w1 := natEq (eq_add_of_le l1); have w2 := natEq (eq_add_of_le l2)
  refine .andI (le_of_eq_add (d := monus (ap2 (sumF (addBody dMb cv)) N (pairT N L)) (ap2 (sumF dPb) N (pairT N L))) ?_)
    (le_of_eq_add (d := monus (ap2 (sumF (addBody dPb cv)) N (pairT N L)) (ap2 (sumF dMb) N (pairT N L))) ?_)
  · ipra_lc w1 - natEq (sum_add (Γ := Γ) dMb cv N (pairT N L)) -
      natEq (sum_add (Γ := Γ) (addBody qAm pAp) tP N (pairT N L)) - natEq (sum_add (Γ := Γ) qAm pAp N (pairT N L)) +
      natEq (sum_add (Γ := Γ) (addBody qAp pAm) tM N (pairT N L)) + natEq (sum_add (Γ := Γ) qAp pAm N (pairT N L)) -
      s3 - s4 + s1 + s2
  · ipra_lc w2 - natEq (sum_add (Γ := Γ) dPb cv N (pairT N L)) -
      natEq (sum_add (Γ := Γ) (addBody qAp pAm) tM N (pairT N L)) - natEq (sum_add (Γ := Γ) qAp pAm N (pairT N L)) +
      natEq (sum_add (Γ := Γ) (addBody qAm pAp) tP N (pairT N L)) + natEq (sum_add (Γ := Γ) qAm pAp N (pairT N L)) -
      s1 - s2 + s3 + s4

/-- `lem:D` (`eq:D`), cleared by `F = L!` with `2N ≤ L`: `N D⁺ ≤ N D⁻ + F H(N)` and
`N D⁻ ≤ N D⁺ + F H(N)`, i.e. `|D_N| ≤ H_N/N`. -/
theorem omitted_bound {N L : PTm n} (hL : Γ ⊢[PRAAx] le (two * N) L) :
    Γ ⊢[PRAAx] le (N * (Ap N L * Ap N L + Am N L * Am N L + Tm N L))
        (N * (two * (Ap N L * Am N L) + Tp N L) + fact L * H N L) ⋏
      le (N * (two * (Ap N L * Am N L) + Tp N L))
        (N * (Ap N L * Ap N L + Am N L * Am N L + Tm N L) + fact L * H N L) := by
  have o := omitted (Γ := Γ) N L
  have d := natEq (diagonal hL)
  have w1 := natEq (eq_add_of_le (Prf.andE₁ o)); have w2 := natEq (eq_add_of_le (Prf.andE₂ o))
  refine .andI (le_of_eq_add (d := N * monus (two * (Ap N L * Am N L) + Tp N L + Conv N L)
      (Ap N L * Ap N L + Am N L * Am N L + Tm N L)) ?_)
    (le_of_eq_add (d := N * monus (Ap N L * Ap N L + Am N L * Am N L + Tm N L + Conv N L)
      (two * (Ap N L * Am N L) + Tp N L)) ?_)
  · ipra_lc 𝔞 N * w1 - d
  · ipra_lc 𝔞 N * w2 - d

open LeanProofs.IPRA.Analysis.BaselAverages (wB boundary_E) in
/-- `lem:E` for every `N = M + 1 ≤ L` (for `N = 1` the sum is empty). -/
theorem E_bound {M L : PTm n} (hL : Γ ⊢[PRAAx] le (succ M) L) :
    Γ ⊢[PRAAx] le (succ M * Ep' M L) (succ M * Em' M L + fact L * H (succ M) L) ⋏
      le (succ M * Em' M L) (succ M * Ep' M L + fact L * H (succ M) L) := by
  refine .orE (zero_or_succ M) ?_ ?_
  · have z1 := natEq ((congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.eB wB))
      (Prf.hyp0 : ((M ≐ zero) :: Γ) ⊢[PRAAx] _) (.eqRefl (pairT (succ M) L))).eqTrans (sum_zero _ _))
    have z2 := natEq ((congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.oB wB))
      (Prf.hyp0 : ((M ≐ zero) :: Γ) ⊢[PRAAx] _) (.eqRefl (pairT (succ M) L))).eqTrans (sum_zero _ _))
    refine .andI (le_of_eq_add (d := fact L * H (succ M) L) ?_) (le_of_eq_add (d := fact L * H (succ M) L) ?_)
    · ipra_lc (𝔞 M + 1) * z2 - (𝔞 M + 1) * z1
    · ipra_lc (𝔞 M + 1) * z1 - (𝔞 M + 1) * z2
  · have e : ((M ≐ succ (pred M)) :: Γ) ⊢[PRAAx] succ (pred M) ≐ M := Prf.hyp0.eqSymm
    have hL' : ((M ≐ succ (pred M)) :: Γ) ⊢[PRAAx] le (succ (succ (pred M))) L :=
      le_congr (congrSucc e).eqSymm (.eqRefl _) hL.wk
    have bE := boundary_E hL'
    have c1 := natEq (congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.eB wB)) e
      (congrPairT (congrSucc e) (.eqRefl L)))
    have c2 := natEq (congrAp2 (sumF (LeanProofs.IPRA.Analysis.BaselFinite.oB wB)) e
      (congrPairT (congrSucc e) (.eqRefl L)))
    have b1 := natEq (eq_add_of_le (Prf.andE₁ bE)); have b2 := natEq (eq_add_of_le (Prf.andE₂ bE))
    refine .andI (le_of_eq_add (d := monus (succ (succ (pred M)) * Od wB (succ (pred M)) (pairT (succ (succ (pred M))) L) +
        fact L * H (succ (succ (pred M))) L) (succ (succ (pred M)) * Ev wB (succ (pred M)) (pairT (succ (succ (pred M))) L))) ?_)
      (le_of_eq_add (d := monus (succ (succ (pred M)) * Ev wB (succ (pred M)) (pairT (succ (succ (pred M))) L) +
        fact L * H (succ (succ (pred M))) L) (succ (succ (pred M)) * Od wB (succ (pred M)) (pairT (succ (succ (pred M))) L))) ?_)
    · ipra_lc b1 -
        (𝔞 (Od wB (succ (pred M)) (pairT (succ (succ (pred M))) L)) - 𝔞 (Ev wB (succ (pred M)) (pairT (succ (succ (pred M))) L))) * natEq e -
        (𝔞 M + 1) * c2 - 𝔞 (fact L) * natEq (congrAp2 (sumF tB) (congrSucc e) (.eqRefl (fact L))) + (𝔞 M + 1) * c1
    · ipra_lc b2 -
        (𝔞 (Ev wB (succ (pred M)) (pairT (succ (succ (pred M))) L)) - 𝔞 (Od wB (succ (pred M)) (pairT (succ (succ (pred M))) L))) * natEq e -
        (𝔞 M + 1) * c1 - 𝔞 (fact L) * natEq (congrAp2 (sumF tB) (congrSucc e) (.eqRefl (fact L))) + (𝔞 M + 1) * c2

/-! ## The crucial finite comparison (`prop:core`) -/

open LeanProofs.IPRA.Analysis.BaselSquares (O) in
/-- `prop:core` (`eq:core`), cleared by `F = L!`: for `N = M + 1` and `2N + 1 ≤ L`, with
`X⁺ = 2(A⁺² + A⁻²)` and `X⁻ = O + 4 A⁺ A⁻` (so `X⁺ − X⁻ = F²(2A_N² − O_N)`),
`N X⁺ ≤ N X⁻ + 2 F H(N)` and `N X⁻ ≤ N X⁺ + 2 F H(N)`, i.e. `|2A_N² − O_N| ≤ 2H_N/N`.
The proof is `2A_N² − O_N = D_N + E_N` (from `eq:second`) with `lem:D` and `lem:E`. -/
theorem core {M L : PTm n} (hL : Γ ⊢[PRAAx] le (succ (two * succ M)) L) :
    Γ ⊢[PRAAx] le (succ M * (two * (Ap (succ M) L * Ap (succ M) L + Am (succ M) L * Am (succ M) L)))
        (succ M * (O (succ M) L + two * two * (Ap (succ M) L * Am (succ M) L)) + two * (fact L * H (succ M) L)) ⋏
      le (succ M * (O (succ M) L + two * two * (Ap (succ M) L * Am (succ M) L)))
        (succ M * (two * (Ap (succ M) L * Ap (succ M) L + Am (succ M) L * Am (succ M) L)) +
          two * (fact L * H (succ M) L)) := by
  have h2 : Γ ⊢[PRAAx] le (two * succ M) L := le_trans (le_succ_self _) hL
  have h1 : Γ ⊢[PRAAx] le (succ M) L :=
    le_trans (le_of_eq_add (d := succ M) (by ipra_ring)) h2
  have db := omitted_bound h2
  have eb := E_bound (M := M) h1
  have d1 := natEq (eq_add_of_le (Prf.andE₁ db)); have d2 := natEq (eq_add_of_le (Prf.andE₂ db))
  have e1 := natEq (eq_add_of_le (Prf.andE₁ eb)); have e2 := natEq (eq_add_of_le (Prf.andE₂ eb))
  refine .andI (le_of_eq_add (d := monus (succ M * (two * (Ap (succ M) L * Am (succ M) L) + Tp (succ M) L) +
        fact L * H (succ M) L) (succ M * (Ap (succ M) L * Ap (succ M) L + Am (succ M) L * Am (succ M) L + Tm (succ M) L)) +
      monus (succ M * Em' M L + fact L * H (succ M) L) (succ M * Ep' M L)) ?_)
    (le_of_eq_add (d := monus (succ M * (Ap (succ M) L * Ap (succ M) L + Am (succ M) L * Am (succ M) L + Tm (succ M) L) +
        fact L * H (succ M) L) (succ M * (two * (Ap (succ M) L * Am (succ M) L) + Tp (succ M) L)) +
      monus (succ M * Ep' M L + fact L * H (succ M) L) (succ M * Em' M L)) ?_)
  · ipra_lc d1 + e1 - (𝔞 M + 1) * natEq (second hL)
  · ipra_lc d2 + e2 + (𝔞 M + 1) * natEq (second hL)

end LeanProofs.IPRA.Analysis.BaselCore
