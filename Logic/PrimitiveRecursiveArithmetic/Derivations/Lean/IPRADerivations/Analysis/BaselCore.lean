import IPRADerivations.Analysis.BaselAverages

/-!
# The crucial finite comparison of the Basel packet

Packet: `analysis/basel_ipra`, `paper/basel_ipra.tex`, Sections `sec:triangle` and `sec:difference`:
`A_N = ∑_{j<N} (−1)^j/(2j+1)`, `O_N = ∑_{j<N} 1/(2j+1)²`, `H_N = ∑_{j<N} 1/(2j+1)`.

Everything is cleared by `F = L!` (with `2N + 1 ≤ L`), `g_j = F/(2j+1)`, and signed sums are kept as pairs of
natural numbers split by parity: `A⁺(N) = ∑_{j<N} (1 ∸ par j) g_j`, `A⁻(N) = ∑_{j<N} par j · g_j`, so that
`F A_N = A⁺ − A⁻`.

This first part provides

* `lift3`, `inst2_lift3`: a body over `(i, N, L)` read as a body over `(i, ⟨N, L⟩)`;
* `p_add`, `q_add`: the parity of a sum, `par (a + b) = (1 ∸ par a) par b + par a (1 ∸ par b)`;
* `shift_rel`: `A^±(K + j) = A^±(K) + (1 ∸ par K) E'^±(j) + par K · E'^∓(j)` for the parity parts `E'` of the
  shifted weights `g_{K+i}`;
* `tail_bound`: `|A_{K+m+1} − A_K| ≤ 1/(2K+1)`, from `lem:decreasing`.
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
  have pa := natEq (par_add (Γ := Γ) a b)
  have sa := natEq (par_sum (Γ := Γ) a); have sb := natEq (par_sum (Γ := Γ) b)
  apply deriveNat; ipra_simps
  linear_combination pa - 𝔞 (par b) * sa - 𝔞 (par a) * sb

theorem q_add (a b : PTm n) :
    Γ ⊢[PRAAx] monus one (par (a + b)) ≐ monus one (par a) * monus one (par b) + par a * par b := by
  have pa := natEq (par_add (Γ := Γ) a b); have s := natEq (par_sum (Γ := Γ) (a + b))
  have sa := natEq (par_sum (Γ := Γ) a); have sb := natEq (par_sum (Γ := Γ) b)
  apply deriveNat; ipra_simps
  linear_combination s - pa + (𝔞 (par b) - 1) * sa - 𝔞 (monus one (par a)) * sb

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
  have wg := natEq (inst_wS (Γ := Γ) j K L)
  have qa := natEq (q_add (Γ := Γ) K j); have pa := natEq (p_add (Γ := Γ) K j)
  refine .andI ?_ ?_
  · apply deriveNat; ipra_simps
    linear_combination A1 + i1 - 𝔞 (monus one (par K)) * E1 - 𝔞 (par K) * O1 -
      (𝔞 (monus one (par K)) * 𝔞 (monus one (par j)) + 𝔞 (par K) * 𝔞 (par j)) * wg + 𝔞 (g (K + j) L) * qa
  · apply deriveNat; ipra_simps
    linear_combination A2 + i2 - 𝔞 (monus one (par K)) * O1 - 𝔞 (par K) * E1 -
      (𝔞 (monus one (par K)) * 𝔞 (par j) + 𝔞 (par K) * 𝔞 (monus one (par j))) * wg + 𝔞 (g (K + j) L) * pa

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
  have z1 := natEq (sum_zero (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.eB wS) (pairT K L))
  have z2 := natEq (sum_zero (Γ := Γ) (LeanProofs.IPRA.Analysis.BaselFinite.oB wS) (pairT K L))
  refine .andI ?_ ?_
  · apply deriveNat; ipra_simps
    linear_combination a - 𝔞 (monus one (par K)) * z1 - 𝔞 (par K) * z2
  · apply deriveNat; ipra_simps
    linear_combination b - 𝔞 (monus one (par K)) * z2 - 𝔞 (par K) * z1

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
  apply deriveNat; ipra_simps; ring

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
    · apply deriveNat; ipra_simps
      linear_combination r2 - r1 + (𝔞 (Om (succ m) K L) - 𝔞 (Ep (succ m) K L)) * c +
        (𝔞 (Ep (succ m) K L) - 𝔞 (Om (succ m) K L)) * hp + d2 - w0
    · apply deriveNat; ipra_simps
      linear_combination r1 - r2 + (𝔞 (Ep (succ m) K L) - 𝔞 (Om (succ m) K L)) * c +
        (𝔞 (Om (succ m) K L) - 𝔞 (Ep (succ m) K L)) * hp + d1
  · have hp := natEq (Prf.hyp0 : ((par K ≐ one) :: Γ) ⊢[PRAAx] _)
    have w0 := natEq (w0P.wk (ψ := par K ≐ one))
    have c := natEq ((congrMonus (.eqRefl one) (Prf.hyp0 : ((par K ≐ one) :: Γ) ⊢[PRAAx] _)).eqTrans (monus_self _))
    have r1 := natEq ((Prf.andE₁ r).wk (ψ := par K ≐ one)); have r2 := natEq ((Prf.andE₂ r).wk (ψ := par K ≐ one))
    have d1 := natEq ((eq_add_of_le (Prf.andE₁ ad)).wk (ψ := par K ≐ one))
    have d2 := natEq ((eq_add_of_le (Prf.andE₂ ad)).wk (ψ := par K ≐ one))
    refine .andI (le_of_eq_add (d := monus (Ep (succ m) K L) (Om (succ m) K L) + g K L) ?_)
      (le_of_eq_add (d := monus (Om (succ m) K L + inst2 wS zero (pairT K L)) (Ep (succ m) K L)) ?_)
    · apply deriveNat; ipra_simps
      linear_combination r2 - r1 + (𝔞 (Ep (succ m) K L) - 𝔞 (Om (succ m) K L)) * hp +
        (𝔞 (Om (succ m) K L) - 𝔞 (Ep (succ m) K L)) * c + d1
    · apply deriveNat; ipra_simps
      linear_combination r1 - r2 + (𝔞 (Om (succ m) K L) - 𝔞 (Ep (succ m) K L)) * hp +
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
  have e := natEq (eq_add_of_le hi)
  refine le_of_eq_add (d := succ (two * monus N (succ i))) ?_
  apply deriveNat; ipra_simps
  linear_combination 2 * e

theorem dc_pt {i N L : PTm n} (hi : Γ ⊢[PRAAx] lt i N) (hL : Γ ⊢[PRAAx] le (two * N) L) :
    Γ ⊢[PRAAx] (two * N) * (g i L * g (monus N (succ i)) L) ≐ fact L * (g i L + g (monus N (succ i)) L) := by
  have hk : Γ ⊢[PRAAx] lt (monus N (succ i)) N :=
    le_of_eq_add (d := i) ((eq_add_of_le hi).eqTrans (by apply deriveNat; ipra_simps; ring))
  have e := natEq (eq_add_of_le hi)
  refine LeanProofs.IPRA.Analysis.BaselDiagonal.pair_pt (odd_pos _) (odd_pos _) (odd_dvd_L hi hL)
    (odd_dvd_L hk hL) ?_
  apply deriveNat; ipra_simps
  linear_combination -2 * e

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
  have a := natEq (sum_add (Γ := Γ) (lift3 gK) (lift3 rK) N (pairT N L))
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
  apply deriveNat; ipra_simps
  linear_combination e₁ - e₂ + 𝔞 (fact L) * (a + e₃ + e₄ - e₅)

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
      have a := natEq (sum_zero (Γ := le zero K :: Γ) f x); have b := natEq (sum_zero (Γ := le zero K :: Γ) h y)
      have d := natEq (sum_zero (Γ := le zero K :: Γ) k z)
      apply deriveNat; ipra_simps
      linear_combination a + 𝔞 c * b - d
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
      apply deriveNat; ipra_simps
      linear_combination s1 + 𝔞 (Syn.shift c) * s2 - s3 + i + p
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
  have z0 := natEq ((congrMonus (.eqRefl one) (par_zero (Γ := Γ))).eqTrans (monus_zero _))
  have z1 := natEq (par_zero (Γ := Γ) (n := n))
  have i0 := natEq ((inst_rf (Γ := Γ) zero (succ M) L).eqTrans (congrAp2 quoF (.eqRefl _)
    (congrSucc (congrMul (.eqRefl _) (monus_zero _)))))
  have a := natEq h1; have b := natEq h2; have c := natEq c1; have d := natEq c2
  refine .andI ?_ ?_
  · apply deriveNat; ipra_simps
    linear_combination a + 𝔞 (inst2 rf zero (pairT (succ M) L)) * z0 + i0 + c
  · apply deriveNat; ipra_simps
    linear_combination b + 𝔞 (inst2 rf zero (pairT (succ M) L)) * z1 + d

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
    le_trans hd (le_trans (le_of_eq_add (d := succ N) (by apply deriveNat; ipra_simps; ring)) hL)
  have h1L : Γ ⊢[PRAAx] le (succ (two * monus N (succ d₀))) L := by
    refine le_trans (le_of_eq_add (d := two * succ d₀) ?_) hL
    have e := natEq (eq_add_of_le hd)
    apply deriveNat; ipra_simps; linear_combination 2 * e
  have fu := natEq (LeanProofs.IPRA.Analysis.BaselSquares.fact_eq hdL)
  have f1 := natEq (LeanProofs.IPRA.Analysis.BaselSquares.fact_eq h1L)
  have f2 := natEq (LeanProofs.IPRA.Analysis.BaselSquares.fact_eq hL)
  have eN := natEq (eq_add_of_le hd)
  have s1 := natEq (LeanProofs.IPRA.Analysis.BaselAverages.C_split (Γ := Γ) (succ d₀) (succ N) L)
  have s0 := natEq (LeanProofs.IPRA.Analysis.BaselAverages.C_split (Γ := Γ) (succ d₀) N L)
  have hN := natEq (LeanProofs.IPRA.Analysis.BaselAverages.H_succ (Γ := Γ) N L)
  have em : Γ ⊢[PRAAx] monus (succ N) (succ d₀) ≐ succ (monus N (succ d₀)) :=
    (succ_monus_succ _ _).eqTrans (LeanProofs.IPRA.Analysis.BaselAverages.monus_succ_eq hd)
  have hm := natEq ((congrAp2 (sumF tB) em (.eqRefl (fact L))).eqTrans
    (LeanProofs.IPRA.Analysis.BaselAverages.H_succ (Γ := Γ) (monus N (succ d₀)) L))
  refine LeanProofs.IPRA.Combinatorics.BinomialIdentities.mul_cancel (D := succ (two * N)) (odd_pos _)
    (LeanProofs.IPRA.Combinatorics.BinomialIdentities.mul_cancel (D := succ (two * monus N (succ d₀))) (odd_pos _) ?_)
  apply deriveNat; ipra_simps
  linear_combination 2 * 𝔞 (fact L) * fu -
    2 * 𝔞 (quo (fact L) (succ d₀)) * 𝔞 (fact L) * eN -
    ((2 * 𝔞 (monus N (succ d₀)) + 1) * 𝔞 (quo (fact L) (succ d₀)) +
      2 * (2 * 𝔞 (monus N (succ d₀)) + 1) * 𝔞 (g (monus N (succ d₀)) L)) * f2 +
    ((2 * 𝔞 N + 1) * 𝔞 (quo (fact L) (succ d₀)) - 2 * 𝔞 (fact L)) * f1 +
    (2 * 𝔞 (monus N (succ d₀)) + 1) * (2 * 𝔞 N + 1) * 𝔞 (quo (fact L) (succ d₀)) * (-s1 + s0 + hN - hm)

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
  have bc := natEq (b_congr (d := succ M) (fst_pair (Γ := Γ) (succ (succ M)) L) (snd_pair (Γ := Γ) (succ (succ M)) L))
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
  · apply deriveNat; ipra_simps
    linear_combination a1 + t1 + 𝔞 (monus one (par M)) * bc
  · apply deriveNat; ipra_simps
    linear_combination a2 + t2 + 𝔞 (par M) * bc

end LeanProofs.IPRA.Analysis.BaselCore
