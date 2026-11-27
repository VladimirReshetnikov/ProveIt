import IPRADerivations.Foundations.CrtLcm

/-!
# The Chinese remainder theorem for a finite system

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, `el:crt`:

  "For positive moduli `m_0, …, m_{k−1}` and integer residues `a_i`, a simultaneous solution exists exactly when
  `gcd(m_i, m_j) ∣ (a_i − a_j)` (`i, j < k`). When it exists, there is a unique representative below
  `L = lcm(m_0, …, m_{k−1})`, and it is primitive recursively computable."

Moduli `m_i = mB(i, y) + 1` and residues `a_i = aB(i, y)` (natural numbers; the packet's integer residues are taken
modulo `m_i`) are given by bodies, `i < K`. With `L = Lc K y = lcm(m_0, …, m_{K−1})` (`CrtLcm`):

* `C K y = ∑_{j<K} ∑_{i<j} [a_i ≢ a_j (mod gcd(m_i, m_j))]`: compatibility as one equation; `compat_at`;
* **`necessary`**: a common solution makes the system compatible;
* `X K y = μ_{x < L}(x solves all K congruences)`, the primitive recursive representative (bounded search);
* `gB`, `G`: the moduli `gcd(m_i, m_J)`, `i < K`, and their lcm; `gcd_dvd_G`: `gcd(lcm(m_0, …, m_{K−1}), m_J)`
  divides `lcm_{i<K} gcd(m_i, m_J)` (from `CrtLcm.dist_dvd`), which is how the packet's prime-power argument
  enters;
* `step`: the previous solution is compatible with `a_K` modulo `gcd(L, m_K)`, so `ChineseRemainder.crt_exists_at`
  extends it;
* **`crt_general`**: `C K y = 0` gives that `X K y` solves all `K` congruences and `X K y < L`;
* **`crt_unique`**: two solutions below `L` are equal.
-/

namespace LeanProofs.IPRA.Foundations.CrtGeneral

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (lcm_pos)
open LeanProofs.IPRA.Foundations.CrtCoprime (mS m_pos fB rem_down left_zero right_zero)
open LeanProofs.IPRA.Foundations.CrtLcm (Lc Lc_zero Lc_succ Lc_pos m_dvd_Lc Lc_cong lcm_mono dist_dvd
  dvd_lcm_left dvd_lcm_right lcm_dvd_of)

variable {n : ℕ} {Γ : List (Fm PTm n)}

section System

variable (mB aB : PTm 2)

/-! ## Compatibility -/

/-- `[a_i ≢ a_j (mod gcd(m_i, m_j))]`, over `0 = i`, `1 = ⟨j, y⟩`. -/
def cB : PTm 2 :=
  monus one (eqb
    (rem (Syn.subst ![var 0, sndT (var 1)] aB)
      (gcd (Syn.subst ![var 0, sndT (var 1)] (mS mB)) (Syn.subst ![fstT (var 1), sndT (var 1)] (mS mB))))
    (rem (Syn.subst ![fstT (var 1), sndT (var 1)] aB)
      (gcd (Syn.subst ![var 0, sndT (var 1)] (mS mB)) (Syn.subst ![fstT (var 1), sndT (var 1)] (mS mB)))))

theorem sub_fst (b : PTm 2) (i z : PTm n) :
    Syn.subst ![i, z] (Syn.subst ![var 0, sndT (var 1)] b) = inst2 b i (sndT z) := by
  simp [subst_reindex2]

theorem sub_snd (b : PTm 2) (i z : PTm n) :
    Syn.subst ![i, z] (Syn.subst ![fstT (var 1), sndT (var 1)] b) = inst2 b (fstT z) (sndT z) := by
  simp [subst_reindex2]

/-- The modulus `gcd(m_i, m_j)`. -/
abbrev g (i j y : PTm n) : PTm n := gcd (inst2 (mS mB) i y) (inst2 (mS mB) j y)

theorem inst2_c (i z : PTm n) :
    inst2 (cB mB aB) i z = monus one (eqb (rem (inst2 aB i (sndT z)) (g mB i (fstT z) (sndT z)))
      (rem (inst2 aB (fstT z) (sndT z)) (g mB i (fstT z) (sndT z)))) := by
  show Syn.subst ![i, z] (cB mB aB) = _
  simp only [cB, PTm.subst_monus, subst_eqb, subst_ap2, subst_ex2, sub_fst, sub_snd,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
  rfl

theorem c_at (i j y : PTm n) :
    Γ ⊢[PRAAx] inst2 (cB mB aB) i (pairT j y) ≐
      monus one (eqb (rem (inst2 aB i y) (g mB i j y)) (rem (inst2 aB j y) (g mB i j y))) := by
  rw [inst2_c]
  have ey := snd_pair (Γ := Γ) j y
  have ej := fst_pair (Γ := Γ) j y
  have eg : Γ ⊢[PRAAx] g mB i (fstT (pairT j y)) (sndT (pairT j y)) ≐ g mB i j y :=
    DiophantineNumberTheory.QuarticStep.congrGcd (congrInst2 _ (.eqRefl _) ey) (congrInst2 _ ej ey)
  exact congrMonus (.eqRefl _) (AnalyticNumberTheory.Euler.congrEqb
    (congrAp2 remF (congrInst2 aB (.eqRefl _) ey) eg) (congrAp2 remF (congrInst2 aB ej ey) eg))

/-- The row `∑_{i<j} [a_i ≢ a_j (mod gcd(m_i, m_j))]`, over `0 = j`, `1 = y`. -/
abbrev oB : PTm 2 := ap2 (sumF (cB mB aB)) (var 0) (pairT (var 0) (var 1))

theorem inst2_o (j y : PTm n) : inst2 (oB mB aB) j y = ap2 (sumF (cB mB aB)) j (pairT j y) := by simp [inst2]

/-- `C K y = ∑_{j<K} ∑_{i<j} [a_i ≢ a_j (mod gcd(m_i, m_j))]`. -/
abbrev C (K y : PTm n) : PTm n := ap2 (sumF (oB mB aB)) K y

theorem compat_row {j y : PTm n} (h : Γ ⊢[PRAAx] ap2 (sumF (cB mB aB)) j (pairT j y) ≐ zero) {i : PTm n}
    (hi : Γ ⊢[PRAAx] lt i j) :
    Γ ⊢[PRAAx] rem (inst2 aB i y) (g mB i j y) ≐ rem (inst2 aB j y) (g mB i j y) :=
  eq_of_viol ((c_at mB aB i j y).eqSymm.eqTrans (sum_zero_elim (cB mB aB) h hi))

/-- Compatibility of `a_i` and `a_j` for `i < j < K`. -/
theorem compat_at {K y i j : PTm n} (h : Γ ⊢[PRAAx] C mB aB K y ≐ zero) (hj : Γ ⊢[PRAAx] lt j K)
    (hi : Γ ⊢[PRAAx] lt i j) :
    Γ ⊢[PRAAx] rem (inst2 aB i y) (g mB i j y) ≐ rem (inst2 aB j y) (g mB i j y) := by
  have r := sum_zero_elim (oB mB aB) h hj
  rw [inst2_o] at r
  exact compat_row mB aB r hi

/-- **Necessity**: if `x ≡ a_i (mod m_i)` and `x ≡ a_j (mod m_j)`, then `a_i ≡ a_j (mod gcd(m_i, m_j))`. -/
theorem necessary {x i j y : PTm n}
    (hi : Γ ⊢[PRAAx] rem x (inst2 (mS mB) i y) ≐ rem (inst2 aB i y) (inst2 (mS mB) i y))
    (hj : Γ ⊢[PRAAx] rem x (inst2 (mS mB) j y) ≐ rem (inst2 aB j y) (inst2 (mS mB) j y)) :
    Γ ⊢[PRAAx] rem (inst2 aB i y) (g mB i j y) ≐ rem (inst2 aB j y) (g mB i j y) := by
  have mi := m_pos (Γ := Γ) mB i y
  have mj := m_pos (Γ := Γ) mB j y
  have gp := gcd_pos (B := inst2 (mS mB) j y) mi
  have gd := gcd_dvd' (b := inst2 (mS mB) j y) mi
  have ri := rem_down gp mi (Prf.andE₁ gd) hi
  have rj := rem_down gp mj (Prf.andE₂ gd) hj
  exact ri.eqSymm.eqTrans rj

/-! ## The lcm of the gcds -/

/-- `gcd(m_i, m_J) − 1`, over `0 = i`, `1 = ⟨J, y⟩`; the moduli `gcd(m_i, m_J)`. -/
def gB : PTm 2 :=
  pred (gcd (Syn.subst ![var 0, sndT (var 1)] (mS mB)) (Syn.subst ![fstT (var 1), sndT (var 1)] (mS mB)))

theorem inst2_g (i z : PTm n) :
    inst2 (mS (gB mB)) i z = succ (pred (g mB i (fstT z) (sndT z))) := by
  show Syn.subst ![i, z] (succ (gB mB)) = _
  simp only [gB, ConciseIPRA.PTm.subst_succ, PTm.subst_pred, subst_ex2, sub_fst, sub_snd]
  rfl

theorem g_at (i J y : PTm n) : Γ ⊢[PRAAx] inst2 (mS (gB mB)) i (pairT J y) ≐ g mB i J y := by
  rw [inst2_g]
  have e : Γ ⊢[PRAAx] g mB i (fstT (pairT J y)) (sndT (pairT J y)) ≐ g mB i J y :=
    DiophantineNumberTheory.QuarticStep.congrGcd (congrInst2 _ (.eqRefl _) (snd_pair _ _))
      (congrInst2 _ (fst_pair _ _) (snd_pair _ _))
  exact (congrSucc (congrPred e)).eqTrans (gcd_pos (B := inst2 (mS mB) J y) (m_pos mB i y)).eqSymm

/-- `G K J y = lcm_{i<K} gcd(m_i, m_J)`. -/
abbrev G (K J y : PTm n) : PTm n := Lc (gB mB) K (pairT J y)

theorem gcd_one_dvd (c X : PTm n) : Γ ⊢[PRAAx] dvd (gcd one c) X :=
  dvd_trans' (gcd_pos (B := c) (congrSucc (pred_succ zero).eqSymm)) (congrSucc (pred_succ zero).eqSymm)
    (Prf.andE₁ (gcd_dvd' (b := c) (congrSucc (pred_succ zero).eqSymm))) (AnalyticNumberTheory.Euler.rem_one X)

theorem gd_step {K J y : PTm n}
    (ih : Γ ⊢[PRAAx] dvd (gcd (Lc mB K y) (inst2 (mS mB) J y)) (G mB K J y)) :
    Γ ⊢[PRAAx] dvd (gcd (Lc mB (succ K) y) (inst2 (mS mB) J y)) (G mB (succ K) J y) := by
  have Lp := Lc_pos (Γ := Γ) mB K y
  have mK := m_pos (Γ := Γ) mB K y
  have mJ := m_pos (Γ := Γ) mB J y
  have Gp := Lc_pos (Γ := Γ) (gB mB) K (pairT J y)
  have g1 := gcd_pos (B := inst2 (mS mB) J y) Lp
  have g2 := gcd_pos (B := inst2 (mS mB) J y) mK
  have eL := Lc_succ (Γ := Γ) mB K y
  have eG := Lc_succ (Γ := Γ) (gB mB) K (pairT J y)
  have d1 : Γ ⊢[PRAAx] dvd (gcd (Lc mB (succ K) y) (inst2 (mS mB) J y))
      (lcm (gcd (Lc mB K y) (inst2 (mS mB) J y)) (gcd (inst2 (mS mB) K y) (inst2 (mS mB) J y))) :=
    dvd_congr_left (DiophantineNumberTheory.QuarticStep.congrGcd eL (.eqRefl _)).eqSymm (dist_dvd Lp mK mJ)
  have d2 : Γ ⊢[PRAAx] dvd (lcm (gcd (Lc mB K y) (inst2 (mS mB) J y)) (gcd (inst2 (mS mB) K y) (inst2 (mS mB) J y)))
      (lcm (G mB K J y) (gcd (inst2 (mS mB) K y) (inst2 (mS mB) J y))) := lcm_mono g1 Gp g2 ih
  have e3 : Γ ⊢[PRAAx] lcm (G mB K J y) (gcd (inst2 (mS mB) K y) (inst2 (mS mB) J y)) ≐ G mB (succ K) J y :=
    (congrAp2 quoF (congrMul (.eqRefl _) (g_at mB K J y).eqSymm)
      (DiophantineNumberTheory.QuarticStep.congrGcd (.eqRefl _) (g_at mB K J y).eqSymm)).eqTrans eG.eqSymm
  exact dvd_congr e3 (dvd_trans' (gcd_pos (B := inst2 (mS mB) J y) (Lc_pos mB _ y)) (lcm_pos g1 g2) d1 d2)

/-- `gcd(lcm(m_0, …, m_{K−1}), m_J) ∣ lcm_{i<K} gcd(m_i, m_J)`. -/
theorem gcd_dvd_G (K J y : PTm n) :
    Γ ⊢[PRAAx] dvd (gcd (Lc mB K y) (inst2 (mS mB) J y)) (G mB K J y) := by
  have hall : Γ ⊢[PRAAx] Fm.all (dvd (gcd (Lc mB (var 0) (Syn.shift y)) (inst2 (mS mB) (Syn.shift J) (Syn.shift y)))
      (G mB (var 0) (Syn.shift J) (Syn.shift y))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_dvd, subst_ap2, subst_ex2, subst_pairT, subst_inst2, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ]
      exact dvd_congr_left (DiophantineNumberTheory.QuarticStep.congrGcd (Lc_zero mB y) (.eqRefl _)).eqSymm
        (gcd_one_dvd _ _)
    · simp only [subst_dvd, subst_ap2, subst_ex2, subst_pairT, subst_inst2, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_succ]
      exact gd_step mB Prf.hyp0
  have h2 := Prf.allE K hall
  simp only [subst_dvd, subst_ap2, subst_ex2, subst_pairT, subst_inst2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ] at h2
  exact h2

/-! ## The search and the step -/

/-- The least solution below `L = lcm(m_0, …, m_{K−1})`. -/
abbrev X (K y : PTm n) : PTm n := Search.mu (fB mB aB) (Lc mB K y) (pairT K y)

/-- A solution of the first `K` congruences solves the `i`-th one. -/
theorem sol_at {x K y i : PTm n} (h : Γ ⊢[PRAAx] CrtCoprime.V mB aB x K y ≐ zero) (hi : Γ ⊢[PRAAx] lt i K) :
    Γ ⊢[PRAAx] rem x (inst2 (mS mB) i y) ≐ rem (inst2 aB i y) (inst2 (mS mB) i y) :=
  CrtCoprime.solution_at mB aB h hi

/-- The solution `x` of the first `K` congruences is compatible with `a_K` modulo each `gcd(m_i, m_K)`. -/
theorem pt_compat {x K y i : PTm n} (hV : Γ ⊢[PRAAx] CrtCoprime.V mB aB x K y ≐ zero)
    (hrow : Γ ⊢[PRAAx] ap2 (sumF (cB mB aB)) K (pairT K y) ≐ zero) (hi : Γ ⊢[PRAAx] lt i K) :
    Γ ⊢[PRAAx] rem x (inst2 (mS (gB mB)) i (pairT K y)) ≐ rem (inst2 aB K y) (inst2 (mS (gB mB)) i (pairT K y)) := by
  have mi := m_pos (Γ := Γ) mB i y
  have gp := gcd_pos (B := inst2 (mS mB) K y) mi
  have r1 := rem_down gp mi (Prf.andE₁ (gcd_dvd' (b := inst2 (mS mB) K y) mi)) (sol_at mB aB hV hi)
  have r2 := compat_row mB aB hrow hi
  have e := g_at (Γ := Γ) mB i K y
  exact (congrAp2 remF (.eqRefl _) e).eqTrans ((r1.eqTrans r2).eqTrans (congrAp2 remF (.eqRefl _) e.eqSymm))

/-- A common solution `x` of `X` modulo `L` and of `a_K` modulo `m_K`, reduced modulo `L(K + 1)`, solves the first
`K + 1` congruences; the search finds the least one. -/
theorem found {x K y : PTm n} (hx1 : Γ ⊢[PRAAx] rem x (Lc mB K y) ≐ rem (X mB aB K y) (Lc mB K y))
    (hx2 : Γ ⊢[PRAAx] rem x (inst2 (mS mB) K y) ≐ rem (inst2 aB K y) (inst2 (mS mB) K y))
    (hV : Γ ⊢[PRAAx] CrtCoprime.V mB aB (X mB aB K y) K y ≐ zero) :
    Γ ⊢[PRAAx] (CrtCoprime.V mB aB (X mB aB (succ K) y) (succ K) y ≐ zero) ⋏ lt (X mB aB (succ K) y) (Lc mB (succ K) y) :=
  CrtCoprime.found_with_bound mB aB (rec2 (succ zero) (CrtLcm.stepB mB))
    (fun j y => Lc_pos mB j y) (fun hi => m_dvd_Lc mB hi) hx1 hx2 hV

alias rem_one' := LeanProofs.IPRA.AnalyticNumberTheory.Euler.rem_one

theorem step {K y : PTm n}
    (ih : Γ ⊢[PRAAx] (C mB aB K y ≐ zero) ⟶ ((CrtCoprime.V mB aB (X mB aB K y) K y ≐ zero) ⋏ lt (X mB aB K y) (Lc mB K y)))
    (hC : Γ ⊢[PRAAx] C mB aB (succ K) y ≐ zero) :
    Γ ⊢[PRAAx] (CrtCoprime.V mB aB (X mB aB (succ K) y) (succ K) y ≐ zero) ⋏ lt (X mB aB (succ K) y) (Lc mB (succ K) y) := by
  have hs : Γ ⊢[PRAAx] C mB aB K y + inst2 (oB mB aB) K y ≐ zero := (sum_succ' (oB mB aB) K y).eqSymm.eqTrans hC
  have ih' := Prf.impE ih (left_zero hs)
  have hrow0 := right_zero hs
  rw [inst2_o] at hrow0
  have hV := Prf.andE₁ ih'
  have Lp := Lc_pos (Γ := Γ) mB K y
  -- `X ≡ a_K` modulo `G = lcm_{i<K} gcd(m_i, m_K)`
  have hG : Γ ⊢[PRAAx] rem (X mB aB K y) (G mB K K y) ≐ rem (inst2 aB K y) (G mB K K y) := by
    refine Lc_cong (gB mB) (.allI (.impI ?_))
    have hV' : Γ.map Fm.shift ⊢[PRAAx] CrtCoprime.V mB aB (X mB aB (Syn.shift K) (Syn.shift y)) (Syn.shift K) (Syn.shift y) ≐ zero := by
      simpa [Fm.shift, Syn.shift] using hV.shift
    have hr' : Γ.map Fm.shift ⊢[PRAAx]
        ap2 (sumF (cB mB aB)) (Syn.shift K) (pairT (Syn.shift K) (Syn.shift y)) ≐ zero := by
      simpa [Fm.shift, Syn.shift] using hrow0.shift
    have sX : Syn.shift (X mB aB K y) = X mB aB (Syn.shift K) (Syn.shift y) := by simp [Syn.shift]
    have sA : Syn.shift (inst2 aB K y) = inst2 aB (Syn.shift K) (Syn.shift y) :=
      AnalyticNumberTheory.MobiusInversion.shift_inst2 _ _ _
    have sP : Syn.shift (pairT K y) = pairT (Syn.shift K) (Syn.shift y) := by simp [Syn.shift]
    rw [sX, sA, sP]
    exact pt_compat mB aB hV'.wk hr'.wk Prf.hyp0
  have hg : Γ ⊢[PRAAx] rem (X mB aB K y) (gcd (Lc mB K y) (inst2 (mS mB) K y)) ≐
      rem (inst2 aB K y) (gcd (Lc mB K y) (inst2 (mS mB) K y)) :=
    rem_down (gcd_pos (B := inst2 (mS mB) K y) Lp) (Lc_pos (gB mB) K (pairT K y)) (gcd_dvd_G mB K K y) hG
  exact CrtCoprime.extend_with_bound mB aB (rec2 (succ zero) (CrtLcm.stepB mB))
    (fun j y => Lc_pos mB j y) (fun hi => m_dvd_Lc mB hi) hV hg

theorem base (y : PTm n) :
    Γ ⊢[PRAAx] (CrtCoprime.V mB aB (X mB aB zero y) zero y ≐ zero) ⋏ lt (X mB aB zero y) (Lc mB zero y) := by
  exact CrtCoprime.search_solution_of_witness mB aB (sum_zero _ _)
    (le_congr (.eqRefl _) (Lc_zero (Γ := Γ) mB y).eqSymm (le_refl one))

/-- **`el:crt`, existence**: for a compatible system (`C K y = 0`), the search `X K y` solves all `K` congruences
and lies below `L = lcm(m_0, …, m_{K−1})`. -/
theorem crt_general {K y : PTm n} (hC : Γ ⊢[PRAAx] C mB aB K y ≐ zero) :
    Γ ⊢[PRAAx] (CrtCoprime.V mB aB (X mB aB K y) K y ≐ zero) ⋏ lt (X mB aB K y) (Lc mB K y) := by
  have hall : Γ ⊢[PRAAx] Fm.all ((C mB aB (var 0) (Syn.shift y) ≐ zero) ⟶
      ((CrtCoprime.V mB aB (X mB aB (var 0) (Syn.shift y)) (var 0) (Syn.shift y) ≐ zero) ⋏
        lt (X mB aB (var 0) (Syn.shift y)) (Lc mB (var 0) (Syn.shift y)))) := by
    ipra_qfind (⟨trivial, trivial, le_QF _ _⟩) [subst_le, subst_lt, subst_ap2, subst_pairT]
    · exact .impI (base mB aB y)
    · exact .impI (step mB aB Prf.hyp1 Prf.hyp0)
  exact .impE (by simpa using Prf.allE K hall) hC

/-- The representative solves the `i`-th congruence, `i < K`. -/
theorem crt_general_at {K y i : PTm n} (hC : Γ ⊢[PRAAx] C mB aB K y ≐ zero) (hi : Γ ⊢[PRAAx] lt i K) :
    Γ ⊢[PRAAx] rem (X mB aB K y) (inst2 (mS mB) i y) ≐ rem (inst2 aB i y) (inst2 (mS mB) i y) :=
  sol_at mB aB (Prf.andE₁ (crt_general mB aB hC)) hi

/-- **`el:crt`, uniqueness**: two solutions of the `K` congruences below `L` are equal. -/
theorem crt_unique {x x' K y : PTm n} (hx : Γ ⊢[PRAAx] CrtCoprime.V mB aB x K y ≐ zero) (hx' : Γ ⊢[PRAAx] CrtCoprime.V mB aB x' K y ≐ zero)
    (lx : Γ ⊢[PRAAx] lt x (Lc mB K y)) (lx' : Γ ⊢[PRAAx] lt x' (Lc mB K y)) : Γ ⊢[PRAAx] x ≐ x' := by
  have Lp := Lc_pos (Γ := Γ) mB K y
  have hc : Γ ⊢[PRAAx] rem x (Lc mB K y) ≐ rem x' (Lc mB K y) := by
    refine Lc_cong mB (.allI (.impI ?_))
    have h1 : Γ.map Fm.shift ⊢[PRAAx] CrtCoprime.V mB aB (Syn.shift x) (Syn.shift K) (Syn.shift y) ≐ zero := by
      simpa [Fm.shift, Syn.shift] using hx.shift
    have h2 : Γ.map Fm.shift ⊢[PRAAx] CrtCoprime.V mB aB (Syn.shift x') (Syn.shift K) (Syn.shift y) ≐ zero := by
      simpa [Fm.shift, Syn.shift] using hx'.shift
    exact (sol_at mB aB h1.wk Prf.hyp0).eqTrans (sol_at mB aB h2.wk Prf.hyp0).eqSymm
  have r1 := Prf.andE₂ (Division.div_mod_of_lt Lp lx)
  have r2 := Prf.andE₂ (Division.div_mod_of_lt Lp lx')
  exact r1.eqSymm.eqTrans (hc.eqTrans r2)

end System

end LeanProofs.IPRA.Foundations.CrtGeneral
