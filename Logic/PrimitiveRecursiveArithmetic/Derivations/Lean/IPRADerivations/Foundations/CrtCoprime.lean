import IPRADerivations.Foundations.MixedRadix
import IPRADerivations.Probability.TowerCommonDen
import IPRADerivations.AnalyticNumberTheory.MobiusInversion
import IPRADerivations.Core.Reindex

/-!
# The Chinese remainder theorem for a finite system of coprime moduli

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, `el:crt`:

  "For positive moduli `m_0, …, m_{k−1}` and integer residues `a_i`, a simultaneous solution exists … there is a
  unique representative below `L`, and it is primitive recursively computable. In particular pairwise coprime
  moduli admit arbitrary residues, with `L = ∏_i m_i`." Proof: "First prove the pairwise coprime case by
  successively applying Theorem `el:crt2`. The product of the previously used moduli is coprime to the next."

The system is given by two bodies: the moduli `m_i = mB(i, y) + 1` (positive by construction) and the residues
`a_i = aB(i, y)`, `i < K`, with a parameter `y`.

* `L K y = ∏_{i<K} m_i`; `V x K y = ∑_{i<K} [x ≢ a_i (mod m_i)]`, the number of violated congruences;
* `X K y = μ_{x < L}(V x K y = 0)`, the least solution below `L`, found by bounded search (`Core/Search`): the
  primitive recursive solution of the packet;
* `H K y = ∑_{j<K} [gcd(m_j, ∏_{i<j} m_i) ≠ 1]`: the hypothesis "the product of the previously used moduli is
  coprime to the next", as one equation;
* `remdvd`: `(x mod M) mod d = x mod d` for `d ∣ M`; `found`: a common solution of `X K y` modulo `L` and of `a_K`
  modulo `m_K` gives a solution of the first `K + 1` congruences below `L(K + 1)`;
* **`crt_coprime`**: `H K y = 0` gives `V (X K y) K y = 0` and `X K y < L K y`, by induction on `K` with the
  two-modulus theorem `ChineseRemainder.crt_exists_at` in the step;
* **`crt_coprime_at`**: then `X K y ≡ a_i (mod m_i)` for every `i < K`.

The general compatible system and the uniqueness of the representative are not derived here.
-/

namespace LeanProofs.IPRA.Foundations.CrtCoprime

open_ipra exports
open LeanProofs.IPRA.Probability.TowerCommonDen (dvd_prod_term)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm)

variable {n : ℕ} {Γ : List (Fm PTm n)}

section System

variable (mB aB : PTm 2)

/-- The modulus `m_i = mB(i, y) + 1`. -/
abbrev mS : PTm 2 := succ mB

theorem mS_at (i y : PTm n) : inst2 (mS mB) i y = succ (inst2 mB i y) := by simp [inst2]

/-- `L K y = ∏_{i<K} m_i`. -/
abbrev L (K y : PTm n) : PTm n := ap2 (prodF (mS mB)) K y

/-- `[x ≢ a_i (mod m_i)]`, over `0 = i`, `1 = ⟨x, y⟩`. -/
def wB : PTm 2 :=
  monus one (eqb (rem (fstT (var 1)) (Syn.subst ![var 0, sndT (var 1)] (mS mB)))
    (rem (Syn.subst ![var 0, sndT (var 1)] aB) (Syn.subst ![var 0, sndT (var 1)] (mS mB))))

theorem inst2_w (i z : PTm n) :
    inst2 (wB mB aB) i z = monus one (eqb (rem (fstT z) (inst2 (mS mB) i (sndT z)))
      (rem (inst2 aB i (sndT z)) (inst2 (mS mB) i (sndT z)))) := by
  simp [inst2, wB, PTm.subst_monus, subst_eqb, subst_ap2, subst_reindex2]

theorem w_at (i x y : PTm n) :
    Γ ⊢[PRAAx] inst2 (wB mB aB) i (pairT x y) ≐
      monus one (eqb (rem x (succ (inst2 mB i y))) (rem (inst2 aB i y) (succ (inst2 mB i y)))) := by
  rw [inst2_w, mS_at]
  have ey := snd_pair (Γ := Γ) x y
  have em : Γ ⊢[PRAAx] succ (inst2 mB i (sndT (pairT x y))) ≐ succ (inst2 mB i y) :=
    congrSucc (congrInst2 mB (.eqRefl _) ey)
  exact congrMonus (.eqRefl _) (AnalyticNumberTheory.Euler.congrEqb
    (congrAp2 remF (fst_pair _ _) em) (congrAp2 remF (congrInst2 aB (.eqRefl _) ey) em))

/-- `V x K y = ∑_{i<K} [x ≢ a_i (mod m_i)]`. -/
abbrev V (x K y : PTm n) : PTm n := ap2 (sumF (wB mB aB)) K (pairT x y)

/-- The search body `V x K y`, over `0 = x`, `1 = ⟨K, y⟩`. -/
abbrev fB : PTm 2 := ap2 (sumF (wB mB aB)) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))

theorem inst2_f (x z : PTm n) : inst2 (fB mB aB) x z = ap2 (sumF (wB mB aB)) (fstT z) (pairT x (sndT z)) := by
  simp [inst2]

theorem f_at (x K y : PTm n) : Γ ⊢[PRAAx] inst2 (fB mB aB) x (pairT K y) ≐ V mB aB x K y := by
  rw [inst2_f]
  exact congrAp2 (sumF (wB mB aB)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))

/-- The least solution below `L`. -/
abbrev X (K y : PTm n) : PTm n := Search.mu (fB mB aB) (L mB K y) (pairT K y)

/-- `[gcd(m_j, ∏_{i<j} m_i) ≠ 1]`, over `0 = j`, `1 = y`. -/
abbrev hB : PTm 2 := monus one (eqb (gcd (mS mB) (ap2 (prodF (mS mB)) (var 0) (var 1))) one)

theorem inst2_h (j y : PTm n) :
    inst2 (hB mB) j y = monus one (eqb (gcd (inst2 (mS mB) j y) (L mB j y)) one) := by
  simp only [inst2, hB, PTm.subst_monus, subst_eqb, subst_ex2, subst_ap2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

/-- `H K y = ∑_{j<K} [gcd(m_j, ∏_{i<j} m_i) ≠ 1]`. -/
abbrev H (K y : PTm n) : PTm n := ap2 (sumF (hB mB)) K y

/-! ## Positivity and divisibility -/

alias succ_pos' := Common.succ_pos

theorem m_pos (i y : PTm n) : Γ ⊢[PRAAx] inst2 (mS mB) i y ≐ succ (pred (inst2 (mS mB) i y)) := by
  rw [mS_at]; exact succ_pos' _

theorem L_pos (K y : PTm n) : Γ ⊢[PRAAx] L mB K y ≐ succ (pred (L mB K y)) :=
  prod_pos_bounded (mS mB) y K (.allI (.impI (m_pos mB _ _)))

theorem m_dvd {i K y : PTm n} (hi : Γ ⊢[PRAAx] lt i K) : Γ ⊢[PRAAx] dvd (inst2 (mS mB) i y) (L mB K y) :=
  dvd_prod_term (mS mB) (m_pos mB _ _) hi

theorem L_succ (K y : PTm n) : Γ ⊢[PRAAx] L mB (succ K) y ≐ L mB K y * inst2 (mS mB) K y :=
  Foundations.MixedRadix.prod_succ' (mS mB) K y

end System

/-- `(x mod M) mod d = x mod d` for `d ∣ M`, `d, M ≥ 1`. -/
theorem remdvd {d M x : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] dvd d M) : Γ ⊢[PRAAx] rem (rem x M) d ≐ rem x d :=
  Division.rem_rem_of_mul hd hM (eq_of_dvd' hd h)

/-- `x ≡ X (mod M)` and `d ∣ M` give `x ≡ X (mod d)`. -/
theorem rem_down {d M x X : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] dvd d M) (hx : Γ ⊢[PRAAx] rem x M ≐ rem X M) : Γ ⊢[PRAAx] rem x d ≐ rem X d :=
  (remdvd hd hM h).eqSymm.eqTrans ((congrAp2 remF hx (.eqRefl _)).eqTrans (remdvd hd hM h))

alias left_zero := Common.add_eq_zero_left

alias right_zero := Common.add_eq_zero_right

section Step

variable (mB aB : PTm 2)

/-- The term `i < K` of the violation count is unchanged when `X` is replaced by `x mod L(K + 1)` with
`x ≡ X (mod L K)`. -/
theorem term_eq {x X K y i : PTm n} (hi : Γ ⊢[PRAAx] lt i K) (hx : Γ ⊢[PRAAx] rem x (L mB K y) ≐ rem X (L mB K y)) :
    Γ ⊢[PRAAx] inst2 (wB mB aB) i (pairT (rem x (L mB (succ K) y)) y) ≐ inst2 (wB mB aB) i (pairT X y) := by
  have hmi := m_pos (Γ := Γ) mB i y
  have hi' : Γ ⊢[PRAAx] lt i (succ K) := le_trans hi (le_succ_self _)
  have r1 := remdvd (x := x) hmi (L_pos mB (succ K) y) (m_dvd mB (y := y) hi')
  have r2 := rem_down hmi (L_pos mB K y) (m_dvd mB (y := y) hi) hx
  have e : Γ ⊢[PRAAx] rem (rem x (L mB (succ K) y)) (succ (inst2 mB i y)) ≐ rem X (succ (inst2 mB i y)) := by
    rw [mS_at] at r1 r2
    exact r1.eqTrans r2
  exact (w_at mB aB i _ y).eqTrans ((congrMonus (.eqRefl _) (AnalyticNumberTheory.Euler.congrEqb e (.eqRefl _))).eqTrans
    (w_at mB aB i X y).eqSymm)

/-- A vanishing violation count certifies each congruence in the prefix. -/
theorem solution_at {x K y i : PTm n} (hV : Γ ⊢[PRAAx] V mB aB x K y ≐ zero)
    (hi : Γ ⊢[PRAAx] lt i K) :
    Γ ⊢[PRAAx] rem x (inst2 (mS mB) i y) ≐ rem (inst2 aB i y) (inst2 (mS mB) i y) := by
  rw [mS_at]
  exact eq_of_viol ((w_at mB aB i x y).eqSymm.eqTrans (sum_zero_elim (wB mB aB) hV hi))

private theorem zero_violation {x y i : PTm n}
    (h : Γ ⊢[PRAAx] rem x (inst2 (mS mB) i y) ≐ rem (inst2 aB i y) (inst2 (mS mB) i y)) :
    Γ ⊢[PRAAx] inst2 (wB mB aB) i (pairT x y) ≐ zero := by
  rw [mS_at] at h
  exact (w_at mB aB i x y).eqTrans (viol_of_eq h)

/-- The bounded search finds a solution whenever a witness lies below its bound. -/
theorem search_solution_of_witness {z K y M : PTm n}
    (hV : Γ ⊢[PRAAx] V mB aB z K y ≐ zero) (hz : Γ ⊢[PRAAx] lt z M) :
    Γ ⊢[PRAAx] (V mB aB (Search.mu (fB mB aB) M (pairT K y)) K y ≐ zero) ⋏
      lt (Search.mu (fB mB aB) M (pairT K y)) M := by
  have sf := Search.search_found ((f_at mB aB z K y).eqTrans hV) hz
  exact .andI ((f_at mB aB _ K y).eqSymm.eqTrans sf.andE₂.andE₁) sf.andE₁

/-- Extend a solution from `K` to `K + 1` using any positive search bound divisible by the prefix moduli. -/
theorem found_with_bound (B : PR 2)
    (positive : ∀ {d : ℕ} {Δ : List (Fm PTm d)} (j y : PTm d),
      Δ ⊢[PRAAx] ap2 B j y ≐ succ (pred (ap2 B j y)))
    (divides : ∀ {d : ℕ} {Δ : List (Fm PTm d)} {i j y : PTm d},
      (Δ ⊢[PRAAx] lt i j) → (Δ ⊢[PRAAx] dvd (inst2 (mS mB) i y) (ap2 B j y)))
    {x X K y : PTm n} (hx1 : Γ ⊢[PRAAx] rem x (ap2 B K y) ≐ rem X (ap2 B K y))
    (hx2 : Γ ⊢[PRAAx] rem x (inst2 (mS mB) K y) ≐ rem (inst2 aB K y) (inst2 (mS mB) K y))
    (hV : Γ ⊢[PRAAx] V mB aB X K y ≐ zero) :
    Γ ⊢[PRAAx] (V mB aB (Search.mu (fB mB aB) (ap2 B (succ K) y) (pairT (succ K) y)) (succ K) y ≐ zero) ⋏
      lt (Search.mu (fB mB aB) (ap2 B (succ K) y) (pairT (succ K) y)) (ap2 B (succ K) y) := by
  let z := rem x (ap2 B (succ K) y)
  have hprefix : Γ ⊢[PRAAx] V mB aB z K y ≐ zero := by
    refine sum_zero_of_bounded (wB mB aB) (pairT z y) K (.allI (.impI ?_))
    have hi : (lt (var 0) (Syn.shift K) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift K) := Prf.hyp0
    have hnext := le_trans hi (le_succ_self (Syn.shift K))
    have hx1' : Γ.map Fm.shift ⊢[PRAAx] rem (Syn.shift x) (ap2 B (Syn.shift K) (Syn.shift y)) ≐
        rem (Syn.shift X) (ap2 B (Syn.shift K) (Syn.shift y)) := by
      simpa [Fm.shift, Syn.shift] using hx1.shift
    have hV' : Γ.map Fm.shift ⊢[PRAAx] V mB aB (Syn.shift X) (Syn.shift K) (Syn.shift y) ≐ zero := by
      simpa [Fm.shift, Syn.shift] using hV.shift
    have hmi := m_pos (Γ := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift) mB (var 0) (Syn.shift y)
    have reduce := remdvd (x := Syn.shift x) hmi (positive (succ (Syn.shift K)) (Syn.shift y)) (divides hnext)
    have preserve := rem_down hmi (positive (Syn.shift K) (Syn.shift y)) (divides hi) hx1'.wk
    simpa [z, Syn.shift] using zero_violation mB aB (reduce.eqTrans (preserve.eqTrans (solution_at mB aB hV'.wk hi)))
  have next := zero_violation mB aB
    ((remdvd (m_pos mB K y) (positive (succ K) y) (divides (le_refl (succ K)))).eqTrans hx2)
  have allZero := (sum_succ' (wB mB aB) K (pairT z y)).eqTrans
    ((congrAdd hprefix next).eqTrans (add_zero zero))
  exact search_solution_of_witness mB aB allZero (rem_lt' (positive (succ K) y) x)

/-- Merge a compatible congruence and find an extended solution below the next search bound. -/
theorem extend_with_bound (B : PR 2)
    (positive : ∀ {d : ℕ} {Δ : List (Fm PTm d)} (j y : PTm d),
      Δ ⊢[PRAAx] ap2 B j y ≐ succ (pred (ap2 B j y)))
    (divides : ∀ {d : ℕ} {Δ : List (Fm PTm d)} {i j y : PTm d},
      (Δ ⊢[PRAAx] lt i j) → (Δ ⊢[PRAAx] dvd (inst2 (mS mB) i y) (ap2 B j y)))
    {x K y : PTm n} (hV : Γ ⊢[PRAAx] V mB aB x K y ≐ zero)
    (hc : Γ ⊢[PRAAx] rem x (gcd (ap2 B K y) (inst2 (mS mB) K y)) ≐
      rem (inst2 aB K y) (gcd (ap2 B K y) (inst2 (mS mB) K y))) :
    Γ ⊢[PRAAx] (V mB aB (Search.mu (fB mB aB) (ap2 B (succ K) y) (pairT (succ K) y)) (succ K) y ≐ zero) ⋏
      lt (Search.mu (fB mB aB) (ap2 B (succ K) y) (pairT (succ K) y)) (ap2 B (succ K) y) := by
  refine Prf.exE (crt_exists_at (positive K y) (m_pos mB K y) hc) ?_
  have hV' : Γ.map Fm.shift ⊢[PRAAx] V mB aB (Syn.shift x) (Syn.shift K) (Syn.shift y) ≐ zero := by
    simpa [Fm.shift, Syn.shift] using hV.shift
  simp only [Fm.shift, Fm.subst_and, Fm.subst_eq, subst_lt, subst_ap2, subst_pairT, subst_inst2,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.shift]
  exact found_with_bound mB aB B positive divides (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0) hV'.wk

/-- A common solution `x` of `X K y` modulo `L K` and of `a_K` modulo `m_K` gives a solution of the first `K + 1`
congruences below `L(K + 1)`; the search finds the least one. -/
theorem found {x K y : PTm n} (hx1 : Γ ⊢[PRAAx] rem x (L mB K y) ≐ rem (X mB aB K y) (L mB K y))
    (hx2 : Γ ⊢[PRAAx] rem x (inst2 (mS mB) K y) ≐ rem (inst2 aB K y) (inst2 (mS mB) K y))
    (hV : Γ ⊢[PRAAx] V mB aB (X mB aB K y) K y ≐ zero) :
    Γ ⊢[PRAAx] (V mB aB (X mB aB (succ K) y) (succ K) y ≐ zero) ⋏ lt (X mB aB (succ K) y) (L mB (succ K) y) :=
  found_with_bound mB aB (prodF (mS mB)) (fun j y => L_pos mB j y) (fun hi => m_dvd mB hi) hx1 hx2 hV

alias rem_one' := LeanProofs.IPRA.AnalyticNumberTheory.Euler.rem_one

/-- The induction step. -/
theorem step {K y : PTm n}
    (ih : Γ ⊢[PRAAx] (H mB K y ≐ zero) ⟶ ((V mB aB (X mB aB K y) K y ≐ zero) ⋏ lt (X mB aB K y) (L mB K y)))
    (hH : Γ ⊢[PRAAx] H mB (succ K) y ≐ zero) :
    Γ ⊢[PRAAx] (V mB aB (X mB aB (succ K) y) (succ K) y ≐ zero) ⋏ lt (X mB aB (succ K) y) (L mB (succ K) y) := by
  have hs : Γ ⊢[PRAAx] H mB K y + inst2 (hB mB) K y ≐ zero := (sum_succ' (hB mB) K y).eqSymm.eqTrans hH
  have ih' := Prf.impE ih (left_zero hs)
  have g0 := right_zero hs
  rw [inst2_h] at g0
  have gK : Γ ⊢[PRAAx] gcd (inst2 (mS mB) K y) (L mB K y) ≐ one := eq_of_viol g0
  have Lp := L_pos (Γ := Γ) mB K y
  have gL : Γ ⊢[PRAAx] gcd (L mB K y) (inst2 (mS mB) K y) ≐ one := gcd_comm_one Lp gK
  have hc : Γ ⊢[PRAAx] rem (X mB aB K y) (gcd (L mB K y) (inst2 (mS mB) K y)) ≐
      rem (inst2 aB K y) (gcd (L mB K y) (inst2 (mS mB) K y)) :=
    (congrAp2 remF (.eqRefl _) gL).eqTrans ((rem_one' _).eqTrans
      ((rem_one' _).eqSymm.eqTrans (congrAp2 remF (.eqRefl _) gL.eqSymm)))
  exact extend_with_bound mB aB (prodF (mS mB)) (fun j y => L_pos mB j y) (fun hi => m_dvd mB hi)
    ih'.andE₁ hc

theorem base (y : PTm n) :
    Γ ⊢[PRAAx] (V mB aB (X mB aB zero y) zero y ≐ zero) ⋏ lt (X mB aB zero y) (L mB zero y) := by
  exact search_solution_of_witness mB aB (sum_zero _ _)
    (le_congr (.eqRefl _) (prod_zero (Γ := Γ) (mS mB) y).eqSymm (le_refl one))

/-- **The Chinese remainder theorem for coprime moduli**: if every modulus is coprime to the product of the
previous ones (`H K y = 0`), the search `X K y` solves all `K` congruences and lies below `∏_{i<K} m_i`. -/
theorem crt_coprime {K y : PTm n} (hH : Γ ⊢[PRAAx] H mB K y ≐ zero) :
    Γ ⊢[PRAAx] (V mB aB (X mB aB K y) K y ≐ zero) ⋏ lt (X mB aB K y) (L mB K y) := by
  have hall : Γ ⊢[PRAAx] Fm.all ((H mB (var 0) (Syn.shift y) ≐ zero) ⟶
      ((V mB aB (X mB aB (var 0) (Syn.shift y)) (var 0) (Syn.shift y) ≐ zero) ⋏
        lt (X mB aB (var 0) (Syn.shift y)) (L mB (var 0) (Syn.shift y)))) := by
    ipra_qfind (⟨trivial, trivial, le_QF _ _⟩) [subst_le, subst_lt, subst_ap2, subst_pairT]
    · exact .impI (base mB aB y)
    · exact .impI (step mB aB Prf.hyp1 Prf.hyp0)
  exact .impE (by simpa using Prf.allE K hall) hH

/-- **The solution**: `X K y ≡ a_i (mod m_i)` for every `i < K`. -/
theorem crt_coprime_at {K y i : PTm n} (hH : Γ ⊢[PRAAx] H mB K y ≐ zero) (hi : Γ ⊢[PRAAx] lt i K) :
    Γ ⊢[PRAAx] rem (X mB aB K y) (succ (inst2 mB i y)) ≐ rem (inst2 aB i y) (succ (inst2 mB i y)) := by
  have h := solution_at mB aB (crt_coprime mB aB hH).andE₁ hi
  rw [mS_at] at h
  exact h

end Step

end LeanProofs.IPRA.Foundations.CrtCoprime
