import IPRADerivations.Foundations.ChineseRemainder
import IPRADerivations.Foundations.MixedRadix
import IPRADerivations.Probability.TowerCommonDen
import IPRADerivations.Core.Search
import IPRADerivations.AnalyticNumberTheory.Multiplicative
import IPRADerivations.AnalyticNumberTheory.EulerProduct
import IPRADerivations.Combinatorics.LegendreDigits
import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.AnalyticNumberTheory.MobiusInversion

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

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.CrtCoprime

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.ChineseRemainder (crt_exists_at rem_eq_of_eq)
open LeanProofs.IPRA.Probability.TowerCommonDen (dvd_prod_term)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (eq_of_viol viol_of_eq)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_of_eq' eq_of_dvd' gcd_comm_one)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

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
  have h1 : Syn.subst ![i, z] (Syn.subst ![var 0, sndT (var 1)] (mS mB)) = inst2 (mS mB) i (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  have h2 : Syn.subst ![i, z] (Syn.subst ![var 0, sndT (var 1)] aB) = inst2 aB i (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, wB, PTm.subst_monus, subst_eqb, subst_ap2, h1, h2]
  simp [inst2]

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
    Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

/-- `H K y = ∑_{j<K} [gcd(m_j, ∏_{i<j} m_i) ≠ 1]`. -/
abbrev H (K y : PTm n) : PTm n := ap2 (sumF (hB mB)) K y

/-! ## Positivity and divisibility -/

theorem succ_pos' (t : PTm n) : Γ ⊢[PRAAx] succ t ≐ succ (pred (succ t)) := congrSucc (pred_succ _).eqSymm

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
    (h : Γ ⊢[PRAAx] dvd d M) : Γ ⊢[PRAAx] rem (rem x M) d ≐ rem x d := by
  have e1 := natEq (Prf.andE₁ (dm hM x))
  have e2 := natEq (eq_of_dvd' hd h)
  refine rem_eq_of_eq hd (k₁ := quo M d * quo x M) (k₂ := zero) ?_
  apply deriveNat; ipra_simps
  linear_combination -e1 - 𝔞 (quo x M) * e2

/-- `x ≡ X (mod M)` and `d ∣ M` give `x ≡ X (mod d)`. -/
theorem rem_down {d M x X : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] dvd d M) (hx : Γ ⊢[PRAAx] rem x M ≐ rem X M) : Γ ⊢[PRAAx] rem x d ≐ rem X d :=
  (remdvd hd hM h).eqSymm.eqTrans ((congrAp2 remF hx (.eqRefl _)).eqTrans (remdvd hd hM h))

theorem left_zero {a b : PTm n} (h : Γ ⊢[PRAAx] a + b ≐ zero) : Γ ⊢[PRAAx] a ≐ zero :=
  (monus_zero a).eqSymm.eqTrans (le_congr (.eqRefl _) h (le_add_right a b))

theorem right_zero {a b : PTm n} (h : Γ ⊢[PRAAx] a + b ≐ zero) : Γ ⊢[PRAAx] b ≐ zero :=
  (monus_zero b).eqSymm.eqTrans (le_congr (.eqRefl _) h (le_add_left b a))

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

/-- A common solution `x` of `X K y` modulo `L K` and of `a_K` modulo `m_K` gives a solution of the first `K + 1`
congruences below `L(K + 1)`; the search finds the least one. -/
theorem found {x K y : PTm n} (hx1 : Γ ⊢[PRAAx] rem x (L mB K y) ≐ rem (X mB aB K y) (L mB K y))
    (hx2 : Γ ⊢[PRAAx] rem x (inst2 (mS mB) K y) ≐ rem (inst2 aB K y) (inst2 (mS mB) K y))
    (hV : Γ ⊢[PRAAx] V mB aB (X mB aB K y) K y ≐ zero) :
    Γ ⊢[PRAAx] (V mB aB (X mB aB (succ K) y) (succ K) y ≐ zero) ⋏ lt (X mB aB (succ K) y) (L mB (succ K) y) := by
  have Lp := L_pos (Γ := Γ) mB (succ K) y
  let z := rem x (L mB (succ K) y)
  have zlt : Γ ⊢[PRAAx] lt z (L mB (succ K) y) := rem_lt' Lp x
  -- the first `K` terms
  have s1 : Γ ⊢[PRAAx] V mB aB z K y ≐ V mB aB (X mB aB K y) K y := by
    refine sum_congr_bounded (wB mB aB) (wB mB aB) (pairT z y) (pairT (X mB aB K y) y) K (.allI (.impI ?_))
    have hx1' : Γ.map Fm.shift ⊢[PRAAx] rem (Syn.shift x) (L mB (Syn.shift K) (Syn.shift y)) ≐
        rem (X mB aB (Syn.shift K) (Syn.shift y)) (L mB (Syn.shift K) (Syn.shift y)) := by
      simpa [Fm.shift, Syn.shift] using hx1.shift
    have sz : Syn.shift (pairT z y) =
        pairT (rem (Syn.shift x) (L mB (succ (Syn.shift K)) (Syn.shift y))) (Syn.shift y) := by
      simp [z, Syn.shift]
    have sX : Syn.shift (pairT (X mB aB K y) y) = pairT (X mB aB (Syn.shift K) (Syn.shift y)) (Syn.shift y) := by
      simp [Syn.shift]
    rw [sz, sX]
    exact term_eq mB aB Prf.hyp0 hx1'.wk
  -- the term `K`
  have hmK := m_pos (Γ := Γ) mB K y
  have dK : Γ ⊢[PRAAx] dvd (inst2 (mS mB) K y) (L mB (succ K) y) :=
    dvd_of_eq' hmK (w := L mB K y) ((L_succ mB K y).eqTrans (mul_comm _ _))
  have rK : Γ ⊢[PRAAx] rem z (inst2 (mS mB) K y) ≐ rem (inst2 aB K y) (inst2 (mS mB) K y) :=
    (remdvd hmK Lp dK).eqTrans hx2
  have tK : Γ ⊢[PRAAx] inst2 (wB mB aB) K (pairT z y) ≐ zero := by
    have r : Γ ⊢[PRAAx] rem z (succ (inst2 mB K y)) ≐ rem (inst2 aB K y) (succ (inst2 mB K y)) := by
      rw [mS_at] at rK; exact rK
    exact (w_at mB aB K z y).eqTrans (viol_of_eq r)
  have vz : Γ ⊢[PRAAx] V mB aB z (succ K) y ≐ zero :=
    (sum_succ' (wB mB aB) K (pairT z y)).eqTrans ((congrAdd (s1.eqTrans hV) tK).eqTrans (add_zero _))
  have sf := Search.search_found (f := fB mB aB) (N := L mB (succ K) y) (x := pairT (succ K) y)
    ((f_at mB aB z (succ K) y).eqTrans vz) zlt
  exact .andI ((f_at mB aB _ (succ K) y).eqSymm.eqTrans (Prf.andE₁ (Prf.andE₂ sf))) (Prf.andE₁ sf)

theorem rem_one' (t : PTm n) : Γ ⊢[PRAAx] rem t one ≐ zero := AnalyticNumberTheory.Euler.rem_one t

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
  have hmK := m_pos (Γ := Γ) mB K y
  have gL : Γ ⊢[PRAAx] gcd (L mB K y) (inst2 (mS mB) K y) ≐ one := gcd_comm_one Lp gK
  have hc : Γ ⊢[PRAAx] rem (X mB aB K y) (gcd (L mB K y) (inst2 (mS mB) K y)) ≐
      rem (inst2 aB K y) (gcd (L mB K y) (inst2 (mS mB) K y)) :=
    (congrAp2 remF (.eqRefl _) gL).eqTrans ((rem_one' _).eqTrans
      ((rem_one' _).eqSymm.eqTrans (congrAp2 remF (.eqRefl _) gL.eqSymm)))
  refine Prf.exE (crt_exists_at Lp hmK hc) ?_
  have hV' : Γ.map Fm.shift ⊢[PRAAx] V mB aB (X mB aB (Syn.shift K) (Syn.shift y)) (Syn.shift K) (Syn.shift y) ≐ zero := by
    simpa [Fm.shift, Syn.shift] using (Prf.andE₁ ih').shift
  have sL : Syn.shift (L mB K y) = L mB (Syn.shift K) (Syn.shift y) := by simp [Syn.shift]
  have sX : Syn.shift (X mB aB K y) = X mB aB (Syn.shift K) (Syn.shift y) := by simp [Syn.shift]
  have sM : Syn.shift (inst2 (mS mB) K y) = inst2 (mS mB) (Syn.shift K) (Syn.shift y) :=
    AnalyticNumberTheory.MobiusInversion.shift_inst2 _ _ _
  have sA : Syn.shift (inst2 aB K y) = inst2 aB (Syn.shift K) (Syn.shift y) :=
    AnalyticNumberTheory.MobiusInversion.shift_inst2 _ _ _
  have e : Fm.shift ((V mB aB (X mB aB (succ K) y) (succ K) y ≐ zero) ⋏ lt (X mB aB (succ K) y) (L mB (succ K) y)) =
      ((V mB aB (X mB aB (succ (Syn.shift K)) (Syn.shift y)) (succ (Syn.shift K)) (Syn.shift y) ≐ zero) ⋏
        lt (X mB aB (succ (Syn.shift K)) (Syn.shift y)) (L mB (succ (Syn.shift K)) (Syn.shift y))) := by
    simp [Fm.shift, Syn.shift]
  rw [e, sL, sX, sM, sA]
  exact found mB aB (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0) hV'.wk

theorem base (y : PTm n) :
    Γ ⊢[PRAAx] (V mB aB (X mB aB zero y) zero y ≐ zero) ⋏ lt (X mB aB zero y) (L mB zero y) := by
  have L0 : Γ ⊢[PRAAx] L mB zero y ≐ one := prod_zero (mS mB) y
  have lt0 : Γ ⊢[PRAAx] lt zero (L mB zero y) := le_congr (.eqRefl _) L0.eqSymm (le_refl _)
  have sf := Search.search_found (f := fB mB aB) (N := L mB zero y) (x := pairT zero y) (i := zero)
    ((f_at mB aB zero zero y).eqTrans (sum_zero _ _)) lt0
  exact .andI ((f_at mB aB _ zero y).eqSymm.eqTrans (Prf.andE₁ (Prf.andE₂ sf))) (Prf.andE₁ sf)

/-- **The Chinese remainder theorem for coprime moduli**: if every modulus is coprime to the product of the
previous ones (`H K y = 0`), the search `X K y` solves all `K` congruences and lies below `∏_{i<K} m_i`. -/
theorem crt_coprime {K y : PTm n} (hH : Γ ⊢[PRAAx] H mB K y ≐ zero) :
    Γ ⊢[PRAAx] (V mB aB (X mB aB K y) K y ≐ zero) ⋏ lt (X mB aB K y) (L mB K y) := by
  have hall : Γ ⊢[PRAAx] Fm.all ((H mB (var 0) (Syn.shift y) ≐ zero) ⟶
      ((V mB aB (X mB aB (var 0) (Syn.shift y)) (var 0) (Syn.shift y) ≐ zero) ⋏
        lt (X mB aB (var 0) (Syn.shift y)) (L mB (var 0) (Syn.shift y)))) := by
    refine PRA.qfInd _ ⟨trivial, trivial, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_le, subst_lt, subst_ap2, subst_pairT, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact .impI (base mB aB y)
    · simp only [Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_le, subst_lt, subst_ap2, subst_pairT, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact .impI (step mB aB Prf.hyp1 Prf.hyp0)
  have h2 := Prf.allE K hall
  simp only [Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_le, subst_lt, subst_ap2, subst_pairT, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h2
  exact .impE h2 hH

/-- **The solution**: `X K y ≡ a_i (mod m_i)` for every `i < K`. -/
theorem crt_coprime_at {K y i : PTm n} (hH : Γ ⊢[PRAAx] H mB K y ≐ zero) (hi : Γ ⊢[PRAAx] lt i K) :
    Γ ⊢[PRAAx] rem (X mB aB K y) (succ (inst2 mB i y)) ≐ rem (inst2 aB i y) (succ (inst2 mB i y)) :=
  eq_of_viol ((w_at mB aB i _ y).eqSymm.eqTrans (sum_zero_elim (wB mB aB) (Prf.andE₁ (crt_coprime mB aB hH)) hi))

end Step

end LeanProofs.IPRA.Foundations.CrtCoprime
