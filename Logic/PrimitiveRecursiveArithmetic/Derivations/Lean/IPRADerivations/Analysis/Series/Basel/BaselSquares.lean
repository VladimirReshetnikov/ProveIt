import IPRADerivations.Analysis.Series.Basel.BaselFinite
import IPRADerivations.Analysis.Series.Basel.BaselDiagonal

/-!
# Square sums of the Basel packet

Packet: `analysis/basel_ipra`, `paper/basel_ipra.tex`, Section `sec:allsquares`:
`S_n = ∑_{j=1}^{n} 1/j²` and `O_N = ∑_{j<N} 1/(2j+1)²`.

Denominators are cleared by `F = L!` for a bound `L` on every denominator used, so that `q_j = F/j` is
exact for `1 ≤ j ≤ L`. With `S(M) = ∑_{j=1}^{M} q_j² = F² S_M` and `O(N) = ∑_{j<N} q_{2j+1}² = F² O_N`,
and writing `N = N₀ + 1`:

* `pt`: for `2 ≤ j ≤ L`, `F q_{j−1} = q_j² + F q_j + (j−1) h²` with `h = q_{j−1} − q_j`; in particular
  `1/j² ≤ 1/(j−1) − 1/j` (the paper's comparison);
* `tail` (`lem:tail`, `eq:tail`): for `N ≤ m ≤ L`, `S(N) ≤ S(m)` and `S(m) + F q_m ≤ S(N) + F q_N`, i.e.
  `0 ≤ S_m − S_N ≤ 1/N − 1/m`;
* `annulus_up`, `annulus_low` (`eq:annulus`): for `2N ≤ L`, `2N S(2N) ≤ 2N S(N) + F²` and
  `4N S(N) + F² ≤ 4N S(2N)`, i.e. `1/(4N) ≤ S_{2N} − S_N ≤ 1/(2N)`;
* `odd_even` (`eq:oddeven`): for `2N ≤ L`, `4 O(N) + S(N) = 4 S(2N)`, i.e. `O_N = S_{2N} − S_N/4`;
* `compare` (`lem:compare`, `eq:compare`): for `N ≤ n`, `2N ≤ L`, `n ≤ L`,
  `4N O(N) ≤ 3N S(n) + 2F²` and `3N S(n) ≤ 4N O(N) + 2F²`, i.e. `|O_N − (3/4) S_n| ≤ 1/(2N)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BaselSquares

open_ipra
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (dvd_fact)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd')
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (quo_anti)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.DiophantineNumberTheory.Hurwitz (add_le_add)
open LeanProofs.IPRA.Analysis.BaselFinite (odd_pos)
open LeanProofs.IPRA.Analysis.Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Definitions -/

/-- `q_j = L!/j`. -/
abbrev qf (j L : PTm n) : PTm n := quo (fact L) j
/-- `q_j²`. -/
abbrev qq (j L : PTm n) : PTm n := qf j L * qf j L

/-- `q_{i+1}²` and `q_{2i+1}²` over `0 = i`, `1 = L`. -/
abbrev sB : PTm 2 := quo (fact (var 1)) (succ (var 0)) * quo (fact (var 1)) (succ (var 0))
abbrev oB : PTm 2 := quo (fact (var 1)) (succ (two * var 0)) * quo (fact (var 1)) (succ (two * var 0))

/-- `S(M) = ∑_{j=1}^{M} q_j²` and `O(N) = ∑_{j<N} q_{2j+1}²`. -/
abbrev S (M L : PTm n) : PTm n := ap2 (sumF sB) M L
abbrev O (N L : PTm n) : PTm n := ap2 (sumF oB) N L

theorem inst2_s (i L : PTm n) : inst2 sB i L = qq (succ i) L := by simp [inst2]
theorem inst2_o (i L : PTm n) : inst2 oB i L = qq (succ (two * i)) L := by simp [inst2]

theorem S_succ (M L : PTm n) : Γ ⊢[PRAAx] S (succ M) L ≐ S M L + qq (succ M) L := by
  have h := sum_succ' (Γ := Γ) sB M L
  rw [inst2_s] at h
  exact h

theorem O_succ (N L : PTm n) : Γ ⊢[PRAAx] O (succ N) L ≐ O N L + qq (succ (two * N)) L := by
  have h := sum_succ' (Γ := Γ) oB N L
  rw [inst2_o] at h
  exact h

/-- `L! = j q_j` for `1 ≤ j = a + 1 ≤ L`. -/
theorem fact_eq {a L : PTm n} (h : Γ ⊢[PRAAx] le (succ a) L) :
    Γ ⊢[PRAAx] fact L ≐ succ a * qf (succ a) L :=
  eq_of_dvd' (odd_pos a) (dvd_fact h)

/-! ## The pointwise comparison -/

/-- For `j = a + 2 ≤ L`: `F q_{j−1} = q_j² + F q_j + (j−1) h²`, `h = q_{j−1} − q_j`. -/
theorem pt {a L : PTm n} (h : Γ ⊢[PRAAx] le (succ (succ a)) L) :
    Γ ⊢[PRAAx] fact L * qf (succ a) L ≐ qq (succ (succ a)) L + fact L * qf (succ (succ a)) L +
      succ a * (monus (qf (succ a) L) (qf (succ (succ a)) L) * monus (qf (succ a) L) (qf (succ (succ a)) L)) := by
  ipra_lc -(𝔞 (qf (succ (succ a)) L) - 𝔞 (monus (qf (succ a) L) (qf (succ (succ a)) L))) * natEq (fact_eq (le_trans (le_succ_self _) h)) +
    𝔞 (qf (succ (succ a)) L) * natEq (fact_eq h) -
    ((𝔞 a + 1) * (𝔞 (qf (succ (succ a)) L) - 𝔞 (monus (qf (succ a) L) (qf (succ (succ a)) L))) - 𝔞 (fact L)) * natEq (eq_add_of_le (quo_anti (Γ := Γ) (F := fact L) (odd_pos a) (le_succ_self (succ a))))

/-! ## Runs of terms bounded below -/

theorem run_step {d M K L : PTm n}
    (ih : Γ ⊢[PRAAx] le (M + d) K ⟶ le (S M L + d * qq K L) (S (M + d) L))
    (h : Γ ⊢[PRAAx] le (M + succ d) K) :
    Γ ⊢[PRAAx] le (S M L + succ d * qq K L) (S (M + succ d) L) := by
  have e : Γ ⊢[PRAAx] M + succ d ≐ succ (M + d) := add_succ _ _
  have hK : Γ ⊢[PRAAx] le (succ (M + d)) K := le_congr e (.eqRefl _) h
  have ihd := Prf.impE ih (le_trans (le_succ_self _) hK)
  have hq := quo_anti (F := fact L) (odd_pos (M + d)) hK
  have eS : Γ ⊢[PRAAx] S (M + succ d) L ≐ S (M + d) L + qq (succ (M + d)) L :=
    (congrAp2 (sumF sB) e (.eqRefl _)).eqTrans (S_succ _ _)
  refine le_congr ?_ eS.eqSymm (add_le_add ihd (le_mul_mono hq hq))
  ipra_ring

/-- Variables: `0 = d`, `1 = M`, `2 = K`, `3 = L`. -/
private abbrev runF : Fm PTm 4 :=
  le (var 1 + var 0) (var 2) ⟶ le (S (var 1) (var 3) + var 0 * qq (var 2) (var 3)) (S (var 1 + var 0) (var 3))

private theorem run₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] runF := by
  ipra_ind (⟨le_QF _ _, le_QF _ _⟩) [subst_le, subst_ap2]
  · refine .impI (le_congr ?_ (congrAp2 (sumF sB) (add_zero _) (.eqRefl _)).eqSymm (le_refl _))
    ipra_ring
  · exact .impI (run_step Prf.hyp1 Prf.hyp0)

/-- For `M + d ≤ K`: `S(M) + d q_K² ≤ S(M + d)`. -/
theorem run {M d K L : PTm n} (h : Γ ⊢[PRAAx] le (M + d) K) :
    Γ ⊢[PRAAx] le (S M L + d * qq K L) (S (M + d) L) := by
  have i := inst (Γ := Γ) run₀ (![d, M, K, L] : Fin 4 → PTm n)
  simp at i
  exact Prf.impE i h

/-- `S` is monotone: `S(N) ≤ S(m)` for `N ≤ m`. -/
theorem S_mono {N m L : PTm n} (h : Γ ⊢[PRAAx] le N m) : Γ ⊢[PRAAx] le (S N L) (S m L) := by
  have e := eq_add_of_le h
  have r := run (Γ := Γ) (L := L) (K := N + monus m N) (le_refl _)
  exact le_trans (le_add_right _ _) (le_congr (.eqRefl _) (congrAp2 (sumF sB) e.eqSymm (.eqRefl _)) r)

/-! ## The tail -/

theorem tail_step {N₀ d L : PTm n}
    (ih : Γ ⊢[PRAAx] le (succ (N₀ + d)) L ⟶
      le (S (succ (N₀ + d)) L + fact L * qf (succ (N₀ + d)) L) (S (succ N₀) L + fact L * qf (succ N₀) L))
    (h : Γ ⊢[PRAAx] le (succ (N₀ + succ d)) L) :
    Γ ⊢[PRAAx] le (S (succ (N₀ + succ d)) L + fact L * qf (succ (N₀ + succ d)) L)
      (S (succ N₀) L + fact L * qf (succ N₀) L) := by
  have e : Γ ⊢[PRAAx] succ (N₀ + succ d) ≐ succ (succ (N₀ + d)) := congrSucc (add_succ _ _)
  have h' : Γ ⊢[PRAAx] le (succ (succ (N₀ + d))) L := le_congr e (.eqRefl _) h
  refine le_of_eq_add (d := monus (S (succ N₀) L + fact L * qf (succ N₀) L)
      (S (succ (N₀ + d)) L + fact L * qf (succ (N₀ + d)) L) +
    succ (N₀ + d) * (monus (qf (succ (N₀ + d)) L) (qf (succ (succ (N₀ + d))) L) *
      monus (qf (succ (N₀ + d)) L) (qf (succ (succ (N₀ + d))) L))) ?_
  ipra_lc natEq (eq_add_of_le (Prf.impE ih (le_trans (le_succ_self _) h'))) -
    natEq ((congrAp2 (sumF sB) e (.eqRefl _)).eqTrans (S_succ (Γ := Γ) _ L)) + natEq (pt h') -
    𝔞 (fact L) * natEq (congrAp2 quoF (.eqRefl (fact L)) e)

/-- Variables: `0 = d`, `1 = N₀`, `2 = L`. -/
private abbrev tailF : Fm PTm 3 :=
  le (succ (var 1 + var 0)) (var 2) ⟶
    le (S (succ (var 1 + var 0)) (var 2) + fact (var 2) * qf (succ (var 1 + var 0)) (var 2))
      (S (succ (var 1)) (var 2) + fact (var 2) * qf (succ (var 1)) (var 2))

private theorem tail₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] tailF := by
  ipra_ind (⟨le_QF _ _, le_QF _ _⟩) [subst_le, subst_ap2]
  · refine .impI (le_congr ?_ (.eqRefl _) (le_refl _))
    exact congrAdd (congrAp2 (sumF sB) (congrSucc (add_zero _)) (.eqRefl _))
      (congrMul (.eqRefl _) (congrAp2 quoF (.eqRefl _) (congrSucc (add_zero _)))) |>.eqSymm
  · exact .impI (tail_step Prf.hyp1 Prf.hyp0)

/-- `lem:tail` (`eq:tail`), cleared by `F = L!`: for `1 ≤ N ≤ m ≤ L` (`N = N₀ + 1`),
`S(N) ≤ S(m)` and `S(m) + F q_m ≤ S(N) + F q_N`, i.e. `0 ≤ S_m − S_N ≤ 1/N − 1/m`. -/
theorem tail {N₀ m L : PTm n} (hm : Γ ⊢[PRAAx] le (succ N₀) m) (hL : Γ ⊢[PRAAx] le m L) :
    Γ ⊢[PRAAx] le (S (succ N₀) L) (S m L) ⋏
      le (S m L + fact L * qf m L) (S (succ N₀) L + fact L * qf (succ N₀) L) := by
  refine .andI (S_mono hm) ?_
  have i := inst (Γ := Γ) tail₀ (![monus m (succ N₀), N₀, L] : Fin 3 → PTm n)
  simp at i
  have e : Γ ⊢[PRAAx] succ (N₀ + monus m (succ N₀)) ≐ m := by
    ipra_lc -natEq (eq_add_of_le hm)
  have r := Prf.impE i (le_congr e.eqSymm (.eqRefl _) hL)
  exact le_congr (congrAdd (congrAp2 (sumF sB) e (.eqRefl _)) (congrMul (.eqRefl _) (congrAp2 quoF (.eqRefl _) e)))
    (.eqRefl _) r

/-! ## The annulus -/

/-- `q_N = 2 q_{2N}` for `2N ≤ L` (`N = N₀ + 1`). -/
theorem q_double {N₀ L : PTm n} (h : Γ ⊢[PRAAx] le (two * succ N₀) L) :
    Γ ⊢[PRAAx] qf (succ N₀) L ≐ two * qf (two * succ N₀) L := by
  have e : Γ ⊢[PRAAx] two * succ N₀ ≐ succ (succ (two * N₀)) := by ipra_ring
  have h₂ : Γ ⊢[PRAAx] le (succ (succ (two * N₀))) L := le_congr e (.eqRefl _) h
  have h₁ : Γ ⊢[PRAAx] le (succ N₀) L :=
    le_trans (le_of_eq_add (d := succ N₀) (by ipra_ring)) h
  have a := natEq (fact_eq h₁); have b := natEq (fact_eq h₂)
  refine mul_cancel (D := succ N₀) (congrSucc (pred_succ _).eqSymm) ?_
  ipra_lc -a + b - (2 * 𝔞 N₀ + 2) * natEq (congrAp2 quoF (.eqRefl (fact L)) e)

/-- `eq:annulus`, upper half: `2N S(2N) ≤ 2N S(N) + F²` for `2N ≤ L`, i.e. `S_{2N} − S_N ≤ 1/(2N)`. -/
theorem annulus_up {N₀ L : PTm n} (h : Γ ⊢[PRAAx] le (two * succ N₀) L) :
    Γ ⊢[PRAAx] le (two * succ N₀ * S (two * succ N₀) L) (two * succ N₀ * S (succ N₀) L + fact L * fact L) := by
  have hm : Γ ⊢[PRAAx] le (succ N₀) (two * succ N₀) := le_of_eq_add (d := succ N₀) (by ipra_ring)
  have e : Γ ⊢[PRAAx] two * succ N₀ ≐ succ (succ (two * N₀)) := by ipra_ring
  have f := natEq ((fact_eq (le_congr e (.eqRefl _) h)).eqTrans
    (congrMul e.eqSymm (congrAp2 quoF (.eqRefl (fact L)) e.eqSymm)))
  refine le_of_eq_add (d := two * succ N₀ * monus (S (succ N₀) L + fact L * qf (succ N₀) L)
    (S (two * succ N₀) L + fact L * qf (two * succ N₀) L)) ?_
  ipra_lc (2 * 𝔞 N₀ + 2) * natEq (eq_add_of_le (Prf.andE₂ (tail hm h))) -
    (2 * 𝔞 N₀ + 2) * 𝔞 (fact L) * natEq (q_double h) + 𝔞 (fact L) * f

/-- `eq:annulus`, lower half: `4N S(N) + F² ≤ 4N S(2N)` for `2N ≤ L`, i.e. `1/(4N) ≤ S_{2N} − S_N`. -/
theorem annulus_low {N₀ L : PTm n} (h : Γ ⊢[PRAAx] le (two * succ N₀) L) :
    Γ ⊢[PRAAx] le (two * two * succ N₀ * S (succ N₀) L + fact L * fact L) (two * two * succ N₀ * S (two * succ N₀) L) := by
  have e₀ : Γ ⊢[PRAAx] succ N₀ + succ N₀ ≐ two * succ N₀ := by ipra_ring
  have r := run (Γ := Γ) (L := L) (M := succ N₀) (d := succ N₀) (K := two * succ N₀) (le_congr e₀.eqSymm (.eqRefl _) (le_refl _))
  have e : Γ ⊢[PRAAx] two * succ N₀ ≐ succ (succ (two * N₀)) := by ipra_ring
  have f := natEq ((fact_eq (le_congr e (.eqRefl _) h)).eqTrans
    (congrMul e.eqSymm (congrAp2 quoF (.eqRefl (fact L)) e.eqSymm)))
  refine le_of_eq_add (d := two * two * succ N₀ * monus (S (succ N₀ + succ N₀) L)
    (S (succ N₀) L + succ N₀ * qq (two * succ N₀) L)) ?_
  ipra_lc (4 * 𝔞 N₀ + 4) * natEq (eq_add_of_le r) -
    (4 * 𝔞 N₀ + 4) * natEq (congrAp2 (sumF sB) e₀ (.eqRefl L) (Γ := Γ)) -
    (𝔞 (fact L) + (2 * 𝔞 N₀ + 2) * 𝔞 (qf (two * succ N₀) L)) * f

/-! ## Odd and even denominators -/

theorem oe_step {N L : PTm n}
    (ih : Γ ⊢[PRAAx] le (two * N) L ⟶ two * two * O N L + S N L ≐ two * two * S (two * N) L)
    (h : Γ ⊢[PRAAx] le (two * succ N) L) :
    Γ ⊢[PRAAx] two * two * O (succ N) L + S (succ N) L ≐ two * two * S (two * succ N) L := by
  have h₀ : Γ ⊢[PRAAx] le (two * N) L := le_trans (le_of_eq_add (d := two) (by ipra_ring)) h
  have e : Γ ⊢[PRAAx] two * succ N ≐ succ (succ (two * N)) := by ipra_ring
  ipra_lc 4 * natEq (O_succ (Γ := Γ) N L) + natEq (S_succ (Γ := Γ) N L) -
    4 * natEq (congrAp2 (sumF sB) e (.eqRefl L)) - 4 * natEq (S_succ (Γ := Γ) (succ (two * N)) L) -
    4 * natEq (S_succ (Γ := Γ) (two * N) L) + natEq (Prf.impE ih h₀) +
    (𝔞 (qf (succ N) L) + 2 * 𝔞 (qf (two * succ N) L)) * natEq (q_double h) +
    4 * (𝔞 (qf (two * succ N) L) + 𝔞 (qf (succ (succ (two * N))) L)) * natEq (congrAp2 quoF (.eqRefl (fact L)) e)

theorem oe_zero (L : PTm n) : Γ ⊢[PRAAx] two * two * O zero L + S zero L ≐ two * two * S (two * zero) L := by
  ipra_lc 4 * natEq (sum_zero (Γ := Γ) oB L) + natEq (sum_zero (Γ := Γ) sB L) -
    4 * natEq (congrAp2 (sumF sB) (by ipra_ring : Γ ⊢[PRAAx] two * zero ≐ (zero : PTm n)) (.eqRefl L)) -
    4 * natEq (sum_zero (Γ := Γ) sB L)

/-- Variables: `0 = N`, `1 = L`. -/
private abbrev oeF : Fm PTm 2 :=
  le (two * var 0) (var 1) ⟶ two * two * O (var 0) (var 1) + S (var 0) (var 1) ≐ two * two * S (two * var 0) (var 1)

private theorem oe₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] oeF := by
  ipra_ind (⟨le_QF _ _, trivial⟩) [subst_le, subst_ap2]
  · exact .impI (oe_zero _)
  · exact .impI (oe_step Prf.hyp1 Prf.hyp0)

/-- `eq:oddeven`, cleared by `F = L!`: `4 O(N) + S(N) = 4 S(2N)` for `2N ≤ L`, i.e.
`O_N = S_{2N} − S_N/4`. -/
theorem odd_even {N L : PTm n} (h : Γ ⊢[PRAAx] le (two * N) L) :
    Γ ⊢[PRAAx] two * two * O N L + S N L ≐ two * two * S (two * N) L := by
  have i := inst (Γ := Γ) oe₀ (![N, L] : Fin 2 → PTm n)
  simp at i
  exact Prf.impE i h

/-! ## The uniform comparison -/

/-- `lem:compare` (`eq:compare`), cleared by `F = L!`: for `1 ≤ N ≤ m` (`N = N₀ + 1`), `2N ≤ L`, `m ≤ L`,
`4N O(N) ≤ 3N S(m) + 2F²` and `3N S(m) ≤ 4N O(N) + 2F²`, i.e. `|O_N − (3/4) S_m| ≤ 1/(2N)`. -/
theorem compare {N₀ m L : PTm n} (hm : Γ ⊢[PRAAx] le (succ N₀) m) (h2 : Γ ⊢[PRAAx] le (two * succ N₀) L)
    (hL : Γ ⊢[PRAAx] le m L) :
    Γ ⊢[PRAAx] le (succ N₀ * (two * two * O (succ N₀) L)) (succ N₀ * (num 3 * S m L) + two * (fact L * fact L)) ⋏
      le (succ N₀ * (num 3 * S m L)) (succ N₀ * (two * two * O (succ N₀) L) + two * (fact L * fact L)) := by
  have h1 : Γ ⊢[PRAAx] le (succ N₀) L :=
    le_trans (le_of_eq_add (d := succ N₀) (by ipra_ring)) h2
  have up := natEq (eq_add_of_le (annulus_up h2)); have low := natEq (eq_add_of_le (annulus_low h2))
  have t := tail hm hL
  have mono := natEq (eq_add_of_le (Prf.andE₁ t)); have tl := natEq (eq_add_of_le (Prf.andE₂ t))
  refine .andI (le_of_eq_add (d := num 3 * succ N₀ * monus (S m L) (S (succ N₀) L) +
    two * monus (two * succ N₀ * S (succ N₀) L + fact L * fact L) (two * succ N₀ * S (two * succ N₀) L)) ?_)
    (le_of_eq_add (d := monus (two * two * succ N₀ * S (two * succ N₀) L)
      (two * two * succ N₀ * S (succ N₀) L + fact L * fact L) + num 3 * succ N₀ * (fact L * qf m L) +
      num 3 * succ N₀ * monus (S (succ N₀) L + fact L * qf (succ N₀) L) (S m L + fact L * qf m L)) ?_)
  · ipra_lc 3 * (𝔞 N₀ + 1) * mono - (𝔞 N₀ + 1) * natEq (odd_even h2) + 2 * up
  · ipra_lc (𝔞 N₀ + 1) * natEq (odd_even h2) + low + 3 * (𝔞 N₀ + 1) * tl + 3 * 𝔞 (fact L) * natEq (fact_eq h1)

end LeanProofs.IPRA.Analysis.BaselSquares
