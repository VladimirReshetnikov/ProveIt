import IPRADerivations.DiophantineNumberTheory.QuadraticReciprocityGoal
import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.AnalyticNumberTheory.DivisorHyperbola
import IPRADerivations.AnalyticNumberTheory.Multiplicative
import IPRADerivations.AnalyticNumberTheory.Mobius
import IPRADerivations.Probability.Independence
import IPRADerivations.Core.OrderCertificates

/-!
# The lattice count of quadratic reciprocity

Packet: `diophantine-number-theory/quadratic_reciprocity_ipra`: the exact count behind Eisenstein's proof,

  `Σ_{i < P} ⌊(i + 1) q / p⌋ + Σ_{j < Q} ⌊(j + 1) p / q⌋ = P Q`   for `p = 2P + 1`, `q = 2Q + 1`, `gcd(p, q) = 1`.

It is the premise `rectangle p q` of `QuadraticReciprocityGoal.close_from_counts`: for odd `p`, `q` with
`gcd(p, q) = 1`,

  `floorSum p q + floorSum q p = ⌊p/2⌋ ⌊q/2⌋`                                                   (`rectangle_of_odd`).

Proof. Count the points `(i + 1, j + 1)` of the rectangle `i < P`, `j < Q` below and above the diagonal
`p (j + 1) = (i + 1) q`. With `a₁(i, j) = [p (j + 1) ≤ (i + 1) q]` and `a₂ = 1 − a₁`:

* the row `i < P` of `a₁` has `⌊(i + 1) q / p⌋` points, since that quotient is at most `Q` (`row_a1`,
  `DivisorHyperbola.row_count`);
* the column `j < Q` of `a₂` has `⌊(j + 1) p / q⌋` points: no point of the rectangle lies on the diagonal, because
  `p ∣ (i + 1) q` and `gcd(p, q) = 1` give `p ∣ i + 1` (Gauss's lemma), while `i + 1 ≤ P < p`; so `a₂(i, j)` is
  `[q (i + 1) ≤ (j + 1) p]` there (`flip_pt`, `col_a2`);
* `a₁ + a₂ = 1`, and the two double sums are exchanged by `Core/Fubini.fubini`.

Eisenstein's lemma itself (`eisenstein p a`), the other premise of `close_from_counts`, is not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.RectangleCount

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHyperbola (leI leI_one leI_zero IB IB_at row_count)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (sum2_lift)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (lift3 at_pair shift_cop)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum_ones)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (one_inst)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gauss dvd_of_eq' dvd_le' gcd_comm_one)
open LeanProofs.IPRA.DiophantineNumberTheory.QuadraticReciprocityGoal (floorSum rectangle)
open LeanProofs.IPRA.Probability.Independence (dsum dsum_rows dsum_congr dsum_add pmB inst3_pmB sum_mul_sum
  inst3_add' row_pt col_pt)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The quotient bound and the diagonal -/

/-- `p K + r = I q` with `I ≤ P`, `p = 2P + 1`, `q = 2Q + 1` is impossible for `K ≥ Q + 1`. -/
theorem no_big {F K r p q P Q I : PTm n} (φ : Fm PTm n) (e1 : Γ ⊢[PRAAx] F ≐ p * K + r)
    (e2 : Γ ⊢[PRAAx] p ≐ two * P + one) (e3 : Γ ⊢[PRAAx] q ≐ two * Q + one) (e4 : Γ ⊢[PRAAx] F ≐ I * q)
    (hi : Γ ⊢[PRAAx] le I P) (h : Γ ⊢[PRAAx] le (succ Q) K) : Γ ⊢[PRAAx] φ := by
  have x1 := natEq e1; have x2 := natEq e2; have x3 := natEq e3; have x4 := natEq e4
  refine not_succ_le_self F φ ?_
  ipra_le 𝔞 P + 𝔞 Q + 𝔞 p * sl h + 𝔞 r + sl hi * 𝔞 q with x1 - x4 + (𝔞 Q + 1) * x2 - 𝔞 P * x3

/-- `⌊I q / p⌋ ≤ Q` for `I ≤ P`, `p = 2P + 1`, `q = 2Q + 1`. -/
theorem quo_bound {p q P Q I : PTm n} (e2 : Γ ⊢[PRAAx] p ≐ two * P + one) (e3 : Γ ⊢[PRAAx] q ≐ two * Q + one)
    (hi : Γ ⊢[PRAAx] le I P) : Γ ⊢[PRAAx] le (quo (I * q) (succ (pred p))) Q := by
  have hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p) :=
    pos_of_eq_succ (c := two * P) (e2.eqTrans (by apply deriveNat; ipra_simps; ring))
  have dm := div_mod_at (Γ := Γ) (x := I * q) (y := succ (pred p)) (c := pred p) (.eqRefl _)
  have e1 : Γ ⊢[PRAAx] I * q ≐ p * quo (I * q) (succ (pred p)) + rem (I * q) (succ (pred p)) :=
    (Prf.andE₁ dm).eqTrans (congrAdd (congrMul hp1.eqSymm (.eqRefl _)) (.eqRefl _))
  refine .orE (lt_or_le Q (quo (I * q) (succ (pred p)))) ?_ Prf.hyp0
  exact no_big _ e1.wk e2.wk e3.wk (.eqRefl _) hi.wk Prf.hyp0

/-- `p ≤ P` is impossible for `p = 2P + 1`. -/
theorem no_small {p P : PTm n} (φ : Fm PTm n) (e2 : Γ ⊢[PRAAx] p ≐ two * P + one) (h : Γ ⊢[PRAAx] le p P) :
    Γ ⊢[PRAAx] φ := by
  have x2 := natEq e2
  refine not_succ_le_self P φ ?_
  ipra_le sl h + 𝔞 P with x2

/-- No point of the rectangle lies on the diagonal: `p (j + 1) = (i + 1) q` is impossible for `i < P`,
`p = 2P + 1` and `gcd(p, q) = 1`. -/
theorem off_diag {p q P i j : PTm n} (φ : Fm PTm n) (e2 : Γ ⊢[PRAAx] p ≐ two * P + one)
    (hc : Γ ⊢[PRAAx] gcd p q ≐ one) (hi : Γ ⊢[PRAAx] lt i P)
    (h : Γ ⊢[PRAAx] p * succ j ≐ succ i * q) : Γ ⊢[PRAAx] φ := by
  have hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p) :=
    pos_of_eq_succ (c := two * P) (e2.eqTrans (by apply deriveNat; ipra_simps; ring))
  have d1 : Γ ⊢[PRAAx] dvd p (q * succ i) := dvd_of_eq' hp1 ((mul_comm _ _).eqTrans h.eqSymm)
  have d2 : Γ ⊢[PRAAx] dvd p (succ i) := gauss hp1 hc d1
  have l : Γ ⊢[PRAAx] le p (succ i) := dvd_le' hp1 d2 (congrSucc (pred_succ _).eqSymm)
  exact no_small φ e2 (le_trans l hi)

/-! ## The two indicators -/

/-- `[p (j + 1) ≤ (i + 1) q]` over `0 = i`, `1 = j`, `2 = ⟨p, q⟩`. -/
abbrev a1 : PTm 3 := monus one (monus (fstT (var 2) * succ (var 1)) (succ (var 0) * sndT (var 2)))
/-- `[p (j + 1) > (i + 1) q]`. -/
abbrev a2 : PTm 3 := monus one a1

theorem inst3_a1 (i j x : PTm n) : inst3 a1 i j x = leI (fstT x * succ j) (succ i * sndT x) := by
  simp [inst3]

theorem inst3_a2 (i j x : PTm n) : inst3 a2 i j x = monus one (leI (fstT x * succ j) (succ i * sndT x)) := by
  simp [inst3]

theorem a1_at (i j p q : PTm n) :
    Γ ⊢[PRAAx] inst3 a1 i j (pairT p q) ≐ leI (p * succ j) (succ i * q) := by
  rw [inst3_a1]
  exact congrMonus (.eqRefl _) (congrMonus (congrMul (fst_pair _ _) (.eqRefl _))
    (congrMul (.eqRefl _) (snd_pair _ _)))

theorem a2_at (i j p q : PTm n) :
    Γ ⊢[PRAAx] inst3 a2 i j (pairT p q) ≐ monus one (leI (p * succ j) (succ i * q)) := by
  rw [inst3_a2]
  exact congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (congrMonus (congrMul (fst_pair _ _) (.eqRefl _))
    (congrMul (.eqRefl _) (snd_pair _ _))))

/-- `[x ≤ F] + (1 − [x ≤ F]) = 1`. -/
theorem leI_split (x F : PTm n) : Γ ⊢[PRAAx] leI x F + monus one (leI x F) ≐ one := by
  refine .orE (zero_or_succ (monus x F)) ?_ ?_
  · have l : ((monus x F ≐ zero) :: Γ) ⊢[PRAAx] leI x F ≐ one :=
      (congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _)
    exact (congrAdd l ((congrMonus (.eqRefl _) l).eqTrans (monus_self _))).eqTrans (add_zero _)
  · have l : ((monus x F ≐ succ (pred (monus x F))) :: Γ) ⊢[PRAAx] leI x F ≐ zero :=
      (congrMonus (.eqRefl _) Prf.hyp0).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _))
    exact (congrAdd l ((congrMonus (.eqRefl _) l).eqTrans (monus_zero _))).eqTrans (zero_add _)

/-- Off the diagonal, `[p (j + 1) > (i + 1) q] = [q (i + 1) ≤ (j + 1) p]`. -/
theorem flip_pt {p q P i j : PTm n} (e2 : Γ ⊢[PRAAx] p ≐ two * P + one) (hc : Γ ⊢[PRAAx] gcd p q ≐ one)
    (hi : Γ ⊢[PRAAx] lt i P) :
    Γ ⊢[PRAAx] monus one (leI (p * succ j) (succ i * q)) ≐ leI (q * succ i) (succ j * p) := by
  refine .orE (lt_or_le (succ i * q) (p * succ j)) ?_ ?_
  · let C : List (Fm PTm n) := lt (succ i * q) (p * succ j) :: Γ
    have h : C ⊢[PRAAx] lt (succ i * q) (p * succ j) := Prf.hyp0
    have l1 : C ⊢[PRAAx] leI (p * succ j) (succ i * q) ≐ zero := leI_zero h
    have l2 : C ⊢[PRAAx] leI (q * succ i) (succ j * p) ≐ one :=
      leI_one (le_congr (mul_comm _ _) (mul_comm _ _) (le_of_lt h))
    exact ((congrMonus (.eqRefl _) l1).eqTrans (monus_zero _)).eqTrans l2.eqSymm
  · let C : List (Fm PTm n) := le (p * succ j) (succ i * q) :: Γ
    have h : C ⊢[PRAAx] le (p * succ j) (succ i * q) := Prf.hyp0
    have l1 : C ⊢[PRAAx] leI (p * succ j) (succ i * q) ≐ one := leI_one h
    have hlt : C ⊢[PRAAx] lt (p * succ j) (succ i * q) := by
      refine .orE (lt_or_eq_of_le h) Prf.hyp0 ?_
      exact off_diag _ e2.wk.wk hc.wk.wk hi.wk.wk Prf.hyp0
    have l2 : C ⊢[PRAAx] leI (q * succ i) (succ j * p) ≐ zero :=
      leI_zero (lt_congr (mul_comm _ _) (mul_comm _ _) hlt)
    exact ((congrMonus (.eqRefl _) l1).eqTrans (monus_self _)).eqTrans l2.eqSymm

/-! ## Rows and columns -/

/-- The row `i < P` of `a₁` has `⌊(i + 1) q / p⌋` points. -/
theorem row_a1 {p q P Q i : PTm n} (e2 : Γ ⊢[PRAAx] p ≐ two * P + one) (e3 : Γ ⊢[PRAAx] q ≐ two * Q + one)
    (hi : Γ ⊢[PRAAx] lt i P) :
    Γ ⊢[PRAAx] ap2 (sumF (rowB a1)) Q (pairT i (pairT p q)) ≐ quo (succ i * q) p := by
  have hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p) :=
    pos_of_eq_succ (c := two * P) (e2.eqTrans (by apply deriveNat; ipra_simps; ring))
  have hp1' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift p ≐ succ (pred (Syn.shift p)) := by
    simpa [Fm.shift, Syn.shift] using hp1.shift
  refine (sum_congr_bounded (rowB a1) IB (pairT i (pairT p q)) (pairT (pred p) (succ i * q)) Q
    (.allI (.impI ?_))).eqTrans ((row_count (quo_bound e2 e3 hi)).eqTrans
      (congrAp2 quoF (.eqRefl _) hp1.eqSymm))
  have s1 : Syn.shift (pairT i (pairT p q)) = pairT (Syn.shift i) (pairT (Syn.shift p) (Syn.shift q)) := by
    simp [Syn.shift]
  have s2 : Syn.shift (pairT (pred p) (succ i * q)) =
      pairT (pred (Syn.shift p)) (succ (Syn.shift i) * Syn.shift q) := by simp [Syn.shift]
  rw [s1, s2]
  refine (row_pt a1 _ _ _).eqTrans ((a1_at _ _ _ _).eqTrans ?_)
  exact (congrMonus (.eqRefl _) (congrMonus (congrMul hp1'.wk (.eqRefl _)) (.eqRefl _))).eqTrans
    (IB_at _ _ _).eqSymm

/-- The column `j < Q` of `a₂` has `⌊(j + 1) p / q⌋` points. -/
theorem col_a2 {p q P Q j : PTm n} (e2 : Γ ⊢[PRAAx] p ≐ two * P + one) (e3 : Γ ⊢[PRAAx] q ≐ two * Q + one)
    (hc : Γ ⊢[PRAAx] gcd p q ≐ one) (hj : Γ ⊢[PRAAx] lt j Q) :
    Γ ⊢[PRAAx] ap2 (sumF (colB a2)) P (pairT j (pairT p q)) ≐ quo (succ j * p) q := by
  have hq1 : Γ ⊢[PRAAx] q ≐ succ (pred q) :=
    pos_of_eq_succ (c := two * Q) (e3.eqTrans (by apply deriveNat; ipra_simps; ring))
  have hq1' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift q ≐ succ (pred (Syn.shift q)) := by
    simpa [Fm.shift, Syn.shift] using hq1.shift
  have e2' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift p ≐ two * Syn.shift P + one := by
    simpa [Fm.shift, Syn.shift] using e2.shift
  have hc' := shift_cop hc
  refine (sum_congr_bounded (colB a2) IB (pairT j (pairT p q)) (pairT (pred q) (succ j * p)) P
    (.allI (.impI ?_))).eqTrans ((row_count (quo_bound e3 e2 hj)).eqTrans
      (congrAp2 quoF (.eqRefl _) hq1.eqSymm))
  have s1 : Syn.shift (pairT j (pairT p q)) = pairT (Syn.shift j) (pairT (Syn.shift p) (Syn.shift q)) := by
    simp [Syn.shift]
  have s2 : Syn.shift (pairT (pred q) (succ j * p)) =
      pairT (pred (Syn.shift q)) (succ (Syn.shift j) * Syn.shift p) := by simp [Syn.shift]
  rw [s1, s2]
  refine (col_pt a2 _ _ _).eqTrans ((a2_at _ _ _ _).eqTrans ((flip_pt e2'.wk hc'.wk Prf.hyp0).eqTrans ?_))
  exact (congrMonus (.eqRefl _) (congrMonus (congrMul hq1'.wk (.eqRefl _)) (.eqRefl _))).eqTrans
    (IB_at _ _ _).eqSymm

/-! ## The count -/

/-- `⌊(i + 1) a / p⌋` over `0 = i`, `1 = p`, `2 = a`: the body of `floorSum`. -/
abbrev fsB : PTm 3 := quo (succ (var 0) * var 2) (var 1)

theorem inst3_fsB (i p a : PTm n) : inst3 fsB i p a = quo (succ i * a) p := by simp [inst3]

theorem one_alg : Γ ⊢[PRAAx] (one : PTm n) * one ≐ one := by apply deriveNat; ipra_simps; ring

/-- The lattice count: `Σ_{i<P} ⌊(i+1) q/p⌋ + Σ_{j<Q} ⌊(j+1) p/q⌋ = P Q` for `p = 2P + 1`, `q = 2Q + 1`,
`gcd(p, q) = 1`. -/
theorem rectangle_count {p q P Q : PTm n} (e2 : Γ ⊢[PRAAx] p ≐ two * P + one)
    (e3 : Γ ⊢[PRAAx] q ≐ two * Q + one) (hc : Γ ⊢[PRAAx] gcd p q ≐ one) :
    Γ ⊢[PRAAx] ap3 (sum2F fsB) P p q + ap3 (sum2F fsB) Q q p ≐ P * Q := by
  have e2' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift p ≐ two * Syn.shift P + one := by
    simpa [Fm.shift, Syn.shift] using e2.shift
  have e3' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift q ≐ two * Syn.shift Q + one := by
    simpa [Fm.shift, Syn.shift] using e3.shift
  have hc' := shift_cop hc
  -- the first sum is the double sum of `a₁`
  have r1 : Γ ⊢[PRAAx] dsum a1 P Q (pairT p q) ≐ ap2 (sumF (lift3 fsB)) P (pairT p q) := by
    refine dsum_rows a1 (lift3 fsB) P Q (pairT p q) (pairT p q) (.allI (.impI ?_))
    simp only [shift_pairT]
    refine (row_a1 e2'.wk e3'.wk Prf.hyp0).eqTrans ?_
    have h := at_pair (Γ := lt (var 0) (Syn.shift P) :: Γ.map Fm.shift) fsB (var 0) (Syn.shift p) (Syn.shift q)
    rw [inst3_fsB] at h
    exact h.eqSymm
  have f1 := (sum2_lift (Γ := Γ) fsB P p q).eqTrans r1.eqSymm
  -- the second sum is the double sum of `a₂`, by Fubini
  have r2 : Γ ⊢[PRAAx] ap2 (sumF (pB a2)) Q (pairT P (pairT p q)) ≐ ap2 (sumF (lift3 fsB)) Q (pairT q p) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT]
    rw [inst2_pB]
    have c := col_a2 (Γ := lt (var 0) (Syn.shift Q) :: Γ.map Fm.shift) e2'.wk e3'.wk hc'.wk Prf.hyp0
    have h := at_pair (Γ := lt (var 0) (Syn.shift Q) :: Γ.map Fm.shift) fsB (var 0) (Syn.shift q) (Syn.shift p)
    rw [inst3_fsB] at h
    exact (congrAp2 (sumF (colB a2)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans
      (c.eqTrans h.eqSymm)
  have f2 := (sum2_lift (Γ := Γ) fsB Q q p).eqTrans (r2.eqSymm.eqTrans (fubini a2 P Q (pairT p q)).eqSymm)
  -- `a₁ + a₂ = 1`
  have tot : Γ ⊢[PRAAx] dsum (a1 + a2) P Q (pairT p q) ≐ dsum (pmB (one : PTm 2) (one : PTm 2)) P Q (pairT p q) := by
    refine dsum_congr (a1 + a2) (pmB (one : PTm 2) (one : PTm 2)) (fun i j x => ?_) P Q (pairT p q)
    rw [inst3_add', inst3_a1, inst3_a2, inst3_pmB, one_inst, one_inst]
    exact (leI_split _ _).eqTrans one_alg.eqSymm
  have cnt : Γ ⊢[PRAAx] dsum (pmB (one : PTm 2) (one : PTm 2)) P Q (pairT p q) ≐ P * Q :=
    (sum_mul_sum (one : PTm 2) (one : PTm 2) P Q (pairT p q)).eqTrans
      (congrMul (sum_ones P _) (sum_ones Q _))
  exact (congrAdd f1 f2).eqTrans ((dsum_add a1 a2 P Q (pairT p q)).eqSymm.eqTrans (tot.eqTrans cnt))

/-- The premise `rectangle p q` of `QuadraticReciprocityGoal.close_from_counts` for odd `p`, `q` with
`gcd(p, q) = 1`: `floorSum p q + floorSum q p = ⌊p/2⌋ ⌊q/2⌋`. -/
theorem rectangle_of_odd {p q : PTm n} (hp : Γ ⊢[PRAAx] par p ≐ one) (hq : Γ ⊢[PRAAx] par q ≐ one)
    (hc : Γ ⊢[PRAAx] gcd p q ≐ one) : Γ ⊢[PRAAx] rectangle p q :=
  rectangle_count (odd_of hp) (odd_of hq) hc

end LeanProofs.IPRA.DiophantineNumberTheory.RectangleCount
