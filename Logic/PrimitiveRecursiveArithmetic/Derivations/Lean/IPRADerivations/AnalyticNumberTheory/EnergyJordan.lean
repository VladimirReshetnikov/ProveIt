import IPRADerivations.Core.BlockSum
import IPRADerivations.Probability.Independence
import IPRADerivations.AnalyticNumberTheory.SquareReciprocal
import IPRADerivations.AnalyticNumberTheory.SumPhi

/-!
# The Jordan count `J₂(d) ≥ d²/4` (`thm:energy`, recovery direction)

Packet: `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`, `energy.tex`, proof of `thm:energy`:
"A bad residue pair modulo `d` has both coordinates divisible by some divisor `t ≥ 2` of `d`. The union bound gives
at most `d² Σ_{t=2}^d 1/t²` bad pairs. … Hence `J_2(d) ≥ d²/4`, also for `d = 1`" (the packet's metatheory:
`EnergyInequality.jordan_quarter`).

`J₂(d) = Σ_{u<d} Σ_{v<d} [gcd(gcd(d, u), v) = 1]` (`J2`). For `d ≥ 1`:

* `one_le_good`: pointwise, `1 ≤ [gcd(d,u,v) = 1] + Σ_{j<d} [t∣d][t∣u][t∣v]` with `t = j + 2`, witnessed at
  `j = gcd(d,u,v) − 2` when the gcd is not `1` (the gcd of positive first arguments needs no case split on `u, v`);
* `jordan_union`: flattening the pair sum (`BlockSum.flatten`) and summing, `d² ≤ J₂(d) + U(d)`;
* `union_eq`: exchanging the sums (`fubini`), the column of `t` is
  `[t ∣ d] (Σ_{u<d} [t∣u])² = [t ∣ d] ⌈d/t⌉²` (`sum_mul_sum`, `Totient.count_multiples`);
* `vb_le`: `[t ∣ d] ⌈d/t⌉² ≤ ⌊d²/t²⌋` (equality when `t ∣ d`);
* `jordan_quarter`: with `T(d+1, d²) = d² + Σ_{j<d} ⌊d²/(j+2)²⌋` and the telescoping bound
  `4(d+1) T(d+1, d²) + 4d² ≤ 7(d+1) d²` (`SquareReciprocal.square_bound`),
  `(d+1) d² ≤ (d+1) · 4 J₂(d)`, hence `d² ≤ 4 J₂(d)`. No separate case `d = 1` is needed.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.EnergyJordan

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.BlockSum (flatB flat_at flatten)
open LeanProofs.IPRA.Probability.Independence (dsum sum_scale sum_mul_sum pmB inst3_pmB row_pt col_pt)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (mulBody count_multiples quo_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.SquareReciprocal (sqB inst2_sq square_bound sqInv cancel_le)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (sum_ones)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gcd_dvd' dvd_trans' dvd_le' eq_of_dvd')
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The count -/

/-- `[gcd(gcd(d, u), v) = 1]`, over `0 = u`, `1 = v`, `2 = d`. -/
abbrev goodB : PTm 3 := eqb (gcd (gcd (var 2) (var 0)) (var 1)) one

/-- `J₂(d) = #{0 ≤ u, v < d : gcd(u, v, d) = 1}`. -/
abbrev J2 (d : PTm n) : PTm n := dsum goodB d d d

theorem inst3_good (u v d : PTm n) : inst3 goodB u v d = eqb (gcd (gcd d u) v) one := by
  simp only [inst3, subst_eqb, subst_ex2, Syn.subst_var, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero]; rfl

/-! ## The pointwise union bound -/

theorem pos_succ (e : PTm n) : Γ ⊢[PRAAx] succ e ≐ succ (pred (succ e)) := congrSucc (pred_succ _).eqSymm

/-- `1 ≤ [gcd(d,u,v) = 1] + Σ_{j<d} f(j)` whenever `f(j) = 1` for every `j < d` with `j + 2 ∣ d, u, v`. -/
theorem one_le_good {d u v z : PTm n} (f : PTm 2) (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (hf : ∀ (Θ : List (Fm PTm n)) (j : PTm n), (Θ ⊢[PRAAx] lt j d) → (Θ ⊢[PRAAx] dvd (succ (succ j)) d) →
      (Θ ⊢[PRAAx] dvd (succ (succ j)) u) → (Θ ⊢[PRAAx] dvd (succ (succ j)) v) → (Θ ⊢[PRAAx] inst2 f j z ≐ one)) :
    Γ ⊢[PRAAx] le one (eqb (gcd (gcd d u) v) one + ap2 (sumF f) d z) := by
  refine .orE (eq_or_ne (gcd (gcd d u) v) one) ?_ ?_
  · exact le_of_eq_add (d := ap2 (sumF f) d z) (congrAdd (eqb_of_eq Prf.hyp0) (.eqRefl _))
  · let Θ : List (Fm PTm n) := neg (gcd (gcd d u) v ≐ one) :: Γ
    have hd' : Θ ⊢[PRAAx] d ≐ succ (pred d) := hd.wk
    have h1 : Θ ⊢[PRAAx] gcd d u ≐ succ (pred (gcd d u)) := gcd_pos hd'
    have hg : Θ ⊢[PRAAx] gcd (gcd d u) v ≐ succ (pred (gcd (gcd d u) v)) := gcd_pos h1
    have a := gcd_dvd' (b := v) h1
    have b := gcd_dvd' (b := u) hd'
    have gd := dvd_trans' hg h1 (Prf.andE₁ a) (Prf.andE₁ b)
    have gu := dvd_trans' hg h1 (Prf.andE₁ a) (Prf.andE₂ b)
    have gv := Prf.andE₂ a
    -- the gcd is at least `2`
    have hp : Θ ⊢[PRAAx] pred (gcd (gcd d u) v) ≐ succ (pred (pred (gcd (gcd d u) v))) := by
      refine .orE (zero_or_succ (pred (gcd (gcd d u) v))) ?_ Prf.hyp0
      exact .botE _ (.impE Prf.hyp1 (hg.wk.eqTrans (congrSucc Prf.hyp0)))
    have hg2 := hg.eqTrans (congrSucc hp)
    have hle := le_congr hg2 (.eqRefl _) (dvd_le' hg gd hd')
    have hj : Θ ⊢[PRAAx] lt (pred (pred (gcd (gcd d u) v))) d := le_trans (le_succ_self _) hle
    have t1 := hf _ _ hj (dvd_congr_left hg2 gd) (dvd_congr_left hg2 gu) (dvd_congr_left hg2 gv)
    have s := le_congr t1 (.eqRefl _) (term_le_sum f (x := z) hj)
    exact le_trans s (le_of_eq_add (d := eqb (gcd (gcd d u) v) one) (by apply deriveNat; ipra_simps; ring))

/-! ## Summing the union bound -/

/-- `[t ∣ d][t ∣ ⌊k/d⌋][t ∣ k mod d]` with `t = j + 2`, over `0 = k`, `1 = j`, `2 = d`. -/
abbrev unB : PTm 3 := eqb (rem (var 2) (succ (succ (var 1)))) zero *
  (eqb (rem (quo (var 0) (var 2)) (succ (succ (var 1)))) zero *
    eqb (rem (rem (var 0) (var 2)) (succ (succ (var 1)))) zero)

theorem inst3_un (k j d : PTm n) : inst3 unB k j d = eqb (rem d (succ (succ j))) zero *
    (eqb (rem (quo k d) (succ (succ j))) zero * eqb (rem (rem k d) (succ (succ j))) zero) := by
  simp [inst3]

/-- The pointwise bound at the flattened index `k`, `d = e + 1`. -/
theorem pt_good (e k : PTm n) :
    Γ ⊢[PRAAx] le one (inst2 (flatB goodB) k (pairT (succ e) (succ e)) + inst2 (oB unB) k (pairT (succ e) (succ e))) := by
  have base := one_le_good (Γ := Γ) (u := quo k (succ e)) (v := rem k (succ e)) (z := pairT k (succ e)) (rowB unB)
    (pos_succ e) (fun Θ j _ h1 h2 h3 => by
      refine (row_pt unB k j (succ e)).eqTrans ?_
      rw [inst3_un]
      exact (congrMul (eqb_of_eq h1) (congrMul (eqb_of_eq h2) (eqb_of_eq h3))).eqTrans
        (by apply deriveNat; ipra_simps; ring))
  have fl := flat_at (Γ := Γ) goodB k (succ e) (succ e)
  rw [inst3_good] at fl
  exact le_congr (.eqRefl _) (congrAdd fl.eqSymm (oB_at unB k (succ e) (succ e)).eqSymm) base

/-- The union sum `U(d) = Σ_{k<d²} Σ_{j<d} [t∣d][t∣⌊k/d⌋][t∣k mod d]`. -/
abbrev U (d : PTm n) : PTm n := ap2 (sumF (oB unB)) (d * d) (pairT d d)

theorem one_inst2 (i z : PTm n) : inst2 (one : PTm 2) i z = one := by simp [inst2]

/-- `d² ≤ J₂(d) + U(d)` for `d = e + 1`. -/
theorem jordan_union (e : PTm n) : Γ ⊢[PRAAx] le (succ e * succ e) (J2 (succ e) + U (succ e)) := by
  have s := sum_le_params (Γ := Γ) (one : PTm 2) (addBody (flatB goodB) (oB unB)) (pairT (succ e) (succ e))
    (pairT (succ e) (succ e)) (succ e * succ e) (.allI (.impI ?_))
  · exact le_congr (sum_ones _ _) ((sum_add _ _ _ _).eqTrans
      (congrAdd (flatten goodB (pos_succ e)) (.eqRefl _))) s
  · rw [one_inst2, inst2_addBody, shift_pairT, shift_succ'']
    exact pt_good _ _

/-! ## The columns of the union sum -/

/-- `[t ∣ d] ⌈d/t⌉²` with `t = j + 2`, over `0 = j`, `1 = d`. -/
abbrev vB : PTm 2 := eqb (rem (var 1) (succ (succ (var 0)))) zero *
  (quo (var 1 + succ (var 0)) (succ (succ (var 0))) * quo (var 1 + succ (var 0)) (succ (succ (var 0))))

theorem inst2_v (j d : PTm n) : inst2 vB j d = eqb (rem d (succ (succ j))) zero *
    (quo (d + succ j) (succ (succ j)) * quo (d + succ j) (succ (succ j))) := by simp [inst2]

/-- `[t ∣ u][t ∣ v]`, over `0 = u`, `1 = v`, `2 = t`. -/
abbrev PP : PTm 3 := pmB mulBody mulBody

theorem flat_PP (k d t : PTm n) :
    Γ ⊢[PRAAx] inst2 (flatB PP) k (pairT d t) ≐ eqb (rem (quo k d) t) zero * eqb (rem (rem k d) t) zero := by
  refine (flat_at PP k d t).eqTrans ?_
  rw [inst3_pmB, Totient.inst2_mul, Totient.inst2_mul]
  exact .eqRefl _

theorem col_point (k j d : PTm n) :
    Γ ⊢[PRAAx] inst2 (colB unB) k (pairT j d) ≐
      eqb (rem d (succ (succ j))) zero * inst2 (flatB PP) k (pairT d (succ (succ j))) := by
  refine (col_pt unB k j d).eqTrans ?_
  rw [inst3_un]
  exact congrMul (.eqRefl _) (flat_PP k d _).eqSymm

theorem shift_K (d j : PTm n) : Syn.shift (eqb (rem d (succ (succ j))) zero) =
    eqb (rem (Syn.shift d) (succ (succ (Syn.shift j)))) zero := by simp [Syn.shift]

/-- The column of `j`: `Σ_{k<d²} [t∣d][t∣⌊k/d⌋][t∣k mod d] = [t ∣ d] ⌈d/t⌉²`, `d = e + 1`. -/
theorem col_eq (e j : PTm n) :
    Γ ⊢[PRAAx] inst2 (pB unB) j (pairT (succ e * succ e) (succ e)) ≐ inst2 vB j (succ e) := by
  rw [inst2_pB]
  refine (congrAp2 (sumF (colB unB)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  have sc := sum_scale (Γ := Γ) (colB unB) (flatB PP) (succ e * succ e) (eqb (rem (succ e) (succ (succ j))) zero)
    (pairT (succ e) (succ (succ j))) (pairT j (succ e)) (.allI (.impI ?_))
  · have fl := flatten (Γ := Γ) PP (m := succ e) (x := succ (succ j)) (pos_succ e)
    have mm := sum_mul_sum (Γ := Γ) mulBody mulBody (succ e) (succ e) (succ (succ j))
    have cm : Γ ⊢[PRAAx] ap2 (sumF mulBody) (succ e) (succ (succ j)) ≐ quo (succ e + succ j) (succ (succ j)) :=
      (count_multiples (pos_succ _)).eqTrans (congrAp2 quoF (congrAdd (.eqRefl _) (pred_succ _)) (.eqRefl _))
    rw [inst2_v]
    exact sc.eqTrans (congrMul (.eqRefl _) (fl.eqTrans (mm.eqTrans (congrMul cm cm))))
  · rw [shift_pairT, shift_pairT, shift_K, shift_succ'', shift_succ'']
    exact col_point _ _ _

/-- `U(d) = Σ_{j<d} [t ∣ d] ⌈d/t⌉²`. -/
theorem union_eq (e : PTm n) : Γ ⊢[PRAAx] U (succ e) ≐ ap2 (sumF vB) (succ e) (succ e) := by
  refine (fubini unB (succ e * succ e) (succ e) (succ e)).eqTrans
    (sum_congr_bounded (pB unB) vB _ _ _ (.allI (.impI ?_)))
  rw [shift_pairT, shift_succ'']
  have h := col_eq (Γ := lt (var 0) (Syn.shift (succ e)) :: Γ.map Fm.shift) (Syn.shift e) (var 0)
  have hm : Syn.shift (succ e * succ e) = succ (Syn.shift e) * succ (Syn.shift e) := by simp [Syn.shift]
  rw [hm]
  exact h

/-! ## Each column is at most `⌊d²/t²⌋` -/

theorem vb_le (j d : PTm n) : Γ ⊢[PRAAx] le (inst2 vB j d) (inst2 (shiftBody sqB) j (d * d)) := by
  rw [inst2_v, inst2_shiftBody, inst2_sq]
  have ht : Γ ⊢[PRAAx] succ (succ j) ≐ succ (pred (succ (succ j))) := pos_succ _
  refine .orE (eq_or_ne (rem d (succ (succ j))) zero) ?_ ?_
  · let Θ : List (Fm PTm n) := (rem d (succ (succ j)) ≐ zero) :: Γ
    have ed := eq_of_dvd' (Γ := Θ) ht.wk Prf.hyp0
    have c : Θ ⊢[PRAAx] quo (d + succ j) (succ (succ j)) ≐ quo d (succ (succ j)) :=
      quo_eq ht.wk (congrAdd ed (.eqRefl _)) (le_refl _)
    have htt : Θ ⊢[PRAAx] succ (succ j) * succ (succ j) ≐ succ (pred (succ (succ j) * succ (succ j))) :=
      pos_mul ht.wk ht.wk
    have q : Θ ⊢[PRAAx] quo (d * d) (succ (succ j) * succ (succ j)) ≐ quo d (succ (succ j)) * quo d (succ (succ j)) := by
      refine quo_eq htt (z := d * d) (q := quo d (succ (succ j)) * quo d (succ (succ j))) (r := zero) ?_ ?_
      · have e1 := natEq ed
        apply deriveNat; ipra_simps; rw [e1]; ring
      · exact le_of_eq_add (d := succ j * succ (succ j) + succ j) (by apply deriveNat; ipra_simps; ring)
    have v1 : Θ ⊢[PRAAx] eqb (rem d (succ (succ j))) zero *
        (quo (d + succ j) (succ (succ j)) * quo (d + succ j) (succ (succ j))) ≐
        quo d (succ (succ j)) * quo d (succ (succ j)) :=
      (congrMul (eqb_of_eq Prf.hyp0) (congrMul c c)).eqTrans (one_mul _)
    exact le_congr v1.eqSymm q.eqSymm (le_refl _)
  · exact le_congr ((congrMul (eqb_of_ne Prf.hyp0) (.eqRefl _)).eqTrans (zero_mul _)).eqSymm (.eqRefl _) (zero_le _)

/-! ## The arithmetic -/

/-- `F ≤ J + U`, `U ≤ B`, `T = F + B` and `4NT + 4F ≤ 7NF` give `N F ≤ N · 4J`. -/
theorem jordan_alg {N F J U' B T : PTm n} (h1 : Γ ⊢[PRAAx] le F (J + U')) (h2 : Γ ⊢[PRAAx] le U' B)
    (h3 : Γ ⊢[PRAAx] T ≐ F + B) (h5 : Γ ⊢[PRAAx] le (num 4 * N * T + num 4 * F) (num 7 * N * F)) :
    Γ ⊢[PRAAx] le (N * F) (N * (num 4 * J)) := by
  have e1 := natEq (eq_add_of_le h1)
  have e2 := natEq (eq_add_of_le h2)
  have e3 := natEq h3
  have e5 := natEq (eq_add_of_le h5)
  refine le_of_eq_add (d := num 4 * F + monus (num 7 * N * F) (num 4 * N * T + num 4 * F) +
    num 4 * N * (monus (J + U') F + monus B U')) ?_
  apply deriveNat; ipra_simps
  linear_combination 4 * 𝔞 N * e1 + 4 * 𝔞 N * e2 + 4 * 𝔞 N * e3 + e5

/-- `d² ≤ 4 J₂(d)` for `d = e + 1`. -/
theorem jordan_quarter (e : PTm n) : Γ ⊢[PRAAx] le (succ e * succ e) (num 4 * J2 (succ e)) := by
  have h1 := le_congr (.eqRefl _) (congrAdd (.eqRefl _) (union_eq e)) (jordan_union (Γ := Γ) e)
  have h2 : Γ ⊢[PRAAx] le (ap2 (sumF vB) (succ e) (succ e)) (ap2 (sumF (shiftBody sqB)) (succ e) (succ e * succ e)) := by
    refine sum_le_params vB (shiftBody sqB) _ _ _ (.allI (.impI ?_))
    have hm : Syn.shift (succ e * succ e) = Syn.shift (succ e) * Syn.shift (succ e) := by simp [Syn.shift]
    rw [hm]
    exact vb_le _ _
  have q1 : Γ ⊢[PRAAx] inst2 sqB zero (succ e * succ e) ≐ succ e * succ e := by
    rw [inst2_sq]
    exact (congrAp2 quoF (.eqRefl _) (one_mul _)).eqTrans
      (quo_eq (congrSucc (pred_succ _).eqSymm) (by ipra_ring) ((succ_monus_succ _ _).eqTrans (zero_monus _)))
  have h3 := (sum_shift sqB (succ e) (succ e * succ e)).eqTrans (congrAdd q1 (.eqRefl _))
  have h5 := square_bound (Γ := Γ) e (succ e * succ e)
  unfold sqInv at h5
  exact cancel_le (pos_succ _) (jordan_alg h1 h2 h3 h5)

/-- Variable `0 = e`, `d = e + 1`: `d² ≤ 4 J₂(d)`. -/
abbrev jordanFormula : Fm PTm 1 := le (succ (var 0) * succ (var 0)) (num 4 * J2 (succ (var 0)))

/-- `J₂(d) ≥ d²/4` for every `d ≥ 1`, as a closed sentence of iPRA. -/
theorem jordan_quarter_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 jordanFormula :=
  closeUniv 1 (jordan_quarter _)

end LeanProofs.IPRA.AnalyticNumberTheory.EnergyJordan
