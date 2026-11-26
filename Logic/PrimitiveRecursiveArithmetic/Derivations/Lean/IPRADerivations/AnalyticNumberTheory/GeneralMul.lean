import IPRADerivations.AnalyticNumberTheory.Radical
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# The general multiplication formula

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:phi-general-mul`:
for `d = gcd(m, n) > 0`, `φ(mn) φ(d) = φ(m) φ(n) d`.

With `e(q, x) = [q prime][q ∣ x]`:

* `e_split`: `e(q, mn) + e(q, d) = e(q, m) + e(q, n)` (`[q ∣ m ∨ q ∣ n] + [q ∣ m ∧ q ∣ n]`), from
  Euclid's lemma and the universal property of the gcd;
* `pp_split`: hence `∏_F(mn) ∏_F(d) = ∏_F(m) ∏_F(n)` for every base `F`, after extending all four
  products to the bound `mn + 1`;
* the formula: multiply the four Euler products (`EulerProduct.euler_product_at`) and cancel
  `rad(m) rad(n) ≥ 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.GeneralMul

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct
open LeanProofs.IPRA.AnalyticNumberTheory.Radical (rad rad_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The exponent identity -/

section Split

variable {m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
include hm hN

abbrev splitF (m N q : PTm n) : Fm PTm n :=
  eqb (rem (m * N) q) zero + eqb (rem (gcd m N) q) zero ≐ eqb (rem m q) zero + eqb (rem N q) zero

theorem split_tt {q : PTm n} (hq1 : Γ ⊢[PRAAx] q ≐ succ (pred q)) (hA : Γ ⊢[PRAAx] dvd q m)
    (hB : Γ ⊢[PRAAx] dvd q N) : Γ ⊢[PRAAx] splitF m N q :=
  (congrAdd (eqb_of_eq (dvd_mul' hq1 N hA)) (eqb_of_eq (gcd_greatest' hq1 hA hB))).eqTrans
    (congrAdd (eqb_of_eq hA) (eqb_of_eq hB)).eqSymm

theorem split_tf {q : PTm n} (hq1 : Γ ⊢[PRAAx] q ≐ succ (pred q)) (hA : Γ ⊢[PRAAx] dvd q m)
    (hB : Γ ⊢[PRAAx] neg (dvd q N)) : Γ ⊢[PRAAx] splitF m N q := by
  have hg := gcd_pos (B := N) hm
  have hgd := gcd_dvd' (b := N) hm
  have d : Γ ⊢[PRAAx] eqb (rem (gcd m N) q) zero ≐ zero :=
    eqb_of_ne (.impI (.impE hB.wk (dvd_trans' hq1.wk hg.wk Prf.hyp0 (Prf.andE₂ hgd).wk)))
  exact (congrAdd (eqb_of_eq (dvd_mul' hq1 N hA)) d).eqTrans (congrAdd (eqb_of_eq hA) (eqb_of_ne hB)).eqSymm

theorem split_ft {q : PTm n} (hq1 : Γ ⊢[PRAAx] q ≐ succ (pred q)) (hA : Γ ⊢[PRAAx] neg (dvd q m))
    (hB : Γ ⊢[PRAAx] dvd q N) : Γ ⊢[PRAAx] splitF m N q := by
  have hg := gcd_pos (B := N) hm
  have hgd := gcd_dvd' (b := N) hm
  have d : Γ ⊢[PRAAx] eqb (rem (gcd m N) q) zero ≐ zero :=
    eqb_of_ne (.impI (.impE hA.wk (dvd_trans' hq1.wk hg.wk Prf.hyp0 (Prf.andE₁ hgd).wk)))
  have c := eqb_of_eq (dvd_congr (mul_comm _ _) (dvd_mul' hq1 m hB))
  exact (congrAdd c d).eqTrans ((add_comm _ _).eqTrans (congrAdd (eqb_of_ne hA) (eqb_of_eq hB)).eqSymm)

theorem split_ff {q : PTm n} (hq : Γ ⊢[PRAAx] prime q) (hA : Γ ⊢[PRAAx] neg (dvd q m))
    (hB : Γ ⊢[PRAAx] neg (dvd q N)) : Γ ⊢[PRAAx] splitF m N q := by
  have hq1 := prime_eq_succ_pred hq
  have hg := gcd_pos (B := N) hm
  have hgd := gcd_dvd' (b := N) hm
  have c : Γ ⊢[PRAAx] eqb (rem (m * N) q) zero ≐ zero := by
    refine eqb_of_ne (.impI (.orE (euclid_lemma_at hq.wk Prf.hyp0) ?_ ?_))
    · exact .impE hA.wk.wk Prf.hyp0
    · exact .impE hB.wk.wk Prf.hyp0
  have d : Γ ⊢[PRAAx] eqb (rem (gcd m N) q) zero ≐ zero :=
    eqb_of_ne (.impI (.impE hA.wk (dvd_trans' hq1.wk hg.wk Prf.hyp0 (Prf.andE₁ hgd).wk)))
  exact (congrAdd c d).eqTrans (congrAdd (eqb_of_ne hA) (eqb_of_ne hB)).eqSymm

/-- `[q ∣ mn] + [q ∣ d] = [q ∣ m] + [q ∣ n]` for a prime `q`. -/
theorem dvd_split {q : PTm n} (hq : Γ ⊢[PRAAx] prime q) : Γ ⊢[PRAAx] splitF m N q := by
  have hq1 := prime_eq_succ_pred hq
  refine .orE (eq_or_ne (rem m q) zero) ?_ ?_
  · refine .orE (eq_or_ne (rem N q) zero) ?_ ?_
    · exact split_tt hm.wk.wk hN.wk.wk hq1.wk.wk Prf.hyp1 Prf.hyp0
    · exact split_tf hm.wk.wk hN.wk.wk hq1.wk.wk Prf.hyp1 Prf.hyp0
  · refine .orE (eq_or_ne (rem N q) zero) ?_ ?_
    · exact split_ft hm.wk.wk hN.wk.wk hq1.wk.wk Prf.hyp1 Prf.hyp0
    · exact split_ff hm.wk.wk hN.wk.wk hq.wk.wk Prf.hyp1 Prf.hyp0

/-- `e(q, mn) + e(q, d) = e(q, m) + e(q, n)`. -/
theorem e_split (q : PTm n) :
    Γ ⊢[PRAAx] inst2 eB q (m * N) + inst2 eB q (gcd m N) ≐ inst2 eB q m + inst2 eB q N := by
  rw [inst2_e, inst2_e, inst2_e, inst2_e]
  refine .orE (isP_01 q) ?_ ?_
  · have z : ∀ x : PTm n, ((isP q ≐ zero) :: Γ) ⊢[PRAAx] isP q * eqb (rem x q) zero ≐ zero :=
      fun x => (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
    exact (congrAdd (z _) (z _)).eqTrans (congrAdd (z _) (z _)).eqSymm
  · have o : ∀ x : PTm n, ((isP q ≐ one) :: Γ) ⊢[PRAAx] isP q * eqb (rem x q) zero ≐ eqb (rem x q) zero :=
      fun x => (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _)
    exact (congrAdd (o _) (o _)).eqTrans ((dvd_split hm.wk hN.wk (prime_of_isP Prf.hyp0)).eqTrans
      (congrAdd (o _) (o _)).eqSymm)

end Split

/-! ## Splitting the prime-indexed products -/

abbrev X3 (F : PTm 2) : PTm 3 := Syn.subst ![var 0, var 1] (pB F)
abbrev Y3 (F : PTm 2) : PTm 3 := Syn.subst ![var 0, var 2] (pB F)

theorem inst3_X3 (F : PTm 2) (j a b : PTm n) : inst3 (X3 F) j a b = inst2 (pB F) j a := by
  simp only [inst3, inst2, X3, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> rfl

theorem inst3_Y3 (F : PTm 2) (j a b : PTm n) : inst3 (Y3 F) j a b = inst2 (pB F) j b := by
  simp only [inst3, inst2, Y3, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> rfl

theorem prod2_X3 (F : PTm 2) (B a b : PTm n) :
    Γ ⊢[PRAAx] ap3 (prod2F (X3 F)) B a b ≐ ap2 (prodF (pB F)) B a := by
  refine (prod2_congr_bounded (X3 F) (Y3 F) a b a a B (.allI (.impI ?_))).eqTrans
    (Permutation.prod2_eq_prod _ _ _ _)
  rw [inst3_X3, inst3_Y3]; exact .eqRefl _

theorem prod_to_pp (F : PTm 2) {x B : PTm n} (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (h : Γ ⊢[PRAAx] le x B) :
    Γ ⊢[PRAAx] ap2 (prodF (pB F)) (succ B) x ≐ PP F x := by
  have e : Γ ⊢[PRAAx] succ B ≐ succ x + monus B x :=
    (congrSucc (eq_add_of_le h)).eqTrans (by ipra_ring)
  exact (congrAp2 (prodF (pB F)) e (.eqRefl _)).eqTrans (prod_extend F hx _)

section PP

variable {m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
include hm hN

/-- `∏_F(mn) ∏_F(d) = ∏_F(m) ∏_F(n)` for a base `F` not depending on the parameter. -/
theorem pp_split (F : PTm 2) (hF : ∀ {k : ℕ} (q x y : PTm k), inst2 F q x = inst2 F q y) :
    Γ ⊢[PRAAx] PP F (m * N) * PP F (gcd m N) ≐ PP F m * PP F N := by
  have hg := gcd_pos (B := N) hm
  have hmN := pos_mul hm hN
  have lm : Γ ⊢[PRAAx] le m (m * N) :=
    le_of_eq_add (d := m * pred N) (withEq hN fun e => by apply deriveNat; ipra_simps; rw [e]; ring)
  have lN : Γ ⊢[PRAAx] le N (m * N) :=
    le_of_eq_add (d := pred m * N) (withEq hm fun e => by apply deriveNat; ipra_simps; rw [e]; ring)
  have ld : Γ ⊢[PRAAx] le (gcd m N) (m * N) :=
    le_trans (dvd_le' hg (Prf.andE₁ (gcd_dvd' (b := N) hm)) hm) lm
  -- The pointwise identity, summed in the exponent.
  have hpt : Γ ⊢[PRAAx] ap3 (prod2F (X3 F * Y3 F)) (succ (m * N)) (m * N) (gcd m N) ≐
      ap3 (prod2F (X3 F * Y3 F)) (succ (m * N)) m N := by
    refine prod2_congr_bounded _ _ _ _ _ _ _ (.allI (.impI ?_))
    rw [EulerProduct.inst3_mul', EulerProduct.inst3_mul', inst3_X3, inst3_Y3, inst3_X3, inst3_Y3,
      inst2_pB, inst2_pB, inst2_pB, inst2_pB, hF _ (Syn.shift (gcd m N)) (Syn.shift (m * N)),
      hF _ (Syn.shift m) (Syn.shift (m * N)), hF _ (Syn.shift N) (Syn.shift (m * N))]
    refine (pw_add _ _ _).eqSymm.eqTrans (.eqTrans ?_ (pw_add _ _ _))
    refine congrAp2 powF ?_ (.eqRefl _)
    have e : Syn.shift (gcd m N) = gcd (Syn.shift m) (Syn.shift N) := by
      simp only [Syn.shift, subst_ex2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
    rw [SumPhi.shift_mul', e]
    exact e_split (GcdFiber.shift_pos hm).wk (GcdFiber.shift_pos hN).wk _
  have s₁ := prod2_mul (Γ := Γ) (X3 F) (Y3 F) (succ (m * N)) (m * N) (gcd m N)
  have s₂ := prod2_mul (Γ := Γ) (X3 F) (Y3 F) (succ (m * N)) m N
  refine .eqTrans ?_ ((s₁.eqSymm.eqTrans (hpt.eqTrans s₂)).eqTrans ?_)
  · exact (congrMul ((prod2_X3 F _ _ _).eqTrans (.eqRefl _))
      ((Permutation.prod2_eq_prod _ _ _ _).eqTrans (prod_to_pp F hg ld))).eqSymm
  · exact congrMul ((prod2_X3 F _ _ _).eqTrans (prod_to_pp F hm lm))
      ((Permutation.prod2_eq_prod _ _ _ _).eqTrans (prod_to_pp F hN lN))

/-- `thm:phi-general-mul` at arbitrary `m, n ≥ 1`. -/
theorem general_mul_at : Γ ⊢[PRAAx] phi (m * N) * phi (gcd m N) ≐ phi m * phi N * gcd m N := by
  have hK := pos_mul (rad_pos (Γ := Γ) m) (rad_pos (Γ := Γ) N)
  refine mul_cancel hK ?_
  ipra_lc -Groth.ι (Q.mk _ (phi (m * N))) * Groth.ι (Q.mk _ (phi (gcd m N))) * natEq (pp_split hm hN F₁ hF₁) +
    Groth.ι (Q.mk _ (phi (gcd m N))) * Groth.ι (Q.mk _ (PP F₁ (gcd m N))) * natEq (euler_product_at (Γ := Γ) (m * N)) +
    Groth.ι (Q.mk _ m) * Groth.ι (Q.mk _ N) * Groth.ι (Q.mk _ (PP F₂ (m * N))) * natEq (euler_product_at (Γ := Γ) (gcd m N)) +
    Groth.ι (Q.mk _ m) * Groth.ι (Q.mk _ N) * Groth.ι (Q.mk _ (gcd m N)) * natEq (pp_split hm hN F₂ hF₂) -
    Groth.ι (Q.mk _ (gcd m N)) * Groth.ι (Q.mk _ (phi N)) * Groth.ι (Q.mk _ (PP F₁ N)) * natEq (euler_product_at (Γ := Γ) m) -
    Groth.ι (Q.mk _ (gcd m N)) * Groth.ι (Q.mk _ m) * Groth.ι (Q.mk _ (PP F₂ m)) * natEq (euler_product_at (Γ := Γ) N)

end PP

/-- `thm:phi-general-mul`: `φ(mn) φ(gcd(m, n)) = φ(m) φ(n) gcd(m, n)` for `m, n ≥ 1`;
variables `0 = m − 1`, `1 = n − 1`. -/
abbrev generalMulFormula : Fm PTm 2 :=
  phi (succ (var 0) * succ (var 1)) * phi (gcd (succ (var 0)) (succ (var 1))) ≐
    phi (succ (var 0)) * phi (succ (var 1)) * gcd (succ (var 0)) (succ (var 1))

theorem general_mul : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 generalMulFormula :=
  closeUniv 2 (general_mul_at (congrSucc (pred_succ _).eqSymm) (congrSucc (pred_succ _).eqSymm))

end LeanProofs.IPRA.AnalyticNumberTheory.GeneralMul
