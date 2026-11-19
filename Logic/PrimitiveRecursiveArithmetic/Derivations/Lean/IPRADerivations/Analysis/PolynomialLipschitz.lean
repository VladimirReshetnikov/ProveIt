import IPRADerivations.Analysis.PowerGap
import IPRADerivations.Combinatorics.BinomialTheorem
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Foundations.EigenvalueBound
import IPRADerivations.Probability.Variance

/-!
# The Lipschitz bound of a polynomial

Packet: `foundations/ipra_finite_use_framework_2026-11-15`, `sections/06_quantitative.tex`, "Polynomial
evaluation", `eq:poly-lip` (P-Lip): for `P(z) = ∑_{j ≤ d} c_j z^j` and `|z|, |w| ≤ M`,
`|P(z) − P(w)| ≤ |z − w| ∑_{j=1}^d j |c_j| max(1, M)^{j−1}`; Lemma `lem:poly-observation` ("Prove the
power-difference identity by induction on `j`, then the polynomial estimate by induction on the coefficient
list").

Cleared form, for natural coefficients `c(j, x)` and natural points (a rational polynomial over a common
denominator `q` becomes one with natural coefficients `c_j q^{d−j}` after multiplying by `q^d`; signed
coefficients split into two natural polynomials):

* `polyB`, `poly_at`: the terms `c_j Z^j` of `P(Z) = ∑_{j<D} c_j Z^j`, read from the parameter `⟨Z, x⟩`;
* `lipB`, `lip_at`: the terms `c_j j M^{j−1}` of the Lipschitz majorant `L(M) = ∑_{j<D} j c_j M^{j−1}`;
* `term_le`: for `Z = W + d ≤ M`, `c_j Z^j ≤ c_j W^j + d c_j j M^{j−1}` (`PowerGap.power_gap` for `j ≥ 1`;
  `j = 0` is constant);
* `poly_lip` (P-Lip): `P(Z) ≤ P(W) + (Z − W) L(M)` for `W ≤ Z ≤ M`, by induction on the number `D` of
  coefficients; with `P(W) ≤ P(Z)` this is `|P(Z) − P(W)| ≤ |Z − W| L(M)`;
* `poly_mono`: `P(W) ≤ P(Z)` for `W ≤ Z`;
* `poly_lip_signed`: for a signed polynomial `P = P⁺ − P⁻` (two natural coefficient bodies),
  `|(P⁺(Z) − P⁻(Z)) − (P⁺(W) − P⁻(W))| ≤ (Z − W)(L⁺(M) + L⁻(M))`, written
  `ad(P⁺(Z) + P⁻(W), P⁺(W) + P⁻(Z)) ≤ d (L⁺(M) + L⁻(M))`: the bound with `|c_j| = c⁺_j + c⁻_j`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.PolynomialLipschitz

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.PowerGap (power_gap shift_le' shift_eq')
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Foundations.EigenvalueBound (ad_le_of)
open LeanProofs.IPRA.Probability.Variance (ad)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

section Poly

variable (c : PTm 2)

/-- `c_j Z^j` over `0 = j`, `1 = ⟨Z, x⟩`. -/
def polyB : PTm 2 := Syn.subst ![var 0, sndT (var 1)] c * pw (fstT (var 1)) (var 0)

/-- `c_j j M^{j−1}` over `0 = j`, `1 = ⟨M, x⟩`. -/
def lipB : PTm 2 := Syn.subst ![var 0, sndT (var 1)] c * (var 0 * pw (fstT (var 1)) (pred (var 0)))

theorem inst2_polyB (j y : PTm n) : inst2 (polyB c) j y = inst2 c j (sndT y) * pw (fstT y) j := by
  simp only [inst2, polyB, PTm.subst_mul, Syn.subst_subst]
  congr 1
  · congr 1; funext i; fin_cases i <;> simp
  · simp

theorem inst2_lipB (j y : PTm n) :
    inst2 (lipB c) j y = inst2 c j (sndT y) * (j * pw (fstT y) (pred j)) := by
  simp only [inst2, lipB, PTm.subst_mul, Syn.subst_subst]
  congr 1
  · congr 1; funext i; fin_cases i <;> simp
  · simp

theorem poly_at (j Z x : PTm n) :
    Γ ⊢[PRAAx] inst2 (polyB c) j (pairT Z x) ≐ inst2 c j x * pw Z j := by
  rw [inst2_polyB]
  exact congrMul (congrInst2 c (.eqRefl _) (snd_pair _ _)) (congrPw (fst_pair _ _) (.eqRefl _))

theorem lip_at (j M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (lipB c) j (pairT M x) ≐ inst2 c j x * (j * pw M (pred j)) := by
  rw [inst2_lipB]
  exact congrMul (congrInst2 c (.eqRefl _) (snd_pair _ _))
    (congrMul (.eqRefl _) (congrPw (fst_pair _ _) (.eqRefl _)))

variable {c}

/-- One term: `c_j Z^j ≤ c_j W^j + d c_j j M^{j−1}` for `Z = W + d ≤ M`. -/
theorem term_le {x Z W M d : PTm n} (hd : Γ ⊢[PRAAx] Z ≐ W + d) (hU : Γ ⊢[PRAAx] le Z M) (j : PTm n) :
    Γ ⊢[PRAAx] le (inst2 c j x * pw Z j)
      (inst2 c j x * pw W j + d * (inst2 c j x * (j * pw M (pred j)))) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · have hj : ((j ≐ zero) :: Γ) ⊢[PRAAx] j ≐ zero := Prf.hyp0
    have eZ := natEq ((congrPw (.eqRefl Z) hj).eqTrans (pw_zero Z))
    have eW := natEq ((congrPw (.eqRefl W) hj).eqTrans (pw_zero W))
    have ej := natEq hj
    ipra_le 0 using
      linear_combination 𝔟 (inst2 c j x) * eW - 𝔟 (inst2 c j x) * eZ +
        𝔟 d * 𝔟 (inst2 c j x) * 𝔟 (pw M (pred j)) * ej
  · have hj : ((j ≐ succ (pred j)) :: Γ) ⊢[PRAAx] j ≐ succ (pred j) := Prf.hyp0
    have pg := power_gap (hd.wk (ψ := j ≐ succ (pred j))) (hU.wk (ψ := j ≐ succ (pred j))) (pred j)
    have pg' : ((j ≐ succ (pred j)) :: Γ) ⊢[PRAAx]
        le (pw Z j) (pw W j + d * (j * pw M (pred j))) :=
      le_congr (congrPw (.eqRefl Z) hj.eqSymm)
        (congrAdd (congrPw (.eqRefl W) hj.eqSymm) (congrMul (.eqRefl d) (congrMul hj.eqSymm (.eqRefl _)))) pg
    ipra_le 𝔟 (inst2 c j x) * sl pg'

/-! ## The polynomial -/

/-- `P(Z) ≤ P(W) + d L(M)` for the first `D` coefficients. -/
abbrev LipInv (c : PTm 2) (D Z W M d x : PTm n) : Fm PTm n :=
  le (ap2 (sumF (polyB c)) D (pairT Z x))
    (ap2 (sumF (polyB c)) D (pairT W x) + d * ap2 (sumF (lipB c)) D (pairT M x))

theorem lip_step {D Z W M d x : PTm n} (hd : Γ ⊢[PRAAx] Z ≐ W + d) (hU : Γ ⊢[PRAAx] le Z M)
    (ih : Γ ⊢[PRAAx] LipInv c D Z W M d x) : Γ ⊢[PRAAx] LipInv c (succ D) Z W M d x := by
  have e1 := natEq (sum_succ' (Γ := Γ) (polyB c) D (pairT Z x))
  have e2 := natEq (sum_succ' (Γ := Γ) (polyB c) D (pairT W x))
  have e3 := natEq (sum_succ' (Γ := Γ) (lipB c) D (pairT M x))
  have a1 := natEq (poly_at (Γ := Γ) c D Z x)
  have a2 := natEq (poly_at (Γ := Γ) c D W x)
  have a3 := natEq (lip_at (Γ := Γ) c D M x)
  have t := term_le (c := c) (x := x) hd hU D
  ipra_le sl ih + sl t using rw [e1, e2, e3, a1, a2, a3]; ring

/-- `eq:poly-lip`: `P(Z) ≤ P(W) + (Z − W) ∑_{j<D} j c_j M^{j−1}` for `W ≤ Z ≤ M`. -/
theorem poly_lip {Z W M d x : PTm n} (hd : Γ ⊢[PRAAx] Z ≐ W + d) (hU : Γ ⊢[PRAAx] le Z M) (D : PTm n) :
    Γ ⊢[PRAAx] LipInv c D Z W M d x := by
  have hall : Γ ⊢[PRAAx] Fm.all (LipInv c (var 0) (Syn.shift Z) (Syn.shift W) (Syn.shift M)
      (Syn.shift d) (Syn.shift x)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      have z1 := natEq (sum_zero (Γ := Γ) (polyB c) (pairT Z x))
      have z2 := natEq (sum_zero (Γ := Γ) (polyB c) (pairT W x))
      have z3 := natEq (sum_zero (Γ := Γ) (lipB c) (pairT M x))
      ipra_le 0 using rw [z1, z2, z3]; ring
    · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact lip_step (shift_eq' hd).wk (shift_le' hU).wk Prf.hyp0
  have h := Prf.allE D hall
  simpa only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] using h

/-- `P(W) ≤ P(Z)` for `W ≤ Z`. -/
theorem poly_mono {W Z x : PTm n} (h : Γ ⊢[PRAAx] le W Z) (D : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF (polyB c)) D (pairT W x)) (ap2 (sumF (polyB c)) D (pairT Z x)) := by
  refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  have h' := (shift_le' h).wk (ψ := lt (var 0) (Syn.shift D))
  have p := pw_le_pw (var 0) h'
  refine le_congr (poly_at c _ _ _).eqSymm (poly_at c _ _ _).eqSymm ?_
  ipra_le 𝔟 (inst2 c (var 0) (Syn.shift x)) * sl p

/-- `eq:poly-lip` with signed coefficients `c⁺ − c⁻`. -/
theorem poly_lip_signed (c' : PTm 2) {Z W M d x : PTm n} (hd : Γ ⊢[PRAAx] Z ≐ W + d)
    (hU : Γ ⊢[PRAAx] le Z M) (D : PTm n) :
    Γ ⊢[PRAAx] le
      (ad (ap2 (sumF (polyB c)) D (pairT Z x) + ap2 (sumF (polyB c')) D (pairT W x))
        (ap2 (sumF (polyB c)) D (pairT W x) + ap2 (sumF (polyB c')) D (pairT Z x)))
      (d * (ap2 (sumF (lipB c)) D (pairT M x) + ap2 (sumF (lipB c')) D (pairT M x))) := by
  have hWZ : Γ ⊢[PRAAx] le W Z := le_of_eq_add hd
  have l₁ := poly_lip (c := c) (x := x) hd hU D
  have l₂ := poly_lip (c := c') (x := x) hd hU D
  have m₁ := poly_mono (c := c) (x := x) hWZ D
  have m₂ := poly_mono (c := c') (x := x) hWZ D
  refine ad_le_of ?_ ?_
  · ipra_le sl l₁ + sl m₂ + 𝔟 d * 𝔟 (ap2 (sumF (lipB c')) D (pairT M x))
  · ipra_le sl l₂ + sl m₁ + 𝔟 d * 𝔟 (ap2 (sumF (lipB c)) D (pairT M x))

end Poly

end LeanProofs.IPRA.Analysis.PolynomialLipschitz
