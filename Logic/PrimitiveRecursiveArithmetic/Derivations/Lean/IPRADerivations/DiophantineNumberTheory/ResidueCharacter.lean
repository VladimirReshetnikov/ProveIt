import IPRADerivations.DiophantineNumberTheory.AperyMultibound
import IPRADerivations.DiophantineNumberTheory.FourSquares

/-!
# Multiplicativity of the quadratic residue symbol, and four rational squares

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/quadratic.tex`: `qr:character`
("Multiplicativity": `χ_p(ab) = χ_p(a) χ_p(b)`) and `qr:rational-four` ("Four squares over the nonnegative
rationals").

With `rb p a` the bit of "some `x < p` has `x² ≡ a (mod p)`" (`GaussLemma.rb`), an odd prime `p` and units
`a`, `b` modulo `p`:

* `pow_cases`: `a^h ≡ 1` when `rb p a = 1` and `a^h ≡ p − 1` when `rb p a = 0` (`h = ⌊p/2⌋`; Euler's criterion,
  `GaussLemma.euler_res`, `euler_nr`);
* `decide_res`, `decide_nr`: conversely the value of `c^h` decides the bit, because `1 ≠ p − 1`;
* `rb_mul_rr`, `rb_mul_nn`, `rb_mul_rn`, `rb_mul_nr`: the four cases of the product, from
  `(ab)^h = a^h b^h`;
* `rb_mul` (`qr:character`): `rb p (a b) = [rb p a = rb p b]`, that is `χ_p(ab) = χ_p(a) χ_p(b)` for the
  values `±1`;
* `rational_four` (`qr:rational-four`): for all `a`, `b`, the four witnesses of `a b` satisfy
  `x₀² + x₁² + x₂² + x₃² = a b`, which is `a/b = ∑ (x_i/b)²` multiplied by `b²`, with `x_i ≤ a b`.

The zero residue (`p ∣ a`) is not included in `rb_mul`: there `χ_p = 0`, while `rb p a = 1`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.ResidueCharacter

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (rem_small)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.PairProduct (sqB)
open LeanProofs.IPRA.DiophantineNumberTheory.ResidueFacts (neg_sq)
open LeanProofs.IPRA.DiophantineNumberTheory.GaussLemma (rb euler_nr euler_res pred_ne_one)
open LeanProofs.IPRA.DiophantineNumberTheory.FourSquaresAlgebra (N4)
open LeanProofs.IPRA.DiophantineNumberTheory.FourSquares (Wf four_squares witness_le)
open LeanProofs.IPRA.Foundations.BoundedReflection (ex_cases eqb_cases eq_of_eqb one_ne_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Euler's criterion in both directions -/

section Criterion

variable {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] par p ≐ one)
include hp hodd

/-- `a^h ≡ p − 1` or `a^h ≡ 1` according to the bit, for a unit `a`. -/
theorem pow_cases {a : PTm n} (hc : Γ ⊢[PRAAx] gcd p a ≐ one) (ha : Γ ⊢[PRAAx] gcd a p ≐ one) :
    Γ ⊢[PRAAx] ((rb p a ≐ zero) ⋏ (rem (pw a (half p)) p ≐ rem (pred p) p)) ⋎
      ((rb p a ≐ one) ⋏ (rem (pw a (half p)) p ≐ rem one p)) := by
  have hp1 := p_pos (prime_two hp)
  refine .orE (ex_cases sqB p (pairT p a)) ?_ ?_
  · exact .orI₁ (.andI Prf.hyp0 ((euler_nr hp.wk hodd.wk hc.wk ha.wk Prf.hyp0).eqTrans
      (rem_small (pred_lt hp1)).wk.eqSymm))
  · exact .orI₂ (.andI Prf.hyp0 (euler_res hp.wk hodd.wk ha.wk Prf.hyp0))

/-- `1 ≢ p − 1 (mod p)`. -/
theorem one_ne_neg {φ : Fm PTm n} (h : Γ ⊢[PRAAx] rem (pred p) p ≐ rem one p) : Γ ⊢[PRAAx] φ := by
  have hq := prime_two hp
  have hp1 := p_pos hq
  exact pred_ne_one hp1 hodd φ ((rem_small (pred_lt hp1)).eqSymm.eqTrans (h.eqTrans (rem_small hq)))

/-- `c^h ≡ 1` makes the unit `c` a residue. -/
theorem decide_res {c : PTm n} (hc : Γ ⊢[PRAAx] gcd p c ≐ one) (hc' : Γ ⊢[PRAAx] gcd c p ≐ one)
    (h : Γ ⊢[PRAAx] rem (pw c (half p)) p ≐ rem one p) : Γ ⊢[PRAAx] rb p c ≐ one := by
  have hp1 := p_pos (prime_two hp)
  refine .orE (ex_cases sqB p (pairT p c)) ?_ Prf.hyp0
  have e := euler_nr hp.wk hodd.wk hc.wk hc'.wk (Prf.hyp0 (Γ := Γ) (φ := rb p c ≐ zero))
  exact one_ne_neg hp.wk hodd.wk ((rem_small (pred_lt hp1)).wk.eqTrans (e.eqSymm.eqTrans h.wk))

/-- `c^h ≡ p − 1` makes the unit `c` a nonresidue. -/
theorem decide_nr {c : PTm n} (hc' : Γ ⊢[PRAAx] gcd c p ≐ one)
    (h : Γ ⊢[PRAAx] rem (pw c (half p)) p ≐ rem (pred p) p) : Γ ⊢[PRAAx] rb p c ≐ zero := by
  refine .orE (ex_cases sqB p (pairT p c)) Prf.hyp0 ?_
  have e := euler_res hp.wk hodd.wk hc'.wk (Prf.hyp0 (Γ := Γ) (φ := rb p c ≐ one))
  exact one_ne_neg hp.wk hodd.wk (h.wk.eqSymm.eqTrans e)

/-! ## The product of two units -/

variable {a b : PTm n} (ha1 : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb1 : Γ ⊢[PRAAx] b ≐ succ (pred b))
  (hca : Γ ⊢[PRAAx] gcd p a ≐ one) (hcb : Γ ⊢[PRAAx] gcd p b ≐ one)
include ha1 hb1 hca hcb

omit hodd in
theorem unit_mul : Γ ⊢[PRAAx] (gcd p (a * b) ≐ one) ⋏ (gcd (a * b) p ≐ one) := by
  have hp1 := p_pos (prime_two hp)
  have c := coprime_mul hp1 hca hcb
  exact .andI c (gcd_comm_one (pos_mul ha1 hb1) c)

omit hodd ha1 hb1 hca hcb in
/-- `(ab)^h ≡ E F` when `a^h ≡ E` and `b^h ≡ F`. -/
theorem pow_mul {E F : PTm n} (ea : Γ ⊢[PRAAx] rem (pw a (half p)) p ≐ rem E p)
    (eb : Γ ⊢[PRAAx] rem (pw b (half p)) p ≐ rem F p) :
    Γ ⊢[PRAAx] rem (pw (a * b) (half p)) p ≐ rem (E * F) p :=
  (congrAp2 remF (mul_pw a b (half p)) (.eqRefl _)).eqTrans (rem_mul_congr2 (p_pos (prime_two hp)) ea eb)

theorem rb_mul_rr (ea : Γ ⊢[PRAAx] rem (pw a (half p)) p ≐ rem one p)
    (eb : Γ ⊢[PRAAx] rem (pw b (half p)) p ≐ rem one p) : Γ ⊢[PRAAx] rb p (a * b) ≐ one := by
  have u := unit_mul hp ha1 hb1 hca hcb
  exact decide_res hp hodd (Prf.andE₁ u) (Prf.andE₂ u)
    ((pow_mul hp ea eb).eqTrans (congrAp2 remF (one_mul one) (.eqRefl _)))

theorem rb_mul_nn (ea : Γ ⊢[PRAAx] rem (pw a (half p)) p ≐ rem (pred p) p)
    (eb : Γ ⊢[PRAAx] rem (pw b (half p)) p ≐ rem (pred p) p) : Γ ⊢[PRAAx] rb p (a * b) ≐ one := by
  have u := unit_mul hp ha1 hb1 hca hcb
  exact decide_res hp hodd (Prf.andE₁ u) (Prf.andE₂ u)
    ((pow_mul hp ea eb).eqTrans (neg_sq (prime_two hp)))

theorem rb_mul_rn (ea : Γ ⊢[PRAAx] rem (pw a (half p)) p ≐ rem one p)
    (eb : Γ ⊢[PRAAx] rem (pw b (half p)) p ≐ rem (pred p) p) : Γ ⊢[PRAAx] rb p (a * b) ≐ zero := by
  have u := unit_mul hp ha1 hb1 hca hcb
  exact decide_nr hp hodd (Prf.andE₂ u)
    ((pow_mul hp ea eb).eqTrans (congrAp2 remF (one_mul _) (.eqRefl _)))

theorem rb_mul_nr (ea : Γ ⊢[PRAAx] rem (pw a (half p)) p ≐ rem (pred p) p)
    (eb : Γ ⊢[PRAAx] rem (pw b (half p)) p ≐ rem one p) : Γ ⊢[PRAAx] rb p (a * b) ≐ zero := by
  have u := unit_mul hp ha1 hb1 hca hcb
  exact decide_nr hp hodd (Prf.andE₂ u)
    ((pow_mul hp ea eb).eqTrans (congrAp2 remF ((mul_comm _ _).eqTrans (one_mul _)) (.eqRefl _)))

omit hp hodd ha1 hb1 hca hcb in
theorem eqb_one_zero : Γ ⊢[PRAAx] eqb (one : PTm n) zero ≐ zero := by
  refine .orE (eqb_cases (one : PTm n) zero) Prf.hyp0 ?_
  exact one_ne_zero _ (eq_of_eqb Prf.hyp0)

omit hp hodd ha1 hb1 hca hcb in
theorem eqb_zero_one : Γ ⊢[PRAAx] eqb (zero : PTm n) one ≐ zero := by
  refine .orE (eqb_cases (zero : PTm n) one) Prf.hyp0 ?_
  exact one_ne_zero _ (eq_of_eqb Prf.hyp0).eqSymm

/-- `qr:character`: `rb p (a b) = [rb p a = rb p b]` for an odd prime `p` and units `a`, `b`. -/
theorem rb_mul : Γ ⊢[PRAAx] rb p (a * b) ≐ eqb (rb p a) (rb p b) := by
  have hac := gcd_comm_one ha1 hca
  have hbc := gcd_comm_one hb1 hcb
  refine .orE (pow_cases hp hodd hca hac) ?_ ?_
  · refine .orE (pow_cases hp hodd hcb hbc).wk ?_ ?_
    · have A : ((rb p b ≐ zero) ⋏ (rem (pw b (half p)) p ≐ rem (pred p) p)) ::
          ((rb p a ≐ zero) ⋏ (rem (pw a (half p)) p ≐ rem (pred p) p)) :: Γ ⊢[PRAAx] _ := Prf.hyp1
      have B : ((rb p b ≐ zero) ⋏ (rem (pw b (half p)) p ≐ rem (pred p) p)) ::
          ((rb p a ≐ zero) ⋏ (rem (pw a (half p)) p ≐ rem (pred p) p)) :: Γ ⊢[PRAAx] _ := Prf.hyp0
      exact (rb_mul_nn hp.wk.wk hodd.wk.wk ha1.wk.wk hb1.wk.wk hca.wk.wk hcb.wk.wk (Prf.andE₂ A)
        (Prf.andE₂ B)).eqTrans ((congrEqb' (Prf.andE₁ A) (Prf.andE₁ B)).eqTrans (eqb_of_eq (.eqRefl zero))).eqSymm
    · have A : ((rb p b ≐ one) ⋏ (rem (pw b (half p)) p ≐ rem one p)) ::
          ((rb p a ≐ zero) ⋏ (rem (pw a (half p)) p ≐ rem (pred p) p)) :: Γ ⊢[PRAAx] _ := Prf.hyp1
      have B : ((rb p b ≐ one) ⋏ (rem (pw b (half p)) p ≐ rem one p)) ::
          ((rb p a ≐ zero) ⋏ (rem (pw a (half p)) p ≐ rem (pred p) p)) :: Γ ⊢[PRAAx] _ := Prf.hyp0
      exact (rb_mul_nr hp.wk.wk hodd.wk.wk ha1.wk.wk hb1.wk.wk hca.wk.wk hcb.wk.wk (Prf.andE₂ A)
        (Prf.andE₂ B)).eqTrans ((congrEqb' (Prf.andE₁ A) (Prf.andE₁ B)).eqTrans eqb_zero_one).eqSymm
  · refine .orE (pow_cases hp hodd hcb hbc).wk ?_ ?_
    · have A : ((rb p b ≐ zero) ⋏ (rem (pw b (half p)) p ≐ rem (pred p) p)) ::
          ((rb p a ≐ one) ⋏ (rem (pw a (half p)) p ≐ rem one p)) :: Γ ⊢[PRAAx] _ := Prf.hyp1
      have B : ((rb p b ≐ zero) ⋏ (rem (pw b (half p)) p ≐ rem (pred p) p)) ::
          ((rb p a ≐ one) ⋏ (rem (pw a (half p)) p ≐ rem one p)) :: Γ ⊢[PRAAx] _ := Prf.hyp0
      exact (rb_mul_rn hp.wk.wk hodd.wk.wk ha1.wk.wk hb1.wk.wk hca.wk.wk hcb.wk.wk (Prf.andE₂ A)
        (Prf.andE₂ B)).eqTrans ((congrEqb' (Prf.andE₁ A) (Prf.andE₁ B)).eqTrans eqb_one_zero).eqSymm
    · have A : ((rb p b ≐ one) ⋏ (rem (pw b (half p)) p ≐ rem one p)) ::
          ((rb p a ≐ one) ⋏ (rem (pw a (half p)) p ≐ rem one p)) :: Γ ⊢[PRAAx] _ := Prf.hyp1
      have B : ((rb p b ≐ one) ⋏ (rem (pw b (half p)) p ≐ rem one p)) ::
          ((rb p a ≐ one) ⋏ (rem (pw a (half p)) p ≐ rem one p)) :: Γ ⊢[PRAAx] _ := Prf.hyp0
      exact (rb_mul_rr hp.wk.wk hodd.wk.wk ha1.wk.wk hb1.wk.wk hca.wk.wk hcb.wk.wk (Prf.andE₂ A)
        (Prf.andE₂ B)).eqTrans ((congrEqb' (Prf.andE₁ A) (Prf.andE₁ B)).eqTrans (eqb_of_eq (.eqRefl one))).eqSymm

end Criterion

/-! ## Four rational squares -/

/-- `qr:rational-four`: `a/b = ∑ (x_i/b)²` cleared by `b²`: the witnesses of `a b` have
`x₀² + x₁² + x₂² + x₃² = a b`. -/
theorem rational_four (a b : PTm n) :
    Γ ⊢[PRAAx] N4 (Wf (a * b) 0) (Wf (a * b) 1) (Wf (a * b) 2) (Wf (a * b) 3) ≐ a * b :=
  four_squares (a * b)

/-- The numerators are at most `a b`. -/
theorem rational_four_le (a b : PTm n) (i : Fin 4) : Γ ⊢[PRAAx] le (Wf (a * b) i) (a * b) :=
  witness_le (a * b) i

end LeanProofs.IPRA.DiophantineNumberTheory.ResidueCharacter
