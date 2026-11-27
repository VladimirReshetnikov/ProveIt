import IPRADerivations.AnalyticNumberTheory.ConvolutionDivisorWeights

/-!
# Dirichlet convolution preserves multiplicativity

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`,
`chapters/elementary.tex`, `el:convolution`.
On positive coprime inputs the existing divisor factorization
reindexes the original convolution sum as a double sum. For a pair
of divisors the original weight is the product of the two weights.
Two applications of scaling for finite sums then split the double
sum into the two original convolutions.

The first closed endpoint uses only the product tests on the actual
divisor rectangle. The second proves the usual preservation of the
unit value and the coprime product law. Both are schemata in the
primitive recursive bodies, with object-level quantifiers over the
natural arguments and their common parameter.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionMultiplicative

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionDivisorWeights
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv cv_at)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorFactor
  (Xp lB riB rB lB_at riB_at rB_at divisor_factor pos_sh on_coprime_divisor_pairs shift_succ_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (subst_up_shift')
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.Probability.Independence (sum_scale shift_inst2)
open LeanProofs.IPRA.Signum (sg sg_zero)
open SumPhi renaming shift_mul' → shift_product

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem inner_point (f g : PTm 2) {m N y a b : PTm n}
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (ha : Γ ⊢[PRAAx] dvd a m)
    (hf : Γ ⊢[PRAAx] productLaw f m N y) (hg : Γ ⊢[PRAAx] productLaw g m N y) :
    Γ ⊢[PRAAx] inst2 (riB (cvB f g)) b (pairT a (Xp m N (pairT (m * N) y))) ≐
      inst2 (cvB f g) a (pairT m y) * inst2 (cvB f g) b (pairT N y) := by
  refine (riB_at (cvB f g) b a m N _).eqTrans ?_
  refine .orE (eq_or_ne (rem N b) zero) ?_ ?_
  · have hb : (dvd b N :: Γ) ⊢[PRAAx] dvd b N := Prf.hyp0
    exact (congrMul (eqb_of_eq hb) (weight_product f g hm.wk hN.wk ha.wk hb hf.wk hg.wk)).eqTrans
      (one_mul _)
  · have hb : (neg (dvd b N) :: Γ) ⊢[PRAAx] neg (dvd b N) := Prf.hyp0
    exact (zero_mul_l (eqb_of_ne hb) _).eqTrans
      (((congrMul (.eqRefl _) (weight_false f g hb)).eqTrans (mul_zero _)).eqSymm)

private theorem inner_sum (f g : PTm 2) {m N y a : PTm n}
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (ha : Γ ⊢[PRAAx] dvd a m)
    (hf : Γ ⊢[PRAAx] productLaw f m N y) (hg : Γ ⊢[PRAAx] productLaw g m N y) :
    Γ ⊢[PRAAx] ap2 (sumF (riB (cvB f g))) (succ N) (pairT a (Xp m N (pairT (m * N) y))) ≐
      inst2 (cvB f g) a (pairT m y) * conv f g N y := by
  refine sum_scale (riB (cvB f g)) (cvB f g) (succ N) (inst2 (cvB f g) a (pairT m y))
    (pairT N y) (pairT a (Xp m N (pairT (m * N) y))) (.allI (.impI ?_))
  simp only [shift_pairT, shift_product, shift_inst2]
  exact inner_point f g (pos_sh hm).wk (pos_sh hN).wk (dvd_shift ha).wk
    (product_law_shift hf).wk (product_law_shift hg).wk

private theorem outer_point (f g : PTm 2) {m N y a : PTm n}
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hf : Γ ⊢[PRAAx] productLaw f m N y) (hg : Γ ⊢[PRAAx] productLaw g m N y) :
    Γ ⊢[PRAAx] inst2 (rB (cvB f g)) a (Xp m N (pairT (m * N) y)) ≐
      conv f g N y * inst2 (cvB f g) a (pairT m y) := by
  refine (rB_at (cvB f g) a m N _).eqTrans ?_
  refine .orE (eq_or_ne (rem m a) zero) ?_ ?_
  · have ha : (dvd a m :: Γ) ⊢[PRAAx] dvd a m := Prf.hyp0
    refine (congrMul (eqb_of_eq ha) (inner_sum f g hm.wk hN.wk ha hf.wk hg.wk)).eqTrans ?_
    exact (one_mul _).eqTrans (mul_comm _ _)
  · have ha : (neg (dvd a m) :: Γ) ⊢[PRAAx] neg (dvd a m) := Prf.hyp0
    exact (zero_mul_l (eqb_of_ne ha) _).eqTrans
      (((congrMul (.eqRefl _) (weight_false f g ha)).eqTrans (mul_zero _)).eqSymm)

/-- The actual convolution product law under the bounded divisor tests. -/
theorem conv_product (f g : PTm 2) {m N y : PTm n}
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hc : Γ ⊢[PRAAx] gcd m N ≐ one)
    (hf : Γ ⊢[PRAAx] productLaw f m N y) (hg : Γ ⊢[PRAAx] productLaw g m N y) :
    Γ ⊢[PRAAx] conv f g (m * N) y ≐ conv f g m y * conv f g N y := by
  have left : Γ ⊢[PRAAx] conv f g (m * N) y ≐
      ap2 (sumF (lB (cvB f g))) (succ (m * N)) (Xp m N (pairT (m * N) y)) := by
    refine sum_congr_bounded (cvB f g) (lB (cvB f g)) _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT, shift_product]
    exact ((lB_at (cvB f g) (var 0) _ _ _).eqTrans (weight_absorb f g (var 0) _ _)).eqSymm
  have middle := divisor_factor (cvB f g) hm hN hc (pairT (m * N) y)
  have right : Γ ⊢[PRAAx] ap2 (sumF (rB (cvB f g))) (succ m) (Xp m N (pairT (m * N) y)) ≐
      conv f g N y * conv f g m y := by
    refine sum_scale (rB (cvB f g)) (cvB f g) (succ m) (conv f g N y) (pairT m y)
      (Xp m N (pairT (m * N) y)) (.allI (.impI ?_))
    simp only [shift_pairT, shift_product]
    have shiftConv : Syn.shift (conv f g N y) = conv f g (Syn.shift N) (Syn.shift y) := by
      simp [Syn.shift]
    rw [shiftConv]
    exact outer_point f g (pos_sh hm).wk (pos_sh hN).wk (product_law_shift hf).wk (product_law_shift hg).wk
  exact left.eqTrans (middle.eqTrans (right.eqTrans (mul_comm _ _)))

/-- Coprime positive factors and the product tests on their finite divisor rectangle. -/
def rectangleFormula (f g : PTm 2) : Fm PTm 3 :=
  le one (var 0) ⟶ le one (var 1) ⟶ gcd (var 0) (var 1) ≐ one ⟶
    productLaw f (var 0) (var 1) (var 2) ⟶ productLaw g (var 0) (var 1) (var 2) ⟶
      conv f g (var 0 * var 1) (var 2) ≐ conv f g (var 0) (var 2) * conv f g (var 1) (var 2)

theorem conv_on_divisor_rectangle_closed (f g : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (rectangleFormula f g) := by
  refine closeUniv 3 (.impI (.impI (.impI (.impI (.impI ?_)))))
  exact conv_product f g (pos_of_one_le hyp2.wk.wk) (pos_of_one_le hyp2.wk) hyp2 Prf.hyp1 Prf.hyp0

theorem conv_at_one (f g : PTm 2) (y : PTm n) :
    Γ ⊢[PRAAx] conv f g one y ≐ inst2 f one y * inst2 g one y := by
  have z : Γ ⊢[PRAAx] inst2 (cvB f g) zero (pairT one y) ≐ zero :=
    (cv_at f g zero one y).eqTrans (zero_mul_l (zero_mul_l sg_zero _) _)
  have u : Γ ⊢[PRAAx] ap2 (sumF (cvB f g)) one (pairT one y) ≐ zero :=
    (sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) z).eqTrans (zero_add _))
  have onePos : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := pos_of_eq_succ (c := zero) (.eqRefl _)
  have o := (weight_true f g (y := y) onePos (dvd_self zero)).eqTrans
    (congrMul (.eqRefl _) (congrInst2 g (RSA.quo_one one) (.eqRefl _)))
  exact (sum_succ' _ _ _).eqTrans ((congrAdd u o).eqTrans (zero_add _))

/-- The unit law and the coprime product law for a body at its parameter. -/
def multiplicative (f : PTm 2) (y : PTm n) : Fm PTm n :=
  (inst2 f one y ≐ one) ⋏ Fm.all (Fm.all (le one (var 1) ⟶ le one (var 0) ⟶ gcd (var 1) (var 0) ≐ one ⟶
    inst2 f (var 1 * var 0) (Syn.shift (Syn.shift y)) ≐
      inst2 f (var 1) (Syn.shift (Syn.shift y)) * inst2 f (var 0) (Syn.shift (Syn.shift y))))

private theorem subst_multiplicative {k : ℕ} (σ : Fin n → PTm k) (f : PTm 2) (y : PTm n) :
    (multiplicative f y).subst σ = multiplicative f (Syn.subst σ y) := by
  simp only [multiplicative, Fm.subst_and, Fm.subst_all, Fm.subst_imp, Fm.subst_eq, subst_inst2,
    subst_le, subst_ex2, subst_up_shift', PTm.subst_mul, Syn.subst_var, Syn.up_one, Syn.up_zero,
    Syn.shift_var, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
  rfl

private theorem multiplicative_shift {f : PTm 2} {y : PTm n} (h : Γ ⊢[PRAAx] multiplicative f y) :
    Γ.map Fm.shift ⊢[PRAAx] multiplicative f (Syn.shift y) := by
  simpa only [Fm.shift, Syn.shift, subst_multiplicative] using h.shift

private theorem multiplicative_at {f : PTm 2} {m N y : PTm n}
    (hf : Γ ⊢[PRAAx] multiplicative f y)
    (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] gcd m N ≐ one) :
    Γ ⊢[PRAAx] inst2 f (m * N) y ≐ inst2 f m y * inst2 f N y := by
  have h := Prf.allE m (Prf.andE₂ hf)
  simp only [Fm.subst_all, Fm.subst_imp, Fm.subst_eq, subst_le, subst_ex2, subst_up_shift',
    subst_inst2, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
    Syn.subst_inst_shift, Syn.subst_var, Syn.up_one, Syn.up_zero, Syn.inst_zero] at h
  have h' := Prf.allE N h
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ex2, subst_inst2, PTm.subst_mul,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
    Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero] at h'
  exact .impE (.impE (.impE h' hm) hN) hc

private theorem product_law_of_multiplicative {f : PTm 2} {m N y : PTm n}
    (hf : Γ ⊢[PRAAx] multiplicative f y)
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hc : Γ ⊢[PRAAx] gcd m N ≐ one) :
    Γ ⊢[PRAAx] productLaw f m N y := by
  unfold productLaw
  exact on_coprime_divisor_pairs hm hN hc fun ha hb hab =>
    multiplicative_at (multiplicative_shift (multiplicative_shift hf)).wk.wk ha hb hab

theorem conv_multiplicative (f g : PTm 2) {y : PTm n}
    (hf : Γ ⊢[PRAAx] multiplicative f y) (hg : Γ ⊢[PRAAx] multiplicative g y) :
    Γ ⊢[PRAAx] multiplicative (cvF f g) y := by
  unfold multiplicative
  refine .andI ?_ (.allI (.allI (.impI (.impI (.impI ?_)))))
  · rw [inst2_cvF]
    exact (conv_at_one f g y).eqTrans ((congrMul (Prf.andE₁ hf) (Prf.andE₁ hg)).eqTrans (one_mul _))
  · simp only [inst2_cvF]
    let m : PTm (n + 2) := var 1
    let N : PTm (n + 2) := var 0
    let Δ := (gcd m N ≐ one) :: le one N :: le one m :: (Γ.map Fm.shift).map Fm.shift
    have hm : Δ ⊢[PRAAx] m ≐ succ (pred m) := pos_of_one_le hyp2
    have hN : Δ ⊢[PRAAx] N ≐ succ (pred N) := pos_of_one_le Prf.hyp1
    have hc : Δ ⊢[PRAAx] gcd m N ≐ one := Prf.hyp0
    exact conv_product f g hm hN hc
      (product_law_of_multiplicative (multiplicative_shift (multiplicative_shift hf)).wk.wk.wk hm hN hc)
      (product_law_of_multiplicative (multiplicative_shift (multiplicative_shift hg)).wk.wk.wk hm hN hc)

def preservationFormula (f g : PTm 2) : Fm PTm 1 :=
  multiplicative f (var 0) ⟶ multiplicative g (var 0) ⟶ multiplicative (cvF f g) (var 0)

/-- The original Dirichlet convolution of multiplicative bodies is multiplicative. -/
theorem conv_preserves_multiplicative_closed (f g : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (preservationFormula f g) :=
  closeUniv 1 (.impI (.impI (conv_multiplicative f g Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionMultiplicative
