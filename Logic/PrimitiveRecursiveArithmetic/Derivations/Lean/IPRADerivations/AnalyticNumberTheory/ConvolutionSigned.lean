import IPRADerivations.AnalyticNumberTheory.ConvolutionMultiplicative
import IPRADerivations.Foundations.SignedSumScale

/-!
# The coprime product law for integer-valued Dirichlet convolution

The source of `el:convolution` allows arbitrary signed values. Each
body is represented by a pair of natural bodies in `ZB`. Multiplication
uses the four original combinations of `DirichletLeibniz.cvB`; its
positive and negative weights are summed separately. The product
hypotheses constrain only the integer values at the divisor pairs,
including complementary divisors of the same positive inputs.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionSigned

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionDivisorWeights (quotient_product)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionMultiplicative (conv_at_one)
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorFactor
  (Xp lB riB rB lB_at riB_at rB_at divisor_factor pos_sh gcd_sh)
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (subst_up_shift')
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.Foundations.SignedSumScale (sum_scale)
open SumPhi renaming shift_mul' → shift_product
open ConvolutionDivisorWeights renaming complementary_divisor → complement_divisor

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The signed summand, using the original four natural-weight bodies. -/
def weight (f g : ZB) : ZB :=
  ⟨addBody (cvB f.pos g.pos) (cvB f.neg g.neg), addBody (cvB f.pos g.neg) (cvB f.neg g.pos)⟩

/-- Dirichlet convolution at signed terms. -/
def convolution (f g : ZB) (M y : PTm n) : ZT n :=
  (weight f g).sum (succ M) (pairT M y)

/-- An integer product law over the exact divisor rectangle. -/
def productLaw (f : ZB) (m N y : PTm n) : Fm PTm n :=
  Fm.all (Fm.all (dvd (var 1) (Syn.shift (Syn.shift m)) ⟶ dvd (var 0) (Syn.shift (Syn.shift N)) ⟶
    ZT.eq (f.val (var 1 * var 0) (Syn.shift (Syn.shift y)))
      (f.val (var 1) (Syn.shift (Syn.shift y)) * f.val (var 0) (Syn.shift (Syn.shift y)))))

private theorem subst_val {k : ℕ} (σ : Fin n → PTm k) (b : ZB) (i x : PTm n) :
    (b.val i x).subst σ = b.val (Syn.subst σ i) (Syn.subst σ x) := by
  simp only [ZB.val, ZT.subst, subst_inst2]

private theorem subst_productLaw {k : ℕ} (σ : Fin n → PTm k) (f : ZB) (m N y : PTm n) :
    (productLaw f m N y).subst σ = productLaw f (Syn.subst σ m) (Syn.subst σ N) (Syn.subst σ y) := by
  simp [productLaw, subst_val, subst_up_shift']

private theorem product_law_shift {f : ZB} {m N y : PTm n} (h : Γ ⊢[PRAAx] productLaw f m N y) :
    Γ.map Fm.shift ⊢[PRAAx] productLaw f (Syn.shift m) (Syn.shift N) (Syn.shift y) := by
  simpa only [Fm.shift, Syn.shift, subst_productLaw] using h.shift

private theorem product_law_at {f : ZB} {a b m N y : PTm n} (h : Γ ⊢[PRAAx] productLaw f m N y)
    (ha : Γ ⊢[PRAAx] dvd a m) (hb : Γ ⊢[PRAAx] dvd b N) :
    ZT.toZ Γ (f.val (a * b) y) = ZT.toZ Γ (f.val a y) * ZT.toZ Γ (f.val b y) := by
  unfold productLaw at h
  have atA := Prf.allE a h
  simp only [Fm.subst_all, Fm.subst_imp, Fm.subst_eq, ZT.subst_eq, ZT.subst_mul, subst_ap2, subst_up_shift',
    subst_val, PTm.subst_mul, ConciseIPRA.PTm.subst_zero, Syn.subst_inst_shift, Syn.subst_var,
    Syn.up_one, Syn.up_zero, Syn.inst_zero] at atA
  have atB := Prf.allE b atA
  simp only [Fm.subst_imp, Fm.subst_eq, ZT.subst_eq, ZT.subst_mul, subst_ap2, subst_val, PTm.subst_mul,
    ConciseIPRA.PTm.subst_zero, Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero] at atB
  simpa only [ZT.toZ_mul] using ZT.toZ_eq (.impE (.impE atB ha) hb)

private theorem weight_true (f g : ZB) {d M y : PTm n}
    (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hd : Γ ⊢[PRAAx] dvd d M) :
    ZT.toZ Γ ((weight f g).val d (pairT M y)) = ZT.toZ Γ (f.val d y) * ZT.toZ Γ (g.val (quo M d) y) := by
  have h (a b : PTm 2) := natEq (ConvolutionDivisorWeights.weight_true a b (y := y) hM hd)
  ipra_lc [weight, ZB.toZ_val, inst2_addBody] h f.pos g.pos + h f.neg g.neg - h f.pos g.neg - h f.neg g.pos

private theorem weight_false (f g : ZB) {d M y : PTm n} (h : Γ ⊢[PRAAx] neg (dvd d M)) :
    ZT.toZ Γ ((weight f g).val d (pairT M y)) = 0 := by
  have e (a b : PTm 2) := natEq (ConvolutionDivisorWeights.weight_false a b (y := y) h)
  ipra_lc [weight, ZB.toZ_val, inst2_addBody] e f.pos g.pos + e f.neg g.neg - e f.pos g.neg - e f.neg g.pos

private theorem weight_absorb (f g : ZB) (d M y : PTm n) :
    𝔞 (eqb (rem M d) zero) * ZT.toZ Γ ((weight f g).val d (pairT M y)) =
      ZT.toZ Γ ((weight f g).val d (pairT M y)) := by
  have h (a b : PTm 2) := natEq (ConvolutionDivisorWeights.weight_absorb (Γ := Γ) a b d M y)
  ipra_lc [weight, ZB.toZ_val, inst2_addBody] h f.pos g.pos + h f.neg g.neg - h f.pos g.neg - h f.neg g.pos

private theorem weight_product (f g : ZB) {a b m N y : PTm n}
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (ha : Γ ⊢[PRAAx] dvd a m) (hb : Γ ⊢[PRAAx] dvd b N)
    (hf : Γ ⊢[PRAAx] productLaw f m N y) (hg : Γ ⊢[PRAAx] productLaw g m N y) :
    ZT.toZ Γ ((weight f g).val (a * b) (pairT (m * N) y)) =
      ZT.toZ Γ ((weight f g).val a (pairT m y)) * ZT.toZ Γ ((weight f g).val b (pairT N y)) := by
  have es := quotient_product hm hN ha hb
  have ge : ZT.toZ Γ (g.val (quo (m * N) (a * b)) y) = ZT.toZ Γ (g.val (quo m a * quo N b) y) := by
    have h := Prf.andE₂ es
    simp only [ZB.toZ_val, natEq (congrInst2 g.pos h (.eqRefl y)), natEq (congrInst2 g.neg h (.eqRefl y))]
  rw [weight_true f g (pos_mul' hm hN) (Prf.andE₁ es), weight_true f g hm ha, weight_true f g hN hb, ge,
    product_law_at hf ha hb, product_law_at hg (complement_divisor hm ha) (complement_divisor hN hb)]
  ring

private def both (transform : PTm 2 → PTm 2) (w : ZB) : ZB := ⟨transform w.pos, transform w.neg⟩

private theorem left_val (w : ZB) (d m N Y : PTm n) :
    ZT.toZ Γ ((both lB w).val d (Xp m N Y)) = 𝔞 (eqb (rem (m * N) d) zero) * ZT.toZ Γ (w.val d Y) := by
  ipra_lc [both, ZB.toZ_val] natEq (lB_at w.pos d m N Y) - natEq (lB_at w.neg d m N Y)

private theorem inner_val (w : ZB) (a b m N Y : PTm n) :
    ZT.toZ Γ ((both riB w).val b (pairT a (Xp m N Y))) =
      𝔞 (eqb (rem N b) zero) * ZT.toZ Γ (w.val (a * b) Y) := by
  ipra_lc [both, ZB.toZ_val] natEq (riB_at w.pos b a m N Y) - natEq (riB_at w.neg b a m N Y)

private theorem outer_val (w : ZB) (a m N Y : PTm n) :
    ZT.toZ Γ ((both rB w).val a (Xp m N Y)) =
      𝔞 (eqb (rem m a) zero) * ZT.toZ Γ ((both riB w).sum (succ N) (pairT a (Xp m N Y))) := by
  ipra_lc [both, ZB.toZ_val, ZB.toZ_sum] natEq (rB_at w.pos a m N Y) - natEq (rB_at w.neg a m N Y)

private theorem right_point (f g : ZB) {a b m N y : PTm n}
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (ha : Γ ⊢[PRAAx] dvd a m)
    (hf : Γ ⊢[PRAAx] productLaw f m N y) (hg : Γ ⊢[PRAAx] productLaw g m N y) :
    Γ ⊢[PRAAx] ZT.eq ((both riB (weight f g)).val b (pairT a (Xp m N (pairT (m * N) y))))
      ((weight f g).val a (pairT m y) * (weight f g).val b (pairT N y)) := by
  refine .orE (eq_or_ne (rem N b) zero) ?_ ?_
  · have hb : (dvd b N :: Γ) ⊢[PRAAx] dvd b N := Prf.hyp0
    apply ZT.derive
    rw [inner_val, ZT.toZ_mul, weight_product f g hm.wk hN.wk ha.wk hb hf.wk hg.wk,
      natEq (eqb_of_eq hb), Q.mk_one, map_one, _root_.one_mul]
  · have hb : (neg (dvd b N) :: Γ) ⊢[PRAAx] neg (dvd b N) := Prf.hyp0
    apply ZT.derive
    rw [inner_val, ZT.toZ_mul, weight_false f g (y := y) hb,
      natEq (eqb_of_ne hb), Q.mk_zero, map_zero]
    ring

private theorem shift_val (w : ZB) (i x : PTm n) :
    (w.val i x).subst (fun j => var j.succ) = w.val (Syn.shift i) (Syn.shift x) :=
  subst_val _ _ _ _

private theorem shift_convolution (f g : ZB) (M y : PTm n) :
    (convolution f g M y).subst (fun j => var j.succ) = convolution f g (Syn.shift M) (Syn.shift y) := by
  simp [convolution, ZB.sum, ZT.subst, Syn.shift]

private theorem inner_sum (f g : ZB) {a m N y : PTm n}
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (ha : Γ ⊢[PRAAx] dvd a m)
    (hf : Γ ⊢[PRAAx] productLaw f m N y) (hg : Γ ⊢[PRAAx] productLaw g m N y) :
    ZT.toZ Γ ((both riB (weight f g)).sum (succ N) (pairT a (Xp m N (pairT (m * N) y)))) =
      ZT.toZ Γ ((weight f g).val a (pairT m y)) * ZT.toZ Γ (convolution f g N y) := by
  refine sum_scale _ _ (succ N) (pairT N y) (pairT a (Xp m N (pairT (m * N) y))) _ (.allI (.impI ?_))
  simp only [shift_val, shift_pairT, shift_product]
  exact right_point f g (pos_sh hm).wk (pos_sh hN).wk (ConvolutionDivisorWeights.dvd_shift ha).wk
    (product_law_shift hf).wk (product_law_shift hg).wk

private theorem outer_point (f g : ZB) {a m N y : PTm n}
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hf : Γ ⊢[PRAAx] productLaw f m N y) (hg : Γ ⊢[PRAAx] productLaw g m N y) :
    Γ ⊢[PRAAx] ZT.eq ((both rB (weight f g)).val a (Xp m N (pairT (m * N) y)))
      (convolution f g N y * (weight f g).val a (pairT m y)) := by
  refine .orE (eq_or_ne (rem m a) zero) ?_ ?_
  · have ha : (dvd a m :: Γ) ⊢[PRAAx] dvd a m := Prf.hyp0
    apply ZT.derive
    rw [outer_val, inner_sum f g hm.wk hN.wk ha hf.wk hg.wk,
      natEq (eqb_of_eq ha), Q.mk_one, map_one, _root_.one_mul, ZT.toZ_mul]
    exact _root_.mul_comm _ _
  · have ha : (neg (dvd a m) :: Γ) ⊢[PRAAx] neg (dvd a m) := Prf.hyp0
    apply ZT.derive
    rw [outer_val, ZT.toZ_mul, weight_false f g (y := y) ha,
      natEq (eqb_of_ne ha), Q.mk_zero, map_zero]
    ring

/-- The coprime product identity of the original signed convolution. -/
theorem convolution_product (f g : ZB) {m N y : PTm n}
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hc : Γ ⊢[PRAAx] gcd m N ≐ one)
    (hf : Γ ⊢[PRAAx] productLaw f m N y) (hg : Γ ⊢[PRAAx] productLaw g m N y) :
    Γ ⊢[PRAAx] ZT.eq (convolution f g (m * N) y) (convolution f g m y * convolution f g N y) := by
  let w := weight f g
  let Y := pairT (m * N) y
  have left : ZT.toZ Γ (convolution f g (m * N) y) =
      ZT.toZ Γ ((both lB w).sum (succ (m * N)) (Xp m N Y)) := by
    refine ZB.toZ_sum_congr w (both lB w) Y (Xp m N Y) (succ (m * N)) (.allI (.impI ?_))
    simp only [Y, shift_pairT, shift_product]
    exact ZT.derive ((left_val w (var 0) _ _ _).trans (weight_absorb f g (var 0) _ _)).symm
  have mid : ZT.toZ Γ ((both lB w).sum (succ (m * N)) (Xp m N Y)) =
      ZT.toZ Γ ((both rB w).sum (succ m) (Xp m N Y)) := by
    ipra_lc [both, ZB.toZ_sum] natEq (divisor_factor w.pos hm hN hc Y) -
      natEq (divisor_factor w.neg hm hN hc Y)
  have right : ZT.toZ Γ ((both rB w).sum (succ m) (Xp m N Y)) =
      ZT.toZ Γ (convolution f g N y) * ZT.toZ Γ (convolution f g m y) := by
    refine sum_scale _ _ (succ m) (pairT m y) (Xp m N Y) (convolution f g N y) (.allI (.impI ?_))
    simp only [Y, shift_pairT, shift_product, shift_convolution]
    exact outer_point f g (pos_sh hm).wk (pos_sh hN).wk (product_law_shift hf).wk (product_law_shift hg).wk
  exact ZT.derive (left.trans (mid.trans (right.trans (by rw [ZT.toZ_mul, _root_.mul_comm]))))

def rectangleFormula (f g : ZB) : Fm PTm 3 :=
  le one (var 0) ⟶ le one (var 1) ⟶ gcd (var 0) (var 1) ≐ one ⟶
    productLaw f (var 0) (var 1) (var 2) ⟶ productLaw g (var 0) (var 1) (var 2) ⟶
      ZT.eq (convolution f g (var 0 * var 1) (var 2))
        (convolution f g (var 0) (var 2) * convolution f g (var 1) (var 2))

theorem signed_convolution_product_closed (f g : ZB) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (rectangleFormula f g) := by
  refine closeUniv 3 (.impI (.impI (.impI (.impI (.impI ?_)))))
  exact convolution_product f g (pos_of_one_le hyp2.wk.wk) (pos_of_one_le hyp2.wk) hyp2 Prf.hyp1 Prf.hyp0

theorem convolution_at_one (f g : ZB) (y : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (convolution f g one y) (f.val one y * g.val one y) := by
  have value (a b c d : PTm 2) : Γ ⊢[PRAAx]
      ap2 (sumF (addBody (cvB a b) (cvB c d))) (succ one) (pairT one y) ≐
        inst2 a one y * inst2 b one y + inst2 c one y * inst2 d one y :=
    (sum_add _ _ _ _).eqTrans (congrAdd (conv_at_one a b y) (conv_at_one c d y))
  apply ZT.derive
  ipra_lc [convolution, weight, ZB.toZ_sum, ZB.toZ_val]
    natEq (value f.pos g.pos f.neg g.neg) - natEq (value f.pos g.neg f.neg g.pos)

end LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionSigned
