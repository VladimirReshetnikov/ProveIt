import IPRADerivations.AnalyticNumberTheory.ConvolutionSigned
import IPRADerivations.AnalyticNumberTheory.MobiusInversionReverse

/-!
# Finite Dirichlet convolution on integer-valued bodies

The remaining algebra laws of `el:convolution` transport the checked
natural-body identities through the four signed components. The body
representation of an iterated convolution reads back the original
`ConvolutionSigned.convolution` at every argument.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionSignedAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionSigned
  (weight convolution productLaw convolution_product convolution_at_one)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (cvF inst2_cvF conv_assoc)
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv inst2_cvB)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorFactor (pos_sh gcd_sh)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorSplit (pos_of_dvd)
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (subst_up_shift')
open LeanProofs.IPRA.AnalyticNumberTheory.HyperbolaSwap (conv_comm0)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversionReverse (conv_add_l conv_add_r conv_unit)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryInstances (epsB)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (coprime_dvd_left gcd_comm_one one_le_of_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

set_option hygiene false in
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-- The signed convolution as a body for subsequent convolutions. -/
def productBody (f g : ZB) : ZB :=
  ⟨addBody (cvF f.pos g.pos) (cvF f.neg g.neg), addBody (cvF f.pos g.neg) (cvF f.neg g.pos)⟩

def epsilon : ZB := ZB.ofNat epsB

theorem toZ_convolution (f g : ZB) (N y : PTm n) :
    ZT.toZ Γ (convolution f g N y) =
      𝔞 (conv f.pos g.pos N y) + 𝔞 (conv f.neg g.neg N y) -
        𝔞 (conv f.pos g.neg N y) - 𝔞 (conv f.neg g.pos N y) := by
  ipra_lc [convolution, weight, ZB.toZ_sum]
    natEq (sum_add (Γ := Γ) (cvB f.pos g.pos) (cvB f.neg g.neg) (succ N) (pairT N y)) -
      natEq (sum_add (Γ := Γ) (cvB f.pos g.neg) (cvB f.neg g.pos) (succ N) (pairT N y))

theorem body_value (f g : ZB) (N y : PTm n) :
    Γ ⊢[PRAAx] ZT.eq ((productBody f g).val N y) (convolution f g N y) := by
  apply ZT.derive
  rw [toZ_convolution]
  ipra_lc [ZB.toZ_val, productBody, inst2_addBody, inst2_cvF]

theorem convolution_comm (f g : ZB) (N y : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (convolution f g N y) (convolution g f N y) := by
  apply ZT.derive
  simp only [toZ_convolution]
  linear_combination natEq (conv_comm0 f.pos g.pos N y) + natEq (conv_comm0 f.neg g.neg N y) -
    natEq (conv_comm0 f.pos g.neg N y) - natEq (conv_comm0 f.neg g.pos N y)

theorem convolution_assoc (f g h : ZB) (N y : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (convolution (productBody f g) h N y) (convolution f (productBody g h) N y) := by
  have left (a b c d e : PTm 2) :
      𝔞 (conv (addBody (cvF a b) (cvF c d)) e N y) =
        𝔞 (conv a (cvF b e) N y) + 𝔞 (conv c (cvF d e) N y) := by
    rw [natEq (conv_add_l _ _ _ _ _), Q.mk_add, map_add,
      ← natEq (conv_assoc a b e N y), ← natEq (conv_assoc c d e N y)]
  have right (a b c d e : PTm 2) :
      𝔞 (conv a (addBody (cvF b c) (cvF d e)) N y) =
        𝔞 (conv a (cvF b c) N y) + 𝔞 (conv a (cvF d e) N y) := by
    rw [natEq (conv_add_r _ _ _ _ _), Q.mk_add, map_add]
  apply ZT.derive
  simp only [toZ_convolution, productBody, left, right]
  ring

private theorem zero_convolution (f : PTm 2) (N y : PTm n) :
    Γ ⊢[PRAAx] conv zero f N y ≐ zero := by
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  rw [inst2_cvB]
  have instZero (i x : PTm (n + 1)) : inst2 (zero : PTm 2) i x = zero := by simp [inst2]
  rw [instZero]
  ipra_ring

theorem convolution_unit (f : ZB) {N : PTm n} (hN : Γ ⊢[PRAAx] le one N) (y : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (convolution epsilon f N y) (f.val N y) := by
  apply ZT.derive
  ipra_lc [toZ_convolution, epsilon, ZB.ofNat, ZB.toZ_val]
    natEq (conv_unit f.pos hN y) - natEq (conv_unit f.neg hN y) +
      natEq (zero_convolution f.neg N y) - natEq (zero_convolution f.pos N y)

theorem convolution_unit_right (f : ZB) {N : PTm n} (hN : Γ ⊢[PRAAx] le one N) (y : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (convolution f epsilon N y) (f.val N y) :=
  ZT.derive ((ZT.toZ_eq (convolution_comm f epsilon N y)).trans (ZT.toZ_eq (convolution_unit f hN y)))

private theorem pos_add (f g : ZB) : (f + g).pos = addBody f.pos g.pos := rfl
private theorem neg_add (f g : ZB) : (f + g).neg = addBody f.neg g.neg := rfl

theorem convolution_add_left (f g h : ZB) (N y : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (convolution (f + g) h N y) (convolution f h N y + convolution g h N y) := by
  apply ZT.derive
  ipra_lc [ZT.toZ_add, toZ_convolution, pos_add, neg_add]
    natEq (conv_add_l f.pos g.pos h.pos N y) + natEq (conv_add_l f.neg g.neg h.neg N y) -
      natEq (conv_add_l f.pos g.pos h.neg N y) - natEq (conv_add_l f.neg g.neg h.pos N y)

theorem convolution_add_right (f g h : ZB) (N y : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (convolution f (g + h) N y) (convolution f g N y + convolution f h N y) := by
  apply ZT.derive
  ipra_lc [ZT.toZ_add, toZ_convolution, pos_add, neg_add]
    natEq (conv_add_r f.pos g.pos h.pos N y) + natEq (conv_add_r f.neg g.neg h.neg N y) -
      natEq (conv_add_r f.pos g.neg h.neg N y) - natEq (conv_add_r f.neg g.pos h.pos N y)

def algebraFormula (f g h : ZB) (N y : PTm n) : Fm PTm n :=
  ZT.eq (convolution f g N y) (convolution g f N y) ⋏
    (ZT.eq (convolution (productBody f g) h N y) (convolution f (productBody g h) N y) ⋏
      ((le one N ⟶ (ZT.eq (convolution epsilon f N y) (f.val N y) ⋏
        ZT.eq (convolution f epsilon N y) (f.val N y))) ⋏
      (ZT.eq (convolution (f + g) h N y) (convolution f h N y + convolution g h N y) ⋏
        ZT.eq (convolution f (g + h) N y) (convolution f g N y + convolution f h N y))))

theorem signed_convolution_algebra_closed (f g h : ZB) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (algebraFormula f g h (var 0) (var 1)) :=
  closeUniv 2 (.andI (convolution_comm f g _ _) (.andI (convolution_assoc f g h _ _)
    (.andI (.impI (.andI (convolution_unit f Prf.hyp0 _) (convolution_unit_right f Prf.hyp0 _)))
      (.andI (convolution_add_left f g h _ _) (convolution_add_right f g h _ _)))))

/-- A signed body's value at one and its product law on positive coprime inputs. -/
def multiplicative (f : ZB) (y : PTm n) : Fm PTm n :=
  ZT.eq (f.val one y) (ZT.natLit 1) ⋏ Fm.all (Fm.all (le one (var 1) ⟶ le one (var 0) ⟶
    gcd (var 1) (var 0) ≐ one ⟶ ZT.eq (f.val (var 1 * var 0) (Syn.shift (Syn.shift y)))
      (f.val (var 1) (Syn.shift (Syn.shift y)) * f.val (var 0) (Syn.shift (Syn.shift y)))))

private theorem subst_val {k : ℕ} (σ : Fin n → PTm k) (b : ZB) (i x : PTm n) :
    (b.val i x).subst σ = b.val (Syn.subst σ i) (Syn.subst σ x) := by
  simp only [ZB.val, ZT.subst, subst_inst2]

private theorem subst_multiplicative {k : ℕ} (σ : Fin n → PTm k) (f : ZB) (y : PTm n) :
    (multiplicative f y).subst σ = multiplicative f (Syn.subst σ y) := by
  simp only [multiplicative, Fm.subst_and, Fm.subst_all, Fm.subst_imp, Fm.subst_eq, ZT.subst_eq, ZT.subst_mul,
    ZT.subst_natLit, subst_le, subst_ex2, subst_up_shift', subst_val, PTm.subst_mul, Syn.subst_var,
    Syn.up_one, Syn.up_zero, Syn.shift_var, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
  rfl

private theorem multiplicative_shift {f : ZB} {y : PTm n} (h : Γ ⊢[PRAAx] multiplicative f y) :
    Γ.map Fm.shift ⊢[PRAAx] multiplicative f (Syn.shift y) := by
  simpa only [Fm.shift, Syn.shift, subst_multiplicative] using h.shift

private theorem multiplicative_at {f : ZB} {a b y : PTm n} (hf : Γ ⊢[PRAAx] multiplicative f y)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) (hc : Γ ⊢[PRAAx] gcd a b ≐ one) :
    Γ ⊢[PRAAx] ZT.eq (f.val (a * b) y) (f.val a y * f.val b y) := by
  have h := Prf.allE a (Prf.andE₂ hf)
  simp only [Fm.subst_all, Fm.subst_imp, Fm.subst_eq, ZT.subst_eq, ZT.subst_mul, subst_le, subst_ex2,
    subst_up_shift', subst_val, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
    Syn.subst_inst_shift, Syn.subst_var, Syn.up_one, Syn.up_zero, Syn.inst_zero] at h
  have h' := Prf.allE b h
  simp only [Fm.subst_imp, Fm.subst_eq, ZT.subst_eq, ZT.subst_mul, subst_le, subst_ex2, subst_val,
    PTm.subst_mul, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
    Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero] at h'
  exact .impE (.impE (.impE h' ha) hb) hc

private theorem on_divisor_rectangle {f : ZB} {m N y : PTm n} (hf : Γ ⊢[PRAAx] multiplicative f y)
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hc : Γ ⊢[PRAAx] gcd m N ≐ one) : Γ ⊢[PRAAx] productLaw f m N y := by
  unfold productLaw
  refine .allI (.allI (.impI (.impI ?_)))
  let a : PTm (n + 2) := var 1
  let b : PTm (n + 2) := var 0
  let m' := Syn.shift (Syn.shift m)
  let N' := Syn.shift (Syn.shift N)
  let Δ := dvd b N' :: dvd a m' :: (Γ.map Fm.shift).map Fm.shift
  have hm' : Δ ⊢[PRAAx] m' ≐ succ (pred m') := (pos_sh (pos_sh hm)).wk.wk
  have hN' : Δ ⊢[PRAAx] N' ≐ succ (pred N') := (pos_sh (pos_sh hN)).wk.wk
  have hc' : Δ ⊢[PRAAx] gcd m' N' ≐ one := (gcd_sh (gcd_sh hc)).wk.wk
  have ha : Δ ⊢[PRAAx] dvd a m' := Prf.hyp1
  have hb : Δ ⊢[PRAAx] dvd b N' := Prf.hyp0
  have pa := pos_of_dvd hm' ha
  have pb := pos_of_dvd hN' hb
  have hba := coprime_dvd_left pb hb (gcd_comm_one hN' (coprime_dvd_left pa ha hc'))
  exact multiplicative_at (multiplicative_shift (multiplicative_shift hf)).wk.wk
    (one_le_of_pos pa) (one_le_of_pos pb) (gcd_comm_one pa hba)

theorem convolution_multiplicative (f g : ZB) {y : PTm n}
    (hf : Γ ⊢[PRAAx] multiplicative f y) (hg : Γ ⊢[PRAAx] multiplicative g y) :
    Γ ⊢[PRAAx] multiplicative (productBody f g) y := by
  unfold multiplicative
  refine .andI ?_ (.allI (.allI (.impI (.impI (.impI ?_)))))
  · apply ZT.derive
    rw [ZT.toZ_eq (body_value f g one y), ZT.toZ_eq (convolution_at_one f g y), ZT.toZ_mul,
      ZT.toZ_eq (Prf.andE₁ hf), ZT.toZ_eq (Prf.andE₁ hg), ZT.toZ_natLit]
    ring
  · let m : PTm (n + 2) := var 1
    let N : PTm (n + 2) := var 0
    let y' := Syn.shift (Syn.shift y)
    let Δ := (gcd m N ≐ one) :: le one N :: le one m :: (Γ.map Fm.shift).map Fm.shift
    have hm : Δ ⊢[PRAAx] m ≐ succ (pred m) := pos_of_one_le hyp2
    have hN : Δ ⊢[PRAAx] N ≐ succ (pred N) := pos_of_one_le Prf.hyp1
    have hc : Δ ⊢[PRAAx] gcd m N ≐ one := Prf.hyp0
    have h := convolution_product f g hm hN hc
      (on_divisor_rectangle (multiplicative_shift (multiplicative_shift hf)).wk.wk.wk hm hN hc)
      (on_divisor_rectangle (multiplicative_shift (multiplicative_shift hg)).wk.wk.wk hm hN hc)
    apply ZT.derive
    rw [ZT.toZ_eq (body_value (Γ := Δ) f g (m * N) y'), ZT.toZ_mul, ZT.toZ_eq (body_value f g m y'),
      ZT.toZ_eq (body_value f g N y')]
    simpa only [ZT.toZ_mul] using ZT.toZ_eq h

def multiplicativityFormula (f g : ZB) : Fm PTm 1 :=
  multiplicative f (var 0) ⟶ multiplicative g (var 0) ⟶ multiplicative (productBody f g) (var 0)

theorem signed_convolution_multiplicative_closed (f g : ZB) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (multiplicativityFormula f g) :=
  closeUniv 1 (.impI (.impI (convolution_multiplicative f g Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionSignedAlgebra
