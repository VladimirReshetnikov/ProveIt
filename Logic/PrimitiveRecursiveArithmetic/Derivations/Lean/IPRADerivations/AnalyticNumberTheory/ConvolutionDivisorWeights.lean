import IPRADerivations.AnalyticNumberTheory.DivisorFactor
import IPRADerivations.AnalyticNumberTheory.DirichletLeibniz
import IPRADerivations.AnalyticNumberTheory.Fermat
import IPRADerivations.AnalyticNumberTheory.Totient
import IPRADerivations.Core.CertificateTactics
import IPRADerivations.Core.SubstCommand

/-!
# Original Dirichlet convolution weights on split divisors

The packet theorem `el:convolution` uses multiplicativity at the
bounded pairs of divisors of two coprime inputs. For those pairs the
quotient of the product by the split divisor is the product of the
two complementary quotients. The lemmas work with the original
`DirichletLeibniz.cvB` weights, including their divisor indicators.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionDivisorWeights

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB cv_at)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorSplit (pos_of_dvd)
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (subst_up_shift')
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
  (dvd_of_eq' eq_of_dvd' one_le_of_pos pos_of_eq_mul)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases)
open LeanProofs.IPRA.Signum (sg sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- Multiplicativity tested at all the pairs of divisors used by the
split sum, with the parameter of the body held fixed. -/
def productLaw (f : PTm 2) (m N y : PTm n) : Fm PTm n :=
  Fm.all (Fm.all (dvd (var 1) (Syn.shift (Syn.shift m)) ⟶ dvd (var 0) (Syn.shift (Syn.shift N)) ⟶
    inst2 f (var 1 * var 0) (Syn.shift (Syn.shift y)) ≐
      inst2 f (var 1) (Syn.shift (Syn.shift y)) * inst2 f (var 0) (Syn.shift (Syn.shift y))))

ipra_subst productLaw [subst_up_shift']

theorem product_law_shift {f : PTm 2} {m N y : PTm n} (h : Γ ⊢[PRAAx] productLaw f m N y) :
    Γ.map Fm.shift ⊢[PRAAx] productLaw f (Syn.shift m) (Syn.shift N) (Syn.shift y) := by
  simpa only [Fm.shift, Syn.shift, subst_productLaw] using h.shift

theorem product_law_at {f : PTm 2} {a b m N y : PTm n} (h : Γ ⊢[PRAAx] productLaw f m N y)
    (ha : Γ ⊢[PRAAx] dvd a m) (hb : Γ ⊢[PRAAx] dvd b N) :
    Γ ⊢[PRAAx] inst2 f (a * b) y ≐ inst2 f a y * inst2 f b y := by
  unfold productLaw at h
  have atA := Prf.allE a h
  simp only [Fm.subst_all, Fm.subst_imp, Fm.subst_eq, subst_ap2, subst_up_shift', subst_inst2,
    PTm.subst_mul, ConciseIPRA.PTm.subst_zero, Syn.subst_inst_shift, Syn.subst_var,
    Syn.up_one, Syn.up_zero, Syn.inst_zero] at atA
  have atB := Prf.allE b atA
  simp only [Fm.subst_imp, Fm.subst_eq, subst_ap2, subst_inst2, PTm.subst_mul,
    ConciseIPRA.PTm.subst_zero, Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero] at atB
  exact .impE (.impE atB ha) hb

theorem dvd_shift {d M : PTm n} (h : Γ ⊢[PRAAx] dvd d M) :
    Γ.map Fm.shift ⊢[PRAAx] dvd (Syn.shift d) (Syn.shift M) := by
  simpa only [dvd, Fm.shift, Syn.shift, Fm.subst_eq, subst_ap2, ConciseIPRA.PTm.subst_zero] using h.shift

theorem weight_true (f g : PTm 2) {d M y : PTm n}
    (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (h : Γ ⊢[PRAAx] dvd d M) :
    Γ ⊢[PRAAx] inst2 (cvB f g) d (pairT M y) ≐ inst2 f d y * inst2 g (quo M d) y := by
  have hs := (congrSg (pos_of_dvd hM h)).eqTrans (sg_succ _)
  refine (cv_at f g d M y).eqTrans ?_
  exact (congrMul ((congrMul hs (eqb_of_eq h)).eqTrans (one_mul _)) (.eqRefl _)).eqTrans (one_mul _)

theorem weight_false (f g : PTm 2) {d M y : PTm n} (h : Γ ⊢[PRAAx] neg (dvd d M)) :
    Γ ⊢[PRAAx] inst2 (cvB f g) d (pairT M y) ≐ zero := by
  have hm := (congrMul (.eqRefl (sg d)) (eqb_of_ne h)).eqTrans (mul_zero _)
  exact (cv_at f g d M y).eqTrans ((congrMul hm (.eqRefl _)).eqTrans (zero_mul _))

theorem weight_absorb (f g : PTm 2) (d M y : PTm n) :
    Γ ⊢[PRAAx] eqb (rem M d) zero * inst2 (cvB f g) d (pairT M y) ≐
      inst2 (cvB f g) d (pairT M y) := by
  refine .orE (eqb_cases (rem M d) zero) ?_ ?_
  · have hz : ((eqb (rem M d) zero ≐ zero) :: Γ) ⊢[PRAAx] eqb (rem M d) zero ≐ zero := Prf.hyp0
    have w := (cv_at (Γ := (eqb (rem M d) zero ≐ zero) :: Γ) f g d M y).eqTrans
      ((congrMul ((congrMul (.eqRefl (sg d)) hz).eqTrans (mul_zero _)) (.eqRefl _)).eqTrans (zero_mul _))
    exact ((congrMul hz (.eqRefl _)).eqTrans (zero_mul _)).eqTrans w.eqSymm
  · exact (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (one_mul _)

private theorem complementary_divisor {d M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] dvd d M) : Γ ⊢[PRAAx] dvd (quo M d) M := by
  have e := eq_of_dvd' (pos_of_dvd hM h) h
  exact dvd_of_eq' (pos_of_eq_mul hM e) (e.eqTrans (mul_comm _ _))

/-- Divisor product and its complementary quotient, for positive inputs. -/
theorem quotient_product {a b m N : PTm n}
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (ha : Γ ⊢[PRAAx] dvd a m) (hb : Γ ⊢[PRAAx] dvd b N) :
    Γ ⊢[PRAAx] dvd (a * b) (m * N) ⋏ (quo (m * N) (a * b) ≐ quo m a * quo N b) := by
  have pa := pos_of_dvd hm ha
  have pb := pos_of_dvd hN hb
  have pp := pos_mul' pa pb
  have prod : Γ ⊢[PRAAx] m * N ≐ (a * b) * (quo m a * quo N b) := by
    ipra_lc 𝔞 N * natEq (eq_of_dvd' pa ha) + 𝔞 (a * quo m a) * natEq (eq_of_dvd' pb hb)
  exact .andI (dvd_of_eq' pp prod)
    (quo_eq pp (prod.eqTrans (add_zero _).eqSymm) (one_le_of_pos pp))

/-- The weight on a split divisor is the product of the original weights
on its two factors under the actual divisor-table tests. -/
theorem weight_product (f g : PTm 2) {a b m N y : PTm n}
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (ha : Γ ⊢[PRAAx] dvd a m) (hb : Γ ⊢[PRAAx] dvd b N)
    (hf : Γ ⊢[PRAAx] productLaw f m N y) (hg : Γ ⊢[PRAAx] productLaw g m N y) :
    Γ ⊢[PRAAx] inst2 (cvB f g) (a * b) (pairT (m * N) y) ≐
      inst2 (cvB f g) a (pairT m y) * inst2 (cvB f g) b (pairT N y) := by
  have eqs := quotient_product hm hN ha hb
  have feq := product_law_at hf ha hb
  have geq := (congrInst2 g (Prf.andE₂ eqs) (.eqRefl _)).eqTrans
    (product_law_at hg (complementary_divisor hm ha) (complementary_divisor hN hb))
  refine (weight_true f g (pos_mul' hm hN) (Prf.andE₁ eqs)).eqTrans
    ((congrMul feq geq).eqTrans ?_)
  refine .eqTrans ?_ (congrMul (weight_true f g hm ha) (weight_true f g hN hb)).eqSymm
  ipra_ring

end LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionDivisorWeights
