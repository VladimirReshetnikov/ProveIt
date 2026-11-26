import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalFiniteProduct
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalPowerAlgebra

/-!
# Products with a common base and numerical exponents

The existing Gaussian-rational product of terms `a * b^(f(i,x))`
equals the product of `a` to the number of factors and `b` to their
actual exponent sum. Only the exponent body is fixed syntax. The
bases, prefix length and parameters are numerical, including zero.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPowerProduct

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteProduct (qprod)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qmul)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power powerF power_zero power_succ)
open LeanProofs.IPRA.Analysis.GaussianRationalPowerAlgebra (power_add qmul_shuffle)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (a b x : PTm n) : PTm n := pairT a (pairT b x)

def factorBody (f : PTm 2) : PTm 2 :=
  qmul (fstT (var 1)) (power (fstT (sndT (var 1))) (inst2 f (var 0) (sndT (sndT (var 1)))))

theorem factor_at (f : PTm 2) (a b x i : PTm n) :
    Γ ⊢[PRAAx] inst2 (factorBody f) i (data a b x) ≐ qmul a (power b (inst2 f i x)) := by
  have tail := snd_pair (Γ := Γ) a (pairT b x)
  have base := (congrFst tail).eqTrans (fst_pair b x)
  have params := (congrSnd tail).eqTrans (snd_pair b x)
  have readExponent : Syn.subst ![i,data a b x] (Syn.subst ![var 0,sndT (sndT (var 1))] f) =
      inst2 f i (sndT (sndT (data a b x))) := by
    simp only [inst2,Syn.subst_subst]
    congr 1
    funext k
    fin_cases k <;> simp
  simp only [inst2,factorBody,GaussianRationalHorner.subst_qmul,GaussianRationalReciprocal.subst_power,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,readExponent]
  exact qmul_congr (fst_pair _ _) (congrAp2 powerF (congrInst2 f (.eqRefl _) params) base)

def productLaw (f : PTm 2) (a b x j : PTm n) : Fm PTm n :=
  qprod (factorBody f) j (data a b x) ≐ qmul (power a j) (power b (ap2 (sumF f) j x))

ipra_subst productLaw [data]

theorem law_zero (f : PTm 2) (a b x : PTm n) : Γ ⊢[PRAAx] productLaw f a b x zero := by
  have exponentZero := (congrAp2 powerF (sum_zero (Γ := Γ) f x) (.eqRefl b)).eqTrans (power_zero b)
  have right := (qmul_congr (power_zero a) exponentZero).eqTrans
    (GaussianReciprocalHorner.qmul_one_right qone qone_canonical)
  exact (GaussianRationalFiniteProduct.product_zero _ _).eqTrans right.eqSymm

theorem law_succ (f : PTm 2) (a b x j : PTm n) (h : Γ ⊢[PRAAx] productLaw f a b x j) :
    Γ ⊢[PRAAx] productLaw f a b x (succ j) := by
  let total := ap2 (sumF f) j x
  let exponent := inst2 f j x
  have nextPower := (congrAp2 powerF (sum_succ (Γ := Γ) f j x) (.eqRefl b)).eqTrans (power_add b total exponent)
  exact (GaussianRationalFiniteProduct.product_succ _ _ _).eqTrans
    ((qmul_congr h (factor_at _ _ _ _ _)).eqTrans
      ((qmul_shuffle (power a j) (power b total) a (power b exponent)).eqTrans
        (qmul_congr (power_succ a j).eqSymm nextPower.eqSymm)))

theorem actual_power_product (f : PTm 2) (a b x j : PTm n) : Γ ⊢[PRAAx] productLaw f a b x j := by
  have all : Γ ⊢[PRAAx] .all (productLaw f (Syn.shift a) (Syn.shift b) (Syn.shift x) (var 0)) := by
    ipra_qfind [subst_productLaw]
    · exact law_zero f a b x
    · exact law_succ f _ _ _ _ Prf.hyp0
  simpa only [subst_productLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem actual_power_product_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (productLaw f (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (actual_power_product f _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalPowerProduct
