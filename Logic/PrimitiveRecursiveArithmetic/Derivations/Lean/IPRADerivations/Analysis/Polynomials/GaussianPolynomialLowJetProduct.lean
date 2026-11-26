import IPRADerivations.Analysis.Polynomials.GaussianRationalLowCoefficientConvolution
import IPRADerivations.Foundations.BoundedSyntaxInduction

/-!
# Low coefficient products with different stored degrees

Two actual buffers may have different numerical degrees while agreeing
at every low exponent. Original finite Cauchy sums then show that their
actual products agree at every low exponent too. Every original degree
guard is retained; both input buffers may otherwise be arbitrary raw
codes. The finite bounded syntax for this comparison is exposed for
later genuine object-theory induction on powers.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialLowJetProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalPolynomialProduct (product)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside cauchySum termBody data term_at)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def jetEqual (P N Q M H : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (Syn.shift H)) ⟶
    exponentCoefficient (Syn.shift P) (Syn.shift N) (var 0) ≐
      exponentCoefficient (Syn.shift Q) (Syn.shift M) (var 0))
@[simp] theorem subst_jetEqual {m : ℕ} (σ : Fin n → PTm m) (P N Q M H : PTm n) :
    (jetEqual P N Q M H).subst σ = jetEqual (Syn.subst σ P) (Syn.subst σ N)
      (Syn.subst σ Q) (Syn.subst σ M) (Syn.subst σ H) := by simp [jetEqual,Syn.subst_shift,Syn.shift_subst]
def jetSyntax (P N Q M H : PTm n) : BFm n := .all (succ H) (.eq
  (exponentCoefficient (Syn.shift P) (Syn.shift N) (var 0))
    (exponentCoefficient (Syn.shift Q) (Syn.shift M) (var 0)))
theorem jet_formula (P N Q M H : PTm n) : formula (jetSyntax P N Q M H) = jetEqual P N Q M H := by
  simp [jetSyntax,jetEqual,formula]

theorem jet_at (P N Q M H e : PTm n) (h : Γ ⊢[PRAAx] jetEqual P N Q M H)
    (he : Γ ⊢[PRAAx] le e H) : Γ ⊢[PRAAx]
    exponentCoefficient P N e ≐ exponentCoefficient Q M e := by
  have gate : Γ ⊢[PRAAx] lt e (succ H) ⟶ exponentCoefficient P N e ≐ exponentCoefficient Q M e := by
    simpa only [jetEqual,Fm.subst_imp,Fm.subst_eq,subst_lt,PTm.subst_succ,
      GaussianRationalLowCoefficientConvolution.subst_exponentCoefficient,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE e
  exact Prf.impE gate ((succ_monus_succ _ _).eqTrans he)

theorem product_reader (P N Q M P' N' Q' M' H e : PTm n)
    (hP : Γ ⊢[PRAAx] jetEqual P N P' N' H) (hQ : Γ ⊢[PRAAx] jetEqual Q M Q' M' H)
    (he : Γ ⊢[PRAAx] le e H) (hN : Γ ⊢[PRAAx] le e N) (hM : Γ ⊢[PRAAx] le e M)
    (hN' : Γ ⊢[PRAAx] le e N') (hM' : Γ ⊢[PRAAx] le e M') : Γ ⊢[PRAAx]
    exponentCoefficient (product P Q N M) (N+M) e ≐ exponentCoefficient (product P' Q' N' M') (N'+M') e := by
  have hp : Γ.map Fm.shift ⊢[PRAAx] jetEqual (Syn.shift P) (Syn.shift N) (Syn.shift P') (Syn.shift N') (Syn.shift H) := by
    simpa only [Fm.shift,subst_jetEqual,Syn.shift] using hP.shift
  have hq : Γ.map Fm.shift ⊢[PRAAx] jetEqual (Syn.shift Q) (Syn.shift M) (Syn.shift Q') (Syn.shift M') (Syn.shift H) := by
    simpa only [Fm.shift,subst_jetEqual,Syn.shift] using hQ.shift
  have eh : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift H) := by simpa [Fm.shift,Syn.shift] using he.shift
  have en : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have em : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hM.shift
  have en' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift N') := by simpa [Fm.shift,Syn.shift] using hN'.shift
  have em' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift M') := by simpa [Fm.shift,Syn.shift] using hM'.shift
  have sums : Γ ⊢[PRAAx] cauchySum P Q N M e ≐ cauchySum P' Q' N' M' e := by
    refine GaussianRationalFiniteSum.sum_congr_bounded termBody termBody (succ e) (data P Q N M e) (data P' Q' N' M' e)
      (.allI (.impI ?_))
    let Δ := lt (var 0) (succ (Syn.shift e)) :: Γ.map Fm.shift
    have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift e) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    have hj : Δ ⊢[PRAAx] le (monus (Syn.shift e) (var 0)) (Syn.shift e) :=
      GaussianRationalMonicReconstruction.monus_le_left _ _
    have left : Δ ⊢[PRAAx] entry (Syn.shift P) (monus (Syn.shift N) (var 0)) ≐
        entry (Syn.shift P') (monus (Syn.shift N') (var 0)) :=
      (exponent_inside _ _ _ (le_trans hi en.wk)).eqSymm.eqTrans
        ((jet_at _ _ _ _ _ _ hp.wk (le_trans hi eh.wk)).eqTrans (exponent_inside _ _ _ (le_trans hi en'.wk)))
    have right : Δ ⊢[PRAAx] entry (Syn.shift Q) (monus (Syn.shift M) (monus (Syn.shift e) (var 0))) ≐
        entry (Syn.shift Q') (monus (Syn.shift M') (monus (Syn.shift e) (var 0))) :=
      (exponent_inside _ _ _ (le_trans hj em.wk)).eqSymm.eqTrans
        ((jet_at _ _ _ _ _ _ hq.wk (le_trans hj eh.wk)).eqTrans (exponent_inside _ _ _ (le_trans hj em'.wk)))
    simpa only [Δ,Syn.shift,PTm.subst_succ,GaussianRationalLowCoefficientConvolution.subst_data] using
      (term_at (Γ := Δ) (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M) (Syn.shift e) (var 0)).eqTrans
        ((qmul_congr left right).eqTrans
          (term_at (Syn.shift P') (Syn.shift Q') (Syn.shift N') (Syn.shift M') (Syn.shift e) (var 0)).eqSymm)
  exact (GaussianRationalLowCoefficientConvolution.product_exponent P Q N M e hN hM).eqTrans
    (sums.eqTrans (GaussianRationalLowCoefficientConvolution.product_exponent P' Q' N' M' e hN' hM').eqSymm)

theorem product_jet (P N Q M P' N' Q' M' H : PTm n)
    (hP : Γ ⊢[PRAAx] jetEqual P N P' N' H) (hQ : Γ ⊢[PRAAx] jetEqual Q M Q' M' H)
    (hN : Γ ⊢[PRAAx] le H N) (hM : Γ ⊢[PRAAx] le H M)
    (hN' : Γ ⊢[PRAAx] le H N') (hM' : Γ ⊢[PRAAx] le H M') : Γ ⊢[PRAAx]
    jetEqual (product P Q N M) (N+M) (product P' Q' N' M') (N'+M') H := by
  have hp : Γ.map Fm.shift ⊢[PRAAx] jetEqual (Syn.shift P) (Syn.shift N) (Syn.shift P') (Syn.shift N') (Syn.shift H) := by
    simpa only [Fm.shift,subst_jetEqual,Syn.shift] using hP.shift
  have hq : Γ.map Fm.shift ⊢[PRAAx] jetEqual (Syn.shift Q) (Syn.shift M) (Syn.shift Q') (Syn.shift M') (Syn.shift H) := by
    simpa only [Fm.shift,subst_jetEqual,Syn.shift] using hQ.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift H) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have hm : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift H) (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hM.shift
  have hn' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift H) (Syn.shift N') := by simpa [Fm.shift,Syn.shift] using hN'.shift
  have hm' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift H) (Syn.shift M') := by simpa [Fm.shift,Syn.shift] using hM'.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift H)) :: Γ.map Fm.shift
  have he : Δ ⊢[PRAAx] le (var 0) (Syn.shift H) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [jetEqual,Syn.shift,PTm.subst_add,GaussianRationalPolynomialProduct.subst_product] using
    product_reader (Syn.shift P) (Syn.shift N) (Syn.shift Q) (Syn.shift M)
      (Syn.shift P') (Syn.shift N') (Syn.shift Q') (Syn.shift M') (Syn.shift H) (var 0)
      hp.wk hq.wk he (le_trans he hn.wk) (le_trans he hm.wk) (le_trans he hn'.wk) (le_trans he hm'.wk)

theorem actual_product_low_jet_different_degrees_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (jetEqual (var 0) (var 1) (var 4) (var 5) (var 8) ⟶ jetEqual (var 2) (var 3) (var 6) (var 7) (var 8) ⟶
      le (var 8) (var 1) ⟶ le (var 8) (var 3) ⟶ le (var 8) (var 5) ⟶ le (var 8) (var 7) ⟶
      jetEqual (product (var 0) (var 2) (var 1) (var 3)) (var 1+var 3)
        (product (var 4) (var 6) (var 5) (var 7)) (var 5+var 7) (var 8)) :=
  closeUniv 9 (.impI (.impI (.impI (.impI (.impI (.impI
    (product_jet _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
      Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.GaussianPolynomialLowJetProduct
