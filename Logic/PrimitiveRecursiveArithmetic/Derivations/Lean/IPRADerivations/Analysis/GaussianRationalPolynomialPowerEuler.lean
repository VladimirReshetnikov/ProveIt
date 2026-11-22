import IPRADerivations.Analysis.GaussianRationalEulerCoefficients
import IPRADerivations.Analysis.GaussianRationalGridCoefficientEquality
import IPRADerivations.Analysis.GaussianRationalPolynomialExponentialStability
import IPRADerivations.Foundations.BoundedSyntaxInduction

/-!
# Actual Euler identity for the original finite polynomial powers

The target is constructed from the SAME capped power sequence and actual
Euler coefficient buffer. Numeric coefficient algebra, including genuine
finite-grid reconstruction of the actual product algebra, supports the
power induction, for the explicit low exponent range e<=N. No polynomial ring, derivative, or desired power law is
an input. The positive power index and all degree/query data are internal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPolynomialPowerEuler

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qmul evaluate)
open GaussianRationalSyntheticDivision (qmul_congr canonicalCoefficients)
open GaussianRationalPolynomialProduct (product product_length product_canonical product_evaluation)
open GaussianRationalCoefficientScaling (scaled scaled_length evaluation_linearity)
open GaussianRationalPolynomialPowers (powerPrefix prefix_length prefix_canonical)
open GaussianRationalEulerCoefficients (euler euler_length euler_canonical)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient)
open GaussianRationalNaturalScale (naturalPoint)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem shift_length (C N : PTm n) (h : Γ ⊢[PRAAx] length C ≐ succ N) :
    Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
  simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using h.shift

theorem product_associative_value (P Q R N M L z : PTm n)
    (hP : Γ ⊢[PRAAx] length P ≐ succ N) (hQ : Γ ⊢[PRAAx] length Q ≐ succ M)
    (hR : Γ ⊢[PRAAx] length R ≐ succ L) : Γ ⊢[PRAAx]
    evaluate (product (product P Q N M) R (N+M) L) z ≐
      evaluate (product P (product Q R M L) N (M+L)) z := by
  have hl : Γ ⊢[PRAAx] evaluate (product (product P Q N M) R (N+M) L) z ≐
      qmul (qmul (evaluate P z) (evaluate Q z)) (evaluate R z) :=
    (product_evaluation _ _ _ _ z (product_length P Q N M) hR).eqTrans
      (qmul_congr (product_evaluation P Q N M z hP hQ) (.eqRefl _))
  have hr : Γ ⊢[PRAAx] evaluate (product P (product Q R M L) N (M+L)) z ≐
      qmul (evaluate P z) (qmul (evaluate Q z) (evaluate R z)) :=
    (product_evaluation _ _ _ _ z hP (product_length Q R M L)).eqTrans
      (qmul_congr (.eqRefl _) (product_evaluation Q R M L z hQ hR))
  exact hl.eqTrans ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans hr.eqSymm)

theorem product_associative_coefficient (P Q R N M L i : PTm n)
    (hP : Γ ⊢[PRAAx] length P ≐ succ N) (hQ : Γ ⊢[PRAAx] length Q ≐ succ M)
    (hR : Γ ⊢[PRAAx] length R ≐ succ L) (hi : Γ ⊢[PRAAx] le i ((N+M)+L)) : Γ ⊢[PRAAx]
    entry (product (product P Q N M) R (N+M) L) i ≐
      entry (product P (product Q R M L) N (M+L)) i := by
  have hp := shift_length P N hP
  have hq := shift_length Q M hQ
  have hr := shift_length R L hR
  have hg : Γ ⊢[PRAAx] GaussianRationalGridCoefficientEquality.gridEqual
      (product (product P Q N M) R (N+M) L) (product P (product Q R M L) N (M+L)) ((N+M)+L) := by
    refine .allI (.impI ?_)
    let Δ := le (var 0) (Syn.shift ((N+M)+L)) :: Γ.map Fm.shift
    simpa only [Δ,Syn.shift,GaussianRationalPolynomialProduct.subst_product,PTm.subst_add] using
      product_associative_value (Syn.shift P) (Syn.shift Q) (Syn.shift R) (Syn.shift N) (Syn.shift M) (Syn.shift L)
        (GaussianRationalFiniteGridIdentity.gridPoint (var 0)) hp.wk hq.wk hr.wk
  exact GaussianRationalGridCoefficientEquality.coefficient_equal _ _ _ i
    (product_length _ _ _ _) ((product_length _ _ _ _).eqTrans (congrSucc (by ipra_ring)))
    (product_canonical _ _ _ _) (product_canonical _ _ _ _) hg hi

theorem product_commutative_value (P Q N M z : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) : Γ ⊢[PRAAx]
    evaluate (product P Q N M) z ≐ evaluate (product Q P M N) z :=
  (product_evaluation P Q N M z hP hQ).eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (product_evaluation Q P M N z hQ hP).eqSymm)
theorem product_commutative_coefficient (P Q N M i : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) (hi : Γ ⊢[PRAAx] le i (N+M)) : Γ ⊢[PRAAx]
    entry (product P Q N M) i ≐ entry (product Q P M N) i := by
  have hp := shift_length P N hP
  have hq := shift_length Q M hQ
  have hg : Γ ⊢[PRAAx] GaussianRationalGridCoefficientEquality.gridEqual
      (product P Q N M) (product Q P M N) (N+M) := by
    refine .allI (.impI ?_)
    let Δ := le (var 0) (Syn.shift (N+M)) :: Γ.map Fm.shift
    simpa only [Δ,Syn.shift,GaussianRationalPolynomialProduct.subst_product] using
      product_commutative_value (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M)
        (GaussianRationalFiniteGridIdentity.gridPoint (var 0)) hp.wk hq.wk
  exact GaussianRationalGridCoefficientEquality.coefficient_equal _ _ _ i
    (product_length P Q N M) ((product_length Q P M N).eqTrans (congrSucc (add_comm _ _)))
    (product_canonical _ _ _ _) (product_canonical _ _ _ _) hg hi

theorem scaled_left_value (P Q N M a z : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) : Γ ⊢[PRAAx]
    evaluate (product (scaled P a) Q N M) z ≐ evaluate (scaled (product P Q N M) a) z := by
  have hl : Γ ⊢[PRAAx] evaluate (product (scaled P a) Q N M) z ≐
      qmul (qmul a (evaluate P z)) (evaluate Q z) :=
    (product_evaluation _ _ _ _ z ((scaled_length P a).eqTrans hP) hQ).eqTrans
      (qmul_congr (evaluation_linearity P a z) (.eqRefl _))
  have hr : Γ ⊢[PRAAx] evaluate (scaled (product P Q N M) a) z ≐
      qmul a (qmul (evaluate P z) (evaluate Q z)) :=
    (evaluation_linearity _ a z).eqTrans (qmul_congr (.eqRefl _) (product_evaluation P Q N M z hP hQ))
  exact hl.eqTrans ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans hr.eqSymm)
theorem scaled_left_coefficient (P Q N M a i : PTm n) (hP : Γ ⊢[PRAAx] length P ≐ succ N)
    (hQ : Γ ⊢[PRAAx] length Q ≐ succ M) (hi : Γ ⊢[PRAAx] le i (N+M)) : Γ ⊢[PRAAx]
    entry (product (scaled P a) Q N M) i ≐ entry (scaled (product P Q N M) a) i := by
  have hp := shift_length P N hP
  have hq := shift_length Q M hQ
  have hg : Γ ⊢[PRAAx] GaussianRationalGridCoefficientEquality.gridEqual
      (product (scaled P a) Q N M) (scaled (product P Q N M) a) (N+M) := by
    refine .allI (.impI ?_)
    let Δ := le (var 0) (Syn.shift (N+M)) :: Γ.map Fm.shift
    simpa only [Δ,Syn.shift,GaussianRationalPolynomialProduct.subst_product,GaussianRationalCoefficientScaling.subst_scaled] using
      scaled_left_value (Syn.shift P) (Syn.shift Q) (Syn.shift N) (Syn.shift M) (Syn.shift a)
        (GaussianRationalFiniteGridIdentity.gridPoint (var 0)) hp.wk hq.wk
  exact GaussianRationalGridCoefficientEquality.coefficient_equal _ _ _ i
    (product_length _ _ _ _) ((scaled_length _ _).eqTrans (product_length _ _ _ _))
    (product_canonical _ _ _ _) (GaussianPolynomialDeterminantTerms.scaled_canonical _ _) hg hi

/-- The r-th target is the Euler derivative of the positive power r+1.
Its original predecessor power is stored explicitly, avoiding subtraction
in the producer or a false zero-power width assertion. -/
def powerEuler (C N K r : PTm n) : PTm n := scaled
  (product (euler C N) (powerPrefix C N K r) N (r*N)) (naturalPoint (succ r))
@[simp] theorem subst_powerEuler {l : ℕ} (σ : Fin n → PTm l) (C N K r : PTm n) :
    Syn.subst σ (powerEuler C N K r) = powerEuler (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ r) := by
  simp [powerEuler]
theorem power_euler_length (C N K r : PTm n) : Γ ⊢[PRAAx]
    length (powerEuler C N K r) ≐ succ (succ r*N) :=
  (scaled_length _ _).eqTrans ((product_length _ _ _ _).eqTrans (congrSucc (by ipra_ring)))

theorem euler_congr {C D N M : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hN : Γ ⊢[PRAAx] N ≐ M) : Γ ⊢[PRAAx]
    euler C N ≐ euler D M := by
  simpa only [GaussianRationalEulerCoefficients.subst_euler,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using Prf.eqCongr (Γ := Γ) (euler (var 0) (var 1) : PTm 2)
      (σ := ![C,N]) (σ' := ![D,M]) (fun i => by fin_cases i; exact hC; exact hN)
theorem scaled_congr {P Q a b : PTm n} (hP : Γ ⊢[PRAAx] P ≐ Q) (ha : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx]
    scaled P a ≐ scaled Q b := by
  simpa only [GaussianRationalCoefficientScaling.subst_scaled,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using Prf.eqCongr (Γ := Γ) (scaled (var 0) (var 1) : PTm 2)
      (σ := ![P,a]) (σ' := ![Q,b]) (fun i => by fin_cases i; exact hP; exact ha)

theorem canonical_at (C N i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (entry C i) :=
  GaussianRationalSyntheticDivision.canonical_coefficient_at C i hCan
    (lt_congr (.eqRefl _) hC.eqSymm ((succ_monus_succ _ _).eqTrans hi))

theorem unit_first_coefficient (C N i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (product (GaussianRationalMonicReduction.singleton GaussianRationalSyntheticDivision.qone) C zero N) i ≐ entry C i := by
  have hc := canonical_at C N i hC hCan hi
  have ht : Γ ⊢[PRAAx] GaussianRationalPolynomialProduct.contribution
      (GaussianRationalMonicReduction.singleton GaussianRationalSyntheticDivision.qone) C N i zero ≐ entry C i :=
    (GaussianRationalPolynomialProduct.contribution_inside _ _ _ _ _ (zero_le i)).eqTrans
      ((qmul_congr (GaussianRationalMonicReduction.singleton_lookup _)
        ((GaussianRationalLinearProduct.padded_inside _ _ _
          (lt_congr (monus_zero i).eqSymm (.eqRefl _) ((succ_monus_succ _ _).eqTrans hi))).eqTrans
            (entry_congr (.eqRefl _) (monus_zero i)))).eqTrans
        ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianReciprocalHorner.qmul_one_right _ hc)))
  have hs : Γ ⊢[PRAAx] GaussianRationalPolynomialProduct.coefficient
      (GaussianRationalMonicReduction.singleton GaussianRationalSyntheticDivision.qone) C N one i ≐ entry C i :=
    (GaussianRationalPolynomialProduct.coefficient_succ _ _ _ zero i).eqTrans
      ((GaussianRationalSyntheticDivision.qadd_congr (GaussianRationalPolynomialProduct.coefficient_zero _ _ _ _) ht).eqTrans
        (GaussianRationalSyntheticDivision.qzero_add _ hc))
  exact (GaussianRationalPolynomialProduct.product_lookup _ _ zero N i
    (le_congr (.eqRefl _) (zero_add N).eqSymm hi)).eqTrans hs

theorem unit_right_coefficient (C N i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (product C (GaussianRationalMonicReduction.singleton GaussianRationalSyntheticDivision.qone) N zero) i ≐ entry C i :=
  (product_commutative_coefficient _ _ N zero i hC (GaussianRationalMonicReduction.singleton_length _)
    (le_congr (.eqRefl _) (add_zero N).eqSymm hi)).eqTrans (unit_first_coefficient C N i hC hCan hi)

theorem scaled_unit_coefficient (C N i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (scaled C (naturalPoint one)) i ≐ entry C i :=
  (GaussianRationalCoefficientScaling.scaled_lookup C _ i
    (lt_congr (.eqRefl _) hC.eqSymm ((succ_monus_succ _ _).eqTrans hi))).eqTrans
      ((GaussianRationalNaturalScale.natScale_as_product one _).eqSymm.eqTrans
        (GaussianRationalNaturalScale.natScale_one_canonical _ (canonical_at C N i hC hCan hi)))

theorem prefix_one_coefficient (C N K i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hK : Γ ⊢[PRAAx] lt zero K)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] entry (powerPrefix C N K one) i ≐ entry C i := by
  have hCode : Γ ⊢[PRAAx] powerPrefix C N K one ≐
      product (GaussianRationalMonicReduction.singleton GaussianRationalSyntheticDivision.qone) C zero N :=
    (GaussianRationalPolynomialPowers.prefix_succ C N K zero hK).eqTrans
      (GaussianPolynomialDeterminantTerms.product_congr (GaussianRationalPolynomialPowers.prefix_zero C N K)
        (.eqRefl _) (zero_mul N) (.eqRefl _))
  exact (entry_congr hCode (.eqRefl _)).eqTrans (unit_first_coefficient C N i hC hCan hi)

theorem base_euler_coefficient (C N K e : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hK : Γ ⊢[PRAAx] lt zero K)
    (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    exponentCoefficient (euler (powerPrefix C N K one) (one*N)) (one*N) e ≐
      exponentCoefficient (powerEuler C N K zero) (one*N) e := by
  have hl : Γ ⊢[PRAAx] exponentCoefficient (euler (powerPrefix C N K one) (one*N)) (one*N) e ≐
      GaussianRationalNaturalScale.natScale e (entry C (monus N e)) :=
    (GaussianRationalPolynomialExponentialStability.exponent_congr
      (euler_congr (.eqRefl _) (one_mul N)) (one_mul N) (.eqRefl _)).eqTrans
      ((GaussianRationalEulerCoefficients.euler_exponent _ N e he).eqTrans
        (GaussianRationalNaturalScale.natScale_congr (.eqRefl _)
          ((GaussianRationalLowCoefficientConvolution.exponent_inside _ N e he).eqTrans
            (prefix_one_coefficient C N K _ hC hCan hK (GaussianRationalMonicReconstruction.monus_le_left _ _)))))
  let U := GaussianRationalMonicReduction.singleton (GaussianRationalSyntheticDivision.qone : PTm n)
  have hCode : Γ ⊢[PRAAx] powerEuler C N K zero ≐ scaled (product (euler C N) U N zero) (naturalPoint one) :=
    scaled_congr (GaussianPolynomialDeterminantTerms.product_congr (.eqRefl _)
      (GaussianRationalPolynomialPowers.prefix_zero C N K) (.eqRefl _) (zero_mul N)) (.eqRefl _)
  have hLen : Γ ⊢[PRAAx] length (product (euler C N) U N zero) ≐ succ N :=
    (product_length _ _ _ _).eqTrans (congrSucc (add_zero N))
  have hr : Γ ⊢[PRAAx] exponentCoefficient (powerEuler C N K zero) (one*N) e ≐
      GaussianRationalNaturalScale.natScale e (entry C (monus N e)) :=
    (GaussianRationalPolynomialExponentialStability.exponent_congr hCode (one_mul N) (.eqRefl _)).eqTrans
      ((GaussianRationalLowCoefficientConvolution.exponent_inside _ N e he).eqTrans
        ((scaled_unit_coefficient _ N _ hLen (product_canonical _ _ _ _) (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
          ((unit_right_coefficient (euler C N) N _ (euler_length C N) (euler_canonical C N)
            (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
              (GaussianRationalEulerCoefficients.euler_entry_exponent C N e he))))
  exact hl.eqTrans hr.eqSymm

def lowEqual (P Q D H : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (Syn.shift H)) ⟶
    exponentCoefficient (Syn.shift P) (Syn.shift D) (var 0) ≐ exponentCoefficient (Syn.shift Q) (Syn.shift D) (var 0))
@[simp] theorem subst_lowEqual {l : ℕ} (σ : Fin n → PTm l) (P Q D H : PTm n) :
    (lowEqual P Q D H).subst σ = lowEqual (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ D) (Syn.subst σ H) := by
  simp [lowEqual,Syn.subst_shift,Syn.shift_subst]
theorem low_equal_at (P Q D H e : PTm n) (h : Γ ⊢[PRAAx] lowEqual P Q D H)
    (he : Γ ⊢[PRAAx] le e H) : Γ ⊢[PRAAx] exponentCoefficient P D e ≐ exponentCoefficient Q D e := by
  have gate : Γ ⊢[PRAAx] lt e (succ H) ⟶ exponentCoefficient P D e ≐ exponentCoefficient Q D e := by
    simpa only [lowEqual,Fm.subst_imp,Fm.subst_eq,subst_lt,ConciseIPRA.PTm.subst_succ,
      GaussianRationalLowCoefficientConvolution.subst_exponentCoefficient,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE e
  exact .impE gate ((succ_monus_succ _ _).eqTrans he)

theorem low_product_left (P Q R D M H e : PTm n) (h : Γ ⊢[PRAAx] lowEqual P Q D H)
    (he : Γ ⊢[PRAAx] le e H) (hD : Γ ⊢[PRAAx] le e D) (hM : Γ ⊢[PRAAx] le e M) : Γ ⊢[PRAAx]
    entry (product P R D M) (monus (D+M) e) ≐ entry (product Q R D M) (monus (D+M) e) := by
  have hh : Γ.map Fm.shift ⊢[PRAAx] lowEqual (Syn.shift P) (Syn.shift Q) (Syn.shift D) (Syn.shift H) := by
    simpa only [Fm.shift,subst_lowEqual,Syn.shift] using h.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift H) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using he.shift
  have hd : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift e) (Syn.shift D) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hD.shift
  have hsum : Γ ⊢[PRAAx] GaussianRationalLowCoefficientConvolution.cauchySum P R D M e ≐
      GaussianRationalLowCoefficientConvolution.cauchySum Q R D M e := by
    refine GaussianRationalFiniteSum.sum_congr_bounded GaussianRationalLowCoefficientConvolution.termBody
      GaussianRationalLowCoefficientConvolution.termBody (succ e) (GaussianRationalLowCoefficientConvolution.data P R D M e)
        (GaussianRationalLowCoefficientConvolution.data Q R D M e) (.allI (.impI ?_))
    let Δ := lt (var 0) (succ (Syn.shift e)) :: Γ.map Fm.shift
    have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift e) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    have hir := le_trans hi hd.wk
    have hentry : Δ ⊢[PRAAx] entry (Syn.shift P) (monus (Syn.shift D) (var 0)) ≐
        entry (Syn.shift Q) (monus (Syn.shift D) (var 0)) :=
      (GaussianRationalLowCoefficientConvolution.exponent_inside _ _ _ hir).eqSymm.eqTrans
        ((low_equal_at _ _ _ _ _ hh.wk (le_trans hi hs.wk)).eqTrans
          (GaussianRationalLowCoefficientConvolution.exponent_inside _ _ _ hir))
    simpa only [Δ,Syn.shift,ConciseIPRA.PTm.subst_succ,GaussianRationalLowCoefficientConvolution.subst_data] using
      (GaussianRationalLowCoefficientConvolution.term_at (Γ := Δ) (Syn.shift P) (Syn.shift R) (Syn.shift D) (Syn.shift M) (Syn.shift e) (var 0)).eqTrans
        ((qmul_congr hentry (.eqRefl _)).eqTrans
          (GaussianRationalLowCoefficientConvolution.term_at (Syn.shift Q) (Syn.shift R) (Syn.shift D) (Syn.shift M) (Syn.shift e) (var 0)).eqSymm)
  exact (GaussianRationalLowCoefficientConvolution.coefficient_cauchy P R D M e hD hM).eqTrans
    (hsum.eqTrans (GaussianRationalLowCoefficientConvolution.coefficient_cauchy Q R D M e hD hM).eqSymm)

theorem chain_coefficient (C N K r i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hr : Γ ⊢[PRAAx] lt r K) (hi : Γ ⊢[PRAAx] le i ((N+r*N)+N)) : Γ ⊢[PRAAx]
    entry (product (product (euler C N) (powerPrefix C N K r) N (r*N)) C (N+r*N) N) i ≐
      entry (product (euler C N) (powerPrefix C N K (succ r)) N (succ r*N)) i :=
  (product_associative_coefficient (euler C N) (powerPrefix C N K r) C N (r*N) N i
    (euler_length C N) (prefix_length C N K r) hC hi).eqTrans
    (entry_congr (GaussianPolynomialDeterminantTerms.product_congr (.eqRefl _)
      (GaussianRationalPolynomialPowers.prefix_succ C N K r hr).eqSymm (.eqRefl _) (by ipra_ring)) (.eqRefl _))

theorem scaled_chain_coefficient (C N K r i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hr : Γ ⊢[PRAAx] lt r K) (hi : Γ ⊢[PRAAx] le i (succ r*N+N)) : Γ ⊢[PRAAx]
    entry (product (powerEuler C N K r) C (succ r*N) N) i ≐
      qmul (naturalPoint (succ r)) (entry (product (euler C N) (powerPrefix C N K (succ r)) N (succ r*N)) i) := by
  have hi' : Γ ⊢[PRAAx] le i ((N+r*N)+N) := le_congr (.eqRefl _) (by ipra_ring) hi
  have hCode : Γ ⊢[PRAAx] product (powerEuler C N K r) C (succ r*N) N ≐
      product (scaled (product (euler C N) (powerPrefix C N K r) N (r*N)) (naturalPoint (succ r))) C (N+r*N) N :=
    GaussianPolynomialDeterminantTerms.product_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
  have hI : Γ ⊢[PRAAx] lt i (length (product (product (euler C N) (powerPrefix C N K r) N (r*N)) C (N+r*N) N)) :=
    lt_congr (.eqRefl _) (product_length _ _ _ _).eqSymm ((succ_monus_succ _ _).eqTrans hi')
  exact (entry_congr hCode (.eqRefl _)).eqTrans
    ((scaled_left_coefficient _ C (N+r*N) N _ i (product_length _ _ _ _) hC hi').eqTrans
      ((GaussianRationalCoefficientScaling.scaled_lookup _ _ i hI).eqTrans
        (qmul_congr (.eqRefl _) (chain_coefficient C N K r i hC hr hi'))))

theorem natural_successor_sum (r a : PTm n) (ha : Γ ⊢[PRAAx] GaussianRationalHorner.canonical a) : Γ ⊢[PRAAx]
    GaussianRationalHorner.qadd (qmul (naturalPoint (succ r)) a) a ≐ qmul (naturalPoint (succ (succ r))) a :=
  (GaussianRationalSyntheticDivision.qadd_congr (GaussianRationalNaturalScale.natScale_as_product (succ r) a).eqSymm
    (GaussianRationalNaturalScale.natScale_one_canonical a ha).eqSymm).eqTrans
      ((GaussianRationalNaturalScale.natScale_add (succ r) one a).eqSymm.eqTrans
        ((GaussianRationalNaturalScale.natScale_congr (by ipra_ring) (.eqRefl _)).eqTrans
          (GaussianRationalNaturalScale.natScale_as_product (succ (succ r)) a)))

theorem power_euler_step_point (C N K r e : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (ih : Γ ⊢[PRAAx] lowEqual (euler (powerPrefix C N K (succ r)) (succ r*N)) (powerEuler C N K r) (succ r*N) N)
    (hr : Γ ⊢[PRAAx] lt (succ r) K) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    exponentCoefficient (euler (powerPrefix C N K (succ (succ r))) (succ (succ r)*N)) (succ (succ r)*N) e ≐
      exponentCoefficient (powerEuler C N K (succ r)) (succ (succ r)*N) e := by
  let P := powerPrefix C N K (succ r)
  let D := succ r*N
  let T := D+N
  let I := monus T e
  let S := product (euler C N) P N D
  have hD : Γ ⊢[PRAAx] le e D := le_trans he
    (le_congr (.eqRefl _) (by unfold D; ipra_ring) (le_add_right N (r*N)))
  have hT : Γ ⊢[PRAAx] le e T := le_trans hD (le_add_right D N)
  have hI : Γ ⊢[PRAAx] le I T := GaussianRationalMonicReconstruction.monus_le_left _ _
  have hr0 : Γ ⊢[PRAAx] lt r K := lt_of_le_of_lt (le_succ_self r) hr
  have hL : Γ ⊢[PRAAx]
      exponentCoefficient (euler (powerPrefix C N K (succ (succ r))) (succ (succ r)*N)) (succ (succ r)*N) e ≐
        exponentCoefficient (euler (product P C D N) T) T e :=
    GaussianRationalPolynomialExponentialStability.exponent_congr
      (euler_congr (GaussianRationalPolynomialPowers.prefix_succ C N K (succ r) hr) (by unfold T D; ipra_ring))
      (by unfold T D; ipra_ring) (.eqRefl _)
  have hLeib : Γ ⊢[PRAAx]
      exponentCoefficient (euler (powerPrefix C N K (succ (succ r))) (succ (succ r)*N)) (succ (succ r)*N) e ≐
        GaussianRationalHorner.qadd (entry (product (euler P D) C D N) I) (entry (product P (euler C N) D N) I) :=
    hL.eqTrans ((GaussianRationalLowCoefficientConvolution.exponent_inside _ T e hT).eqTrans
      ((GaussianRationalEulerCoefficients.product_leibniz P C D N e hD he).eqTrans
        (GaussianRationalPolynomialBuffers.added_lookup _ _ _ I ((succ_monus_succ _ _).eqTrans hI))))
  have hFirst : Γ ⊢[PRAAx] entry (product (euler P D) C D N) I ≐ qmul (naturalPoint (succ r)) (entry S I) :=
    (low_product_left (euler P D) (powerEuler C N K r) C D N N e ih he hD he).eqTrans
      (scaled_chain_coefficient C N K r I hC hr0 hI)
  have hSecond : Γ ⊢[PRAAx] entry (product P (euler C N) D N) I ≐ entry S I :=
    product_commutative_coefficient P (euler C N) D N I (prefix_length C N K (succ r)) (euler_length C N) hI
  have hiS : Γ ⊢[PRAAx] le I (N+D) := le_congr (.eqRefl _) (add_comm D N) hI
  have hCan := canonical_at S (N+D) I (product_length _ _ _ _) (product_canonical _ _ _ _) hiS
  have hIR : Γ ⊢[PRAAx] lt I (length S) :=
    lt_congr (.eqRefl _) (product_length _ _ _ _).eqSymm ((succ_monus_succ _ _).eqTrans hiS)
  have hR : Γ ⊢[PRAAx] exponentCoefficient (powerEuler C N K (succ r)) (succ (succ r)*N) e ≐
      qmul (naturalPoint (succ (succ r))) (entry S I) :=
    (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (by unfold T D; ipra_ring) (.eqRefl _)).eqTrans
      ((GaussianRationalLowCoefficientConvolution.exponent_inside _ T e hT).eqTrans
        (GaussianRationalCoefficientScaling.scaled_lookup S _ I hIR))
  exact hLeib.eqTrans ((GaussianRationalSyntheticDivision.qadd_congr hFirst hSecond).eqTrans
    ((natural_successor_sum r (entry S I) hCan).eqTrans hR.eqSymm))

def lowSyntax (P Q D H : PTm n) : BFm n := .all (succ H) (.eq
  (exponentCoefficient (Syn.shift P) (Syn.shift D) (var 0)) (exponentCoefficient (Syn.shift Q) (Syn.shift D) (var 0)))
theorem low_formula (P Q D H : PTm n) : formula (lowSyntax P Q D H) = lowEqual P Q D H := by
  simp [lowSyntax,lowEqual,formula]
def powerLaw (C N K r : PTm n) : Fm PTm n := lt r K ⟶
  lowEqual (euler (powerPrefix C N K (succ r)) (succ r*N)) (powerEuler C N K r) (succ r*N) N
def powerSyntax (C N K r : PTm n) : BFm n := .imp (.lt r K)
  (lowSyntax (euler (powerPrefix C N K (succ r)) (succ r*N)) (powerEuler C N K r) (succ r*N) N)
@[simp] theorem subst_powerLaw {l : ℕ} (σ : Fin n → PTm l) (C N K r : PTm n) :
    (powerLaw C N K r).subst σ = powerLaw (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ r) := by
  simp [powerLaw]
theorem power_formula (C N K r : PTm n) : formula (powerSyntax C N K r) = powerLaw C N K r := by
  simp [powerSyntax,powerLaw,formula,low_formula,BFm.lt,BFm.le,lt,le]

theorem base_low (C N K : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hK : Γ ⊢[PRAAx] lt zero K) : Γ ⊢[PRAAx]
    lowEqual (euler (powerPrefix C N K one) (one*N)) (powerEuler C N K zero) (one*N) N := by
  have hc := shift_length C N hC
  have hh : Γ.map Fm.shift ⊢[PRAAx] canonicalCoefficients (Syn.shift C) := by
    simpa only [Fm.shift,GaussianRationalSyntheticDivision.subst_canonicalCoefficients,Syn.shift] using hCan.shift
  have hk : Γ.map Fm.shift ⊢[PRAAx] lt zero (Syn.shift K) := by
    simpa only [Fm.shift,subst_lt,ConciseIPRA.PTm.subst_zero,Syn.shift] using hK.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift
  have he : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Δ,Syn.shift,GaussianRationalEulerCoefficients.subst_euler,GaussianRationalPolynomialPowers.subst_prefix,
    subst_powerEuler,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,PTm.subst_mul] using
    base_euler_coefficient (Syn.shift C) (Syn.shift N) (Syn.shift K) (var 0) hc.wk hh.wk hk.wk he

theorem step_low (C N K r : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (ih : Γ ⊢[PRAAx] lowEqual (euler (powerPrefix C N K (succ r)) (succ r*N)) (powerEuler C N K r) (succ r*N) N)
    (hr : Γ ⊢[PRAAx] lt (succ r) K) : Γ ⊢[PRAAx]
    lowEqual (euler (powerPrefix C N K (succ (succ r))) (succ (succ r)*N)) (powerEuler C N K (succ r)) (succ (succ r)*N) N := by
  have hc := shift_length C N hC
  have hh : Γ.map Fm.shift ⊢[PRAAx] lowEqual
      (euler (powerPrefix (Syn.shift C) (Syn.shift N) (Syn.shift K) (succ (Syn.shift r))) (succ (Syn.shift r)*Syn.shift N))
      (powerEuler (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift r)) (succ (Syn.shift r)*Syn.shift N) (Syn.shift N) := by
    simpa only [Fm.shift,subst_lowEqual,GaussianRationalEulerCoefficients.subst_euler,GaussianRationalPolynomialPowers.subst_prefix,
      subst_powerEuler,ConciseIPRA.PTm.subst_succ,PTm.subst_mul,Syn.shift] using ih.shift
  have hk : Γ.map Fm.shift ⊢[PRAAx] lt (succ (Syn.shift r)) (Syn.shift K) := by
    simpa only [Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using hr.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift
  have he : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Δ,Syn.shift,GaussianRationalEulerCoefficients.subst_euler,GaussianRationalPolynomialPowers.subst_prefix,
    subst_powerEuler,ConciseIPRA.PTm.subst_succ,PTm.subst_mul] using
    power_euler_step_point (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift r) (var 0) hc.wk hh.wk hk.wk he

theorem power_base (C N K : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) : Γ ⊢[PRAAx] powerLaw C N K zero :=
  .impI (base_low C N K hC.wk hCan.wk Prf.hyp0)
theorem power_step (C N K r : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (ih : Γ ⊢[PRAAx] powerLaw C N K r) : Γ ⊢[PRAAx] powerLaw C N K (succ r) := by
  refine .impI ?_
  have hr : (lt (succ r) K :: Γ) ⊢[PRAAx] lt r K := lt_of_le_of_lt (le_succ_self r) Prf.hyp0
  exact step_low C N K r hC.wk (.impE ih.wk hr) Prf.hyp0

theorem power_euler (C N K r : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hr : Γ ⊢[PRAAx] lt r K) : Γ ⊢[PRAAx]
    lowEqual (euler (powerPrefix C N K (succ r)) (succ r*N)) (powerEuler C N K r) (succ r*N) N := by
  have hc := shift_length C N hC
  have hh : Γ.map Fm.shift ⊢[PRAAx] canonicalCoefficients (Syn.shift C) := by
    simpa only [Fm.shift,GaussianRationalSyntheticDivision.subst_canonicalCoefficients,Syn.shift] using hCan.shift
  have all : Γ ⊢[PRAAx] .all (formula (powerSyntax (Syn.shift C) (Syn.shift N) (Syn.shift K) (var 0))) := by
    refine Foundations.BoundedSyntaxInduction.induction _ ?_ ?_
    · simpa only [power_formula,subst_powerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using power_base (Γ := Γ) C N K hC hCan
    · simpa only [power_formula,subst_powerLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        power_step (Γ := formula (powerSyntax (Syn.shift C) (Syn.shift N) (Syn.shift K) (var 0)) :: Γ.map Fm.shift)
          (Syn.shift C) (Syn.shift N) (Syn.shift K) (var 0) hc.wk
          (by simpa only [power_formula] using (Prf.hyp0 (Ax := PRAAx)))
  have gate : Γ ⊢[PRAAx] powerLaw C N K r := by
    simpa only [power_formula,subst_powerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r
  exact .impE gate hr

theorem power_euler_coefficient (C N K r e : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hr : Γ ⊢[PRAAx] lt r K) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    exponentCoefficient (euler (powerPrefix C N K (succ r)) (succ r*N)) (succ r*N) e ≐
      exponentCoefficient (powerEuler C N K r) (succ r*N) e :=
  low_equal_at _ _ _ _ _ (power_euler C N K r hC hCan hr) he

theorem logarithm_power_euler (d K r e : PTm n) (hr : Γ ⊢[PRAAx] lt r K) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    exponentCoefficient (euler (powerPrefix (GaussianFiniteLogarithmPolynomial.polynomial d) d K (succ r)) (succ r*d)) (succ r*d) e ≐
      exponentCoefficient (powerEuler (GaussianFiniteLogarithmPolynomial.polynomial d) d K r) (succ r*d) e :=
  power_euler_coefficient _ _ _ _ _ (GaussianFiniteLogarithmPolynomial.polynomial_length d)
    (GaussianFiniteLogarithmPolynomial.polynomial_canonical d) hr he

theorem power_euler_canonical (C N K r : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (powerEuler C N K r) :=
  GaussianPolynomialDeterminantTerms.scaled_canonical _ _

theorem zero_degree_euler (C e : PTm n) : Γ ⊢[PRAAx]
    exponentCoefficient (euler C zero) zero e ≐ qzero := by
  refine .orE (zero_or_succ e) ?_ ?_
  · exact (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans
      ((GaussianRationalLowCoefficientConvolution.exponent_inside _ zero zero (le_refl _)).eqTrans
        ((entry_congr (.eqRefl _) (monus_self zero)).eqTrans (GaussianRationalEulerCoefficients.euler_constant _ _)))
  · exact GaussianRationalLowCoefficientConvolution.exponent_outside _ _ e
      (lt_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _))

theorem zero_power_euler (C N K e : PTm n) : Γ ⊢[PRAAx]
    exponentCoefficient (euler (powerPrefix C N K zero) (zero*N)) (zero*N) e ≐ qzero :=
  (GaussianRationalPolynomialExponentialStability.exponent_congr (euler_congr (.eqRefl _) (zero_mul N))
    (zero_mul N) (.eqRefl _)).eqTrans (zero_degree_euler _ e)

def output (C N K r : PTm n) : PTm n := pairT
  (euler (powerPrefix C N K (succ r)) (succ r*N)) (powerEuler C N K r)
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (C N K r : PTm n) : PTm n := PTm.app outputF ![C,N,K,r]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (C N K r : PTm n) :
    Syn.subst σ (output C N K r) = output (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ r) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (C N K r : PTm n) :
    Syn.subst σ (run C N K r) = run (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ K) (Syn.subst σ r) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (C N K r : PTm n) : Γ ⊢[PRAAx] run C N K r ≐ output C N K r := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![C,N,K,r]
theorem returned_euler (C N K r : PTm n) : Γ ⊢[PRAAx]
    fstT (run C N K r) ≐ euler (powerPrefix C N K (succ r)) (succ r*N) :=
  (congrFst (program_at C N K r)).eqTrans (fst_pair _ _)
theorem returned_target (C N K r : PTm n) : Γ ⊢[PRAAx] sndT (run C N K r) ≐ powerEuler C N K r :=
  (congrSnd (program_at C N K r)).eqTrans (snd_pair _ _)
theorem returned_power_euler (C N K r e : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hCan : Γ ⊢[PRAAx] canonicalCoefficients C) (hr : Γ ⊢[PRAAx] lt r K) (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    exponentCoefficient (fstT (run C N K r)) (succ r*N) e ≐
      exponentCoefficient (sndT (run C N K r)) (succ r*N) e :=
  (GaussianRationalPolynomialExponentialStability.exponent_congr (returned_euler C N K r) (.eqRefl _) (.eqRefl _)).eqTrans
    ((power_euler_coefficient C N K r e hC hCan hr he).eqTrans
      (GaussianRationalPolynomialExponentialStability.exponent_congr (returned_target C N K r).eqSymm (.eqRefl _) (.eqRefl _)))

theorem actual_product_association_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (length (var 0) ≐ succ (var 3) ⟶ length (var 1) ≐ succ (var 4) ⟶ length (var 2) ≐ succ (var 5) ⟶
      le (var 6) ((var 3+var 4)+var 5) ⟶
      entry (product (product (var 0) (var 1) (var 3) (var 4)) (var 2) (var 3+var 4) (var 5)) (var 6) ≐
        entry (product (var 0) (product (var 1) (var 2) (var 4) (var 5)) (var 3) (var 4+var 5)) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (product_associative_coefficient _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_product_commutation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 2) ⟶ length (var 1) ≐ succ (var 3) ⟶ le (var 4) (var 2+var 3) ⟶
      entry (product (var 0) (var 1) (var 2) (var 3)) (var 4) ≐ entry (product (var 1) (var 0) (var 3) (var 2)) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (product_commutative_coefficient _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_power_euler_target_storage_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (powerEuler (var 0) (var 1) (var 2) (var 3)) ≐ succ (succ (var 3)*var 1) ⋏
      canonicalCoefficients (powerEuler (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.andI (power_euler_length _ _ _ _) (power_euler_canonical _ _ _ _))
theorem actual_low_power_euler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶ canonicalCoefficients (var 0) ⟶ lt (var 3) (var 2) ⟶ le (var 4) (var 1) ⟶
      exponentCoefficient (euler (powerPrefix (var 0) (var 1) (var 2) (succ (var 3))) (succ (var 3)*var 1)) (succ (var 3)*var 1) (var 4) ≐
        exponentCoefficient (powerEuler (var 0) (var 1) (var 2) (var 3)) (succ (var 3)*var 1) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (power_euler_coefficient _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem original_logarithm_low_power_euler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (var 1) ⟶ le (var 3) (var 0) ⟶
      exponentCoefficient (euler (powerPrefix (GaussianFiniteLogarithmPolynomial.polynomial (var 0)) (var 0) (var 1) (succ (var 2)))
        (succ (var 2)*var 0)) (succ (var 2)*var 0) (var 3) ≐
      exponentCoefficient (powerEuler (GaussianFiniteLogarithmPolynomial.polynomial (var 0)) (var 0) (var 1) (var 2)) (succ (var 2)*var 0) (var 3)) :=
  closeUniv 4 (.impI (.impI (logarithm_power_euler _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_zero_power_euler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (exponentCoefficient (euler (powerPrefix (var 0) (var 1) (var 2) zero) (zero*var 1)) (zero*var 1) (var 3) ≐ qzero) :=
  closeUniv 4 (zero_power_euler _ _ _ _)
theorem actual_power_euler_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_returned_power_euler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶ canonicalCoefficients (var 0) ⟶ lt (var 3) (var 2) ⟶ le (var 4) (var 1) ⟶
      exponentCoefficient (fstT (run (var 0) (var 1) (var 2) (var 3))) (succ (var 3)*var 1) (var 4) ≐
        exponentCoefficient (sndT (run (var 0) (var 1) (var 2) (var 3))) (succ (var 3)*var 1) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (returned_power_euler _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianRationalPolynomialPowerEuler
