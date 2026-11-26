import IPRADerivations.Analysis.Polynomials.Products.GaussianPolynomialLowJetProduct
import IPRADerivations.Analysis.Polynomials.Products.GaussianPolynomialLinearFactorCoefficients
import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaExponentCoefficientStability

/-!
# Original actual powers agree across Gamma coefficient horizons

The original power-prefix program retains its own true cap at each
successor. A genuine bounded-formula induction transports finite low
coefficient equality between buffers with different stored degrees.
The actual original Gamma input reader coherence discharges this input
relation, giving exact power-prefix coefficients across unrelated
degree horizons and ambient power caps. Only a finite comparison is
claimed here; regular all-degree coefficient names remain separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPowerHorizonCoherence

open_ipra
open GaussianRationalHorner (qmul)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianRationalPolynomialPowers (powerPrefix)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside)
open GaussianRationalPolynomialExponentialStability (exponent_congr)
open GaussianPolynomialLowJetProduct (jetEqual jetSyntax jet_formula jet_at)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem jet_transport {P N Q M P' N' Q' M' H : PTm n}
    (hP : Γ ⊢[PRAAx] P ≐ P') (hN : Γ ⊢[PRAAx] N ≐ N')
    (hQ : Γ ⊢[PRAAx] Q ≐ Q') (hM : Γ ⊢[PRAAx] M ≐ M')
    (h : Γ ⊢[PRAAx] jetEqual P N Q M H) : Γ ⊢[PRAAx] jetEqual P' N' Q' M' H := by
  have hp : Γ.map Fm.shift ⊢[PRAAx] Syn.shift P ≐ Syn.shift P' := by simpa [Fm.shift,Syn.shift] using hP.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] Syn.shift N ≐ Syn.shift N' := by simpa [Fm.shift,Syn.shift] using hN.shift
  have hq : Γ.map Fm.shift ⊢[PRAAx] Syn.shift Q ≐ Syn.shift Q' := by simpa [Fm.shift,Syn.shift] using hQ.shift
  have hm : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ Syn.shift M' := by simpa [Fm.shift,Syn.shift] using hM.shift
  have hh : Γ.map Fm.shift ⊢[PRAAx] jetEqual (Syn.shift P) (Syn.shift N) (Syn.shift Q) (Syn.shift M) (Syn.shift H) := by
    simpa only [Fm.shift,GaussianPolynomialLowJetProduct.subst_jetEqual,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift H)) :: Γ.map Fm.shift
  have he : Δ ⊢[PRAAx] le (var 0) (Syn.shift H) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  exact (exponent_congr hp.wk.eqSymm hn.wk.eqSymm (.eqRefl (var 0))).eqTrans
    ((jet_at _ _ _ _ _ _ hh.wk he).eqTrans (exponent_congr hq.wk hm.wk (.eqRefl _)))

theorem prefix_index (C N K : PTm n) {i j : PTm n} (h : Γ ⊢[PRAAx] i ≐ j) : Γ ⊢[PRAAx]
    powerPrefix C N K i ≐ powerPrefix C N K j :=
  GaussianPolynomialDeterminantTerms.stage_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) h

theorem zero_power_jet (C N D M K T H : PTm n) : Γ ⊢[PRAAx]
    jetEqual (powerPrefix C N K zero) (zero*N) (powerPrefix D M T zero) (zero*M) H := by
  refine .allI (.impI ?_)
  simpa only [jetEqual,Syn.shift,GaussianRationalPolynomialPowers.subst_prefix,PTm.subst_mul,PTm.subst_zero] using
    (exponent_congr (Γ := lt (var 0) (succ (Syn.shift H)) :: Γ.map Fm.shift)
      (GaussianRationalPolynomialPowers.prefix_zero (Syn.shift C) (Syn.shift N) (Syn.shift K))
      (zero_mul (Syn.shift N)) (.eqRefl (var 0))).eqTrans
        (exponent_congr (GaussianRationalPolynomialPowers.prefix_zero (Syn.shift D) (Syn.shift M) (Syn.shift T))
          (zero_mul (Syn.shift M)) (.eqRefl (var 0))).eqSymm

theorem first_power_reader (C N K e : PTm n) (hK : Γ ⊢[PRAAx] lt zero K)
    (he : Γ ⊢[PRAAx] le e N) : Γ ⊢[PRAAx]
    exponentCoefficient (powerPrefix C N K one) (one*N) e ≐ qmul qone (exponentCoefficient C N e) := by
  have code := (GaussianRationalPolynomialPowers.prefix_succ (Γ := Γ) C N K zero hK).eqTrans
    (GaussianPolynomialDeterminantTerms.product_congr (GaussianRationalPolynomialPowers.prefix_zero C N K)
      (.eqRefl C) (zero_mul N) (.eqRefl N))
  exact (exponent_congr code (one_mul N) (.eqRefl e)).eqTrans
    ((exponent_inside _ _ _ he).eqTrans
      ((GaussianPolynomialLinearFactorCoefficients.constant_left_value _ _ _ _
        (GaussianRationalMonicReconstruction.monus_le_left N e)).eqTrans
          (qmul_congr (.eqRefl qone) (exponent_inside C N e he).eqSymm)))

def powerLaw (C N D M K T H r : PTm n) : Fm PTm n := lt r K ⟶ lt r T ⟶
  jetEqual (powerPrefix C N K (succ r)) (succ r*N) (powerPrefix D M T (succ r)) (succ r*M) H
def powerSyntax (C N D M K T H r : PTm n) : BFm n := .imp (.lt r K) (.imp (.lt r T)
  (jetSyntax (powerPrefix C N K (succ r)) (succ r*N) (powerPrefix D M T (succ r)) (succ r*M) H))
ipra_subst powerLaw
theorem power_formula (C N D M K T H r : PTm n) : formula (powerSyntax C N D M K T H r) = powerLaw C N D M K T H r := by
  simp [powerSyntax,powerLaw,formula,jet_formula,BFm.lt,BFm.le,lt,le]

theorem first_power_jet (C N D M K T H : PTm n) (h : Γ ⊢[PRAAx] jetEqual C N D M H)
    (hN : Γ ⊢[PRAAx] le H N) (hM : Γ ⊢[PRAAx] le H M)
    (hK : Γ ⊢[PRAAx] lt zero K) (hT : Γ ⊢[PRAAx] lt zero T) : Γ ⊢[PRAAx]
    jetEqual (powerPrefix C N K one) (one*N) (powerPrefix D M T one) (one*M) H := by
  have hh : Γ.map Fm.shift ⊢[PRAAx] jetEqual (Syn.shift C) (Syn.shift N) (Syn.shift D) (Syn.shift M) (Syn.shift H) := by
    simpa only [Fm.shift,GaussianPolynomialLowJetProduct.subst_jetEqual,Syn.shift] using h.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift H) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have hm : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift H) (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hM.shift
  have hk : Γ.map Fm.shift ⊢[PRAAx] lt zero (Syn.shift K) := by simpa [Fm.shift,Syn.shift] using hK.shift
  have ht : Γ.map Fm.shift ⊢[PRAAx] lt zero (Syn.shift T) := by simpa [Fm.shift,Syn.shift] using hT.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift H)) :: Γ.map Fm.shift
  have he : Δ ⊢[PRAAx] le (var 0) (Syn.shift H) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [jetEqual,Syn.shift,GaussianRationalPolynomialPowers.subst_prefix,PTm.subst_mul,PTm.subst_succ,PTm.subst_zero] using
    (first_power_reader (Syn.shift C) (Syn.shift N) (Syn.shift K) (var 0) hk.wk (le_trans he hn.wk)).eqTrans
      ((qmul_congr (.eqRefl qone) (jet_at _ _ _ _ _ _ hh.wk he)).eqTrans
        (first_power_reader (Syn.shift D) (Syn.shift M) (Syn.shift T) (var 0) ht.wk (le_trans he hm.wk)).eqSymm)

theorem positive_degree_bound (H N r : PTm n) (hN : Γ ⊢[PRAAx] le H N) : Γ ⊢[PRAAx] le H (succ r*N) :=
  le_trans hN (le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N (zero_lt_succ r)))

theorem power_base (C N D M K T H : PTm n) (h : Γ ⊢[PRAAx] jetEqual C N D M H)
    (hN : Γ ⊢[PRAAx] le H N) (hM : Γ ⊢[PRAAx] le H M) : Γ ⊢[PRAAx] powerLaw C N D M K T H zero :=
  .impI (.impI (first_power_jet _ _ _ _ _ _ _ h.wk.wk hN.wk.wk hM.wk.wk Prf.hyp1 Prf.hyp0))

theorem power_step (C N D M K T H r : PTm n) (h : Γ ⊢[PRAAx] jetEqual C N D M H)
    (hN : Γ ⊢[PRAAx] le H N) (hM : Γ ⊢[PRAAx] le H M)
    (ih : Γ ⊢[PRAAx] powerLaw C N D M K T H r) : Γ ⊢[PRAAx] powerLaw C N D M K T H (succ r) := by
  refine .impI (.impI ?_)
  let Δ := lt (succ r) T :: lt (succ r) K :: Γ
  have hk : Δ ⊢[PRAAx] lt r K := lt_of_le_of_lt (le_succ_self r) Prf.hyp1
  have ht : Δ ⊢[PRAAx] lt r T := lt_of_le_of_lt (le_succ_self r) Prf.hyp0
  have previous := Prf.impE (Prf.impE ih.wk.wk hk) ht
  have products := GaussianPolynomialLowJetProduct.product_jet (Γ := Δ)
    (powerPrefix C N K (succ r)) (succ r*N) C N (powerPrefix D M T (succ r)) (succ r*M) D M H
    previous h.wk.wk (positive_degree_bound H N r hN.wk.wk) hN.wk.wk
    (positive_degree_bound H M r hM.wk.wk) hM.wk.wk
  exact jet_transport (GaussianRationalPolynomialPowers.prefix_succ C N K (succ r) Prf.hyp1).eqSymm
    (by ipra_ring) (GaussianRationalPolynomialPowers.prefix_succ D M T (succ r) Prf.hyp0).eqSymm (by ipra_ring) products

theorem positive_power_jet (C N D M K T H r : PTm n) (h : Γ ⊢[PRAAx] jetEqual C N D M H)
    (hN : Γ ⊢[PRAAx] le H N) (hM : Γ ⊢[PRAAx] le H M)
    (hK : Γ ⊢[PRAAx] lt r K) (hT : Γ ⊢[PRAAx] lt r T) : Γ ⊢[PRAAx]
    jetEqual (powerPrefix C N K (succ r)) (succ r*N) (powerPrefix D M T (succ r)) (succ r*M) H := by
  have hh : Γ.map Fm.shift ⊢[PRAAx] jetEqual (Syn.shift C) (Syn.shift N) (Syn.shift D) (Syn.shift M) (Syn.shift H) := by
    simpa only [Fm.shift,GaussianPolynomialLowJetProduct.subst_jetEqual,Syn.shift] using h.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift H) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have hm : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift H) (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hM.shift
  have all : Γ ⊢[PRAAx] .all (formula (powerSyntax (Syn.shift C) (Syn.shift N) (Syn.shift D) (Syn.shift M)
      (Syn.shift K) (Syn.shift T) (Syn.shift H) (var 0))) := by
    refine Foundations.BoundedSyntaxInduction.induction _ ?_ ?_
    · simpa only [power_formula,subst_powerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using power_base C N D M K T H h hN hM
    · simpa only [power_formula,subst_powerLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        power_step (Γ := formula (powerSyntax (Syn.shift C) (Syn.shift N) (Syn.shift D) (Syn.shift M)
          (Syn.shift K) (Syn.shift T) (Syn.shift H) (var 0)) :: Γ.map Fm.shift)
          (Syn.shift C) (Syn.shift N) (Syn.shift D) (Syn.shift M) (Syn.shift K) (Syn.shift T) (Syn.shift H) (var 0)
          hh.wk hn.wk hm.wk (by simpa only [power_formula] using (Prf.hyp0 (Ax := PRAAx)))
  have gate : Γ ⊢[PRAAx] powerLaw C N D M K T H r := by
    simpa only [power_formula,subst_powerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r
  exact Prf.impE (Prf.impE gate hK) hT

theorem power_jet (C N D M K T H j : PTm n) (h : Γ ⊢[PRAAx] jetEqual C N D M H)
    (hN : Γ ⊢[PRAAx] le H N) (hM : Γ ⊢[PRAAx] le H M)
    (hK : Γ ⊢[PRAAx] le j K) (hT : Γ ⊢[PRAAx] le j T) : Γ ⊢[PRAAx]
    jetEqual (powerPrefix C N K j) (j*N) (powerPrefix D M T j) (j*M) H := by
  refine .orE (zero_or_succ j) ?_ ?_
  · exact jet_transport (prefix_index C N K Prf.hyp0.eqSymm) (congrMul Prf.hyp0.eqSymm (.eqRefl N))
      (prefix_index D M T Prf.hyp0.eqSymm) (congrMul Prf.hyp0.eqSymm (.eqRefl M)) (zero_power_jet _ _ _ _ _ _ _)
  · have hk : ((j ≐ succ (LeanProofs.IPRA.PTm.pred j)) :: Γ) ⊢[PRAAx] lt (LeanProofs.IPRA.PTm.pred j) K :=
      le_congr Prf.hyp0 (.eqRefl K) hK.wk
    have ht : ((j ≐ succ (LeanProofs.IPRA.PTm.pred j)) :: Γ) ⊢[PRAAx] lt (LeanProofs.IPRA.PTm.pred j) T :=
      le_congr Prf.hyp0 (.eqRefl T) hT.wk
    exact jet_transport (prefix_index C N K Prf.hyp0.eqSymm) (congrMul Prf.hyp0.eqSymm (.eqRefl N))
      (prefix_index D M T Prf.hyp0.eqSymm) (congrMul Prf.hyp0.eqSymm (.eqRefl M))
        (positive_power_jet _ _ _ _ _ _ _ _ h.wk hN.wk hM.wk hk ht)

theorem original_input_jet (q N L M H : PTm n)
    (hL : Γ ⊢[PRAAx] le H (GaussianGammaReciprocalDegreeCells.degree L))
    (hM : Γ ⊢[PRAAx] le H (GaussianGammaReciprocalDegreeCells.degree M)) : Γ ⊢[PRAAx]
    jetEqual (GaussianGammaExponentCoefficientPolynomial.polynomial q N L) (GaussianGammaReciprocalDegreeCells.degree L)
      (GaussianGammaExponentCoefficientPolynomial.polynomial q N M) (GaussianGammaReciprocalDegreeCells.degree M) H := by
  have hl : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift H) (GaussianGammaReciprocalDegreeCells.degree (Syn.shift L)) := by
    simpa [Fm.shift,Syn.shift] using hL.shift
  have hm : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift H) (GaussianGammaReciprocalDegreeCells.degree (Syn.shift M)) := by
    simpa [Fm.shift,Syn.shift] using hM.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift H)) :: Γ.map Fm.shift
  have he : Δ ⊢[PRAAx] le (var 0) (Syn.shift H) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Δ,jetEqual,Syn.shift,GaussianGammaExponentCoefficientPolynomial.subst_polynomial,
    GaussianGammaReciprocalDegreeCells.subst_degree] using
    GaussianGammaExponentCoefficientStability.input_horizon_coherence (Syn.shift q) (Syn.shift N) (Syn.shift L) (Syn.shift M)
      (var 0) (le_trans he hl.wk) (le_trans he hm.wk)

theorem original_positive_power_horizon (q N L M K T H r : PTm n)
    (hL : Γ ⊢[PRAAx] le H (GaussianGammaReciprocalDegreeCells.degree L))
    (hM : Γ ⊢[PRAAx] le H (GaussianGammaReciprocalDegreeCells.degree M))
    (hK : Γ ⊢[PRAAx] lt r K) (hT : Γ ⊢[PRAAx] lt r T) : Γ ⊢[PRAAx]
    jetEqual (powerPrefix (GaussianGammaExponentCoefficientPolynomial.polynomial q N L) (GaussianGammaReciprocalDegreeCells.degree L) K (succ r))
      (succ r*GaussianGammaReciprocalDegreeCells.degree L)
      (powerPrefix (GaussianGammaExponentCoefficientPolynomial.polynomial q N M) (GaussianGammaReciprocalDegreeCells.degree M) T (succ r))
      (succ r*GaussianGammaReciprocalDegreeCells.degree M) H :=
  positive_power_jet _ _ _ _ _ _ _ _ (original_input_jet q N L M H hL hM) hL hM hK hT

theorem original_power_horizon (q N L M K T H j : PTm n)
    (hL : Γ ⊢[PRAAx] le H (GaussianGammaReciprocalDegreeCells.degree L))
    (hM : Γ ⊢[PRAAx] le H (GaussianGammaReciprocalDegreeCells.degree M))
    (hK : Γ ⊢[PRAAx] le j K) (hT : Γ ⊢[PRAAx] le j T) : Γ ⊢[PRAAx]
    jetEqual (powerPrefix (GaussianGammaExponentCoefficientPolynomial.polynomial q N L) (GaussianGammaReciprocalDegreeCells.degree L) K j)
      (j*GaussianGammaReciprocalDegreeCells.degree L)
      (powerPrefix (GaussianGammaExponentCoefficientPolynomial.polynomial q N M) (GaussianGammaReciprocalDegreeCells.degree M) T j)
      (j*GaussianGammaReciprocalDegreeCells.degree M) H :=
  power_jet _ _ _ _ _ _ _ _ (original_input_jet q N L M H hL hM) hL hM hK hT

theorem original_Gamma_positive_power_horizon_coherence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le (var 6) (GaussianGammaReciprocalDegreeCells.degree (var 2)) ⟶
      le (var 6) (GaussianGammaReciprocalDegreeCells.degree (var 3)) ⟶ lt (var 7) (var 4) ⟶ lt (var 7) (var 5) ⟶
      jetEqual
        (powerPrefix (GaussianGammaExponentCoefficientPolynomial.polynomial (var 0) (var 1) (var 2)) (GaussianGammaReciprocalDegreeCells.degree (var 2)) (var 4) (succ (var 7)))
        (succ (var 7)*GaussianGammaReciprocalDegreeCells.degree (var 2))
        (powerPrefix (GaussianGammaExponentCoefficientPolynomial.polynomial (var 0) (var 1) (var 3)) (GaussianGammaReciprocalDegreeCells.degree (var 3)) (var 5) (succ (var 7)))
        (succ (var 7)*GaussianGammaReciprocalDegreeCells.degree (var 3)) (var 6)) :=
  closeUniv 8 (.impI (.impI (.impI (.impI
    (original_positive_power_horizon _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem original_Gamma_power_horizon_coherence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le (var 6) (GaussianGammaReciprocalDegreeCells.degree (var 2)) ⟶
      le (var 6) (GaussianGammaReciprocalDegreeCells.degree (var 3)) ⟶ le (var 7) (var 4) ⟶ le (var 7) (var 5) ⟶
      jetEqual
        (powerPrefix (GaussianGammaExponentCoefficientPolynomial.polynomial (var 0) (var 1) (var 2)) (GaussianGammaReciprocalDegreeCells.degree (var 2)) (var 4) (var 7))
        (var 7*GaussianGammaReciprocalDegreeCells.degree (var 2))
        (powerPrefix (GaussianGammaExponentCoefficientPolynomial.polynomial (var 0) (var 1) (var 3)) (GaussianGammaReciprocalDegreeCells.degree (var 3)) (var 5) (var 7))
        (var 7*GaussianGammaReciprocalDegreeCells.degree (var 3)) (var 6)) :=
  closeUniv 8 (.impI (.impI (.impI (.impI
    (original_power_horizon _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianGammaPowerHorizonCoherence
