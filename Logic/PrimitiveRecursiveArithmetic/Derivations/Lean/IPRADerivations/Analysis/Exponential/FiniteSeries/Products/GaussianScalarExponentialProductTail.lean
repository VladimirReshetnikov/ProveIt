import IPRADerivations.Analysis.Exponential.FiniteSeries.Products.GaussianScalarExponentialProductLowDegrees
import IPRADerivations.Analysis.Exponential.Estimates.GaussianRationalExponentialTail
import IPRADerivations.Foundations.DyadicGain

/-!
# The tail of the actual rectangular exponential product

The original product buffer reads descending entries with explicit
padding. Its high-degree terms only use coefficient pairs whose
degrees add to the requested exponent. The Euclidean bound iterates
over the original finite sums at both levels. The original factorial
majorants and a computed cutoff make this actual residual as small as
the requested dyadic error on a positive numerical disk.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianScalarExponentialProductTail

open_ipra
open GaussianRationalHorner (qzero qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalHornerPerturbation (bounded_sum_same_den)
open GaussianScalarExponentialProductLowDegrees (buffer descending_at product highPart high_part_term
  evaluationData subst_evaluationData)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside)
open GaussianScalarExponentialDiagonal (coefficient)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

def termsBounded (f : PTm 2) (N x A B : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ bounded (inst2 f (var 0) (Syn.shift x)) (Syn.shift A) (Syn.shift B))

def prefixBound (f : PTm 2) (N x A B k : PTm n) : Fm PTm n :=
  le k N ⟶ bounded (GaussianRationalFiniteSum.sum f k x) (k*A) B

ipra_subst prefixBound

ipra_subst termsBounded [Syn.shift_subst, Syn.subst_shift]

theorem term_bound_at (f : PTm 2) (N x A B i : PTm n)
    (h : Γ ⊢[PRAAx] termsBounded f N x A B) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] bounded (inst2 f i x) A B := by
  have q : Γ ⊢[PRAAx] lt i N ⟶ bounded (inst2 f i x) A B := by simpa [termsBounded] using h.allE i
  exact .impE q hi

theorem prefix_step (f : PTm 2) (N x A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] termsBounded f N x A B) (hk : Γ ⊢[PRAAx] lt k N)
    (ih : Γ ⊢[PRAAx] prefixBound f N x A B k) :
    Γ ⊢[PRAAx] bounded (GaussianRationalFiniteSum.sum f (succ k) x) (succ k*A) B :=
  bound_congr (GaussianRationalFiniteSum.sum_succ f k x).eqSymm (succ_mul k A).eqSymm (.eqRefl _)
    (bounded_sum_same_den _ _ _ _ _ hB (.impE ih (le_trans (le_succ_self _) hk))
      (term_bound_at f N x A B k h hk))

theorem sum_bound (f : PTm 2) (N x A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] termsBounded f N x A B) :
    Γ ⊢[PRAAx] bounded (GaussianRationalFiniteSum.sum f N x) (N*A) B := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] termsBounded f (Syn.shift N) (Syn.shift x) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift,subst_termsBounded,Syn.shift] using h.shift
  have hb : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have all : Γ ⊢[PRAAx] .all (prefixBound f (Syn.shift N) (Syn.shift x) (Syn.shift A) (Syn.shift B) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_prefixBound]
    · exact .impI (bound_congr (GaussianRationalFiniteSum.sum_zero _ _).eqSymm (zero_mul A).eqSymm (.eqRefl _)
        (GaussianMonicResidualRadius.zero_bounded zero _ hB.wk))
    · exact .impI (prefix_step f _ _ _ _ _ hb.wk.wk hs.wk.wk Prf.hyp0 Prf.hyp1)
  have p : Γ ⊢[PRAAx] prefixBound f N x A B N := by
    simpa only [subst_prefixBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact .impE p (le_refl _)

/-- A nonzero original convolution entry has exactly the requested total degree. -/
theorem contribution_degree (K e i : PTm n)
    (he : Γ ⊢[PRAAx] le e (K+K)) (hi : Γ ⊢[PRAAx] le i K)
    (hd : Γ ⊢[PRAAx] le i (monus (K+K) e)) (hj : Γ ⊢[PRAAx] le (monus (monus (K+K) e) i) K) :
    Γ ⊢[PRAAx] monus K i+monus K (monus (monus (K+K) e) i) ≐ e := by
  ipra_lc natEq (eq_add_of_le he)-natEq (eq_add_of_le hi)+natEq (eq_add_of_le hd)-natEq (eq_add_of_le hj)

theorem large_degree {a b e H : PTm n} (h : Γ ⊢[PRAAx] a+b ≐ e) (he : Γ ⊢[PRAAx] le (H+H) e) :
    Γ ⊢[PRAAx] le H a ⋎ le H b := by
  refine .orE (lt_or_le a H) ?_ (.orI₁ Prf.hyp0)
  have h₁ := natEq (h.wk (ψ := lt a H))
  have bound : (lt a H :: Γ) ⊢[PRAAx] le H b := by
    ipra_le sl he.wk+sl (Prf.hyp0 : (lt a H :: Γ) ⊢[PRAAx] lt a H)+1 using linear_combination h₁
  exact .orI₂ bound

def smallCoefficients (q H B : PTm n) : Fm PTm n :=
  .all (le (Syn.shift H) (var 0) ⟶ bounded (coefficient (Syn.shift q) (var 0)) one (Syn.shift B))

theorem small_at (q H B j : PTm n) (h : Γ ⊢[PRAAx] smallCoefficients q H B)
    (hj : Γ ⊢[PRAAx] le H j) : Γ ⊢[PRAAx] bounded (coefficient q j) one B := by
  have rs : Γ ⊢[PRAAx] le H j ⟶ bounded (coefficient q j) one B := by
    simpa [smallCoefficients] using h.allE j
  exact .impE rs hj

def coarseCoefficients (q A : PTm n) : Fm PTm n :=
  .all (bounded (coefficient (Syn.shift q) (var 0)) (Syn.shift A) one)

ipra_subst smallCoefficients [Syn.shift_subst, Syn.subst_shift]

ipra_subst coarseCoefficients [Syn.shift_subst, Syn.subst_shift]

theorem coarse_at (q A j : PTm n) (h : Γ ⊢[PRAAx] coarseCoefficients q A) :
    Γ ⊢[PRAAx] bounded (coefficient q j) A one := by
  simpa [coarseCoefficients] using h.allE j

/-- In the original bounded convolution, a high total degree forces at least one small factor. -/
theorem high_contribution_bound (u v K e i H A B : PTm n)
    (he : Γ ⊢[PRAAx] le e (K+K)) (hH : Γ ⊢[PRAAx] le (H+H) e) (hi : Γ ⊢[PRAAx] le i K)
    (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] coarseCoefficients u A) (hv : Γ ⊢[PRAAx] coarseCoefficients v A)
    (hsu : Γ ⊢[PRAAx] smallCoefficients u H B) (hsv : Γ ⊢[PRAAx] smallCoefficients v H B) :
    Γ ⊢[PRAAx] bounded
      (GaussianRationalPolynomialProduct.contribution (buffer u K) (buffer v K) K (monus (K+K) e) i) A B := by
  let k := monus (K+K) e
  let j := monus k i
  let term := GaussianRationalPolynomialProduct.contribution (buffer u K) (buffer v K) K k i
  refine .orE (lt_or_le k i) ?_ ?_
  · exact bound_congr (GaussianRationalPolynomialProduct.contribution_outside _ _ _ _ _ Prf.hyp0).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianMonicResidualRadius.zero_bounded A B hB.wk)
  let Δ := le i k :: Γ
  have hk : Δ ⊢[PRAAx] le i k := Prf.hyp0
  refine .orE (lt_or_le K j) ?_ ?_
  · have hout : (lt K j :: Δ) ⊢[PRAAx] le (succ K) j := Prf.hyp0
    have e := (GaussianRationalPolynomialProduct.contribution_inside (buffer u K) (buffer v K) K k i hk.wk).eqTrans
      ((qmul_congr (.eqRefl _) (GaussianRationalLinearProduct.padded_outside (buffer v K) (succ K) j hout)).eqTrans
        (GaussianRationalSyntheticDivision.qmul_zero_right _))
    exact bound_congr e.eqSymm (.eqRefl _) (.eqRefl _) (GaussianMonicResidualRadius.zero_bounded A B hB.wk.wk)
  let Ξ := le j K :: Δ
  have hj : Ξ ⊢[PRAAx] le j K := Prf.hyp0
  have hEntry : Ξ ⊢[PRAAx] term ≐ qmul (coefficient u (monus K i)) (coefficient v (monus K j)) :=
    (GaussianRationalPolynomialProduct.contribution_inside _ _ K k i hk.wk).eqTrans
      (qmul_congr (descending_at u K i hi.wk.wk)
        ((GaussianRationalLinearProduct.padded_inside _ _ _ ((succ_monus_succ _ _).eqTrans hj)).eqTrans
          (descending_at v K j hj)))
  have degrees := large_degree (contribution_degree K e i he.wk.wk hi.wk.wk hk.wk hj) hH.wk.wk
  refine .orE degrees ?_ ?_
  · exact bound_congr hEntry.wk.eqSymm (one_mul _) (by ipra_ring)
      (bounded_product _ _ one B A one hB.wk.wk.wk (le_refl _)
        (small_at _ _ _ (monus K i) hsu.wk.wk.wk Prf.hyp0) (coarse_at _ _ (monus K j) hv.wk.wk.wk))
  · exact bound_congr hEntry.wk.eqSymm (by ipra_ring) (one_mul _)
      (bounded_product _ _ A one one B (le_refl _) hB.wk.wk.wk
        (coarse_at _ _ (monus K i) hu.wk.wk.wk) (small_at _ _ _ (monus K j) hsv.wk.wk.wk Prf.hyp0))

theorem high_exponent_bound (u v K e H A B : PTm n)
    (he : Γ ⊢[PRAAx] le e (K+K)) (hH : Γ ⊢[PRAAx] le (H+H) e) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] coarseCoefficients u A) (hv : Γ ⊢[PRAAx] coarseCoefficients v A)
    (hsu : Γ ⊢[PRAAx] smallCoefficients u H B) (hsv : Γ ⊢[PRAAx] smallCoefficients v H B) :
    Γ ⊢[PRAAx] bounded (exponentCoefficient (product u v K) (K+K) e) (succ K*A) B := by
  let k := monus (K+K) e
  let f := GaussianRationalPolynomialProduct.contributionBody
  let x := GaussianRationalPolynomialProduct.data (buffer u K) (buffer v K) K k
  have h := (exponent_inside (product u v K) (K+K) e he).eqTrans
    (GaussianRationalPolynomialProduct.product_lookup (buffer u K) (buffer v K) K K k
      (GaussianRationalMonicReconstruction.monus_le_left _ _))
  apply bound_congr h.eqSymm (.eqRefl _) (.eqRefl _)
  apply sum_bound f (succ K) x A B hB
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift K)) :: Γ.map Fm.shift
  let a := Syn.shift u
  let b := Syn.shift v
  let L := Syn.shift K
  let E := Syn.shift e
  let J := Syn.shift H
  let P := Syn.shift A
  let Q := Syn.shift B
  have leE : Δ ⊢[PRAAx] le E (L+L) := by simpa [Δ,E,L,Fm.shift,Syn.shift] using he.shift.wk
  have leH : Δ ⊢[PRAAx] le (J+J) E := by simpa [Δ,J,E,Fm.shift,Syn.shift] using hH.shift.wk
  have leB : Δ ⊢[PRAAx] le one Q := by simpa [Δ,Q,Fm.shift,Syn.shift] using hB.shift.wk
  have ca : Δ ⊢[PRAAx] coarseCoefficients a P := by simpa [Δ,a,P,Fm.shift,Syn.shift] using hu.shift.wk
  have cb : Δ ⊢[PRAAx] coarseCoefficients b P := by simpa [Δ,b,P,Fm.shift,Syn.shift] using hv.shift.wk
  have sa : Δ ⊢[PRAAx] smallCoefficients a J Q := by simpa [Δ,a,J,Q,Fm.shift,Syn.shift] using hsu.shift.wk
  have sb : Δ ⊢[PRAAx] smallCoefficients b J Q := by simpa [Δ,b,J,Q,Fm.shift,Syn.shift] using hsv.shift.wk
  have hi : Δ ⊢[PRAAx] le (var 0) L := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have term := high_contribution_bound a b L E (var 0) J P Q leE leH hi leB ca cb sa sb
  have eq := GaussianRationalPolynomialProduct.contribution_body_at (Γ := Δ) (buffer a L) (buffer b L)
    L (monus (L+L) E) (var 0)
  simpa only [Δ,x,k,f,a,b,L,E,J,P,Q,Syn.shift,GaussianRationalPolynomialProduct.subst_data,
    GaussianScalarExponentialProductLowDegrees.subst_buffer,PTm.subst_monus,PTm.subst_add,ConciseIPRA.PTm.subst_succ] using
    bound_congr eq.eqSymm (.eqRefl _) (.eqRefl _) term

theorem high_part_bound (u v K H A B : PTm n) (hH : Γ ⊢[PRAAx] le (H+H) (succ K))
    (hB : Γ ⊢[PRAAx] le one B) (hu : Γ ⊢[PRAAx] coarseCoefficients u A)
    (hv : Γ ⊢[PRAAx] coarseCoefficients v A) (hsu : Γ ⊢[PRAAx] smallCoefficients u H B)
    (hsv : Γ ⊢[PRAAx] smallCoefficients v H B) :
    Γ ⊢[PRAAx] bounded (highPart u v K) (K*(succ K*A)) B := by
  let f := offB GaussianRationalPowerExpansion.termBody
  let x := pairT (succ K) (evaluationData u v K)
  apply sum_bound f K x (succ K*A) B hB
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift
  let a := Syn.shift u
  let b := Syn.shift v
  let L := Syn.shift K
  let J := Syn.shift H
  let P := Syn.shift A
  let Q := Syn.shift B
  let i : PTm (n+1) := var 0
  have hi : Δ ⊢[PRAAx] lt i L := Prf.hyp0
  have hcut : Δ ⊢[PRAAx] le (J+J) (succ L) := by simpa [Δ,J,L,Fm.shift,Syn.shift] using hH.shift.wk
  have leE : Δ ⊢[PRAAx] le (succ L+i) (L+L) :=
    le_congr ((add_comm (succ i) L).eqTrans ((add_succ L i).eqTrans (succ_add L i).eqSymm))
      (.eqRefl _) (add_le_add_right L hi)
  have leB : Δ ⊢[PRAAx] le one Q := by simpa [Δ,Q,Fm.shift,Syn.shift] using hB.shift.wk
  have ca : Δ ⊢[PRAAx] coarseCoefficients a P := by simpa [Δ,a,P,Fm.shift,Syn.shift] using hu.shift.wk
  have cb : Δ ⊢[PRAAx] coarseCoefficients b P := by simpa [Δ,b,P,Fm.shift,Syn.shift] using hv.shift.wk
  have sa : Δ ⊢[PRAAx] smallCoefficients a J Q := by simpa [Δ,a,J,Q,Fm.shift,Syn.shift] using hsu.shift.wk
  have sb : Δ ⊢[PRAAx] smallCoefficients b J Q := by simpa [Δ,b,J,Q,Fm.shift,Syn.shift] using hsv.shift.wk
  have r := high_exponent_bound a b L (succ L+i) J P Q leE (le_trans hcut (le_add_right _ _)) leB ca cb sa sb
  simpa only [Δ,x,a,b,L,J,P,Q,i,f,Syn.shift,subst_pairT,subst_evaluationData,PTm.subst_mul,
    ConciseIPRA.PTm.subst_succ] using (bound_congr (high_part_term a b L i hi).eqSymm (.eqRefl _) (.eqRefl _) r)

/-- Past twice the disk radius, individual original factorial majorants decrease. -/
theorem term_order (R N i : PTm n) (hR : Γ ⊢[PRAAx] le (R+R) N) (hi : Γ ⊢[PRAAx] le N i) :
    Γ ⊢[PRAAx] le (pw R i*fact N) (pw R N*fact i) := by
  let t := monus i N
  have e := eq_add_of_le hi
  have h := ExponentialTail.ratio_inv hR t
  have r : Γ ⊢[PRAAx] le (two*(pw R (N+t)*fact N)) (two*(pw R N*fact (N+t))) := by
    ipra_le sl h+𝔟 (ExponentialTail.tsum N R t)*𝔟 (fact N)
  exact le_congr (congrMul (congrAp2 powF e.eqSymm (.eqRefl _)) (.eqRefl _))
    (congrMul (.eqRefl _) (congrAp2 factF e.eqSymm (.eqRefl zero)))
    (RationalValueBounds.positive_cancel (le_succ_self one) r)

def growthExponent (R : PTm n) : PTm n := R*(R+R)
def coarse (R : PTm n) : PTm n := pw two (growthExponent R)
def smallDen (p : PTm n) : PTm n := pw two (p+num 4)

theorem term_coarse_bound (R i : PTm n) (hR : Γ ⊢[PRAAx] le one R) :
    Γ ⊢[PRAAx] le (pw R i) (coarse R*fact i) := by
  have base : Γ ⊢[PRAAx] le (pw R (R+R)) (coarse R) := ExponentialTail.pow_bound R
  have pos := GaussianRationalPolynomialExponential.factorial_positive (Γ := Γ) i
  refine .orE (le_total i (R+R)) ?_ ?_
  · have bound := le_trans (GaussianFactorBudget.power_monotone_length R i (R+R) hR.wk Prf.hyp0) base.wk
    ipra_le sl bound+𝔟 (coarse R)*sl pos.wk
  · have prev := term_order (Γ := le (R+R) i :: Γ) R (R+R) i (le_refl _) Prf.hyp0
    have basePos := GaussianRationalPolynomialExponential.factorial_positive (Γ := le (R+R) i :: Γ) (R+R)
    ipra_le sl prev+𝔟 (pw R i)*sl basePos+𝔟 (fact i)*sl base.wk

theorem term_dyadic_bound (R p i : PTm n) (hi : Γ ⊢[PRAAx] le (ExponentialTail.Nt R p) i) :
    Γ ⊢[PRAAx] le (smallDen p*pw R i) (fact i) := by
  let N := ExponentialTail.Nt R p
  let D := smallDen p
  have lower : Γ ⊢[PRAAx] le (R+R) N := le_add_right _ _
  have term := term_order R N i lower hi
  have D' : Γ ⊢[PRAAx] D ≐ pw two (succ (succ (succ (succ p)))) :=
    congrAp2 powF (by ipra_ring) (.eqRefl _)
  have base := le_congr (congrMul D'.eqSymm (.eqRefl (pw R N))) (.eqRefl (fact N))
    (ExponentialTail.first_term (Γ := Γ) R p)
  have all : Γ ⊢[PRAAx] le (fact N*(D*pw R i)) (fact N*fact i) := by
    ipra_le 𝔟 D*sl term+𝔟 (fact i)*sl base
  exact RationalValueBounds.positive_cancel (GaussianRationalPolynomialExponential.factorial_positive N) all

ipra_subst growthExponent
ipra_subst coarse
ipra_subst smallDen

theorem coarse_coefficients (q R : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hq : Γ ⊢[PRAAx] bounded q R one) :
    Γ ⊢[PRAAx] coarseCoefficients q (coarse R) := by
  refine .allI ?_
  let Q := Syn.shift q
  let T := Syn.shift R
  let i : PTm (n+1) := var 0
  have hR' : Γ.map Fm.shift ⊢[PRAAx] le one T := by simpa [T,Fm.shift,Syn.shift] using hR.shift
  have hq' : Γ.map Fm.shift ⊢[PRAAx] bounded Q T one := by simpa [Q,T,Fm.shift,Syn.shift] using hq.shift
  have h := GaussianRationalExponentialTail.term_bound Q T i hq'
  have b : Γ.map Fm.shift ⊢[PRAAx] bounded (coefficient Q i) (coarse T) one :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
      (GaussianRationalPolynomialExponential.factorial_positive i) (le_refl _)
      (le_congr (by ipra_ring) (.eqRefl _) (term_coarse_bound T i hR')) h
  simpa only [Q,T,i,Syn.shift,subst_coarse] using b

theorem small_coefficients (q R p : PTm n) (hq : Γ ⊢[PRAAx] bounded q R one) :
    Γ ⊢[PRAAx] smallCoefficients q (ExponentialTail.Nt R p) (smallDen p) := by
  refine .allI (.impI ?_)
  let Q := Syn.shift q
  let T := Syn.shift R
  let P := Syn.shift p
  let i : PTm (n+1) := var 0
  let Δ := le (ExponentialTail.Nt T P) i :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (ExponentialTail.Nt T P) i := Prf.hyp0
  have hq' : Δ ⊢[PRAAx] bounded Q T one := by simpa [Δ,Q,T,Fm.shift,Syn.shift] using hq.shift.wk
  have h := GaussianRationalExponentialTail.term_bound Q T i hq'
  have b := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (GaussianRationalPolynomialExponential.factorial_positive i)
    (GaussianFactorBudget.power_positive two _ (le_succ_self one))
    (le_congr (mul_comm (smallDen P) (pw T i)) (one_mul _).eqSymm (term_dyadic_bound T P i hi)) h
  simpa [Δ,Q,T,P,i,Fm.shift,Syn.shift,coefficient,smallDen,ExponentialTail.Nt] using b

def reserve (R p : PTm n) : PTm n := growthExponent R + (R+R) + p + num 40
def rectangleCutoff (R p : PTm n) : PTm n := num 16*reserve R p
def innerDemand (R p : PTm n) : PTm n := num 4*reserve R p

theorem degree_budget (R p : PTm n) : Γ ⊢[PRAAx]
    le (ExponentialTail.Nt R (innerDemand R p)+ExponentialTail.Nt R (innerDemand R p)) (succ (rectangleCutoff R p)) := by
  unfold rectangleCutoff innerDemand reserve growthExponent
  ipra_le 6*𝔟 (R*(R+R))+12*𝔟 R+8*𝔟 p+313

theorem count_budget (R p : PTm n) : Γ ⊢[PRAAx]
    le (rectangleCutoff R p*(succ (rectangleCutoff R p)*coarse R)*pw two p) (smallDen (innerDemand R p)) := by
  let J := reserve R p
  let K := rectangleCutoff R p
  let F := pw two (J+num 16)
  let G := growthExponent R
  have hK0 : Γ ⊢[PRAAx] le (succ K) (num 16*pw two J) := by
    have h := Foundations.DyadicGain.amplitude_reserve (Γ := Γ) J
    change Γ ⊢[PRAAx] le (succ (num 16*J)) (num 16*pw two J)
    ipra_le 16*sl h+15
  have hK : Γ ⊢[PRAAx] le (succ K) F := le_trans hK0
    (le_congr (.eqRefl _) ((mul_comm _ _).eqTrans (pw_add two J (num 16)).eqSymm)
      (mul_le_mul_right (pw two J) (Foundations.DyadicGain.amplitude_absorb (num 16))))
  have hF := le_mul_mono
    (le_mul_mono (le_trans (le_succ_self K) hK) (le_mul_mono hK (le_refl (coarse R))))
    (le_refl (pw two p))
  have e : Γ ⊢[PRAAx] le ((J+num 16)+((J+num 16)+G)+p) (innerDemand R p+num 4) := by
    unfold innerDemand
    change Γ ⊢[PRAAx] le ((J+num 16)+((J+num 16)+G)+p) (num 4*J+num 4)
    dsimp [J,G,reserve]
    ipra_le 𝔟 (growthExponent R)+4*𝔟 R+𝔟 p+52
  exact le_trans (le_congr (.eqRefl _)
    ((congrMul ((congrMul (.eqRefl F) (pw_add two (J+num 16) G).eqSymm).eqTrans
      (pw_add two (J+num 16) ((J+num 16)+G)).eqSymm) (.eqRefl _)).eqTrans
        (pw_add two ((J+num 16)+((J+num 16)+G)) p).eqSymm) hF)
    (GaussianFactorBudget.power_monotone_length two _ _ (le_succ_self one) e)

/-- The actual high-degree part is at most the requested dyadic error. -/
theorem actual_high_part_dyadic (u v R p : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hu : Γ ⊢[PRAAx] bounded u R one) (hv : Γ ⊢[PRAAx] bounded v R one) :
    Γ ⊢[PRAAx] bounded (highPart u v (rectangleCutoff R p)) one (pw two p) := by
  have b := GaussianFactorBudget.power_positive (Γ := Γ) two (innerDemand R p+num 4) (le_succ_self one)
  have h := high_part_bound u v (rectangleCutoff R p) (ExponentialTail.Nt R (innerDemand R p))
    (coarse R) (smallDen (innerDemand R p)) (degree_budget R p) b (coarse_coefficients u R hR hu)
    (coarse_coefficients v R hR hv) (small_coefficients u R _ hu) (small_coefficients v R _ hv)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ b
    (GaussianFactorBudget.power_positive two p (le_succ_self one))
    (le_congr (.eqRefl _) (one_mul _).eqSymm (count_budget R p)) h

theorem actual_scalar_product_dyadic (u v R p : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hu : Γ ⊢[PRAAx] bounded u R one) (hv : Γ ⊢[PRAAx] bounded v R one) :
    Γ ⊢[PRAAx] distanceBounded
      (qmul (GaussianRationalPolynomialExponential.scalarSum u (rectangleCutoff R p))
        (GaussianRationalPolynomialExponential.scalarSum v (rectangleCutoff R p)))
      (GaussianRationalPolynomialExponential.scalarSum (GaussianRationalHorner.qadd u v) (rectangleCutoff R p))
      one (pw two p) := by
  let K := rectangleCutoff R p
  have eq := GaussianScalarExponentialProductLowDegrees.exact_rectangular_product_split (Γ := Γ) u v K
  have can : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (highPart u v K) :=
    GaussianRationalFiniteSum.sum_canonical _ _ _
  have diff := (GaussianRationalSyntheticDivision.qsub_congr eq (.eqRefl _)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_sub_cancel _ _ can)
  exact bound_congr diff.eqSymm (.eqRefl _) (.eqRefl _) (actual_high_part_dyadic u v R p hR hu hv)

theorem actual_rectangular_degree_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (ExponentialTail.Nt (var 0) (innerDemand (var 0) (var 1))+
      ExponentialTail.Nt (var 0) (innerDemand (var 0) (var 1))) (succ (rectangleCutoff (var 0) (var 1)))) :=
  closeUniv 2 (degree_budget _ _)

theorem actual_rectangular_count_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (rectangleCutoff (var 0) (var 1)*(succ (rectangleCutoff (var 0) (var 1))*coarse (var 0))*pw two (var 1))
      (smallDen (innerDemand (var 0) (var 1)))) :=
  closeUniv 2 (count_budget _ _)

theorem original_rectangular_exponential_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ bounded (var 0) (var 2) one ⟶ bounded (var 1) (var 2) one ⟶
      distanceBounded
        (qmul (GaussianRationalPolynomialExponential.scalarSum (var 0) (rectangleCutoff (var 2) (var 3)))
          (GaussianRationalPolynomialExponential.scalarSum (var 1) (rectangleCutoff (var 2) (var 3))))
        (GaussianRationalPolynomialExponential.scalarSum (GaussianRationalHorner.qadd (var 0) (var 1))
          (rectangleCutoff (var 2) (var 3))) one (pw two (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (actual_scalar_product_dyadic _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianScalarExponentialProductTail
