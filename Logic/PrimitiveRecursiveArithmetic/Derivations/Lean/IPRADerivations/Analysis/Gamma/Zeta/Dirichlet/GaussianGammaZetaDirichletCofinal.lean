import IPRADerivations.Analysis.Gamma.Zeta.Dirichlet.GaussianGammaZetaDirichletFiniteRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate

/-!
# The original cofinal Dirichlet name on Re(s)>1

At precision p the name queries the literal finite Dirichlet prefix
through (2^(p+A+3))^A at precision p+1. The margin A is witnessed by the
original rational chart for s-1.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletCofinal

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaZetaDirichletRowDecay (block block_positive)
open GaussianGammaZetaDirichletFiniteRate (prefixData budget prefix_observations)
open GaussianGammaZetaMellinDampedImproper (dirichletF parameters)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianNamedLipschitzRate (diagonalNumerator diagonalDenominator diagonalEnvelope)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianEulerIntegralGammaIdentification.source

def level (A p : PTm n) : PTm n := p+(A+num 3)
def cutoff (A p : PTm n) : PTm n := block A (level A p)
abbrev data (z R B A : PTm n) : PTm n := parameters z R B A

def sample (p z R B A : PTm n) : PTm n := ap2 dirichletF (succ p) (prefixData (cutoff A p) z R B A)
def nameF : PR 2 :=
  PTm.toPR (sample (var 0) (fstT (fstT (var 1))) (sndT (fstT (var 1)))
    (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)

ipra_subst level
ipra_subst cutoff
ipra_subst sample

theorem sample_at (p z R B A : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data z R B A) ≐ sample p z R B A := by
  let x := data z R B A
  let y := fstT x
  let w := sndT x
  have h := toPR_eq (Γ := Γ)
    (sample (var 0) (fstT (fstT (var 1))) (sndT (fstT (var 1))) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2) ![p,x]
  have e : Γ ⊢[PRAAx] ap2 nameF p x ≐ sample p (fstT y) (sndT y) (fstT w) (sndT w) := by
    simpa only [nameF,ap2,y,w,subst_sample,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val] using h
  have hy : Γ ⊢[PRAAx] y ≐ pairT z R := fst_pair _ _
  have hw : Γ ⊢[PRAAx] w ≐ pairT B A := snd_pair _ _
  have read : Γ ⊢[PRAAx] sample p (fstT y) (sndT y) (fstT w) (sndT w) ≐ sample p z R B A := by
    simpa only [subst_sample,Syn.subst_var,Matrix.cons_val] using
      Prf.eqCongr (sample (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
        (σ := ![p,fstT y,sndT y,fstT w,sndT w]) (σ' := ![p,z,R,B,A])
        (fun i => by fin_cases i
                     · exact .eqRefl p
                     · exact (congrFst hy).eqTrans (fst_pair _ _)
                     · exact (congrSnd hy).eqTrans (snd_pair _ _)
                     · exact (congrFst hw).eqTrans (fst_pair _ _)
                     · exact (congrSnd hw).eqTrans (snd_pair _ _))
  exact e.eqTrans read

private theorem dyadic_successor (p : PTm n) : Γ ⊢[PRAAx] unit (succ p) ≐ two*unit p :=
  GaussianRationalHalfAngleRecovery.unit_succ p

private theorem unit_level (A p : PTm n) : Γ ⊢[PRAAx] unit (level A p) ≐ budget A*unit (succ p) := by
  let X := unit p
  let Y := unit A
  have e0 : Γ ⊢[PRAAx] unit (zero : PTm n) ≐ one := pw_zero two
  have e1 := (dyadic_successor (Γ := Γ) (zero : PTm n)).eqTrans (congrMul (.eqRefl two) e0)
  have e2 := (dyadic_successor (Γ := Γ) (succ zero : PTm n)).eqTrans (congrMul (.eqRefl two) e1)
  have e3 : Γ ⊢[PRAAx] unit (num 3 : PTm n) ≐ num 8 :=
    (dyadic_successor (Γ := Γ) (succ (succ zero) : PTm n)).eqTrans
      ((congrMul (.eqRefl two) e2).eqTrans (by ipra_ring))
  have e := (pw_add (Γ := Γ) two p (A+num 3)).eqTrans
    (congrMul (.eqRefl X) ((pw_add two A (num 3)).eqTrans (congrMul (.eqRefl Y) e3)))
  exact e.eqTrans ((by unfold budget; ipra_ring : Γ ⊢[PRAAx] X*(Y*num 8) ≐ budget A*(two*X)).eqTrans
    (congrMul (.eqRefl _) (dyadic_successor p).eqSymm))

theorem cutoff_positive (A p : PTm n) : Γ ⊢[PRAAx] le one (cutoff A p) := block_positive A (level A p)

private theorem cutoff_monotone (A p q : PTm n) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] le (cutoff A p) (cutoff A q) :=
  pw_le_pw A (GaussianExponentialReference.unit_monotone (add_le_add_right (A+num 3) hpq))

theorem late_observations (p q N z R B A : PTm n) (hz : Γ ⊢[PRAAx] S z R B A)
    (hN : Γ ⊢[PRAAx] le (cutoff A p) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B A))
      (ap2 dirichletF q (prefixData N z R B A)) (unit p+unit q) (unit p*unit q) := by
  let U := unit p
  let V := unit q
  let T := unit (succ p)
  let H := unit (level A p)
  let C := budget A
  have dp := denominator_positive H (succ p) q (unit_positive (Γ := Γ) (level A p))
  have raw := prefix_observations (succ p) q (cutoff A p) N z R B A (level A p) hz (le_refl _) hN
  have move : Γ ⊢[PRAAx] le (rateNumerator C H (succ p) q*(U*V)) ((U+V)*rateDenominator H (succ p) q) := by
    refine le_of_eq_add (d := zero) ?_
    have eh := natEq (unit_level (Γ := Γ) A p)
    have et := natEq (dyadic_successor (Γ := Γ) p)
    apply deriveNat
    dsimp only [rateNumerator,rateDenominator,U,V,H,C,T]
    ipra_simps
    rw [eh,et]
    ring
  exact distance_congr (sample_at p z R B A).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ dp (positive_product _ _ (unit_positive p) (unit_positive q)) move raw)

private theorem lower_second_error (x y p q : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded x y (unit p+unit (succ q)) (unit p*unit (succ q))) :
    Γ ⊢[PRAAx] distanceBounded x y (unit p+unit q) (unit p*unit q) := by
  have hp := unit_positive (Γ := Γ) p
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp (unit_positive (succ q)))
    (positive_product _ _ hp (unit_positive q)) ?_ h
  refine le_of_eq_add (d := unit p*unit p*unit q) ?_
  have eq := natEq (dyadic_successor (Γ := Γ) q)
  apply deriveNat
  ipra_simps
  rw [eq]
  ring

theorem observations (p q z R B A : PTm n) (hz : Γ ⊢[PRAAx] S z R B A) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B A)) (ap2 nameF q (data z R B A))
      (unit p+unit q) (unit p*unit q) := by
  refine (le_total p q).orE ?_ ?_
  · exact lower_second_error _ _ p q
      (distance_congr (.eqRefl _) (sample_at q z R B A).eqSymm (.eqRefl _) (.eqRefl _)
        (late_observations p (succ q) (cutoff A q) z R B A hz.wk (cutoff_monotone A p q Prf.hyp0)))
  · have rev := lower_second_error _ _ q p
      (distance_congr (.eqRefl _) (sample_at p z R B A).eqSymm (.eqRefl _) (.eqRefl _)
        (late_observations q (succ p) (cutoff A p) z R B A hz.wk (cutoff_monotone A q p Prf.hyp0)))
    exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
      (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive p)) rev)

theorem regular (z R B A : PTm n) (hz : Γ ⊢[PRAAx] S z R B A) : Γ ⊢[PRAAx] pointCN nameF (data z R B A) := by
  refine .allI (.allI ?_)
  let sh (x : PTm n) := Syn.shift (Syn.shift x)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] S (sh z) (sh R) (sh B) (sh A) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hz.shift.shift
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,unit,Δ,sh,Syn.shift, data,
    GaussianGammaZetaMellinDampedImproper.subst_parameters] using
    observations (var 1) (var 0) (sh z) (sh R) (sh B) (sh A) hs

private theorem cutoff_diagonal (p N z R B A h : PTm n) (hz : Γ ⊢[PRAAx] S z R B A)
    (hN : Γ ⊢[PRAAx] le (block A h) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 dirichletF p (prefixData N z R B A)) (ap2 nameF p (data z R B A))
      (diagonalNumerator (budget A) (unit h) two p) (diagonalDenominator (unit h) p) := by
  let U := unit p
  let H := unit h
  let C := budget A
  let K := cutoff A p
  have hU := unit_positive (Γ := Γ) p
  have hH := unit_positive (Γ := Γ) h
  have hD := positive_product _ _ hH hU
  refine (le_total K N).orE ?_ ?_
  · have hUU := positive_product _ _ hU hU
    have raw := late_observations p p N z R B A hz.wk Prf.hyp0
    apply distance_radius_mono _ _ _ _ _ _ hUU.wk hD.wk ?_
      (distance_symmetric _ _ _ _ hUU.wk raw)
    exact le_of_eq_add (d := C*U*U*U) (by dsimp only [diagonalNumerator,diagonalDenominator]; ipra_ring)
  · have raw := prefix_observations p (succ p) N K z R B A h hz.wk hN.wk (le_trans hN.wk Prf.hyp0)
    apply distance_congr (.eqRefl _) (sample_at p z R B A).eqSymm (.eqRefl _) (.eqRefl _)
    apply distance_radius_mono _ _ _ _ _ _ (denominator_positive H p (succ p) hH.wk) hD.wk ?_ raw
    refine le_of_eq_add (d := H*H*U*U) ?_
    have eq := natEq (dyadic_successor (Γ := le N K::Γ) p)
    apply deriveNat
    dsimp only [rateNumerator,rateDenominator,diagonalNumerator,diagonalDenominator,U,H,C]
    ipra_simps
    rw [eq]
    ring

theorem cutoff_rate (N z R B A h : PTm n) (hz : Γ ⊢[PRAAx] S z R B A)
    (hN : Γ ⊢[PRAAx] le (block A h) N) :
    Γ ⊢[PRAAx] independentRate dirichletF nameF (prefixData N z R B A) (data z R B A) (budget A) (unit h) := by
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ two (unit_positive h)
    (GaussianGammaZetaMellinDampedImproper.dirichlet_regular _ _ _ _ _
      (GaussianGammaZetaDirichletPowerOrder.shifted_source z R B A hz)) (regular z R B A hz)
  refine .allI ?_
  let sh (x : PTm n) := Syn.shift x
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] S (sh z) (sh R) (sh B) (sh A) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hz.shift
  have hc : Δ ⊢[PRAAx] le (block (sh A) (sh h)) (sh N) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hN.shift
  simpa [diagonalEnvelope,Syn.shift,sh,Δ,two,one,data,prefixData] using
    cutoff_diagonal (var 0) (sh N) (sh z) (sh R) (sh B) (sh A) (sh h) hs hc

theorem actual_original_Dirichlet_cutoff_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (S (var 1) (var 2) (var 3) (var 4) ⟶ le (block (var 4) (var 5)) (var 0) ⟶
      independentRate dirichletF nameF (prefixData (var 0) (var 1) (var 2) (var 3) (var 4))
        (data (var 1) (var 2) (var 3) (var 4)) (budget (var 4)) (unit (var 5))) :=
  closeUniv 6 (.impI (.impI (cutoff_rate _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletCofinal
