import IPRADerivations.Analysis.GaussianEulerQuadraticCutoffComparison

/-!
# The cofinal sampled Jacobian integral for quadratic Euler substitution

The actual sampler evaluates the compact quadratic pullback on computed
rational cutoffs. Its radius pays both omitted tails and yields exact
independent observation errors against the original Euler improper name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerQuadraticImproperJacobian

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerQuadraticCutoffGeometry (source)
open GaussianEulerQuadraticImproperSchedule (threshold index)
open GaussianEulerQuadraticCutoffComparison (jacobianData gain denominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (rate_at rateNumerator rateDenominator)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

abbrev data (z R B A c d : PTm n) : PTm n := GaussianEulerIncompleteName.data z R B A c d
def sample (p z R B A c d : PTm n) : PTm n :=
  ap2 GaussianEulerSquareJacobianCompactName.nameF (succ p) (jacobianData (index p A one c d) z R B A c d)

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p z R B A c d : PTm n) :
    Syn.subst σ (sample p z R B A c d) = sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ c) (Syn.subst σ d) := by simp [sample]

private def fields (p x : PTm n) : Fin 7 → PTm n :=
  ![p, fstT (fstT x), sndT (fstT x), fstT (fstT (sndT x)), sndT (fstT (sndT x)),
    fstT (sndT (sndT x)), sndT (sndT (sndT x))]
private def body : PTm 7 := sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
def reader (f : PTm 7) (p x : PTm n) : PTm n := Syn.subst (fields p x) f
def nameF : PR 2 := PTm.toPR (reader body (var 0) (var 1))

private theorem decoded_values (p z R B A c d : PTm n) (i : Fin 7) :
    Γ ⊢[PRAAx] fields p (data z R B A c d) i ≐ (![p,z,R,B,A,c,d] : Fin 7 → PTm n) i := by
  let x := data z R B A c d
  have head : Γ ⊢[PRAAx] fstT x ≐ pairT z R := fst_pair _ _
  have tail : Γ ⊢[PRAAx] sndT x ≐ pairT (pairT B A) (pairT c d) := snd_pair _ _
  have middle : Γ ⊢[PRAAx] fstT (sndT x) ≐ pairT B A := (congrFst tail).eqTrans (fst_pair _ _)
  have last : Γ ⊢[PRAAx] sndT (sndT x) ≐ pairT c d := (congrSnd tail).eqTrans (snd_pair _ _)
  fin_cases i
  · exact .eqRefl _
  · exact (congrFst head).eqTrans (fst_pair _ _)
  · exact (congrSnd head).eqTrans (snd_pair _ _)
  · exact (congrFst middle).eqTrans (fst_pair _ _)
  · exact (congrSnd middle).eqTrans (snd_pair _ _)
  · exact (congrFst last).eqTrans (fst_pair _ _)
  · exact (congrSnd last).eqTrans (snd_pair _ _)

theorem reader_at (f : PTm 7) (p z R B A c d : PTm n) : Γ ⊢[PRAAx]
    ap2 (PTm.toPR (reader f (var 0) (var 1))) p (data z R B A c d) ≐
      Syn.subst (![p,z,R,B,A,c,d] : Fin 7 → PTm n) f := by
  let x := data z R B A c d
  have substReader : Syn.subst (![p,x] : Fin 2 → PTm n) (reader f (var 0) (var 1)) = reader f p x := by
    unfold reader
    rw [Syn.subst_subst]
    congr 1
    funext i
    fin_cases i <;> simp [fields]
  have readback : Γ ⊢[PRAAx] ap2 (PTm.toPR (reader f (var 0) (var 1))) p x ≐ reader f p x := by
    simpa only [ap2,substReader] using toPR_eq (Γ := Γ) (reader f (var 0) (var 1) : PTm 2) ![p,x]
  exact readback.eqTrans (Prf.eqCongr f (decoded_values p z R B A c d))

theorem name_at (p z R B A c d : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B A c d) ≐ sample p z R B A c d := by
  have decode : Syn.subst (![p,z,R,B,A,c,d] : Fin 7 → PTm n) body = sample p z R B A c d := by
    simp only [body,subst_sample,Syn.subst_var]
    rfl
  simpa only [nameF,decode] using reader_at body p z R B A c d

theorem observation_budget (L H p q : PTm n) (h : Γ ⊢[PRAAx] le (L*unit (succ p)) H) :
    Γ ⊢[PRAAx] le (rateNumerator L H (succ p) q*(unit p*unit q)) ((unit p+unit q)*rateDenominator H (succ p) q) := by
  have dou : Γ ⊢[PRAAx] unit (succ p) ≐ unit p*two := pw_succ two p
  have paid := le_congr (congrMul (.eqRefl L) dou) (.eqRefl H) h
  have clear : Γ ⊢[PRAAx] le
      ((L*(unit p*two)*unit q+H*(unit p*two+unit q))*(unit p*unit q))
      ((unit p+unit q)*(H*(unit p*two)*unit q)) := by ipra_le (𝔞(unit p)*(𝔞(unit q))^2)*sl paid
  exact le_congr
    (congrMul (congrAdd (congrMul (congrMul (.eqRefl _) dou.eqSymm) (.eqRefl _))
      (congrMul (.eqRefl _) (congrAdd dou.eqSymm (.eqRefl _)))) (.eqRefl _))
    (congrMul (.eqRefl _) (congrMul (congrMul (.eqRefl _) dou.eqSymm) (.eqRefl _))) clear

theorem original_observations (p q z R B A c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B A c d) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B A c d))
      (ap2 GaussianEulerImproperName.nameF q (GaussianEulerImproperName.data z R B A))
      (unit p+unit q) (unit p*unit q) := by
  let k := threshold p A one
  let j := index p A one c d
  have approximate := GaussianEulerQuadraticCutoffComparison.original_jacobian_cutoff_rate k j z R B A c d hs (le_refl j)
  have spend : Γ ⊢[PRAAx] le (gain k j A R*unit (succ p)) (denominator k j A R) :=
    le_congr (congrMul (one_mul _) (.eqRefl _)) (.eqRefl _)
      (GaussianEulerQuadraticImproperSchedule.cutoff_budget p A R one c d)
  have hDen : Γ ⊢[PRAAx] le one (denominator k j A R) := positive_product _ _ (unit_positive _) (unit_positive _)
  exact distance_congr (name_at p z R B A c d).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive _ _ _ hDen)
      (positive_product _ _ (unit_positive p) (unit_positive q)) (observation_budget _ _ p q spend)
      (rate_at _ _ _ _ _ _ (succ p) q approximate))

theorem original_Euler_cross (z R B A c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B A c d) :
    Γ ⊢[PRAAx] crossEquivalent nameF GaussianEulerImproperName.nameF
      (data z R B A c d) (GaussianEulerImproperName.data z R B A) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have h : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) (sh c) (sh d) :=
    by simpa only [Fm.shift,Syn.shift,GaussianEulerQuadraticCutoffGeometry.subst_source,sh] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,GaussianEulerIncompleteName.subst_data,GaussianEulerImproperName.subst_data,Syn.shift,sh] using
    original_observations (var 1) (var 0) (sh z) (sh R) (sh B) (sh A) (sh c) (sh d) h

theorem name_regular (z R B A c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B A c d) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B A c d) := by
  have e := original_Euler_cross z R B A c d hs
  exact cross_trans _ _ _ _ _ _ e (cross_symm _ _ _ _ e)

theorem original_Gamma_cross (z R B A c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B A c d) :
    Γ ⊢[PRAAx] crossEquivalent nameF GaussianGammaReciprocalInverse.gammaF
      (data z R B A c d) (GaussianGammaReciprocalInverse.gammaData z R B A) :=
  cross_trans _ _ _ _ _ _ (original_Euler_cross z R B A c d hs)
    (GaussianEulerIntegralGammaIdentification.original_Euler_integral_is_Gamma z R B A hs.andE₁)

theorem actual_improper_quadratic_Jacobian_is_Gamma_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      crossEquivalent nameF GaussianGammaReciprocalInverse.gammaF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (GaussianGammaReciprocalInverse.gammaData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 6 (.impI (original_Gamma_cross _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerQuadraticImproperJacobian
