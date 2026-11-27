import IPRADerivations.Analysis.Euler.QuadraticSubstitution.Jacobian.GaussianEulerSquareJacobianRate
import IPRADerivations.Analysis.Euler.CompactExhaustion.Grids.GaussianEulerCompactAdditivity

/-!
# An actual compact name of the retimed quadratic Euler Jacobian

The sampler calls the unchanged raw quadratic-Jacobian PR3 evaluator
at its explicit Fast(2*c*T,p) query. Source-derived domain and rate
proofs supply the original compact constructor's sampled modulus.
The raw evaluator and all finite-cell equalities remain unchanged.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSquareJacobianCompactName

open_ipra
open GaussianEulerSquareJacobianRate (rawF rawData rawSample query lipschitz)
open GaussianCompactRiemannName (inside sampledModulus localBody)
open GaussianCompactLogarithmBounds (domain)
open GaussianRationalMetric (distanceBounded)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def fixedData (z B c d T : PTm n) : PTm n := pairT T (rawData z B c d)
def evaluatorTerm (p t y : PTm n) : PTm n := ap3 rawF (query p (fstT y) (fstT (sndT y))) t (sndT y)
def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 0) (var 1) (var 2))
def source (z R B c d a C E T : PTm n) : Fm PTm n :=
  GaussianEulerCompactAdditivity.intervalSource z R B a C E T ⋏ (le one c ⋏ le one d)
def data (z R B c d a C E T : PTm n) : PTm n :=
  GaussianCompactRiemannName.data a C E (lipschitz R E T c d) T (fixedData z B c d T)
abbrev nameF : PR 2 := GaussianCompactRiemannName.nameF evaluatorF

ipra_subst fixedData
ipra_subst evaluatorTerm
ipra_subst source
ipra_subst data

theorem evaluator_at (p t z B c d T : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluatorF p t (fixedData z B c d T) ≐ ap3 rawF (query p T c) t (rawData z B c d) := by
  have read := toPR_pairVector3_eq (Γ := Γ) (k := 1)
    (ap3 rawF (query (var 0) (var 2) (fstT (var 3))) (var 1) (var 3)) p t ![T, rawData z B c d]
  simp only [subst_ap3, GaussianEulerSquareJacobianRate.subst_query, subst_fstT, Syn.subst_var] at read
  refine read.eqTrans (congrAp3 rawF ?_ (.eqRefl t) (.eqRefl _))
  ipra_congr (query (var 0) (var 1) (var 2) : PTm 3) with
    [.eqRefl p, .eqRefl T, fst_pair c _] using [rawData, GaussianRationalQuadratureDilation.pullData]

theorem evaluator_decoded_at (p t z B c d T : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluatorF p t (fixedData z B c d T) ≐ rawSample (query p T c) z B c d (fstT t) (sndT t) :=
  (evaluator_at p t z B c d T).eqTrans (GaussianEulerSquareJacobianRate.raw_decoded_at _ t z B c d)

theorem quadrature_at (p N z B c d a C E T : PTm n) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.quadrature evaluatorF p N a C E (fixedData z B c d T) ≐
      GaussianCompactRiemannName.quadrature rawF (query p T c) N a C E (rawData z B c d) := by
  have rows : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (GaussianCompactRiemannName.sampleBody evaluatorF)
      (GaussianCompactRiemannName.sampleBody rawF) N (GaussianCompactRiemannName.sampleData p N a C E (fixedData z B c d T))
      (GaussianCompactRiemannName.sampleData (query p T c) N a C E (rawData z B c d)) := by
    refine .allI (.impI ?_)
    simpa only [GaussianRationalFiniteSum.termsEqual,GaussianCompactRiemannName.subst_sampleData,subst_fixedData,
      GaussianEulerSquareJacobianRate.subst_query,GaussianEulerSquareJacobianRate.subst_rawData,Syn.shift] using
      ((GaussianCompactRiemannName.sample_body_at (Γ := _ :: Γ.map Fm.shift) evaluatorF (var 0) (Syn.shift p) (Syn.shift N)
        (Syn.shift a) (Syn.shift C) (Syn.shift E) (fixedData (Syn.shift z) (Syn.shift B) (Syn.shift c) (Syn.shift d) (Syn.shift T))).eqTrans
          ((evaluator_at (Syn.shift p) (GaussianCompactRiemannName.grid (var 0) (Syn.shift N) (Syn.shift a) (Syn.shift C) (Syn.shift E))
            (Syn.shift z) (Syn.shift B) (Syn.shift c) (Syn.shift d) (Syn.shift T)).eqTrans
              (GaussianCompactRiemannName.sample_body_at rawF (var 0) (query (Syn.shift p) (Syn.shift T) (Syn.shift c)) (Syn.shift N)
                (Syn.shift a) (Syn.shift C) (Syn.shift E) (rawData (Syn.shift z) (Syn.shift B) (Syn.shift c) (Syn.shift d))).eqSymm))
  exact GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _)
    (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ rows)

theorem wrapped_at (p t z B c d T : PTm n) : Γ ⊢[PRAAx]
    ap2 (GaussianCompactRiemannName.evaluatorName evaluatorF) p
      (GaussianCompactRiemannName.nameData t (fixedData z B c d T)) ≐ rawSample (query p T c) z B c d (fstT t) (sndT t) :=
  (GaussianCompactRiemannName.evaluator_at evaluatorF p t _).eqTrans (evaluator_decoded_at p t z B c d T)

theorem wrapped_rate (z R B E T c d t u A D : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerSquareTimeGeometry.source z R B E c d)
    (ht : Γ ⊢[PRAAx] domain (fstT t) (sndT t) E T) (hu : Γ ⊢[PRAAx] domain (fstT u) (sndT u) E T)
    (hD : Γ ⊢[PRAAx] le one D)
    (near : Γ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) A D) : Γ ⊢[PRAAx]
    independentRate (GaussianCompactRiemannName.evaluatorName evaluatorF) (GaussianCompactRiemannName.evaluatorName evaluatorF)
      (GaussianCompactRiemannName.nameData t (fixedData z B c d T)) (GaussianCompactRiemannName.nameData u (fixedData z B c d T))
      (lipschitz R E T c d*A) D := by
  let sh := fun x : PTm n => Syn.shift (Syn.shift x)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] GaussianEulerSquareTimeGeometry.source (sh z) (sh R) (sh B) (sh E) (sh c) (sh d) := by
    simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  have ts : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] domain (fstT (sh t)) (sndT (sh t)) (sh E) (sh T) := by simpa [Fm.shift,Syn.shift,sh] using ht.shift.shift
  have us : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] domain (fstT (sh u)) (sndT (sh u)) (sh E) (sh T) := by simpa [Fm.shift,Syn.shift,sh] using hu.shift.shift
  have ds : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (sh D) := by simpa [Fm.shift,Syn.shift,sh] using hD.shift.shift
  have ns : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] distanceBounded
      (GaussianPositiveRationalLogarithm.fraction (fstT (sh t)) (sndT (sh t)))
      (GaussianPositiveRationalLogarithm.fraction (fstT (sh u)) (sndT (sh u))) (sh A) (sh D) := by
    simpa [Fm.shift,Syn.shift,sh,GaussianCompactRiemannName.value,GaussianPositiveRationalLogarithm.fraction] using near.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,GaussianCompactRiemannName.subst_nameData,subst_fixedData,
    GaussianEulerSquareJacobianRate.subst_lipschitz,PTm.subst_mul,Syn.shift,sh] using
    distance_congr (wrapped_at (var 1) (sh t) (sh z) (sh B) (sh c) (sh d) (sh T)).eqSymm
      (wrapped_at (var 0) (sh u) (sh z) (sh B) (sh c) (sh d) (sh T)).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianEulerSquareJacobianRate.retimed_observations (var 1) (var 0) (sh z) (sh R) (sh B) (sh E) (sh T)
        (sh c) (sh d) (fstT (sh t)) (sndT (sh t)) (fstT (sh u)) (sndT (sh u)) (sh A) (sh D) hs ts us ds ns)

theorem local_modulus_at (z R B c d a C E T t u A D : PTm n) (h : Γ ⊢[PRAAx] source z R B c d a C E T)
    (hD : Γ ⊢[PRAAx] le one D) (ht : Γ ⊢[PRAAx] inside a C E t) (hu : Γ ⊢[PRAAx] inside a C E u)
    (near : Γ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) A D) : Γ ⊢[PRAAx]
    independentRate (GaussianCompactRiemannName.evaluatorName evaluatorF) (GaussianCompactRiemannName.evaluatorName evaluatorF)
      (GaussianCompactRiemannName.nameData t (fixedData z B c d T)) (GaussianCompactRiemannName.nameData u (fixedData z B c d T))
      (lipschitz R E T c d*A) D :=
  wrapped_rate z R B E T c d t u A D (.andI h.andE₁.andE₁ h.andE₂)
    (GaussianEulerCompactAdditivity.domain_of_inside t a C E T h.andE₁.andE₂.andE₁ h.andE₁.andE₁.andE₂.andE₁ h.andE₁.andE₂.andE₂ ht)
    (GaussianEulerCompactAdditivity.domain_of_inside u a C E T h.andE₁.andE₂.andE₁ h.andE₁.andE₁.andE₂.andE₁ h.andE₁.andE₂.andE₂ hu) hD near

theorem sampled_modulus (z R B c d a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B c d a C E T) : Γ ⊢[PRAAx]
    sampledModulus evaluatorF a C E (lipschitz R E T c d) (fixedData z B c d T) := by
  let sh := fun x : PTm n => Syn.shift (Syn.shift (Syn.shift (Syn.shift x)))
  have hs : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      source (sh z) (sh R) (sh B) (sh c) (sh d) (sh a) (sh C) (sh E) (sh T) := by simpa [Fm.shift,Syn.shift,sh] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [localBody,subst_fixedData,GaussianEulerSquareJacobianRate.subst_lipschitz,Syn.shift,sh] using
    local_modulus_at (sh z) (sh R) (sh B) (sh c) (sh d) (sh a) (sh C) (sh E) (sh T)
      (var 3) (var 2) (var 1) (var 0) hs.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem compact_input (z R B c d a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B c d a C E T) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.input evaluatorF a C E (lipschitz R E T c d) T (fixedData z B c d T) :=
  .andI h.andE₁.andE₂.andE₁ (.andI h.andE₁.andE₁.andE₂.andE₁
    (.andI (le_trans (le_add_left C a) h.andE₁.andE₂.andE₂) (sampled_modulus z R B c d a C E T h)))

theorem name_regular (z R B c d a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B c d a C E T) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN nameF (data z R B c d a C E T) :=
  GaussianCompactRiemannName.name_regular evaluatorF _ _ _ _ _ _ (compact_input z R B c d a C E T h)

theorem name_at (p z R B c d a C E T : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B c d a C E T) ≐ GaussianCompactRiemannName.quadrature evaluatorF
      (GaussianCompactRiemannName.precision p T) (GaussianCompactRiemannName.mesh p (lipschitz R E T c d) T)
      a C E (fixedData z B c d T) := GaussianCompactRiemannName.name_at evaluatorF p _ _ _ _ _ _

theorem name_raw_at (p z R B c d a C E T : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B c d a C E T) ≐ GaussianCompactRiemannName.quadrature rawF
      (query (GaussianCompactRiemannName.precision p T) T c) (GaussianCompactRiemannName.mesh p (lipschitz R E T c d) T)
      a C E (rawData z B c d) :=
  (name_at p z R B c d a C E T).eqTrans (quadrature_at _ _ z B c d a C E T)

theorem actual_retimed_quadratic_Euler_compact_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      GaussianEuclideanDistanceName.pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))) :=
  closeUniv 9 (.impI (name_regular _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerSquareJacobianCompactName
