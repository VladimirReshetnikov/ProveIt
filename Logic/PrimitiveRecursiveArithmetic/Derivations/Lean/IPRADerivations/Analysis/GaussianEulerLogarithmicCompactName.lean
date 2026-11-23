import IPRADerivations.Analysis.GaussianEulerLogarithmicMultiplier

/-!
# Constructive compact quadrature for every numerical logarithmic order

A computed observation clock pays the genuine logarithmic multiplier
error. The actual PR3 evaluator retains the original Euler and logarithm
programs at that clock. Original compact guards alone give its sampled
modulus and the existing actual compact quadrature name. No improper
tail or differentiability assertion is assumed or claimed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCompactName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicMultiplier (observationCost lipschitz majorant)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNamedInverseRate (rateNumerator rateDenominator independentRate denominator_positive)
open GaussianCompactLogarithmBounds (domain)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def query (p j R E T : PTm n) : PTm n := GaussianFastValueCut.exponent (observationCost j R E T) p
def sample (p j R E T z B a b : PTm n) : PTm n := GaussianEulerLogarithmicMultiplier.sample (query p j R E T) j z B a b
def fixedData (j R E T z B : PTm n) : PTm n := pairT (pairT j (pairT R E)) (pairT T (pairT z B))
def evaluatorTerm (p t x : PTm n) : PTm n := sample p (fstT (fstT x)) (fstT (sndT (fstT x))) (sndT (sndT (fstT x)))
  (fstT (sndT x)) (fstT (sndT (sndT x))) (sndT (sndT (sndT x))) (fstT t) (sndT t)
def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 0) (var 1) (var 2))
def source (z R B E T C : PTm n) : Fm PTm n := GaussianEulerCompactModulus.source z R B E T C
def data (j z R B E T C : PTm n) : PTm n := GaussianCompactRiemannName.data one C E (lipschitz j R E T) T (fixedData j R E T z B)
def nameF : PR 2 := GaussianCompactRiemannName.nameF evaluatorF

@[simp] theorem subst_query {m : ℕ} (σ : Fin n → PTm m) (p j R E T : PTm n) :
    Syn.subst σ (query p j R E T) = query (Syn.subst σ p) (Syn.subst σ j) (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by simp [query]
@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p j R E T z B a b : PTm n) :
    Syn.subst σ (sample p j R E T z B a b) = sample (Syn.subst σ p) (Syn.subst σ j) (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T)
      (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [sample]
@[simp] theorem subst_fixedData {m : ℕ} (σ : Fin n → PTm m) (j R E T z B : PTm n) :
    Syn.subst σ (fixedData j R E T z B) = fixedData (Syn.subst σ j) (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ z) (Syn.subst σ B) := by simp [fixedData]
@[simp] theorem subst_evaluatorTerm {m : ℕ} (σ : Fin n → PTm m) (p t x : PTm n) :
    Syn.subst σ (evaluatorTerm p t x) = evaluatorTerm (Syn.subst σ p) (Syn.subst σ t) (Syn.subst σ x) := by simp [evaluatorTerm]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B E T C : PTm n) :
    (source z R B E T C).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ C) := by simp [source]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (j z R B E T C : PTm n) :
    Syn.subst σ (data j z R B E T C) = data (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ C) := by simp [data]

theorem query_budget (p j R E T : PTm n) : Γ ⊢[PRAAx] le (observationCost j R E T*unit p) (unit (query p j R E T)) :=
  GaussianFastValueCut.query_budget _ _

theorem evaluator_at (p t x : PTm n) : Γ ⊢[PRAAx] ap3 evaluatorF p t x ≐ evaluatorTerm p t x := by
  simpa [evaluatorF,ap3] using toPR_eq (Γ := Γ) (evaluatorTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]

theorem sample_at (p j R E T z B a b : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluatorF p (pairT a b) (fixedData j R E T z B) ≐ sample p j R E T z B a b := by
  refine (evaluator_at p (pairT a b) (fixedData j R E T z B)).eqTrans ?_
  simpa [evaluatorTerm,fixedData] using
    Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) : PTm 9)
      (σ := ![p,fstT (fstT (fixedData j R E T z B)),fstT (sndT (fstT (fixedData j R E T z B))),sndT (sndT (fstT (fixedData j R E T z B))),
        fstT (sndT (fixedData j R E T z B)),fstT (sndT (sndT (fixedData j R E T z B))),sndT (sndT (sndT (fixedData j R E T z B))),fstT (pairT a b),sndT (pairT a b)])
      (σ' := ![p,j,R,E,T,z,B,a,b]) (fun i => by
        fin_cases i
        exact .eqRefl _
        exact (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
        exact (congrFst (congrSnd (fst_pair _ _))).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
        exact (congrSnd (congrSnd (fst_pair _ _))).eqTrans ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
        exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
        exact (congrFst (congrSnd (snd_pair _ _))).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
        exact (congrSnd (congrSnd (snd_pair _ _))).eqTrans ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
        exact fst_pair _ _
        exact snd_pair _ _)

theorem raw_evaluator_at (p t j R E T z B : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluatorF p t (fixedData j R E T z B) ≐ sample p j R E T z B (fstT t) (sndT t) := by
  refine (evaluator_at p t (fixedData j R E T z B)).eqTrans ?_
  simpa [evaluatorTerm,fixedData] using
    Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) : PTm 9)
      (σ := ![p,fstT (fstT (fixedData j R E T z B)),fstT (sndT (fstT (fixedData j R E T z B))),sndT (sndT (fstT (fixedData j R E T z B))),
        fstT (sndT (fixedData j R E T z B)),fstT (sndT (sndT (fixedData j R E T z B))),sndT (sndT (sndT (fixedData j R E T z B))),fstT t,sndT t])
      (σ' := ![p,j,R,E,T,z,B,fstT t,sndT t]) (fun i => by
        fin_cases i
        exact .eqRefl _
        exact (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
        exact (congrFst (congrSnd (fst_pair _ _))).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
        exact (congrSnd (congrSnd (fst_pair _ _))).eqTrans ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
        exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
        exact (congrFst (congrSnd (snd_pair _ _))).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
        exact (congrSnd (congrSnd (snd_pair _ _))).eqTrans ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
        exact .eqRefl _
        exact .eqRefl _)

/-- The computed query pays both independent observation errors without
changing the genuine compact Lipschitz factor. -/
theorem original_variation (p q j z R B E T a b c d A D : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.input z R B E T a b c d A D) : Γ ⊢[PRAAx]
    distanceBounded (sample p j R E T z B a b) (sample q j R E T z B c d)
      (rateNumerator (lipschitz j R E T*A) D p q) (rateDenominator D p q) := by
  let P := query p j R E T
  let Q := query q j R E T
  have hD := h.andE₂.andE₂.andE₂.andE₁
  have raw := GaussianEulerLogarithmicMultiplier.original_variation P Q j z R B E T a b c d A D h
  apply distance_radius_mono _ _ _ _ _ _ (denominator_positive D P Q hD) (denominator_positive D p q hD) _ raw
  dsimp only [GaussianEulerLogarithmicMultiplier.numerator,rateNumerator,rateDenominator]
  ipra_le (𝔞 D*𝔞 D*𝔞(unit q)*𝔞(unit Q))*sl (query_budget (Γ := Γ) p j R E T)+
    (𝔞 D*𝔞 D*𝔞(unit p)*𝔞(unit P))*sl (query_budget (Γ := Γ) q j R E T)

theorem sample_bound (p j z R B E T a b : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerLogarithmicMultiplier.source z R B E T a b) : Γ ⊢[PRAAx]
    bounded (sample p j R E T z B a b) (majorant j R E T) one :=
  GaussianEulerLogarithmicMultiplier.original_sample_bound (query p j R E T) j z R B E T a b h

theorem wrapped_at (p t j R E T z B : PTm n) : Γ ⊢[PRAAx]
    ap2 (GaussianCompactRiemannName.evaluatorName evaluatorF) p
      (GaussianCompactRiemannName.nameData t (fixedData j R E T z B)) ≐ sample p j R E T z B (fstT t) (sndT t) :=
  (GaussianCompactRiemannName.evaluator_at evaluatorF p t _).eqTrans (raw_evaluator_at p t j R E T z B)

theorem local_modulus_at (j z R B E T C t u A D : PTm n) (h : Γ ⊢[PRAAx] source z R B E T C)
    (hD : Γ ⊢[PRAAx] le one D) (ht : Γ ⊢[PRAAx] GaussianCompactRiemannName.inside one C E t)
    (hu : Γ ⊢[PRAAx] GaussianCompactRiemannName.inside one C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) A D) : Γ ⊢[PRAAx]
    independentRate (GaussianCompactRiemannName.evaluatorName evaluatorF) (GaussianCompactRiemannName.evaluatorName evaluatorF)
      (GaussianCompactRiemannName.nameData t (fixedData j R E T z B))
      (GaussianCompactRiemannName.nameData u (fixedData j R E T z B)) (lipschitz j R E T*A) D := by
  have input : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.input z R B E T (fstT t) (sndT t) (fstT u) (sndT u) A D :=
    .andI h.andE₁ (.andI (GaussianEulerCompactModulus.domain_of_inside t C E T h.andE₁.andE₂.andE₁ h.andE₂ ht)
      (.andI (GaussianEulerCompactModulus.domain_of_inside u C E T h.andE₁.andE₂.andE₁ h.andE₂ hu) (.andI hD hd)))
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      GaussianEulerExponentCompactBounds.input (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B))
        (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T)) (fstT (Syn.shift (Syn.shift t))) (sndT (Syn.shift (Syn.shift t)))
        (fstT (Syn.shift (Syn.shift u))) (sndT (Syn.shift (Syn.shift u))) (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift D)) :=
    by simpa [Fm.shift,Syn.shift] using input.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,GaussianCompactRiemannName.subst_nameData,subst_fixedData,GaussianEulerLogarithmicMultiplier.subst_lipschitz,PTm.subst_mul,Syn.shift] using
    distance_congr (wrapped_at (var 1) (Syn.shift (Syn.shift t)) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B))).eqSymm
      (wrapped_at (var 0) (Syn.shift (Syn.shift u)) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift R))
        (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B))).eqSymm
      (.eqRefl _) (.eqRefl _)
      (original_variation (var 1) (var 0) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
        (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T)) (fstT (Syn.shift (Syn.shift t)))
        (sndT (Syn.shift (Syn.shift t))) (fstT (Syn.shift (Syn.shift u))) (sndT (Syn.shift (Syn.shift u)))
        (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift D)) hs)

theorem sampled_modulus (j z R B E T C : PTm n) (h : Γ ⊢[PRAAx] source z R B E T C) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.sampledModulus evaluatorF one C E (lipschitz j R E T) (fixedData j R E T z B) := by
  have hs : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      source (Syn.shift (Syn.shift (Syn.shift (Syn.shift z)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift R))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift B)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift E))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift C)))) :=
    by simpa [Fm.shift,Syn.shift] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [GaussianCompactRiemannName.localBody,subst_fixedData,GaussianEulerLogarithmicMultiplier.subst_lipschitz,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    local_modulus_at (Syn.shift (Syn.shift (Syn.shift (Syn.shift j)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift z))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift R)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift B))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift E)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift T))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift C)))) (var 3) (var 2) (var 1) (var 0)
      hs.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem compact_input (j z R B E T C : PTm n) (h : Γ ⊢[PRAAx] source z R B E T C) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.input evaluatorF one C E (lipschitz j R E T) T (fixedData j R E T z B) :=
  .andI (le_refl one) (.andI h.andE₁.andE₂.andE₁
    (.andI (le_trans (le_add_left C one) h.andE₂) (sampled_modulus j z R B E T C h)))

theorem name_regular (j z R B E T C : PTm n) (h : Γ ⊢[PRAAx] source z R B E T C) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN nameF (data j z R B E T C) :=
  GaussianCompactRiemannName.name_regular evaluatorF _ _ _ _ _ _ (compact_input j z R B E T C h)

theorem name_at (p j z R B E T C : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data j z R B E T C) ≐ GaussianCompactRiemannName.quadrature evaluatorF
      (GaussianCompactRiemannName.precision p T) (GaussianCompactRiemannName.mesh p (lipschitz j R E T) T)
      one C E (fixedData j R E T z B) := GaussianCompactRiemannName.name_at evaluatorF p _ _ _ _ _ _

theorem actual_all_orders_Euler_logarithmic_compact_modulus_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      GaussianCompactRiemannName.sampledModulus evaluatorF one (var 6) (var 4)
        (lipschitz (var 0) (var 2) (var 4) (var 5)) (fixedData (var 0) (var 2) (var 4) (var 5) (var 1) (var 3))) :=
  closeUniv 7 (.impI (sampled_modulus _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_all_orders_Euler_logarithmic_compact_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      GaussianEuclideanDistanceName.pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) :=
  closeUniv 7 (.impI (name_regular _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCompactName
