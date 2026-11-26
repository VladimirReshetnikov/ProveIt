import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicIntervalName

/-!
# Logarithmic interval names with independent geometry and client guards

The numerical interval denominator G need not equal the evaluator's
compact lower guard E. Explicit original interval inequalities derive
both actual time domains. This preserves the original fixed evaluator
client when interval encodings are rescaled, and supplies the exact
source-only inputs needed for comparison of different clients.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicClientIntervalName

open_ipra
open GaussianEulerLogarithmicCompactName (evaluatorF fixedData wrapped_at original_variation)
open GaussianEulerLogarithmicMultiplier (lipschitz)
open GaussianCompactRiemannName (inside sampledModulus localBody)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev nameF : PR 2 := GaussianEulerLogarithmicCompactName.nameF
def source (z R B a C G E T : PTm n) : Fm PTm n :=
  GaussianEulerExponentCompactBounds.source z R B E ⋏
    (le one a ⋏ (le one G ⋏ (le G (E*a) ⋏ le (a+C) (G*T))))
def data (j z R B a C G E T : PTm n) : PTm n :=
  GaussianCompactRiemannName.data a C G (lipschitz j R E T) T (fixedData j R E T z B)
ipra_subst source
ipra_subst data

theorem domain_of_inside (z R B a C G E T t : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C G E T) (ht : Γ ⊢[PRAAx] inside a C G t) : Γ ⊢[PRAAx]
    GaussianCompactLogarithmBounds.domain (fstT t) (sndT t) E T := by
  have first := mul_le_mul_right (sndT t) h.andE₂.andE₂.andE₂.andE₁
  have second : Γ ⊢[PRAAx] le ((E*a)*sndT t) (G*(E*fstT t)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right E ht.andE₂.andE₂.andE₁)
  have lower := RationalValueBounds.positive_cancel h.andE₂.andE₂.andE₁
    (le_trans first second)
  have upper := le_trans ht.andE₂.andE₂.andE₂ (mul_le_mul_right (sndT t) h.andE₂.andE₂.andE₂.andE₂)
  have upper' : Γ ⊢[PRAAx] le (G*fstT t) (G*(T*sndT t)) := le_congr (.eqRefl _) (by ipra_ring) upper
  exact .andI (.andI ht.andE₁ ht.andE₂.andE₁)
    (.andI lower (RationalValueBounds.positive_cancel h.andE₂.andE₂.andE₁ upper'))

theorem local_modulus_at (j z R B a C G E T t u A D : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C G E T) (hD : Γ ⊢[PRAAx] le one D)
    (ht : Γ ⊢[PRAAx] inside a C G t) (hu : Γ ⊢[PRAAx] inside a C G u)
    (hd : Γ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) A D) :
    Γ ⊢[PRAAx] independentRate (GaussianCompactRiemannName.evaluatorName evaluatorF)
      (GaussianCompactRiemannName.evaluatorName evaluatorF)
      (GaussianCompactRiemannName.nameData t (fixedData j R E T z B))
      (GaussianCompactRiemannName.nameData u (fixedData j R E T z B)) (lipschitz j R E T*A) D := by
  have input : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.input z R B E T
      (fstT t) (sndT t) (fstT u) (sndT u) A D :=
    .andI h.andE₁ (.andI (domain_of_inside z R B a C G E T t h ht)
      (.andI (domain_of_inside z R B a C G E T u h hu) (.andI hD hd)))
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      GaussianEulerExponentCompactBounds.input (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
        (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T))
        (fstT (Syn.shift (Syn.shift t))) (sndT (Syn.shift (Syn.shift t)))
        (fstT (Syn.shift (Syn.shift u))) (sndT (Syn.shift (Syn.shift u)))
        (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift D)) := by simpa [Fm.shift,Syn.shift] using input.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,GaussianCompactRiemannName.subst_nameData,
    GaussianEulerLogarithmicCompactName.subst_fixedData,GaussianEulerLogarithmicMultiplier.subst_lipschitz,
    PTm.subst_mul,Syn.shift] using
    distance_congr (wrapped_at (var 1) (Syn.shift (Syn.shift t)) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B))).eqSymm
      (wrapped_at (var 0) (Syn.shift (Syn.shift u)) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift R))
        (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B))).eqSymm
      (.eqRefl _) (.eqRefl _)
      (original_variation (var 1) (var 0) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
        (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T))
        (fstT (Syn.shift (Syn.shift t))) (sndT (Syn.shift (Syn.shift t)))
        (fstT (Syn.shift (Syn.shift u))) (sndT (Syn.shift (Syn.shift u)))
        (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift D)) hs)

theorem sampled_modulus (j z R B a C G E T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C G E T) : Γ ⊢[PRAAx]
    sampledModulus evaluatorF a C G (lipschitz j R E T) (fixedData j R E T z B) := by
  have hs : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      source (Syn.shift (Syn.shift (Syn.shift (Syn.shift z)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift R))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift B)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift a))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift C)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift G))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift E)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))) :=
    by simpa [Fm.shift,Syn.shift] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [localBody,GaussianEulerLogarithmicCompactName.subst_fixedData,
    GaussianEulerLogarithmicMultiplier.subst_lipschitz,Syn.shift] using
    local_modulus_at (Syn.shift (Syn.shift (Syn.shift (Syn.shift j)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift z))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift R)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift B))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift a)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift C))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift G)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift E))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))) (var 3) (var 2) (var 1) (var 0) hs.wk.wk.wk.wk
      Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem compact_input (j z R B a C G E T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C G E T) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.input evaluatorF a C G (lipschitz j R E T) T (fixedData j R E T z B) :=
  .andI h.andE₂.andE₁ (.andI h.andE₂.andE₂.andE₁
    (.andI (le_trans (le_add_left C a) h.andE₂.andE₂.andE₂.andE₂) (sampled_modulus j z R B a C G E T h)))

theorem name_regular (j z R B a C G E T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C G E T) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN nameF (data j z R B a C G E T) :=
  GaussianCompactRiemannName.name_regular evaluatorF _ _ _ _ _ _ (compact_input j z R B a C G E T h)

theorem canonical_source (z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    source z R B a C E E T :=
  .andI h.andE₁ (.andI h.andE₂.andE₁ (.andI h.andE₁.andE₂.andE₁ (.andI
    (le_congr (one_mul _) (mul_comm a E) (mul_le_mul_right E h.andE₂.andE₁)) h.andE₂.andE₂)))

theorem rescaled_source (k z R B a C G E T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a C G E T) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    source z R B (k*a) (k*C) (k*G) E T := by
  have lower : Γ ⊢[PRAAx] le (k*G) (E*(k*a)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right k h.andE₂.andE₂.andE₂.andE₁)
  have upper : Γ ⊢[PRAAx] le (k*a+k*C) ((k*G)*T) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right k h.andE₂.andE₂.andE₂.andE₂)
  exact .andI h.andE₁ (.andI (positive_product _ _ hk h.andE₂.andE₁)
    (.andI (positive_product _ _ hk h.andE₂.andE₂.andE₁) (.andI lower upper)))

theorem actual_logarithmic_separate_geometry_client_name_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      GaussianEuclideanDistanceName.pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))) :=
  closeUniv 9 (.impI (name_regular _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicClientIntervalName
