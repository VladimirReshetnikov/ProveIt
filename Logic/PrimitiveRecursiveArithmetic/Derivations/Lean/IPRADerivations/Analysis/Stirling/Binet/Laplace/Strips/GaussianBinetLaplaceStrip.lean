import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceIntegrand
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactRiemannName

/-!
# Compact Binet Laplace strips

The existing compact Riemann program uses strictly positive rational
tags. Translating its coordinates by one lets the same evaluator cover
panels whose physical left endpoint is zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceStrip

open_ipra
open GaussianBinetLaplaceIntegrand (meshGain)
open GaussianCompactRiemannName (inside localBody nameData evaluatorName sampledModulus value)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalMetric (distanceBounded qsub qnegative)
open GaussianRationalHorner (qadd)

variable {n : ℕ} {Γ : List (Fm PTm n)}

inductive Kernel where
  | finite
  | cofinal

def integrandF : Kernel → PR 2
  | .finite => GaussianBinetLaplaceIntegrand.finiteF
  | .cofinal => GaussianBinetLaplaceIntegrand.cofinalF

def integrandData (K : Kernel) (X Y D sign R T N A B : PTm n) : PTm n :=
  match K with
  | .finite => GaussianBinetLaplaceIntegrand.finiteData X Y D sign R T N A B
  | .cofinal => GaussianBinetLaplaceIntegrand.cofinalData X Y D sign R T A B

def source (X Y D sign R T A C E : PTm n) : Fm PTm n :=
  GaussianLogGammaEulerResidualDomain.source X Y D sign R ⋏ (le one E ⋏ le (A+C) (E*T))

def tagNumerator (t : PTm n) : PTm n := monus (fstT t) (sndT t)

abbrev fixedData (X Y D sign R T N : PTm n) : PTm n :=
  GaussianCompactRiemannName.sampleData X Y D sign R (pairT T N)

def evaluatorTerm (K : Kernel) (p t x : PTm n) : PTm n :=
  ap2 (integrandF K) p (integrandData K (GaussianCompactRiemannName.field0 x) (GaussianCompactRiemannName.field1 x)
    (GaussianCompactRiemannName.field2 x) (GaussianCompactRiemannName.field3 x) (GaussianCompactRiemannName.field4 x)
    (fstT (GaussianCompactRiemannName.field5 x)) (sndT (GaussianCompactRiemannName.field5 x)) (tagNumerator t) (sndT t))

def evaluatorF (K : Kernel) : PR 3 := PTm.toPR (evaluatorTerm K (var 0) (var 1) (var 2))

abbrev nameF (K : Kernel) : PR 2 := GaussianCompactRiemannName.nameF (evaluatorF K)
def data (X Y D sign R T N A C E : PTm n) : PTm n :=
  GaussianCompactRiemannName.data (E+A) C E (meshGain R T) T (fixedData X Y D sign R T N)

@[simp] theorem subst_integrandData {m : ℕ} (σ : Fin n → PTm m) (K : Kernel) (X Y D sign R T N A B : PTm n) :
    Syn.subst σ (integrandData K X Y D sign R T N A B) =
      integrandData K (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign)
        (Syn.subst σ R) (Syn.subst σ T) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ B) := by
  cases K <;> simp [integrandData]

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (X Y D sign R T A C E : PTm n) :
    (source X Y D sign R T A C E).subst σ = source (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign)
      (Syn.subst σ R) (Syn.subst σ T) (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) := by simp [source,one]

ipra_subst tagNumerator

ipra_subst meshGain [two]

ipra_subst evaluatorTerm

ipra_subst data

theorem tag_inside (t A C E T : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hT : Γ ⊢[PRAAx] le (A+C) (E*T))
    (h : Γ ⊢[PRAAx] inside (E+A) C E t) :
    Γ ⊢[PRAAx] le (sndT t) (fstT t) ⋏ le (tagNumerator t) (T*sndT t) := by
  let a := fstT t
  let b := sndT t
  let u := tagNumerator t
  have lo : Γ ⊢[PRAAx] le b a :=
    RationalValueBounds.positive_cancel hE (le_trans
      (le_of_eq_add (d := A*b) (by ipra_ring : Γ ⊢[PRAAx] (E+A)*b ≐ E*b+A*b)) h.andE₂.andE₂.andE₁)
  have ext : Γ ⊢[PRAAx] le ((E+A+C)*b) (E*(b+T*b)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (le_refl (E*b)) (mul_le_mul_right b hT))
  have upper : Γ ⊢[PRAAx] le (b+u) (b+T*b) :=
    le_congr (eq_add_of_le lo) (.eqRefl _)
      (RationalValueBounds.positive_cancel hE (le_trans h.andE₂.andE₂.andE₂ ext))
  exact .andI lo (le_of_eq_add (add_left_cancel ((eq_add_of_le upper).eqTrans (add_assoc _ _ _))))

theorem translated_value (t : PTm n) (hB : Γ ⊢[PRAAx] le one (sndT t))
    (h : Γ ⊢[PRAAx] le (sndT t) (fstT t)) :
    Γ ⊢[PRAAx] qsub (value t) (fraction one one) ≐ fraction (tagNumerator t) (sndT t) := by
  let a := fstT t
  let b := sndT t
  let u := tagNumerator t
  let c : PTm n := fraction one one
  have e : Γ ⊢[PRAAx] qadd c (fraction u b) ≐ value t :=
    (GaussianEulerPositivePowerChartCorrectedImage.fraction_sum one one u b (le_refl one) hB).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _
        ((by ipra_ring : Γ ⊢[PRAAx] one*b+u*one ≐ b+u).eqTrans (eq_add_of_le h).eqSymm) (one_mul b))
  exact (GaussianRationalSyntheticDivision.qsub_congr e.eqSymm (.eqRefl c)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_sub_cancel c (fraction u b)
      (GaussianRationalHorner.ofGaussian_canonical _ _ hB))

theorem tag_source (t u A C E T M Q : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hT : Γ ⊢[PRAAx] le (A+C) (E*T))
    (hQ : Γ ⊢[PRAAx] le one Q) (ht : Γ ⊢[PRAAx] inside (E+A) C E t) (hu : Γ ⊢[PRAAx] inside (E+A) C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (value t) (value u) M Q) :
    Γ ⊢[PRAAx] GaussianBinetKernelTimeContinuity.source (tagNumerator t) (sndT t) (tagNumerator u) (sndT u) T M Q := by
  have lt := tag_inside t A C E T hE hT ht
  have lu := tag_inside u A C E T hE hT hu
  have dt := translated_value t ht.andE₂.andE₁ lt.andE₁
  have du := translated_value u hu.andE₂.andE₁ lu.andE₁
  have d := GaussianNameRingLaws.sum_left_error (value t) (value u) (qnegative (fraction one one)) M Q hQ hd
  exact .andI ht.andE₂.andE₁ (.andI hu.andE₂.andE₁ (.andI hQ
    (.andI lt.andE₂ (.andI lu.andE₂ (distance_congr dt du (.eqRefl _) (.eqRefl _) d)))))

private theorem val_five {α : Type} (a b c d e f g h i : α) : ![a,b,c,d,e,f,g,h,i] (5 : Fin 9) = f := rfl
private theorem val_six {α : Type} (a b c d e f g h i : α) : ![a,b,c,d,e,f,g,h,i] (6 : Fin 9) = g := rfl
private theorem val_seven {α : Type} (a b c d e f g h i : α) : ![a,b,c,d,e,f,g,h,i] (7 : Fin 9) = h := rfl
private theorem val_eight {α : Type} (a b c d e f g h i : α) : ![a,b,c,d,e,f,g,h,i] (8 : Fin 9) = i := rfl

theorem evaluator_at (K : Kernel) (p t X Y D sign R T N : PTm n) :
    Γ ⊢[PRAAx] ap3 (evaluatorF K) p t (fixedData X Y D sign R T N) ≐
      ap2 (integrandF K) p (integrandData K X Y D sign R T N (tagNumerator t) (sndT t)) := by
  let x := fixedData X Y D sign R T N
  have ev : Γ ⊢[PRAAx] ap3 (evaluatorF K) p t x ≐ evaluatorTerm K p t x := by
    simpa only [evaluatorF, ap3, subst_evaluatorTerm, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (evaluatorTerm K (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]
  have fields := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
      (integrandData K (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) : PTm 9)
      (σ := ![GaussianCompactRiemannName.field0 x, GaussianCompactRiemannName.field1 x, GaussianCompactRiemannName.field2 x,
        GaussianCompactRiemannName.field3 x, GaussianCompactRiemannName.field4 x, fstT (GaussianCompactRiemannName.field5 x),
        sndT (GaussianCompactRiemannName.field5 x), tagNumerator t, sndT t])
      (σ' := ![X,Y,D,sign,R,T,N,tagNumerator t,sndT t]) (fun i => by
        fin_cases i
        exact GaussianCompactRiemannName.field0_at _ _ _ _ _ _
        exact GaussianCompactRiemannName.field1_at _ _ _ _ _ _
        exact GaussianCompactRiemannName.field2_at _ _ _ _ _ _
        exact GaussianCompactRiemannName.field3_at _ _ _ _ _ _
        exact GaussianCompactRiemannName.field4_at _ _ _ _ _ _
        exact (congrFst (GaussianCompactRiemannName.field5_at _ _ _ _ _ _)).eqTrans (fst_pair _ _)
        exact (congrSnd (GaussianCompactRiemannName.field5_at _ _ _ _ _ _)).eqTrans (snd_pair _ _)
        exact .eqRefl _
        exact .eqRefl _)
  exact ev.eqTrans (congrAp2 (integrandF K) (.eqRefl p)
    (by simpa only [subst_integrandData, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, val_five, val_six, val_seven, val_eight,
      Matrix.head_cons, Matrix.tail_cons] using fields))

theorem wrapped_at (K : Kernel) (p t X Y D sign R T N : PTm n) :
    Γ ⊢[PRAAx] ap2 (evaluatorName (evaluatorF K)) p (nameData t (fixedData X Y D sign R T N)) ≐
      ap2 (integrandF K) p (integrandData K X Y D sign R T N (tagNumerator t) (sndT t)) :=
  (GaussianCompactRiemannName.evaluator_at (evaluatorF K) p t _).eqTrans (evaluator_at K p t X Y D sign R T N)

private theorem integrand_rate (K : Kernel) (X Y D sign R T N t u M Q : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianLogGammaEulerResidualDomain.source X Y D sign R)
    (ht : Γ ⊢[PRAAx] GaussianBinetKernelTimeContinuity.source (tagNumerator t) (sndT t) (tagNumerator u) (sndT u) T M Q) :
    Γ ⊢[PRAAx] independentRate (integrandF K) (integrandF K)
      (integrandData K X Y D sign R T N (tagNumerator t) (sndT t))
      (integrandData K X Y D sign R T N (tagNumerator u) (sndT u)) (meshGain R T*M) Q := by
  cases K
  · exact GaussianBinetLaplaceIntegrand.finite_time_rate X Y D sign R T N _ _ _ _ M Q hz ht
  · exact GaussianBinetLaplaceIntegrand.cofinal_time_rate X Y D sign R T _ _ _ _ M Q hz ht

theorem local_modulus_at (K : Kernel) (X Y D sign R T N A C E t u M Q : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E) (hQ : Γ ⊢[PRAAx] le one Q)
    (ht : Γ ⊢[PRAAx] inside (E+A) C E t) (hu : Γ ⊢[PRAAx] inside (E+A) C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (value t) (value u) M Q) :
    Γ ⊢[PRAAx] independentRate (evaluatorName (evaluatorF K)) (evaluatorName (evaluatorF K))
      (nameData t (fixedData X Y D sign R T N)) (nameData u (fixedData X Y D sign R T N)) (meshGain R T*M) Q := by
  let s (z : PTm n) := Syn.shift (Syn.shift z)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hr := integrand_rate K X Y D sign R T N t u M Q h.andE₁
    (tag_source t u A C E T M Q h.andE₂.andE₁ h.andE₂.andE₂ hQ ht hu hd)
  have hs : Δ ⊢[PRAAx] independentRate (integrandF K) (integrandF K)
      (integrandData K (s X) (s Y) (s D) (s sign) (s R) (s T) (s N) (tagNumerator (s t)) (sndT (s t)))
      (integrandData K (s X) (s Y) (s D) (s sign) (s R) (s T) (s N) (tagNumerator (s u)) (sndT (s u)))
      (meshGain (s R) (s T)*s M) (s Q) := by simpa [Δ, Fm.shift, Syn.shift, s] using hr.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate, Syn.shift, s, GaussianCompactRiemannName.subst_nameData,
    GaussianCompactRiemannName.subst_sampleData, subst_pairT, subst_meshGain, PTm.subst_mul, Δ] using
    distance_congr (wrapped_at (Γ := Δ) K (var 1) (s t) (s X) (s Y) (s D) (s sign) (s R) (s T) (s N)).eqSymm
      (wrapped_at K (var 0) (s u) (s X) (s Y) (s D) (s sign) (s R) (s T) (s N)).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianNamedInverseRate.rate_at _ _ _ _ _ _ (var 1) (var 0) hs)

theorem sampled_modulus (K : Kernel) (X Y D sign R T N A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E) :
    Γ ⊢[PRAAx] sampledModulus (evaluatorF K) (E+A) C E (meshGain R T) (fixedData X Y D sign R T N) := by
  let s (z : PTm n) := Syn.shift (Syn.shift (Syn.shift (Syn.shift z)))
  let Δ := (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) (s T) (s A) (s C) (s E) := by
    simpa only [Δ,Fm.shift,Syn.shift,s,subst_source] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [localBody, Syn.shift, s, subst_meshGain, GaussianCompactRiemannName.subst_sampleData,
    subst_pairT, PTm.subst_add, Δ] using
    local_modulus_at K (s X) (s Y) (s D) (s sign) (s R) (s T) (s N) (s A) (s C) (s E)
      (var 3) (var 2) (var 1) (var 0) hs.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem compact_input (K : Kernel) (X Y D sign R T N A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E) :
    Γ ⊢[PRAAx] GaussianCompactRiemannName.input (evaluatorF K) (E+A) C E (meshGain R T) T (fixedData X Y D sign R T N) :=
  .andI (le_trans h.andE₂.andE₁ (le_add_right E A)) (.andI h.andE₂.andE₁
    (.andI (le_trans (le_add_left C A) h.andE₂.andE₂) (sampled_modulus K X Y D sign R T N A C E h)))

theorem regular (K : Kernel) (X Y D sign R T N A C E : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign R T A C E) :
    Γ ⊢[PRAAx] pointCN (nameF K) (data X Y D sign R T N A C E) :=
  GaussianCompactRiemannName.name_regular _ _ _ _ _ _ _ (compact_input K X Y D sign R T N A C E h)

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceStrip
