import IPRADerivations.Analysis.GaussianEulerUnitKernelCompactRate
import IPRADerivations.Analysis.GaussianCompactRiemannName

/-!
# The original rational unit kernel on a native affine compact

The actual PR3 evaluator uses the original rational unit-kernel sampler
with parameter data pair(z,B). Native endpoint guards place the whole
interval inside [1/G,1-1/G]. They derive every original rational-time
guard and the sampled modulus of the unchanged evaluator. The standard
compact program therefore supplies its actual regular quadrature name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelCompactName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (inside sampledModulus localBody)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianNamedInverseRate (independentRate)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def fixedData (z B : PTm n) : PTm n := pairT z B
def evaluatorTerm (p t x : PTm n) : PTm n := ap2 GaussianEulerUnitSubstitutionKernel.nameF p
  (GaussianEulerUnitSubstitutionKernel.data (fstT x) (sndT x) (fstT t) (sndT t))
def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 0) (var 1) (var 2))
def lipschitz (R G : PTm n) : PTm n := GaussianEulerUnitKernelCompactRate.lipschitz R G
def source (z R B a C E G : PTm n) : Fm PTm n := GaussianEulerExponentCompactBounds.source z R B G ⋏
  (le one E ⋏ (le E (G*a) ⋏ le (G*(a+C)+E) (G*E)))
def data (z R B a C E G : PTm n) : PTm n := GaussianCompactRiemannName.data a C E (lipschitz R G) one (fixedData z B)
abbrev nameF : PR 2 := GaussianCompactRiemannName.nameF evaluatorF

@[simp] theorem subst_fixedData {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (fixedData z B) = fixedData (Syn.subst σ z) (Syn.subst σ B) := by simp [fixedData]
@[simp] theorem subst_evaluatorTerm {m : ℕ} (σ : Fin n → PTm m) (p t x : PTm n) :
    Syn.subst σ (evaluatorTerm p t x) = evaluatorTerm (Syn.subst σ p) (Syn.subst σ t) (Syn.subst σ x) := by simp [evaluatorTerm]
@[simp] theorem subst_lipschitz {m : ℕ} (σ : Fin n → PTm m) (R G : PTm n) :
    Syn.subst σ (lipschitz R G) = lipschitz (Syn.subst σ R) (Syn.subst σ G) := by simp [lipschitz]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B a C E G : PTm n) :
    (source z R B a C E G).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ G) := by simp [source]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B a C E G : PTm n) :
    Syn.subst σ (data z R B a C E G) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ G) := by simp [data]

/-- Arbitrary raw time codes are decoded; no pair eta rule is assumed. -/
theorem evaluator_at (p t z B : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluatorF p t (fixedData z B) ≐ ap2 GaussianEulerUnitSubstitutionKernel.nameF p
      (GaussianEulerUnitSubstitutionKernel.data z B (fstT t) (sndT t)) := by
  have term : Γ ⊢[PRAAx] ap3 evaluatorF p t (fixedData z B) ≐ evaluatorTerm p t (fixedData z B) := by
    simpa [evaluatorF,ap3] using toPR_eq (Γ := Γ) (evaluatorTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,fixedData z B]
  have fields : Γ ⊢[PRAAx] GaussianEulerUnitSubstitutionKernel.data (fstT (fixedData z B)) (sndT (fixedData z B)) (fstT t) (sndT t) ≐
      GaussianEulerUnitSubstitutionKernel.data z B (fstT t) (sndT t) := by
    simpa only [GaussianEulerUnitSubstitutionKernel.subst_data,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (GaussianEulerUnitSubstitutionKernel.data (var 0) (var 1) (var 2) (var 3) : PTm 4)
        (σ := ![fstT (fixedData z B),sndT (fixedData z B),fstT t,sndT t]) (σ' := ![z,B,fstT t,sndT t])
        (fun i => by fin_cases i; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _; exact .eqRefl _)
  exact term.eqTrans (congrAp2 GaussianEulerUnitSubstitutionKernel.nameF (.eqRefl _) fields)

theorem sample_at (p z B a b : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluatorF p (pairT a b) (fixedData z B) ≐ ap2 GaussianEulerUnitSubstitutionKernel.nameF p
      (GaussianEulerUnitSubstitutionKernel.data z B a b) := by
  have fields : Γ ⊢[PRAAx] GaussianEulerUnitSubstitutionKernel.data z B (fstT (pairT a b)) (sndT (pairT a b)) ≐
      GaussianEulerUnitSubstitutionKernel.data z B a b := by
    simpa only [GaussianEulerUnitSubstitutionKernel.subst_data,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (GaussianEulerUnitSubstitutionKernel.data (var 0) (var 1) (var 2) (var 3) : PTm 4)
        (σ := ![z,B,fstT (pairT a b),sndT (pairT a b)]) (σ' := ![z,B,a,b])
        (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _)
  exact (evaluator_at p (pairT a b) z B).eqTrans (congrAp2 GaussianEulerUnitSubstitutionKernel.nameF (.eqRefl _) fields)

theorem wrapped_at (p t z B : PTm n) : Γ ⊢[PRAAx]
    ap2 (GaussianCompactRiemannName.evaluatorName evaluatorF) p (GaussianCompactRiemannName.nameData t (fixedData z B)) ≐
      ap2 GaussianEulerUnitSubstitutionKernel.nameF p (GaussianEulerUnitSubstitutionKernel.data z B (fstT t) (sndT t)) :=
  (GaussianCompactRiemannName.evaluator_at evaluatorF p t _).eqTrans (evaluator_at p t z B)

theorem start_positive (z R B a C E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G) : Γ ⊢[PRAAx] le one a := by
  refine .orE (zero_or_succ a) ?_ ?_
  · have e : (a ≐ zero)::Γ ⊢[PRAAx] G*a ≐ zero := (congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)
    have bad : (a ≐ zero)::Γ ⊢[PRAAx] le one zero := le_trans h.andE₂.andE₁.wk
      (le_congr (.eqRefl _) e h.andE₂.andE₂.andE₁.wk)
    exact .botE _ (succ_ne_zero ((monus_zero one).eqSymm.eqTrans bad))
  · exact le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ (pred a))

theorem right_endpoint_le_one (z R B a C E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G) : Γ ⊢[PRAAx]
    le (a+C) E :=
  RationalValueBounds.positive_cancel h.andE₁.andE₂.andE₁
    (le_trans (le_add_right (G*(a+C)) E) h.andE₂.andE₂.andE₂)

/-- Every actual positive encoding in the physical interval has the
same certified unit margin, independently of its raw denominator. -/
theorem inside_source (z R B a C E G t : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G)
    (ht : Γ ⊢[PRAAx] inside a C E t) : Γ ⊢[PRAAx]
    GaussianEulerUnitKernelCompactRate.source z R B (fstT t) (sndT t) G := by
  let m := fstT t
  let d := sndT t
  have lower : Γ ⊢[PRAAx] le d (G*m) := by
    have first := mul_le_mul_right d h.andE₂.andE₂.andE₁
    have second := mul_le_mul_right G ht.andE₂.andE₂.andE₁
    have later : Γ ⊢[PRAAx] le (G*a*d) (E*(G*m)) :=
      le_congr (by dsimp only [d]; ipra_ring) (by dsimp only [m]; ipra_ring) second
    exact RationalValueBounds.positive_cancel h.andE₂.andE₁ (le_trans first later)
  have upper : Γ ⊢[PRAAx] le (G*m+d) (G*d) := by
    have first := add_le_add_right (E*d) (mul_le_mul_right G ht.andE₂.andE₂.andE₂)
    have second := mul_le_mul_right d h.andE₂.andE₂.andE₂
    have beginning : Γ ⊢[PRAAx] le (E*(G*m+d)) ((G*(a+C)+E)*d) :=
      le_congr (by dsimp only [m]; ipra_ring) (by dsimp only [d]; ipra_ring) first
    have ending : Γ ⊢[PRAAx] le ((G*(a+C)+E)*d) (E*(G*d)) :=
      le_congr (.eqRefl _) (by ipra_ring) second
    exact RationalValueBounds.positive_cancel h.andE₂.andE₁ (le_trans beginning ending)
  have strict : Γ ⊢[PRAAx] lt m d := by
    refine .orE (lt_or_le m d) Prf.hyp0 ?_
    have reversed : (le d m)::Γ ⊢[PRAAx] le (G*d) (G*m) :=
      le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right G Prf.hyp0)
    have bad : (le d m)::Γ ⊢[PRAAx] lt (G*d) (G*d) :=
      le_trans (le_congr (by ipra_ring) (.eqRefl _) (add_le_add₂ reversed ht.andE₂.andE₁.wk)) upper.wk
    exact le_lt_absurd _ (le_refl _) bad
  exact .andI h.andE₁ (.andI (.andI ht.andE₁ strict) (.andI h.andE₁.andE₂.andE₁ (.andI lower upper)))

theorem evaluator_bound (p t z R B a C E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G)
    (ht : Γ ⊢[PRAAx] inside a C E t) : Γ ⊢[PRAAx]
    bounded (ap3 evaluatorF p t (fixedData z B)) (GaussianEulerUnitKernelCompactRate.majorant R G) one :=
  GaussianRationalReciprocal.bound_congr (evaluator_at p t z B).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerUnitKernelCompactRate.original_bound p z R B (fstT t) (sndT t) G (inside_source z R B a C E G t h ht))

theorem local_modulus_at (z R B a C E G t u A D : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G)
    (hD : Γ ⊢[PRAAx] le one D) (ht : Γ ⊢[PRAAx] inside a C E t) (hu : Γ ⊢[PRAAx] inside a C E u)
    (near : Γ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) A D) : Γ ⊢[PRAAx]
    independentRate (GaussianCompactRiemannName.evaluatorName evaluatorF) (GaussianCompactRiemannName.evaluatorName evaluatorF)
      (GaussianCompactRiemannName.nameData t (fixedData z B)) (GaussianCompactRiemannName.nameData u (fixedData z B)) (lipschitz R G*A) D := by
  have rate := GaussianEulerUnitKernelCompactRate.original_rate z R B (fstT t) (sndT t) (fstT u) (sndT u) G A D
    (.andI (inside_source z R B a C E G t h ht) (.andI (inside_source z R B a C E G u h hu) (.andI hD near)))
  let sh := fun x : PTm n => Syn.shift (Syn.shift x)
  have rs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] independentRate GaussianEulerUnitSubstitutionKernel.nameF GaussianEulerUnitSubstitutionKernel.nameF
      (GaussianEulerUnitSubstitutionKernel.data (sh z) (sh B) (fstT (sh t)) (sndT (sh t)))
      (GaussianEulerUnitSubstitutionKernel.data (sh z) (sh B) (fstT (sh u)) (sndT (sh u))) (lipschitz (sh R) (sh G)*sh A) (sh D) := by
    simpa [Fm.shift,Syn.shift,sh,lipschitz] using rate.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,GaussianCompactRiemannName.subst_nameData,subst_fixedData,subst_lipschitz,PTm.subst_mul,Syn.shift,sh] using
    distance_congr (wrapped_at (var 1) (sh t) (sh z) (sh B)).eqSymm (wrapped_at (var 0) (sh u) (sh z) (sh B)).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianNamedInverseRate.rate_at _ _ _ _ _ _ (var 1) (var 0) rs)

theorem sampled_modulus (z R B a C E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G) : Γ ⊢[PRAAx]
    sampledModulus evaluatorF a C E (lipschitz R G) (fixedData z B) := by
  let sh := fun x : PTm n => Syn.shift (Syn.shift (Syn.shift (Syn.shift x)))
  have hs : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      source (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh G) := by simpa [Fm.shift,Syn.shift,sh] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [localBody,subst_fixedData,subst_lipschitz,Syn.shift,sh] using
    local_modulus_at (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh G) (var 3) (var 2) (var 1) (var 0)
      hs.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem compact_input (z R B a C E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.input evaluatorF a C E (lipschitz R G) one (fixedData z B) :=
  .andI (start_positive z R B a C E G h) (.andI h.andE₂.andE₁
    (.andI (le_congr (.eqRefl _) (by ipra_ring) (le_trans (le_add_left C a) (right_endpoint_le_one z R B a C E G h)))
      (sampled_modulus z R B a C E G h)))

theorem name_regular (z R B a C E G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E G) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN nameF (data z R B a C E G) :=
  GaussianCompactRiemannName.name_regular evaluatorF _ _ _ _ _ _ (compact_input z R B a C E G h)

theorem name_at (p z R B a C E G : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B a C E G) ≐ GaussianCompactRiemannName.quadrature evaluatorF
      (GaussianCompactRiemannName.precision p one) (GaussianCompactRiemannName.mesh p (lipschitz R G) one)
      a C E (fixedData z B) := GaussianCompactRiemannName.name_at evaluatorF p _ _ _ _ _ _

theorem actual_original_rational_unit_kernel_evaluator_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (ap3 evaluatorF (var 0) (pairT (var 3) (var 4)) (fixedData (var 1) (var 2)) ≐
      ap2 GaussianEulerUnitSubstitutionKernel.nameF (var 0) (GaussianEulerUnitSubstitutionKernel.data (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (sample_at _ _ _ _ _)

theorem actual_original_unit_kernel_sampled_modulus_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      sampledModulus evaluatorF (var 3) (var 4) (var 5) (lipschitz (var 1) (var 6)) (fixedData (var 0) (var 2))) :=
  closeUniv 7 (.impI (sampled_modulus _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_unit_kernel_compact_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      GaussianEuclideanDistanceName.pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) :=
  closeUniv 7 (.impI (name_regular _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelCompactName
