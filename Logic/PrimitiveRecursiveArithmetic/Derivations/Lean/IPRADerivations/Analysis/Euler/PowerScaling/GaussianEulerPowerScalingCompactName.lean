import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingCompactRate
import IPRADerivations.Analysis.Euler.CompactExhaustion.Grids.GaussianEulerCompactAdditivity

/-!
# The actual compact quadrature of the power-damped Euler integrand

The compact constructor uses the original power-damped sample program
on its ordinary affine grid. Its uniform modulus and source conditions
come from the checked chart and integrand bounds.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingCompactName

open_ipra
open GaussianEulerPowerScalingCompactRate (lipschitz)
open GaussianCompactRiemannName (inside sampledModulus localBody value evaluatorName nameData)
open GaussianCompactLogarithmBounds (domain)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianEulerPowerScalingCompactRate.nameF
local notation "X" => GaussianEulerPowerScalingCompactRate.data

def fixedData (z B e f d h S : PTm n) : PTm n :=
  GaussianCompactRiemannName.sampleData z B e f d (pairT h S)
def body (p t x : PTm n) : PTm n :=
  ap2 F p (X (GaussianCompactRiemannName.field0 x) (GaussianCompactRiemannName.field1 x)
    (GaussianCompactRiemannName.field2 x) (GaussianCompactRiemannName.field3 x) (GaussianCompactRiemannName.field4 x)
    (fstT (GaussianCompactRiemannName.field5 x)) (sndT (GaussianCompactRiemannName.field5 x)) (fstT t) (sndT t))
def evaluatorF : PR 3 := PTm.toPR (body (var 0) (var 1) (var 2))
def source (z R B e f d h Q S a C E T : PTm n) : Fm PTm n :=
  GaussianEulerCompactAdditivity.intervalSource z R B a C E T ⋏ GaussianEulerPositivePowerChart.parameters e f d h Q S
def data (z R B e f d h Q S a C E T : PTm n) : PTm n :=
  GaussianCompactRiemannName.data a C E (lipschitz R Q S E T) T (fixedData z B e f d h S)
abbrev nameF : PR 2 := GaussianCompactRiemannName.nameF evaluatorF

ipra_subst fixedData
ipra_subst body [GaussianCompactRiemannName.field0, GaussianCompactRiemannName.field1, GaussianCompactRiemannName.field2, GaussianCompactRiemannName.field3, GaussianCompactRiemannName.field4, GaussianCompactRiemannName.field5]
ipra_subst source

theorem evaluator_at (p t z B e f d h S : PTm n) :
    Γ ⊢[PRAAx] ap3 evaluatorF p t (fixedData z B e f d h S) ≐ ap2 F p (X z B e f d h S (fstT t) (sndT t)) := by
  have read := toPR_pairVector3_eq (Γ := Γ) (k := 6)
    (ap2 F (var 0)
        (X (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (fstT (var 1)) (sndT (var 1)))) p t ![z, B, e, f, d, h, S]
  simp only [subst_ap2, GaussianEulerPowerScalingCompactRate.subst_data, subst_fstT, subst_sndT, Syn.subst_var] at read
  exact read

theorem wrapped_at (p t z B e f d h S : PTm n) :
    Γ ⊢[PRAAx] ap2 (evaluatorName evaluatorF) p (nameData t (fixedData z B e f d h S)) ≐
      ap2 F p (X z B e f d h S (fstT t) (sndT t)) :=
  (GaussianCompactRiemannName.evaluator_at evaluatorF p t _).eqTrans (evaluator_at p t z B e f d h S)

theorem wrapped_rate (z R B e f d h Q S E T t u A D : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerPowerScalingCompactRate.source z R B e f d h Q S E T (fstT t) (sndT t) (fstT u) (sndT u) A D) :
    Γ ⊢[PRAAx] independentRate (evaluatorName evaluatorF) (evaluatorName evaluatorF)
      (nameData t (fixedData z B e f d h S)) (nameData u (fixedData z B e f d h S)) (lipschitz R Q S E T*A) D := by
  let sh (s : PTm n) := Syn.shift (Syn.shift s)
  let x := X z B e f d h S (fstT t) (sndT t)
  let y := X z B e f d h S (fstT u) (sndT u)
  let L := lipschitz R Q S E T*A
  have hr : Γ ⊢[PRAAx] independentRate F F x y L D :=
    GaussianEulerPowerScalingCompactRate.original_rate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs
  have rs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] independentRate F F (sh x) (sh y) (sh L) (sh D) := by
    simpa only [Fm.shift,Syn.shift,GaussianNamedInverseRate.subst_independentRate,sh] using hr.shift.shift
  have xs : sh x = X (sh z) (sh B) (sh e) (sh f) (sh d) (sh h) (sh S) (fstT (sh t)) (sndT (sh t)) := by
    simp [sh,x,Syn.shift]
  have ys : sh y = X (sh z) (sh B) (sh e) (sh f) (sh d) (sh h) (sh S) (fstT (sh u)) (sndT (sh u)) := by
    simp [sh,y,Syn.shift]
  have ls : sh L = lipschitz (sh R) (sh Q) (sh S) (sh E) (sh T)*sh A := by simp [sh,L,Syn.shift]
  refine .allI (.allI ?_)
  have near := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ (var 1) (var 0) rs
  rw [xs,ys,ls] at near
  simpa only [independentRate,GaussianCompactRiemannName.subst_nameData,subst_fixedData,
    GaussianEulerPowerScalingCompactRate.subst_lipschitz,PTm.subst_mul,Syn.shift,sh] using
    distance_congr (wrapped_at (var 1) (sh t) (sh z) (sh B) (sh e) (sh f) (sh d) (sh h) (sh S)).eqSymm
      (wrapped_at (var 0) (sh u) (sh z) (sh B) (sh e) (sh f) (sh d) (sh h) (sh S)).eqSymm (.eqRefl _) (.eqRefl _) near

theorem local_modulus_at (z R B e f d h Q S a C E T t u A D : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B e f d h Q S a C E T) (hd : Γ ⊢[PRAAx] le one D)
    (ht : Γ ⊢[PRAAx] inside a C E t) (hu : Γ ⊢[PRAAx] inside a C E u)
    (hn : Γ ⊢[PRAAx] distanceBounded (value t) (value u) A D) :
    Γ ⊢[PRAAx] independentRate (evaluatorName evaluatorF) (evaluatorName evaluatorF)
      (nameData t (fixedData z B e f d h S)) (nameData u (fixedData z B e f d h S)) (lipschitz R Q S E T*A) D := by
  have he := hs.andE₁.andE₁.andE₂.andE₁
  have td := GaussianEulerCompactAdditivity.domain_of_inside t a C E T hs.andE₁.andE₂.andE₁ he hs.andE₁.andE₂.andE₂ ht
  have ud := GaussianEulerCompactAdditivity.domain_of_inside u a C E T hs.andE₁.andE₂.andE₁ he hs.andE₁.andE₂.andE₂ hu
  exact wrapped_rate z R B e f d h Q S E T t u A D
    (.andI hs.andE₁.andE₁ (.andI (.andI hs.andE₂ (.andI he td)) (.andI ud (.andI hd hn))))

theorem sampled_modulus (z R B e f d h Q S a C E T : PTm n) (hs : Γ ⊢[PRAAx] source z R B e f d h Q S a C E T) :
    Γ ⊢[PRAAx] sampledModulus evaluatorF a C E (lipschitz R Q S E T) (fixedData z B e f d h S) := by
  let sh := fun s : PTm n => Syn.shift (Syn.shift (Syn.shift (Syn.shift s)))
  have ss : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      source (sh z) (sh R) (sh B) (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S) (sh a) (sh C) (sh E) (sh T) := by
    simpa only [Fm.shift,Syn.shift,subst_source,sh] using hs.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [localBody,subst_fixedData,GaussianEulerPowerScalingCompactRate.subst_lipschitz,Syn.shift,sh] using
    local_modulus_at (sh z) (sh R) (sh B) (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S) (sh a) (sh C) (sh E) (sh T)
      (var 3) (var 2) (var 1) (var 0) ss.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem compact_input (z R B e f d h Q S a C E T : PTm n) (hs : Γ ⊢[PRAAx] source z R B e f d h Q S a C E T) :
    Γ ⊢[PRAAx] GaussianCompactRiemannName.input evaluatorF a C E (lipschitz R Q S E T) T (fixedData z B e f d h S) :=
  .andI hs.andE₁.andE₂.andE₁ (.andI hs.andE₁.andE₁.andE₂.andE₁
    (.andI (le_trans (le_add_left C a) hs.andE₁.andE₂.andE₂) (sampled_modulus _ _ _ _ _ _ _ _ _ _ _ _ _ hs)))

theorem name_regular (z R B e f d h Q S a C E T : PTm n) (hs : Γ ⊢[PRAAx] source z R B e f d h Q S a C E T) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B e f d h Q S a C E T) :=
  GaussianCompactRiemannName.name_regular evaluatorF _ _ _ _ _ _ (compact_input _ _ _ _ _ _ _ _ _ _ _ _ _ hs)

theorem actual_power_damped_compact_name_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⟶
        pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))) :=
  closeUniv 13 (.impI (name_regular _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingCompactName
