import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerFrozen
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactAdditivity

/-!
# Ordinary compact quadrature of the named power-damped Euler kernel

The compact name applies the named kernel to the original affine grid.
The fixed positive parameter guards give the same time modulus at every
point of the interval and for independent observation indices.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerCompact

open_ipra
open GaussianNamedDampingPowerIntegrand (gain)
open GaussianCompactRiemannName (inside localBody value evaluatorName nameData)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev kernelF (F G : PR 2) : PR 2 := GaussianNamedDampingPowerIntegrand.nameF F G
local notation "kernelData" => GaussianNamedDampingPowerIntegrand.data

def fixedData (z B x y : PTm n) : PTm n := pairT (pairT z B) (pairT x y)
def body (F G : PR 2) (p t d : PTm n) : PTm n :=
  ap2 (kernelF F G) p (kernelData F G (fstT (fstT d)) (sndT (fstT d)) (fstT (sndT d)) (sndT (sndT d)) (fstT t) (sndT t))
def evaluatorF (F G : PR 2) : PR 3 := PTm.toPR (body F G (var 0) (var 1) (var 2))
def source (F G : PR 2) (z Rz B x y C₀ C R₀ R a W E T : PTm n) : Fm PTm n :=
  GaussianEulerCompactAdditivity.intervalSource z Rz B a W E T ⋏
    (GaussianNamedPositiveLogarithm.source F x C₀ C ⋏ GaussianNamedPositiveLogarithm.source G y R₀ R)
def lipschitz (Rz C R E T : PTm n) : PTm n := gain Rz C R E T zero zero one
abbrev nameF (F G : PR 2) : PR 2 := GaussianCompactRiemannName.nameF (evaluatorF F G)
def data (z Rz B x y C R a W E T : PTm n) : PTm n :=
  GaussianCompactRiemannName.data a W E (lipschitz Rz C R E T) T (fixedData z B x y)

ipra_subst fixedData
ipra_subst source
ipra_subst lipschitz [gain, GaussianNamedDampingPowerIntegrand.decayBound, GaussianNamedDampingPowerChart.gain, GaussianNamedDampingPowerChart.majorant, GaussianCompactLogarithmBounds.radius, one]
ipra_subst data

private theorem kernel_data_congr (F G : PR 2) {z z' B B' x x' y y' a b : PTm n}
    (hz : Γ ⊢[PRAAx] z ≐ z') (hB : Γ ⊢[PRAAx] B ≐ B') (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y') :
    Γ ⊢[PRAAx] kernelData F G z B x y a b ≐ kernelData F G z' B' x' y' a b := by
  let term : PTm 6 := kernelData F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
  have eq := Prf.eqCongr term (σ := ![z,B,x,y,a,b]) (σ' := ![z',B',x',y',a,b]) (fun i => by
    fin_cases i
    exact hz
    exact hB
    exact hx
    exact hy
    exact .eqRefl _
    exact .eqRefl _)
  have left : Syn.subst ![z,B,x,y,a,b] term = kernelData F G z B x y a b := by
    simp only [term,GaussianNamedDampingPowerIntegrand.subst_data,Syn.subst_var]
    rfl
  have right : Syn.subst ![z',B',x',y',a,b] term = kernelData F G z' B' x' y' a b := by
    simp only [term,GaussianNamedDampingPowerIntegrand.subst_data,Syn.subst_var]
    rfl
  rw [left,right] at eq
  exact eq

theorem evaluator_at (F G : PR 2) (p t z B x y : PTm n) :
    Γ ⊢[PRAAx] ap3 (evaluatorF F G) p t (fixedData z B x y) ≐ ap2 (kernelF F G) p (kernelData F G z B x y (fstT t) (sndT t)) := by
  have raw : Γ ⊢[PRAAx] ap3 (evaluatorF F G) p t (fixedData z B x y) ≐ body F G p t (fixedData z B x y) := by
    simpa [evaluatorF,body,ap3] using
      toPR_eq (Γ := Γ) (body F G (var 0) (var 1) (var 2) : PTm 3) ![p,t,fixedData z B x y]
  have left := fst_pair (Γ := Γ) (pairT z B) (pairT x y)
  have right := snd_pair (Γ := Γ) (pairT z B) (pairT x y)
  exact raw.eqTrans (congrAp2 _ (.eqRefl _) (kernel_data_congr F G
    ((congrFst left).eqTrans (fst_pair z B)) ((congrSnd left).eqTrans (snd_pair z B))
    ((congrFst right).eqTrans (fst_pair x y)) ((congrSnd right).eqTrans (snd_pair x y))))

theorem wrapped_at (F G : PR 2) (p t z B x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (evaluatorName (evaluatorF F G)) p (nameData t (fixedData z B x y)) ≐
      ap2 (kernelF F G) p (kernelData F G z B x y (fstT t) (sndT t)) :=
  (GaussianCompactRiemannName.evaluator_at (evaluatorF F G) p t _).eqTrans (evaluator_at F G p t z B x y)

theorem kernel_source_at (F G : PR 2) (z Rz B x y C₀ C R₀ R a W E T t : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B x y C₀ C R₀ R a W E T) (ht : Γ ⊢[PRAAx] inside a W E t) :
    Γ ⊢[PRAAx] GaussianNamedDampingPowerIntegrand.source F G z Rz B x y C₀ C R₀ R E T (fstT t) (sndT t) := by
  have he := hs.andE₁.andE₁.andE₂.andE₁
  exact .andI hs.andE₁.andE₁ (.andI hs.andE₂.andE₁ (.andI hs.andE₂.andE₂ (.andI he
    (GaussianEulerCompactAdditivity.domain_of_inside t a W E T hs.andE₁.andE₂.andE₁ he hs.andE₁.andE₂.andE₂ ht))))

private theorem time_gain (Rz C R E T A : PTm n) : Γ ⊢[PRAAx]
    gain Rz C R E T zero zero A ≐ lipschitz Rz C R E T*A := by
  unfold lipschitz gain GaussianNamedDampingPowerChart.gain
  ipra_ring

private theorem same_parameter_rate (F : PR 2) (x D : PTm n) (hx : Γ ⊢[PRAAx] pointCN F x)
    (hd : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx] independentRate F F x x zero D :=
  GaussianNamedRateRadius.weaken F F x x zero one zero D (le_refl one) hd
    (le_congr (zero_mul D).eqSymm (zero_mul one).eqSymm (le_refl zero))
    (GaussianNamedDifferenceRate.self_rate F x hx)

theorem local_modulus_at (F G : PR 2) (z Rz B x y C₀ C R₀ R a W E T t u A D : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B x y C₀ C R₀ R a W E T) (hd : Γ ⊢[PRAAx] le one D)
    (ht : Γ ⊢[PRAAx] inside a W E t) (hu : Γ ⊢[PRAAx] inside a W E u)
    (hn : Γ ⊢[PRAAx] distanceBounded (value t) (value u) A D) :
    Γ ⊢[PRAAx] independentRate (evaluatorName (evaluatorF F G)) (evaluatorName (evaluatorF F G))
      (nameData t (fixedData z B x y)) (nameData u (fixedData z B x y)) (lipschitz Rz C R E T*A) D := by
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let l := kernelData F G z B x y (fstT t) (sndT t)
  let r := kernelData F G z B x y (fstT u) (sndT u)
  let L := lipschitz Rz C R E T*A
  have raw := GaussianNamedDampingPowerIntegrand.original_rate F G F G z Rz B x y x y C₀ C R₀ R E T
    (fstT t) (sndT t) (fstT u) (sndT u) zero zero A D
    (kernel_source_at F G z Rz B x y C₀ C R₀ R a W E T t hs ht)
    (kernel_source_at F G z Rz B x y C₀ C R₀ R a W E T u hs hu) hd
    (same_parameter_rate F x D hs.andE₂.andE₁.andE₁ hd) (same_parameter_rate G y D hs.andE₂.andE₂.andE₁ hd) hn
  have hr : Γ ⊢[PRAAx] independentRate (kernelF F G) (kernelF F G) l r L D := by
    simpa only [GaussianNamedInverseRate.subst_independentRate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqSubst1 (independentRate (kernelF F G) (kernelF F G) (Syn.shift l) (Syn.shift r) (var 0) (Syn.shift D))
        (time_gain Rz C R E T A)
        (by simpa only [GaussianNamedInverseRate.subst_independentRate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using raw)
  have rs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] independentRate (kernelF F G) (kernelF F G) (sh l) (sh r) (sh L) (sh D) := by
    simpa only [Fm.shift,Syn.shift,GaussianNamedInverseRate.subst_independentRate,sh] using hr.shift.shift
  have ls : sh l = kernelData F G (sh z) (sh B) (sh x) (sh y) (fstT (sh t)) (sndT (sh t)) := by simp [sh,l,Syn.shift]
  have rs' : sh r = kernelData F G (sh z) (sh B) (sh x) (sh y) (fstT (sh u)) (sndT (sh u)) := by simp [sh,r,Syn.shift]
  have Ls : sh L = lipschitz (sh Rz) (sh C) (sh R) (sh E) (sh T)*sh A := by simp [sh,L,Syn.shift]
  refine .allI (.allI ?_)
  have near := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ (var 1) (var 0) rs
  rw [ls,rs',Ls] at near
  simpa only [independentRate,GaussianCompactRiemannName.subst_nameData,subst_fixedData,subst_lipschitz,PTm.subst_mul,Syn.shift,sh] using
    distance_congr (wrapped_at F G (var 1) (sh t) (sh z) (sh B) (sh x) (sh y)).eqSymm
      (wrapped_at F G (var 0) (sh u) (sh z) (sh B) (sh x) (sh y)).eqSymm (.eqRefl _) (.eqRefl _) near

theorem sampled_modulus (F G : PR 2) (z Rz B x y C₀ C R₀ R a W E T : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B x y C₀ C R₀ R a W E T) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.sampledModulus (evaluatorF F G) a W E (lipschitz Rz C R E T) (fixedData z B x y) := by
  let sh := fun s : PTm n => Syn.shift (Syn.shift (Syn.shift (Syn.shift s)))
  have ss : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      source F G (sh z) (sh Rz) (sh B) (sh x) (sh y) (sh C₀) (sh C) (sh R₀) (sh R) (sh a) (sh W) (sh E) (sh T) := by
    simpa only [Fm.shift,Syn.shift,subst_source,sh] using hs.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [localBody,subst_fixedData,subst_lipschitz,Syn.shift,sh] using
    local_modulus_at F G (sh z) (sh Rz) (sh B) (sh x) (sh y) (sh C₀) (sh C) (sh R₀) (sh R) (sh a) (sh W) (sh E) (sh T)
      (var 3) (var 2) (var 1) (var 0) ss.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem compact_input (F G : PR 2) (z Rz B x y C₀ C R₀ R a W E T : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B x y C₀ C R₀ R a W E T) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.input (evaluatorF F G) a W E (lipschitz Rz C R E T) T (fixedData z B x y) :=
  .andI hs.andE₁.andE₂.andE₁ (.andI hs.andE₁.andE₁.andE₂.andE₁
    (.andI (le_trans (le_add_left W a) hs.andE₁.andE₂.andE₂) (sampled_modulus F G _ _ _ _ _ _ _ _ _ _ _ _ _ hs)))

theorem name_regular (F G : PR 2) (z Rz B x y C₀ C R₀ R a W E T : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B x y C₀ C R₀ R a W E T) :
    Γ ⊢[PRAAx] pointCN (nameF F G) (data z Rz B x y C R a W E T) :=
  GaussianCompactRiemannName.name_regular (evaluatorF F G) _ _ _ _ _ _ (compact_input F G _ _ _ _ _ _ _ _ _ _ _ _ _ hs)

theorem actual_named_power_damped_compact_name_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
      (source F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⟶
        pointCN (nameF F G) (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 8) (var 9) (var 10) (var 11) (var 12))) :=
  closeUniv 13 (.impI (name_regular F G _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerCompact
