import IPRADerivations.Analysis.GaussianBoundedIntegerExponential

/-!
# Integer-scaled exponential at a numerical base sample

The original exponential stages can be compared with the exact
rational powers of a single approximate base. Only a same-precision
distance certificate is required for that sample.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianBoundedIntegerExponentialSample

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBoundedIntegerExponential (error error_zero error_growth)
open GaussianBoundedIntegerExponentialStages (scaledF stageData radius expF expData point majorant
  powerBudget productF productData power_bound)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans point_at)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (power power_succ bound_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem stage_input (f : PR 2) (E i R x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) (hi : Γ ⊢[PRAAx] le i E) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input (scaledF f) (radius E R) (stageData E i x) :=
  GaussianNamedNaturalScale.exponential_input f E i R x h hi

theorem point_bound (f : PR 2) (p E i R x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) (hi : Γ ⊢[PRAAx] le i E) :
    Γ ⊢[PRAAx] bounded (point f p E i R x) (majorant E R) one :=
  bound_congr (GaussianRadiusExponentialName.sample_at _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianPositiveExponentialMajorant.disk_bound _ _ _
      (GaussianRadiusExponentialName.query_bound _ _ _ _ (stage_input f E i R x h hi)))

theorem one_cross (f : PR 2) (E R x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] crossEquivalent (expF f) (GaussianRadiusExponentialName.nameF f)
      (expData E one R x) (GaussianRadiusExponentialName.data R x) :=
  GaussianExponentialRadiusIndependence.independent_radii_proper (scaledF f) f
    (radius E R) R (stageData E one x) x (stage_input f E one R x h hE) h
    (GaussianNamedNaturalScale.one_cross f E R x h)

theorem successor_cross (f : PR 2) (E i R x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) (hi : Γ ⊢[PRAAx] le (succ i) E) :
    Γ ⊢[PRAAx] crossEquivalent (productF f) (expF f) (productData f E i R x) (expData E (succ i) R x) := by
  have a := stage_input f E i R x h (le_trans (le_succ_self i) hi)
  have b := stage_input f E one R x h (le_trans (zero_lt_succ i) hi)
  have prod := GaussianExponentialAddition.exponential_add_cross (scaledF f) (scaledF f) (radius E R)
    (stageData E i x) (stageData E one x) (GaussianNamedNaturalScale.radius_positive E R) a b
  have c := GaussianExponentialRadiusIndependence.independent_radii_proper
    (GaussianNameArithmetic.addF (scaledF f) (scaledF f)) (scaledF f) (radius E R+radius E R) (radius E R)
    (GaussianNamedNaturalScale.addData E i x) (stageData E (succ i) x)
    (GaussianExponentialReference.add_input _ _ _ _ _ a b) (stage_input f E (succ i) R x h hi)
    (GaussianNamedNaturalScale.add_step_cross f E i R x h hi)
  exact cross_trans _ _ _ _ _ _ prod c

private theorem later_point (f : PR 2) (p q E i R x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) (hi : Γ ⊢[PRAAx] le i E)
    (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (point f q E i R x) (point f p E i R x) two (unit p) := by
  have regular := GaussianRadiusExponentialName.name_regular _ _ _ (stage_input f E i R x h hi)
  have grow := GaussianExponentialReference.unit_monotone hpq
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive p)) (unit_positive p) _
    (point_at _ _ q p regular)
  ipra_le 𝔞(unit p)*sl grow

theorem successor_sample (f : PR 2) (p E i R x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) (hi : Γ ⊢[PRAAx] le (succ i) E) :
    Γ ⊢[PRAAx] distanceBounded (point f p E (succ i) R x)
      (qmul (point f p E i R x) (point f p E one R x)) (two+num 4*majorant E R) (unit p) := by
  let s := GaussianNamedSmallPerturbationTransport.productClock (expF f) (expF f) (expData E i R x) (expData E one R x) p
  have hs : Γ ⊢[PRAAx] le p s := le_add_right _ _
  have hi' := le_trans (le_succ_self i) hi
  have hE := le_trans (zero_lt_succ i) hi
  have raw := GaussianNameArithmetic.product_distance (point f s E i R x) (point f p E i R x)
    (point f s E one R x) (point f p E one R x) two two (unit p) (majorant E R) (majorant E R) (unit_positive p)
    (later_point f p s E i R x h hi' hs) (later_point f p s E one R x h hE hs)
    (point_bound f s E one R x h hE) (point_bound f p E i R x h hi')
  have same : Γ ⊢[PRAAx] distanceBounded (ap2 (productF f) p (productData f E i R x))
      (qmul (point f p E i R x) (point f p E one R x)) (num 4*majorant E R) (unit p) := distance_congr
    (GaussianNamedSmallPerturbationTransport.product_at (expF f) (expF f) _ _ p).eqSymm
    (.eqRefl _) (by ipra_ring) (.eqRefl _) raw
  have den := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive p)
  have first := distance_symmetric _ _ _ _ den (cross_at _ _ _ _ p p (successor_cross f E i R x h hi))
  have closer := distance_radius_mono _ _ _ _ two (unit p) den (unit_positive p)
    (le_of_eq_add (d := zero) (by ipra_ring)) first
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p) closer same

def sampleBudget (E i R A H : PTm n) : PTm n := (H+one)*error E i R A

@[simp] theorem subst_sampleBudget {l : ℕ} (σ : Fin n → PTm l) (E i R A H : PTm n) :
    Syn.subst σ (sampleBudget E i R A H) =
      sampleBudget (Syn.subst σ E) (Syn.subst σ i) (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ H) := by
  simp [sampleBudget,one]

private theorem sample_budget_growth (E i R A H : PTm n) :
    Γ ⊢[PRAAx] le (two+num 4*majorant E R+majorant E R*sampleBudget E i R A H+H*powerBudget E A)
      (sampleBudget E (succ i) R A H) := by
  have g := GaussianBoundedIntegerExponential.error_growth (Γ := Γ) E i R A
  ipra_le (𝔞 H+1)*sl g+𝔞 H*(2+4*𝔞(majorant E R)+𝔞(powerBudget E A))+2*𝔞(powerBudget E A) using
    unfold sampleBudget GaussianBoundedIntegerExponential.stepCost
    ipra_simps
    ring

private theorem sample_step (f : PR 2) (p E i R x c A H : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) (hc : Γ ⊢[PRAAx] bounded c A one)
    (base : Γ ⊢[PRAAx] distanceBounded (point f p E one R x) c H (unit p))
    (hi : Γ ⊢[PRAAx] le (succ i) E)
    (previous : Γ ⊢[PRAAx] distanceBounded (point f p E i R x) (power c i) (sampleBudget E i R A H) (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (point f p E (succ i) R x) (power c (succ i)) (sampleBudget E (succ i) R A H) (unit p) := by
  have old := le_trans (le_succ_self i) hi
  have oneE := le_trans (zero_lt_succ i) hi
  have raw := GaussianNameArithmetic.product_distance (point f p E i R x) (power c i) (point f p E one R x) c
    (sampleBudget E i R A H) H (unit p) (majorant E R) (powerBudget E A) (unit_positive p) previous base
    (point_bound f p E one R x hf oneE) (power_bound c A E i hc old)
  have right := distance_congr (.eqRefl _) (power_succ c i).eqSymm (.eqRefl _) (.eqRefl _) raw
  have whole := distance_triangle_same _ _ _ _ _ _ (unit_positive p) (successor_sample f p E i R x hf hi) right
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive p) (unit_positive p)
    (le_congr (by ipra_ring) (.eqRefl _)
      (AnalyticNumberTheory.PhiLower.le_mul_mono (sample_budget_growth E i R A H) (le_refl (unit p)))) whole

theorem prefix_error (f : PR 2) (p E i R x c A H : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) (hc : Γ ⊢[PRAAx] bounded c A one)
    (base : Γ ⊢[PRAAx] distanceBounded (point f p E one R x) c H (unit p))
    (hi : Γ ⊢[PRAAx] le i E) :
    Γ ⊢[PRAAx] distanceBounded (point f p E i R x) (power c i) (sampleBudget E i R A H) (unit p) := by
  let law := fun (E p R x c A H i : PTm (n+1)) => le i E ⟶
    distanceBounded (point f p E i R x) (power c i) (sampleBudget E i R A H) (unit p)
  have hf' : Γ.map Fm.shift ⊢[PRAAx] GaussianRadiusExponentialName.input f (Syn.shift R) (Syn.shift x) :=
    by simpa [Fm.shift,Syn.shift] using hf.shift
  have hc' : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift c) (Syn.shift A) one :=
    by simpa [Fm.shift,Syn.shift,one] using hc.shift
  have hb' : Γ.map Fm.shift ⊢[PRAAx] distanceBounded (point f (Syn.shift p) (Syn.shift E) one (Syn.shift R) (Syn.shift x))
      (Syn.shift c) (Syn.shift H) (unit (Syn.shift p)) := by
    simpa [Fm.shift,Syn.shift,one] using base.shift
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift E) ⟶
      distanceBounded (point f (Syn.shift p) (Syn.shift E) (var 0) (Syn.shift R) (Syn.shift x)) (power (Syn.shift c) (var 0))
        (sampleBudget (Syn.shift E) (var 0) (Syn.shift R) (Syn.shift A) (Syn.shift H)) (unit (Syn.shift p))) := by
    refine PRA.qfInd _ ⟨trivial,trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp,subst_le,GaussianRationalMetric.subst_distanceBounded,GaussianBoundedIntegerExponentialStages.subst_point,
        GaussianRationalReciprocal.subst_power,subst_sampleBudget,GaussianCoefficientNameBounds.subst_unit,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      have grow : Γ ⊢[PRAAx] le (error E zero R A*unit p) (sampleBudget E zero R A H*unit p) :=
        le_of_eq_add (d := H*error E zero R A*unit p) (by unfold sampleBudget; ipra_ring)
      exact .impI (distance_radius_mono _ _ _ _ _ _ (unit_positive p) (unit_positive p) grow (error_zero f p E R x c A)).wk
    · simp only [Fm.subst_imp,subst_le,GaussianRationalMetric.subst_distanceBounded,GaussianBoundedIntegerExponentialStages.subst_point,
        GaussianRationalReciprocal.subst_power,subst_sampleBudget,GaussianCoefficientNameBounds.subst_unit,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let I := law (Syn.shift E) (Syn.shift p) (Syn.shift R) (Syn.shift x) (Syn.shift c) (Syn.shift A) (Syn.shift H) (var 0)
      let Δ := le (succ (var 0)) (Syn.shift E) :: I :: Γ.map Fm.shift
      have prev : Δ ⊢[PRAAx] I := Prf.hyp1
      exact sample_step f (Syn.shift p) (Syn.shift E) (var 0) (Syn.shift R) (Syn.shift x) (Syn.shift c)
        (Syn.shift A) (Syn.shift H) hf'.wk.wk hc'.wk.wk hb'.wk.wk Prf.hyp0
        (.impE prev (le_trans (le_succ_self (var 0 : PTm (n+1))) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] le i E ⟶
      distanceBounded (point f p E i R x) (power c i) (sampleBudget E i R A H) (unit p) := by
    simpa only [Fm.subst_imp,subst_le,GaussianRationalMetric.subst_distanceBounded,GaussianBoundedIntegerExponentialStages.subst_point,
      GaussianRationalReciprocal.subst_power,subst_sampleBudget,GaussianCoefficientNameBounds.subst_unit,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE i
  exact .impE rule hi

theorem actual_integer_exponential_sample_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((GaussianRadiusExponentialName.input f (var 3) (var 4) ⋏ bounded (var 5) (var 6) one) ⟶
      distanceBounded (point f (var 0) (var 1) one (var 3) (var 4)) (var 5) (var 7) (unit (var 0)) ⟶
      le (var 2) (var 1) ⟶ distanceBounded (point f (var 0) (var 1) (var 2) (var 3) (var 4))
        (power (var 5) (var 2)) (sampleBudget (var 1) (var 2) (var 3) (var 6) (var 7)) (unit (var 0))) :=
  closeUniv 8 (.impI (.impI (.impI (prefix_error f _ _ _ _ _ _ _ _ hyp2.andE₁ hyp2.andE₂ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBoundedIntegerExponentialSample
