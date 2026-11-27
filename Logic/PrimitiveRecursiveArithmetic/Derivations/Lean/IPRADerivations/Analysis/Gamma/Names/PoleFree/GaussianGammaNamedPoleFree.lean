import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaNamedPoleFreeModulus
import IPRADerivations.Foundations.FiniteQueryDemand
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius

/-!
# Original Gamma on regular complex names with a uniform pole certificate

Each output evaluates the original native Gamma program at a decoded
input observation. A finite maximum provides a common precision even
when the native modulus is supplied without a monotonicity theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFree

open_ipra
open LeanProofs.IPRA.Foundations.FiniteQueryDemand (finiteMaximum finiteMaximum_succ_bound)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaHalfPlaneInputContinuity (modulus subst_modulus)
open GaussianGammaReciprocalInverse (gammaF gammaData gamma_regular)
open GaussianRationalL1 (rawGaussian rawDen)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm cross_refl)
open GaussianNamedInverseRate (rate_at)
open GaussianNamedRateRadius (distance_at_later_clocks distance_at_succ_clocks)
open GaussianRationalDistanceOrder (distance_congr distance_of_ordered_observations)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (f : PR 2) (x R E : PTm n) : Fm PTm n := pointCN f x ⋏ .all
  (GaussianGammaReciprocalInverse.source (rawGaussian (ap2 f (var 0) (Syn.shift x)))
    (Syn.shift R) (rawDen (ap2 f (var 0) (Syn.shift x))) one (Syn.shift E))

ipra_subst source [Syn.subst_shift, Syn.shift_subst, one]

theorem source_at (f : PR 2) (k x R E : PTm n) (h : Γ ⊢[PRAAx] source f x R E) : Γ ⊢[PRAAx]
    GaussianGammaReciprocalInverse.source (rawGaussian (ap2 f k x)) R (rawDen (ap2 f k x)) one E := by
  simpa [Syn.subst_inst_shift,one] using h.andE₂.allE k

def demandBody : PTm 2 := modulus (var 0) (fstT (var 1)) (sndT (var 1))
def clock (p R E : PTm n) : PTm n := succ (finiteMaximum demandBody (succ (succ p)) (pairT R E))
def encodedData (f : PR 2) (k x R E : PTm n) : PTm n :=
  gammaData (rawGaussian (ap2 f k x)) R (rawDen (ap2 f k x)) E
def sample (f : PR 2) (p x R E : PTm n) : PTm n := ap2 gammaF (succ p) (encodedData f (clock p R E) x R E)
def data (x R E : PTm n) : PTm n := pairT x (pairT R E)
def nameF (f : PR 2) : PR 2 := PTm.toPR
  (sample f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))))

ipra_subst clock
ipra_subst encodedData [gammaData, GaussianGammaReciprocalInverse.gammaHeight]
ipra_subst sample
ipra_subst data

private theorem demand_at (s R E : PTm n) : Γ ⊢[PRAAx] inst2 demandBody s (pairT R E) ≐ modulus s R E := by
  have h := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (modulus (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![s,fstT (pairT R E),sndT (pairT R E)]) (σ' := ![s,R,E])
    (fun i => by fin_cases i; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _)
  simpa only [demandBody,inst2,subst_modulus,Syn.subst_var,
    subst_fstT,subst_sndT,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using h

theorem clock_demand (p R E s : PTm n) (hs : Γ ⊢[PRAAx] le s (succ p)) :
    Γ ⊢[PRAAx] le (succ (modulus s R E)) (clock p R E) := by
  exact finiteMaximum_succ_bound demandBody hs (demand_at s R E)

theorem name_at (f : PR 2) (p x R E : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF f) p (data x R E) ≐ sample f p x R E := by
  simpa [nameF, data, pairVector, pairVectorField] using
    (toPR_pairVector_eq (Γ := Γ) (k := 2)
      (sample f (var 0) (var 1) (var 2) (var 3)) p ![x, R, E])

theorem encoded_regular (f : PR 2) (k x R E : PTm n) (h : Γ ⊢[PRAAx] source f x R E) :
    Γ ⊢[PRAAx] pointCN gammaF (encodedData f k x R E) :=
  gamma_regular _ R _ one E (source_at f k x R E h)

theorem encoded_rate (f g : PR 2) (r t s x y R E : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R E) (hg : Γ ⊢[PRAAx] source g y R E)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hr : Γ ⊢[PRAAx] le (succ (modulus s R E)) r) (ht : Γ ⊢[PRAAx] le (succ (modulus s R E)) t) :
    Γ ⊢[PRAAx] GaussianNamedInverseRate.independentRate gammaF gammaF
      (encodedData f r x R E) (encodedData g t y R E) one (unit s) := by
  let u := ap2 f r x
  let v := ap2 g t y
  let m := modulus s R E
  have den := positive_product _ _ (unit_positive (Γ := Γ) r) (unit_positive t)
  have actual := GaussianFastValueCut.recode_distance_bound u v _ _ den (cross_at f g x y r t he)
  have near := distance_at_later_clocks r t m hr ht actual
  exact GaussianGammaNamedPoleFreeModulus.original_rate s (rawGaussian u) (rawGaussian v) R (rawDen u) (rawDen v) E
    (source_at f r x R E hf) (source_at g t y R E hg) near

private theorem observations_of_le (f g : PR 2) (p q x y R E : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R E) (hg : Γ ⊢[PRAAx] source g y R E)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (sample f p x R E) (sample g q y R E) (unit p+unit q) (unit p*unit q) := by
  let r := clock p R E
  let t := clock q R E
  let s := succ p
  have hs : Γ ⊢[PRAAx] le s (succ q) :=
    le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one hpq)
  have rate := encoded_rate f g r t s x y R E hf hg he
    (clock_demand p R E s (le_refl _)) (clock_demand q R E s hs)
  have obs := rate_at gammaF gammaF (encodedData f r x R E) (encodedData g t y R E) one (unit s) (succ p) (succ q) rate
  exact distance_at_succ_clocks _ _ p q obs

theorem original_observations (f g : PR 2) (p q x y R E : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R E) (hg : Γ ⊢[PRAAx] source g y R E)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x R E)) (ap2 (nameF g) q (data y R E))
      (unit p+unit q) (unit p*unit q) := by
  have sourceResult : Γ ⊢[PRAAx] distanceBounded (sample f p x R E) (sample g q y R E)
      (unit p+unit q) (unit p*unit q) := by
    exact distance_of_ordered_observations _ _ p q
      (observations_of_le f g p q x y R E hf.wk hg.wk he.wk Prf.hyp0)
      (observations_of_le g f q p y x R E hg.wk hf.wk (cross_symm _ _ _ _ he.wk) Prf.hyp0)
  exact distance_congr (name_at f p x R E).eqSymm (name_at g q y R E).eqSymm (.eqRefl _) (.eqRefl _) sourceResult

theorem proper (f g : PR 2) (x y R E : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R E) (hg : Γ ⊢[PRAAx] source g y R E)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x R E) (data y R E) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have sf : Δ ⊢[PRAAx] source f (sh x) (sh R) (sh E) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_source] using hf.shift.shift
  have sg : Δ ⊢[PRAAx] source g (sh y) (sh R) (sh E) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_source] using hg.shift.shift
  have se : Δ ⊢[PRAAx] crossEquivalent f g (sh x) (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,subst_data,Syn.shift,sh] using
    original_observations f g (var 1) (var 0) (sh x) (sh y) (sh R) (sh E) sf sg se

theorem name_regular (f : PR 2) (x R E : PTm n) (h : Γ ⊢[PRAAx] source f x R E) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x R E) := by
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit,crossEquivalent] using
    proper f f x x R E h h (cross_refl f x h.andE₁)

theorem actual_named_pole_free_Gamma_regular_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) (var 2) ⟶ pointCN (nameF f) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFree
