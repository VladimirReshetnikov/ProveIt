import ContinuousMeasure.Truncation

/-!
# Fully typed numerical presentations and remaining proof targets

The finite rows below are actual arrays. The record fields are quantitative
admissibility hypotheses, not new axioms. Definitions ending in `Goal` state
integration targets and do not by themselves assert theorems. ActionCompletion
proves the dense-action target; the completed-name Vitali target stays open.

This host-level API permits arbitrary Lean functions between codes. An iPRA
instance additionally fixes primitive-recursive programs for these functions
and constructs their object-language contracts. No universal PR evaluator is
assumed by these declarations.
-/

namespace IPRAContinuousMeasure

def ratEntry (a : Array Rat) (i : Nat) : Rat := a[i]?.getD 0
def natEntry (a : Array Nat) (i : Nat) : Nat := a[i]?.getD 0
def dyadic (p : Nat) : Rat := (1 / 2 : Rat) ^ p

structure FiniteProbability where
  weights : Array Rat
  nonneg : ∀ i, i < weights.size → 0 ≤ ratEntry weights i
  normalized : qsum (ratEntry weights) weights.size = 1

namespace FiniteProbability

def size (P : FiniteProbability) : Nat := P.weights.size
def weight (P : FiniteProbability) : Nat → Rat := ratEntry P.weights
def integral (P : FiniteProbability) (f : Nat → Rat) : Rat :=
  integrate P.size P.weight f
def l1 (P : FiniteProbability) (f g : Nat → Rat) : Rat :=
  P.integral (fun i => (f i - g i).abs)
def rho (P : FiniteProbability) (f g : Nat → Rat) : Rat :=
  P.integral (fun i => cappedDistance (f i) (g i))

theorem l1_nonneg (P : FiniteProbability) (f g : Nat → Rat) :
    0 ≤ P.l1 f g :=
  integrate_nonneg P.nonneg (fun _ _ => Rat.abs_nonneg)

theorem l1_self (P : FiniteProbability) (f : Nat → Rat) : P.l1 f f = 0 := by
  unfold l1 integral integrate
  simp only [Rat.sub_self, Rat.abs_zero, Rat.mul_zero, qsum_zero]

theorem l1_symm (P : FiniteProbability) (f g : Nat → Rat) :
    P.l1 f g = P.l1 g f := by
  unfold l1 integral integrate
  apply qsum_ext
  intro i _
  dsimp only
  rw [Rat.abs_sub_comm]

theorem l1_triangle (P : FiniteProbability) (f g h : Nat → Rat) :
    P.l1 f h ≤ P.l1 f g + P.l1 g h := by
  have hpoint : ∀ i, i < P.size →
      (f i - h i).abs ≤ (f i - g i).abs + (g i - h i).abs := by
    intro i _
    exact (within_abs_iff _ _ _).mp (within_triangle
      ((within_abs_iff _ _ _).mpr Rat.le_refl)
      ((within_abs_iff _ _ _).mpr Rat.le_refl))
  have hi := integrate_mono P.nonneg hpoint
  simpa only [integrate_add, l1, integral, size, weight] using hi

theorem integral_l1_bound (P : FiniteProbability) (f g : Nat → Rat) :
    Within (P.l1 f g) (P.integral f) (P.integral g) :=
  expectation_error P.nonneg (fun _ _ =>
    (within_abs_iff _ _ _).mpr Rat.le_refl)

theorem rho_le_l1 (P : FiniteProbability) (f g : Nat → Rat) :
    P.rho f g ≤ P.l1 f g := by
  apply integrate_mono P.nonneg
  intro i _
  have ha : 0 ≤ (f i - g i).abs := Rat.abs_nonneg
  grind [cappedDistance]

end FiniteProbability

/-- `Refinement coarse fine` is a finite partition refinement including all
mass equations, also for zero-mass coarse cells. -/
structure Refinement (coarse fine : FiniteProbability) where
  parent : Array Nat
  length : parent.size = fine.size
  inRange : ∀ j, j < fine.size → natEntry parent j < coarse.size
  mass : ∀ i, i < coarse.size →
    qsum (fun j => if natEntry parent j = i then fine.weight j else 0) fine.size =
      coarse.weight i

def Refinement.pull {P Q : FiniteProbability} (r : Refinement P Q)
    (f : Nat → Rat) : Nat → Rat := fun j => f (natEntry r.parent j)

/-- Exact integration is unchanged by a certified finite refinement. -/
theorem refinement_integral {P Q : FiniteProbability} (r : Refinement P Q)
    (f : Nat → Rat) : Q.integral (r.pull f) = P.integral f := by
  let F : Nat → Nat → Rat :=
    fun i j => if natEntry r.parent j = i then Q.weight j * f i else 0
  have row : ∀ i, i < P.size → qsum (F i) Q.size = P.weight i * f i := by
    intro i hi
    calc
      qsum (F i) Q.size =
          qsum (fun j => f i * (if natEntry r.parent j = i then Q.weight j else 0)) Q.size := by
        apply qsum_ext
        intro j _
        dsimp [F]
        split <;> grind
      _ = f i * qsum (fun j => if natEntry r.parent j = i then Q.weight j else 0) Q.size :=
        qsum_scale _ _ _
      _ = P.weight i * f i := by rw [r.mass i hi]; exact Rat.mul_comm _ _
  have col : ∀ j, j < Q.size →
      qsum (fun i => F i j) P.size = Q.weight j * f (natEntry r.parent j) := by
    intro j hj
    calc
      qsum (fun i => F i j) P.size =
          qsum (fun i => if i = natEntry r.parent j then
            Q.weight j * f (natEntry r.parent j) else 0) P.size := by
        apply qsum_ext
        intro i _
        dsimp [F]
        grind
      _ = Q.weight j * f (natEntry r.parent j) :=
        qsum_single _ (r.inRange j hj)
  unfold FiniteProbability.integral integrate Refinement.pull
  calc
    qsum (fun j => Q.weight j * f (natEntry r.parent j)) Q.size =
        qsum (fun j => qsum (fun i => F i j) P.size) Q.size :=
      qsum_ext (fun j hj => (col j hj).symm)
    _ = qsum (fun i => qsum (F i) Q.size) P.size := (qsum_exchange F P.size Q.size).symm
    _ = qsum (fun i => P.weight i * f i) P.size := qsum_ext row

theorem refinement_l1 {P Q : FiniteProbability} (r : Refinement P Q)
    (f g : Nat → Rat) : Q.l1 (r.pull f) (r.pull g) = P.l1 f g :=
  refinement_integral r (fun i => (f i - g i).abs)

theorem refinement_rho {P Q : FiniteProbability} (r : Refinement P Q)
    (f g : Nat → Rat) : Q.rho (r.pull f) (r.pull g) = P.rho f g :=
  refinement_integral r (fun i => cappedDistance (f i) (g i))

theorem refinement_tail {P Q : FiniteProbability} (r : Refinement P Q)
    (K : Rat) (f : Nat → Rat) :
    Q.integral (fun i => tail K (r.pull f i)) = P.integral (fun i => tail K (f i)) :=
  refinement_integral r (fun i => tail K (f i))

/-- Coherent countable tower of finite probability presentations. Only the
finite data needed by a query are evaluated. -/
structure ProbabilityTower where
  stage : Nat → FiniteProbability
  refine : ∀ s t, s ≤ t → Refinement (stage s) (stage t)
  identity : ∀ s j (_hj : j < (stage s).size),
    natEntry (refine s s (Nat.le_refl s)).parent j = j
  composition : ∀ s t u (hst : s ≤ t) (htu : t ≤ u) j
      (_hj : j < (stage u).size),
    natEntry (refine s u (Nat.le_trans hst htu)).parent j =
      natEntry (refine s t hst).parent (natEntry (refine t u htu).parent j)

structure SimpleTable (A : ProbabilityTower) where
  level : Nat
  values : Array Rat
  length : values.size = (A.stage level).size

namespace SimpleTable

def row {A : ProbabilityTower} (f : SimpleTable A) : Nat → Rat := ratEntry f.values

def lift {A : ProbabilityTower} (f : SimpleTable A) (t : Nat) (ht : f.level ≤ t) :
    Nat → Rat := (A.refine f.level t ht).pull f.row

def common {A : ProbabilityTower} (f g : SimpleTable A) : Nat := max f.level g.level

def distance {A : ProbabilityTower} (f g : SimpleTable A) : Rat :=
  (A.stage (common f g)).l1
    (f.lift (common f g) (Nat.le_max_left _ _))
    (g.lift (common f g) (Nat.le_max_right _ _))

def measureDistance {A : ProbabilityTower} (f g : SimpleTable A) : Rat :=
  (A.stage (common f g)).rho
    (f.lift (common f g) (Nat.le_max_left _ _))
    (g.lift (common f g) (Nat.le_max_right _ _))

def tailIntegral {A : ProbabilityTower} (f : SimpleTable A) (K : Rat) : Rat :=
  (A.stage f.level).integral (fun i => tail K (f.row i))

end SimpleTable

/-- Regular L1 names use the standard symmetric dyadic Cauchy bound. -/
structure RegularL1Name (A : ProbabilityTower) where
  sample : Nat → SimpleTable A
  regular : ∀ p q, SimpleTable.distance (sample p) (sample q) ≤ dyadic p + dyadic q

/-- A continuous-in-measure name, which alone need not be an L1 name. -/
structure RegularMeasureName (A : ProbabilityTower) where
  sample : Nat → SimpleTable A
  regular : ∀ p q,
    SimpleTable.measureDistance (sample p) (sample q) ≤ dyadic p + dyadic q

def SameL1Name {A : ProbabilityTower} (f g : RegularL1Name A) : Prop :=
  ∀ p, SimpleTable.distance (f.sample p) (g.sample p) ≤ 2 * dyadic p

/-- A quantitative uniform integrability contract expressed using continuous
clipping tails. The dyadic-p slack is the sampling error of a regular name. -/
structure UniformTailControl {A : ProbabilityTower} (f : Nat → RegularL1Name A) where
  cutoff : Nat → Nat
  positive : ∀ k, 1 ≤ cutoff k
  bound : ∀ n k p, ((f n).sample p).tailIntegral (cutoff k : Rat) ≤
    dyadic k + dyadic p

structure TailControl {A : ProbabilityTower} (f : RegularL1Name A) where
  cutoff : Nat → Nat
  positive : ∀ k, 1 ≤ cutoff k
  bound : ∀ k p, (f.sample p).tailIntegral (cutoff k : Rat) ≤ dyadic k + dyadic p

/-- An explicit rate for convergence in the bounded continuous measure metric. -/
structure InMeasureRate {A : ProbabilityTower} (f : Nat → RegularL1Name A)
    (g : RegularL1Name A) where
  index : Nat → Nat
  bound : ∀ k n, index k ≤ n → ∀ p,
    SimpleTable.measureDistance ((f n).sample p) (g.sample p) ≤
      dyadic k + 2 * dyadic p

/-- Target after finite Vitali, refinement invariance and completion have been
assembled. This definition does not claim the target is proved. -/
def VitaliConvergenceGoal {A : ProbabilityTower} (f : Nat → RegularL1Name A)
    (g : RegularL1Name A) (index : Nat → Nat) : Prop :=
  ∀ k n, index k ≤ n → ∀ p,
    SimpleTable.distance ((f n).sample p) (g.sample p) ≤ dyadic k + 2 * dyadic p

/-- A dense action approximated at requested output precision, with a
uniform gain bound. Such data are enough for the standard extension argument;
linearity or positivity can be added as separate numerical contracts. -/
structure DenseAction (A B : ProbabilityTower) where
  run : SimpleTable A → Nat → SimpleTable B
  gain : Rat
  gainNonneg : 0 ≤ gain
  stability : ∀ f g p q,
    SimpleTable.distance (run f p) (run g q) ≤
      gain * SimpleTable.distance f g + dyadic p + dyadic q

def actionSample {A B : ProbabilityTower} (T : DenseAction A B)
    (f : RegularL1Name A) (gainBound p : Nat) : SimpleTable B :=
  T.run (f.sample (p + gainBound + 2)) (p + 2)

def ActionRegularityGoal {A B : ProbabilityTower} (T : DenseAction A B)
    (f : RegularL1Name A) (gainBound : Nat) : Prop :=
  ∀ p q, SimpleTable.distance (actionSample T f gainBound p)
      (actionSample T f gainBound q) ≤ dyadic p + dyadic q

end IPRAContinuousMeasure
