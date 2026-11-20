import Mathlib

/-!
# Rational Euler transport: definitions and named proof obligations

Blueprint for the finite arithmetic theorem in `ode_section.tex`.
This file has NOT been elaborated in the artifact runtime. It contains
executable mathematical definitions and Prop-valued goals, not proofs of
those goals. In particular, no successful host elaboration would constitute
an object-iPRA derivation.

The final port replaces QVec/QMat by the report's natural-coded rational
arrays, reifies the displayed recursions as fixed PR terms, Booleanizes the
finite norm inequalities, and proves the goals in `Prf PRAAx`. The relevant
existing arithmetic providers are `Foundations.DiscreteGronwall` and
`Foundations.OdeRefinement` in the pinned ProveIt repository.
-/

namespace CertifiedContinuation.ODE

abbrev QVec (d : Nat) := Fin d → ℚ
abbrev QMat (d : Nat) := Fin d → Fin d → ℚ

def vzero (d : Nat) : QVec d := fun _ => 0

def vadd {d : Nat} (x y : QVec d) : QVec d := fun i => x i + y i

def vsub {d : Nat} (x y : QVec d) : QVec d := fun i => x i - y i

def vscale {d : Nat} (a : ℚ) (x : QVec d) : QVec d := fun i => a * x i

def msub {d : Nat} (A B : QMat d) : QMat d := fun i j => A i j - B i j

def matvec {d : Nat} (A : QMat d) (x : QVec d) : QVec d :=
  fun i => ∑ j, A i j * x j

def matmul {d : Nat} (A B : QMat d) : QMat d :=
  fun i j => ∑ k, A i k * B k j

def identity (d : Nat) : QMat d := fun i j => if i = j then 1 else 0

/-- A total finite maximum, with default zero for the empty list. -/
def qmax : List ℚ → ℚ
  | [] => 0
  | a :: as => max a (qmax as)

def vnorm {d : Nat} (x : QVec d) : ℚ :=
  qmax ((List.finRange d).map (fun i => |x i|))

def mnorm {d : Nat} (A : QMat d) : ℚ :=
  qmax ((List.finRange d).map (fun i => ∑ j, |A i j|))

def InUnit (t : ℚ) : Prop := 0 ≤ t ∧ t ≤ 1

def dyadic (r : Nat) : ℚ := 1 / (2 : ℚ) ^ r

/-- Concrete fixed evaluator data; an arbitrary value of this structure is
not asserted to carry a primitive-recursive presentation. -/
structure KernelData (d : Nat) where
  coefficient : ℚ → QMat d
  K : Nat
  L : Nat
  U : Nat
  initial : QVec d

def CoefficientBounds {d : Nat} (D : KernelData d) : Prop :=
  (∀ t, InUnit t → mnorm (D.coefficient t) ≤ (D.K : ℚ)) ∧
  (∀ s t, InUnit s → InUnit t →
    mnorm (msub (D.coefficient t) (D.coefficient s)) ≤
      (D.L : ℚ) * |t - s|)

def InitialBound {d : Nat} (D : KernelData d) : Prop :=
  1 ≤ D.U ∧ vnorm D.initial ≤ (D.U : ℚ)

/-- A proof-bearing host contract, supplied only after proving its fields.
The object-theory port must supply literal iPRA derivations instead. -/
structure RationalMatrixContract (d : Nat) where
  data : KernelData d
  coefficients : CoefficientBounds data
  initial : InitialBound data

def G {d : Nat} (D : KernelData d) : ℚ := (3 : ℚ) ^ D.K

def Y {d : Nat} (D : KernelData d) : ℚ := G D * (D.U : ℚ)

def H {d : Nat} (D : KernelData d) : ℚ :=
  ((D.L : ℚ) + (D.K : ℚ) ^ 2) * Y D

def C {d : Nat} (D : KernelData d) : ℚ := G D * H D

/-- Totalized at n=0 by rational division. Every theorem below assumes n>0. -/
def node {d : Nat} (D : KernelData d) (n : Nat) : Nat → QVec d
  | 0 => D.initial
  | j + 1 =>
      let x := node D n j
      vadd x (vscale (1 / (n : ℚ))
        (matvec (D.coefficient ((j : ℚ) / (n : ℚ))) x))

/-- A total cell selector. Under InUnit t and t<1 it is floor(nt). -/
def cell (n : Nat) (t : ℚ) : Nat :=
  min (Int.toNat (⌊(n : ℚ) * t⌋ : ℤ)) (n - 1)

def polygon {d : Nat} (D : KernelData d) (n : Nat) (t : ℚ) : QVec d :=
  if t = 1 then node D n n
  else
    let j := cell n t
    let x := node D n j
    vadd x (vscale (t - (j : ℚ) / (n : ℚ))
      (matvec (D.coefficient ((j : ℚ) / (n : ℚ))) x))

def halfstep (n : Nat) : ℚ := 1 / (2 * (n : ℚ))

def fineTime (n j : Nat) : ℚ := (j : ℚ) * halfstep n

/-- The coarse polygon's exact defect when viewed at the fine mesh. -/
def residual {d : Nat} (D : KernelData d) (n j : Nat) : QVec d :=
  let t := fineTime n j
  let x := polygon D n t
  let y := polygon D n (fineTime n (j + 1))
  vsub (vsub y x) (vscale (halfstep n) (matvec (D.coefficient t) x))

def oddResidualFormula {d : Nat} (D : KernelData d) (n i : Nat) : QVec d :=
  let δ := halfstep n
  let t0 := fineTime n (2 * i)
  let t1 := fineTime n (2 * i + 1)
  let x := node D n i
  vscale δ
    (vsub (matvec (msub (D.coefficient t0) (D.coefficient t1)) x)
      (vscale δ (matvec (D.coefficient t1)
        (matvec (D.coefficient t0) x))))

def fineError {d : Nat} (D : KernelData d) (n j : Nat) : ℚ :=
  vnorm (vsub (polygon D n (fineTime n j)) (node D (2 * n) j))

/-- Bounds are computed by a finite scan; positivity ensures this finds an
exponent with M <= 2^e. Proving that fact is a named obligation below. -/
def exponentSearch (M : Nat) : Nat :=
  ((List.range (M + 1)).find? (fun e => decide (M ≤ 2 ^ e))).getD M

def positiveCeiling (q : ℚ) : Nat :=
  max 1 (Int.toNat (⌈q⌉ : ℤ))

def shift (q : ℚ) : Nat := exponentSearch (positiveCeiling q)

def rationalName {d : Nat} (D : KernelData d) (p : Nat) (t : ℚ) : QVec d :=
  polygon D (2 ^ (p + shift (C D))) t

/-- The weak pairwise convention admits every usual 2^-p approximation name. -/
def InitialNameLaw {d : Nat} (a : Nat → QVec d) (U : Nat) : Prop :=
  (∀ r, vnorm (a r) ≤ (U : ℚ)) ∧
  (∀ r s, vnorm (vsub (a r) (a s)) ≤ dyadic r + dyadic s)

def withInitial {d : Nat} (D : KernelData d) (v : QVec d) : KernelData d :=
  { D with initial := v }

def namedOutput {d : Nat} (D : KernelData d) (a : Nat → QVec d)
    (p : Nat) (t : ℚ) : QVec d :=
  let cv := shift (4 * G D)
  let cm := shift (4 * max 1 (C D))
  polygon (withInitial D (a (p + cv))) (2 ^ (p + cm)) t

def integrand {d : Nat} (D : KernelData d) (n : Nat) (t : ℚ) : QVec d :=
  matvec (D.coefficient t) (polygon D n t)

def leftSum {d : Nat} (f : ℚ → QVec d) (M : Nat) (t : ℚ) : QVec d :=
  fun i => (t / (M : ℚ)) *
    ∑ j ∈ Finset.range M, f ((j : ℚ) * t / (M : ℚ)) i

/-! ## Named, currently unproved obligations
These are definitions of propositions. They are not theorem declarations. -/

def GrowthGoal : Prop :=
  ∀ (n K j : Nat), 0 < n → j ≤ n →
    (1 + (K : ℚ) / (n : ℚ)) ^ j ≤ (3 : ℚ) ^ K

def ShiftGoal : Prop := ∀ q : ℚ, 0 ≤ q → q ≤ (2 : ℚ) ^ shift q

def NodeBoundGoal {d : Nat} (D : KernelData d) : Prop :=
  CoefficientBounds D → InitialBound D →
    ∀ n j, 0 < n → j ≤ n → vnorm (node D n j) ≤ Y D

def PolygonBoundGoal {d : Nat} (D : KernelData d) : Prop :=
  CoefficientBounds D → InitialBound D →
    ∀ n t, 0 < n → InUnit t → vnorm (polygon D n t) ≤ Y D

def SpatialCoherenceGoal {d : Nat} (D : KernelData d) : Prop :=
  CoefficientBounds D → InitialBound D →
    ∀ n s t, 0 < n → InUnit s → InUnit t →
      vnorm (vsub (polygon D n t) (polygon D n s)) ≤
        (D.K : ℚ) * Y D * |t - s|

def EvenResidualGoal {d : Nat} (D : KernelData d) : Prop :=
  ∀ n i, 0 < n → i < n → residual D n (2 * i) = vzero d

def OddResidualGoal {d : Nat} (D : KernelData d) : Prop :=
  ∀ n i, 0 < n → i < n →
    residual D n (2 * i + 1) = oddResidualFormula D n i

def ResidualBoundGoal {d : Nat} (D : KernelData d) : Prop :=
  CoefficientBounds D → InitialBound D →
    ∀ n j, 0 < n → j < 2 * n →
      vnorm (residual D n j) ≤ (halfstep n) ^ 2 * H D

def ErrorRecurrenceGoal {d : Nat} (D : KernelData d) : Prop :=
  CoefficientBounds D → InitialBound D →
    ∀ n j, 0 < n → j < 2 * n →
      fineError D n (j + 1) ≤
        (1 + (D.K : ℚ) * halfstep n) * fineError D n j +
        (halfstep n) ^ 2 * H D

def RefinementGoal {d : Nat} (D : KernelData d) : Prop :=
  CoefficientBounds D → InitialBound D →
    ∀ n t, 0 < n → InUnit t →
      vnorm (vsub (polygon D n t) (polygon D (2 * n) t)) ≤
        C D / (2 * (n : ℚ))

def DyadicTailGoal {d : Nat} (D : KernelData d) : Prop :=
  CoefficientBounds D → InitialBound D →
    ∀ r s t, r ≤ s → InUnit t →
      vnorm (vsub (polygon D (2 ^ r) t) (polygon D (2 ^ s) t)) ≤
        C D * dyadic r

def RationalNameGoal {d : Nat} (D : KernelData d) : Prop :=
  CoefficientBounds D → InitialBound D →
    ∀ p q t, p ≤ q → InUnit t →
      vnorm (vsub (rationalName D p t) (rationalName D q t)) ≤ dyadic p

def InitialStabilityGoal {d : Nat} (D : KernelData d) : Prop :=
  CoefficientBounds D → ∀ n t v w, 0 < n → InUnit t →
    vnorm (vsub (polygon (withInitial D v) n t)
      (polygon (withInitial D w) n t)) ≤ G D * vnorm (vsub v w)

def CoefficientStabilityGoal {d : Nat} (D E : KernelData d) : Prop :=
  D.K = E.K → D.U = E.U → D.initial = E.initial →
  CoefficientBounds D → CoefficientBounds E → InitialBound D →
    ∀ η, 0 ≤ η →
      (∀ t, InUnit t → mnorm (msub (D.coefficient t) (E.coefficient t)) ≤ η) →
      ∀ n t, 0 < n → InUnit t →
        vnorm (vsub (polygon D n t) (polygon E n t)) ≤
          (G D) ^ 2 * (D.U : ℚ) * η

def NamedOutputGoal {d : Nat} (D : KernelData d) (a : Nat → QVec d) : Prop :=
  CoefficientBounds D → 1 ≤ D.U → InitialNameLaw a D.U →
    ∀ p q t, p ≤ q → InUnit t →
      vnorm (vsub (namedOutput D a p t) (namedOutput D a q t)) ≤ dyadic p

def IntegralObservationGoal {d : Nat} (D : KernelData d) : Prop :=
  CoefficientBounds D → InitialBound D →
    ∀ n M t, 0 < n → 0 < M → InUnit t →
      vnorm (vsub (vsub (polygon D n t) D.initial)
        (leftSum (integrand D n) M t)) ≤
        H D / (n : ℚ) + H D / (M : ℚ)

/-!
## Object-iPRA port targets

1. `QCode` uses a signed-numerator natural code and a positive denominator.
   Total arithmetic has a fixed default on invalid codes; every theorem carries
   the denominator-validity bit. No reduction to lowest terms is required.
2. A `VecCode d` is a bounded-array code with d entries; a `MatCode d` has d*d
   entries. All index ranges become PR finite sums/maxima/Boolean folds.
3. `node`, `cell`, `polygon`, `residual`, `exponentSearch`, and `leftSum` are
   compiled once as PR programs. K,L,U,n,p and the data arrays are numerical
   arguments. Kernel choice is one fixed rational formula or a fixed finite
   instruction language; arbitrary PR syntax is not evaluated uniformly.
4. `NodeBoundGoal`, `OddResidualGoal`, and `ErrorRecurrenceGoal` become literal
   open-sequent `Prf PRAAx` endpoints at arbitrary terms. Denominator-cleared
   prefix arrays supply quantifier-free induction invariants.
5. Apply existing `OdeRefinement.node_bound` only after the concrete recurrence
   endpoint exists. Apply its geometric Cauchy lemma to the produced dyadic
   errors, then prove `RationalNameGoal` and `NamedOutputGoal` at the same
   object judgment.
6. `SpatialCoherenceGoal` is needed when interpreting pointwise names as one
   continuous function. `IntegralObservationGoal` supplies the finite common-
   refinement identity; a separately named semantic theorem interprets it as
   the integral equation. It is not silently imported into the object theory.
-/

end CertifiedContinuation.ODE
