import ConciseIPRA.PR
import ObjectTraceCompiler
import RelationalWitnesses

/-!
# Application targets for the finitary-interface framework

This file gives semantic Lean statements with all finite data exposed.  They
are intended to be migrated to `Prf PRAAx` by the trace, Boolean, and relational
compilers.  The file was not compiled in the artifact environment.  Visible
`sorry` terms mark the remaining proof work.
-/

set_option autoImplicit false

namespace LeanProofs.ConciseIPRA.FinitaryInterface

open scoped BigOperators

/-! ## Rational balls and guarded reciprocal -/

structure RatBall where
  center : ℚ
  radius : ℚ
  radius_nonneg : 0 ≤ radius


def RatBall.Contains (B : RatBall) (x : ℚ) : Prop :=
  |x - B.center| ≤ B.radius

/-- The exact rational error radius around `1 / center`.  It is used only under
`radius < |center|`; the totalized value at a bad guard is harmless. -/
def reciprocalRadius (B : RatBall) : ℚ :=
  if B.radius < |B.center| then
    B.radius / (|B.center| * (|B.center| - B.radius))
  else 0

/-- Core guarded reciprocal estimate.  Clearing denominators turns the proof
into ordered-ring arithmetic suitable for an object-language verifier. -/
theorem guardedReciprocal_sound (B : RatBall) (x : ℚ)
    (hguard : B.radius < |B.center|) (hx : B.Contains x) :
    x ≠ 0 ∧ |x⁻¹ - B.center⁻¹| ≤ reciprocalRadius B := by
  sorry

/-! ## Cubic inverse by exact rational bisection -/

structure RatInterval where
  lo : ℚ
  hi : ℚ


def RatInterval.width (I : RatInterval) : ℚ := I.hi - I.lo

def RatInterval.midpoint (I : RatInterval) : ℚ := (I.lo + I.hi) / 2

def cubic (y : ℚ) : ℚ := y * y * y + y

def CubicBrackets (x : ℚ) (I : RatInterval) : Prop :=
  cubic I.lo ≤ x ∧ x ≤ cubic I.hi

/-- Total bisection step.  The branch is a decidable rational comparison. -/
def cubicBisect (x : ℚ) (I : RatInterval) : RatInterval :=
  let m := I.midpoint
  if cubic m ≤ x then ⟨m, I.hi⟩ else ⟨I.lo, m⟩


def cubicBisectN (x : ℚ) : Nat → RatInterval → RatInterval
  | 0, I => I
  | n + 1, I => cubicBisectN x n (cubicBisect x I)


def cubicInitial (x : ℚ) : RatInterval :=
  let B := |x| + 1
  ⟨-B, B⟩

/-- Strict monotonicity is the polynomial identity
`cubic b - cubic a = (b-a) * (a^2+a*b+b^2+1)`. -/
theorem cubic_strictMono : StrictMono cubic := by
  sorry


theorem cubicInitial_brackets (x : ℚ) : CubicBrackets x (cubicInitial x) := by
  sorry


theorem cubicBisect_preserves (x : ℚ) (I : RatInterval)
    (hI : CubicBrackets x I) :
    CubicBrackets x (cubicBisect x I) := by
  sorry


theorem cubicBisect_width (x : ℚ) (I : RatInterval) :
    (cubicBisect x I).width = I.width / 2 := by
  sorry

/-- Exact finite contract consumed by the trace compiler. -/
theorem cubicInverseContract (x : ℚ) (n : Nat) :
    CubicBrackets x (cubicBisectN x n (cubicInitial x)) ∧
    (cubicBisectN x n (cubicInitial x)).width =
      (cubicInitial x).width / (2 : ℚ) ^ n := by
  sorry

/-! ## Height bounds and complete finite lists -/

/-- `universe H` is a finite list containing every well-formed code of height
at most `H`.  This is the finite-ball producer needed for generic filtering. -/
structure HeightPresentation where
  point : Nat → Bool
  height : Nat → Nat
  universe : Nat → List Nat
  universe_complete : ∀ H c, height c ≤ H → c ∈ universe H


def HeightPresentation.pointsBelow (X : HeightPresentation) (H : Nat) : List Nat :=
  (X.universe H).filter fun c => X.point c


def HeightBound (X : HeightPresentation) (H : Nat) : Prop :=
  ∀ c, X.point c = true → X.height c ≤ H


def CompletePointList (X : HeightPresentation) (L : List Nat) : Prop :=
  (∀ c ∈ L, X.point c = true) ∧ (∀ c, X.point c = true → c ∈ L)


theorem completeListOfHeightBound (X : HeightPresentation) (H : Nat)
    (hH : HeightBound X H) : CompletePointList X (X.pointsBelow H) := by
  sorry


def listHeightBound (X : HeightPresentation) (L : List Nat) : Nat :=
  L.foldl (fun H c => max H (X.height c)) 0


theorem heightBoundOfCompleteList (X : HeightPresentation) (L : List Nat)
    (hL : CompletePointList X L) : HeightBound X (listHeightBound X L) := by
  sorry

/-! ## Finite simplicial carriers -/

structure FinSimplicialComplex (n : Nat) where
  simplex : Finset (Fin n) → Prop
  downClosed : ∀ {σ τ}, τ ⊆ σ → simplex σ → simplex τ


def SimplicialMap {n m : Nat} (K : FinSimplicialComplex n)
    (L : FinSimplicialComplex m) (f : Fin n → Fin m) : Prop :=
  ∀ σ, K.simplex σ → L.simplex (σ.image f)

/-- A strong carrier does not choose a target vertex.  It supplies a nonempty
finite cloud at each source vertex and one target simplex containing all clouds
above every source simplex. -/
structure StrongCarrier {n m : Nat} (K : FinSimplicialComplex n)
    (L : FinSimplicialComplex m) where
  cloud : Fin n → Finset (Fin m)
  nonempty : ∀ v, (cloud v).Nonempty
  carried : ∀ σ, K.simplex σ →
    ∃ τ, L.simplex τ ∧ ∀ v ∈ σ, cloud v ⊆ τ


def RespectsCarrier {n m : Nat} {K : FinSimplicialComplex n}
    {L : FinSimplicialComplex m} (C : StrongCarrier K L)
    (f : Fin n → Fin m) : Prop :=
  ∀ v, f v ∈ C.cloud v


def Contiguous {n m : Nat} (K : FinSimplicialComplex n)
    (L : FinSimplicialComplex m) (f g : Fin n → Fin m) : Prop :=
  ∀ σ, K.simplex σ →
    ∃ τ, L.simplex τ ∧
      (∀ v ∈ σ, f v ∈ τ) ∧ (∀ v ∈ σ, g v ∈ τ)


theorem carrierSelection_simplicial {n m : Nat}
    {K : FinSimplicialComplex n} {L : FinSimplicialComplex m}
    (C : StrongCarrier K L) (f : Fin n → Fin m)
    (hf : RespectsCarrier C f) : SimplicialMap K L f := by
  sorry


theorem carrierSelections_contiguous {n m : Nat}
    {K : FinSimplicialComplex n} {L : FinSimplicialComplex m}
    (C : StrongCarrier K L) (f g : Fin n → Fin m)
    (hf : RespectsCarrier C f) (hg : RespectsCarrier C g) :
    Contiguous K L f g := by
  sorry

/-- Follow-on target: instantiate the explicit finite prism operator over
`ZMod 2` and derive equality of induced homology maps. -/
theorem carrierMapChoiceIndependence : True := by
  trivial

/-! ## Strong finite affine gluing -/

section AffineGluing

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

structure StrongAffineDatum (r N : Nat) where
  f : Fin r → R
  a : Fin r → R
  local : Fin r → M
  cover : (∑ i, a i * (f i) ^ N) = 1
  compat : ∀ i j, (f j) ^ N • local i = (f i) ^ N • local j


def StrongAffineDatum.glued {r N : Nat} (D : StrongAffineDatum (R := R) (M := M) r N) : M :=
  ∑ i, D.a i • D.local i

/-- Cross-multiplied form of the localization statement: the glued global
section restricts to the supplied local numerator on every standard open. -/
theorem finiteAffineGluing {r N : Nat}
    (D : StrongAffineDatum (R := R) (M := M) r N) (k : Fin r) :
    (D.f k) ^ N • D.glued = D.local k := by
  sorry

end AffineGluing

/-!
Object-language migration:

* encode rational and finite-table operations by fixed `PR` symbols;
* Booleanize each displayed finite invariant;
* package bisection, filtering, finite maximum, prism checking, and finite sums
  as `PRTraceSystem`s;
* use local ring/order proofs as `TraceProofs` fields;
* invoke `traceReflection` and only then `pra_iff_native`.
-/

end LeanProofs.ConciseIPRA.FinitaryInterface
