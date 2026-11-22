import Mathlib

/-!
# Explicit rational analytic programs and targets: UNCOMPILED BLUEPRINT

These are host definitions and proposition-valued obligations.  No analytic
main theorem is asserted here.  For an iPRA theorem, replace these objects by
fixed `PR` definitions and prove their rational contracts in `Prf PRAAx`.
The report gives the finite invariants and a dependency order for that work.
-/

namespace ContinuousIPRA.AnalyticBlueprint

abbrev QVec (d : Nat) := Fin d → Rat

def eps (n : Nat) : Rat := 1 / (2 : Rat) ^ n

def vnorm {d : Nat} (x : QVec d) : Rat :=
  (List.ofFn fun i => |x i|).foldl max 0

def vadd {d : Nat} (x y : QVec d) : QVec d := fun i => x i + y i
def vsub {d : Nat} (x y : QVec d) : QVec d := fun i => x i - y i
def vscale {d : Nat} (a : Rat) (x : QVec d) : QVec d := fun i => a * x i

abbrev FieldEvaluator (d : Nat) := Rat → QVec d → Nat → QVec d

def inTube {d : Nat} (x₀ : QVec d) (T R t : Rat) (x : QVec d) : Prop :=
  0 ≤ t ∧ t ≤ T ∧ vnorm (vsub x x₀) ≤ R

structure FieldContract {d : Nat} (E : FieldEvaluator d)
    (x₀ : QVec d) (T R M Lt Lx : Rat) : Prop where
  time_pos : 0 < T
  radius_nonneg : 0 ≤ R
  bound_nonneg : 0 ≤ M
  time_lip_nonneg : 0 ≤ Lt
  state_lip_nonneg : 0 ≤ Lx
  tube_budget : T * (M + 1) ≤ R
  bound : ∀ t x p, inTube x₀ T R t x → vnorm (E t x p) ≤ M + eps p
  compatible : ∀ t x p s y q,
    inTube x₀ T R t x → inTube x₀ T R s y →
    vnorm (vsub (E t x p) (E s y q)) ≤
      Lt * |t-s| + Lx * vnorm (vsub x y) + eps p + eps q

def eulerNode {d : Nat} (E : FieldEvaluator d) (x₀ : QVec d)
    (h : Rat) (p : Nat) : Nat → QVec d
  | 0 => x₀
  | j + 1 =>
      let x := eulerNode E x₀ h p j
      vadd x (vscale h (E ((j : Rat) * h) x p))

def eulerPolygon {d : Nat} (E : FieldEvaluator d) (x₀ : QVec d)
    (T : Rat) (N p : Nat) (t : Rat) : QVec d :=
  if N = 0 then x₀ else
    let h := T / (N : Rat)
    let clipped := max 0 (min T t)
    let j := min N (Int.toNat ⌊clipped / h⌋)
    if j = N then eulerNode E x₀ h p N else
      let x := eulerNode E x₀ h p j
      vadd x (vscale (clipped - (j : Rat) * h) (E ((j : Rat) * h) x p))

def NodeInvariantObligation : Prop :=
  ∀ d (E : FieldEvaluator d) (x₀ : QVec d) T R M Lt Lx N p,
    FieldContract E x₀ T R M Lt Lx → 0 < N →
    ∀ j, j ≤ N →
      vnorm (vsub (eulerNode E x₀ (T / (N : Rat)) p j) x₀) ≤
        (j : Rat) * (T / (N : Rat)) * (M + 1)

def GronwallBudget (Lx T : Rat) : Rat :=
  (3 : Rat) ^ (Int.toNat ⌈Lx * T⌉)

def residue (T K : Rat) (N p : Nat) : Rat := eps p + K * T / (N : Rat)

def PolygonComparisonObligation : Prop :=
  ∀ d (E : FieldEvaluator d) (x₀ : QVec d) T R M Lt Lx N N' p p',
    FieldContract E x₀ T R M Lt Lx → 0 < N → 0 < N' →
    ∀ t, 0 ≤ t → t ≤ T →
      vnorm (vsub (eulerPolygon E x₀ T N p t) (eulerPolygon E x₀ T N' p' t)) ≤
        GronwallBudget Lx T * T *
          (residue T (Lt + Lx * (M + 1)) N p +
           residue T (Lt + Lx * (M + 1)) N' p')

def EulerNameObligation : Prop :=
  ∀ d (E : FieldEvaluator d) (x₀ : QVec d) T R M Lt Lx c,
    FieldContract E x₀ T R M Lt Lx →
    8 * max 1 (GronwallBudget Lx T * T * (1 + (Lt + Lx * (M+1)) * T)) ≤
      (2 : Rat)^c →
    ∀ n m t, 0 ≤ t → t ≤ T →
      vnorm (vsub
        (eulerPolygon E x₀ T (2^(n+c)) (n+c) t)
        (eulerPolygon E x₀ T (2^(m+c)) (m+c) t)) ≤ eps (n+3) + eps (m+3)

structure GaussianRat where
  re : Rat
  im : Rat
  deriving DecidableEq

namespace GaussianRat
def add (z w : GaussianRat) : GaussianRat := ⟨z.re+w.re, z.im+w.im⟩
def sub (z w : GaussianRat) : GaussianRat := ⟨z.re-w.re, z.im-w.im⟩
def mul (z w : GaussianRat) : GaussianRat :=
  ⟨z.re*w.re-z.im*w.im, z.re*w.im+z.im*w.re⟩
def scale (a : Rat) (z : GaussianRat) : GaussianRat := ⟨a*z.re, a*z.im⟩
def normSq (z : GaussianRat) : Rat := z.re^2+z.im^2
def inv (z : GaussianRat) : GaussianRat :=
  ⟨z.re/normSq z, -z.im/normSq z⟩
def pow (z : GaussianRat) : Nat → GaussianRat
  | 0 => ⟨1, 0⟩
  | n+1 => mul (pow z n) z
end GaussianRat

def segment (a b : GaussianRat) (u : Rat) : GaussianRat :=
  a.add ((b.sub a).scale u)

def segmentClearanceSq (a b w : GaussianRat) : Rat :=
  let v := b.sub a
  let z := a.sub w
  if v.normSq = 0 then z.normSq else
    let u := max 0 (min 1 (-(z.re*v.re+z.im*v.im)/v.normSq))
    (z.add (v.scale u)).normSq

def SegmentGuardObligation : Prop :=
  ∀ a b w δ,
    0 < δ → δ^2 ≤ segmentClearanceSq a b w →
    ∀ u, 0 ≤ u → u ≤ 1 → δ^2 ≤ ((segment a b u).sub w).normSq

def KernelIdentityObligation : Prop :=
  ∀ u h : GaussianRat, ∀ m : Nat,
    u.normSq ≠ 0 → (u.sub h).normSq ≠ 0 →
    (u.sub h).inv =
      ((List.range m).foldl (fun acc r =>
        acc.add ((h.pow r).mul ((u.pow (r+1)).inv))) ⟨0,0⟩).add
        ((h.pow m).mul (((u.pow m).mul (u.sub h)).inv))

/-!
Main remaining endpoints:
* NodeInvariantObligation: QF induction on j, with N and precision as parameters.
* PolygonComparisonObligation: exact common refinement, rational Gronwall.
* EulerNameObligation: specialize the proved bound and discharge its power budget.
* Integral equation: define the two regular names, then prove all Near(...;0)
  observations with explicit Euler and quadrature indices (report Section 6).
* SegmentGuardObligation: complete the square and split the clamping cases.
* KernelIdentityObligation: finite geometric identity after guarded denominator clearing.
* Quadrature, Taylor and derivative budgets: rational finite sum inequalities;
  semantic holomorphicity is a separate adequacy theorem.

The unguarded inv operation is total because Rat division is total.  Every
correctness theorem for inverse must retain its nonzero/positive clearance
premise.  Its value at zero has no analytic meaning.
-/

end ContinuousIPRA.AnalyticBlueprint
