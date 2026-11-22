import Std

/-!
Finite host definitions and named targets for the small-gain extension.

These definitions are a Lean-oriented blueprint.  A value of one of the
`...Target` propositions is not supplied here.  The repository integration
must replace rational vectors by their PR sequence codes and construct the
corresponding literal `Prf PRAAx` derivations.  No `axiom` or `sorry` asserts
those obligations.  The function argument `E` is a host parameter; in an
object-iPRA application it must be one fixed supplied PR program.
-/

namespace CoupledIPRA

abbrev Vec (d : Nat) := Fin d → Rat
abbrev Mat (d : Nat) := Fin d → Fin d → Rat

def absQ (x : Rat) : Rat := if x < 0 then -x else x
def maxQ (x y : Rat) : Rat := if x ≤ y then y else x
def sumQ {d : Nat} (f : Fin d → Rat) : Rat :=
  (List.ofFn f).foldl (fun a b => a + b) 0
def maxZeroQ {d : Nat} (f : Fin d → Rat) : Rat :=
  (List.ofFn f).foldl maxQ 0
def dyadic (p : Nat) : Rat := 1 / (2 : Rat)^p

def zero {d : Nat} : Vec d := fun _ => 0
def ones {d : Nat} : Vec d := fun _ => 1
def add {d : Nat} (x y : Vec d) : Vec d := fun i => x i + y i
def sub {d : Nat} (x y : Vec d) : Vec d := fun i => x i - y i
def scale {d : Nat} (a : Rat) (x : Vec d) : Vec d := fun i => a * x i
def absolute {d : Nat} (x : Vec d) : Vec d := fun i => absQ (x i)
def LE {d : Nat} (x y : Vec d) : Prop := ∀ i, x i ≤ y i
def mv {d : Nat} (a : Mat d) (x : Vec d) : Vec d :=
  fun i => sumQ (fun j => a i j * x j)
def weightedNorm {d : Nat} (w x : Vec d) : Rat :=
  maxZeroQ (fun i => absQ (x i) / w i)
def dist {d : Nat} (w x y : Vec d) : Rat := weightedNorm w (sub x y)

structure Box (d : Nat) where
  lower : Vec d
  upper : Vec d

def InBox {d : Nat} (box : Box d) (x : Vec d) : Prop :=
  ∀ i, box.lower i ≤ x i ∧ x i ≤ box.upper i

structure Data (d : Nat) where
  matrix : Mat d
  weights : Vec d
  reciprocalGap : Nat

def contraction {d : Nat} (c : Data d) : Rat :=
  1 - 1 / (c.reciprocalGap : Rat)

def SmallGain {d : Nat} (c : Data d) : Prop :=
  1 ≤ c.reciprocalGap ∧
  (∀ i, 0 < c.weights i) ∧
  (∀ i j, 0 ≤ c.matrix i j) ∧
  LE (mv c.matrix c.weights) (scale (contraction c) c.weights)

def Diameter {d : Nat} (c : Data d) (box : Box d) (r : Rat) : Prop :=
  0 ≤ r ∧ ∀ i, box.upper i - box.lower i ≤ r * c.weights i

def ActionContract {d : Nat} (c : Data d) (box : Box d)
    (E : Vec d → Nat → Vec d) : Prop :=
  (∀ x p, InBox box x → InBox box (E x p)) ∧
  ∀ x y p q, InBox box x → InBox box y →
    LE (absolute (sub (E x p) (E y q)))
      (add (mv c.matrix (absolute (sub x y)))
           (scale (dyadic p + dyadic q) c.weights))

def orbit {d : Nat} (E : Vec d → Nat → Vec d) (p : Nat) (seed : Vec d) :
    Nat → Vec d
  | 0 => seed
  | n + 1 => E (orbit E p seed n) p

def residual {d : Nat} (c : Data d) (E : Vec d → Nat → Vec d)
    (x : Vec d) (p : Nat) : Rat :=
  dist c.weights x (E x p) + dyadic p

def residualVector {d : Nat} (c : Data d) (E : Vec d → Nat → Vec d)
    (x : Vec d) (p : Nat) : Vec d :=
  add (absolute (sub x (E x p))) (scale (dyadic p) c.weights)

def outputPrecision (g k : Nat) : Nat := k + g + 1
def outputSteps {d : Nat} (c : Data d) (h k : Nat) : Nat :=
  c.reciprocalGap * (k + h + 1)
def name {d : Nat} (c : Data d) (E : Vec d → Nat → Vec d)
    (seed : Vec d) (h g k : Nat) : Vec d :=
  orbit E (outputPrecision g k) seed (outputSteps c h k)

def Regular {d : Nat} (w : Vec d) (q : Nat → Vec d) : Prop :=
  ∀ k l, dist w (q k) (q l) ≤ dyadic k + dyadic l

def powApply {d : Nat} (a : Mat d) (r : Vec d) : Nat → Vec d
  | 0 => r
  | n + 1 => mv a (powApply a r n)

def neumannPrefix {d : Nat} (a : Mat d) (r : Vec d) : Nat → Vec d
  | 0 => zero
  | n + 1 => add (neumannPrefix a r n) (powApply a r n)

def neumannCertificate {d : Nat} (c : Data d) (r : Vec d) (n : Nat) : Vec d :=
  add (neumannPrefix c.matrix r n)
    (scale ((c.reciprocalGap : Rat) * weightedNorm c.weights (powApply c.matrix r n))
      c.weights)

def automaticWeights {d : Nat} (a : Mat d) (m : Nat) : Vec d :=
  neumannPrefix a ones m

structure Schedule (d : Nat) where
  update : Nat → Fin d → Bool
  readTime : Nat → Fin d → Fin d → Nat

def history {d : Nat} (E : Vec d → Nat → Vec d) (p : Nat) (seed : Vec d)
    (schedule : Schedule d) : Nat → Array (Vec d)
  | 0 => #[seed]
  | t + 1 =>
    let h := history E p seed schedule t
    let current := (h[t]?).getD seed
    let next : Vec d := fun i =>
      if schedule.update t i then
        let mixed : Vec d := fun j => ((h[schedule.readTime t i j]?).getD seed) j
        E mixed p i
      else current i
    h.push next

def runState {d : Nat} (E : Vec d → Nat → Vec d) (p : Nat) (seed : Vec d)
    (schedule : Schedule d) (t : Nat) : Vec d :=
  ((history E p seed schedule t)[t]?).getD seed

def DelayGuard {d : Nat} (schedule : Schedule d) (delay horizon : Nat) : Prop :=
  ∀ t, t < horizon → ∀ i j,
    t - delay ≤ schedule.readTime t i j ∧ schedule.readTime t i j ≤ t

def CoverageGuard {d : Nat} (schedule : Schedule d) (window delay blocks : Nat) : Prop :=
  ∀ n, n < blocks → ∀ i, ∃ t,
    n * (window + delay) ≤ t ∧ t < n * (window + delay) + window ∧
      schedule.update t i = true

def asyncPrecision (g k : Nat) : Nat := k + g + 2
def asyncBlocks {d : Nat} (c : Data d) (h k : Nat) : Nat :=
  c.reciprocalGap * (k + h + 2)
def asyncName {d : Nat} (c : Data d) (E : Vec d → Nat → Vec d)
    (seed : Vec d) (schedule : Schedule d) (window delay h g k : Nat) : Vec d :=
  runState E (asyncPrecision g k) seed schedule
    ((window + delay) * asyncBlocks c h k)

def WeightedMaximumTarget : Prop :=
  ∀ {d} (c : Data d), 0 < d → SmallGain c →
    ∀ v r z, LE v (add (mv c.matrix v) r) →
      LE (add (mv c.matrix z) r) z → LE v z

def GeometricBlockTarget : Prop :=
  ∀ s : Nat, 1 ≤ s → (1 - 1 / (s : Rat))^s ≤ 1 / 2

def ResidualSeparationTarget : Prop :=
  ∀ {d} (c : Data d) (box : Box d) (E : Vec d → Nat → Vec d),
    0 < d → SmallGain c → ActionContract c box E →
    ∀ x y p q, InBox box x → InBox box y →
      dist c.weights x y ≤ (c.reciprocalGap : Rat) *
        (residual c E x p + residual c E y q)

def ProducerTarget : Prop :=
  ∀ {d} (c : Data d) (box : Box d) (E : Vec d → Nat → Vec d)
      (seed : Vec d) (r : Rat) (h g : Nat),
    0 < d → SmallGain c → ActionContract c box E → InBox box seed →
    Diameter c box r →
    (c.reciprocalGap : Rat) * r ≤ (2 : Rat)^h →
    (c.reciprocalGap : Rat) * (2 * (c.reciprocalGap : Rat) + 1) ≤ (2 : Rat)^g →
    (∀ k, InBox box (name c E seed h g k)) ∧
    (∀ k, (c.reciprocalGap : Rat) *
      residual c E (name c E seed h g k) (outputPrecision g k) ≤ dyadic k) ∧
    Regular c.weights (name c E seed h g)

def NeumannCertificateTarget : Prop :=
  ∀ {d} (c : Data d), SmallGain c →
    ∀ r n, LE zero r →
      LE (add (mv c.matrix (neumannCertificate c r n)) r)
         (neumannCertificate c r n)

def AutomaticWeightsTarget : Prop :=
  ∀ {d} (a : Mat d) (m s : Nat) (theta : Rat),
    0 < d → 1 ≤ m → 1 ≤ s → (∀ i j, 0 ≤ a i j) →
    0 ≤ theta → theta < 1 → LE (powApply a ones m) (scale theta ones) →
    (∀ i, automaticWeights a m i ≤ (s : Rat) * (1 - theta)) →
    SmallGain { matrix := a, weights := automaticWeights a m, reciprocalGap := s }

def PosteriorErrorTarget : Prop :=
  ∀ {d} (c : Data d) (box : Box d) (E : Vec d → Nat → Vec d)
      (q : Nat → Vec d) (p : Nat → Nat),
    0 < d → SmallGain c → ActionContract c box E →
    (∀ k, InBox box (q k)) →
    (∀ k, (c.reciprocalGap : Rat) * residual c E (q k) (p k) ≤ dyadic k) →
    ∀ x work z k, InBox box x → LE zero z →
      LE (add (mv c.matrix z) (residualVector c E x work)) z →
      LE (absolute (sub x (q k))) (add z (scale (dyadic k) c.weights))

def DelayedRunTarget : Prop :=
  ∀ {d} (c : Data d) (box : Box d) (E : Vec d → Nat → Vec d)
      (q : Nat → Vec d) (pq : Nat → Nat) (seed : Vec d)
      (r : Rat) (schedule : Schedule d) (window delay p n j : Nat),
    0 < d → SmallGain c → ActionContract c box E →
    InBox box seed → Diameter c box r →
    (∀ k, InBox box (q k)) →
    (∀ k, (c.reciprocalGap : Rat) * residual c E (q k) (pq k) ≤ dyadic k) →
    1 ≤ window → DelayGuard schedule delay (n * (window + delay)) →
    CoverageGuard schedule window delay n →
    dist c.weights (runState E p seed schedule (n * (window + delay))) (q j) ≤
      (contraction c)^n * r + (c.reciprocalGap : Rat) * dyadic p + dyadic j

def AsynchronousProducerTarget : Prop :=
  ∀ {d} (c : Data d) (box : Box d) (E : Vec d → Nat → Vec d)
      (q : Nat → Vec d) (pq : Nat → Nat) (seed : Vec d)
      (r : Rat) (schedule : Schedule d) (window delay h g : Nat),
    0 < d → SmallGain c → ActionContract c box E →
    InBox box seed → Diameter c box r →
    (∀ k, InBox box (q k)) →
    (∀ k, (c.reciprocalGap : Rat) * residual c E (q k) (pq k) ≤ dyadic k) →
    1 ≤ window → r ≤ (2 : Rat)^h → (c.reciprocalGap : Rat) ≤ (2 : Rat)^g →
    (∀ k, DelayGuard schedule delay ((window + delay) * asyncBlocks c h k)) →
    (∀ k, CoverageGuard schedule window delay (asyncBlocks c h k)) →
    Regular c.weights (asyncName c E seed schedule window delay h g) ∧
      ∀ k j, dist c.weights (asyncName c E seed schedule window delay h g k) (q j) ≤
        dyadic k / 2 + dyadic j

/-!
Object-iPRA implementation order:

1. PR integer/rational codecs, vector/matrix sequence operations, and the
   Boolean characteristic predicates for all finite inequalities.
2. Finite maximum with attaining index; rational weighted triangle and
   matrix-monotonicity lemmas; object proof of WeightedMaximumTarget's code.
3. QF induction on n for c^n*(1+n/s) <= 1; then on block count.
4. The orbit invariant: InBox x_n and
      dist x_n x_(n+1) <= c^n*R + 2*s*2^-p.
   All p, R, s, dimensions and input program parameters remain free.
5. Substitute N(k), P(k) and cut the action contracts to obtain Producer.
6. Finite matrix geometric identity and residual-vector comparison, giving
   NeumannCertificate and PosteriorError.
7. For asynchronous evaluation, encode the finite state history, read times,
   update mask and coverage certificate.  The block invariant is exactly
   SG19's old-history envelope plus the improved envelope on updated slots.

The source file contains definitions and theorem targets only.  Host-level
proofs of these propositions, if added, must be labeled separately from the
literal encoded arithmetic theorem endpoints.
-/

end CoupledIPRA
