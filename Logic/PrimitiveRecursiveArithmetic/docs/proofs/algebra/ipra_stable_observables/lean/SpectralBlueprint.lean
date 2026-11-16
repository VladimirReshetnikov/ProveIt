import Std

/-!
# Finite rational definitions and explicit spectral proof targets

This file is a host-Lean blueprint. Its data, algorithms and propositions
are compiler-checked. The propositions named `...Target` below are NOT
proved or assumed: they are definitions of the remaining obligations.
No new axiom, placeholder proof, or abstract real is introduced. The audit
records Classical.choice inherited from Std rational definitions; these
host declarations are not embedded iPRA proofs.

The companion ObjectObservation module has a different role: it proves
generic inference rules for the embedded `Prf PRAAx` relation. Reifying
these rational algorithms as PR symbols and proving the targets in that
object theory remain separate steps, specified in the report.

`frobSq` is the SQUARE of the Frobenius norm. Thus the root comparison
target deliberately squares `frobSq (S-T)` once more.
-/

namespace IPRAStableObservables.Spectral

abbrev Vec (n : Nat) := Fin n -> Rat
abbrev Mat (n : Nat) := Fin n -> Fin n -> Rat

def sq (q : Rat) : Rat := q * q
def absQ (q : Rat) : Rat := if q < 0 then -q else q

/-- An explicitly recursive finite sum, without a real completion. -/
def sumQ : (n : Nat) -> (Fin n -> Rat) -> Rat
  | 0, _ => 0
  | n + 1, f => f 0 + sumQ n (fun i => f i.succ)

def transpose {n} (A : Mat n) : Mat n := fun i j => A j i
def identity (n : Nat) : Mat n := fun i j => if i = j then 1 else 0
def add {n} (A B : Mat n) : Mat n := fun i j => A i j + B i j
def sub {n} (A B : Mat n) : Mat n := fun i j => A i j - B i j
def scale {n} (r : Rat) (A : Mat n) : Mat n := fun i j => r * A i j
def mul {n} (A B : Mat n) : Mat n :=
  fun i j => sumQ n (fun k => A i k * B k j)
def diagonal {n} (d : Vec n) : Mat n :=
  fun i j => if i = j then d i else 0
def conjugate {n} (A Q : Mat n) : Mat n := mul (mul (transpose Q) A) Q
def reconstruct {n} (Q : Mat n) (d : Vec n) : Mat n :=
  mul (mul Q (diagonal d)) (transpose Q)
def frobSq {n} (A : Mat n) : Rat :=
  sumQ n (fun i => sumQ n (fun j => sq (A i j)))
def offdiagSq {n} (A : Mat n) : Rat :=
  sumQ n (fun i => sumQ n (fun j => if i = j then 0 else sq (A i j)))
def dot {n} (v w : Vec n) : Rat := sumQ n (fun i => v i * w i)
def matVec {n} (A : Mat n) (v : Vec n) : Vec n :=
  fun i => sumQ n (fun j => A i j * v j)
def quadratic {n} (A : Mat n) (v : Vec n) : Rat := dot v (matVec A v)

def Symmetric {n} (A : Mat n) : Prop := A = transpose A
def Orthogonal {n} (Q : Mat n) : Prop :=
  mul (transpose Q) Q = identity n /\ mul Q (transpose Q) = identity n
def Sorted {n} (d : Vec n) : Prop := forall i j, i.val <= j.val -> d i <= d j
def Nonnegative {n} (d : Vec n) : Prop := forall i, 0 <= d i
def PositiveSemidefinite {n} (A : Mat n) : Prop :=
  Symmetric A /\ forall v : Vec n, 0 <= quadratic A v

/-- Certificate data have no proof fields. Validity is a separate predicate. -/
structure DiagonalData (n : Nat) where
  basis : Mat n
  values : Vec n

def DiagonalCertificate {n} (A : Mat n) (eta : Rat) (w : DiagonalData n) : Prop :=
  Symmetric A /\ 0 <= eta /\ Orthogonal w.basis /\ Sorted w.values /\
  (forall i, conjugate A w.basis i i = w.values i) /\
  frobSq (sub (conjugate A w.basis) (diagonal w.values)) <= sq eta

/-- A rational LDL / weighted Gram certificate. The factor is not required
to be orthogonal; that restriction would incorrectly exclude generic PSD
rational matrices with irrational eigenvalues. -/
structure PositiveData (n : Nat) where
  factor : Mat n
  weights : Vec n

def PositiveCertificate {n} (A : Mat n) (w : PositiveData n) : Prop :=
  Nonnegative w.weights /\ A = reconstruct w.factor w.weights

structure RootData (n : Nat) where
  root : Mat n
  positive : PositiveData n

def RootCertificate {n} (A : Mat n) (eta : Rat) (w : RootData n) : Prop :=
  0 <= eta /\ PositiveCertificate w.root w.positive /\
  frobSq (sub (mul w.root w.root) A) <= sq eta

def ProjectorCertificate {n} (A : Mat n) (eta : Rat) (P : Mat n) : Prop :=
  0 <= eta /\ Symmetric P /\ mul P P = P /\
  frobSq (sub (mul A P) (mul P A)) <= sq eta

def thresholdMask {n} (tau : Rat) (d : Vec n) : Vec n :=
  fun i => if d i < tau then 1 else 0
def thresholdProjector {n} (tau : Rat) (w : DiagonalData n) : Mat n :=
  reconstruct w.basis (thresholdMask tau w.values)
def ThresholdMargin {n} (tau gamma : Rat) (d : Vec n) : Prop :=
  forall i, gamma <= absQ (d i - tau)

def shifted {n} (A : Mat n) (tau : Rat) : Mat n :=
  sub A (scale tau (identity n))
def gapMatrix {n} (A : Mat n) (tau gap : Rat) : Mat n :=
  sub (mul (shifted A tau) (shifted A tau)) (scale (sq gap) (identity n))

/-- Totalized scalar pivot rule from the report. -/
def pivotRotation (h b : Rat) : Rat × Rat :=
  if b = 0 then (1, 0)
  else if sq b <= sq h then
    let t := b / (4 * h)
    ((1 - sq t) / (1 + sq t), 2 * t / (1 + sq t))
  else
    let c : Rat := 3 / 5
    let s : Rat := 4 / 5
    let plus := (sq c - sq s) * b - c * s * h
    let minus := (sq c - sq s) * b + c * s * h
    if sq minus < sq plus then (c, -s) else (c, s)

def pivotValue (h b c s : Rat) : Rat := (sq c - sq s) * b - c * s * h

def planeRotation {n} (i j : Fin n) (c s : Rat) : Mat n := fun r t =>
  if r = i then (if t = i then c else if t = j then -s else 0)
  else if r = j then (if t = i then s else if t = j then c else 0)
  else if r = t then 1 else 0

def pivotPairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).filterMap fun j => if i.val < j.val then some (i, j) else none

/-- Finite first-maximum scan; dimensions zero and one return none. -/
def choosePivot {n} (A : Mat n) : Option (Fin n × Fin n) :=
  (pivotPairs n).foldl (fun best pair =>
    match best with
    | none => some pair
    | some old =>
      if sq (A old.1 old.2) < sq (A pair.1 pair.2) then some pair else best) none

structure JacobiState (n : Nat) where
  current : Mat n
  basis : Mat n

def jacobiStep {n} (eta : Rat) (w : JacobiState n) : JacobiState n :=
  if offdiagSq w.current <= sq eta then w
  else match choosePivot w.current with
  | none => w
  | some (i, j) =>
    let b := w.current i j
    let h := w.current i i - w.current j j
    let cs := pivotRotation h b
    let G := planeRotation i j cs.1 cs.2
    { current := conjugate w.current G, basis := mul w.basis G }

def jacobiRun {n} (A : Mat n) (eta : Rat) : Nat -> JacobiState n
  | 0 => { current := A, basis := identity n }
  | t + 1 => jacobiStep eta (jacobiRun A eta t)

def ceilNat (q : Rat) : Nat := q.ceil.toNat
def jacobiFuel {n} (A : Mat n) (eta : Rat) : Nat :=
  n * (n - 1) * (ceilNat (frobSq A / sq eta) + 1)

def diagonalOrder {n} (A : Mat n) : List (Fin n) :=
  (List.finRange n).mergeSort fun i j =>
    if A i i = A j j then decide (i.val <= j.val) else decide (A i i < A j j)

/-- Total definition: the fallback i is unused once the sorting-length
lemma is proved. It also avoids inventing an inhabitant of Fin 0. -/
def sortedData {n} (w : JacobiState n) : DiagonalData n :=
  let order := diagonalOrder w.current
  let index := fun i : Fin n => order.getD i.val i
  { basis := fun i j => w.basis i (index j)
    values := fun i => w.current (index i) (index i) }

def diagonalize {n} (A : Mat n) (eta : Rat) : DiagonalData n :=
  sortedData (jacobiRun A eta (jacobiFuel A eta))

/-! ## Explicit unproved targets

Every declaration below is a definition of a proposition. Merely checking
its type does not establish that proposition. No instance of the final
obligations structure is supplied.
-/

def PivotImprovementTarget : Prop := forall h b : Rat, b ≠ 0 ->
  let cs := pivotRotation h b
  sq cs.1 + sq cs.2 = 1 /\ 2 * sq (pivotValue h b cs.1 cs.2) <= sq b

def EnergyIdentityTarget : Prop := forall (n : Nat) (A : Mat n), Symmetric A ->
  forall (i j : Fin n), i.val < j.val -> forall c s : Rat, sq c + sq s = 1 ->
  offdiagSq (conjugate A (planeRotation i j c s)) =
    offdiagSq A - 2 * sq (A i j) +
      2 * sq (pivotValue (A i i - A j j) (A i j) c s)

def DiagonalizationFuelTarget : Prop := forall (n : Nat) (A : Mat n) (eta : Rat),
  Symmetric A -> 0 < eta -> DiagonalCertificate A eta (diagonalize A eta)

def SpectralComparisonTarget : Prop :=
  forall (n : Nat) (A B : Mat n) (alpha beta delta : Rat)
    (u v : DiagonalData n),
    DiagonalCertificate A alpha u -> DiagonalCertificate B beta v ->
    0 <= delta -> frobSq (sub A B) <= sq delta ->
    forall i, sq (u.values i - v.values i) <= sq (delta + alpha + beta)

def PositiveSoundnessTarget : Prop := forall (n : Nat) (A : Mat n) (w : PositiveData n),
  PositiveCertificate A w -> PositiveSemidefinite A

def PositiveCompletenessTarget : Prop := forall (n : Nat) (A : Mat n),
  PositiveSemidefinite A -> Exists (PositiveCertificate A)

/-- A correctness target for a supplied rational LDL producer. Separate
PR reification and its code-bound proof are required for object-iPRA. -/
def PositiveProducerTarget (produce : {n : Nat} -> Mat n -> PositiveData n) : Prop :=
  forall (n : Nat) (A : Mat n), PositiveSemidefinite A ->
    PositiveCertificate A (produce A)

def RootProducerTarget
    (produce : {n : Nat} -> Mat n -> Rat -> RootData n) : Prop :=
  forall (n : Nat) (A : Mat n) (eta : Rat), PositiveSemidefinite A -> 0 < eta ->
    RootCertificate A eta (produce A eta)

def SquareRootMixedBasisTarget : Prop :=
  forall (n : Nat) (Q R : Mat n) (s t : Vec n),
    Orthogonal Q -> Orthogonal R -> Nonnegative s -> Nonnegative t ->
    let S := reconstruct Q s
    let T := reconstruct R t
    sq (frobSq (sub S T)) <=
      (n : Rat) * frobSq (sub (mul S S) (mul T T))

def ThresholdProjectorValidityTarget : Prop :=
  forall (n : Nat) (A : Mat n) (eta tau : Rat) (w : DiagonalData n),
    DiagonalCertificate A eta w ->
      ProjectorCertificate A eta (thresholdProjector tau w)

/-- Core finite separation inequality. Labels can be arbitrary zero-one
vectors; disagreement must be accompanied by a supplied spectral gap. -/
def SeparatedProjectorsTarget : Prop :=
  forall (n : Nat) (Q R : Mat n) (d e p q : Vec n) (gap : Rat),
    Orthogonal Q -> Orthogonal R -> 0 < gap ->
    (forall i, p i = 0 \/ p i = 1) ->
    (forall j, q j = 0 \/ q j = 1) ->
    (forall i j, p i ≠ q j -> gap <= absQ (d i - e j)) ->
    sq gap * frobSq (sub (reconstruct Q p) (reconstruct R q)) <=
      frobSq (sub (reconstruct Q d) (reconstruct R e))

def ThresholdProjectorComparisonTarget : Prop :=
  forall (n : Nat) (A B : Mat n) (alpha beta delta tau gamma : Rat)
    (u v : DiagonalData n),
    DiagonalCertificate A alpha u -> DiagonalCertificate B beta v ->
    0 <= delta -> frobSq (sub A B) <= sq delta -> 0 < gamma ->
    ThresholdMargin tau gamma u.values -> ThresholdMargin tau gamma v.values ->
    sq (2 * gamma) *
      frobSq (sub (thresholdProjector tau u) (thresholdProjector tau v)) <=
      sq (delta + alpha + beta)

def PositiveGapToMarginTarget : Prop :=
  forall (n : Nat) (A : Mat n) (eta tau gap : Rat)
    (w : DiagonalData n) (pos : PositiveData n),
    DiagonalCertificate A eta w -> 0 < gap -> 2 * eta <= gap ->
    PositiveCertificate (gapMatrix A tau gap) pos ->
    ThresholdMargin tau (gap - eta) w.values

/-- Named completion obligations, with no supplied instance. -/
structure UnprovedMatrixObligations : Prop where
  pivot : PivotImprovementTarget
  energy : EnergyIdentityTarget
  fuel : DiagonalizationFuelTarget
  comparison : SpectralComparisonTarget
  positivity : PositiveSoundnessTarget
  positiveCompleteness : PositiveCompletenessTarget
  squareRootMixedBasis : SquareRootMixedBasisTarget
  projectorValidity : ThresholdProjectorValidityTarget
  separatedProjectors : SeparatedProjectorsTarget
  thresholdComparison : ThresholdProjectorComparisonTarget
  gapToMargin : PositiveGapToMarginTarget

end IPRAStableObservables.Spectral
