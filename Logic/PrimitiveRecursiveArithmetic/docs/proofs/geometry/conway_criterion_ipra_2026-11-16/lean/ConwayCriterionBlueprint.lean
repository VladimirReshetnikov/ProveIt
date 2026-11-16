import IPRADerivations.Core.LinearAlgebra
import IPRADerivations.Core.Pairing
import IPRADerivations.Core.Search
import IPRADerivations.Core.MultiSums

/-!
# Conway criterion: host-level blueprint

This file is a source-level formalization outline.  It deliberately contains no
`axiom`, `sorry`, or `admit`.  The executable definitions below isolate the
finite data and the affine identities.  The final object-iPRA theorems are
recorded as commented target signatures; completing them requires the finite
torus-refinement development described in `FORMALIZATION_PLAN.md`.

The intended final theorem is an actual empty-context derivation

    ([] : List (Fm PTm 0)) ⊢[PRAAx] conwayCriterionFormula

inside the checked `IPRADerivations` library, followed by transfer through
`pra_iff_native`.
-/

namespace LeanProofs.IPRA.Conway

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm

structure IPoint where
  x : Int
  y : Int
  deriving DecidableEq, Repr

namespace IPoint

def zero : IPoint := ⟨0, 0⟩
def add (p q : IPoint) : IPoint := ⟨p.x + q.x, p.y + q.y⟩
def neg (p : IPoint) : IPoint := ⟨-p.x, -p.y⟩
def sub (p q : IPoint) : IPoint := ⟨p.x - q.x, p.y - q.y⟩
def smul (n : Int) (p : IPoint) : IPoint := ⟨n * p.x, n * p.y⟩
def det (p q : IPoint) : Int := p.x * q.y - p.y * q.x

def translate (w p : IPoint) : IPoint := add p w

/-- `halfTurn s p = s-p`; `s` is the doubled center. -/
def halfTurn (s p : IPoint) : IPoint := sub s p

@[simp] theorem halfTurn_involutive (s p : IPoint) :
    halfTurn s (halfTurn s p) = p := by
  cases s; cases p; simp [halfTurn, sub]

/-- Composition of half-turns is translation by the difference of doubled centers. -/
theorem halfTurn_comp (r s p : IPoint) :
    halfTurn r (halfTurn s p) = translate (sub r s) p := by
  cases r; cases s; cases p; simp [halfTurn, translate, add, sub]

@[simp] theorem det_self (p : IPoint) : det p p = 0 := by
  simp [det]

end IPoint

abbrev PLPath := List IPoint

def translatePath (w : IPoint) (p : PLPath) : PLPath := p.map (IPoint.translate w)
def halfTurnPath (s : IPoint) (p : PLPath) : PLPath := p.map (IPoint.halfTurn s)
def reversePath (p : PLPath) : PLPath := p.reverse

@[simp] theorem translatePath_reverse (w : IPoint) (p : PLPath) :
    translatePath w (reversePath p) = reversePath (translatePath w p) := by
  simp [translatePath, reversePath]

@[simp] theorem halfTurnPath_reverse (s : IPoint) (p : PLPath) :
    halfTurnPath s (reversePath p) = reversePath (halfTurnPath s p) := by
  simp [halfTurnPath, reversePath]

/-- Open-path shoelace functional `Σ det(pᵢ,pᵢ₊₁)`. -/
def pathJ : PLPath → Int
  | p :: q :: r => IPoint.det p q + pathJ (q :: r)
  | _ => 0

/-- Six oriented boundary paths in counterclockwise order.  Empty geometric arcs
are represented by singleton lists. -/
structure Datum where
  a : PLPath
  b : PLPath
  c : PLPath
  d : PLPath
  e : PLPath
  f : PLPath
  deriving Repr

/-- Total last element with an explicit default; the checker separately requires
nonempty paths. -/
def lastD : List α → α → α
  | [], z => z
  | x :: xs, z => xs.foldl (fun _ y => y) x

namespace Datum

def A (d : Datum) : IPoint := d.a.headD IPoint.zero
def B (d : Datum) : IPoint := lastD d.a IPoint.zero
def C (d : Datum) : IPoint := lastD d.b IPoint.zero
def D (d : Datum) : IPoint := lastD d.c IPoint.zero
def E (d : Datum) : IPoint := lastD d.d IPoint.zero
def F (d : Datum) : IPoint := lastD d.e IPoint.zero

/-- First period, forced by the translated pair `a,d`. -/
def periodT (d : Datum) : IPoint := IPoint.sub d.E d.A

/-- Second period, written without division by two. -/
def periodU (d : Datum) : IPoint :=
  IPoint.sub (IPoint.add d.E d.F) (IPoint.add d.B d.C)

/-- Doubled center of path `e`. -/
def eCenter2 (d : Datum) : IPoint := IPoint.add d.E d.F

/-- The two orbit representatives in the explicit Conway construction. -/
inductive OrbitKind
  | direct
  | turned
  deriving DecidableEq, Repr

def placePoint (d : Datum) (kind : OrbitKind) (m n : Int) (p : IPoint) : IPoint :=
  let shift := IPoint.add (IPoint.smul m d.periodT) (IPoint.smul n d.periodU)
  match kind with
  | .direct => IPoint.translate shift p
  | .turned => IPoint.translate shift (IPoint.halfTurn d.eCenter2 p)

end Datum

/-!
## Completion targets

The following declarations are specifications, not active Lean constants.
They are comments so that this blueprint does not smuggle unproved mathematics
through an opaque constant or a new axiom.

Host-level semantic layer:

```
structure DiskCert (d : Datum) where
  triangulation : List (IPoint × IPoint × IPoint)
  boundary_ok : ...
  incidence_ok : ...
  positive_orientation : ...

structure TorusCert (d : Datum) where
  pieces : List RationalConvexPolygon
  inside_unit_cell : ...
  pairwise_zero_area_intersection : ...
  total_area_one : ...

theorem period_area_identity
    (hd : DiskCert d) (hc : ConwayLocal d) :
    IPoint.det d.periodT d.periodU = twiceArea hd := ...

theorem buildTorus_correct
    (hd : DiskCert d) (hc : ConwayLocal d) :
    TorusCert d := ...

theorem orbit_tiles_plane
    (hd : DiskCert d) (hc : ConwayLocal d) :
    PeriodicTiling d.periodT d.periodU
      (fun m n => place d .direct m n)
      (fun m n => place d .turned m n) := ...
```

Object-iPRA endpoint:

```
def conwayCriterionFormula : Fm PTm 0 :=
  univ 2 (premiseCode 0 1 ➝
    detAreaCode 0 1 ⋏ torusCertificateCode 0 (buildTorusCode 0 1))

theorem conwayCriterion :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] conwayCriterionFormula := by
  ...

theorem conwayCriterionNative : NativeProvable (unPRA conwayCriterionFormula) :=
  (pra_iff_native _).mp conwayCriterion
```

Here every displayed `...Code` is a primitive-recursive symbol whose defining
equations are generated with the existing `toPR`/recursion infrastructure.
See `FORMALIZATION_PLAN.md` for the dependency order and proof obligations.
-/

end LeanProofs.IPRA.Conway
