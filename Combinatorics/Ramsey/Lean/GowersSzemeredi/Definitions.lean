import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Combinatorics.Additive.FreimanHom
import Mathlib.Data.Finset.Pi
import Mathlib.Data.ZMod.ValMinAbs

/-!
# Definitions for Gowers's proof of Szemeredi's theorem

This file formalizes the auxiliary language used in W. T. Gowers,
"A new proof of Szemeredi's theorem", *GAFA* 11 (2001), 465--588.

The paper works in `ZMod N` (with `N` normally prime), uses the unnormalized
discrete Fourier transform, and regards subsets as their indicator functions.
Finite subsets are represented by `Finset`; partial functions in the paper are
represented by a total function together with the `Finset` on which it is used.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## General finite-combinatorial helpers -/

/-- The number of elements of a finite type satisfying a predicate. -/
noncomputable def countWhere {X : Type*} [Fintype X] (p : X -> Prop) : Nat := by
  classical
  exact (Finset.univ.filter p).card

/-- The paper's convention for comparing a finite cardinality with a real bound. -/
def cardAtLeast {X : Type*} (A : Finset X) (x : Real) : Prop :=
  x <= A.card

/-- The paper's convention for comparing a finite cardinality with a real upper bound. -/
def cardAtMost {X : Type*} (A : Finset X) (x : Real) : Prop :=
  (A.card : Real) <= x

/-- A finite indexed family is a partition of `S`. -/
def IsPartition {X : Type*} [DecidableEq X] {m : Nat}
    (P : Fin m -> Finset X) (S : Finset X) : Prop :=
  (forall x, x ∈ S <-> exists i, x ∈ P i) /\
    forall i j, i != j -> Disjoint (P i) (P j)

/-- `Q` refines `P`: it has the same union and every `Q`-cell lies in a `P`-cell. -/
def IsRefinement {X : Type*} [DecidableEq X] {m n : Nat}
    (Q : Fin n -> Finset X) (P : Fin m -> Finset X) : Prop :=
  (forall x, (exists j, x ∈ Q j) <-> exists i, x ∈ P i) /\
    (forall j, exists i, Q j ⊆ P i) /\
    (forall i j, i != j -> Disjoint (Q i) (Q j))

/-- Average cell size, measured in `Real`. -/
def averageCellSize {X : Type*} {m : Nat} (P : Fin m -> Finset X) : Real :=
  (∑ i, (P i).card : Nat) / (m : Real)

/-! ## Arithmetic progressions -/

/-- A finite arithmetic progression in the natural numbers. -/
structure NatAP where
  start : Nat
  step : Nat
  length : Nat

/-- The finite set underlying a natural-number arithmetic progression. -/
noncomputable def NatAP.carrier (P : NatAP) : Finset Nat := by
  classical
  exact Finset.univ.image (fun i : Fin P.length => P.start + (i : Nat) * P.step)

/-- A genuine natural-number progression has positive common difference. -/
def NatAP.IsProper (P : NatAP) : Prop :=
  0 < P.step /\ P.carrier.card = P.length

/-- A family of natural-number progressions partitions a finite set. -/
def IsNatAPPartition {m : Nat} (P : Fin m -> NatAP) (S : Finset Nat) : Prop :=
  IsPartition (fun i => (P i).carrier) S

/-- A (possibly wrapping) arithmetic progression in `ZMod N`. -/
structure ModAP (N : Nat) where
  start : ZMod N
  step : ZMod N
  length : Nat

/-- The finite set underlying a modular arithmetic progression. -/
noncomputable def ModAP.carrier {N : Nat} (P : ModAP N) : Finset (ZMod N) := by
  classical
  exact Finset.univ.image (fun i : Fin P.length => P.start + (i : Nat) * P.step)

/-- A modular progression is proper when it does not wrap or repeat. -/
def ModAP.IsProper {N : Nat} (P : ModAP N) : Prop :=
  P.carrier.card = P.length

/-- A modular interval beginning at `a`, of the given length. -/
def modInterval (N : Nat) (a : ZMod N) (length : Nat) : ModAP N :=
  { start := a, step := 1, length := length }

/-- The diameter convention from the paragraph before Lemma 2.3. -/
def diameterAtMost {N : Nat} (A : Finset (ZMod N)) (s : Nat) : Prop :=
  exists a : ZMod N, A ⊆ (modInterval N a (s + 1)).carrier

/-- A subset of the positive integers contains a nonconstant progression of length `k`. -/
def HasNatAP (A : Finset Nat) (k : Nat) : Prop :=
  exists a d : Nat, 0 < d /\ ∀ i, i < k → a + i * d ∈ A

/-- A subset of `ZMod N` contains a nonconstant modular progression of length `k`. -/
def HasModAP {N : Nat} (A : Finset (ZMod N)) (k : Nat) : Prop :=
  exists a d : ZMod N, d != 0 /\ ∀ i, i < k → a + (i : Nat) * d ∈ A

/-- An arithmetic progression is monochromatic for a coloring of the positive integers. -/
def HasMonochromaticAP (M r : Nat) (color : Nat -> Fin r) (k : Nat) : Prop :=
  exists a d : Nat, exists c : Fin r, 0 < d /\
    ∀ i, i < k → a + i * d ∈ Finset.Icc 1 M /\ color (a + i * d) = c

/-! ## Fourier analysis and uniformity -/

/-- A complex-valued function takes values in the closed unit disc `D`. -/
def DiscValued {X : Type*} (f : X -> Complex) : Prop :=
  forall x, ‖f x‖ <= 1

/-- The indicator function of a finite subset of `ZMod N`. -/
def indicator {N : Nat} (A : Finset (ZMod N)) : ZMod N -> Complex :=
  fun x => if x ∈ A then 1 else 0

/-- The density `|A| / N`. -/
def density {N : Nat} (A : Finset (ZMod N)) : Real :=
  A.card / (N : Real)

/-- The balanced function `1_A - |A|/N`. -/
def balanced {N : Nat} (A : Finset (ZMod N)) : ZMod N -> Complex :=
  fun x => indicator A x - density A

/-- Gowers's unnormalized discrete Fourier transform. -/
def fourier {N : Nat} [NeZero N] (f : ZMod N -> Complex) : ZMod N -> Complex :=
  ZMod.dft f

/-- The standard exponential character `x |-> exp(2*pi*i*x/N)`. -/
def exponential {N : Nat} [NeZero N] (x : ZMod N) : Complex :=
  ZMod.stdAddChar x

/-- Gowers's nonstandard correlation/convolution `f * g`. -/
def correlation {N : Nat} [NeZero N]
    (f g : ZMod N -> Complex) (s : ZMod N) : Complex :=
  ∑ t : ZMod N, f t * star (g (t - s))

/-- The first difference `Delta(f; a)(s) = f(s) * conj (f(s-a))`. -/
def difference {N : Nat} (f : ZMod N -> Complex) (a s : ZMod N) : Complex :=
  f s * star (f (s - a))

/-- Iterated difference, in the order used by the inductive definition in Section 3. -/
def iteratedDifference {N : Nat} (f : ZMod N -> Complex) :
    List (ZMod N) -> ZMod N -> Complex
  | [], s => f s
  | a :: as, s => difference (iteratedDifference f as) a s

/-- A `d`-tuple of elements of `ZMod N`. -/
abbrev Point (N d : Nat) := Fin d -> ZMod N

/-- Iterated difference with a fixed number of difference variables. -/
def cubeDifference {N d : Nat} (f : ZMod N -> Complex) (a : Point N d) :
    ZMod N -> Complex :=
  iteratedDifference f (List.ofFn a)

/-- `alpha`-uniformity of degree `d` (including the paper's degree-zero convention). -/
def UniformOfDegree {N : Nat} [NeZero N]
    (f : ZMod N -> Complex) (alpha : Real) (d : Nat) : Prop :=
  ∑ a : Point N d, ‖∑ s : ZMod N, cubeDifference f a s‖ ^ 2 <=
    alpha * (N : Real) ^ (d + 2)

/-- Uniformity for a set means uniformity of its balanced function. -/
def UniformSetOfDegree {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (alpha : Real) (d : Nat) : Prop :=
  UniformOfDegree (balanced A) alpha d

/-- The Gowers norm appearing in Lemma 3.9. -/
def gowersNorm {N : Nat} [NeZero N] (d : Nat) (f : ZMod N -> Complex) : Real :=
  ‖∑ a : Point N d, ∑ s : ZMod N, cubeDifference f a s‖ ^
    ((1 : Real) / (2 : Real) ^ d)

/-- The Hamming weight of a Boolean cube vertex. -/
def boolWeight {d : Nat} (e : Fin d -> Bool) : Nat :=
  countWhere fun i => e i = true

/-- Apply complex conjugation according to the parity of a cube vertex. -/
def parityConj {d : Nat} (e : Fin d -> Bool) (z : Complex) : Complex :=
  if Even (boolWeight e) then z else star z

/-- The affine argument `s - e dot x` at a Boolean cube vertex. -/
def cubeArgument {N d : Nat} (s : ZMod N) (x : Point N d)
    (e : Fin d -> Bool) : ZMod N :=
  s - ∑ i, if e i then x i else 0

/-- The multilinear cube form used in Lemma 3.8. -/
def cubeForm {N d : Nat} [NeZero N]
    (f : (Fin d -> Bool) -> ZMod N -> Complex) : Complex :=
  ∑ x : Point N d, ∑ s : ZMod N,
    ∏ e : Fin d -> Bool, parityConj e (f e (cubeArgument s x e))

/-- A `d`-dimensional additive cube is parameterized by its base and sidelengths. -/
structure AdditiveCube (N d : Nat) where
  base : ZMod N
  side : Point N d

/-- A vertex of an additive cube. -/
def AdditiveCube.vertex {N d : Nat} (C : AdditiveCube N d) (e : Fin d -> Bool) : ZMod N :=
  C.base + ∑ i, if e i then C.side i else 0

/-- All vertices of a cube lie in `A`. -/
def AdditiveCube.IsIn {N d : Nat} (C : AdditiveCube N d) (A : Finset (ZMod N)) : Prop :=
  forall e, C.vertex e ∈ A

/-- The number of `d`-dimensional cubes contained in `A`. -/
noncomputable def cubeCount {N d : Nat} [NeZero N] (A : Finset (ZMod N)) : Nat :=
  countWhere fun p : ZMod N × Point N d =>
    ({ base := p.1, side := p.2 } : AdditiveCube N d).IsIn A

/-! ## Polynomials, multilinear maps, boxes, and Bohr neighborhoods -/

/-- A function agrees with a polynomial of degree at most `k` on `A`. -/
def PolynomialOn {N : Nat} (k : Nat) (A : Finset (ZMod N))
    (f : ZMod N -> ZMod N) : Prop :=
  exists c : Fin (k + 1) -> ZMod N,
    ∀ x, x ∈ A → f x = ∑ i, c i * x ^ (i : Nat)

/-- A function is affine-linear on `A`. -/
def LinearOn {N : Nat} (A : Finset (ZMod N)) (f : ZMod N -> ZMod N) : Prop :=
  exists a b : ZMod N, ∀ x, x ∈ A → f x = a * x + b

/-- A multilinear polynomial in `k` variables, including its constant term. -/
def IsMultilinear {N k : Nat} (mu : Point N k -> ZMod N) : Prop :=
  exists c : (Fin k -> Bool) -> ZMod N, ∀ x,
    mu x = ∑ e, c e * ∏ i, if e i then x i else 1

/-- A function agrees with a multilinear polynomial on a specified domain. -/
def MultilinearOn {N k : Nat} (A : Finset (Point N k))
    (f : Point N k -> ZMod N) : Prop :=
  exists mu : Point N k -> ZMod N, IsMultilinear mu /\ ∀ x, x ∈ A → f x = mu x

/-- A box is a product of modular arithmetic progressions with common difference. -/
structure Box (N k : Nat) where
  axis : Fin k -> ModAP N
  commonDiff : ZMod N
  axis_step : ∀ i, (axis i).step = commonDiff

/-- The set of points in a box. -/
noncomputable def Box.carrier {N k : Nat} [NeZero N]
    (P : Box N k) : Finset (Point N k) := by
  classical
  exact Finset.univ.filter (fun x => ∀ i, x i ∈ (P.axis i).carrier)

/-- The width of a box is the least axis length (zero in dimension zero). -/
noncomputable def Box.width {N k : Nat} (P : Box N k) : Nat := by
  classical
  exact if h : k = 0 then 0
    else by
      let i : Fin k := ⟨0, Nat.pos_of_ne_zero h⟩
      have hu : (Finset.univ : Finset (Fin k)).Nonempty := ⟨i, Finset.mem_univ i⟩
      exact (Finset.univ.image fun j : Fin k => (P.axis j).length).min'
        (hu.image fun j : Fin k => (P.axis j).length)

/-- A family of boxes partitions a box. -/
def IsBoxPartition {N k m : Nat} [NeZero N]
    (Q : Fin m -> Box N k) (P : Box N k) : Prop :=
  IsPartition (fun i => (Q i).carrier) P.carrier

/-- The diameter of the image of a finite set under a modular map. -/
def imageDiameterAtMost {N X : Nat} (A : Finset (Fin X -> ZMod N))
    (f : (Fin X -> ZMod N) -> ZMod N) (s : Nat) : Prop :=
  diameterAtMost (A.image f) s

/-- The centered absolute value `|x|` used throughout Sections 5--16. -/
def centeredAbs {N : Nat} (x : ZMod N) : Nat :=
  x.valMinAbs.natAbs

/-- The Bohr neighborhood `B(K, delta)`. -/
noncomputable def bohr {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (delta : Real) : Finset (ZMod N) := by
  classical
  exact Finset.univ.filter fun d =>
    ∀ r, r ∈ K → (centeredAbs (r * d) : Real) <= delta * N

/-! ## Additive quadruples and Freiman homomorphisms -/

/-- An ordered additive quadruple `(a,b,c,d)` has `a+b=c+d`. -/
def IsAdditiveQuadruple {G : Type*} [Add G] (q : Fin 4 -> G) : Prop :=
  q 0 + q 1 = q 2 + q 3

/-- A quadruple is in `A` and is additive both before and after applying `phi`. -/
def IsPhiAdditive {G H : Type*} [Add G] [Add H]
    (A : Finset G) (phi : G -> H) (q : Fin 4 -> G) : Prop :=
  (∀ i, q i ∈ A) /\ IsAdditiveQuadruple q /\
    phi (q 0) + phi (q 1) = phi (q 2) + phi (q 3)

/-- The number of `phi`-additive quadruples in `A`. -/
noncomputable def phiAdditiveCount {G H : Type*} [Fintype G]
    [Add G] [Add H] (A : Finset G) (phi : G -> H) : Nat :=
  countWhere (IsPhiAdditive A phi)

/-- Section 6's notion of a `gamma`-additive partial function. -/
def GammaAdditive {N : Nat} [NeZero N] (A : Finset (ZMod N))
    (phi : ZMod N -> ZMod N) (gamma : Real) : Prop :=
  gamma * (N : Real) ^ 3 <= phiAdditiveCount A phi

/-- A Freiman homomorphism of order `k`, using Mathlib's standard definition. -/
def FreimanHom {G H : Type*} [AddCommMonoid G] [AddCommMonoid H]
    (k : Nat) (A : Finset G) (phi : G -> H) : Prop :=
  IsAddFreimanHom k (A : Set G) Set.univ phi

/-- A `2k`-tuple has equal sums in its first and second halves. -/
def IsAdditiveTuple {G : Type*} [AddCommMonoid G] {k : Nat}
    (x : Fin (2 * k) -> G) : Prop :=
  (Finset.univ.filter (fun i : Fin (2 * k) => (i : Nat) < k)).sum x =
    (Finset.univ.filter (fun i : Fin (2 * k) => k <= (i : Nat))).sum x

/-- The number of additive `2k`-tuples in a finite set. -/
noncomputable def additiveTupleCount {G : Type*} [Fintype G] [AddCommMonoid G]
    (k : Nat) (A : Finset G) : Nat :=
  countWhere fun x : Fin (2 * k) -> G => (∀ i, x i ∈ A) /\ IsAdditiveTuple x

/-- The number of additive `2k`-tuples whose image under `phi` is also additive. -/
noncomputable def phiAdditiveTupleCount {G H : Type*} [Fintype G]
    [AddCommMonoid G] [AddCommMonoid H] (k : Nat) (A : Finset G) (phi : G -> H) : Nat :=
  countWhere fun x : Fin (2 * k) -> G =>
    (∀ i, x i ∈ A) /\ IsAdditiveTuple x /\ IsAdditiveTuple (fun i => phi (x i))

/-- Section 9's `gamma`-homomorphism of order `k`, expressed without division
so that the empty-domain case is unambiguous. -/
def GammaHomOfOrder {G H : Type*} [Fintype G] [AddCommMonoid G] [AddCommMonoid H]
    (k : Nat) (A : Finset G) (phi : G -> H) (gamma : Real) : Prop :=
  gamma * additiveTupleCount k A <= phiAdditiveTupleCount k A phi

/-- A homomorphism on a structured difference set, as defined before Corollary 7.10. -/
def IsBHomomorphism {N : Nat} (A B : Finset (ZMod N))
    (phi : ZMod N -> ZMod N) : Prop :=
  exists psi : ZMod N -> ZMod N,
    FreimanHom 2 B psi /\
      ∀ x, x ∈ A → ∀ y, y ∈ A →
        x - y ∈ B → phi x - phi y = psi (x - y)

/-! ## Generalized arithmetic progressions -/

/-- A finite generalized arithmetic progression in an additive group. -/
structure GeneralizedAP (G : Type*) [AddCommMonoid G] where
  dimension : Nat
  base : G
  step : Fin dimension -> G
  length : Fin dimension -> Nat

/-- The formal size (product of side lengths) of a generalized progression. -/
def GeneralizedAP.size {G : Type*} [AddCommMonoid G] (P : GeneralizedAP G) : Nat :=
  ∏ i, P.length i

/-- The carrier of a generalized arithmetic progression. -/
noncomputable def GeneralizedAP.carrier {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (P : GeneralizedAP G) : Finset G := by
  classical
  let I := (i : Fin P.dimension) -> Fin (P.length i)
  exact Finset.univ.image fun a : I => P.base + ∑ i, (a i : Nat) • P.step i

/-- A generalized progression is proper when all coefficient representations are unique. -/
def GeneralizedAP.IsProper {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (P : GeneralizedAP G) : Prop :=
  P.carrier.card = P.size

end LeanProofs.GowersSzemeredi
