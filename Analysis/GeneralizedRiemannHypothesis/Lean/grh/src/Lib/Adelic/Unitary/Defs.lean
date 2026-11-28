import Lib.Adelic.Adeles.AdditiveCharacter
import Lib.Adelic.Hecke.Basic
import Lib.General.Topology

/-!
# Adelic unitary groups over a CM field: levels, hermitian spaces, lattices and mass

This file defines unitary groups over the adeles of a CM field `E`, with signs `s` at the infinite
places. `New.Gf` is the finite adelic unitary group of the identity form, `New.stdLevel` is its
integral subgroup K_0, and `New.G` is the product G_∞ × G_f. A level is an open subgroup of K_0.
Given a CM type of `E` (`CMType E`, which fixes a complex embedding at each infinite place), a
hermitian space with a point is a form J over E together with an adelic matrix x such that xᴴJx is
diag(s) at the infinite places and 1 at the finite ones; it yields a rational subgroup and a
lattice. The mass is defined for the standard space, where J = 1 and x = 1.

Notions from earlier files:
* `𝔸 E`, `𝔸f E`: the adeles of `E` and its finite adeles; `Ô E`: the integral finite adeles;
  `toAdele : E →+* 𝔸 E` is the embedding of E in its adeles.
* `LocField w`, `LocInt w`: the completion E_w at a finite place w and its ring of integers;
  `evalAt w` takes a finite adele to its component at w.
* `U J`: the group of invertible matrices g with gᴴJg = J.
* `intGL n O`: the matrices in GL_n(R) that, with their inverses, have entries in the subring O;
  `congruenceGL M e`: those of them whose rows e(i) are congruent to rows of 1 modulo M.
* `star w`: the complex conjugate of a finite place w; w is split (`IsSplit`) if `star w ≠ w`.
  `star` on finite adeles is complex conjugation, and `conjLoc h : E_u →+* E_w` is the map it
  induces when `star u = w`.

## Main definitions and results

* `New.Gf`: the finite adelic unitary group G_f.
* `New.G`: the adelic unitary group G = G_∞ × G_f.
* `New.mass`: the mass of the genus of O_E^l.

## Relation to the literature

Known; see `Lib.Adelic.Unitary.WeakApproximation` and `Lib.Adelic.Witt.IwasawaDecomposition` for
sources.
-/

noncomputable section

section SpaceDefs

open NumberField MeasureTheory Measure Matrix GeneralLinearGroup WithZero Filter Valued

namespace New

section Components

variable {E : Type*} [Field E] [NumberField E] {n : Type*} [Fintype n] [DecidableEq n]
  (w : FinPlace E)

/-! ### Adelic matrices and their local components -/

/-- Two matrices over the finite adeles are equal if they have the same component at every finite
place. -/
lemma matrix_ext_evalAt {m n : Type*} {M N : Matrix m n (𝔸f E)}
    (h : ∀ u : FinPlace E, M.map (evalAt u) = N.map (evalAt u)) : M = N :=
  Matrix.ext fun i j ↦
    DFunLike.ext _ _ fun u ↦ by simpa [evalAt_apply] using congr_fun₂ (h u) i j

/-- The ring homomorphism 𝔸 → ℂ taking an adele of E to its component at the infinite place v;
in `𝔸 E` every infinite component is a complex number. -/
@[simps!]
def evalInf (v : InfinitePlace E) : 𝔸 E →+* ℂ := (Pi.evalRingHom _ v).comp (RingHom.fst ..)

/-- Two matrices over the adeles are equal if they have the same component at every infinite place
and the same finite part. -/
lemma matrix_ext_𝔸 {m n : Type*} {M N : Matrix m n (𝔸 E)}
    (h_inf : ∀ v : InfinitePlace E, M.map (evalInf v) = N.map (evalInf v))
    (h_fin : M.map (RingHom.snd (InfinitePlace E → ℂ) (𝔸f E)) =
      N.map (RingHom.snd (InfinitePlace E → ℂ) (𝔸f E))) : M = N :=
  Matrix.ext fun i j ↦
    Prod.ext (funext fun v ↦ congr_fun₂ (h_inf v) i j) (congr_fun₂ h_fin i j)

/-- The homomorphism sending g in GL_n(E_w) to the element of GL_n(𝔸_f) with component g at w
and 1 at the other places. -/
def singleGL : GL n (LocField w) →* GL n (𝔸f E) :=
  Units.map
    { toFun g := 1 + (g - 1).map (singleAdele w)
      map_one' := by simp
      map_mul' := by noncomm_ring [← Matrix.map_mul, ← Matrix.map_add _ (map_add _), implies_true] }

/-- The component of `singleGL w g` at `w` itself is `g`. -/
@[simp]
lemma evalAt_singleGL (g : GL n (LocField w)) :
    (singleGL w g : GL n (𝔸f E)).map (evalAt w) = g := by
  have h_same (x : LocField w) : evalAt w (singleAdele w x) = x := singleAdele_same w x
  ext i j : 2
  -- `evalAt_apply` is left out so that `evalAt w` is pushed through sums as a ring homomorphism.
  simp [singleGL, -evalAt_apply, Matrix.one_apply, h_same]

/-- The component of `singleGL w g`, the adelic matrix placing `g` at `w`, at a place `u` other than
`w` is `1`. -/
@[simp]
lemma evalAt_singleGL_of_ne {u w : FinPlace E} (h : u ≠ w) (g : GL n (LocField w)) :
    (singleGL w g).map (evalAt u) = 1 := by
  have h_zero (x : LocField w) : evalAt u (singleAdele w x) = 0 := singleAdele_of_ne h x
  ext i j
  -- `evalAt_apply` is left out so that `evalAt u` is pushed through sums as a ring homomorphism.
  simp [singleGL, -evalAt_apply, Matrix.one_apply, h_zero]

lemma GL_ext_evalAt {a b : GL n (𝔸f E)}
    (h : ∀ u : FinPlace E, a.map (evalAt u) = b.map (evalAt u)) : a = b :=
  Units.ext (matrix_ext_evalAt fun u ↦ congrArg Units.val (h u))

variable {R : Type _} [CommRing R] {O : Subring R}

/-! ### Topology of integral and congruence subgroups -/

/-- The units of the ring of matrices with entries in a subring O form the group `intGL n O` of
invertible matrices that, with their inverses, have entries in O. -/
lemma units_matrix_eq_intGL : (O.matrix (n := n)).units = intGL n O := by
  ext
  exact mem_intGL.symm

/-- If a subring O of R, a commutative ring with a topology, is open, then GL_n(O) = `intGL n O` is
open in GL_n(R). -/
lemma isOpen_intGL [TopologicalSpace R] (h : IsOpen (O : Set R)) : (intGL n O).IsOpen := by
  rw [← units_matrix_eq_intGL]
  exact (O.matrix (n := n)).isOpen_units h.matrix

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- If a subring O of a Hausdorff topological ring R is compact, then GL_n(O) = `intGL n O` is
compact. -/
lemma isCompact_intGL [T2Space R] (h : IsCompact (O : Set R)) :
    IsCompact (intGL n O : Set (GL n R)) := by
  rw [← units_matrix_eq_intGL]
  exact (O.matrix (n := n)).units_isCompact h.matrix

/-- If the subring O of R and the O-submodule M are open, then the congruence subgroup of GL_n(O)
of matrices whose rows e(i) are congruent to those of 1 modulo M is open in GL_n(R). -/
lemma isOpen_congruenceGL {m : Type*} {e : m → n} [Finite m] {M : Submodule O R}
    (hO : IsOpen (O : Set R)) (hM : IsOpen (M : Set R)) : (congruenceGL M e).IsOpen := by
  have h_cont : Continuous fun g : GL n R ↦ (g.val - 1).submatrix e id := by fun_prop
  change IsOpen {g ∈ intGL n O | ∀ (i : m) (j : n), (g.val - 1) (e i) j ∈ M}
  exact (isOpen_intGL hO).and (hM.matrix.preimage h_cont)

/-- If the O-submodules M_i of R shrink to 0 along a filter, then the principal congruence
subgroups of level M_i eventually lie in any given neighbourhood of 1 in GL_n(R). -/
lemma eventually_congruenceGL_subset {ι : Type*} {l : Filter ι} {s : Set (GL n R)}
    {M : ι → Submodule O R} (h_small : Tendsto (fun i : ι ↦ (M i : Set R)) l (nhds 0).smallSets)
    (hs : s ∈ nhds (1 : GL n R)) :
    ∀ᶠ i : ι in l, ∀ g ∈ congruenceGL (M i) id, g ∈ s := by
  -- Follow `g` along the filter "`g ∈ congruenceGL (M i) id` for `i` far along `l`". The topology
  -- of `GL n R` is induced by `g ↦ (g, g⁻¹)`, so it suffices that both matrices tend to `1`.
  let F : Filter (GL n R) := l.bind fun i ↦ 𝓟 {g | g ∈ congruenceGL (M i) id}
  suffices h_le : F ≤ nhds 1 from h_le hs
  -- The entries of `g - 1` lie in `M i`, which shrinks to `0`.
  have h_val : Tendsto (fun g : GL n R ↦ g.val) F (nhds 1) := by
    refine tendsto_sub_nhds_zero_iff.1 (tendsto_pi_nhds.2 fun a ↦ tendsto_pi_nhds.2 fun b U hU ↦ ?_)
    exact (h_small.eventually (mem_lift' hU)).mono fun i h_sub g ⟨_, h_entries⟩ ↦
      h_sub (h_entries a b)
  -- The congruence subgroups are closed under inversion.
  have h_inv : Tendsto (fun g : GL n R ↦ g⁻¹) F F := fun U hU ↦
    l.mem_of_superset hU fun i hi g hg ↦ hi ((congruenceGL (M i) id).inv_mem hg)
  rw [Units.isInducing_embedProduct.nhds_eq_comap, ← tendsto_iff_comap]
  exact h_val.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (h_val.comp h_inv))

end Components

/-! ### The local and adelic groups -/

section Groups

variable {E : Type*} [Field E] [NumberField E] (n : Type*) [Fintype n] [DecidableEq n]
  (w : FinPlace E)

/-- For a finite place w of E, the subgroup GL_n(O_w) of GL_n(E_w) of matrices that, with their
inverses, have entries in the local integers. -/
abbrev localIntGL : Subgroup (GL n (LocField w)) := intGL n (LocInt w).toSubring

/-- The set of g in GL_n(E_w) with g and ϖg⁻¹ integral and det g of valuation j, where ϖ is a
uniformiser. For j at most the cardinality of n it is the GL_n(O_w)-double coset of
diag(ϖ1_j, 1). -/
def basicDoubleCoset (j : ℕ) : Set (GL n (LocField w)) :=
  {g : GL n (LocField w) |
    (∀ a b : n, v (g a b) ≤ 1) ∧ (∀ a b : n, v (g⁻¹ a b) ≤ exp 1) ∧ v g.val.det = exp (-↑j)}

variable (E) [IsCMField E]

/-- The finite adelic unitary group G_f: matrices g in GL_n(𝔸_f) with gᴴg = 1. -/
@[instance_reducible]
def Gf : Type _ := ↥(U (1 : Matrix n n (𝔸f E)))
  deriving Group, TopologicalSpace, MeasurableSpace, DistribMulAction _ (n → 𝔸f E), PolishSpace,
  CoeOut _ (GL n (𝔸f E)), CoeOut _ (Matrix n n (𝔸f E)), SecondCountableTopology

instance : ContinuousSMul (Gf E n) (n → 𝔸f E) := ⟨.matrix_mulVec (by fun_prop) continuous_snd⟩

variable [IsEmpty n] in
deriving instance Subsingleton for Gf E n

@[simp]
lemma Gf.coe_mul (g k : Gf E n) : (g * k).val = g.val * k.val := rfl

/-- The matrix of the product of an element of G_f and an element of `U 1`, which is the same
group, is the product of the matrices. -/
@[simp]
lemma Gf.coe_mul_U (g : Gf E n) (k : U 1) : (g * k).val = g.val * k.val := rfl

@[simp]
lemma Gf.coe_inv (g : Gf E n) : g⁻¹.val = g.val⁻¹ := rfl

@[simp]
lemma Gf.coe_one : (1 : Gf E n).val = 1 := rfl

@[simp]
lemma Gf.subtype_eq_val (g : Gf E n) :
    DFunLike.coe (F := Gf E n →* GL n (𝔸f E)) (U (1 : Matrix n n (𝔸f E))).subtype g = g.val :=
  rfl

/-- A homomorphism f into GL_n(𝔸_f) with values in `U 1`, seen as a homomorphism into G_f, sends x
to f x with the proof that it is unitary. The type `M →* Gf E n` is given explicitly because
`simp` does not unfold `Gf`, so the lemma for `M →* U 1` does not apply to such terms. -/
@[simp]
lemma Gf.codRestrict_eq_mk {M : Type*} [Monoid M] (f : M →* GL n (𝔸f E))
    (h : ∀ x : M, f x ∈ U (1 : Matrix n n (𝔸f E))) (x : M) :
    DFunLike.coe (F := M →* Gf E n) (f.codRestrict (U (1 : Matrix n n (𝔸f E))) h) x =
      ⟨f x, h x⟩ :=
  rfl

@[ext]
lemma Gf.val_ext {g k : Gf E n} (h : g.val = k.val) : g = k := Subtype.ext h

/-- The subgroup K_0 = G_f ∩ GL_n(Ô) of the finite adelic unitary group, the stabiliser of the
standard lattice Ô^n. -/
def stdLevel : Subgroup (Gf E n) := (intGL n (Ô E)).subgroupOf (U 1)

variable {n} (s : n → ℤˣ)

/-- The archimedean unitary group G_∞ for signs s: one copy of the complex unitary group U(diag
s) = `USign s`, the g in GL_n(ℂ) with gᴴ diag(s) g = diag(s), for each infinite place of E. -/
abbrev GInf : Type _ := InfinitePlace E → USign s

/-- The adelic unitary group G = G_∞ × G_f for signs s at the infinite places and the identity
matrix at the finite places. -/
abbrev G : Type _ := GInf E s × Gf E n

/-- Elements of `New.Gf` are viewed in `New.G` with component 1 at the infinite places. -/
instance : Coe (Gf E n) (G E s) := ⟨(1, ·)⟩

/-- The diagonal adelic matrix that is diag(s) at every infinite place and the identity at the
finite places. -/
def stdForm : Matrix n n (𝔸 E) := diagonal (α := 𝔸 E) fun i ↦ (fun _ ↦ s i, 1)

end Groups

section SplitPlaces

variable {E : Type*} [Field E] [NumberField E] {n : Type*} [Fintype n] [DecidableEq n]
  [IsCMField E] {s : n → ℤˣ} {w : FinPlace E} (hw : w.IsSplit)

/-- The function F on G = G_∞ × G_f is right invariant under K, a subset or subgroup of G_f:
F(g·(1, k)) = F(g) for all k ∈ K and all g ∈ G. -/
@[simp]
abbrev HasLevel {W : Sort*} {S : Type*} [Membership _ S] (F : G E s → W) (K : S) :=
  ∀ k ∈ K, ∀ g : G E s, F (g * (1, k)) = F g

/-- The j-th Hecke operator on a representation π of GL_n(E_w): the action (`New.heckeFun`) of
the indicator function of `New.basicDoubleCoset` j, for K = GL_n(O_w). -/
def heckeGL {A W : Type*} [CommSemiring A] [AddCommMonoid W] [Module A W]
    (π : Representation A (GL n (LocField w)) W) (j : ℕ) : Module.End A W :=
  heckeFun π (localIntGL n w) ((basicDoubleCoset n w j).indicator 1)

/-! ### Conjugate places and split places -/

/-- For complex conjugate finite places, `star u = w`, the component at `w` of the conjugate of a
finite adele `x` is the image of its component at `u` under `conjLoc h : E_u →+* E_w`. -/
lemma evalAt_star_eq_conjLoc {u w : FinPlace E} (h : star u = w) (x : 𝔸f E) :
    evalAt w (star x) = conjLoc h (evalAt u x) :=
  adeleMap_apply (starRingEnd E) (star_eq_iff_star_eq.mp h) x

/-- Let `u` and `w` be complex conjugate finite places, `star u = w`, and `g` an invertible matrix
over the finite adeles. The component at `w` of the conjugate transpose of `g` is the transpose of
the component of `g` at `u`, carried to `E_w` by the conjugation `conjLoc h : E_u →+* E_w`. -/
lemma evalAt_star_GL {u w : FinPlace E} (h : star u = w) (g : GL n (𝔸f E)) :
    (GeneralLinearGroup.map (evalAt w) (star g)).val =
      ((GeneralLinearGroup.map (evalAt u) g).val.map (conjLoc h))ᵀ := by
  ext i j : 1
  change evalAt w (star (g j i)) = conjLoc h (evalAt u (g j i))
  exact evalAt_star_eq_conjLoc h (g j i)

/-- For finite places with `star u ≠ w`, where `star u` is the complex conjugate place, the
component at `u` of the conjugate transpose of `singleGL w g` (the adelic matrix with component `g`
at `w` and `1` elsewhere) is `1`. -/
@[local simp]
lemma evalAt_star_singleGL {u w : FinPlace E} (h : star u ≠ w) (g : GL n (LocField w)) :
    (star (singleGL w g)).map (evalAt u) = 1 := by
  ext1
  -- The component at `u` of the conjugate transpose comes from the component at `star u`.
  rw [evalAt_star_GL (star_star u), evalAt_singleGL_of_ne h]
  simp

/-- The homomorphism G_f → GL_n(E_w) sending an element to its component at w. -/
def Gf.atPlace (w : FinPlace E) : Gf E n →* GL n (LocField w) :=
  MonoidHom.comp (GeneralLinearGroup.map (evalAt w)) (U 1).subtype

/-- At a split place `w` (one moved by complex conjugation), the finite adelic matrix with
component `g` at `w`, the inverse of the conjugate transpose of `g` at `star w` and `1` elsewhere
is unitary. -/
lemma singleGL_mul_star_singleGL_inv_mem_U {w : FinPlace E} (hw : w.IsSplit)
    (g : GL n (LocField w)) :
    singleGL w g * star (singleGL w g⁻¹) ∈ U (1 : Matrix n n (𝔸f E)) := by
  set a : GL n (𝔸f E) := singleGL w g * star (singleGL w g⁻¹) with ha
  suffices h_eq : star a * 1 * a = 1 from congrArg Units.val h_eq
  -- The identity is checked at each place, treating `w` and `star w` separately.
  refine GL_ext_evalAt fun u ↦ ?_
  rcases eq_or_ne u w with rfl | hu
  · simp [ha, hw]
  rcases eq_or_ne (star u) w with rfl | hu_star
  · simp [ha, hu]
  · simp [ha, hu, hu_star]

/-- For a split place w, the homomorphism GL_n(E_w) → G_f sending g to the unitary element with
component g at w, the inverse conjugate transpose of g at w̄, and 1 at all other places. -/
def ofSplitPlace : GL n (LocField w) →* Gf E n :=
  MonoidHom.mk' (fun g ↦ ⟨singleGL w g * star (singleGL w g⁻¹),
    singleGL_mul_star_singleGL_inv_mem_U hw g⟩) fun _ _ ↦
    Subtype.ext <| GL_ext_evalAt fun u ↦ by
      by_cases hu : u = w <;> aesop

/-- For a finite place `w` of `E` that is split over the maximal real subfield and for `g` in
`GL_n(E_w)`, the component at `w` of the element `ofSplitPlace hw g` of `G_f` is `g`. -/
@[simp]
lemma atPlace_ofSplitPlace {w : FinPlace E} (hw : w.IsSplit) (g : GL n (LocField w)) :
    (ofSplitPlace hw g).atPlace w = g := by
  -- The factor placed at `star w` has component `1` at `w`, as `star w ≠ w`.
  simp [Gf.atPlace, ofSplitPlace, hw]

variable (n) (S : Set (FinPlace E))

/-! ### Supports, levels and reductions -/

/-- For a ring homomorphism f from the integral finite adeles to S, the homomorphism K_0 →
GL_n(S) applying f to each entry. -/
def stdLevel.map {S : Type*} [CommRing S] (f : Ô E →+* S) : stdLevel E n →* GL n S :=
  (intGL.map f).comp ((U 1).subtype.subgroupComap (intGL n (Ô E)))

/-- The subgroup of G_f of elements supported on S ∪ S̄, that is, with component 1 at every
place outside S ∪ S̄. -/
def Gf.supportedOn : Subgroup (Gf E n) :=
  ⨅ w : FinPlace E, ⨅ _ : w ∉ S ∧ star w ∉ S, (atPlace (n := n) w).ker

/-- The elements of `New.Gf` whose component at each `w ∈ S` lies in the subgroup `K w`, with no
condition outside `S`; by default `K w` is `New.localIntGL`, the integral matrices with integral
inverse. -/
def localLevel (K : (w : FinPlace E) → Subgroup (GL n (LocField w)) := fun w ↦ localIntGL n w) :
    Subgroup (Gf E n) where
  carrier := {g : Gf E n | ∀ w ∈ S, g.atPlace w ∈ K w}
  mul_mem' := by simp_all [mul_mem]
  one_mem' := by simp
  inv_mem' := by simp_all

/-- The subgroup of G_f of elements with component 1 at every place in S (hence, being unitary,
also at the conjugate places). -/
def Gf.trivialOn : Subgroup (Gf E n) := ⨅ w ∈ S, (atPlace (n := n) w).ker

end SplitPlaces

section Levels

section

variable {E : Type*} [Field E] [NumberField E] {n : Type*} [Fintype n] [DecidableEq n]
  [IsCMField E] {s : n → ℤˣ} (g : G E s) {K : Subgroup (Gf E n)}

/-- Reduction modulo w: the homomorphism from K_0 = G_f ∩ GL_n(Ô) to GL_n of the residue field
at w. -/
def stdLevel.reduceAt (w : FinPlace E) : stdLevel E n →* GL n (ResField w) := map n (New.reduceAt w)

/-- An element of the finite adelic unitary group G_f lies in `localLevel n S K` iff its component
at each place `w ∈ S` lies in the subgroup `K w` of GL_n(E_w). -/
lemma mem_localLevel {S : Set (FinPlace E)} {K : (w : FinPlace E) → Subgroup (GL n (LocField w))}
    {g : Gf E n} : g ∈ localLevel n S K ↔ ∀ w ∈ S, g.atPlace w ∈ K w :=
  .rfl

/-- An element of the finite adelic unitary group G_f lies in its integral subgroup K_0 =
`New.stdLevel` iff its entries lie in the integral finite adeles `Ô E`. -/
lemma mem_stdLevel {g : Gf E n} : g ∈ stdLevel E n ↔ ∀ i j : n, g.val i j ∈ Ô E := by
  -- The inverse of a unitary matrix is its conjugate transpose, and `Ô E` is stable under `star`.
  rw [stdLevel, Subgroup.mem_subgroupOf]
  refine mem_intGL.trans (and_iff_left_of_imp fun h i j ↦ ?_)
  simpa [← U.inv_val_eq_conjTranspose, ← conjTranspose_apply] using star_mem_Ô (h j i)

lemma isOpen_stdLevel : (stdLevel E n).IsOpen := (isOpen_intGL isOpen_Ô).preimage_val

lemma isCompact_stdLevel : IsCompact (stdLevel E n : Set (Gf E n)) :=
  (isCompact_intGL isCompact_Ô).preimage_val (isClosed_U _)

/-- The subgroup K of the finite adelic unitary group G_f is a level: it is open and contained
in K_0 = G_f ∩ GL_n(Ô). -/
class IsLevel (K : Subgroup (Gf E n)) : Prop where
  /-- K lies in K_0 = `New.stdLevel`. -/
  le : K ≤ stdLevel E n
  /-- K is open. -/
  isOpen : K.IsOpen

instance : IsLevel (stdLevel E n) := ⟨le_rfl, isOpen_stdLevel⟩

/-- For a subgroup K of G_f, the index [K₀ : K ∩ K₀], where K₀ = `New.stdLevel`; it is 0 if the
index is infinite. -/
abbrev stdLevelIndex (K : Subgroup (Gf E n)) : ℕ := K.relIndex (stdLevel E n)

/-! ### The adelic group as a group of adelic matrices; compactness and Haar measure -/

/-- The homomorphism sending a family (a_w) in GL_n(ℂ), indexed by the infinite places, and b in
GL_n(𝔸_f) to the element of GL_n(𝔸) with components a_w and finite part b. -/
@[simps! apply_val]
def mkAdelicGL : (InfinitePlace E → GL n ℂ) × GL n (𝔸f E) →* GL n (𝔸 E) :=
  MonoidHom.toHomUnits
    { toFun g := of fun i j ↦ (fun v ↦ g.1 v i j, g.2 i j)
      map_one' := by
        ext <;> simp [apply_ite Prod.fst, apply_ite Prod.snd, ite_apply, Matrix.one_apply]
      map_mul' g h := Matrix.ext fun i j ↦ by simp [Matrix.mul_apply, ← prod_mk_sum, funext_iff] }

/-- The isomorphism from G = G_∞ × G_f to the unitary group over the adeles of the form that is
diag(s) at the infinite places and 1 at the finite ones, `New.stdForm`. -/
def G.toUnitary : G E s ≃* U (stdForm E s) where
  toFun g :=
    ⟨mkAdelicGL (fun v ↦ g.1 v, g.2), by
      -- The relation is checked at every infinite place and on the finite part.
      apply matrix_ext_𝔸
      · simp only [↓Matrix.map_mul, stdForm, evalInf_apply, Prod.fst_zero, Pi.zero_apply,
          diagonal_map]
        exact fun v ↦ (g.1 v).property
      · simp only [↓Matrix.map_mul, RingHom.coe_snd, stdForm, Prod.snd_zero, diagonal_map,
          diagonal_one]
        exact g.2.property⟩
  invFun g :=
    (fun v ↦ U.map (evalInf v) (by simp) (by simp [stdForm, signMatrix]) g,
      U.map (RingHom.snd ..) (by simp) (by simp [stdForm]) g)
  map_mul' g k := Subtype.ext (mkAdelicGL.map_mul (_, g.2.1) (_, k.2.1))

/-- The matrix over the adeles of an element g of the adelic unitary group G. -/
@[local simp]
def G.adeleMatrix : Matrix n n (𝔸 E) := g.toUnitary.val.val

/-- At an infinite place, the entries of the adelic matrix `g.adeleMatrix` of an element `g` of
G = G_∞ × G_f are those of the component of `g` there. -/
@[simp]
lemma G.adeleMatrix_fst (g : G E s) (i j : n) (w : InfinitePlace E) :
    (g.adeleMatrix i j).1 w = (g.1 w).val i j :=
  rfl

/-- The finite parts of the entries of the adelic matrix `g.adeleMatrix` of an element `g` of
G = G_∞ × G_f are the entries of the finite component of `g`. -/
@[simp]
lemma G.adeleMatrix_snd (g : G E s) (i j : n) : (g.adeleMatrix i j).2 = g.2.val i j := rfl

@[simp]
lemma G.adeleMatrix_one : adeleMatrix (1 : G E s) = 1 := by simp

@[simp]
lemma G.adeleMatrix_mul (g k : G E s) : (g * k).adeleMatrix = g.adeleMatrix * k.adeleMatrix := by
  simp

@[fun_prop]
lemma G.continuous_adeleMatrix : Continuous (adeleMatrix : G E s → Matrix n n (𝔸 E)) := by
  refine continuous_matrix fun i j ↦ Continuous.prodMk (continuous_pi fun w ↦ ?_) ?_
  · change Continuous fun g : G E s ↦ (g.1 w).val i j
    fun_prop
  · change Continuous fun g : G E s ↦ g.2.val i j
    fun_prop

instance : PolishSpace (GL n (𝔸f E)) where

deriving instance LocallyCompactSpace, BorelSpace, IsTopologicalGroup for Gf E n, G E s

/-- A level is compact: it is an open, hence closed, subgroup contained in the compact group K_0. -/
lemma IsLevel.isCompact {K : Subgroup (Gf E n)} [h : IsLevel K] : IsCompact (K : Set (Gf E n)) :=
  isCompact_stdLevel.of_isClosed_subset (K.isClosed_of_isOpen h.isOpen) h.le

instance [h : IsLevel K] : CompactSpace K := isCompact_iff_compactSpace.1 h.isCompact

/-- The Haar measure on `New.Gf` that gives `New.stdLevel` mass one. -/
instance : MeasureSpace (Gf E n) where
  volume := haarMeasure ⟨⟨_, isCompact_stdLevel⟩, by simp [isOpen_stdLevel.interior_eq]⟩

instance : (volume (α := Gf E n)).IsHaarMeasure := isHaarMeasure_haarMeasure _

/-- For a CM field `E`, the standard level `stdLevel E n` has measure 1 under `volume` on the finite
adelic unitary group `Gf E n` (matrices g over the finite adeles with gᴴg = 1). Here `stdLevel E n`
is the compact open subgroup G_f ∩ GL_n(Ô), the stabiliser of the standard lattice Ô^n. -/
@[simp]
lemma volume_stdLevel : volume (stdLevel E n : Set (Gf E n)) = 1 := haarMeasure_self

end

attribute [local simp] G.adeleMatrix

variable (E : Type*) [Field E] [CMType E] {n : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ}

/-! ### Hermitian spaces with a point -/

/-- A hermitian space with a point: a matrix J over E and x in GL_n(𝔸) with xᴴJx equal to
diag(s) at the infinite places and 1 at the finite places. -/
structure Space (n : Type*) [Fintype n] [DecidableEq n] (s : n → ℤˣ) where
  /-- The matrix over `E` of the hermitian form. -/
  J : Matrix n n E
  /-- The point, an invertible adelic matrix. -/
  x : GL n (𝔸 E)
  /-- In the basis `x` the form is `diag s` at the infinite places and `1` at the finite places. -/
  gram_point : x.1ᴴ * J.map toAdele * x.1 = stdForm E s

namespace Space

variable {E} (V : Space E n s)

/-- For a space (J, x), the isomorphism g ↦ x g x⁻¹ from G to the adelic unitary group U(J)(𝔸). -/
def toRatCoords : G E s ≃* U (V.J.map toAdele) := G.toUnitary.trans (U.conj V.x V.gram_point)

/-- For a space (J, x), the homomorphism γ ↦ x⁻¹ γ x from the rational unitary group U(J)(E) to
G. -/
def ratEmbed : U V.J →* G E s := V.toRatCoords.symm.toMonoidHom.comp (U.map toAdele (by simp) rfl)

/-- For a space (J, x), the homomorphism U(J)(E) → G_f sending γ to the finite part of x⁻¹ γ x. -/
def embFin : U V.J →* Gf E n := (MonoidHom.snd ..).comp V.ratEmbed

/-- For a space (J, x), the subgroup x⁻¹ U(J)(E) x of G, the image of the rational unitary
group. -/
def Γ : Subgroup (G E s) := V.ratEmbed.range

/-- For a space (J, x), the subgroup of G_f formed by the finite parts of the elements x⁻¹ γ x,
γ in U(J)(E). -/
abbrev Γf : Subgroup (Gf E n) := V.embFin.range

/-- For a space (J, x), the adelic vector x⁻¹y attached to a rational vector y in E^n. -/
def vecAtPoint : (n → E) →ₛₗ[(toAdele : E →+* 𝔸 E)] n → 𝔸 E :=
  V.x⁻¹.1.mulVecLin ∘ₛₗ LinearMap.mk (σ := toAdele) ⟨fun y ↦ toAdele ∘ y, by simp⟩
    (by simp [funext_iff])

lemma vecAtPoint_apply (y : n → E) : V.vecAtPoint y = V.x⁻¹.val *ᵥ (toAdele ∘ y) := rfl

/-- For a space (J, x), the lattice E^n ∩ x_f Ô^n, as an additive subgroup of E^n. It consists of
the y whose vector x⁻¹y has integral finite part. -/
def baseLattice : AddSubgroup (n → E) where
  carrier := {y : n → E | ∀ i : n, (V.vecAtPoint y i).2 ∈ Ô E}
  add_mem' := by simp_all [add_mem]
  zero_mem' := by simp
  neg_mem' := by simp

end Space

variable (n)

/-- The definite space I_n with J = 1 and x = 1, the hermitian form given by the sum of the norms
of the coordinates. -/
@[simps]
def stdSpace : Space E n 1 where
  J := 1
  x := 1
  gram_point := by simp [stdForm, ← Pi.one_def, Prod.mk_one_one]

/-- The mass of the genus of O_E^l: the sum of 1/#(Γ ∩ gK_0g⁻¹) over the classes ΓgK_0 in G_f,
where Γ is the image of U_l(E), the rational unitary group of the standard space `stdSpace`. -/
def mass (l : ℕ) : ℝ := (classSum (stdSpace E (Fin l)).Γf (stdLevel E (Fin l)) 1 : ℝ)

variable {E n}

/-- The homomorphism U_n(E) → G_f sending a matrix γ over E with γᴴγ = 1 to its image over the
finite adeles. -/
abbrev stdEmbFin : U (stdSpace E n).J →* Gf E n := (stdSpace E n).embFin

/-- The image of U_n(E), the matrices γ over E with γᴴγ = 1, in the finite adelic unitary group
G_f. -/
abbrev stdRatPoints : Subgroup (Gf E n) := (stdSpace E n).Γf

end Levels

end New

end SpaceDefs

/-! ## An element z of a CM field with z − star z invertible -/

namespace New

variable {E : Type*} [Field E] [NumberField E]

/-- A CM field `E` has an element `z` with `z - star z` invertible, as complex conjugation is not
the identity. -/
lemma exists_isUnit_sub_star [h : NumberField.IsCMField E] : ∃ z : E, IsUnit (z - star z) := by
  obtain ⟨z, hz⟩ : ∃ z : E, NumberField.IsCMField.complexConj E z ≠ z :=
    DFunLike.ne_iff.mp h.complexConj_ne_one
  exact ⟨z, (sub_ne_zero.mpr hz.symm).isUnit⟩

end New

end
