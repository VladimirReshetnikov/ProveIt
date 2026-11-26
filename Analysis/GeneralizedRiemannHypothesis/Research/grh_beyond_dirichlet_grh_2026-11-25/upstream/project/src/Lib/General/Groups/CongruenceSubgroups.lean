import Lib.Base

/-!
# Integral, congruence and unitary matrix groups over a ring, with their topology

The file opens with a few general facts on induction, reindexing, compact, open and closed sets, and
integrability.

* `New.intGL`, `New.congruenceGL`: the matrices of `GL n R` that are invertible over a subring `O`,
  and the congruence subgroups among them; `New.intGL.toMatrix` reads such a matrix over `O`, and
  `New.intGL.map` applies a ring map out of `O`.
* `New.U`: the unitary group of a matrix `J`, the `g` in `GL n R` with `gᴴ * J * g = J`, with change
  of ring `New.U.map`, change of basis `New.U.conj` and determinant `New.U.det`.
* `New.U.isClosedEmbedding_coe`: for invertible `J`, `U J` is closed in the space of matrices; with
  the bound on the entries of a unitary matrix, this gives that the complex unitary group of the
  identity matrix is compact.

The file also supplies the Polish and Borel instances on units, the measurable and measure space
structures on matrices, the Polish instance on unitary groups and the Borel instance on complex
ones, local compactness of unitary groups, and the additive Haar measure on matrices.
-/

noncomputable section

attribute [fun_prop] Continuous.mul_const

open Function Matrix MeasureTheory MulOpposite Set Notation Topology Units

/-- Well-founded induction on an integer weight `w` over a finite type: a property `P` holds
everywhere if it holds at each point as soon as it holds at all points of smaller weight. -/
lemma Finite.int_weight_induction {ι : Type*} [Finite ι] (w : ι → ℤ) {P : ι → Prop}
    (h_step : ∀ a : ι, (∀ b : ι, w b < w a → P b) → P a) (a : ι) : P a :=
  (wellFounded_of_trans_of_irrefl fun a b : ι ↦ w a < w b).induction a h_step

section Reindex

variable {F : Sort*} {α β : Type*} [EquivLike F α β]

/-- A statement `∀ y, p y` about `β` is reindexed along an equivalence `e` from `α` to `β`. -/
lemma New.forall_reindex_equiv (e : F) {p : β → Prop} : (∀ y : β, p y) ↔ ∀ x : α, p (e x) :=
  (EquivLike.surjective e).forall

/-- A statement `∃ y, p y` about `β` is reindexed along an equivalence `e` from `α` to `β`. -/
lemma New.exists_reindex_equiv (e : F) {p : β → Prop} : (∃ y : β, p y) ↔ ∃ x : α, p (e x) :=
  (EquivLike.surjective e).exists

/-- A finite sum over `β` is reindexed along an equivalence `e` from `α` to `β`. -/
lemma New.sum_reindex_equiv [Fintype α] [Fintype β] {M : Type*} [AddCommMonoid M] (e : F)
    (f : β → M) : ∑ i : β, f i = ∑ i : α, f (e i) := ((EquivLike.bijective e).sum_comp f).symm

/-- A finite product over `β` is reindexed along an equivalence `e` from `α` to `β`. -/
lemma New.prod_reindex_equiv [Fintype α] [Fintype β] {M : Type*} [CommMonoid M] (e : F)
    (f : β → M) : ∏ i : β, f i = ∏ i : α, f (e i) := ((EquivLike.bijective e).prod_comp f).symm

/-- For an equivalence `e` from `α` to `β`, statements `∀ y, p y` and `∃ y, p y` about `β`, and
finite sums and products over `β` of values in a type of universe 0, become those over `α` of the
composite with `e`. The four rules are joined so that `simp` takes them as one argument. -/
lemma New.reindex_equiv (e : F) :
    (∀ {p : β → Prop}, (∀ y : β, p y) ↔ ∀ x : α, p (e x)) ∧
    (∀ {p : β → Prop}, (∃ y : β, p y) ↔ ∃ x : α, p (e x)) ∧
    ∀ [Fintype α] [Fintype β] {M : Type} (f : β → M),
      (∀ [AddCommMonoid M], ∑ i : β, f i = ∑ i : α, f (e i)) ∧
      ∀ [CommMonoid M], ∏ i : β, f i = ∏ i : α, f (e i) :=
  ⟨New.forall_reindex_equiv e, New.exists_reindex_equiv e,
    fun f ↦ ⟨New.sum_reindex_equiv e f, New.prod_reindex_equiv e f⟩⟩

end Reindex

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {s K : Set X} {f : Y → X}

/-- If K is compact and s is closed in a topological space, then s ∩ K is compact as a subset of
the subspace s. -/
lemma IsCompact.preimage_val (hK : IsCompact K) (hs : IsClosed s := by infer_instance) :
    IsCompact (s ↓∩ K) := hs.isProperMap_subtypeVal.isCompact_preimage hK

/-- The image of a compact set under a continuous map is compact; continuity is found by
automation unless supplied. -/
lemma IsCompact.image_of_continuous (hs : IsCompact s) (f : X → Y)
    (hf : Continuous f := by fun_prop) :
    IsCompact (f '' s : Set Y) := hs.image hf

/-- The preimage of an open set under a continuous map is open; continuity is found by
automation unless supplied. -/
lemma IsOpen.preimage_of_continuous (hs : IsOpen s) (hf : Continuous f := by fun_prop) :
    IsOpen (f ⁻¹' s) := hs.preimage hf

/-- The preimage of a closed set under a continuous map is closed; continuity is found by
automation unless supplied. -/
lemma IsClosed.preimage_of_continuous (hs : IsClosed s) (hf : Continuous f := by fun_prop) :
    IsClosed (f ⁻¹' s) := hs.preimage hf

variable {E : Type _} [NormedAddCommGroup E] [MeasurableSpace X] [OpensMeasurableSpace X]
  {ν : Measure X} [IsFiniteMeasureOnCompacts ν] {f : X → E}

/-- A continuous function f from a Hausdorff space to a normed group is integrable on a compact
set K, for a measure ν finite on compact sets. Continuity is proved automatically by
default. -/
lemma IsCompact.integrableOn [T2Space X] (hK : IsCompact K) (f : X → E)
    (hf : Continuous f := by fun_prop) : IntegrableOn f K ν :=
  hf.continuousOn.integrableOn_compact hK

/-- A continuous function f of compact support with values in a normed group is integrable, for
a measure ν finite on compact sets. Continuity is proved automatically by default. -/
lemma HasCompactSupport.integrable (hc : HasCompactSupport f) (hf : Continuous f := by fun_prop) :
    Integrable f ν := hf.integrable_of_hasCompactSupport hc

/-- A continuous function from a compact space `X` to a normed group is integrable for every measure
ν on `X` that is finite on compact sets. Continuity is proved automatically by default. -/
lemma New.DiscreteSeries.integrable_of_compactSpace [CompactSpace X]
    (hf : Continuous f := by fun_prop (disch := simp)) : Integrable f ν :=
  HasCompactSupport.integrable (.of_compactSpace f) hf

namespace New

section Matrices

variable {m n R S : Type*} [DecidableEq n]

section

variable [Countable m] [Countable n] [Monoid R] [TopologicalSpace R] [ContinuousMul R]
  [PolishSpace R]

instance : PolishSpace Rˣ := by
  have : PolishSpace Rᵐᵒᵖ := opEquiv.symm.polishSpace_induced
  exact isClosedEmbedding_embedProduct.polishSpace

deriving instance PolishSpace for Matrix m n R

variable [MeasurableSpace R] [BorelSpace R]

instance : MeasurableSpace (Matrix m n R) := .pi

instance : BorelSpace Rˣ := by
  borelize Rˣ
  use (continuous_val.measurableEmbedding val_injective).comap_eq

end

section

variable [Countable m] [Countable n] [TopologicalSpace R] [SecondCountableTopology R]
  [MeasurableSpace R] [BorelSpace R] [Finite m] [Finite n] [Countable R] [LocallyCompactSpace R]

deriving instance Countable, LocallyCompactSpace, BorelSpace for Matrix m n R

end

instance [Fintype m] [Fintype n] [MeasureSpace R] : MeasureSpace (Matrix m n R) := .pi

/-! ### Special matrices -/

/-- For a map u: m → n of index sets, the n×m matrix whose j-th column is the standard basis
vector e_{u(j)}. -/
def inclMatrix (R : Type*) [Zero R] [One R] (u : m → n) : Matrix n m R :=
  submatrix (1 : Matrix n n R) id u

/-- The diagonal complex matrix whose entries are the signs s_i = ±1. -/
def signMatrix (s : n → ℤˣ) : Matrix n n ℂ := Matrix.diagonal fun i : n ↦ (s i : ℂ)

@[simp]
lemma signMatrix_one : signMatrix (n := n) 1 = 1 := by simp [signMatrix]

variable [Fintype n] [CommRing R] [CommRing S] {O : Subring R}

/-- Multiplying M on the right by the inclusion matrix of u selects the columns u(j) of M. -/
lemma mul_inclMatrix {l : Type*} (M : Matrix l n R) (u : m → n) :
    M * inclMatrix R u = M.submatrix id u := mul_submatrix_one (Equiv.refl n) u M

omit [Fintype n] in
lemma one_map_ringHom (f : R →+* S) : (1 : Matrix n n R).map f = 1 :=
  Matrix.map_one f f.map_zero f.map_one

/-- The diagonal matrix of a vector of signs ε is its own inverse. -/
lemma signMatrix_mul_self (ε : n → ℤˣ) : signMatrix ε * signMatrix ε = 1 := by
  simp [signMatrix, ← Int.cast_mul]

/-- The homomorphism sending a family of units of R to the diagonal matrix in GL_n(R) with these
entries. -/
def diagGL : (n → Rˣ) →* GL n R :=
  (Units.map (diagonalRingHom n R).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

@[simp]
lemma coe_diagGL (t : n → Rˣ) : (diagGL t).val = Matrix.diagonal fun i : n ↦ ↑(t i) := rfl

/-- The transpose of g, as an element of GL_n(R). -/
@[simps]
def transposeGL (g : GL n R) : GL n R where
  val := gᵀ
  inv := g⁻¹.1ᵀ
  val_inv := by simp [← transpose_mul]
  inv_val := by simp [← transpose_mul]

/-- For distinct indices i, j and a in R, the element 1 + aE_{ij} of GL_n(R), with inverse
1 − aE_{ij}. -/
@[simps]
def transvectionGL {i j : n} (h : i ≠ j) (a : R) : GL n R where
  val := transvection i j a
  inv := transvection i j (-a)
  val_inv := by simp [transvection_mul_transvection_same, h]
  inv_val := by simp [transvection_mul_transvection_same, h]

/-! ### Integral matrices and congruence subgroups -/

/-- For a subring O of R, the subgroup GL_n(O) of GL_n(R): matrices with entries in O whose
inverse has entries in O. -/
def intGL (n : Type*) [Fintype n] [DecidableEq n] (O : Subring R) : Subgroup (GL n R) :=
  (GeneralLinearGroup.map (n := n) O.subtype).range

/-- A matrix lies in GL_n(O) if and only if its entries and those of its inverse lie in O. -/
lemma mem_intGL {g : GL n R} :
    g ∈ intGL n O ↔ (∀ i j : n, g i j ∈ O) ∧ ∀ i j : n, g⁻¹ i j ∈ O := by
  refine ⟨fun ⟨k, hk⟩ ↦ by simp [← hk, ← map_inv], fun ⟨h_val, h_inv⟩ ↦ ?_⟩
  -- Lift `g` and its inverse to matrices over `O`; they are still inverse to each other.
  let A : Matrix n n O := of fun i j ↦ ⟨g i j, h_val i j⟩
  let B : Matrix n n O := of fun i j ↦ ⟨g⁻¹ i j, h_inv i j⟩
  have hAB : (A * B).map O.subtype = (1 : Matrix n n O).map O.subtype := by
    rw [Matrix.map_mul, one_map_ringHom]
    exact g.mul_inv
  exact ⟨.mkOfMulEqOne A B (map_injective O.subtype_injective hAB), Units.ext rfl⟩

/-- The matrix over `O` with the entries of an element `k` of GL_n(O). -/
def intGL.toMatrix (k : intGL n O) : Matrix n n O :=
  of fun i j ↦ ⟨((k : GL n R) : Matrix n n R) i j, (mem_intGL.mp k.prop).left i j⟩

/-- The entry of `toMatrix k`, the matrix over `O` of an integral matrix `k`, at `(i, j)` is the
entry of `k`, read in `O`. -/
@[simp]
lemma intGL.toMatrix_apply (k : intGL n O) (i j : n) :
    toMatrix k i j = ⟨((k : GL n R) : Matrix n n R) i j, (mem_intGL.mp k.prop).left i j⟩ := rfl

/-- For a ring homomorphism f: O → S, the homomorphism GL_n(O) → GL_n(S) applying f to each
entry. -/
def intGL.map (f : O →+* S) : intGL n O →* GL n S :=
  (GeneralLinearGroup.map f).comp <| MonoidHom.toHomUnits
    { toFun := toMatrix
      map_one' := by aesop (add simp Matrix.one_apply)
      map_mul' := by aesop (add simp mul_apply) }

variable {f : O →+* S} {k : intGL n O}

/-- The entries of the image of an integral matrix k are the images under f of its entries, read
in `O`. -/
@[simp]
lemma intGL.map_apply (i j : n) : map f k i j = f (toMatrix k i j) := rfl

/-- An integral matrix `k` maps to `1` under `f` if and only if `f` kills every entry of
`k - 1`, read in `O`. -/
lemma intGL.map_eq_one :
    map f k = 1 ↔ ∀ i j : n, f (toMatrix k i j - toMatrix (1 : intGL n O) i j) = 0 := by
  simp only [← map_one (map f), GeneralLinearGroup.ext_iff, map_apply, map_sub, sub_eq_zero]

/-- For a subring O of R, the O-submodule of R spanned by a consists of the a y with y in O. -/
@[simp]
lemma mem_span_singleton_iff_exists_mul {a x : R} : x ∈ O ∙ a ↔ ∃ y ∈ O, x = a * y := by
  simp [Submodule.mem_span_singleton, O.smul_def, mul_comm, eq_comm]

/-- For an O-submodule M of R and a map e of index sets, the group of matrices in GL_n(O) whose
rows e(i) are congruent to those of 1 modulo M; for e the identity, the principal congruence
subgroup of level M. -/
def congruenceGL (M : Submodule O R) (e : m → n) : Subgroup (GL n R) :=
  Subgroup.ofDiv {g ∈ intGL n O | ∀ (i : m) (j : n), (g.1 - 1) (e i) j ∈ M} ⟨1, by simp⟩ <| by
    rintro g ⟨hg, hg_row⟩ k ⟨hk, hk_row⟩
    refine ⟨div_mem hg hk, fun i j ↦ ?_⟩
    -- `g k⁻¹ - 1 = ((g - 1) - (k - 1)) k⁻¹`, and `k⁻¹` has entries in `O`.
    have h_eq : (g * k⁻¹).1 - 1 = ((g.1 - 1) - (k.1 - 1)) * k⁻¹.1 := by simp [sub_mul]
    rw [h_eq, mul_apply]
    refine sum_mem fun l _ ↦ ?_
    rw [mul_comm]
    exact M.smul_mem ⟨k⁻¹.val l j, (mem_intGL.mp hk).right l j⟩ (sub_mem (hg_row i l) (hk_row i l))

end Matrices

/-! ### Unitary groups -/

section Unitary

variable {m n R S : Type*} [Fintype n] [CommRing R] [CommRing S] [StarRing R] [StarRing S]

/-- A ring map f that commutes with the involutions carries zᴴ B z to (f z)ᴴ (f B) (f z). -/
lemma map_conjTranspose_mul_mul (f : R →+* S) (hf : ∀ x : R, f (star x) = star (f x))
    (z B : Matrix n n R) : (zᴴ * B * z).map f = (z.map f)ᴴ * B.map f * z.map f := by
  simp [conjTranspose_map _ hf]

/-- The Gram matrix of XY for the form J is Yᴴ (Xᴴ J X) Y. -/
lemma gram_mul {c : Type*} [Fintype m] (X : Matrix n m R) (J : Matrix n n R) (Y : Matrix m c R) :
    (X * Y)ᴴ * J * (X * Y) = Yᴴ * (Xᴴ * J * X) * Y := by simp [Matrix.mul_assoc]

variable [DecidableEq n]

/-- If x carries the form J to J' and y carries J' to J'', then xy carries J to J''. -/
lemma gram_mul_of_gram_eq {J J' J'' : Matrix n n R} {x y : GL n R} (hx : x.valᴴ * J * x = J')
    (hy : y.valᴴ * J' * y = J'') : (x * y).valᴴ * J * (x * y).val = J'' := by
  rw [Units.val_mul, gram_mul, hx, hy]

/-- If x carries the form J to J', then its inverse carries J' to J. -/
lemma gram_inv_of_gram_eq {J J' : Matrix n n R} {x : GL n R} (hx : x.valᴴ * J * x = J') :
    x⁻¹.valᴴ * J' * x⁻¹ = J := by simp [← hx, ← gram_mul]

/-- The unitary group U(J) of a matrix J over a commutative ring with involution: the g in
GL_n(R) with gᴴJg = J. -/
def U (J : Matrix n n R) : Subgroup (GL n R) where
  carrier := {g : GL n R | g.1ᴴ * J * g.1 = J}
  mul_mem' := gram_mul_of_gram_eq
  one_mem' := by simp
  inv_mem' := gram_inv_of_gram_eq

/-- For a vector of signs ε, the unitary group U(J) of the diagonal matrix J=diag(ε). -/
abbrev USign (ε : n → ℤˣ) := U (signMatrix ε)

variable {J : Matrix n n R}

lemma mem_U {g : GL n R} : g ∈ U J ↔ g.valᴴ * J * g = J := .rfl

-- An element of a unitary group is read as its matrix.
instance : CoeOut (U J) (Matrix n n R) := ⟨(·.val.val)⟩

namespace U

/-- For g in the unitary group U(J), one has J g⁻¹ = gᴴ J. -/
lemma form_mul_inv_eq (g : U J) : J * ((g⁻¹ : U J) : Matrix n n R) = (g : Matrix n n R)ᴴ * J :=
  (mul_inv_eq_iff_eq_mul g.val).mpr (mem_U.mp g.prop).symm

/-- If J is an involution, the inverse of g in the unitary group U(J) is J gᴴ J. -/
lemma coe_inv (hJ : J * J = 1) (g : U J) :
    ((g⁻¹ : U J) : Matrix n n R) = J * (g : Matrix n n R)ᴴ * J := by
  rw [mul_assoc, ← form_mul_inv_eq, ← mul_assoc, hJ, one_mul]

/-- In the unitary group of the identity matrix, the inverse is the conjugate transpose. -/
lemma inv_val_eq_conjTranspose (g : U (1 : Matrix n n R)) :
    ((g⁻¹ : U (1 : Matrix n n R)) : Matrix n n R) = (g : Matrix n n R)ᴴ := by
  simpa using form_mul_inv_eq g

/-- An element g of U(J) preserves the pairing Aᴴ J B of matrices A and B. -/
lemma gram_invariant (g : U J) {a b : Type*} (A : Matrix n a R) (B : Matrix n b R) :
    ((g : Matrix n n R) * A)ᴴ * J * ((g : Matrix n n R) * B) = Aᴴ * J * B := by
  simp [Matrix.mul_assoc, ← form_mul_inv_eq]

/-- An element g of U(J) preserves the sesquilinear form with matrix J. -/
lemma form_mulVec_mulVec (g : U J) (x y : n → R) :
    star (g *ᵥ x) ⬝ᵥ J *ᵥ g *ᵥ y = star x ⬝ᵥ J *ᵥ y := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, mem_U.mp g.prop]

/-- For invertible J and a matrix M with MᴴJM = J, the element of U(J) with matrix M. -/
@[simps! coe_val]
def of (hJ : IsUnit J) M (h : Mᴴ * J * M = J) : U J :=
  ⟨(isUnit_of_mul_isUnit_right (by rwa [h] : IsUnit (Mᴴ * J * M))).unit, h⟩

/-- For a ring homomorphism f commuting with the involutions and carrying J to J', the
homomorphism U(J) → U(J') applying f to each entry. By default `simp` proves both conditions. -/
def map (f : R →+* S) (hf : ∀ x : R, f (star x) = star (f x) := by simp) {J : Matrix n n R}
    {J' : Matrix n n S} (h : J.map f = J' := by simp) : U J →* U J' :=
  ((GeneralLinearGroup.map f).comp (U J).subtype).codRestrict (U J') fun g ↦ by
    -- Apply `f` to `gᴴ * J * g = J`.
    show ((g : Matrix n n R).map f)ᴴ * J' * (g : Matrix n n R).map f = J'
    rw [← h, ← map_conjTranspose_mul_mul f hf, mem_U.mp g.prop]

/-- Let `f : R → S` be an injective ring map that commutes with the involutions and carries the
invertible n × n matrix `J` over `R` to `J'`. An element `g` of the unitary group `U J'` whose
matrix is the image under `f` of a matrix `M` over `R` is the image of an element of `U J` with
matrix `M`. -/
lemma mem_range_map {f : R →+* S} (hf_star : ∀ x : R, f (star x) = star (f x))
    (hf_inj : Injective f) {J : Matrix n n R} (hJ : IsUnit J) {J' : Matrix n n S}
    (hJ_map : J.map f = J') {g : U J'} {M : Matrix n n R}
    (hM_map : M.map f = (g : Matrix n n S)) :
    ∃ k : U J, (k : Matrix n n R) = M ∧ map f hf_star hJ_map k = g := by
  -- `M` preserves `J` because its image under the injective map `f` preserves `J'`.
  have h_form : (Mᴴ * J * M).map f = J.map f := by
    rw [map_conjTranspose_mul_mul f hf_star, hM_map, hJ_map, mem_U.mp g.prop]
  exact ⟨of hJ M (map_injective hf_inj h_form), rfl, Subtype.ext (Units.ext hM_map)⟩

/-- For x in GL_n(R) with xᴴJx = J', the isomorphism U(J') ≅ U(J), g ↦ x g x⁻¹. -/
@[simps! apply_coe symm_apply_coe]
def conj (x : GL n R) {J} {J' : Matrix n n R} (h : x.1ᴴ * J * x = J') : U J' ≃* U J where
  toFun g := ⟨x * g * x⁻¹, gram_mul_of_gram_eq (gram_mul_of_gram_eq h g.2) (gram_inv_of_gram_eq h)⟩
  invFun g := ⟨x⁻¹ * g * x, gram_mul_of_gram_eq (gram_mul_of_gram_eq (gram_inv_of_gram_eq h) g.2) h⟩
  left_inv g := by simp [mul_assoc]
  right_inv g := by simp [mul_assoc]
  map_mul' g k := by simp [mul_assoc]

/-- For J with unit determinant, the determinant as a homomorphism from U(J) to the group of
elements u of R with uū = 1. -/
def det (hJ : IsUnit J.det) : U J →* unitary R :=
  MonoidHom.mk' (fun g ↦ ⟨(g : Matrix n n R).det, by
    -- Take determinants in `gᴴ * J * g = J` and cancel `det J`.
    have h_det : ((g : Matrix n n R)ᴴ * J * g).det = J.det := by rw [mem_U.mp g.prop]
    simpa [unitary, mul_comm, mul_assoc, hJ.mul_eq_left] using h_det⟩) (by simp)

/-- Let `f : R → S` be a continuous ring map that commutes with the involutions and carries `J` to
`J'`. The induced map `U J → U J'` of unitary groups is continuous. -/
lemma continuous_map {f : R →+* S} [TopologicalSpace R] [TopologicalSpace S]
    (hf_cont : Continuous f := by fun_prop) {hf_star : ∀ x : R, f (star x) = star (f x)}
    {J' : Matrix n n S} {hJ_map : J.map f = J'} :
    Continuous (map f hf_star hJ_map : U J → U J') :=
  (by fun_prop : Continuous fun g : U J ↦ GeneralLinearGroup.map f (g : GL n R)).subtype_mk _

end U

end Unitary

/-! ### Topology of unitary groups -/

section Topology

variable {m n R S : Type*} [DecidableEq n] [Fintype n] [CommRing R] [StarRing R]
  [TopologicalSpace R] [IsTopologicalRing R] [ContinuousStar R]

/-- The unitary group `U J` of a matrix J is closed in GL_n(R), for a Hausdorff topological ring R
with continuous involution. -/
lemma isClosed_U (J : Matrix n n R) [T2Space R] : IsClosed (U J : Set (GL n R)) :=
  isClosed_eq (f := fun g : GL n R ↦ g.valᴴ * J * g) (by fun_prop) continuous_const

instance (J : Matrix n n R) [T2Space R] [LocallyCompactSpace R] : LocallyCompactSpace (U J) :=
  (isClosed_U J).locallyCompactSpace

instance (J : Matrix n n R) [PolishSpace R] : PolishSpace (U J) := (isClosed_U J).polishSpace

variable {J : Matrix n n R} [T2Space R]

omit [IsTopologicalRing R] [ContinuousStar R] in
/-- A subgroup `H` of `U J` that is described by asking the entries `(i, j)` with `p i j` to equal
those of the identity matrix is closed. -/
lemma isClosed_of_entries_eq_one {H : Subgroup (U J)} {p : n → n → Prop}
    (hH : ∀ {g : U J}, g ∈ H ↔ ∀ i j : n, p i j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j) :
    IsClosed (H : Set (U J)) := by
  -- The `(i, j)` entry is continuous and constant on `H`, hence also on its closure.
  refine isClosed_of_closure_subset fun g hg ↦ hH.mpr fun i j hij ↦ ?_
  exact EqOn.closure (f := fun k : U J ↦ (k : Matrix n n R) i j) (fun k hk ↦ hH.mp hk i j hij)
    (by fun_prop) continuous_const hg

/-- For invertible J over a Hausdorff topological commutative ring with continuous involution,
the map sending an element of the unitary group U(J) to its matrix is a closed embedding. -/
lemma U.isClosedEmbedding_coe (hJ : IsUnit J) :
    IsClosedEmbedding (fun g : U J ↦ (g : Matrix n n R)) := by
  -- `g ↦ (g, g⁻¹)` is a closed embedding, and on `U J` the inverse is the continuous
  -- function `J⁻¹ * gᴴ * J` of the matrix, so this map factors through the graph of that
  -- function.
  have h_graph : IsEmbedding fun M : Matrix n n R ↦ (M, op (J⁻¹ * Mᴴ * J)) :=
    isEmbedding_graph (by fun_prop)
  have h_inv (g : U J) : J⁻¹ * (g : Matrix n n R)ᴴ * J = (g⁻¹ : U J) := by
    simp [← isUnit_iff_isUnit_det, hJ, ← form_mul_inv_eq, mul_assoc]
  have h_pair :
      IsClosedEmbedding fun g : U J ↦ ((g : Matrix n n R), op (J⁻¹ * (g : Matrix n n R)ᴴ * J)) := by
    simp only [h_inv]
    exact isClosedEmbedding_embedProduct.comp (isClosed_U J).isClosedEmbedding_subtypeVal
  exact .of_comp h_graph h_pair

/-- An element of the complex unitary group U(1) of the identity matrix is a unitary matrix. -/
lemma U_one_mem_unitaryGroup (g : U (1 : Matrix n n ℂ)) :
    (g : Matrix n n ℂ) ∈ unitaryGroup n ℂ := by
  simpa [mem_unitaryGroup_iff', star_eq_conjTranspose] using mem_U.mp g.prop

instance : CompactSpace (U (1 : Matrix n n ℂ)) := by
  -- The entries of a unitary matrix lie in the closed unit disc, so the group is the preimage of
  -- a compact set of matrices under a closed embedding.
  have h_compact : IsCompact
      {g : U (1 : Matrix n n ℂ) | (g : Matrix n n ℂ) ∈ (Metric.closedBall 0 1).matrix} :=
    (U.isClosedEmbedding_coe isUnit_one).isCompact_preimage (isCompact_closedBall 0 1).matrix
  simpa [← isCompact_univ_iff, mem_matrix, entry_norm_bound_of_unitary, U_one_mem_unitaryGroup]
    using h_compact

instance : CompactSpace (U (signMatrix (n := n) 1)) := signMatrix_one.substr inferInstance

/-- For a complex matrix J, the unitary group U(J) carries the Borel σ-algebra of its topology. -/
instance U.borelSpace {J : Matrix n n ℂ} : BorelSpace (U J) := inferInstance

variable {A : Type*} [Fintype m] [AddGroup A] [TopologicalSpace A] [MeasureSpace A]
  [(volume (α := A)).IsAddHaarMeasure] [SigmaFinite (volume (α := A))] [MeasurableAdd A]

instance : SigmaFinite (volume (α := Matrix m n A)) := Measure.pi.sigmaFinite _

/-- The product measure on functions from `n` to `A` is an additive Haar measure. -/
instance isAddHaarMeasure_pi : (volume (α := n → A)).IsAddHaarMeasure where

instance : (volume (α := Matrix m n A)).IsAddHaarMeasure := isAddHaarMeasure_pi

end Topology

end New

end
