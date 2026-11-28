import Lib.General.LinearAlgebra.PartnerAlgebra

/-!
# The Gram matrix of a space is invertible and hermitian; group elements from isometries

Let `E` be a number field and `s : n → ℤˣ` a family of signs. The standard form `New.stdForm E s`
is its own inverse. It is hermitian when `E` has a CM type (`CMType E`), and then the Gram matrix
of a space is invertible and hermitian. For a CM field, matrices that preserve the standard form
give elements of the adelic unitary group.

## Notation

* `New.𝔸 E`: the adeles of `E`, with the diagonal embedding `New.toAdele : E →+* 𝔸 E`, given at
  the infinite places by the chosen CM type of `E`.
* `New.stdForm E s`: the diagonal adelic matrix with the signs `s` at the infinite places and `1`
  at the finite places.
* `New.Space E n s`: a matrix `J` over `E` with an invertible adelic matrix `x` such that
  `xᴴ * J.map toAdele * x` is `New.stdForm E s`.
* `New.G E s`: the adelic unitary group of the standard form; `New.G.adeleMatrix` is the matrix of
  an element.

## Main definitions and results

* `New.Space.isUnit_J`, `New.Space.isHermitian_J`: `J` is invertible and hermitian.
* `New.G.ofMatrix`: the group element given by a matrix that preserves the standard form.
-/

section SpaceGram

open NumberField Matrix

namespace New
section

variable {E : Type*} [Field E] [NumberField E] {n : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ}

/-- The standard form `stdForm E s`, which is diagonal with the signs `s` at the infinite places
and `1` at the finite places, is its own inverse. -/
@[simp]
lemma stdForm_mul_self : stdForm E s * stdForm E s = 1 := by
  simp [stdForm, funext_iff, ← Int.cast_mul]

omit [Fintype n] in
@[simp]
lemma stdForm_one : stdForm E (1 : n → ℤˣ) = 1 := by
  rw [stdForm, ← diagonal_one, diagonal_eq_diagonal_iff]
  intro i
  ext <;> simp

@[simp]
lemma isUnit_stdForm : IsUnit (stdForm E s) := .of_mul_eq_one _ stdForm_mul_self

end

variable {E : Type*} [Field E] [CMType E] {n : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ}

omit [Fintype n] in
/-- The standard form `stdForm E s`, a diagonal matrix with the signs `s` at the infinite places
and `1` at the finite places, is hermitian. -/
@[simp]
lemma conjTranspose_stdForm : (stdForm E s)ᴴ = stdForm E s := by
  rw [stdForm, diagonal_conjTranspose, diagonal_eq_diagonal_iff]
  intro i
  ext <;> simp

/-- The diagonal embedding `toAdele` of `E` in its adeles, given at the infinite places by the CM
type, commutes with the conjugate transpose of matrices. -/
@[simp]
lemma conjTranspose_map_toAdele {m k : Type*} (a : Matrix m k E) :
    (a.map toAdele)ᴴ = aᴴ.map toAdele := by
  exact (conjTranspose_map _ fun x ↦ (star_toAdele x).symm).symm

namespace Space
/-- A space `V` is a matrix `J` over `E` with an invertible adelic matrix `x` such that
`xᴴ J x = S`, where `S = stdForm E s` is the diagonal matrix of signs and `toAdele` maps `E` to
its adeles. Over the adeles `J = (x⁻¹)ᴴ S x⁻¹`. -/
lemma map_J (V : Space E n s) : V.J.map toAdele = V.x⁻¹.valᴴ * stdForm E s * V.x⁻¹.val :=
  (gram_inv_of_gram_eq V.gram_point).symm

@[simp]
lemma isUnit_J (V : Space E n s) : IsUnit V.J := by
  have h_adelic : IsUnit (toAdele.mapMatrix V.J) := by simp [map_J]
  exact isUnit_of_mapMatrix toAdele h_adelic

lemma map_J_inv_mul_map_J (V : Space E n s) : V.J⁻¹.map toAdele * V.J.map toAdele = 1 := by
  have h_det : IsUnit V.J.det := (isUnit_iff_isUnit_det V.J).mp V.isUnit_J
  simp [← Matrix.map_mul, nonsing_inv_mul V.J h_det]

lemma map_J_inv (V : Space E n s) :
    V.J⁻¹.map toAdele = V.x.val * stdForm E s * V.x.valᴴ := by
  have h_gram_mul_stdForm : V.x.valᴴ * V.J.map toAdele * V.x.val * stdForm E s = 1 := by
    rw [V.gram_point, stdForm_mul_self]
  have h_right_inv : V.J.map toAdele * (V.x.val * stdForm E s * V.x.valᴴ) = 1 := by
    rw [← mul_assoc, mul_eq_one_comm]
    simpa only [mul_assoc] using h_gram_mul_stdForm
  exact left_inv_eq_right_inv V.map_J_inv_mul_map_J h_right_inv

lemma isHermitian_J (V : Space E n s) : V.J.IsHermitian := by
  have h_adelic : V.Jᴴ.map toAdele = V.J.map toAdele := by
    simp [← conjTranspose_map_toAdele, map_J, mul_assoc]
  exact map_injective toAdele.injective h_adelic

lemma conjTranspose_J (V : Space E n s) : V.Jᴴ = V.J := V.isHermitian_J.eq

/-- The Gram matrix `J` of a space `V` is hermitian, so for matrices `X`, `Y` over `E` with rows
indexed by `n`, the matrix `Yᴴ J X` is the conjugate transpose of `Xᴴ J Y`. -/
lemma conjTranspose_mul_J_mul_swap (V : Space E n s) {a b : Type*} (X : Matrix n a E)
    (Y : Matrix n b E) :
    Yᴴ * V.J * X = (Xᴴ * V.J * Y)ᴴ := by
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, V.conjTranspose_J,
    Matrix.mul_assoc]

end Space

end New

end SpaceGram

namespace New

open scoped Matrix

variable {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]
  {n : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ}

/-- The element of the adelic unitary group `G E s` given by an adelic matrix `m` with
`mᴴ S m = S`, where `S` is the standard form `stdForm E s`. -/
noncomputable def G.ofMatrix (m : Matrix n n (𝔸 E)) (h : mᴴ * stdForm E s * m = stdForm E s) :
    G E s :=
  toUnitary.symm (U.of isUnit_stdForm m h)

/-- For a CM field `E` and signs `s` indexed by a finite type `n`, let `S = stdForm E s` be the
diagonal adelic matrix with the signs `s` at the infinite places and `1` at the finite places. If an
adelic matrix `m` satisfies `mᴴ S m = S`, the element `G.ofMatrix m h` of the adelic unitary group
`G E s` of `S` has matrix `m`. -/
@[simp]
lemma G.adeleMatrix_ofMatrix (m : Matrix n n (𝔸 E)) (h : mᴴ * stdForm E s * m = stdForm E s) :
    (ofMatrix m h).adeleMatrix = m := rfl

end New
