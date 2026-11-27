import Lib.General.LinearAlgebra.MatrixPolynomials

/-!
# The unipotent radical attached to an idempotent matrix

For an idempotent matrix `ε`, the matrices `1 + ε Y (1 - ε)` form the unipotent radical of the
parabolic subgroup that keeps the image of `ε`. If a polynomial in `g` is a projection onto the
image of `ε`, then every translate of `g` by the radical is conjugate to `g` under the radical
(`semiconjBy_radicalHom_aeval_sub`).
-/

open Matrix Polynomial Multiplicative

namespace New

variable {n k : Type*} [Fintype n] [DecidableEq n] [CommRing k] {ε : Matrix n n k}

variable (ε) in
/-- The upper right blocks with respect to `ε`: the matrices `Z` with `ε Z = Z` and `Z ε = 0`. For
an idempotent `ε` these are the maps that kill the image of `ε` and send everything into it. -/
def upperBlocks : Submodule k (Matrix n n k) where
  carrier := {Z : Matrix n n k | ε * Z = Z ∧ Z * ε = 0}
  add_mem' := by
    rintro Y Z ⟨hεY, hYε⟩ ⟨hεZ, hZε⟩
    exact ⟨by rw [mul_add, hεY, hεZ], by rw [add_mul, hYε, hZε, add_zero]⟩
  zero_mem' := ⟨mul_zero ε, zero_mul ε⟩
  smul_mem' := by
    rintro c Z ⟨hεZ, hZε⟩
    exact ⟨by rw [mul_smul_comm, hεZ], by rw [smul_mul_assoc, hZε, smul_zero]⟩

lemma mem_upperBlocks_iff {Z : Matrix n n k} :
    Z ∈ upperBlocks ε ↔ ε * Z = Z ∧ Z * ε = 0 :=
  Iff.rfl

lemma mul_mul_one_sub_mem_upperBlocks (hε : IsIdempotentElem ε) (Y : Matrix n n k) :
    ε * Y * (1 - ε) ∈ upperBlocks ε :=
  mem_upperBlocks_iff.mpr ⟨by rw [← mul_assoc, ← mul_assoc, hε.eq],
    by rw [mul_assoc, hε.one_sub_mul_self, mul_zero]⟩

/-- An upper right block `Y` (that is, `ε Y = Y` and `Y ε = 0`) satisfies `Y Z = 0` for every matrix
`Z` with `ε Z = Z`. -/
lemma mul_eq_zero_of_mem_upperBlocks {Y Z : Matrix n n k} (hY : Y ∈ upperBlocks ε)
    (hZ : ε * Z = Z) : Y * Z = 0 := by
  rw [← hZ, ← mul_assoc, (mem_upperBlocks_iff.mp hY).2, zero_mul]

/-- The upper right blocks, the matrices `Z` with `ε Z = Z` and `Z ε = 0`, are stable under left
multiplication by a matrix `g` with `ε g ε = g ε` (for an idempotent `ε`: `g` keeps the image of
`ε`). -/
lemma mul_mem_upperBlocks_left {g Z : Matrix n n k} (hg : ε * (g * ε) = g * ε)
    (hZ : Z ∈ upperBlocks ε) : g * Z ∈ upperBlocks ε := by
  obtain ⟨hεZ, hZε⟩ := mem_upperBlocks_iff.mp hZ
  exact mem_upperBlocks_iff.mpr ⟨by rw [← hεZ, ← mul_assoc g, ← mul_assoc, hg],
    by rw [mul_assoc, hZε, mul_zero]⟩

/-- The upper right blocks, the matrices `Z` with `ε Z = Z` and `Z ε = 0`, are stable under right
multiplication by a matrix `g` with `ε g ε = g ε`. -/
lemma mul_mem_upperBlocks_right {g Z : Matrix n n k} (hg : ε * (g * ε) = g * ε)
    (hZ : Z ∈ upperBlocks ε) : Z * g ∈ upperBlocks ε := by
  obtain ⟨hεZ, -⟩ := mem_upperBlocks_iff.mp hZ
  exact mem_upperBlocks_iff.mpr
    ⟨by rw [← mul_assoc, hεZ], by rw [mul_assoc, mul_eq_zero_of_mem_upperBlocks hZ hg]⟩

/-- The homomorphism `Y ↦ 1 + ε Y (1 - ε)` from the additive group of matrices to `GL n k`. Its
image is the unipotent radical of the parabolic subgroup that keeps the image of the idempotent
`ε`. -/
noncomputable def radicalHom (hε : IsIdempotentElem ε) :
    Multiplicative (Matrix n n k) →* GL n k :=
  MonoidHom.toHomUnits
    { toFun Y := 1 + ε * Y.toAdd * (1 - ε)
      map_one' := by rw [toAdd_one, mul_zero, zero_mul, add_zero]
      map_mul' Y Z := by
        have h_zero : ε * Y.toAdd * (1 - ε) * (ε * Z.toAdd * (1 - ε)) = 0 :=
          mul_eq_zero_of_mem_upperBlocks (mul_mul_one_sub_mem_upperBlocks hε Y.toAdd)
            (mem_upperBlocks_iff.mp (mul_mul_one_sub_mem_upperBlocks hε Z.toAdd)).1
        rw [toAdd_mul]
        linear_combination (norm := noncomm_ring) -h_zero }

lemma coe_radicalHom (hε : IsIdempotentElem ε) (Y : Multiplicative (Matrix n n k)) :
    (radicalHom hε Y : Matrix n n k) = 1 + ε * Y.toAdd * (1 - ε) := rfl

/-- If `ε Z = Z` and `Z ε = 0`, that is, if `Z` is an upper right block, then the matrix
`1 + ε Z (1 - ε)` of `radicalHom` is `1 + Z`. -/
lemma coe_radicalHom_of_mem (hε : IsIdempotentElem ε) {Z : Matrix n n k}
    (hZ : Z ∈ upperBlocks ε) : (radicalHom hε (ofAdd Z) : Matrix n n k) = 1 + Z := by
  obtain ⟨hεZ, hZε⟩ := mem_upperBlocks_iff.mp hZ
  rw [coe_radicalHom, toAdd_ofAdd, hεZ, mul_sub, mul_one, hZε, sub_zero]

/-- The elements `1 + ε Y (1 - ε)` of the radical fix the image of `ε` pointwise. -/
lemma coe_radicalHom_mul_idempotent (hε : IsIdempotentElem ε) (Y : Multiplicative (Matrix n n k)) :
    (radicalHom hε Y : Matrix n n k) * ε = ε := by
  rw [coe_radicalHom, add_mul, one_mul, mul_assoc (ε * Y.toAdd), hε.one_sub_mul_self, mul_zero,
    add_zero]

/-- Over a topological ring, the map `Y ↦ 1 + ε Y (1 - ε)` into `GL n k` is continuous. -/
lemma continuous_radicalHom [TopologicalSpace k] [IsTopologicalRing k] (hε : IsIdempotentElem ε) :
    Continuous (radicalHom hε) := by
  refine Continuous.of_coeHom_comp ?_
  show Continuous fun Y : Multiplicative (Matrix n n k) ↦ 1 + ε * Y.toAdd * (1 - ε)
  exact continuous_const.add ((continuous_const.mul continuous_toAdd).mul continuous_const)

/-- Let `ε g ε = g ε` and let `x - g` be an upper right block (a matrix `Z` with `ε Z = Z` and
`Z ε = 0`). Then `p(x) - p(g)` is an upper right block for every polynomial `p`. -/
lemma aeval_sub_aeval_mem_upperBlocks {g x : Matrix n n k} (hg : ε * (g * ε) = g * ε)
    (hx : x - g ∈ upperBlocks ε) (p : k[X]) : aeval x p - aeval g p ∈ upperBlocks ε := by
  -- `x` and `g` induce the same map on the image of `ε`, and the same map on the quotient by it.
  obtain ⟨hx_range, hx_ker⟩ := mem_upperBlocks_iff.mp hx
  -- By `aeval_semiconj`, `a b = c a` gives `a p(b) = p(c) a`; here `a` is `ε` or `1 - ε`.
  have hx_image : ε * (g * ε) = x * ε := by
    linear_combination (norm := noncomm_ring) hg - hx_ker
  have hg_quot : (1 - ε) * g = (1 - ε) * g * (1 - ε) := by
    linear_combination (norm := noncomm_ring) -hg
  have hx_quot : (1 - ε) * x = (1 - ε) * g * (1 - ε) := by
    linear_combination (norm := noncomm_ring) hg_quot - hx_range
  have h_image : aeval x p * ε = aeval g p * ε :=
    (aeval_semiconj hx_image p).symm.trans (aeval_semiconj hg p)
  have h_quot : (1 - ε) * aeval x p = (1 - ε) * aeval g p :=
    (aeval_semiconj hx_quot p).trans (aeval_semiconj hg_quot p).symm
  refine mem_upperBlocks_iff.mpr ⟨?_, by rw [sub_mul, h_image, sub_self]⟩
  linear_combination (norm := noncomm_ring) -h_quot

/-- If `ε p(g) = p(g)` and `p(g) ε = ε` (that is, `ε` is idempotent and `p(g)` is a projection onto
the image of `ε`), then `ε g ε = g ε` (`g` keeps the image of `ε`). -/
lemma mul_mul_eq_mul_of_aeval {g : Matrix n n k} {p : k[X]} (h_range : ε * aeval g p = aeval g p)
    (h_fix : aeval g p * ε = ε) : ε * (g * ε) = g * ε := by
  have h_comm : g * aeval g p = aeval g p * g := aeval_semiconj rfl p
  have h_eq : g * ε = aeval g p * (g * ε) := by
    rw [← mul_assoc, ← h_comm, mul_assoc, h_fix]
  rw [h_eq, ← mul_assoc, h_range]

/-- Let `p(g)` be a projection onto the image of `ε` (`ε p(g) = p(g)` and `p(g) ε = ε`), and let
`x - g` be an upper right block (a matrix `Z` with `ε Z = Z` and `Z ε = 0`). Then
`D = p(x) - p(g)` satisfies `(1 + D) x = g (1 + D)`. -/
lemma semiconjBy_one_add_aeval_sub {g x : Matrix n n k} {p : k[X]}
    (h_range : ε * aeval g p = aeval g p) (h_fix : aeval g p * ε = ε)
    (hx : x - g ∈ upperBlocks ε) : SemiconjBy (1 + (aeval x p - aeval g p)) x g := by
  obtain ⟨hεD, -⟩ := mem_upperBlocks_iff.mp
    (aeval_sub_aeval_mem_upperBlocks (mul_mul_eq_mul_of_aeval h_range h_fix) hx p)
  obtain ⟨hεZ, -⟩ := mem_upperBlocks_iff.mp hx
  have hg_comm : g * aeval g p = aeval g p * g := aeval_semiconj rfl p
  have hx_comm : x * aeval x p = aeval x p * x := aeval_semiconj rfl p
  -- Write `Z = x - g`, `D = p(x) - p(g)` and `e = p(g)`. The claim is `Z = g D - D x`, and
  -- `g D - D x = e Z - Z (e + D)`, where `Z e = 0`, `Z D = 0` and `e Z = Z`.
  have hZe : (x - g) * aeval g p = 0 := mul_eq_zero_of_mem_upperBlocks hx h_range
  have hZD : (x - g) * (aeval x p - aeval g p) = 0 := mul_eq_zero_of_mem_upperBlocks hx hεD
  have heZ : aeval g p * (x - g) = x - g := by rw [← hεZ, ← mul_assoc, h_fix]
  rw [SemiconjBy]
  linear_combination (norm := noncomm_ring) hg_comm - hx_comm + hZe + hZD - heZ

/-- If `ε g ε = g ε`, then, with `u = radicalHom hε Y` and `u' = radicalHom hε Z`, the difference
`u g u' - g` is an upper right block: it is unchanged by `ε` on the left and killed by `ε` on the
right. -/
lemma radicalHom_mul_mul_sub_mem_upperBlocks (hε : IsIdempotentElem ε) {g : Matrix n n k}
    (hg : ε * (g * ε) = g * ε) (Y Z : Multiplicative (Matrix n n k)) :
    (radicalHom hε Y : Matrix n n k) * g * radicalHom hε Z - g ∈ upperBlocks ε := by
  rw [coe_radicalHom, coe_radicalHom]
  set A : Matrix n n k := ε * Y.toAdd * (1 - ε)
  set B : Matrix n n k := ε * Z.toAdd * (1 - ε)
  have hA : A ∈ upperBlocks ε := mul_mul_one_sub_mem_upperBlocks hε Y.toAdd
  have hgB : g * B ∈ upperBlocks ε :=
    mul_mem_upperBlocks_left hg (mul_mul_one_sub_mem_upperBlocks hε Z.toAdd)
  have h_zero : A * (g * B) = 0 :=
    mul_eq_zero_of_mem_upperBlocks hA (mem_upperBlocks_iff.mp hgB).1
  have h_diff : (1 + A) * g * (1 + B) - g = A * g + g * B := by
    linear_combination (norm := noncomm_ring) h_zero
  rw [h_diff]
  exact add_mem (mul_mem_upperBlocks_right hg hA) hgB

/-- Let `ε` be idempotent, let `p(g)` be a projection onto its image (`ε p(g) = p(g)` and
`p(g) ε = ε`), and let `x = u g u'` with `u, u'` in the image of `radicalHom`, the group of the
matrices `1 + ε Y (1 - ε)`. Then the element of that group with parameter `D = p(x) - p(g)`
conjugates `x` to `g`. -/
lemma semiconjBy_radicalHom_aeval_sub (hε : IsIdempotentElem ε) {g x : GL n k} {p : k[X]}
    (h_range : ε * aeval (g : Matrix n n k) p = aeval (g : Matrix n n k) p)
    (h_fix : aeval (g : Matrix n n k) p * ε = ε)
    (Y Z : Multiplicative (Matrix n n k)) (hx : x = radicalHom hε Y * g * radicalHom hε Z) :
    SemiconjBy (radicalHom hε (ofAdd (aeval (x : Matrix n n k) p - aeval (g : Matrix n n k) p)))
      x g := by
  have hg : ε * ((g : Matrix n n k) * ε) = g * ε := mul_mul_eq_mul_of_aeval h_range h_fix
  have h_mem : (x : Matrix n n k) - g ∈ upperBlocks ε := by
    rw [hx, Units.val_mul, Units.val_mul]
    exact radicalHom_mul_mul_sub_mem_upperBlocks hε hg Y Z
  rw [← SemiconjBy.units_val_iff,
    coe_radicalHom_of_mem hε (aeval_sub_aeval_mem_upperBlocks hg h_mem p)]
  exact semiconjBy_one_add_aeval_sub h_range h_fix h_mem

end New
