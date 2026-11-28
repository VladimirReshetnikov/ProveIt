import Lib.Adelic.Adeles.LocalFactors

/-!
# Tame local characters, integral frames and the local Gauss sum

`F` is a ring satisfying `New.SemilocalField`, modelled on a finite product of non-archimedean local
fields. Its integers are `O`, of volume one, and `ϖ` is a uniformiser. `New.invOnUnits χ` is `χ⁻¹`
on the units of `O` and zero elsewhere. `New.TameLocalChar χ` says that on `O`, `New.invOnUnits χ`
is a primitive character `η` of a finite ring `R` composed with a surjection `π` from `O` onto `R`
with kernel `ϖ O`. The file proves basic facts on such characters, introduces integral frames, and
shows that the Fourier transform of `New.invOnUnits χ` over `O` is γ·χ(ϖ t) when ϖ t is an integral
unit and zero otherwise, for some constant γ with ‖γ‖² = 1 / card R.

The quadratic Gauss sum that gives the product rule of the Weil representation at the finite places
is a different one; it is in `Lib.Weil.Construction.FiniteCocycle`.

## Main definitions and results

* `New.Exchange.IntegralFrame`: an integral basis in three blocks of columns `K, I, L` with its dual
  basis; `New.Exchange.IntegralFrame.blockRelations` lists the relations between the blocks.
* `New.Exchange.exists_local_gauss_sum`: the Fourier transform of the inverse of a tamely ramified
  character χ, cut off to the units, equal to γ·χ(ϖ t) when ϖ t is an integral unit and zero
  otherwise, for some γ with ‖γ‖² = 1 / card R.
* `New.Exchange.IntegralFrame.stdDatum`: the function x ↦ G(x (K I)) on integral matrices x, zero
  elsewhere.

Notions from other files:
* `New.SemilocalField`: Conditions met by a finite product of non-archimedean local fields: a
  locally compact ring with Haar measure, compact open subring O of volume one, a topologically
  nilpotent invertible ϖ in O, and `New.IsValuationPair O`.
* `New.HasIntegralConductor`: The additive character ψ is continuous and has conductor O: ψ is
  trivial on tO exactly when t lies in O.
* `New.IsIntegralUnit` x: x lies in O and has an inverse in O. `New.IsIntMatrix` O M: every entry of
  the matrix M lies in O.

## Relation to the literature

Known result: Gauss sums of a character of the determinant over matrix rings. Only one-dimensional
ramified characters are treated, and the exact value is not computed. For matrices over a finite
ring, the eigen-relation, the vanishing at singular index and the modulus are proved in another file
(`New.Exchange.exists_matrixFourier_eq_mul_inv_det`, used here). This file proves the scalar case
over the integers of a product of local fields, with the modulus. Source: T. Kondo, On Gaussian sums
attached to the general linear groups over finite fields, J. Math. Soc. Japan 15 (1963) 244–255; for
the scalar case over finite rings, E. Lamprecht, Math. Nachr. 9 (1953), see K. Conrad, Gauss and
Jacobi sums on finite fields and Z/mZ, §4; for the local scalar case, Tate's thesis §2.5.

See also `Lib.Weil.MixedModel.ZeroTerm`.
-/

/-! ## First facts on tame local characters -/

namespace New.TameLocalChar

open SemilocalField

variable {F : Type} [SemilocalField F] {χ : MulChar F ℂ} [h : TameLocalChar χ]

/-- For a tame character χ and s in O, the function `invOnUnits χ` (χ⁻¹ on the units of O, zero
elsewhere) is unchanged by adding ϖ s: it is invariant under translation by ϖ O. -/
lemma invOnUnits_uniformizer_mul_add {s : F} (hs : s ∈ O) (x : F) :
    invOnUnits χ ((ϖ : Fˣ) * s + x) = invOnUnits χ x := by
  have h_mem : ((ϖ : Fˣ) : F) * s ∈ O := mul_mem ϖ_mem hs
  by_cases hx : x ∈ O
  · -- On `O` the function factors through the reduction `h.reduction`, which kills `ϖ * s`.
    have h_zero : h.reduction ⟨(ϖ : Fˣ) * s, h_mem⟩ = 0 :=
      (h.reduction_surjective_and_eq_zero_iff.right _).mpr (by simpa using hs)
    have h_factor : ∀ z : O, invOnUnits χ (z : F) = h.resChar (h.reduction z) :=
      h.isPrimitive_resChar_and_invOnUnits_eq.right
    calc
      _ = h.resChar (h.reduction (⟨(ϖ : Fˣ) * s, h_mem⟩ + ⟨x, hx⟩)) :=
        h_factor (⟨(ϖ : Fˣ) * s, h_mem⟩ + ⟨x, hx⟩)
      _ = invOnUnits χ x := by rw [map_add, h_zero, zero_add, ← h_factor]
  · -- Off `O` both sides vanish, since `ϖ * s + x` is not in `O` either.
    simp [invOnUnits, IsIntegralUnit, add_mem_cancel_left h_mem, hx]

/-- A tame character χ has absolute value 1 at every unit t of O. -/
lemma norm_eq_one {t : F} (ht : IsIntegralUnit t) : ‖χ t‖ = 1 := by
  -- `(χ t)⁻¹` is the value of `h.resChar` at a unit of the finite residue ring, so a root of unity.
  have h_inv_eq : (χ t)⁻¹ = h.resChar (h.reduction ⟨t, ht.left⟩) := by
    rw [← h.isPrimitive_resChar_and_invOnUnits_eq.right, invOnUnits, ite_eq_left ht]
  have h_unit : IsUnit (h.reduction ⟨t, ht.left⟩) := .map _ (isIntegralUnit_iff_isUnit.1 ht)
  have h_ord : IsOfFinOrder (χ t)⁻¹ := by
    rw [h_inv_eq]
    exact h.resChar.toMonoidHom.isOfFinOrder h_unit.isOfFinOrder
  simpa using h_ord.norm_eq_one

/-- For a tame character χ, the function `invOnUnits χ` (χ⁻¹ on the units of O, zero elsewhere) is
locally constant. -/
lemma isLocallyConstant_invOnUnits : IsLocallyConstant (invOnUnits χ) := by
  -- The function is unchanged by adding an element of `ϖ * O`, a neighbourhood of zero.
  have h_nhds : {y : F | ((ϖ⁻¹ : Fˣ) : F) * y ∈ O} ∈ nhds 0 :=
    (isOpen_O.preimage_of_continuous (f := fun y ↦ ((ϖ⁻¹ : Fˣ) : F) * y)).mem_nhds (by simp)
  refine isLocallyConstant_of_eventually_add (.mono h_nhds fun y hy x ↦ ?_)
  simpa [add_comm] using h.invOnUnits_uniformizer_mul_add hy x

end New.TameLocalChar

/-! ## Integral frames and the local Gauss sum -/

namespace New.Exchange

open Matrix MeasureTheory SemilocalField Fintype

attribute [local instance low] Fintype.ofFinite

/-- An integral invertible matrix over F cut into column blocks (K I L), with its integral inverse
cut into row blocks `dualK`, `dualI`, `dualL`; the blocks K and L have `p` columns, I has `n`. -/
structure IntegralFrame (F : Type*) [SemilocalField F] (m n p : Type) [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p] where
  /-- The first block of columns of the basis. -/
  K : Matrix m p F
  /-- The last block of columns of the basis. -/
  L : Matrix m p F
  /-- The middle block of columns of the basis. -/
  I : Matrix m n F
  /-- The block of rows of the dual basis that is dual to `K`. -/
  dualK : Matrix p m F
  /-- The block of rows of the dual basis that is dual to `L`. -/
  dualL : Matrix p m F
  /-- The block of rows of the dual basis that is dual to `I`. -/
  dualI : Matrix n m F
  /-- The matrix `P` with column blocks `K, I, L` and the matrix `Q` with row blocks
  `dualK, dualI, dualL` have entries in `O` and are inverse to each other. -/
  isIntMatrix_and_mul_eq_one :
      let P : Matrix m (p ⊕ n ⊕ p) F := fromCols K (fromCols I L)
      let Q : Matrix (p ⊕ n ⊕ p) m F := fromRows dualK (fromRows dualI dualL)
      IsIntMatrix O P ∧ IsIntMatrix O Q ∧ P * Q = 1 ∧ Q * P = 1

-- `Type _` lets each declaration fix the universe of `F`: some need `Type`, others stay general.
variable {F : Type _} [SemilocalField F] {m n p a : Type} [Fintype m] [DecidableEq m] [Fintype n]
  [DecidableEq n] [Fintype p] [DecidableEq p]

omit [DecidableEq n] [Fintype p] [DecidableEq p] in
/-- Selecting rows of `M` and then multiplying by `N` selects the same rows of `M * N`. -/
@[simp] lemma submatrix_id_mul {c : Type*} (f : c → a) (M : Matrix a n F) (N : Matrix n p F) :
    M.submatrix f id * N = (M * N).submatrix f id := rfl

open scoped Classical in
/-- Dividing by `invOnUnits χ x` multiplies by `χ x` if `x` is a unit of `O`; otherwise it is a
division by zero, which gives zero. -/
lemma div_invOnUnits (χ : MulChar F ℂ) (γ : ℂ) (x : F) :
    γ / invOnUnits χ x = if IsIntegralUnit x then γ * χ x else 0 := by
  rw [invOnUnits]
  split_ifs <;> simp

open scoped Classical in
/-- The local Gauss sum. Let `F` be semilocal, with Haar measure giving `O` volume one. Let `χ` be
tame, that is, `χ⁻¹` on the units of `O` is the pullback of a primitive character of the finite
residue ring `R = O / ϖ`, and let `ψ` be a continuous additive character of conductor `O`, so that
`ψ` is trivial on `t O` exactly when `t ∈ O`. Then there is `γ` such that (a)
`‖γ‖ ^ 2 = (card R)⁻¹`, and (b) for every `t`, the integral over `O` of the product of
`invOnUnits χ x` (which is `χ⁻¹` on the units and `0` elsewhere) and `ψ (t x)` equals `γ χ(ϖ t)`
if `ϖ t` is a unit of `O`, and `0` otherwise. -/
lemma exists_local_gauss_sum {χ : MulChar F ℂ} (hχ : TameLocalChar χ) {ψ : AddChar F ℂ}
    (hψ : HasIntegralConductor ψ) :
    ∃ γ : ℂ,
      -- (a) the size of the Gauss sum
      ‖γ‖ ^ 2 = (Nat.card hχ.ResidueRing : ℝ)⁻¹ ∧
      -- (b) the Fourier transform of `invOnUnits χ` on the integers
      ∀ t : F,
        ∫ x : F in (O : Subring F), invOnUnits χ x * ψ (t * x) =
          if IsIntegralUnit ((ϖ : Fˣ) * t) then γ * χ ((ϖ : Fˣ) * t) else 0 := by
  -- Averaging over translates by representatives of `ResidueRing = O / ϖ` turns the integral into
  -- the Gauss sum `Γ` of `resChar` on the finite ring `ResidueRing`, seen as `1 × 1` matrices.
  -- The primitive additive character `φ` of the ring has `φ (reduction x) = ψ (ϖ⁻¹ * x)`.
  obtain ⟨hψ_cont, hψ_cond⟩ := hψ
  obtain ⟨φ, hφ_prim, hφψ⟩ := exists_primitive_residue_addChar
    hχ.reduction_surjective_and_eq_zero_iff hψ_cond
  obtain ⟨h_prim, hη⟩ := hχ.isPrimitive_resChar_and_invOnUnits_eq
  have h_cont : Continuous (invOnUnits χ) := hχ.isLocallyConstant_invOnUnits.continuous
  let S (y : Matrix Unit Unit hχ.ResidueRing) : ℂ := hχ.resChar y.det
  obtain ⟨Γ, h_norm, h_fourier⟩ := exists_matrixFourier_eq_mul_inv_det (a := Unit) hφ_prim h_prim
  have h_twist (y : Matrix Unit Unit hχ.ResidueRing) :
      matrixFourier φ S y = Γ * hχ.resChar⁻¹ y.det * S 1 :=
    h_fourier S (by simp [S, -det_unique]) y
  refine ⟨Γ / card hχ.ResidueRing, by simpa [field] using h_norm, fun t ↦ ?_⟩
  let f (x : F) : ℂ := invOnUnits χ x * ψ (t * x)
  suffices h_div : ∫ x in (O : Subring F), f x =
      Γ / card hχ.ResidueRing / invOnUnits χ ((ϖ : Fˣ) * t) by rw [h_div, div_invOnUnits]
  have h_shift (s : F) (hs : s ∈ O) :
      ∫ x in (O : Subring F), f (s + x) = ∫ x in (O : Subring F), f x :=
    setIntegral_add_left_eq_self_of_mem (M := O.toAddSubgroup) f hs
  by_cases ht : (ϖ : Fˣ) * t ∈ O
  · let rep : hχ.ResidueRing → (O : Subring F) :=
      Function.surjInv hχ.reduction_surjective_and_eq_zero_iff.1
    let u : hχ.ResidueRing := hχ.reduction ⟨(ϖ : Fˣ) * t, ht⟩
    -- on `O`, the function `f` factors through `ResidueRing`
    have h_factor (z : (O : Subring F)) :
        f z = hχ.resChar (hχ.reduction z) * φ (u * hχ.reduction z) := by
      simp [f, u, hη, ← map_mul, hφψ, mul_assoc]
    have h_sum (x : (O : Subring F)) : ∑ r, f (rep r + x) = hχ.resChar⁻¹ u * Γ := by
      -- `r + reduction x` runs over the residue ring, that is, over the `1 × 1` matrices
      calc ∑ r, f (rep r + x) = matrixFourier φ S (u • 1) :=
            sum_equiv (.trans (.addRight (hχ.reduction x)) uniqueEquiv.symm) _ _ fun r ↦ by
              simpa [S, rep, Function.surjInv_eq, trace] using h_factor (rep r + x)
        _ = hχ.resChar⁻¹ u * Γ := by simpa [S, mul_comm] using h_twist (u • 1)
    have h_avg : (∫ x in (O : Subring F), f x) * card hχ.ResidueRing = hχ.resChar⁻¹ u * Γ := by
      calc (∫ x in (O : Subring F), f x) * card hχ.ResidueRing
        _ = ∑ r, ∫ x in (O : Subring F), f (rep r + x) := by simp [h_shift, mul_comm]
        _ = ∫ x in (O : Subring F), ∑ r, f (rep r + x) :=
          (integral_finsetSum _ fun r _ ↦
            ContinuousOn.integrableOn_compact isCompact_O (by fun_prop)).symm
        _ = ∫ _ : F in (O : Subring F), hχ.resChar⁻¹ u * Γ :=
          setIntegral_congr_fun isCompact_O.measurableSet fun x hx ↦ h_sum ⟨x, hx⟩
        _ = hχ.resChar⁻¹ u * Γ := by simp [volume_O, Measure.real]
    simpa [f, u, hη ⟨_, ht⟩, MulChar.inv_apply_eq_inv', field] using h_avg
  · -- translating by `ϖ * s` multiplies the integral by `ψ (ϖ * t * s)`, which is not always `1`
    have h_zero : ∫ x in (O : Subring F), f x = 0 := by
      by_contra h_ne
      refine ht ((hψ_cond _).1 fun s hs ↦ (mul_eq_right₀ h_ne).1 ?_)
      simpa [f, hχ.invOnUnits_uniformizer_mul_add, hs, mul_add, ψ.map_add_eq_mul,
        integral_const_mul,
        mul_left_comm _ (ψ _), mul_left_comm t, mul_assoc] using h_shift _ (O.mul_mem ϖ_mem hs)
    simp [h_zero, invOnUnits, IsIntegralUnit, ht]

/-- The six blocks of an integral frame have entries in `O`, and each block of the dual basis
is a left inverse of its own block of the basis and vanishes on the other two. -/
structure IntegralFrame.BlockRelations (A : IntegralFrame F m n p) : Prop where
  /-- The block `dualL` has entries in `O`. -/
  isIntMatrix_dualL : IsIntMatrix O A.dualL
  /-- The block `dualI` has entries in `O`. -/
  isIntMatrix_dualI : IsIntMatrix O A.dualI
  /-- The block `K` has entries in `O`. -/
  isIntMatrix_K : IsIntMatrix O A.K
  /-- The block `L` has entries in `O`. -/
  isIntMatrix_L : IsIntMatrix O A.L
  /-- The block `dualK` has entries in `O`. -/
  isIntMatrix_dualK : IsIntMatrix O A.dualK
  /-- The block `I` has entries in `O`. -/
  isIntMatrix_I : IsIntMatrix O A.I
  /-- `dualK` is a left inverse of `K`. -/
  dualK_mul_K : A.dualK * A.K = 1
  /-- The rows of `dualI` vanish on the columns of `K`. -/
  dualI_mul_K : A.dualI * A.K = 0
  /-- The rows of `dualL` vanish on the columns of `K`. -/
  dualL_mul_K : A.dualL * A.K = 0
  /-- The rows of `dualK` vanish on the columns of `I`. -/
  dualK_mul_I : A.dualK * A.I = 0
  /-- `dualI` is a left inverse of `I`. -/
  dualI_mul_I : A.dualI * A.I = 1
  /-- The rows of `dualL` vanish on the columns of `I`. -/
  dualL_mul_I : A.dualL * A.I = 0
  /-- The rows of `dualK` vanish on the columns of `L`. -/
  dualK_mul_L : A.dualK * A.L = 0
  /-- The rows of `dualI` vanish on the columns of `L`. -/
  dualI_mul_L : A.dualI * A.L = 0
  /-- `dualL` is a left inverse of `L`. -/
  dualL_mul_L : A.dualL * A.L = 1

/-- The relations `New.Exchange.IntegralFrame.BlockRelations` hold in every integral frame: its six
blocks have entries in `O`, and each block of the dual basis is a left inverse of its own block
of the basis and vanishes on the other two. They are read off block by block from
`A.isIntMatrix_and_mul_eq_one`. -/
lemma IntegralFrame.blockRelations (A : IntegralFrame F m n p) : A.BlockRelations := by
  obtain ⟨hP_int, hQ_int, -, hQP⟩ := A.isIntMatrix_and_mul_eq_one
  -- the nine products are the blocks of `Q * P = 1`
  have h_entry (i j : p ⊕ n ⊕ p) :
      (fromRows A.dualK (fromRows A.dualI A.dualL) * fromCols A.K (fromCols A.I A.L)) i j =
        if i = j then 1 else 0 := by rw [hQP, one_apply]
  exact
    { isIntMatrix_dualL := fun i j ↦ hQ_int (.inr (.inr i)) j
      isIntMatrix_dualI := fun i j ↦ hQ_int (.inr (.inl i)) j
      isIntMatrix_K := fun i j ↦ hP_int i (.inl j)
      isIntMatrix_L := fun i j ↦ hP_int i (.inr (.inr j))
      isIntMatrix_dualK := fun i j ↦ hQ_int (.inl i) j
      isIntMatrix_I := fun i j ↦ hP_int i (.inr (.inl j))
      dualK_mul_K := ext fun i j ↦ by simpa [Matrix.one_apply] using h_entry (.inl i) (.inl j)
      dualI_mul_K := ext fun i j ↦ by simpa using h_entry (.inr (.inl i)) (.inl j)
      dualL_mul_K := ext fun i j ↦ by simpa using h_entry (.inr (.inr i)) (.inl j)
      dualK_mul_I := ext fun i j ↦ by simpa using h_entry (.inl i) (.inr (.inl j))
      dualI_mul_I := ext fun i j ↦ by
           simpa [Matrix.one_apply] using h_entry (.inr (.inl i)) (.inr (.inl j))
      dualL_mul_I := ext fun i j ↦ by simpa using h_entry (.inr (.inr i)) (.inr (.inl j))
      dualK_mul_L := ext fun i j ↦ by simpa using h_entry (.inl i) (.inr (.inr j))
      dualI_mul_L := ext fun i j ↦ by simpa using h_entry (.inr (.inl i)) (.inr (.inr j))
      dualL_mul_L := ext fun i j ↦ by
           simpa [Matrix.one_apply] using h_entry (.inr (.inr i)) (.inr (.inr j)) }

open scoped Classical in
/-- For an integral frame A with blocks K, I, L and a function G on `a × (p ⊕ n)` matrices, the
function of an `a × m` matrix x equal to G(x·(K I)) if x has entries in O and 0 otherwise. -/
noncomputable def IntegralFrame.stdDatum (A : IntegralFrame F m n p) (G : Matrix a (p ⊕ n) F → ℂ)
    (x : Matrix a m F) : ℂ :=
  if IsIntMatrix O x then G (x * A.K.fromCols A.I) else 0

end New.Exchange

/-!
## Multiplicativity of the character cut off to units

`New.invOnUnits_mul`: `New.invOnUnits χ` is multiplicative on `O`, since a product in `O` is a unit
exactly when both factors are.
-/

/-- For x and y in O, `invOnUnits χ (x y) = invOnUnits χ x * invOnUnits χ y`. -/
lemma New.invOnUnits_mul {F : Type} [V : SemilocalField F] {χ : MulChar F ℂ} {x y : F}
    (hx : x ∈ V.O) (hy : y ∈ V.O) :
    invOnUnits χ (x * y) = invOnUnits χ x * invOnUnits χ y := by
  classical
  -- A product in `O` is a unit of `O` exactly when both factors are.
  have h_unit : IsIntegralUnit (x * y) ↔ IsIntegralUnit x ∧ IsIntegralUnit y := by
    simpa [← isIntegralUnit_iff_isUnit] using
      (IsUnit.mul_iff (x := (⟨x, hx⟩ : V.O)) (y := ⟨y, hy⟩))
  simp only [invOnUnits, h_unit, map_mul, mul_inv, ite_zero_mul_ite_zero]
