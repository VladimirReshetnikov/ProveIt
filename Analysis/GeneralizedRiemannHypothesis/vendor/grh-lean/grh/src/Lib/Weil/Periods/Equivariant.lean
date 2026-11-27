import Lib.Adelic.AutomorphicForms.AutomorphicAsAlgebraic
import Lib.Weil.Periods.Grading

/-!
# The character `ψ_U` and the function `𝒲_φ`

Let `Y` be a grading of the hermitian space `V` (`New.Grading`): a splitting of its basis into a
set `X` and a string of `s` vectors. It gives the Bessel group `R = U ⋊ H`
(`New.Grading.besselGroup`). Here `U` (`New.Grading.unipotent`) is the group of points whose matrix
in rational coordinates, minus `1`, raises grades, and `H` is the unitary group of the standard
definite space on `X`, embedded by `New.Grading.inclX`. Write `U^{≥2}` for the points whose matrix
minus `1` raises grades by at least `2`.

This file defines the projection `R → H` (`New.Grading.leviPart`) and the function
`ψ_U (u) = ψ (½ ȷ tr (𝔢 u))` (`New.Grading.unipotentChar`). It shows that `ψ_U` is a character on
`U^{≥2}(𝔸)`, trivial on rational points and invariant under conjugation by `H(𝔸)`. It defines
`ψ_U`-equivariant functions on `[R]` (`New.Grading.IsEquivariant`) and the function `𝒲_φ`
(`New.Grading.sourceFn`) of an algebraic form `φ`. It shows that `𝒲_φ` is `ψ_U`-equivariant when `s`
is odd, since then `U = U^{≥2}`, and that it is the only such function with its values on `H`.

Notions from other files:
* `New.Grading.gradeOf`: the grade of a basis index, `0` on `X` and `s - 1 - 2 i` on the string
  vector `i`.
* `New.HasDegreeGe w' w d x`: the matrix `x` raises grades by at least `d`, that is `x b a = 0`
  whenever `w' b < w a + d`.
* `New.Grading.shift`: the rational endomorphism `𝔢` of `V` that sends each string vector to a
  multiple of the next one and kills `X` and the last string vector.
* `New.algFormCoeff 1 t φ`: the function `h ↦ t (conjWeylRep κ e h_∞⁻¹ (φ h_fin))` on `H(𝔸)` of an
  algebraic form `φ` and a linear functional `t` on its values.

## Relation to the literature

Known; see `Lib.Weil.Periods.Unfolding` for sources.
-/

open MeasureTheory Matrix
noncomputable section
namespace New.Grading
variable {E ι X : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]
  {s : ℕ} {ε : ι → ℤˣ} {N : E} {V : Space E ι ε} (Y : Grading V N X s)

/-! ### The factor in `H` of an element of `R = U ⋊ H` -/

/-- The factor `h ∈ H` of an element `u h` of `R = U ⋊ H`: the continuous homomorphism `R → H`
given by `New.Grading.exists_besselGroup_proj`, a retraction of `New.Grading.inclX` with kernel
`U`. -/
def leviPart : Y.besselGroup →* G E (1 : X → ℤˣ) := Y.exists_besselGroup_proj.choose

@[fun_prop]
lemma continuous_leviPart : Continuous Y.leviPart := by
  obtain ⟨h_cont, -⟩ := Y.exists_besselGroup_proj.choose_spec
  exact h_cont

lemma mul_inv_inclX_leviPart_mem (r : Y.besselGroup) :
    r * (Y.inclX (Y.leviPart r))⁻¹ ∈ Y.unipotent := by
  obtain ⟨-, h_mem, -⟩ := Y.exists_besselGroup_proj.choose_spec
  exact h_mem r

/-- The projection `R → H` is a retraction of the inclusion of `H`. -/
lemma leviPart_inclX (a : G E (1 : X → ℤˣ)) :
    Y.leviPart ⟨Y.inclX a, Y.inclX_mem_besselGroup a⟩ = a := by
  obtain ⟨-, -, h_inclX, -⟩ := Y.exists_besselGroup_proj.choose_spec
  exact h_inclX a

/-- The kernel of the projection `R → H` is `U`. -/
lemma leviPart_eq_one_iff {r : Y.besselGroup} : Y.leviPart r = 1 ↔ (r : G E ε) ∈ Y.unipotent := by
  obtain ⟨-, -, -, h_ker, -⟩ := Y.exists_besselGroup_proj.choose_spec
  exact (h_ker r).symm

/-- The projection `R → H` sends rational points to rational points. -/
lemma leviPart_mem_Gamma {r : Y.besselGroup} (hr : (r : G E ε) ∈ V.Γ) :
    Y.leviPart r ∈ (stdSpace E X).Γ := by
  obtain ⟨-, -, -, -, h_rat⟩ := Y.exists_besselGroup_proj.choose_spec
  exact h_rat r ⟨hr, r.property⟩

/-- For `u ∈ U` and `a ∈ H`, the factor in `H` of `u a` is `a`. -/
lemma leviPart_mul_inclX {u : G E ε} (hu : u ∈ Y.unipotent) (a : G E (1 : X → ℤˣ)) :
    Y.leviPart ⟨u * Y.inclX a,
      mul_mem (Y.unipotent_le_besselGroup hu) (Y.inclX_mem_besselGroup a)⟩ = a := by
  have h_unip : Y.leviPart ⟨u, Y.unipotent_le_besselGroup hu⟩ = 1 := Y.leviPart_eq_one_iff.mpr hu
  calc Y.leviPart (⟨u, Y.unipotent_le_besselGroup hu⟩ * ⟨Y.inclX a, Y.inclX_mem_besselGroup a⟩)
      = Y.leviPart ⟨u, Y.unipotent_le_besselGroup hu⟩ *
          Y.leviPart ⟨Y.inclX a, Y.inclX_mem_besselGroup a⟩ := by rw [map_mul]
    _ = a := by rw [h_unip, leviPart_inclX, one_mul]

omit [Fintype X] in
/-- If `u` lies in `U`, so does its finite part `(1, u_fin)`. -/
lemma mk_one_snd_mem_unipotent {u : G E ε} (hu : u ∈ Y.unipotent) : (1, u.2) ∈ Y.unipotent := by
  refine Y.mem_unipotent.mpr fun i j hij ↦ ?_
  have h_entry : V.ratCoordMatrix u i j = (1 : Matrix ι ι (𝔸 E)) i j :=
    sub_eq_zero.mp (Y.mem_unipotent.mp hu i j hij)
  rw [Matrix.sub_apply, sub_eq_zero, V.ratCoordMatrix_inr, V.ratCoordMatrixFin_snd, map_apply,
    h_entry]
  by_cases h_eq : i = j <;> simp [h_eq, one_apply]

/-- The inclusion of `H` sends the finite part `(1, a_fin)` of `a` to the finite part of the
inclusion of `a`. -/
lemma inclX_mk_one_snd (a : G E (1 : X → ℤˣ)) : Y.inclX (1, a.2) = (1, (Y.inclX a).2) := by
  refine V.isEmbedding_ratCoordMatrix.injective (Matrix.ext fun i j ↦ ?_)
  rw [Y.inclX_inr, V.ratCoordMatrix_inr, V.ratCoordMatrix_inr, ratCoordMatrixFin_inclXFin,
    V.ratCoordMatrixFin_snd, ratCoordMatrix_inclX]
  -- Compare the entries block by block along `Y.indexEquiv`.
  obtain ⟨x | k, rfl⟩ := Y.indexEquiv.surjective i <;>
    obtain ⟨y | l, rfl⟩ := Y.indexEquiv.surjective j <;> simp [one_apply, apply_ite]

/-- The factor in `H` of a real point of `R` (a point with finite part `1`) is a real point. -/
lemma leviPart_snd_eq_one {r : Y.besselGroup} (hr : (r : G E ε).2 = 1) :
    (Y.leviPart r).2 = 1 := by
  -- With `a` the factor in `H`, `(1, (a r⁻¹)_fin)` lies in `U`; since `r_fin = 1` it is
  -- `(1, (inclX a)_fin)`, the inclusion of `(1, a_fin)` (`inclX_mk_one_snd`).
  have h_inv_mem : ((r : G E ε) * (Y.inclX (Y.leviPart r))⁻¹)⁻¹ ∈ Y.unipotent :=
    inv_mem (Y.mul_inv_inclX_leviPart_mem r)
  have h_snd : ((r : G E ε) * (Y.inclX (Y.leviPart r))⁻¹)⁻¹.2 = (Y.inclX (Y.leviPart r)).2 := by
    rw [_root_.mul_inv_rev, inv_inv, Prod.snd_mul, Prod.snd_inv, hr, inv_one, mul_one]
  have h_mem : Y.inclX (1, (Y.leviPart r).2) ∈ Y.unipotent := by
    rw [inclX_mk_one_snd, ← h_snd]
    exact Y.mk_one_snd_mem_unipotent h_inv_mem
  have h_one : Y.leviPart ⟨Y.inclX (1, (Y.leviPart r).2), Y.inclX_mem_besselGroup _⟩ = 1 :=
    Y.leviPart_eq_one_iff.mpr h_mem
  exact congrArg Prod.snd ((Y.leviPart_inclX _).symm.trans h_one)

/-! ### The character `ψ_U` -/

/-- The part of degree `d` of a matrix on the basis of `V`: it keeps the entries `(b, a)` with
`gradeOf b = gradeOf a + d` and replaces the others by `0`. -/
def degreePart (d : ℤ) : Matrix ι ι (𝔸 E) →+ Matrix ι ι (𝔸 E) where
  toFun A := of fun b a ↦ if Y.gradeOf b = Y.gradeOf a + d then A b a else 0
  map_zero' := Matrix.ext fun b a ↦ by simp
  map_add' A B := Matrix.ext fun b a ↦ by
    by_cases h : Y.gradeOf b = Y.gradeOf a + d <;> simp [h]

omit [Fintype X] in
lemma degreePart_apply (d : ℤ) (A : Matrix ι ι (𝔸 E)) (b a : ι) :
    Y.degreePart d A b a = if Y.gradeOf b = Y.gradeOf a + d then A b a else 0 := rfl

omit [Fintype X] in
/-- A matrix that raises grades by at least `d'` has no part of degree `d < d'`. -/
lemma degreePart_eq_zero {d d' : ℤ} {A : Matrix ι ι (𝔸 E)}
    (hA : HasDegreeGe Y.gradeOf Y.gradeOf d' A) (hd : d < d') : Y.degreePart d A = 0 := by
  refine Matrix.ext fun b a ↦ ?_
  rw [degreePart_apply, Matrix.zero_apply, ite_eq_right_iff]
  exact fun h_grade ↦ hA b a (by omega)

omit [Fintype X] in
lemma degreePart_one {d : ℤ} (hd : d ≠ 0) : Y.degreePart d 1 = 0 := by
  refine Matrix.ext fun b a ↦ ?_
  rw [degreePart_apply, Matrix.zero_apply, ite_eq_right_iff]
  exact fun h_grade ↦ one_apply_ne (by rintro rfl; omega)

omit [Fintype X] in
/-- On `U^{≥2}` the part of degree `2` of the matrix in rational coordinates is additive:
`(u u')₂ = u₂ + u'₂`, because `(u - 1) (u' - 1)` raises grades by at least `4`. -/
lemma degreePart_two_ratCoordMatrix_mul {u u' : G E ε}
    (hu : HasDegreeGe Y.gradeOf Y.gradeOf 2 (V.ratCoordMatrix u - 1))
    (hu' : HasDegreeGe Y.gradeOf Y.gradeOf 2 (V.ratCoordMatrix u' - 1)) :
    Y.degreePart 2 (V.ratCoordMatrix (u * u')) =
      Y.degreePart 2 (V.ratCoordMatrix u) + Y.degreePart 2 (V.ratCoordMatrix u') := by
  have h_high : HasDegreeGe Y.gradeOf Y.gradeOf 4
      ((V.ratCoordMatrix u - 1) * (V.ratCoordMatrix u' - 1)) := hu.mul hu' le_rfl
  have h_expand : V.ratCoordMatrix (u * u') =
      (V.ratCoordMatrix u - 1) * (V.ratCoordMatrix u' - 1) +
        (V.ratCoordMatrix u + V.ratCoordMatrix u') - 1 := by
    rw [map_mul]
    noncomm_ring
  rw [h_expand, map_sub, map_add, map_add, Y.degreePart_eq_zero h_high (by norm_num),
    Y.degreePart_one two_ne_zero, zero_add, sub_zero]

omit [Fintype X] in
/-- The shift `𝔢` lowers grades by `2`: its entry `(a, b)` vanishes unless
`gradeOf b = gradeOf a + 2`. -/
lemma shift_apply_eq_zero {a b : ι} (hab : Y.gradeOf b ≠ Y.gradeOf a + 2) : Y.shift a b = 0 := by
  -- The shift vanishes outside the string; on the string its entry `(i, k)` needs `i = k + 1`.
  obtain ⟨x | i, rfl⟩ := Y.indexEquiv.surjective a <;>
    obtain ⟨y | k, rfl⟩ := Y.indexEquiv.surjective b
  · simp [shift]
  · simp [shift]
  · simp [shift]
  · have h_ne : (i : ℕ) ≠ k + 1 := by
      rw [gradeOf_inr, gradeOf_inr] at hab
      omega
    simp [shift, h_ne]

omit [Fintype X] in
/-- Let `𝔢 = Y.shift` be the matrix that kills `X` and the last string vector and sends each string
vector to a multiple of the next one, so that it lowers grades by `2`. Then for every adelic matrix
`A` on the basis of `V`, `tr (𝔢 A) = tr (𝔢 A₂)`, where `A₂ = Y.degreePart 2 A` keeps only the
entries `(b, a)` with `gradeOf b = gradeOf a + 2`. -/
lemma trace_shift_mul (A : Matrix ι ι (𝔸 E)) :
    (Y.shift * A).trace = (Y.shift * Y.degreePart 2 A).trace := by
  simp only [trace, diag_apply, mul_apply]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  by_cases hab : Y.gradeOf b = Y.gradeOf a + 2 <;>
    simp [degreePart_apply, hab, Y.shift_apply_eq_zero]

/-- The matrix in rational coordinates of a point of `H` commutes with the shift `𝔢`. -/
lemma commute_shift_ratCoordMatrix_inclX (a : G E (1 : X → ℤˣ)) :
    Commute Y.shift (V.ratCoordMatrix (Y.inclX a)) := by
  simp [commute_iff_eq, ratCoordMatrix_inclX, shift, ← submatrix_map, fromBlocks_map,
    submatrix_mul_equiv, fromBlocks_multiply]

/-- Conjugation by an element `r` of `R` keeps the property that the matrix of `u`, minus `1`,
raises grades by at least `d`. -/
lemma hasDegreeGe_conj {d : ℤ} {r u : G E ε} (hr : r ∈ Y.besselGroup)
    (hu : HasDegreeGe Y.gradeOf Y.gradeOf d (V.ratCoordMatrix u - 1)) :
    HasDegreeGe Y.gradeOf Y.gradeOf d (V.ratCoordMatrix (r * u * r⁻¹) - 1) := by
  have h_conj : V.ratCoordMatrix (r * u * r⁻¹) - 1 =
      V.ratCoordMatrix r * (V.ratCoordMatrix u - 1) * V.ratCoordMatrix r⁻¹ := by
    rw [mul_sub, sub_mul, mul_one, ← map_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one]
  have h_left :
      HasDegreeGe Y.gradeOf Y.gradeOf d (V.ratCoordMatrix r * (V.ratCoordMatrix u - 1)) :=
    (Y.hasDegreeGe_zero_of_mem_besselGroup hr).mul hu (zero_add d).ge
  rw [h_conj]
  exact h_left.mul (Y.hasDegreeGe_zero_of_mem_besselGroup (inv_mem hr)) (add_zero d).ge

variable [WeilData E]

/-- The function `ψ_U (u) = ψ (½ ȷ tr (𝔢 u))` on `G`, where `ψ` is the standard additive character,
`ȷ` is the element of the Weil data, `𝔢 = Y.shift`, and `u` stands for its matrix in rational
coordinates. -/
def unipotentChar (u : G E ε) : ℂ :=
  stdAddChar E (↑(WeilData.j / 2 : E) * (Y.shift * V.ratCoordMatrix u).trace)

omit [Fintype X] in
@[fun_prop]
lemma continuous_unipotentChar : Continuous Y.unipotentChar := by
  have h_mat : Continuous V.ratCoordMatrix := V.isEmbedding_ratCoordMatrix.continuous
  exact continuous_subtype_val.comp (continuous_stdAddChar.comp (by fun_prop))

omit [Fintype X] in
/-- For a grading `Y` presenting `V` as `X ⊕ J_s`, and Weil data on `E`, consider
`ψ_U (u) = ψ (½ ȷ tr (𝔢 u))` (`Y.unipotentChar`, with `𝔢 = Y.shift` and `u` taken as its matrix in
rational coordinates). This function is multiplicative on elements `u` of `G` for which `u - 1`
raises grades by at least `2`: `ψ_U (u u') = ψ_U (u) ψ_U (u')`. So on `U^{≥2}(𝔸)` the function `ψ_U`
is a character. -/
lemma unipotentChar_mul {u u' : G E ε}
    (hu : HasDegreeGe Y.gradeOf Y.gradeOf 2 (V.ratCoordMatrix u - 1))
    (hu' : HasDegreeGe Y.gradeOf Y.gradeOf 2 (V.ratCoordMatrix u' - 1)) :
    Y.unipotentChar (u * u') = Y.unipotentChar u * Y.unipotentChar u' := by
  have h_trace : (Y.shift * V.ratCoordMatrix (u * u')).trace =
      (Y.shift * V.ratCoordMatrix u).trace + (Y.shift * V.ratCoordMatrix u').trace := by
    rw [trace_shift_mul, Y.degreePart_two_ratCoordMatrix_mul hu hu', mul_add, trace_add,
      ← trace_shift_mul,
      ← trace_shift_mul]
  rw [unipotentChar, h_trace, mul_add, AddChar.map_add_eq_mul, Circle.coe_mul, unipotentChar,
    unipotentChar]

omit [Fintype X] in
/-- For a grading `Y` presenting `V` as `X ⊕ J_s`, and Weil data on `E`, the function
`ψ_U (u) = ψ (½ ȷ tr (𝔢 u))` (`Y.unipotentChar`, with `𝔢 = Y.shift`) equals `1` at every rational
point `u ∈ V.Γ` of `G`, not only on the unipotent part. -/
lemma unipotentChar_of_mem_Gamma {u : G E ε} (hu : u ∈ V.Γ) : Y.unipotentChar u = 1 := by
  choose a ha using (Space.mem_Gamma_iff_ratCoordMatrix.mp hu :
    ∀ i k : ι, ∃ c : E, toAdele c = V.ratCoordMatrix u i k)
  have h_mat : V.ratCoordMatrix u = (of a).map toAdele := Matrix.ext fun i k ↦ (ha i k).symm
  rw [unipotentChar, shift, h_mat, ← Matrix.map_mul, ← AddMonoidHom.map_trace, ← map_mul,
    stdAddChar_toAdele, Circle.coe_one]

/-- The function `ψ_U` is invariant under conjugation by `H(𝔸)`. -/
lemma unipotentChar_conj (a : G E (1 : X → ℤˣ)) (u : G E ε) :
    Y.unipotentChar (Y.inclX a * u * (Y.inclX a)⁻¹) = Y.unipotentChar u := by
  have h_trace : (Y.shift * V.ratCoordMatrix (Y.inclX a * u * (Y.inclX a)⁻¹)).trace =
      (Y.shift * V.ratCoordMatrix u).trace :=
    calc (Y.shift * V.ratCoordMatrix (Y.inclX a * u * (Y.inclX a)⁻¹)).trace
        = (V.ratCoordMatrix (Y.inclX a) *
            (Y.shift * V.ratCoordMatrix u * V.ratCoordMatrix (Y.inclX a)⁻¹)).trace := by
          rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc,
            (Y.commute_shift_ratCoordMatrix_inclX a).eq, mul_assoc, mul_assoc, mul_assoc]
      _ = (Y.shift * V.ratCoordMatrix u).trace := by
          rw [trace_mul_comm, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  rw [unipotentChar, h_trace, unipotentChar]

/-! ### Equivariant functions and the function `𝒲_φ` -/

/-- A function `W` on `R(𝔸)` is `ψ_U`-equivariant if it is continuous, left invariant under `R(F)`
(a function on `[R] = R(F) \ R(𝔸)`), and `W (u r) = ψ_U (u) W (r)` for `u ∈ U^{≥2}(𝔸)`. -/
structure IsEquivariant (W : Y.besselGroup → ℂ) : Prop where
  /-- The function is continuous. -/
  continuous : Continuous W
  /-- The function is left invariant under `R(F)`. -/
  rat_mul : ∀ γ : Y.besselGroup, (γ : G E ε) ∈ V.Γ → ∀ r : Y.besselGroup, W (γ * r) = W r
  /-- The function transforms by `ψ_U` under `U^{≥2}(𝔸)`. -/
  unipotent_mul : ∀ u : Y.besselGroup,
    HasDegreeGe Y.gradeOf Y.gradeOf 2 (V.ratCoordMatrix u - 1) →
      ∀ r : Y.besselGroup, W (u * r) = Y.unipotentChar u * W r

variable {κ : NumberField.InfinitePlace E → ℕ → ℕ} {e : NumberField.InfinitePlace E → ℤ}
  (t : (WeylIndex X κ → ℂ) →ₗ[ℂ] ℂ) (φ : AlgForm (E := E) X κ e)

/-- The function `𝒲_φ (u h) = ψ_U (u) (φ (h_fin), π_X (h_∞) v_*)` on `R(𝔸)`. The vector `v_*` enters
through the linear form `t = (·, v_*)`. The values of `φ` transform under `ȟ = ᵗh⁻¹`
(`conjWeylRep`), and `(ȟ ζ, π_X (h) v) = (ζ, v)`, so the second factor is `t (ȟ_∞⁻¹ φ (h_fin))`,
which is `algFormCoeff 1 t φ h`. -/
def sourceFn (t : (WeylIndex X κ → ℂ) →ₗ[ℂ] ℂ) (φ : AlgForm (E := E) X κ e)
    (r : Y.besselGroup) : ℂ :=
  Y.unipotentChar (r * (Y.inclX (Y.leviPart r))⁻¹) * algFormCoeff 1 t φ (Y.leviPart r)

/-- Let `u` lie in the unipotent subgroup `U = Y.unipotent`, and let `a` lie in `H`, the adelic
unitary group of the standard definite space on `X`, embedded by `inclX`. Then the source function
`𝒲_φ = Y.sourceFn t φ` of the algebraic form `φ` satisfies
`𝒲_φ (u a) = ψ_U (u) · algFormCoeff 1 t φ a`, where `ψ_U = Y.unipotentChar` and the second factor is
`t (ρ(a_∞⁻¹) φ(a_fin))` with `ρ = conjWeylRep`. For `t = (·, v_*)` this is the formula
`𝒲_φ (u a) = ψ_U (u) (φ (a_fin), π_X (a_∞) v_*)`. -/
lemma sourceFn_mul {u : G E ε} (hu : u ∈ Y.unipotent) (a : G E (1 : X → ℤˣ)) :
    Y.sourceFn t φ ⟨u * Y.inclX a,
        mul_mem (Y.unipotent_le_besselGroup hu) (Y.inclX_mem_besselGroup a)⟩ =
      Y.unipotentChar u * algFormCoeff 1 t φ a := by
  rw [sourceFn, Y.leviPart_mul_inclX hu a, mul_inv_cancel_right]

/-- This is the case `t = gramForm v` of `New.Grading.sourceFn_mul`, where `v` stands for the
complex conjugate of `v_*` and `gramForm` is the Gram pairing `(ξ, η) ↦ ξ* G η`. Let `u` lie in the
unipotent subgroup `Y.unipotent`, and let `a` lie in the adelic unitary group of the standard
definite space on `X`, embedded by `inclX`. Then the source function of the algebraic form `φ`
satisfies `Y.sourceFn (gramForm v) φ (u a) = ψ_U (u) · gramForm (conjWeylRep κ e a.1 v) (φ.1 a.2)`,
where `a.1` is the infinite (real) part of `a` and `a.2` is its finite part. -/
lemma sourceFn_gramForm_mul_inclX (v : WeylIndex X κ → ℂ) {u : G E ε} (hu : u ∈ Y.unipotent)
    (a : G E (1 : X → ℤˣ)) :
    Y.sourceFn (gramForm v) φ ⟨u * Y.inclX a,
        mul_mem (Y.unipotent_le_besselGroup hu) (Y.inclX_mem_besselGroup a)⟩ =
      Y.unipotentChar u * gramForm (conjWeylRep κ e a.1 v) (φ.1 a.2) := by
  have h_invariant : gramForm (conjWeylRep κ e a.1 v) (φ.1 a.2) =
      gramForm v (conjWeylRep κ e a.1⁻¹ (φ.1 a.2)) := by
    -- `conjWeylRep κ e a.1` preserves the Gram product and undoes `conjWeylRep κ e a.1⁻¹`.
    rw [← gramForm_conjWeylRep (e := e) a.1 v, Representation.self_inv_apply]
  rw [Y.sourceFn_mul (gramForm v) φ hu, algFormCoeff_apply, h_invariant]

/-- On `H`, the function `𝒲_φ` is the coefficient function `algFormCoeff 1 t φ` of `φ`. -/
lemma sourceFn_inclX (a : G E (1 : X → ℤˣ)) :
    Y.sourceFn t φ ⟨Y.inclX a, Y.inclX_mem_besselGroup a⟩ = algFormCoeff 1 t φ a := by
  rw [sourceFn, leviPart_inclX, mul_inv_cancel, Y.unipotentChar_of_mem_Gamma (one_mem _), one_mul]

omit [WeilData E] in
/-- The algebraic form `algFormRep κ e a φ` is the right translate `g ↦ φ (g a)`. -/
private lemma algFormRep_apply (a g : Gf E X) (φ : AlgForm (E := E) X κ e) :
    (algFormRep κ e a φ : Gf E X → WeylIndex X κ → ℂ) g =
      (φ : Gf E X → WeylIndex X κ → ℂ) (g * a) := rfl

/-- Right translation of `𝒲_φ` by a finite point of `H` is right translation of `φ`. -/
lemma sourceFn_mul_inclX (r : Y.besselGroup) (a : Gf E X) :
    Y.sourceFn t φ (r * ⟨Y.inclX (1, a), Y.inclX_mem_besselGroup (1, a)⟩) =
      Y.sourceFn t (algFormRep κ e a φ) r := by
  rw [sourceFn, sourceFn, map_mul, leviPart_inclX, map_mul, Subgroup.coe_mul, _root_.mul_inv_rev,
    mul_assoc, mul_inv_cancel_left, algFormCoeff_apply, algFormCoeff_apply, Prod.fst_mul, mul_one,
    Prod.snd_mul, algFormRep_apply]

lemma sourceFn_add (ψ : AlgForm (E := E) X κ e) (r : Y.besselGroup) :
    Y.sourceFn t (φ + ψ) r = Y.sourceFn t φ r + Y.sourceFn t ψ r := by
  rw [sourceFn, map_add, Pi.add_apply, mul_add, sourceFn, sourceFn]

lemma sourceFn_smul (c : ℂ) (r : Y.besselGroup) :
    Y.sourceFn t (c • φ) r = c * Y.sourceFn t φ r := by
  rw [sourceFn, map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm, sourceFn]

lemma sourceFn_smul_left (c : ℂ) (r : Y.besselGroup) :
    Y.sourceFn (c • t) φ r = c * Y.sourceFn t φ r := by
  rw [sourceFn, sourceFn, algFormCoeff_apply, algFormCoeff_apply, LinearMap.smul_apply, smul_eq_mul,
    mul_left_comm]

/-- If `X^⊥` (the string) has odd rank `s`, so that `U = U^{≥2}`, then `𝒲_φ = Y.sourceFn t φ` is a
`ψ_U`-equivariant function on `[R]`. Here `𝒲_φ (u h) = ψ_U (u) (φ (h_fin), π_X (h_∞) v_*)`, with
`t = (·, v_*)`. Equivariant means continuous, left `R(F)`-invariant, and
`𝒲_φ (u r) = ψ_U (u) 𝒲_φ (r)` for `u ∈ U^{≥2}(𝔸)`. -/
lemma isEquivariant_sourceFn (hs : Odd s) (t : (WeylIndex X κ → ℂ) →ₗ[ℂ] ℂ)
    (φ : AlgForm (E := E) X κ e) : Y.IsEquivariant (Y.sourceFn t φ) := by
  have h_aut : (stdSpace E X).IsAutomorphic (algFormCoeff 1 t φ) :=
    Space.isAutomorphic_algFormCoeff φ
  have h_deg (r : Y.besselGroup) : HasDegreeGe Y.gradeOf Y.gradeOf 2
      (V.ratCoordMatrix (r * (Y.inclX (Y.leviPart r))⁻¹) - 1) :=
    Y.hasDegreeGe_two_of_odd hs (Y.mul_inv_inclX_leviPart_mem r)
  -- Write `r = u a` with `u` in `U = U^{≥2}` and `a` in `H`. Then `𝒲_φ` is continuous, the factor
  -- `ψ_U (u)` is multiplicative in `r`, and rational points act trivially on both factors.
  have h_mul (p r : Y.besselGroup) :
      Y.unipotentChar (↑(p * r) * (Y.inclX (Y.leviPart (p * r)))⁻¹) =
        Y.unipotentChar (p * (Y.inclX (Y.leviPart p))⁻¹) *
          Y.unipotentChar (r * (Y.inclX (Y.leviPart r))⁻¹) := by
    -- The factor in `U` of `p r` is that of `p` times a conjugate under `H` of that of `r`.
    have h_factor : (↑(p * r) : G E ε) * (Y.inclX (Y.leviPart (p * r)))⁻¹ =
        ((p : G E ε) * (Y.inclX (Y.leviPart p))⁻¹) *
          (Y.inclX (Y.leviPart p) * ((r : G E ε) * (Y.inclX (Y.leviPart r))⁻¹) *
            (Y.inclX (Y.leviPart p))⁻¹) := by
      rw [map_mul, map_mul, Subgroup.coe_mul]
      group
    rw [h_factor, Y.unipotentChar_mul (h_deg p)
      (Y.hasDegreeGe_conj (Y.inclX_mem_besselGroup _) (h_deg r)), Y.unipotentChar_conj]
  refine { continuous := ?_, rat_mul := fun γ hγ r ↦ ?_, unipotent_mul := fun u hu r ↦ ?_ }
  · have h_cont : Continuous (algFormCoeff 1 t φ) := h_aut.continuous
    unfold sourceFn
    fun_prop
  · have h_levi : Y.leviPart γ ∈ (stdSpace E X).Γ := Y.leviPart_mem_Gamma hγ
    obtain ⟨h_inclX_rat, -⟩ := Y.inclX_mem_ratBessel h_levi
    rw [sourceFn, h_mul, Y.unipotentChar_of_mem_Gamma (mul_mem hγ (inv_mem h_inclX_rat)), one_mul,
      map_mul, h_aut.rat_mul _ h_levi, sourceFn]
  · have h_levi : Y.leviPart u = 1 :=
      Y.leviPart_eq_one_iff.mpr (Y.mem_unipotent.mpr fun b a h_lt ↦ hu b a (by omega))
    rw [sourceFn, h_mul, map_mul, h_levi, map_one, inv_one, mul_one, one_mul, mul_assoc, sourceFn]

variable {Y t φ} in
/-- Let the grading `Y` of `V` have a string of odd length `s`, so that `U = U^{≥2}`. A
`ψ_U`-equivariant function `W` on `R(𝔸)` that agrees on `H` with `algFormCoeff 1 t φ`, the values
of `𝒲_φ` there, is `𝒲_φ`. -/
lemma IsEquivariant.eq_sourceFn {W : Y.besselGroup → ℂ} (hW : Y.IsEquivariant W) (hs : Odd s)
    (h_levi : ∀ a : G E (1 : X → ℤˣ),
      W ⟨Y.inclX a, Y.inclX_mem_besselGroup a⟩ = algFormCoeff 1 t φ a) :
    W = Y.sourceFn t φ := by
  funext ⟨r, hr⟩
  -- Write `r = u a` with `u` in `U` and `a` in `H`.
  obtain ⟨u, hu, a, rfl⟩ : ∃ u ∈ Y.unipotent, ∃ a : G E (1 : X → ℤˣ), r = u * Y.inclX a :=
    Y.exists_unipotent_mul_inclX hr
  rw [Y.sourceFn_mul t φ hu, ← h_levi]
  exact hW.unipotent_mul ⟨u, Y.unipotent_le_besselGroup hu⟩ (Y.hasDegreeGe_two_of_odd hs hu)
    ⟨Y.inclX a, Y.inclX_mem_besselGroup a⟩

/-- The group `R(F_∞)` of real points of `R`. -/
def besselReal : Subgroup (GInf E ε) := Y.besselGroup.comap (MonoidHom.inl (GInf E ε) (Gf E ι))

/-- The group `R(F_∞)` of real points of `R` is closed. -/
instance : IsClosed (Y.besselReal : Set (GInf E ε)) :=
  (inferInstance : IsClosed (Y.besselGroup : Set (G E ε))).preimage (Continuous.prodMk_left 1)

end New.Grading

end
