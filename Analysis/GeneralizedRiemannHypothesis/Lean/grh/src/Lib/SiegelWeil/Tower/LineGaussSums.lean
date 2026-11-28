import Lib.ClassField.HeckeCharacter.TameModulus
import Lib.SiegelWeil.SingularForms.UnimodularCoefficients
import Lib.Weil.MixedModel.Slices

/-!
# Standard partners, shear invariance, Gauss sums along lines and coefficients of lifts

Let `s` be an integral `b × n` matrix over a semilocal field (`New.SemilocalField`) with compact
open subring `O`, and let `χ` be a character; where `χ` is tame (`TameLocalChar`), `invOnUnits χ` is
locally constant and `χ` has absolute value one on units of `O`. The file constructs the standard
pair of partners attached to `s`. Finally it describes the Fourier coefficients `H.centreCoeff T`
along a splitting `H` of a hermitian space `X` of an equivariant lift `𝒟`
(`New.Exchange.IsEquivariantLift`) on a space `M` of local data.

## Main definitions and results

* `New.stdColDatum`: `y ↦ χ⁻¹ (det (s y))` for integral `y` with `det (s y)` a unit of `O`, else
  zero.
* `New.stdRowDatum`: `x ↦ χ⁻¹ (det (s; x))` if `s` stacked on `x` lies in `GL_n(O)`, else zero.
* `New.areMatched_stdRowDatum_stdColDatum`: these two are partners (`New.AreMatched`): they are
  carried by the blocks of rows of `k⁻¹` and of columns of `k`, for `k ∈ GL_n(O)`, and their values
  there differ by the factor `χ (det k)`.
* `New.Exchange.map_shear_stdColDatum_eq`: if a linear form is invariant, on a space `M` of
  Schwartz–Bruhat functions, under the shears `y ↦ y + u z s y`, then it takes the same value on the
  standard datum `New.stdColDatum χ s` and on its composite with `y ↦ y + u r y`, when both lie in
  `M`, `s` is integral, `s u = 0` and `r u = 0`.
* `New.Exchange.exists_lineTerm_localDatum`: the operator `New.Exchange.lineTerm`, the term along a
  line split off each of two hermitian spaces, sends a standard datum for the large pair of spaces
  to a scalar times a standard datum for the small pair. The scalar at the adele `x` depends on
  `a = x κ⁻¹`, where κ is a fixed idele. It is zero unless `a` is integral outside `S ∪ S̄` and both
  `a` and `ϖ ā` are units of `O` at the set `S` of places where `χ` is read. Then it is
  `l β * γ * χ⁻¹(a) * χ(ϖ ā)`, where `l β` is a nonzero constant for each of the two terms `β` and
  `|γ|²` is the inverse of the order of the residue ring.
* `New.Exchange.IsEquivariantLift.exists_linear_centreCoeff`: the coefficient at a point is a linear
  functional of the datum. A shear of the datum by `z` along the centre of the radical multiplies it
  by the additive character at `S` of `tr (T_S z)`, where `T_S` is the component at `S` of the
  product of `T` with the inverse of the idele `invDifferentIdele E`.

Notions from other files:
* `New.SemilocalField`: Conditions met by a finite product of non-archimedean local fields: a
  locally compact ring with Haar measure, compact open subring O of volume one, a topologically
  nilpotent invertible ϖ in O, and `New.IsValuationPair O`.
* `New.schwartzBruhat`: The space of locally constant, compactly supported complex functions that
  vanish outside a given set.
* `New.invOnUnits`: `χ⁻¹` on the units of `O`, zero elsewhere.
* `New.Space.Splitting.centreCoeff`: `H.centreCoeff T D g` is the mean of
  `ψ (tr (T M)) * D (H.radicalCentre M * g)` over adelic matrices `M` modulo rational ones;
  `H.radicalCentre M` has matrix `1 + H.kAdelic * (M - Mᴴ) * H.lCoord`.
* `New.Exchange.SplitTameChar`: A character ν of the idele classes of norm one with positive weight
  at every infinite place, whose tame part is non-trivial exactly on a non-empty finite set S of
  places disjoint from its conjugate.

## Relation to the literature

Known; see `Lib.SiegelWeil.Tower.LargeSideConstantTerm` and
`Lib.SiegelWeil.SingularForms.UnimodularCoefficients` for sources.
-/

noncomputable section

/-! ## The standard pair of partners attached to an integral matrix -/

namespace New

open Matrix SemilocalField schwartzBruhat

variable {F : Type _} [SemilocalField F] {a b n : Type} [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] (e : b ⊕ a ≃ n) (χ : MulChar F ℂ) (s : Matrix b n F)

/-! ### The standard functions -/

open scoped Classical in
/-- For a matrix `s` with rows indexed by `b`, the function sending an integral `y` with `det (s y)`
a unit of `O` to `χ⁻¹ (det (s y))`, and every other `y` to zero. -/
def stdColDatum (y : Matrix n b F) : ℂ := if IsIntMatrix O y then invOnUnits χ (s * y).det else 0

/-- The function sending `x` to `χ⁻¹` of the determinant of the square matrix with rows those of
`s` and `x`, ordered by `e`, if that matrix lies in `GL_n(O)`, and to zero otherwise. -/
def stdRowDatum (x : Matrix a n F) : ℂ := stdColDatum χ 1 ((s.fromRows x).submatrix e.symm id)

/-- A square matrix over `F` is primitive over the compact open subring `O = SemilocalField.O` of
`F` (integral, with an integral left inverse) if and only if it is integral and its determinant is a
unit of `O`. -/
lemma isPrimitiveMatrix_iff_int_and_unit_det {A : Matrix n n F} :
    IsPrimitiveMatrix O A ↔ IsIntMatrix O A ∧ IsIntegralUnit A.det :=
  -- The determinant of an integral left inverse inverts `A.det`; conversely, if `c * A.det = 1`,
  -- then `c` times the adjugate is an integral left inverse.
  ⟨fun ⟨hA, L, hL, h⟩ ↦ ⟨hA, hA.det_mem, L.det, hL.det_mem, by simp [← det_mul, h]⟩,
    fun ⟨hA, _, c, hc, h⟩ ↦
      ⟨hA, c • A.adjugate, hA.adjugate.smul hc, by simp [adjugate_mul, smul_smul, h]⟩⟩

variable {χ : MulChar F ℂ} {s : Matrix b n F} {Ψ : Matrix n b F → ℂ}

omit [Fintype b] [DecidableEq n] in
/-- If `Ψ` is locally constant with compact support in the matrices with a left inverse, then
`y ↦ Ψ yᵀ` is locally constant with compact support in the matrices with a right inverse. -/
lemma _root_.Membership.mem.transpose_mem_schwartzBruhat (h : Ψ ∈ schwartzBruhat HasLeftInv) :
    (fun y : Matrix b n F ↦ Ψ yᵀ) ∈ schwartzBruhat fun x : Matrix b n F ↦ HasLeftInv xᵀ :=
  schwartzBruhat.comp h transpose transpose_transpose fun _ hx ↦ hx

omit [DecidableEq n] in
/-- A locally constant function that vanishes off the primitive matrices has compact support and
vanishes off the matrices with a left inverse. -/
lemma schwartzBruhat.mem_of_support_isPrimitiveMatrix (h : IsLocallyConstant Ψ)
    (hs : ∀ y : Matrix n b F, Ψ y ≠ 0 → IsPrimitiveMatrix O y) :
    Ψ ∈ schwartzBruhat HasLeftInv := by
  refine ⟨h, isCompact_O.matrix.closure_of_subset fun y hy ↦ (hs y hy).1, fun y hy ↦ ?_⟩
  obtain ⟨-, L, -, hL⟩ := hs y hy
  exact ⟨L, hL⟩

/-! ### Supports, and the identity of partners -/

/-- If `t` is a unit of `O`, then `invOnUnits χ x = χ t * invOnUnits χ (x * t)`: the element `x` is
a unit of `O` if and only if `x * t` is one. -/
lemma invOnUnits_eq_mul_of_unit {t x : F} (h : IsIntegralUnit t) :
    invOnUnits χ x = χ t * invOnUnits χ (x * t) := by
  obtain ⟨ht, c, hc, hct⟩ := h
  have h_iff : IsIntegralUnit (x * t) ↔ IsIntegralUnit x := by
    -- If `w` inverts `x * t`, then `w * t` inverts `x`; if `w` inverts `x`, then `w * c` inverts
    -- `x * t`.
    refine ⟨fun ⟨hxt, w, hw, hwx⟩ ↦ ⟨?_, w * t, mul_mem hw ht, by grind⟩,
      fun ⟨hx, w, hw, hwx⟩ ↦ ⟨mul_mem hx ht, w * c, mul_mem hw hc, by grind⟩⟩
    have hx_eq : x * t * c = x := by grind
    simpa [hx_eq] using mul_mem hxt hc
  have hχt : χ t ≠ 0 := ((IsUnit.of_mul_eq_one_right c hct).map χ).ne_zero
  by_cases hx : IsIntegralUnit x <;> simp [invOnUnits, h_iff, hx, hχt]

omit [DecidableEq n] in
/-- If the standard datum of an integral `s` does not vanish at `y`, then `y` is integral and
`s * y` is primitive: integral, with an integral inverse. -/
lemma isIntMatrix_of_stdColDatum_ne_zero (hs : IsIntMatrix O s) {y : Matrix n b F}
    (hy : stdColDatum χ s y ≠ 0) :
    IsIntMatrix O y ∧ IsPrimitiveMatrix O (s * y) := by
  obtain ⟨y_int, det_unit⟩ : IsIntMatrix O y ∧ IsIntegralUnit (s * y).det := by
    grind [stdColDatum, invOnUnits]
  exact ⟨y_int, isPrimitiveMatrix_iff_int_and_unit_det.2 ⟨hs.mul y_int, det_unit⟩⟩

omit [DecidableEq n] in
/-- The standard datum of an integral `s` vanishes off the primitive matrices. -/
lemma isPrimitiveMatrix_of_stdColDatum_ne_zero (hs : IsIntMatrix O s) (y : Matrix n b F)
    (hy : stdColDatum χ s y ≠ 0) :
    IsPrimitiveMatrix O y := by
  obtain ⟨y_int, -, L, L_int, hL⟩ := isIntMatrix_of_stdColDatum_ne_zero hs hy
  -- `L` is an integral left inverse of `s * y`, so `L * s` is one of `y`.
  exact ⟨y_int, L * s, L_int.mul hs, by rwa [L.mul_assoc]⟩

/-- For integral `s`, the row datum `stdRowDatum e χ s` and the column datum `stdColDatum χ s` are
partners for `χ` over `O`. The row datum sends `x` to `χ⁻¹ (det (s; x))` (rows ordered by `e`) if
`(s; x)` lies in `GL_n(O)`, and to `0` otherwise. The column datum sends an integral `y` with
`det (s y)` a unit to `χ⁻¹ (det (s y))`, and every other `y` to `0`. Being partners means: they
vanish off the last rows `a` of `k⁻¹`, resp. the first columns `b` of `k`, for `k ∈ GL_n(O)`, and
the first at `invLastRows e k` is `χ (det k)` times the second at `firstCols e k`. -/
lemma areMatched_stdRowDatum_stdColDatum [Fintype a] (hs : IsIntMatrix O s) :
    AreMatched O e χ (stdRowDatum e χ s) (stdColDatum χ s) := by
  classical
  refine ⟨fun x (hx : stdColDatum χ 1 ((s.fromRows x).submatrix e.symm id) ≠ 0) ↦ ?_,
    fun y hy ↦ ?_, fun k hk ↦ ?_⟩
  · -- The matrix with rows `s` and `x` is some `g` in `intGL n O`; take `k = g⁻¹`.
    obtain ⟨g, hg, g_eq : g.val = 1 * (s.fromRows x).submatrix e.symm id⟩ :=
      isPrimitiveMatrix_iff.1 (isIntMatrix_of_stdColDatum_ne_zero .one hx).2
    exact ⟨g⁻¹, inv_mem hg, by ext; simp [g_eq]⟩
  · -- A primitive matrix is a block of columns of an element of `GL_n(O)`.
    exact (isValuationPair.exists_firstCols_iff e).2
      (isPrimitiveMatrix_of_stdColDatum_ne_zero hs y hy)
  · -- Let `A` have rows `s` and `invLastRows e k`. It is integral, and
    -- `A.det * k.det = (s * firstCols e k).det` with `k.det` a unit of `O`.
    let A : Matrix n n F := (s.fromRows (invLastRows e k)).submatrix e.symm id
    obtain ⟨k_int, -⟩ := mem_intGL.1 hk
    have A_int : IsIntMatrix O A := by simp_all [A, IsIntMatrix, reindex_equiv e, mem_intGL]
    have y_int : IsIntMatrix O (firstCols e k) := fun i j ↦ k_int i _
    have k_det : IsIntegralUnit k.val.det :=
      (isPrimitiveMatrix_iff_int_and_unit_det.1 ((isPrimitiveMatrix_iff_mem_intGL k).2 hk)).2
    calc stdRowDatum e χ s (invLastRows e k)
      _ = invOnUnits χ A.det := by simp [stdRowDatum, stdColDatum, A, A_int]
      _ = χ k.val.det * invOnUnits χ (A.det * k.val.det) := invOnUnits_eq_mul_of_unit k_det
      _ = χ k.val.det * stdColDatum χ s (firstCols e k) := by
        rw [det_fromRows_invLastRows, stdColDatum, ite_eq_left y_int]

variable (χ) [hχ : TameLocalChar χ]

/-! ### The tame case: local constancy and compact support -/

omit [DecidableEq n] in
/-- For tame `χ` and integral `s`, the standard datum `y ↦ χ⁻¹ (det (s y))` is locally constant with
compact support in the matrices that have a left inverse: it is a locally constant function cut off
by the clopen set of integral matrices, and it vanishes off the primitive ones. -/
lemma stdColDatum_mem_schwartzBruhat (hs : IsIntMatrix O s) :
    stdColDatum χ s ∈ schwartzBruhat HasLeftInv := by
  have h_loc : IsLocallyConstant fun y : Matrix n b F ↦ invOnUnits χ (s * y).det :=
    hχ.isLocallyConstant_invOnUnits.comp_continuous (by fun_prop)
  have h_clopen : IsClopen {y : Matrix n b F | IsIntMatrix O y} :=
    ⟨isCompact_O.matrix.isClosed, isOpen_O.matrix⟩
  exact mem_of_support_isPrimitiveMatrix (LocallyConstant.indicator ⟨_, h_loc⟩
    h_clopen).isLocallyConstant
    (isPrimitiveMatrix_of_stdColDatum_ne_zero hs)

omit [Fintype b] [DecidableEq b] in
/-- For tame χ, the datum `stdRowDatum e χ s`, that is `x ↦ χ⁻¹ (det (s; x))`, is locally constant
with compact support in the matrices that have a right inverse. -/
lemma stdRowDatum_mem [DecidableEq a] :
    stdRowDatum e χ s ∈ schwartzBruhat fun x : Matrix a n F ↦ HasLeftInv xᵀ := by
  -- `stdRowDatum e χ s` is `stdColDatum χ 1` composed with the map that stacks `x` under `s`;
  -- this map is continuous, and taking the rows `a` is a left inverse of it.
  let rows (M : Matrix n n F) : Matrix a n F := M.submatrix (e ∘ .inr) id
  -- Rows of an invertible matrix have a right inverse.
  have rows_full : Set.MapsTo rows HasLeftInv fun x ↦ HasLeftInv xᵀ := fun M ⟨L, hL⟩ ↦
    hasLeftInv_invLastRows_transpose e (.mkOfMulEqOne L M hL)
  have stack_cont : Continuous fun x : Matrix a n F ↦ (s.fromRows x).submatrix e.symm id := by
    refine (continuous_matrix fun i j ↦ ?_).matrix_submatrix _ _
    cases i <;> simp only [fromRows_apply_inl, fromRows_apply_inr] <;> fun_prop
  exact comp (stdColDatum_mem_schwartzBruhat χ .one) rows
    (fun x ↦ by ext; simp [rows]) rows_full stack_cont

end New

/-! ## Shear invariance of linear forms on the standard datum -/

section ShearInvariance

open MeasureTheory New SemilocalField

/-- Let `F` be a semilocal field with integer ring `O`, and `χ` a multiplicative character of `F`.
Let `s` be a `b × n` matrix over `O`, and `u` a column and `r` a row with `s u = 0` and `r u = 0`.
`stdColDatum χ s` sends an integral `y` with `det (s y)` a unit of `O` to `χ⁻¹ (det (s y))`, and
every other `y` to `0`. Suppose the linear form `Λ` is invariant under all shears `y ↦ y + u z s y`
on a space `M` of locally constant, compactly supported functions vanishing outside `U`. Then `Λ`
takes the same value on `stdColDatum χ s` and on its composite with `y ↦ y + u r y`, when both lie
in `M`. -/
lemma New.Exchange.map_shear_stdColDatum_eq {F b n : Type} [V : SemilocalField F] [Fintype b]
    [DecidableEq b]
    [Fintype n] {χ : MulChar F ℂ} {M : Submodule ℂ (Matrix n b F → ℂ)} {U : Set (Matrix n b F)}
    {s : Matrix b n F} (hs : IsIntMatrix O s) {u : Matrix n Unit F} {r : Matrix Unit n F}
    (hsu : s * u = 0) (hru : r * u = 0) {Λ : (Matrix n b F → ℂ) →ₗ[ℂ] ℂ} (hM : M ≤ schwartzBruhat U)
    (hΛ : ∀ Ψ ∈ M, ∀ z : Matrix Unit b F,
      Λ (fun y : Matrix n b F ↦ Ψ (y + u * (z * (s * y)))) = Λ Ψ)
    (h_std : stdColDatum χ s ∈ M)
    (h_shear : (fun y : Matrix n b F ↦ stdColDatum χ s (y + u * (r * y))) ∈ M) :
    Λ (fun y : Matrix n b F ↦ stdColDatum χ s (y + u * (r * y))) = Λ (stdColDatum χ s) := by
  classical
  -- Average over the shears `τ t`, for `t` an integral matrix. This does not change `Λ`, and the
  -- two functions have the same average.
  let Ψ (y : Matrix n b F) : ℂ := stdColDatum χ s (y + u * (r * y))
  let S : AddSubgroup (Matrix n b F) := V.O.toAddSubgroup.matrix
  have : CompactSpace S := isCompact_iff_compactSpace.1 isCompact_O.matrix
  let τ (t : S) (y : Matrix n b F) : Matrix n b F := y + u * (r * t.1 * (s * y))
  let mean (Φ : Matrix n b F → ℂ) (y : Matrix n b F) : ℂ := ⨍ t, Φ (τ t y) ∂.addHaar
  have h_mean {Φ : Matrix n b F → ℂ} (hΦ : Φ ∈ M) : Λ (mean Φ) = Λ Φ := by
    have h_loc : IsLocallyConstant fun (t : S) (y : Matrix n b F) ↦ Φ (τ t y) :=
      schwartzBruhat.isLocallyConstant_curry (hM hΦ) τ (fun t ↦ τ (-t))
        fun t y ↦ by simp [τ, s.mul_add, ← s.mul_assoc, hsu]
    have h_int (y : Matrix n b F) : Integrable (fun t ↦ Φ (τ t y)) (.addHaar : Measure S) :=
      (h_loc.comp (· y)).continuous.integrable_of_hasCompactSupport (.of_compactSpace _)
    have h_diff : mean Φ - Φ = fun y ↦ ⨍ t, (Φ (τ t y) - Φ y) ∂.addHaar := by
      simp [funext_iff, mean, average, integral_sub (h_int _).to_average (integrable_const _)]
    -- The mean of a locally constant family in the kernel of `Λ` lies in this kernel.
    have h_ker (t : S) : (fun y ↦ Φ (τ t y)) - Φ ∈ LinearMap.ker Λ := by simp [τ, hΛ Φ hΦ]
    rw [← sub_eq_zero, ← map_sub, h_diff]
    exact integral_mem_of_isLocallyConstant _ (h_loc.comp (· - Φ)) h_ker
  suffices h_eq : mean Ψ = mean (stdColDatum χ s) by
    calc Λ Ψ = Λ (mean Ψ) := (h_mean h_shear).symm
      _ = Λ (mean (stdColDatum χ s)) := by rw [h_eq]
      _ = Λ (stdColDatum χ s) := h_mean h_std
  funext y
  by_cases hy : ∃ ρ : Matrix Unit b F, stdColDatum χ s (y + u * ρ) ≠ 0
  · -- Here `s * y` has an integral left inverse `g`, and the shear of `τ t y` is `τ (t + t₀) y` for
    -- the integral matrix `t₀ = (y + u * ρ) * g`.
    obtain ⟨ρ, hρ⟩ := hy
    obtain ⟨h_int, -, g, hg, hgy : g * (s * (y + u * ρ)) = 1⟩ :=
      isIntMatrix_of_stdColDatum_ne_zero hs hρ
    let t₀ : S := ⟨(y + u * ρ) * g, h_int.mul hg⟩
    have hsy : g * (s * y) = 1 := by simpa [s.mul_add, ← s.mul_assoc, hsu] using hgy
    have h_shift (t : S) : Ψ (τ t y) = stdColDatum χ s (τ (t + t₀) y) := by
      simp [Ψ, τ, t₀, Matrix.mul_assoc _ g, ← Matrix.mul_assoc _ u, hsy, hru, add_assoc,
        Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    simp [mean, h_shift, average, integral_add_right_eq_self fun t ↦ stdColDatum χ s (τ t y)]
  · -- Otherwise both integrands vanish.
    have h_zero (ρ : Matrix Unit b F) : stdColDatum χ s (y + u * ρ) = 0 :=
      not_not.1 (not_exists.1 hy ρ)
    simp [mean, Ψ, τ, h_zero, add_assoc, ← Matrix.mul_add]

end ShearInvariance

/-! ## Terms along a line as Gauss sums -/

namespace New.Exchange

open Matrix WeilData MeasureTheory SemilocalField Space Splitting Fintype

variable {E n n' r r' b : Type} {s : n → ℤˣ} {s' : n' → ℤˣ} {t : r → ℤˣ} {t' : r' → ℤˣ} [Field E]
  [CMType E] [WeilData E] [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype r]
  [DecidableEq r] [Fintype r'] [DecidableEq r'] {W : Space E n s} {W' : Space E n' s'}
  {V : Space E r t} {V' : Space E r' t'} [Fintype b] [DecidableEq b] (A : W'.Splitting W Unit)
  (σ' : b ⊕ r' ≃ n') (σ : b ⊕ r ≃ n)

section Local

variable {F : Type} [SemilocalField F] {χ : MulChar F ℂ}

/-- The matrix with rows indexed by `n' ≃ b ⊕ r'` and columns by `Unit ⊕ (b ⊕ r) ⊕ Unit`, where
`n ≃ b ⊕ r`: on the rows `b` it is `(0, (1 0), 0)` and on the rows `r'` it is `(K, (0 I), L)`. -/
noncomputable def frameMatrix (K L : Matrix r' Unit F) (I : Matrix r' r F) :
    Matrix n' (Unit ⊕ n ⊕ Unit) F :=
  ((fromRows 0 K).fromCols
    (((fromBlocks 1 0 0 I).submatrix id σ.symm).fromCols (fromRows 0 L))).submatrix σ'.symm id

omit [Fintype n] [DecidableEq n'] in
/-- For an integral frame `Q` (blocks `K`, `I`, `L` of columns with dual blocks of rows, integral
and inverse to each other), the matrix `frameMatrix σ' σ Q.K Q.L Q.I` is primitive: integral, with
an integral left inverse, which is built from the dual blocks. -/
lemma isPrimitiveMatrix_frameMatrix (Q : IntegralFrame F r' r Unit) :
    IsPrimitiveMatrix O (frameMatrix σ' σ Q.K Q.L Q.I) := by
  obtain ⟨basis_int, dual_int, -, h_dual⟩ := Q.isIntMatrix_and_mul_eq_one
  have basis_blocks : (∀ i j, Q.K i j ∈ O) ∧ (∀ i j, Q.I i j ∈ O) ∧ ∀ i j, Q.L i j ∈ O := by
    simpa [IsIntMatrix, forall_and] using basis_int
  have dual_blocks : (∀ i j, Q.dualK i j ∈ O) ∧ (∀ i j, Q.dualI i j ∈ O) ∧ ∀ i j,
    Q.dualL i j ∈ O := by
    simpa [IsIntMatrix, forall_and] using dual_int
  refine ⟨?_, (frameMatrix σ' σ Q.dualKᵀ Q.dualLᵀ Q.dualIᵀ)ᵀ, ?_, ?_⟩
  · simp [frameMatrix, ite_mem, IsIntMatrix, reindex_equiv σ, reindex_equiv σ', forall_and,
      basis_blocks, Matrix.one_apply]
  · simp [frameMatrix, ite_mem, IsIntMatrix, reindex_equiv σ, reindex_equiv σ', forall_and,
      dual_blocks, Matrix.one_apply]
  · -- Entry by entry, this follows from the nine block equations in `h_dual`.
    simp [← ext_iff, forall_and, Matrix.mul_apply, Matrix.one_apply] at h_dual
    simp [← ext_iff, frameMatrix, eq_comm, reindex_equiv σ, forall_and, h_dual,
      Matrix.mul_apply, Matrix.one_apply]

/-- If `G` is primitive (integral with an integral left inverse) and `P`, `R` are integral matrices
inverse to each other, then the standard datum `χ⁻¹ (det ·)` at `G * T * R` is the constant
`χ⁻¹ (det (R * G))` times its value at `T`. -/
lemma stdColDatum_one_mul_mul {m : Type} [Fintype m] [DecidableEq m] {G P : Matrix n' m F}
    {R : Matrix m n' F}
    (hG : IsPrimitiveMatrix O G) (hP : IsIntMatrix O P) (hR : IsIntMatrix O R) (hPR : P * R = 1)
    (hRP : R * P = 1) (T : Matrix m m F) :
    stdColDatum χ 1 (G * T * R) = invOnUnits χ (R * G).det * stdColDatum χ 1 T := by
  classical
  obtain ⟨G_int, G', G'_int, hG' : G' * G = 1⟩ := hG
  have h_det : (G * T * R).det = (R * G).det * T.det := by
    rw [← det_comm' hRP hPR, ← Matrix.mul_assoc, det_mul]
  have h_int : IsIntMatrix O (G * T * R) ↔ IsIntMatrix O T := by
    refine ⟨fun hT ↦ ?_, fun hT ↦ (G_int.mul hT).mul hR⟩
    simpa [← G'.mul_assoc, hG', hRP, mul_assoc, Matrix.mul_assoc] using G'_int.mul (hT.mul hP)
  -- `invOnUnits χ` is multiplicative on `O`.
  simp only [stdColDatum, h_int, Matrix.one_mul, h_det]
  grind [invOnUnits_mul, IsIntMatrix.det_mem, IsIntMatrix.mul]

/-- The matrix under the determinant of the datum, in the frames of the two isotropic lines. It is
block upper triangular; its diagonal blocks are `c`, the matrix with rows `p` and `y`, and the last
coordinate `z (.inr 0)` of `z`, in this order (`LineIndex n r` indexes coordinates by `n` and one
more coordinate, then by `r`, then one last coordinate) if `β = true` and in the opposite order if
`β = false`. -/
noncomputable def triangularForm (β : Bool) (c : F) (p : Matrix b n F) (y : Matrix r n F)
    (z : LineIndex n r → F) : Matrix (Unit ⊕ n ⊕ Unit) (Unit ⊕ n ⊕ Unit) F :=
  fromBlocks (cond β c (z (.inr 0)) • 1) (vecToMatrix (z ∘ .inl ∘ .inl)) 0
    (((p.fromRows y).submatrix σ.symm id).fromBlocks
      ((fromRows 0 (vecToMatrix (z ∘ .inl ∘ .inr))).submatrix σ.symm id) 0
      (cond β (z (.inr 0)) c • 1))

open scoped Classical in
omit [DecidableEq r] [Fintype b] [DecidableEq b] in
/-- The standard datum at `triangularForm σ β c p y z`, times `ε`, is a product over the coordinates
of `z` times the standard datum `stdRowDatum σ χ p y`. Each coordinate contributes the indicator
function of `O`; the last one has the further factor `ε * χ⁻¹(c) * χ⁻¹(z i)` on units. -/
lemma mul_stdColDatum_triangularForm (ε : ℂ) (β : Bool) (c : F) (p : Matrix b n F)
    (y : Matrix r n F) (z : LineIndex n r → F) :
    let f : LineIndex n r → F → ℂ :=
      1 ⊕ᵥ fun (_ : Unit × Unit) (x : F) ↦ ε * invOnUnits χ c * invOnUnits χ x
    ε * stdColDatum χ 1 (triangularForm σ β c p y z) =
      (∏ i : LineIndex n r, if z i ∈ O then f i (z i) else 0) * stdRowDatum σ χ p y := by
  intro f
  let M : Matrix n n F := (p.fromRows y).submatrix σ.symm id
  have h_int : IsIntMatrix O (triangularForm σ β c p y z) ↔
      IsIntMatrix O M ∧ c ∈ O ∧ ∀ i, z i ∈ O := by
    cases β <;> simp [triangularForm, M, IsIntMatrix, reindex_equiv σ, Unique.forall_iff,
      vecToMatrix] <;> grind
  have h_det : (triangularForm σ β c p y z).det = c * z (.inr 0) * M.det := by
    cases β <;> simp [triangularForm, M, det_fromBlocks_zero₂₁] <;> ring
  have h_prod : (∏ i, if z i ∈ O then f i (z i) else 0) =
      if ∀ i, z i ∈ O then ε * invOnUnits χ c * invOnUnits χ (z (.inr 0)) else 0 := by
    simp [f, prod_ite_zero, prod_prod_type]
  -- It remains that `invOnUnits χ` is multiplicative on `O` and vanishes off `O`.
  simp only [h_prod, stdRowDatum, stdColDatum, Matrix.one_mul, h_int, h_det]
  grind [invOnUnits_mul, mul_mem, invOnUnits, IsIntMatrix.det_mem]

/-- The quotient `invOnUnits χ x / invOnUnits χ y` is `χ⁻¹(x) χ(y)` if `x` and `y` are units of
`O`. Otherwise it is `0`, as its numerator or its denominator is `0`. The lemma states this under
a further condition `q`. -/
lemma ite_isIntegralUnit_eq_ite_invOnUnits_div (q : Prop) (x y : F) [Decidable q]
    [Decidable (q ∧ IsIntegralUnit x ∧ IsIntegralUnit y)] :
    (if q ∧ IsIntegralUnit x ∧ IsIntegralUnit y then (χ x)⁻¹ * χ y else 0) =
      if q then invOnUnits χ x / invOnUnits χ y else 0 := by
  simp only [invOnUnits]
  split_ifs <;> simp_all

end Local

/-- In the frame of `lineTermSplitting A X β` (the matrix `frameAt` of its basis, with coordinates
indexed by `LineIndex n r` and by `r × n`), at the point with line coordinate `a` and other
coordinates `z` and `y`, the standard datum of `p * I'` equals `stdColDatum χ 1` (`χ⁻¹ det` if
integral with unit determinant, else `0`) at the product of `G` (built by `σ'`, `σ` from the frame
of `X`), the block triangular matrix `triangularForm` and the inverse frame `R` of `A`. -/
lemma stdRowDatum_frameAt_lineTermSplitting (X : V'.Splitting V Unit) [IsBaseAdapted A]
    [IsBaseAdapted X] {F : Type} [SemilocalField F] {S : Set (FinPlace E)} {π : 𝔸f E →+* F}
    {χ : MulChar F ℂ} (rd : ReadsAt S π) (a : 𝔸 E) (p : Matrix b n F) (β : Bool)
    (y : Matrix r n F) (z : LineIndex n r → F) :
    let w (i : LineIndex n r) : 𝔸 E := a * i.isRight.toNat
    let R : Matrix (Unit ⊕ n ⊕ Unit) n' F :=
      fromRows (adaptedFrame rd A).dualK (fromRows (adaptedFrame rd A).dualI
        (adaptedFrame rd A).dualL)
    let G : Matrix n' (Unit ⊕ n ⊕ Unit) F :=
      frameMatrix σ' σ (adaptedFrame rd X).K (adaptedFrame rd X).L (adaptedFrame rd X).I
    let πf (c : 𝔸 E) : F := π c.2
    stdRowDatum σ' χ (p * (adaptedFrame rd A).dualI)
        (vecToMatrix (((lineTermSplitting A X β).frameAt 1 (lineTermBasis W V)).map πf *ᵥ
          (πf ∘ w ⊕ᵥ z ⊕ᵥ matrixToVec y))) =
      stdColDatum χ 1 (G * triangularForm σ β (π a.2) p y z * R) := by
  intro w R G πf
  -- It suffices to compare the two matrices. Insert the Kronecker form of the frame of the line
  -- term (`↓`: before its factors are rewritten) and multiply out the blocks.
  refine congrArg (stdColDatum χ 1) ?_
  simp +zetaDelta [↓frameAt_lineTermSplitting, frameMatrix, triangularForm, stdForm,
    adaptedFrame, mulVec, dotProduct, iCoord, sum_prod_type, vecToMatrix, matrixToVec, mul_assoc,
    Matrix.mul_apply, Matrix.mul_assoc, Finset.sum_add_distrib, submatrix_id_mul,
    fromCols_mul_fromBlocks, fromBlocks_mul_fromRows, fromCols_mul_fromRows, Matrix.add_mul]
  -- It remains to rearrange the products and sums in each entry.
  cases β <;> congr with ⟨⟩ <;>
    simp [Finset.mul_sum, diagonal, mul_add, mul_assoc, Matrix.mul_apply, Finset.sum_add_distrib]
  all_goals grind

open scoped Classical in
/-- Let `A` and `X` be adapted splittings of a hyperbolic plane off `W'` and `V'`, leaving `W` and
`V`. `lineTerm A X β x` maps data on `Hom(W', V')` to data on `Hom(W, V)`, and `β` picks one of two
models. A datum `localDatum W' V' v Φ rd` has real part `v` (in the Fock space `PairFock`). At a set
`S` of places it is `Φ`, read through `π` into the semilocal field `F` (subring `O`, element `ϖ`),
and elsewhere it is the vacuum. `stdRowDatum σ χ p y` is `χ⁻¹ det` of the rows of `p` and `y`
ordered by `σ` if that matrix is in `GL(O)`, else `0`. There are nonzero constants `l β` such that
for every tame `χ` there is a number `γ` with (a) `|γ|²` the inverse of the order of the residue
ring and (b) the following. The term at `x = scaleIdele E * a` (a fixed idele times `a`) maps the
datum with real part `v` and, at `S`, `stdRowDatum σ' χ (p * I')` (`I'` reads the coordinates of `W`
in the frame of `A`) to a scalar times the datum with real part `lineTermReal A X β a.1 v` and, at
`S`, `stdRowDatum σ χ p`. Here `a.1` and `a.2` are the infinite and finite parts of `a`. The scalar
is `l β * γ * χ⁻¹(a) * χ(ϖ ā)`, read at `S`, if `a.2` is integral at every finite place outside `S`
and its conjugate and both `a` and `ϖ ā` are units of `O` at `S`; otherwise it is `0`. -/
lemma exists_lineTerm_localDatum (X : V'.Splitting V Unit) [IsBaseAdapted A] [IsBaseAdapted X] :
    ∃ l : Bool → ℂˣ, ∀ {F : Type} [SemilocalField F] {S : Set (FinPlace E)} {π : 𝔸f E →+* F}
      {χ : MulChar F ℂ} (rd : ReadsAt S π) (hχ : TameLocalChar χ), ∃ γ : ℂ,
      -- (a)
      ‖γ‖ ^ 2 = (Nat.card hχ.ResidueRing : ℝ)⁻¹ ∧
      -- (b)
      ∀ (p : Matrix b n F) (β : Bool) (v : PairFock E s' t') (x : 𝔸 E),
        let a : 𝔸 E := x * (scaleIdele E)⁻¹.val
        lineTerm A X β x (localDatum W' V' v (stdRowDatum σ' χ (p * (adaptedFrame rd A).dualI)) rd)
          =
          (l β * γ * if idem S.conjClosureᶜ * a.2 ∈ Ô E ∧ IsIntegralUnit (π a.2) ∧
              IsIntegralUnit (π (star a.2) * ϖ.val) then
            (χ (π a.2))⁻¹ * χ (π (star a.2) * ϖ.val) else 0) •
            localDatum W V (lineTermReal A X β a.1 v) (stdRowDatum σ χ p) rd := by
  -- `lineTerm A X β` is the mixed term of a splitting with an explicit adapted frame, so
  -- `slice_localDatum` computes it once the datum is factored along that frame. One factor
  -- integrates to a Gauss sum, the others to `1`.
  refine ⟨fun β ↦ vacuumFactor (isAdapted_lineTermSplitting A X β), fun {F} _ {S π χ} rd hχ ↦ ?_⟩
  obtain ⟨γ, hγ, h_gauss⟩ : ∃ γ : ℂ, ‖γ‖ ^ 2 = (Nat.card hχ.ResidueRing : ℝ)⁻¹ ∧ ∀ c : F,
      ∫ x in (O : Subring F), invOnUnits χ x * rd.ψ (c * x) = γ / invOnUnits χ (ϖ.val * c) := by
    simpa only [div_invOnUnits] using exists_local_gauss_sum hχ rd.hasIntegralConductor_psi
  -- `P` and `R` are the integral frame of `A` and its inverse, `G` is built from the frame of `X`.
  let Q : IntegralFrame F n' n Unit := adaptedFrame rd A
  let P : Matrix n' (Unit ⊕ n ⊕ Unit) F := fromCols Q.K (fromCols Q.I Q.L)
  let R : Matrix (Unit ⊕ n ⊕ Unit) n' F := fromRows Q.dualK (fromRows Q.dualI Q.dualL)
  obtain ⟨P_int, R_int, hPR : P * R = 1, hRP : R * P = 1⟩ := Q.isIntMatrix_and_mul_eq_one
  let G : Matrix n' (Unit ⊕ n ⊕ Unit) F :=
    frameMatrix σ' σ (adaptedFrame rd X).K (adaptedFrame rd X).L (adaptedFrame rd X).I
  have G_prim : IsPrimitiveMatrix O G := isPrimitiveMatrix_frameMatrix σ' σ _
  -- `R * G` is primitive, so `ε = χ⁻¹ (det (R * G))` has absolute value one.
  obtain ⟨-, det_unit : IsIntegralUnit (R * G).det⟩ := isPrimitiveMatrix_iff_int_and_unit_det.1
    ((IsPrimitiveMatrix.mul_iff ⟨R_int, P, P_int, hPR⟩).2 G_prim)
  let ε : ℂ := invOnUnits χ (R * G).det
  refine ⟨ε * γ, by simp [ε, invOnUnits, det_unit, hχ.norm_eq_one, hγ], ?_⟩
  intro p β v x a
  -- The point of translation is `scaleIdele E • w`, with `w` zero except in the last coordinate.
  let w (i : LineIndex n r) : 𝔸 E := a * i.isRight.toNat
  have h_point : (0 ⊕ᵥ matrixToVec (scalar Unit x) : LineIndex n r → 𝔸 E) = scaleIdele E • w := by
    simp [funext_iff, w, a, Units.smul_def, mul_comm x, matrixToVec, mul_assoc]
  let πf (c : 𝔸 E) : F := π c.2
  -- The factors of the datum: `1` in all coordinates but the last.
  let f : LineIndex n r → F → ℂ :=
    1 ⊕ᵥ fun (_ : Unit × Unit) (c : F) ↦ ε * invOnUnits χ (π a.2) * invOnUnits χ c
  have h_factor (y : Matrix r n F) (z : LineIndex n r → F) :
      stdRowDatum σ' χ (p * Q.dualI) (vecToMatrix (((lineTermSplitting A X β).frameAt 1
          (lineTermBasis W V)).map πf *ᵥ (πf ∘ w ⊕ᵥ z ⊕ᵥ matrixToVec y))) =
        (∏ i, if z i ∈ O then f i (z i) else 0) * stdRowDatum σ χ p y := by
    rw [stdRowDatum_frameAt_lineTermSplitting,
      stdColDatum_one_mul_mul G_prim P_int R_int hPR hRP, mul_stdColDatum_triangularForm]
  -- `slice_localDatum` leaves one integral for each `f i`; the last one is given by `h_gauss`.
  have h_integrals : ∏ i, ∫ t in (O : Subring F), rd.ψ (π (star (w i).2) * t) * f i t =
      ε * γ * (invOnUnits χ (π a.2) / invOnUnits χ (π (star a.2) * ϖ.val)) := by
    simp [w, f, integral_const_mul, volume_O, Measure.real, h_gauss, mul_comm (rd.ψ _), mul_assoc,
      mul_comm ϖ.val, mul_div_left_comm]
  rw [ite_isIntegralUnit_eq_ite_invOnUnits_div, lineTermReal, lineTerm_eq_slice, h_point,
    slice_localDatum rd (isAdapted_lineTermSplitting A X β) (stdRowDatum_mem _ _) w v f h_factor,
    h_integrals]
  simp [w, mul_assoc]

end New.Exchange

/-!
## Fourier coefficients of an equivariant lift as functionals of the datum

Here `S = 𝔠.ramifiedPlaces`, and `componentsAt 𝔠` takes the components of an adele at `S`.

* `New.Exchange.IsEquivariantLift.apply_shear`: translation by an element supported on `S ∪ S̄` that
  is a shear at `S` corresponds to a shear of the datum.
-/

namespace New.Exchange.IsEquivariantLift

open Matrix G Space.Splitting

variable {E n₀ a b m p : Type} [Field E] [CMType E] [WeilData E] [Fintype a] [Fintype b]
  [DecidableEq b] [Fintype m] [DecidableEq m] {μ : NumberField.InfinitePlace E → ℤ}
  {𝔠 : SplitTameChar E μ} {r : m → ℤˣ} {X : Space E m r}
  {M : Submodule ℂ (Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ)}
  {𝒟 : (Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] G E r → ℂ}

omit [WeilData E] in
/-- An element of the adelic unitary group with matrix `1 + (e C - ē C')`, where `e` is the
idempotent of `S`, is trivial at infinity, is supported on `S ∪ S̄` and has component `1 + C`
at `S`. -/
lemma components_of_mat_eq_one_add (g : G E r) (C C' : Matrix m m (𝔸 E))
    (hg : g.adeleMatrix = 1 + ((idemAdele 𝔠.ramifiedPlaces : 𝔸 E) • C - star
      (idemAdele 𝔠.ramifiedPlaces : 𝔸 E) • C')) :
    ((1, g.2) : G E r) = g ∧ g.2 ∈ New.Gf.supportedOn m 𝔠.ramifiedPlaces ∧
      (atPlaces 𝔠.ramifiedPlaces g.2).1 = (1 + C).map (componentsAt 𝔠) := by
  refine ⟨?_, ?_, ?_⟩
  · -- both idempotents vanish at infinity
    aesop (add simp [Prod.ext_iff, funext_iff, one_apply, ext_iff.symm])
  · -- both idempotents vanish at the places outside `S ∪ S̄`
    aesop (add simp [Gf.supportedOn, Gf.atPlace, star_idem, one_apply, ext_iff.symm, Prod.ext_iff,
      funext_iff])
  · -- at the places of `S` the first idempotent is `1` and the second is `0`
    aesop (add simp [atPlaces, 𝔠.star_notMem, funext_iff, star_idem, one_apply, ext_iff.symm,
      Prod.ext_iff])

/-- Let `𝒟` be an equivariant lift on `M` and let `ν` in the unitary group have matrix
`1 + e c k - ē B` (`e` the idempotent of `S`), so that it is `1 + c k` at `S`, with `k c = 0`.
Shearing a datum in `M` by the components at `S` (`componentsAt`) of `x⁻¹ ν x` keeps it in `M`, and
the lift of the sheared datum at `y x` is the lift of the datum at `y ν⁻¹ x`. -/
lemma apply_shear (h𝒟 : IsEquivariantLift 𝔠 X M 𝒟) {Ψ : Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ}
    (hΨ : Ψ ∈ M) {ν : G E r} {c : Matrix m a (𝔸 E)} {k : Matrix a m (𝔸 E)} {B : Matrix m m (𝔸 E)}
    (hν : adeleMatrix ν = 1 + ((idemAdele 𝔠.ramifiedPlaces : 𝔸 E) • (c * k) - star
      (idemAdele 𝔠.ramifiedPlaces : 𝔸 E) • B))
    (hkc : k * c = 0) (x : G E r) :
    let Ψ' (y : Matrix m b (LocProd 𝔠.ramifiedPlaces)) : ℂ := Ψ (y +
      (adeleMatrix x⁻¹ * c).map (componentsAt 𝔠) * ((k * adeleMatrix x).map (componentsAt 𝔠) * y))
    Ψ' ∈ M ∧ ∀ y : G E r, 𝒟 Ψ' (y * x) = 𝒟 Ψ (y * (ν⁻¹ * x)) := by
  classical
  -- The conjugate `g = x⁻¹ ν x` is supported on S ∪ S̄, and its component at S is the shear
  -- `1 + (x⁻¹ c) (k x)`, of determinant 1 since `k * c = 0`. The law `h𝒟.map_translate` for g at
  -- the points `y * (ν⁻¹ * x)` is the claim, because `y * (ν⁻¹ * x) * g = y * x`.
  intro Ψ'
  let g : G E r := x⁻¹ * (ν * x)
  let e : 𝔸 E := idemAdele 𝔠.ramifiedPlaces
  have h_mat : g.adeleMatrix = 1 + (e • (x⁻¹.adeleMatrix * c * (k * x.adeleMatrix)) -
      star e • (x⁻¹.adeleMatrix * (B * x.adeleMatrix))) := by
    simp [g, e, adeleMatrix_mul, hν, mul_add, add_mul, mul_sub, sub_mul, Matrix.mul_assoc,
      ← adeleMatrix_mul x⁻¹]
  obtain ⟨h_fin, h_supp, h_at⟩ := components_of_mat_eq_one_add g _ _ h_mat
  have h_det : (atPlaces 𝔠.ramifiedPlaces g.2).val.det = 1 := by
    rw [h_at, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_one_add_mul_comm]
    simp [← Matrix.mul_assoc, k.mul_assoc, ← adeleMatrix_mul, hkc]
  have h_shear : (fun y ↦ Ψ ((atPlaces 𝔠.ramifiedPlaces g.2).1 * y)) = Ψ' := by
    simp [Ψ', h_at, Matrix.map_add, Matrix.add_mul, Matrix.mul_assoc]
  obtain ⟨h_mem, h_law⟩ := h𝒟.map_translate hΨ g.2 h_supp
  simp only [h_shear, h_det, h_fin] at h_mem h_law
  exact ⟨h_mem, fun y ↦ by simpa [g, mul_assoc] using h_law (y * (ν⁻¹ * x))⟩

/-- Let `𝒟` be an equivariant lift on `M` and let `ν` in the unitary group have matrix
`1 + e c k - ē B` (`e` the idempotent of `S`), so that it is `1 + c k` at `S`, with `k c = 0`.
Shearing a datum in `M` by the components at `S` (`componentsAt`) of `x⁻¹ ν x` keeps it in `M` and
moves the point at which the Fourier coefficient `H.centreCoeff T` of its lift is taken from
`ν⁻¹ x` to `x`. -/
lemma centreCoeff_shear (h𝒟 : IsEquivariantLift 𝔠 X M 𝒟) [Fintype p] [DecidableEq p] [Fintype n₀]
    [DecidableEq n₀] {s₀ : n₀ → ℤˣ} {X₀ : Space E n₀ s₀} (H : X.Splitting X₀ p) (T : Matrix p p E)
    {Ψ : Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ} (hΨ : Ψ ∈ M) {ν : G E r} {c : Matrix m a (𝔸 E)}
    {k : Matrix a m (𝔸 E)} {B : Matrix m m (𝔸 E)}
    (hν : adeleMatrix ν = 1 + ((idemAdele 𝔠.ramifiedPlaces : 𝔸 E) • (c * k) - star
      (idemAdele 𝔠.ramifiedPlaces : 𝔸 E) • B))
    (hkc : k * c = 0) (x : G E r) :
    let Ψ' (y : Matrix m b (LocProd 𝔠.ramifiedPlaces)) : ℂ := Ψ (y +
      (adeleMatrix x⁻¹ * c).map (componentsAt 𝔠) * ((k * adeleMatrix x).map (componentsAt 𝔠) * y))
    Ψ' ∈ M ∧ H.centreCoeff T (𝒟 Ψ') x = H.centreCoeff T (𝒟 Ψ) (ν⁻¹ * x) :=
  (h𝒟.apply_shear hΨ hν hkc x).imp_right fun h_shift ↦ by simp only [centreCoeff, h_shift]

/-- Let `𝒟` be an equivariant lift on `M` (functions of `m × b` matrices over the completions at the
ramified places `S` of `𝔠`) to functions on the unitary group of `X`, and let `H` split `X` over
`X₀`. Fix `T` a `p × p` matrix over `E`. (a) At each point `x`, the `T`-th Fourier coefficient
`Ψ ↦ H.centreCoeff T (𝒟 Ψ) x` along the centre of the radical of `H` is, on `M`, the restriction of
a linear functional `L`. Here `H.kAdelic` is the adelic frame of the isotropic subspace of `H` and
`H.lCoord` its conjugate transpose times the form, a matrix of coordinates. (b) The shear of `Ψ` by
`z` along this frame at `x` stays in `M` and multiplies `L Ψ` by `ψ_S (tr (T_S z))`, with `ψ_S` the
additive character at `S` and `T_S` the matrix of components at `S` of `δ⁻¹ T`, where `δ` is the
idele `invDifferentIdele E`. -/
lemma exists_linear_centreCoeff (h𝒟 : IsEquivariantLift 𝔠 X M 𝒟) [Fintype p] [DecidableEq p]
    [Fintype n₀] [DecidableEq n₀] {s₀ : n₀ → ℤˣ} {X₀ : Space E n₀ s₀} (H : X.Splitting X₀ p)
    (T : Matrix p p E) (x : G E r) :
    ∃ L : (Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] ℂ, ∀ Ψ ∈ M,
      -- (a)
      L Ψ = H.centreCoeff T (𝒟 Ψ) x ∧
      -- (b)
      ∀ z : Matrix p p (LocProd 𝔠.ramifiedPlaces),
        let Ψ' (y : Matrix m b (LocProd 𝔠.ramifiedPlaces)) : ℂ :=
          Ψ (y + (x⁻¹.adeleMatrix * H.kAdelic).map (componentsAt 𝔠) * z *
            ((H.lCoord * x.adeleMatrix).map (componentsAt 𝔠) * y))
        Ψ' ∈ M ∧ L Ψ' = 𝔠.readsAt.ψ
          (((invDifferentIdele E)⁻¹.val • T.map toAdele).map (componentsAt 𝔠) * z).trace • L Ψ := by
  -- The coefficient is linear on M; extend it to a functional on all functions.
  let L₀ : M →ₗ[ℂ] ℂ :=
    { toFun Ψ := H.centreCoeff T (𝒟 Ψ) x
      map_add' Ψ Φ := by
        simpa using H.centreCoeff_add (h𝒟.isAutFunction Ψ.2) (h𝒟.isAutFunction Φ.2) T x
      map_smul' := by simp [centreCoeff, ← quotMean_const_mul, mul_left_comm] }
  obtain ⟨L, hL₀ : L ∘ₗ M.subtype = L₀⟩ := L₀.exists_extend
  have hL Φ (hΦ : Φ ∈ M) : L Φ = H.centreCoeff T (𝒟 Φ) x := LinearMap.congr_fun hL₀ ⟨Φ, hΦ⟩
  refine ⟨L, fun Ψ hΨ ↦ ⟨hL Ψ hΨ, fun z ↦ ?_⟩⟩
  -- Lift z to an adelic matrix N. The shear by z is the one of `centreCoeff_shear` for the central
  -- element `ν = H.radicalCentre (idemAdele S • N)`.
  obtain ⟨N, rfl⟩ : ∃ N : Matrix p p (𝔸 E), N.map (componentsAt 𝔠) = z :=
    ⟨z.map (0, adeleOfLocal _ ·), ext fun i j ↦ evalPlaces_adeleOfLocal _ (z i j)⟩
  let e : 𝔸 E := idemAdele 𝔠.ramifiedPlaces
  have h_mat : (H.radicalCentre (e • N)).adeleMatrix = 1 +
      (e • (H.kAdelic * N * H.lCoord) - star e • (H.kAdelic * Nᴴ * H.lCoord)) := by
    rw [H.adeleMatrix_radicalCentre]
    simp [Matrix.mul_sub, Matrix.sub_mul]
  obtain ⟨h_mem, h_cf⟩ := h𝒟.centreCoeff_shear H T hΨ h_mat (by simp [← Matrix.mul_assoc]) x
  -- The coefficient at `ν⁻¹ * x` is `ψ (tr (T * idemAdele S • N))` times the coefficient at `x`.
  rw [← H.centreCoeff_radicalCentre_mul (h𝒟.isAutFunction hΨ) (e • N) (_ * x),
    mul_inv_cancel_left] at h_cf
  -- The character at S is `ψf` twisted by the finite part of `invDifferentIdele E`, which cancels
  -- `(invDifferentIdele E)⁻¹`.
  have h_char : 𝔠.readsAt.ψ (((invDifferentIdele E)⁻¹.1 • T.map toAdele * N).map
      (componentsAt 𝔠)).trace = stdAddChar E (T.map toAdele * e • N).trace := by
    have h_δ : algebraMap E (𝔸f E) WeilData.j * WeilData.α.val * star WeilData.α.val =
        (invDifferentIdele E).1.2 := rfl
    rw [← AddMonoidHom.map_trace, componentsAt, RingHom.comp_apply, ReadsAt.psi_apply,
      stdLattice.selfDualAddChar_apply, h_δ, mul_left_comm, RingHom.coe_snd, ← Prod.snd_mul]
    simp [stdAddChar, e]
  simp only [← Matrix.map_mul, Matrix.mul_assoc x⁻¹.adeleMatrix]
  exact ⟨h_mem, by rw [hL _ h_mem, hL _ hΨ, h_cf, h_char, smul_eq_mul]⟩

/-- If `𝒟` is an equivariant lift on `M` (automorphic values, equivariant for translations at `S`),
the data in `M` that `𝒟` kills are stable under translation by invertible matrices over the
completions at `S`. -/
lemma comp_mul_mem_ker (h𝒟 : IsEquivariantLift 𝔠 X M 𝒟) (g : GL m (LocProd 𝔠.ramifiedPlaces))
    (Ψ : Matrix m b (LocProd 𝔠.ramifiedPlaces) → ℂ) (hΨ : Ψ ∈ M ⊓ 𝒟.ker) :
    (fun y : Matrix m b (LocProd 𝔠.ramifiedPlaces) ↦ Ψ (g.val * y)) ∈ M ⊓ 𝒟.ker := by
  -- g is the component at S of some k supported on S ∪ S̄; by `map_translate` the image of the
  -- translate of Ψ, translated by k, is a multiple of `𝒟 Ψ = 0`.
  obtain ⟨h_mem, h_zero : 𝒟 Ψ = 0⟩ := hΨ
  obtain ⟨k, hk, rfl⟩ := 𝔠.exists_atPlaces_eq g
  obtain ⟨h_mem', h_law⟩ := h𝒟.map_translate h_mem k hk
  refine ⟨h_mem', funext fun z : G E r ↦ ?_⟩
  obtain ⟨x, rfl⟩ := mul_right_surjective (1, k) z
  simp [h_law x, h_zero]

end New.Exchange.IsEquivariantLift

end
