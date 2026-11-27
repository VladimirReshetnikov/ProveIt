import New.Reduction.Lattices.Colength
import New.UpperBound.Divisibility.SetupAtLevel
import New.UpperBound.Objects.Rows

/-!
# The colength of source forms at p = N

This file compares three modules of source forms, `𝒜_ι`, `𝒜^L` and `𝒜^∨`, with values integral
for the standard lattice, for `L_0` and for `L_0^∨` at `Σ_N`. These are
`integralFormsAt D.SourceForm d` for `d = 1`, `diagPointN 0` and `dualPointN 0`. The comparison
shows that `𝒜' ∩ 𝒜_ι` has colength at most `m f b D_X` in `𝒜_ι`, where `D_X` is the dimension of
the space of source forms. It bounds a colength by a mean degree. The case of monomials, which is
not used later, comes first as a model.

## Main definitions and results

* `New.Data.exists_colengthDvd_upIntegralForms_pow`: `𝒜'` has colength at most `m f b D_X`.

Notions from other files:
* `New.Data.nonInducedPlaces`: the set `Σ_N` of the conjugates of the places above `N` that `ιₚ`
  induces.
* `New.Data.diagPointN`: the point `δ_j`, which takes the standard lattice at `Σ_N` to `L_j`.
* `New.Data.upIntegralForms`: the module `𝒜'`, the preimage of `𝒜^L` under `Up ^ (m / 2)`.
-/

noncomputable section

namespace New

open Finset

/-- The model case of the bound on colengths. In the free module on the monomials `z ^ α` of degree
`a` in `k` variables, the span of the vectors `N ^ α_i • z ^ α` has index dividing
`N ^ ∑_α α_i`, in the sense of `New.ColengthDvd`. -/
lemma colengthDvd_span_pow_monomials {O : Type*} [CommRing O] [IsDomain O] [ValuationRing O] (N : O)
    {k a : ℕ} (i : Fin k) :
    ColengthDvd ⊤
      (Submodule.span O (Set.range fun α : Monomials (Fin k) a ↦ Pi.single α (N ^ α.val i)))
      (N ^ ∑ α : Monomials (Fin k) a, α.val i) := by
  -- The diagonal matrix of the factors `N ^ α_i` carries `z ^ α` to `N ^ α_i • z ^ α`.
  let A : Matrix (Monomials (Fin k) a) (Monomials (Fin k) a) O := .diagonal fun α ↦ N ^ α.1 i
  refine ColengthDvd.of_det_dvd (A := A) (by simp [A, prod_pow_eq_pow_sum]) ?_
  rintro _ ⟨v, rfl⟩
  have h_sum : A.mulVecLin v = ∑ α, v α • Pi.single α (N ^ α.1 i) := funext fun β ↦ by
    simp [A, Matrix.mulVec_diagonal, Finset.sum_apply, Pi.single_apply, mul_comm]
  rw [h_sum]
  exact Submodule.sum_mem _ fun α _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

/-- The mean degree in one of `k` variables of the monomials of degree `a` is `a / k`, by symmetry
in the variables. -/
lemma mul_sum_monomials_apply {k a : ℕ} (i : Fin k) :
    k * ∑ α : Monomials (Fin k) a, α.val i = a * Fintype.card (Monomials (Fin k) a) := by
  -- Swapping `z_i` and `z_j` permutes the monomials and exchanges their exponents.
  have h_swap (j : Fin k) :
      ∑ α : Monomials (Fin k) a, α.1 j = ∑ α : Monomials (Fin k) a, α.1 i :=
    have h_sum (α : Fin k →₀ ℕ) : ∑ x, Finsupp.equivMapDomain (Equiv.swap i j) α x = ∑ x, α x :=
      Fintype.sum_equiv (Equiv.swap i j) _ _ fun x ↦ by simp
    Fintype.sum_equiv ((Finsupp.equivCongrLeft (Equiv.swap i j)).subtypeEquiv fun α ↦ by
      simp [h_sum]) _ _ fun α ↦ by simp
  calc k * ∑ α : Monomials (Fin k) a, α.1 i
      = ∑ j : Fin k, ∑ α : Monomials (Fin k) a, α.1 j := by
        simp only [h_swap, sum_const, card_fin, smul_eq_mul]
    _ = ∑ α : Monomials (Fin k) a, ∑ j, α.1 j := sum_comm
    _ = a * Fintype.card (Monomials (Fin k) a) := by
      simp [fun α : Monomials (Fin k) a ↦ (mem_finsuppAntidiag.1 α.2).1, mul_comm]

end New

namespace New.Data

open Matrix Finset Equiv IsSplitLevel

variable {P : Parameters} (D : Data P)

/-- The degree in the variable `a`, summed over all pairs of a class and a basis vector of the
values of source forms. A basis vector is a family of tableaux (`WeylIndex`), one for each infinite
place `τ : D.Φ` of `E`; its degree in `a` is the number of entries equal to `a` (`tableauWeight`),
summed over `τ`. -/
noncomputable def sumDegreeOf (a : D.X 0) : ℕ :=
  ∑ i : StdClasses (D.levelX 0) × WeylIndex (D.X 0) D.columnCount, ∑ τ : D.Φ,
    tableauWeight i.2 τ a

/-- The summed degree `D.sumDegreeOf a`, the degree in the variable `a` summed over all pairs of a
class and a basis vector of the values of source forms, is the same for all variables `a` of
`X_0`. -/
lemma sumDegreeOf_eq (a b : D.X 0) : D.sumDegreeOf a = D.sumDegreeOf b := by
  -- Up to the class number this is the exponent of `2` in the determinant of the action of
  -- `diag (1, …, 2, …, 1)`, and a transposition moves the entry `2` from `a` to `b`.
  let A : Matrix (D.X 0) (D.X 0) ℤ :=
    (diagonal fun c : D.X 0 ↦ if c = a then 2 else 1).submatrix id (swap a b)
  let B : Matrix (D.X 0) (D.X 0) ℤ := submatrix 1 (swap a b) id
  have hAB : A * B = diagonal fun c : D.X 0 ↦ if c = a then 2 else 1 := by simp [A, B]
  have hBA : B * A = diagonal fun c : D.X 0 ↦ if c = b then 2 else 1 := by
    simp [A, B, ← submatrix_mul, swap_apply_eq_iff]
  simpa [sumDegreeOf, hAB, hBA, schur_diagonal, prod_pow_eq_pow_sum, Fintype.sum_prod_type]
    using det_mul_comm (schur D.columnCount fun _ : D.Φ ↦ A) (schur D.columnCount fun _ : D.Φ ↦ B)

/-- The number `D.sumDegreeOf u` counts the entries equal to `u` in a family of tableaux, a basis
vector of the Weyl module in which source forms take values, summed over all pairs of a double coset
for the level `D.levelX 0` and such a basis vector. There are `D_X = finrank ℂ D.SourceForm` pairs,
and the mean is at most `D.f * D.a / D.k`. -/
lemma mul_sumDegreeOf_le (u : D.X 0) :
    D.k * D.sumDegreeOf u ≤ Module.finrank ℂ D.SourceForm * (D.f * D.a) := by
  let J : Type := StdClasses (D.levelX 0) × WeylIndex (D.X 0) D.columnCount
  have h_rank : Module.finrank ℂ D.SourceForm = Fintype.card J := by
    simp [J, finrank_levelSpace_smoothFormRep, classAut_levelX_zero_eq_bot, -Fintype.card_pi,
      -MonoidHom.coe_range]
  calc D.k * D.sumDegreeOf u
      = ∑ c : D.X 0, D.sumDegreeOf c := by simp [D.sumDegreeOf_eq _ u, D.card_X, n]
    _ = ∑ i : J, ∑ τ : D.Φ, ∑ c : D.X 0, tableauWeight i.2 τ c := sum_comm_cycle.symm
    -- At each place a basis vector has total degree at most `D.a` in all variables together.
    _ ≤ ∑ _i : J, ∑ _τ : D.Φ, D.a := sum_le_sum fun i _ ↦ sum_le_sum fun τ _ ↦
        (sum_tableauWeight i.2 τ).trans_le (D.sum_height_mul_columnCount_le τ)
    _ = Module.finrank ℂ D.SourceForm * (D.f * D.a) := by simp [h_rank]

variable [PadicPlace D.N]

/-- `𝒜_ι ⊆ 𝒜^∨`, with `𝒜_ι` and `𝒜^∨` the source forms integral at `1` and at `D.dualPointN 0`. A
source form `φ` is integral at `d` if the coordinates of `(g * d)⁻¹ φ g` are `N`-integral for all
`g`. -/
lemma integralFormsAt_one_le :
    integralFormsAt D.SourceForm 1 ≤ integralFormsAt D.SourceForm (D.dualPointN 0) := by
  classical
  -- The inverse of `δ_0^∨` acts at each `τ` by an integral matrix, and the weight is polynomial.
  refine fun φ ⟨h_source, (h_integral : GaugeLe 1 1 φ)⟩ ↦ ⟨h_source, fun g ↦ ?_⟩
  let d : Gf D.E (D.X 0) := D.diagPoint 0 (D.nonInducedPlaces \ D.piNPlaces)
  have h_dual : D.dualPointN 0 = d⁻¹ := by
    simp [d, dualPointN, diagPoint, diagN_eq_sdiff_mul D.piNPlaces]
  let A (τ : D.Φ) : Matrix (D.X 0) (D.X 0) ℂ_[D.N] :=
    (GeneralLinearGroup.map (adeleExtension (weightEmbedding ιₚ τ)) d.val).val
  have hA (τ : D.Φ) (i j : D.X 0) : ‖A τ i j‖ ≤ 1 := by
    simp only [A, d, map_adeleExtension_diagPoint, coe_diagGL, diagonal_apply]
    split_ifs <;> simp [norm_p_lt_one.le]
  let ξ : WeylIndex (D.X 0) D.columnCount → ℂ_[D.N] :=
    weylRep D.columnCount (D.lastEntry 0) (fun τ : D.Φ ↦
    GeneralLinearGroup.map (adeleExtension (weightEmbedding ιₚ τ)) (g * 1)⁻¹.val) *ᵥ ιₚ ∘ φ.val g
  calc weylGauge D.columnCount (D.lastEntry 0) (g * D.dualPointN 0) (φ.val g)
      = ‖schur D.columnCount A *ᵥ ξ‖ := by
        simp [h_dual, weylGauge, weylRep, lastEntry, A, ξ, -coe_units_inv]
    _ ≤ ‖ξ‖ := Rows.norm_schur_mulVec_le .refl hA ξ
    _ ≤ 1 := h_integral g

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- For every finite adelic point `c` there is a rational point `γ` such that `γ c δ_0^∨` is
integral above `N` and `γ c δ_0` is `diag (1, …, 1, N)` at `Σ_N` times an element integral above
`N`. Here `δ_0 = D.diagPointN 0` and `δ_0^∨ = D.dualPointN 0`. -/
lemma exists_mul_dualPointN_mem_integralAbove (c : Gf D.E (D.X 0)) :
    ∃ γ : U (stdSpace D.E (D.X 0)).J,
      stdEmbFin γ * c * D.dualPointN 0 ∈ integralAbove (D.X 0) D.N ∧
      (D.diagPoint 0 D.nonInducedPlaces)⁻¹ * (stdEmbFin γ * c * D.diagPointN 0) ∈
        integralAbove (D.X 0) D.N := by
  simpa [mul_assoc] using exists_mul_mem_integralAbove D.N (c * D.dualPointN 0)
    (D.diagPoint 0 D.nonInducedPlaces)⁻¹

/-- Let `𝒜^L` and `𝒜^∨` be the modules of source forms `φ` integral at `δ_0 = D.diagPointN 0` and at
`δ_0^∨ = D.dualPointN 0`. The colength (`ColengthDvd`) of `𝒜^L` in `𝒜^∨` divides `N ^ l`, with
`l = D.sumDegreeOf (.inr ())` the sum of the degrees in the last variable. -/
lemma colengthDvd_integralFormsAt_diagPointN :
    ColengthDvd (integralFormsAt D.SourceForm (D.dualPointN 0))
      (integralFormsAt D.SourceForm (D.diagPointN 0)) (D.N ^ D.sumDegreeOf (.inr ())) := by
  classical
  -- Evaluate at class representatives `r c` adapted to both points. A form lies in `𝒜^L` if each
  -- coordinate is divisible by `N` to its degree in the last variable.
  let J : Type := StdClasses (D.levelX 0) × WeylIndex (D.X 0) D.columnCount
  let d : Gf D.E (D.X 0) := (D.diagPoint 0 D.nonInducedPlaces)⁻¹
  choose γ h_dual h_diagPoint using D.exists_mul_dualPointN_mem_integralAbove
  let r (c : StdClasses (D.levelX 0)) : Gf D.E (D.X 0) := stdEmbFin (γ c.out) * c.out
  let ev : D.FormX 0 →ₗ[embValRing] J → ℂ :=
    { toFun φ i := φ.val (r i.1) i.2, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  let incl : (J → embValRing) →ₗ[embValRing] J → ℂ := (Algebra.linearMap embValRing ℂ).compLeft J
  let A : Matrix J J embValRing := diagonal fun i ↦ D.N ^ ∑ τ, tableauWeight i.2 τ (.inr ())
  have h_diag : ColengthDvd (.map incl ⊤) (.map incl A.mulVecLin.range)
      (D.N ^ D.sumDegreeOf (.inr ())) :=
    (ColengthDvd.of_det_dvd (by rw [det_diagonal, prod_pow_eq_pow_sum, sumDegreeOf]) le_rfl).map
      incl le_sup_left le_rfl
  refine h_diag.comap ev ?_ ?_
  · -- The values at the `r c` of a form in `𝒜^∨` have integral coordinates.
    rintro φ ⟨-, hφ : GaugeLe (D.dualPointN 0) 1 φ⟩
    exact ⟨fun i ↦ ⟨ev φ i, (weylGauge_le_one_iff _ (h_dual i.1.out)).1 (hφ (r i.1)) i.2⟩,
      trivial, rfl⟩
  rintro φ ⟨hφ : φ ∈ D.SourceForm, -⟩ ⟨_, ⟨y, rfl⟩, hy : incl (A *ᵥ y) = ev φ⟩
  refine ⟨hφ, fun g ↦ ?_⟩
  obtain ⟨c, δ, k, rfl⟩ : ∃ (c : StdClasses (D.levelX 0)) (δ : U (stdSpace D.E (D.X 0)).J)
      (k : D.levelX 0), g = stdEmbFin δ * c.out * k :=
    exists_eq_map_mul_rep_mul stdEmbFin (D.levelX 0) Quotient.out_eq g
  -- The point `r c * k * δ_0` is `d⁻¹` times an integral factor.
  have h_point : d * (r c * (k * D.diagPointN 0)) ∈ integralAbove (D.X 0) D.N := by
    have hk : (D.diagPointN 0)⁻¹ * k.val * D.diagPointN 0 ∈ integralAbove (D.X 0) D.N := by
      obtain ⟨a, -, ha⟩ := D.atPlaces_conj_mem_mirabolic k
      exact mem_integralAbove_of_inclGL_eq ha
    simpa [r, mul_assoc] using mul_mem (h_diagPoint c.out) hk
  have h_value : ιₚ ∘ φ.val (r c) =
      schur D.columnCount (fun _ ↦ diagonal (1 ⊕ᵥ D.N)) *ᵥ fun w ↦ ιₚ (y (c, w)) := by
    ext w
    simp [show φ.val (r c) w = (A *ᵥ y) (c, w) from (congrFun hy (c, w)).symm, A, schur_diagonal,
      prod_pow_eq_pow_sum, mulVec_diagonal]
  have h_class : φ.val (stdEmbFin δ * c.out * k) =
      (stdSpace D.E (D.X 0)).weightRep D.columnCount (D.lastEntry 0) δ (φ.val c.out) := by
    simpa using levelSpace_smoothFormRep_apply hφ δ c.out k
  have h_rep : φ.val (r c) =
      (stdSpace D.E (D.X 0)).weightRep D.columnCount (D.lastEntry 0) (γ c.out) (φ.val c.out) := by
    simpa [r] using levelSpace_smoothFormRep_apply hφ (γ c.out) c.out 1
  calc
    _ = weylGauge D.columnCount (D.lastEntry 0) (r c * (k.val * D.diagPointN 0)) (φ.val (r c)) := by
      rw [h_class, h_rep, mul_assoc, mul_assoc, mul_assoc, weylGauge_embFin, weylGauge_embFin]
    _ = weylGauge D.columnCount (D.lastEntry 0) d⁻¹ (φ.val (r c)) := by
      rw [← weylGauge_mul_of_mem_integralAbove d⁻¹ h_point, inv_mul_cancel_left d]
    _ = ‖fun w ↦ ιₚ (y (c, w))‖ := by
      -- `d` acts at each `τ` by the inverse of `diag (1, …, 1, N)`.
      simp [weylGauge, h_value, weylRep, lastEntry, d, map_adeleExtension_diagPoint,
        star_inducedPlace_mem_nonInducedPlaces, -coe_units_inv]
    _ ≤ 1 := (pi_norm_le_iff_of_nonempty _).2 fun w ↦ (y (c, w)).prop

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- The operator `Up = upOperator (D.formRepAtN 0)`, a sum of right translates with roots of unity
as coefficients (see `upOperator_mem_sourceForm`), maps `𝒜^L`, the source forms integral at
`D.diagPointN 0`, to `𝒜^∨`, those integral at `D.dualPointN 0`. -/
lemma upOperator_mem_integralFormsAt {φ : D.FormX 0}
    (hφ : φ ∈ integralFormsAt D.SourceForm (D.diagPointN 0)) :
    upOperator (D.formRepAtN 0) φ ∈ integralFormsAt D.SourceForm (D.dualPointN 0) := by
  classical
  obtain ⟨h_source, h_integral⟩ := hφ
  refine ⟨D.upOperator_mem_sourceForm h_source, fun g ↦ ?_⟩
  -- The value at `g` is a sum of roots of unity times values `φ (g g')`, where `g' δ_0` and `δ_0^∨`
  -- differ on the right by an element `k` that is integral above `N`.
  let k (y : D.X 0 → D.nonInducedPlaces → ZMod D.N) : Gf D.E (D.X 0) :=
    embedGL (inclGL (lastRowColGL y))
  let g' (y : D.X 0 → D.nonInducedPlaces → ZMod D.N) : Gf D.E (D.X 0) :=
    D.dualPointN 0 * k y * (D.diagPointN 0)⁻¹
  have h_value : (upOperator (D.formRepAtN 0) φ).val g =
      ∑ y with IsUnit (y (.inr ())), psiN (y (.inr ())) • φ.val (g * g' y) := by
    simp [upOperator, conjEmbedGL, g', k, mul_assoc]
  rw [h_value]
  refine weylGauge_sum_le _ zero_le_one fun y _ ↦ ?_
  rw [weylGauge_smul, psiN, P.norm_map_selfDualAddChar, one_mul,
    ← weylGauge_mul_of_mem_integralAbove (k := k y) _
    (mem_integralAbove_of_inclGL_eq (atPlaces_embedGL _).symm),
    show g * D.dualPointN 0 * k y = g * g' y * D.diagPointN 0 by simp [g', mul_assoc]]
  exact h_integral (g * g' y)

/-- Let `𝒜_ι` and `𝒜^L` be the modules of source forms (`D.SourceForm`) that are integral at the
points `1` and `δ_0 = D.diagPointN 0`. Let `Up = upOperator (D.formRepAtN 0)` be the sum of right
translates described at `upOperator_mem_sourceForm`. Let `l = D.sumDegreeOf (.inr ())` be the summed
degree in the last variable of `X_0`. Then the index (`ColengthDvd`) in `𝒜_ι` of the preimage of
`𝒜^L` under `Up ^ i` divides `N ^ (l (i + 1))`. -/
lemma colengthDvd_comap_upOperator_pow (i : ℕ) :
    ColengthDvd (integralFormsAt D.SourceForm 1)
      ((integralFormsAt D.SourceForm (D.diagPointN 0)).comap
        ((upOperator (D.formRepAtN 0) ^ i).restrictScalars embValRing))
      (D.N ^ (D.sumDegreeOf (.inr ()) * (i + 1))) := by
  -- The colength `l` is paid once from `𝒜_ι ⊆ 𝒜^∨` to `𝒜^L`, and once for each factor `Up`: the
  -- preimage of `𝒜^L` under `Up ^ i` lies in that of `𝒜^∨` under `Up ^ (i + 1)`.
  induction i with
  | zero =>
    rw [zero_add, mul_one]
    exact D.colengthDvd_integralFormsAt_diagPointN.comap .id D.integralFormsAt_one_le
      fun φ _ hφ ↦ by simpa using hφ
  | succ i ih =>
    rw [mul_add_one, pow_add (D.N : embValRing)]
    refine ih.trans (D.colengthDvd_integralFormsAt_diagPointN.comap _ (fun φ hφ ↦ ?_) fun _ _ h ↦ h)
    simpa [pow_succ'] using D.upOperator_mem_integralFormsAt hφ

/-- **The prime `N`, colength.** Let `𝒜_ι` be the module of source forms with `N`-integral values
for the standard lattice, and `𝒜' = D.upIntegralForms` the module of forms `φ` on `X_0` such that
`Up ^ (m / 2) φ` is a source form integral at `D.diagPointN 0`, with
`Up = upOperator (D.formRepAtN 0)`. There is `e ≤ m f b D_X` such that every finite family in `𝒜_ι`
is carried into `𝒜'` by a square matrix whose determinant divides `N ^ e`. Here `m = D.m` is the
number of theta lifts from `X_0` to `X_m`, `f = D.f` the number of infinite places of `E`, `b = D.b`
the value of `D.weight` on the set `D.bPlaces` of infinite places, and `D_X` the dimension of the
space of source forms. -/
lemma exists_colengthDvd_upIntegralForms_pow :
    ∃ e : ℕ,
      e ≤ D.m * D.f * D.b * Module.finrank ℂ D.SourceForm ∧
      ColengthDvd (integralFormsAt D.SourceForm 1) D.upIntegralForms (D.N ^ e) := by
  let l : ℕ := D.sumDegreeOf (.inr ())
  refine ⟨l * (D.ϱ + 1 + 1), ?_, D.colengthDvd_comap_upOperator_pow (D.ϱ + 1)⟩
  have hl : (D.k * l : ℝ) ≤ Module.finrank ℂ D.SourceForm * (D.f * D.a) :=
    mod_cast D.mul_sumDegreeOf_le (.inr ())
  have h_size : (D.ϱ + 1 + 1 : ℝ) * D.a ≤ D.m * D.b * D.k := D.le_of_hasLogBound
  refine le_of_mul_le_mul_left (a := (D.k : ℝ)) ?_ (by simp)
  push_cast
  calc
    _ ≤ Module.finrank ℂ D.SourceForm * (D.f * D.a) * (D.ϱ + 1 + 1 : ℝ) := by grw [← mul_assoc, hl]
    _ = Module.finrank ℂ D.SourceForm * D.f * ((D.ϱ + 1 + 1 : ℝ) * D.a) := by ring
    _ ≤ Module.finrank ℂ D.SourceForm * D.f * (D.m * D.b * D.k) := by gcongr
    _ = D.k * (D.m * D.f * D.b * Module.finrank ℂ D.SourceForm) := by ring

end New.Data

end
