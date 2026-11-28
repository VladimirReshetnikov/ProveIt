import Lib.Adelic.AutomorphicForms.PAdicGauge
import Lib.General.LinearAlgebra.BlockEmbeddings
import New.Determinant.Exchange.MatchingPartners

/-!
# One exchange, and class sums at the level of a row stabilizer

The exchange identity compares class sums of theta kernels on a definite space `E^n` with integrals
over `[U(V')]`. For `W = E^b ⊕ W'` and an invariant datum it confines the twist to the kernel of
`(V', E^b)`, two spaces of equal rank. (`E^b` is the standard definite space with basis indexed by
`b`.) If `F` is invariant under a row stabilizer, the datum is a product for `z` in the stabilizer,
and the class sum at full level unfolds to the class sum of this product at the level of the
stabilizer.

## Main definitions and results

* `New.Rows.rowStabilizer`: the invertible A with the columns of 1 off e and w · φ(A) = w.
* `New.Rows.columnDatum`: the factor that depends only on the columns e.
* `New.Rows.columnDatum_mul_ite_eq_ite_mem_rowStabilizer`: for F left invariant under
  `New.Rows.rowStabilizer`, the function χ(det z) F(z⁻¹ y), cut down to z in the stabilizer, is a
  product.
* `New.Rows.integrable_and_mul_stdClassSum_eq_integral_mul`: from the exchange identity for matched
  data on `E^b ⊕ W'`, with the constant `c`: for an invariant datum `Ψ'`, `c` times the class sum
  of the kernel of `χ (det x'') Ψ' (x''⁻¹ x')` is the integral of the kernel of `(V', E^b)` with
  datum `χ ∘ det` times the kernel of `(V', W')` with datum `Ψ'`.
  `New.Rows.mul_stdClassSum_eq_integral_mul_modKernel` sums this over the classes of `U(E^b)`.
* `New.Rows.stdClassSum_rowStabilizer_eq`: a class sum at full level equals a class sum at the level
  of a row stabilizer, with a datum supported on matrices of a special shape.

Notions from other files:
* `New.AutChar`: an automorphic circle-valued character of U(1)(𝔸). `HasWeight` e ψ gives its
  exponents e at the infinite places and its tame parts ψ at the finite places.
* `New.modKernelStdSpace` W α β 𝔪 Ψ P g h: the theta kernel of the pair of W and the standard
  definite space, with the twisting characters α and β, the datum Ψ modulo 𝔪 and the polynomial P,
  at the adelic point g and at the point with real part 1 and finite part h.
* `New.stdLevel`: the level K₀, the stabilizer of the standard lattice.
* `New.Fock.polyVector` ε P: the Fock vector P(ζ(x)) exp(-|x|²/2), where ζ conjugates the
  coordinates of positive sign. For a pair with signs s and t, `homSigns` s t gives the products of
  the signs as those of the coordinates, and `realSigns` repeats them at every infinite place.
* `New.Modulus`: a modulus, a nonzero ideal 𝔪 of O_E prime to its complex conjugate, that is, never
  divisible by both w and w̄; `New.Modulus.ResidueRing` is the residue ring O_E/𝔪.
* `New.Exchange.IsTameFor`: `IsTameFor 𝔪 ν e χ` says that 𝔪 ≠ (1), that ν has weight e and that its
  tame part is ramified exactly at the places dividing 𝔪 and gives the character χ modulo 𝔪.
* `New.Rows.liftMod`: a chosen lift of g ∈ GL_n(O_E/𝔪) to K₀, with component 1 outside the places
  dividing 𝔪 and their conjugates.
* `New.Space` E n s: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸)
  with xᴴJx equal to diag(s) at the infinite places and 1 at the finite places.
* `New.G` E s: the adelic unitary group G = G_∞ × G_f for signs s at the infinite places and the
  identity matrix at the finite places; `New.Gf` E n is G_f.

## Relation to the literature

See `New.OneLift.ComparisonOperator.FirstFactors`, `New.OneLift.ComparisonOperator.GluingMaps`
and `New.Determinant.Exchange.ExplicitMatching` for related work.
-/

noncomputable section

/-!
## The function χ(det z) F(z⁻¹ y) on a row stabilizer as a product

`New.inclMatrix R e` is the N × r matrix whose column j is the unit vector e j.
-/

section RowStabilizer

open Matrix MulAction

namespace New.Rows

variable {R S r a c N : Type} [CommRing R] [CommRing S] [Fintype r] [DecidableEq r] [Fintype N]
  [DecidableEq N]

/-- The columns of the square matrix z outside the image of e are those of the identity matrix. -/
abbrev FixesColsOff (e : r ↪ N) (z : Matrix N N R) : Prop :=
  z * (1 - inclMatrix R e * (inclMatrix R e)ᵀ) = 1 - inclMatrix R e * (inclMatrix R e)ᵀ

/-- The subgroup of the A in GL_N(R) such that (a) the columns of A outside the image of e are those
of 1, and (b) w · φ(A) = w. Condition (a) says that A fixes the projection
`1 - inclMatrix R e * (inclMatrix R e)ᵀ` under left multiplication. Condition (b) says that φ(A)
fixes w under right multiplication, hence the passage through the opposite group. -/
def rowStabilizer (φ : R →+* S) (w : Matrix c N S) (e : r ↪ N) : Subgroup (GL N R) :=
  -- the set is the intersection of two stabilizers, for left and for right multiplication
  Subgroup.copy (s := {A : GL N R | FixesColsOff e A.1 ∧ w * A.1.map φ = w})
    (stabilizer (GL N R) (1 - inclMatrix R e * (inclMatrix R e)ᵀ) ⊓
      ((stabilizer (Matrix N N S)ᵐᵒᵖˣ w.row).comap Units.opEquiv.symm.toMonoidHom).unop.comap
        (GeneralLinearGroup.map φ))
    rfl

open scoped Classical in
/-- The function of an N×r matrix σ equal to χ(det of the rows e of σ) if
`w * σ.map φ = w * inclMatrix S e`, and 0 otherwise. -/
def columnDatum (χ : MulChar R ℂ) (φ : R →+* S) (w : Matrix c N S) (e : r ↪ N)
    (σ : Matrix N r R) : ℂ :=
  if w * map σ φ = w * inclMatrix S e then χ (submatrix σ e id).det else 0

open scoped Classical in
/-- Let H = `rowStabilizer φ w e` be the group of the invertible A that have the columns of 1 off
the image of e and satisfy w · φ(A) = w, let F be left invariant under H, and let z be an N × N
matrix. Then `columnDatum` of the columns e of z, times F(y) if z has the columns of 1 off e and 0
otherwise, equals χ(det z) F(z⁻¹ y) if z lies in H, and 0 otherwise. -/
lemma columnDatum_mul_ite_eq_ite_mem_rowStabilizer (χ : MulChar R ℂ) (φ : R →+* S)
    (w : Matrix c N S) (e : r ↪ N) {F : Matrix N a R → ℂ}
    (hF : ∀ A ∈ rowStabilizer φ w e, ∀ y : Matrix N a R, F (A.val * y) = F y) (y : Matrix N a R)
    (z : Matrix N N R) :
    columnDatum χ φ w e (z.submatrix id e) * (if FixesColsOff e z then F y else 0) =
      if ∃ Z ∈ rowStabilizer φ w e, Z.val = z then χ z.det * F (z⁻¹ * y) else 0 := by
  -- On a matrix with the columns of `1` off `e`, the datum `columnDatum` can be read on the whole
  -- matrix.
  have h_datum (hz : FixesColsOff e z) :
      columnDatum χ φ w e (z.submatrix id e) = if w * z.map φ = w then χ z.det else 0 := by
    obtain ⟨u, rfl⟩ : ∃ u : Matrix N r R, z = 1 + u * (inclMatrix R e)ᵀ :=
      ⟨(z - 1) * inclMatrix R e, by
        linear_combination (norm := noncomm_ring [Matrix.mul_assoc]) hz⟩
    -- For `z = 1 + u * (inclMatrix R e)ᵀ`: the columns `e` and their minor on the rows `e`.
    have h_cols : (1 + u * (inclMatrix R e)ᵀ).submatrix id e = inclMatrix R e + u := by
      simp [← mul_inclMatrix, Matrix.add_mul, Matrix.mul_assoc, inclMatrix_transpose_mul_self]
    have h_det : ((inclMatrix R e + u).submatrix e id).det = (1 + u * (inclMatrix R e)ᵀ).det := by
      rw [← inclMatrix_transpose_mul, Matrix.mul_add, inclMatrix_transpose_mul_self,
        det_one_add_mul_comm]
    -- Both conditions on `w` say `w * u.map φ = 0`, as `(inclMatrix S e)ᵀ` cancels on the right.
    have h_w_cols : w * (inclMatrix R e + u).map φ = w * inclMatrix S e ↔ w * u.map φ = 0 := by
      simp [Matrix.map_add, map_inclMatrix, Matrix.mul_add]
    have h_w_all : w * (1 + u * (inclMatrix R e)ᵀ).map φ = w ↔ w * u.map φ = 0 := by
      simp [Matrix.map_add, map_inclMatrix, Matrix.mul_add, transpose_map, ← w.mul_assoc,
        (mul_left_injective_of_inv _ _ (inclMatrix_transpose_mul_self e)).eq_iff'
          (Matrix.zero_mul _)]
    simp only [columnDatum, h_cols, h_det, h_w_cols, h_w_all]
  have h_mem (Z : GL N R) :
      Z ∈ rowStabilizer φ w e ↔ FixesColsOff e Z.1 ∧ w * Z.1.map φ = w := .rfl
  split_ifs with h_fixes hz hz
  · obtain ⟨Z, hZ, rfl⟩ := hz
    have hF_inv : F (Z.val⁻¹ * y) = F y := by simpa [coe_units_inv] using hF Z⁻¹ (inv_mem hZ) y
    rw [h_datum h_fixes, ite_eq_left ((h_mem Z).1 hZ).right, hF_inv]
  · -- If `z` satisfies both conditions without being in the group, it is not invertible.
    have h_det (h_rows : w * z.map φ = w) : χ z.det = 0 := χ.map_nonunit fun h_unit ↦ by
      obtain ⟨Z, rfl⟩ := (isUnit_iff_isUnit_det z).2 h_unit
      exact hz ⟨Z, (h_mem Z).2 ⟨h_fixes, h_rows⟩, rfl⟩
    simp +contextual [h_datum h_fixes, h_det]
  · obtain ⟨Z, hZ, rfl⟩ := hz
    exact absurd ((h_mem Z).1 hZ).left h_fixes
  · exact mul_zero _

end New.Rows

end RowStabilizer

/-!
## Rapid decay of kernels, one exchange, and class sums at row stabilizers

`New.modKernel S T a b 𝔪 Ψ P` is the theta kernel of the pair `(S, T)` for a function `Ψ` on
matrices modulo `𝔪` and a polynomial `P`; `New.stdClassSum K` is the class sum of level `K` on the
standard definite space `stdSpace`.
-/

namespace New.Rows

open NumberField Matrix Finset MeasureTheory Ideal.Quotient Exchange Subgroup IsLevel Fock Space

variable {E n b : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] [Fintype b]
  [DecidableEq b]

/-- Let `S` and `V` be hermitian spaces with signs `s` and `t` at the infinite places. If some place
divides the modulus `𝔪` and the function `Ψ` on matrices modulo `𝔪` is supported on matrices with a
left inverse, the theta kernel `modKernel` of `(S, V)` for `Ψ`, the polynomial `P` and the twisting
characters `a`, `β` has rapid decay in the adelic point `g` of `U(S)`: its product with any power of
the height is bounded. -/
lemma isRapid_modKernel {s : n → ℤˣ} {t : b → ℤˣ} {𝔪 : Modulus E} (S : Space E n s)
    (V : Space E b t) (a β : AutChar E) (h𝔪 : Nonempty 𝔪.places)
    {Ψ : Matrix b n 𝔪.ResidueRing → ℂ}
    (hΨ : ∀ y : Matrix b n 𝔪.ResidueRing, Ψ y ≠ 0 → HasLeftInv y)
    (P : MvPolynomial (NumberField.InfinitePlace E × b × n) ℂ) (h : G E t) :
    S.IsRapid fun g : G E s ↦ modKernel S V a β 𝔪 Ψ P g h := by
  intro M
  -- `decay`: |θ(g, h)| ht(g)^M ≤ C · (N-th moment of the Fock vector) · ht(h)^B, for all `g`
  obtain ⟨B, N, C, decay⟩ := pairTheta_modDatum_decay S V a β h𝔪 hΨ M
  exact ⟨_, fun g ↦ decay _ h g (Fock.fockMoment_polyVector_ne_top N P)⟩

/-- A matrix `y` with rows indexed by `m ⊕ k` whose top block `y.toRows₁` (the rows in `m`) has unit
determinant has a left inverse (`HasLeftInv`), namely `(y.toRows₁⁻¹ 0)`. -/
lemma hasLeftInv_of_isUnit_det_toRows₁ {R m k : Type} [CommRing R] [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] {y : Matrix (m ⊕ k) m R} (hy : IsUnit y.toRows₁.det) :
    HasLeftInv y := by
  refine ⟨fromCols y.toRows₁⁻¹ 0, ?_⟩
  rw [← y.fromRows_toRows, fromCols_mul_fromRows]
  simp [hy]

omit [WeilData E] in
/-- Let `Ψ'` be a function on matrices modulo `𝔪` that is invariant under right multiplication by
invertible matrices. Then the functions `Φ x = χ (det x'') Ψ' (x''⁻¹ x')` of `x = (x' x'')` and
`Ψ y = χ (det y') Ψ' (y'')` of `y = (y'; y'')` are matched for `χ⁻¹` (`AreMatched`). -/
lemma areMatched_det_mul {𝔪 : Modulus E} (χ : MulChar 𝔪.ResidueRing ℂ)
    {Ψ' : Matrix n b 𝔪.ResidueRing → ℂ}
    (hΨ' : ∀ (y : Matrix n b 𝔪.ResidueRing) (γ : GL b 𝔪.ResidueRing), Ψ' (y * γ.1) = Ψ' y) :
    AreMatched ⊤ (.refl (b ⊕ n)) χ⁻¹
      (fun x : Matrix n (b ⊕ n) 𝔪.ResidueRing ↦ χ x.toCols₂.det * Ψ' (x.toCols₂⁻¹ * x.toCols₁))
      (fun y : Matrix (b ⊕ n) b 𝔪.ResidueRing ↦ χ y.toRows₁.det * Ψ' y.toRows₂) := by
  -- `areMatched_block` gives the matched function `χ (det y') Ψ' (-y'' y'⁻¹)`, and the invariance
  -- of `Ψ'` removes the factor `-y'⁻¹`.
  have h_row : (fun x : Matrix n (b ⊕ n) 𝔪.ResidueRing ↦
      χ x.toCols₂.det * Ψ' (x.toCols₂⁻¹ * x.toCols₁)) = blockRowDatum (.refl (b ⊕ n)) χ⁻¹ Ψ' := by
    simp [funext_iff, blockRowDatum]
  have h_col : (fun y : Matrix (b ⊕ n) b 𝔪.ResidueRing ↦ χ y.toRows₁.det * Ψ' y.toRows₂) =
      blockColDatum (.refl (b ⊕ n)) χ⁻¹ Ψ' := funext fun y ↦ by
    by_cases hy : IsUnit y.toRows₁.det
    · rw [← hΨ' _ (-(GeneralLinearGroup.mk'' _ hy)⁻¹)]
      simp [blockColDatum]
    · simp [blockColDatum, χ.map_nonunit hy]
  rw [h_row, h_col]
  exact areMatched_block (.refl (b ⊕ n)) χ⁻¹ Ψ'

/-- One exchange. Let `V'` and `W'` be hermitian spaces with bases indexed by `b` and `n` and signs
`t` and `s` at the infinite places, with adelic unitary groups `G E t` and `G E s`. Let `E^b` be the
standard definite space (`stdSpace`), `W = E^b ⊕ W'`, and let `.sum ((1, h'), g)` be the point of
`U(W)` with blocks `h'` and `g`. Let `𝔪 ≠ (1)` be a modulus and `χ` a character of `𝒪 / 𝔪`. For a
function `Φ` on matrices modulo `𝔪`, `K Φ` is a function on the finite points of `U(E^n)`. We assume
the exchange identity: for matched `Φ`, `Ψ` (`AreMatched`), `c` times the class sum of `K Φ` at full
level is the integral over the automorphic quotient of `U(V')` of the theta kernel of `(V', W)` with
datum `Ψ` and the polynomial `P` in the variables of `W'`. Let `Ψ'` be invariant under right
multiplication by `GL_b (𝒪 / 𝔪)`. Then the product of the kernel of `(V', E^b)` at `h'` and the
kernel of `(V', W')` at `g` is integrable, and its integral is `c` times the class sum of `K Φ` for
`Φ (x' x'') = χ (det x'') Ψ' (x''⁻¹ x')`. -/
lemma integrable_and_mul_stdClassSum_eq_integral_mul {s : n → ℤˣ} {t : b → ℤˣ} {𝔪 : Modulus E}
    (V' : Space E b t) (W' : Space E n s) {a β β' : AutChar E}
    (h𝔪 : Nonempty 𝔪.places) (χ : MulChar 𝔪.ResidueRing ℂ) {Ψ' : Matrix n b 𝔪.ResidueRing → ℂ}
    (hΨ' : ∀ (y : Matrix n b 𝔪.ResidueRing) (γ : GL b 𝔪.ResidueRing), Ψ' (y * γ.1) = Ψ' y)
    {P : MvPolynomial (InfinitePlace E × n × b) ℂ} {h' : Gf E b} {g : G E s}
    {K : (Matrix n (b ⊕ n) 𝔪.ResidueRing → ℂ) → Gf E n → ℂ} {c : ℂ}
    (h_exchange : ∀ (Φ : Matrix n (b ⊕ n) 𝔪.ResidueRing → ℂ)
      (Ψ : Matrix (b ⊕ n) b 𝔪.ResidueRing → ℂ),
      AreMatched ⊤ (.refl (b ⊕ n)) χ⁻¹ Φ Ψ →
      c * stdClassSum (stdLevel E n) (K Φ) =
        ∫ x : G E t, modKernel V' ((stdSpace E b).sum W') a (β * β') 𝔪 Ψ
          (renameRowsCols .inr id P) x (.sum ((1, h'), g)) ∂V'.quotMeasure) :
    Integrable (fun x : G E t ↦
      modKernelStdSpace V' a β 𝔪 (fun y : Matrix b b 𝔪.ResidueRing ↦ χ y.det) 1 x h' *
      modKernel V' W' a β' 𝔪 Ψ' P x g) V'.quotMeasure ∧
    c * stdClassSum (stdLevel E n)
      (K fun x : Matrix n (b ⊕ n) 𝔪.ResidueRing ↦ χ x.toCols₂.det * Ψ' (x.toCols₂⁻¹ * x.toCols₁)) =
      ∫ x : G E t, modKernelStdSpace V' a β 𝔪 (fun y : Matrix b b 𝔪.ResidueRing ↦ χ y.det) 1 x h' *
        modKernel V' W' a β' 𝔪 Ψ' P x g ∂V'.quotMeasure := by
  -- The function matched with `χ (det x'') Ψ' (x''⁻¹ x')` is the product `χ (det y') Ψ' (y'')`, so
  -- its kernel factors along `E^b ⊕ W'`.
  let Ψ (y : Matrix (b ⊕ n) b 𝔪.ResidueRing) : ℂ := χ y.toRows₁.det * Ψ' y.toRows₂
  have h_factor : (fun x ↦ modKernel V' ((stdSpace E b).sum W') a (β * β') 𝔪 Ψ
      (renameRowsCols .inr id P) x (.sum ((1, h'), g))) = fun x : G E t ↦
      modKernelStdSpace V' a β 𝔪 (fun y ↦ χ y.det) 1 x h' * modKernel V' W' a β' 𝔪 Ψ' P x g := by
    simp [Ψ, ← modKernel_sum_right]
  -- The integral converges, as `y'` is invertible on the support.
  have Ψ_supp (y : Matrix (b ⊕ n) b 𝔪.ResidueRing) (hy : Ψ y ≠ 0) : HasLeftInv y :=
    hasLeftInv_of_isUnit_det_toRows₁ (χ.apply_ne_zero_iff.1 (left_ne_zero_of_mul hy))
  rw [← h_factor]
  exact ⟨(isRapid_modKernel V' _ a (β * β') h𝔪 Ψ_supp _ _).integrable (by fun_prop [modKernel]),
    h_exchange _ Ψ (areMatched_det_mul χ hΨ')⟩

/-- One exchange, summed over the classes of `U(E^b)`. Let `V'` and `W'` be hermitian spaces with
bases indexed by `b` and `n` and signs `t` and `s` at the infinite places, with adelic unitary
groups `G E t` and `G E s`; let `E^b` be the standard definite space, `𝔪 ≠ (1)` a modulus and `χ` a
character of `𝒪 / 𝔪`. Suppose that `c₀` times the class sum over the finite points `h'` of `U(E^b)`
of `coef h'` times the theta kernel of `(V', E^b)` at `(x, h')` is `F x`. Suppose that the functions
`K Φ h'` on the finite points of `U(E^n)` satisfy the exchange identity: for matched data `Φ`, `Ψ`
modulo `𝔪` (`AreMatched`), `c` times the class sum of `K Φ h'` is the integral over the automorphic
quotient of `U(V')` of the kernel of `(V', E^b ⊕ W')` with datum `Ψ` and the polynomial `P` in the
variables of `W'`, at the point `.sum ((1, h'), g)` with blocks `h'` (real part `1`) and `g`. Let
`Ψ'` be invariant under right multiplication by `GL_b (𝒪 / 𝔪)`. Then `c c₀` times the class sum over
`h'` of `coef h'` times the class sum of `K Φ h'`, for `Φ (x' x'') = χ (det x'') Ψ' (x''⁻¹ x')`, is
the integral of `F` times the kernel of `(V', W')` at `g` with datum `Ψ'` and polynomial `P`. -/
lemma mul_stdClassSum_eq_integral_mul_modKernel {s : n → ℤˣ} {t : b → ℤˣ} {𝔪 : Modulus E}
    (V' : Space E b t) (W' : Space E n s) {a β β' : AutChar E}
    (h𝔪 : Nonempty 𝔪.places) {χ : MulChar 𝔪.ResidueRing ℂ} {coef : Gf E b → ℂ} {F : G E t → ℂ}
    {c₀ : ℂ} (hF : ∀ x : G E t, c₀ * stdClassSum (stdLevel E b) (fun h' : Gf E b ↦ coef h' *
      modKernelStdSpace V' a β 𝔪 (fun y : Matrix b b 𝔪.ResidueRing ↦ χ y.det) 1 x h') = F x)
    {Ψ' : Matrix n b 𝔪.ResidueRing → ℂ}
    (hΨ' : ∀ (y : Matrix n b 𝔪.ResidueRing) (γ : GL b 𝔪.ResidueRing), Ψ' (y * γ.1) = Ψ' y)
    {P : MvPolynomial (InfinitePlace E × n × b) ℂ} {g : G E s}
    {K : (Matrix n (b ⊕ n) 𝔪.ResidueRing → ℂ) → Gf E b → Gf E n → ℂ} {c : ℂ}
    (h_exchange : ∀ (Φ : Matrix n (b ⊕ n) 𝔪.ResidueRing → ℂ)
      (Ψ : Matrix (b ⊕ n) b 𝔪.ResidueRing → ℂ),
      AreMatched ⊤ (.refl (b ⊕ n)) χ⁻¹ Φ Ψ → ∀ h' : Gf E b,
      c * stdClassSum (stdLevel E n) (K Φ h') =
        ∫ x : G E t, modKernel V' ((stdSpace E b).sum W') a (β * β') 𝔪 Ψ
          (renameRowsCols .inr id P) x (.sum ((1, h'), g)) ∂V'.quotMeasure) :
    c * c₀ * stdClassSum (stdLevel E b) (fun h' : Gf E b ↦ coef h' * stdClassSum (stdLevel E n) (K
        (fun x : Matrix n (b ⊕ n) 𝔪.ResidueRing ↦ χ x.toCols₂.det * Ψ' (x.toCols₂⁻¹ * x.toCols₁))
          h')) =
      ∫ x : G E t, F x * modKernel V' W' a β' 𝔪 Ψ' P x g ∂V'.quotMeasure := by
  let θ (h' : Gf E b) (x : G E t) : ℂ :=
    modKernelStdSpace V' a β 𝔪 (fun y ↦ χ y.det) 1 x h' * modKernel V' W' a β' 𝔪 Ψ' P x g
  have h_one (h' : Gf E b) : Integrable (θ h') V'.quotMeasure ∧
      c * stdClassSum (stdLevel E n) (K (fun x : Matrix n (b ⊕ n) 𝔪.ResidueRing ↦
        χ x.toCols₂.det * Ψ' (x.toCols₂⁻¹ * x.toCols₁)) h') = ∫ x, θ h' x ∂V'.quotMeasure :=
    integrable_and_mul_stdClassSum_eq_integral_mul V' W' h𝔪 χ hΨ' (K := (K · h')) fun Φ Ψ hΦΨ ↦
      h_exchange Φ Ψ hΦΨ h'
  have h_mul (x : G E t) : F x * modKernel V' W' a β' 𝔪 Ψ' P x g =
      c₀ * stdClassSum (stdLevel E b) fun h' ↦ coef h' * θ h' x := by
    -- `finsum_eq_sum_of_fintype` must act first, before the summand is rewritten.
    simp [← hF, θ, classSum, ↓finsum_eq_sum_of_fintype, sum_mul, mul_assoc]
  -- The class sum is finite, so it commutes with the integral.
  have h_comm : ∫ x, stdClassSum (stdLevel E b) (fun h' ↦ coef h' * θ h' x) ∂V'.quotMeasure =
      stdClassSum (stdLevel E b) fun h' ↦ coef h' * ∫ x, θ h' x ∂V'.quotMeasure := by
    simp [classSum, ↓finsum_eq_sum_of_fintype, Rat.smul_def, ← mul_assoc, integral_finsetSum,
      Integrable.const_mul, h_one, integral_const_mul]
  simp_rw [h_mul, integral_const_mul, h_comm]
  rw [mul_classSum, mul_classSum]
  congr 1 with h'
  linear_combination c₀ * coef h' * (h_one h').right

/-- Let `V'` and `W'` be hermitian spaces, and let `F` on the adelic unitary group of `V'` be
automorphic, rapidly decreasing (`rapidFunctions`) and right invariant under the full level
`stdLevel`. Let `β'`, the character that twists the action of `U(V')` in the theta kernel of
`(V', W')`, have weight `wt` and trivial tame part (`HasWeight wt 1`); `a` is the other twist. In
the integral of `F` against the kernel over the quotient by rational points (`quotMeasure`), all
right translates `ψ (· γ)` of a datum `ψ` modulo `𝔪` by `γ` in `GL (𝒪 / 𝔪)` give the same value. So
their sum, read modulo a multiple `𝔪'` of `𝔪`, gives the number of the `γ` times the integral for
`ψ`. -/
lemma integral_mul_modKernel_sum_translates {s : n → ℤˣ} {t : b → ℤˣ} {𝔪 : Modulus E}
    (V' : Space E b t) (W' : Space E n s)
    {a β' : AutChar E} {wt : InfinitePlace E → ℤ} (hβ' : β'.HasWeight wt 1) {F : G E t → ℂ}
    (hF : F ∈ V'.rapidFunctions) (hF_level : HasLevel F (stdLevel E b)) {𝔪' : Modulus E}
    (h_le : 𝔪'.ideal ≤ 𝔪.ideal) (ψ : Matrix n b 𝔪.ResidueRing → ℂ)
    (P : MvPolynomial (InfinitePlace E × n × b) ℂ) (g : G E s) :
    ∫ x : G E t, F x * modKernel V' W' a β' 𝔪' (fun y : Matrix n b 𝔪'.ResidueRing ↦
        ∑ γ : GL b 𝔪.ResidueRing, ψ (y.map (factor h_le) * γ.1)) P x g ∂V'.quotMeasure =
      Fintype.card (GL b 𝔪.ResidueRing) *
        ∫ x : G E t, F x * modKernel V' W' a β' 𝔪 ψ P x g ∂V'.quotMeasure := by
  obtain ⟨hF_aut, hF_rapid⟩ := hF
  let I (ψ₀ : Matrix n b 𝔪.ResidueRing → ℂ) (x : G E t) : ℂ := F x * modKernel V' W' a β' 𝔪 ψ₀ P x g
  have I_cont : Continuous (I ψ) := hF_aut.continuous.mul (by fun_prop [modKernel])
  have I_rat : V'.Γ.FixesLeft (I ψ) := fun δ hδ x ↦
    congrArg₂ (· * ·) (hF_aut.rat_mul δ hδ x) ((pairThetaKer V' W' a β').theta_rat_mul δ hδ x)
  have I_rapid : V'.IsRapid (I ψ) := by
    simpa [I, Pi.mul_def, mul_comm, modKernel, pairTheta] using
      hF_rapid.mul ((pairThetaKer V' W' a β').isModerate _ g)
  -- The integrand for `ψ (· γ)` is that for `ψ`, translated by a lift of `γ`.
  have I_translate (γ : GL b 𝔪.ResidueRing) :
      I (fun y ↦ ψ (y * γ.1)) = fun x ↦ I ψ (x * (1, (liftMod γ).1)) := by
    have h_char : (β'.val (detFin t (liftMod γ).1) : ℂ) = 1 := by
      rw [hβ'.apply_det_eq_charOfTamePart (𝔪 := 𝔪) (by simp)]
      exact finprod_eq_one_of_forall_eq_one fun w ↦
        MulChar.one_apply (((isUnit_iff_isUnit_det _).1 (Units.isUnit _)).map _)
    ext x
    simp [I, modKernel_mul_stdLevel_left, h_char, hF_level _ (liftMod γ).2]
  have h_same (γ : GL b 𝔪.ResidueRing) :
      ∫ x, I (fun y ↦ ψ (y * γ.1)) x ∂V'.quotMeasure = ∫ x, I ψ x ∂V'.quotMeasure ∧
      Integrable (I fun y ↦ ψ (y * γ.1)) V'.quotMeasure := by
    simpa [I_translate, I_rapid.integrable I_cont] using
      V'.integral_comp_mul_right (1, (liftMod γ).1) I_rat I_cont
  calc _ = ∫ x, ∑ γ : GL b 𝔪.ResidueRing, I (fun y ↦ ψ (y * γ.1)) x ∂V'.quotMeasure := by
        simp [I, ← modKernel_factor h_le, ← Finset.sum_fn, ← modKernelBilin_apply, mul_sum]
    _ = _ := by simp [integral_finsetSum, h_same, I]

open scoped Classical in
omit [WeilData E] in
/-- The tower property of class sums. Let `f₀` be left invariant under the rational points `Γf` and
right invariant (`rightStabilizer`) under `levelOfSubgroup H`, the elements of the full level
`stdLevel` that reduce modulo `𝔪` into the subgroup `H`, and let `f`, of full level, be the sum of
the right translates of `f₀` by lifts of coset representatives of `H`. Then the class sum of `f₀` at
that level is the class sum of `f` at full level. -/
lemma stdClassSum_tower {𝔪 : Modulus E} (H : Subgroup (GL b 𝔪.ResidueRing)) {f f₀ : Gf E b → ℂ}
    (right_inv : stdLevel E b ≤ rightStabilizer f) (left_inv₀ : (stdSpace E b).Γf.FixesLeft f₀)
    (right_inv₀ : 𝔪.levelOfSubgroup H ≤ rightStabilizer f₀)
    (sum_eq : ∀ h : Gf E b, f h = ∑ q : GL b 𝔪.ResidueRing ⧸ H, f₀ (h * (liftMod q.out).1)) :
    stdClassSum (𝔪.levelOfSubgroup H) f₀ = stdClassSum (stdLevel E b) f := by
  refine .symm ?_
  calc _ = classIntegral (stdSpace E b).Γf (stdLevel E b) f :=
        (classIntegral_eq_classSum right_inv).symm
    _ = ∑ q : GL b 𝔪.ResidueRing ⧸ H, classIntegral (stdSpace E b).Γf (stdLevel E b) f₀ :=
      classIntegral_sum univ (fun _ ↦ .id ℂ) _
        (fun _ ↦ ⟨left_inv₀, isOpen_mono right_inv₀ isOpen⟩) sum_eq
    -- The number of cosets cancels the index of the level.
    _ = _ := by simp [classIntegral_eq_inv_smul_classSum left_inv₀ right_inv₀ le, Rat.smul_def,
        𝔪.stdLevelIndex_levelOfSubgroup, index_eq_card]

/-- The substitution `x_τ ↦ c_τᵀ x_τ` in the columns `j` with `s j = 1` and `x_τ ↦ d_τ x_τ` in the
other columns, on complex polynomials in the entries of `b × n` matrices `x_τ`, one for each
infinite place `τ`. -/
abbrev signedRowSubst (s : n → ℤˣ) (c d : InfinitePlace E → Matrix b b ℂ) :
    MvPolynomial (InfinitePlace E × b × n) ℂ →ₐ[ℂ] MvPolynomial (InfinitePlace E × b × n) ℂ :=
  MvPolynomial.aeval fun ((τ, k, j) : InfinitePlace E × b × n) ↦
    ∑ i : b, (if s j = 1 then c τ i k else d τ k i) • MvPolynomial.X (τ, i, j)

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
omit [WeilData E] in
/-- Let `δ` be a rational point of the unitary group of the standard definite space `E^b`, paired
with a space of signs `s`. Let `polyVector` of a polynomial `P` be its Fock vector
`P (ζ x) exp (-|x|²/2)` for the signs of the pair. The real part of `δ⁻¹` acts on it (by
`realPairWeil γ 0`, the real Weil action twisted by `det ^ γ`) as the substitution
`x_τ ↦ (δ⁻¹)ᵀ x_τ` in the columns of sign `1` and `x_τ ↦ δ x_τ` in those of sign `-1`, times
`∏ τ, (det δ) ^ (q - γ τ)`, where `q` (`negCount s`) is the number of signs `-1`. At the place `τ`,
`δ` is read in the complex embedding `Φ τ` that the CM type chooses. -/
lemma realPairWeil_ratEmbed_inv_polyVector {s : n → ℤˣ} (γ : InfinitePlace E → ℤ)
    (δ : U (stdSpace E b).J) (P : MvPolynomial (InfinitePlace E × b × n) ℂ) :
    realPairWeil (s := s) (s' := 1) γ 0 (1, ((stdSpace E b).ratEmbed δ⁻¹).1)
        (polyVector (realSigns E (homSigns s 1)) P) =
      (∏ τ : InfinitePlace E, Φ τ (δ : Matrix b b E).det ^ ((negCount s : ℤ) - γ τ)) •
        polyVector (realSigns E (homSigns s 1))
          (signedRowSubst s (fun τ : InfinitePlace E ↦ (↑δ⁻¹ : Matrix b b E).map (Φ τ))
            (fun τ : InfinitePlace E ↦ (δ : Matrix b b E).map (Φ τ)) P) := by
  -- The point `(1, u)` is block diagonal (the space `E^b` is definite), so it acts by a
  -- substitution times a character of the vacuum (`realPairWeil_polyVector` with `x = 1`).
  let u : GInf E (1 : b → ℤˣ) := ((stdSpace E b).ratEmbed δ⁻¹).1
  have hu_mat (τ : InfinitePlace E) : (u τ : GL b ℂ).val = (Φ τ).mapMatrix (↑δ⁻¹ : Matrix b b E) :=
    stdSpace_ratEmbed_apply δ⁻¹ τ
  have hu_inv (τ : InfinitePlace E) :
      ((↑(u τ)⁻¹ : GL b ℂ) : Matrix b b ℂ) = (Φ τ).mapMatrix (δ : Matrix b b E) := by
    simp [u, ← stdSpace_ratEmbed_apply δ τ]
  rw [realPairWeil_polyVector γ 0 (y := u) (by simp) (by simp) P]
  simp only [hu_mat, hu_inv]
  congr 1
  · -- The principal minors of the identity, and that of `u` on no rows, are `1`; the one of `u`
    -- on all rows is `det δ⁻¹`.
    simp [negCount, ← RingHom.map_det, -RingHom.mapMatrix_apply, principalMinor_of_forall,
      DiscreteSeries.principalMinor_of_forall_not]
  · simp [Matrix.one_apply, eq_comm (a := (1 : ℤˣ))]

/-- Let `W` be a hermitian space with signs `s`, definite or not. The kernel of `(W, E^b)` is that
of a function `Ψ` on matrices modulo the ideal `𝔪` and a polynomial `P`; the automorphic characters
`α` and `β` twist the actions of `U(E^b)` and `U(W)`. Let `α` have exponents `γ` at the infinite
places, and let `δ` be a rational point of `U(E^b)`. The kernel at the adelic point `g` and the
finite point `δ h` is `∏ τ, (det δ) ^ (q - γ τ)`, with `q` the number of signs `-1`, times the
kernel at `(g, h)` of the polynomial obtained from `P` by `x_τ ↦ (δ⁻¹)ᵀ x_τ` in the columns of sign
`1` and `x_τ ↦ δ x_τ` in those of sign `-1`. -/
lemma modKernelStdSpace_stdEmbFin_mul {s : n → ℤˣ} {𝔪 : Modulus E} {α β : AutChar E}
    {γ : InfinitePlace E → ℤ} {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ}
    (hα : α.HasWeight γ ψ) (W : Space E n s)
    (Ψ : Matrix b n 𝔪.ResidueRing → ℂ) (P : MvPolynomial (InfinitePlace E × b × n) ℂ)
    (δ : U (stdSpace E b).J) (g : G E s) (h : Gf E b) :
    modKernelStdSpace W α β 𝔪 Ψ P g (stdEmbFin δ * h) =
      (∏ τ : InfinitePlace E, Φ τ (δ : Matrix b b E).det ^ ((negCount s : ℤ) - γ τ)) *
        modKernelStdSpace W α β 𝔪 Ψ
          (signedRowSubst s (fun τ : InfinitePlace E ↦ (↑δ⁻¹ : Matrix b b E).map (Φ τ))
            (fun τ : InfinitePlace E ↦ (δ : Matrix b b E).map (Φ τ)) P) g h := by
  -- The kernel is invariant under the rational point `δ⁻¹`. It cancels the finite translation and
  -- leaves the real part `u` of `δ⁻¹`, which acts on the Fock vector alone.
  let T : Space E b 1 := stdSpace E b
  let u : GInf E (1 : b → ℤˣ) := (T.ratEmbed δ⁻¹).1
  let c : ℂ := ∏ τ : InfinitePlace E, Φ τ (δ : Matrix b b E).det ^ ((negCount s : ℤ) - γ τ)
  let Q : MvPolynomial (InfinitePlace E × b × n) ℂ :=
    signedRowSubst s (fun τ : InfinitePlace E ↦ (↑δ⁻¹ : Matrix b b E).map (Φ τ))
      (fun τ : InfinitePlace E ↦ (δ : Matrix b b E).map (Φ τ)) P
  have h_point : T.ratEmbed δ⁻¹ * (1, stdEmbFin δ * h) = (u, h) :=
    Prod.ext (by simp [u, T]) (by simp [T, embFin])
  have h_split : ((g, u, h) : G E s × G E _) = (g, 1, h) * (1, u, 1) := by simp [Prod.mul_def]
  have h_inv (f : 𝒮 (W.hom T)) :
      pairTheta W T α β f (g, 1, stdEmbFin δ * h) = pairTheta W T α β f (g, u, h) := by
    simpa [← h_point, pairTheta] using
      ((pairThetaKer W T α β).rat_mul (one_mem _) ⟨δ⁻¹, rfl⟩ g (1, stdEmbFin δ * h) f).symm
  calc modKernelStdSpace W α β 𝔪 Ψ P g (stdEmbFin δ * h)
      = pairTheta W T α β (modDatum W T 𝔪 Ψ (polyVector _ P)) (g, u, h) := h_inv _
    _ = pairTheta W T α β
          (modDatum W T 𝔪 Ψ (realPairWeil γ 0 (1, u) (polyVector _ P))) (g, 1, h) := by
        rw [h_split, pairTheta_mul, modDatum, modDatum, pairWeil_integrated_right α β (ha := hα) u]
    -- `u` substitutes in `P` and multiplies it by `c`, and the kernel is linear in the Fock vector.
    _ = c * modKernelStdSpace W α β 𝔪 Ψ Q g h := by
      rw [realPairWeil_ratEmbed_inv_polyVector]
      simp [modKernelStdSpace, modKernel, modDatum, pairTheta, T, c, Q]

/-- Consider the theta kernel `modKernelStdSpace` of a hermitian space `W` and the standard definite
space `E^b`, for a function `Ψ` on matrices modulo the ideal `𝔪`, a polynomial `P` and automorphic
characters `α`, `β` that twist the actions of `U(E^b)` and `U(W)`, at an adelic point `g` of `U(W)`.
Let `α` be tame for `𝔪` (`IsTameFor`): `𝔪 ≠ (1)`, `α` has exponents `γ` at the infinite places, and
its residue characters are nontrivial exactly at the primes dividing `𝔪`, with product `χ` on
`𝒪 / 𝔪`. Let the Fock vector of `P` be fixed by the real group of `E^b`. Then the kernel, as a
function of the finite point of `U(E^b)`, is left invariant under the rational points. -/
lemma fixesLeft_modKernelStdSpace {s : n → ℤˣ} {𝔪 : Modulus E} {α β : AutChar E}
    {γ : InfinitePlace E → ℤ} {χ : MulChar 𝔪.ResidueRing ℂ}
    {P : MvPolynomial (InfinitePlace E × b × n) ℂ} {g : G E s}
    {W : Space E n s} (hα : IsTameFor 𝔪 α γ χ)
    (hP : ∀ u : GInf E (1 : b → ℤˣ), realPairWeil (s := s) (s' := 1) γ 0 (1, u)
      (polyVector (realSigns E (homSigns s 1)) P) = polyVector (realSigns E (homSigns s 1)) P)
    (Ψ : Matrix b n 𝔪.ResidueRing → ℂ) :
    (stdSpace E b).Γf.FixesLeft (modKernelStdSpace W α β 𝔪 Ψ P g) := by
  rintro _ ⟨δ, rfl⟩ h
  obtain ⟨-, ψ, h_weight, -⟩ := hα
  -- Moving `h` by `δ` replaces `P` by `c • Q`, and `c • Q = P` by `hP` at the real part of `δ⁻¹`.
  let c : ℂ := ∏ τ : InfinitePlace E, Φ τ (δ : Matrix b b E).det ^ ((negCount s : ℤ) - γ τ)
  let Q : MvPolynomial (InfinitePlace E × b × n) ℂ :=
    signedRowSubst s (fun τ : InfinitePlace E ↦ (↑δ⁻¹ : Matrix b b E).map (Φ τ))
      (fun τ : InfinitePlace E ↦ (δ : Matrix b b E).map (Φ τ)) P
  have h_fixed : c • Q = P := polyVector_injective (ε := realSigns E (homSigns s 1)) <| by
    rw [map_smul, ← realPairWeil_ratEmbed_inv_polyVector, hP]
  calc modKernelStdSpace W α β 𝔪 Ψ P g (stdEmbFin δ * h)
      = c * modKernelStdSpace W α β 𝔪 Ψ Q g h :=
        modKernelStdSpace_stdEmbFin_mul h_weight W Ψ P δ g h
    _ = modKernelStdSpace W α β 𝔪 Ψ (c • Q) g h := by simp [← modKernelBilin_apply]
    _ = modKernelStdSpace W α β 𝔪 Ψ P g h := by rw [h_fixed]

/-- Let the automorphic character `α` be tame for the ideal `𝔪` (`IsTameFor`): `𝔪 ≠ (1)`, `α` has
exponents `γ` at the infinite places, and its residue characters are nontrivial exactly at the
primes dividing `𝔪`, with product `χ` on `𝒪 / 𝔪`. Let `β` be the second twisting character, and let
the Fock vector of the polynomial `P` be fixed by the real group of the standard definite space
`E^b`. Let `F` be left invariant under the group `H` (`rowStabilizer`) of the invertible `A` modulo
`𝔪` with `w · φ(A) = w` and the columns of `1` off `e`. Write `x = (x′ | x″)`. Then the class sum at
full level of the kernel with datum `χ (det x″) F (x″⁻¹ x′)` equals the class sum, at the level
`levelOfSubgroup H` of the elements that reduce modulo `𝔪` into `H`, of the kernel with this datum
restricted to `x″` in `H`. With `σ` the columns `e` of `x″`, the restricted datum is
`columnDatum χ φ w e σ` times `F x′` if `x″` has the columns of `1` off `e`; else it is 0. -/
lemma stdClassSum_rowStabilizer_eq {𝔪 : Modulus E} {r c S : Type} [Fintype r] [DecidableEq r]
    [CommRing S] {ε : n ⊕ b → ℤˣ} {α β : AutChar E} {γ : InfinitePlace E → ℤ}
    {χ : MulChar 𝔪.ResidueRing ℂ}
    {P : MvPolynomial (InfinitePlace E × b × (n ⊕ b)) ℂ} {g : G E ε} {W : Space E (n ⊕ b) ε}
    (hα : IsTameFor 𝔪 α γ χ)
    (hP : ∀ u : GInf E (1 : b → ℤˣ), realPairWeil (s := ε) (s' := 1) γ 0 (1, u)
      (polyVector (realSigns E (homSigns ε 1)) P) = polyVector (realSigns E (homSigns ε 1)) P)
    (φ : 𝔪.ResidueRing →+* S) (w : Matrix c b S) (e : r ↪ b) {F : Matrix b n 𝔪.ResidueRing → ℂ}
    (hF : ∀ A ∈ rowStabilizer φ w e, ∀ y : Matrix b n 𝔪.ResidueRing, F (A.val * y) = F y) :
    stdClassSum (𝔪.levelOfSubgroup (rowStabilizer φ w e))
        (modKernelStdSpace W α β 𝔪 (fun x : Matrix b (n ⊕ b) 𝔪.ResidueRing ↦
          columnDatum χ φ w e (x.toCols₂.submatrix id e) *
            if FixesColsOff e x.toCols₂ then F x.toCols₁ else 0) P g) =
      stdClassSum (stdLevel E b) (modKernelStdSpace W α β 𝔪
        (fun x : Matrix b (n ⊕ b) 𝔪.ResidueRing ↦
        χ x.toCols₂.det * F (x.toCols₂⁻¹ * x.toCols₁)) P g) := by
  classical
  -- With x = (x′ | x″), the datum `Φ₀` on the left is `Φ` cut down to x″ ∈ `H`. The twisted
  -- translates of `Φ₀` by coset representatives of `H` add up to `Φ`, and their kernels are
  -- right translates of the kernel of `Φ₀`.
  let H : Subgroup (GL b 𝔪.ResidueRing) := rowStabilizer φ w e
  let Φ (x : Matrix b (n ⊕ b) 𝔪.ResidueRing) : ℂ := χ x.toCols₂.det * F (x.toCols₂⁻¹ * x.toCols₁)
  let Φ₀ (x : Matrix b (n ⊕ b) 𝔪.ResidueRing) : ℂ :=
    columnDatum χ φ w e (x.toCols₂.submatrix id e) *
    if FixesColsOff e x.toCols₂ then F x.toCols₁ else 0
  let θ (Ψ : Matrix b (n ⊕ b) 𝔪.ResidueRing → ℂ) : Gf E b → ℂ := modKernelStdSpace W α β 𝔪 Ψ P g
  let tr (A : GL b 𝔪.ResidueRing) (Ψ : Matrix b (n ⊕ b) 𝔪.ResidueRing → ℂ) :
      Matrix b (n ⊕ b) 𝔪.ResidueRing → ℂ := χ A.1.det • fun x ↦ Ψ (A⁻¹.1 * x)
  -- Right translation of the kernel by `k` is the twisted translation of the datum.
  have θ_tr (Ψ : Matrix b (n ⊕ b) 𝔪.ResidueRing → ℂ) (k : stdLevel E b) (h : Gf E b) :
      θ Ψ (h * k.1) = θ (tr (𝔪.reductionGL k) Ψ) h := by
    simp only [θ, tr, ↓modKernel_mul_stdLevel_right, hα.apply_det]
  -- The twist cancels the factor χ(det A)⁻¹ that the translation adds to χ(det x″).
  have tr_Φ (A : GL b 𝔪.ResidueRing) : tr A Φ = Φ := by
    ext x
    rw [← x.fromCols_toCols]
    generalize x.toCols₂ = y
    rcases em (IsUnit y) with ⟨Y, rfl⟩ | hy
    · simp [tr, Φ, ← mul_assoc (χ _), ← map_mul, ← det_mul, Matrix.mul_inv_rev, Matrix.mul_assoc]
    · simp [tr, Φ, χ.map_nonunit ((isUnit_iff_isUnit_det y).not.1 hy)]
  have Φ₀_eq (x : Matrix b (n ⊕ b) 𝔪.ResidueRing) :
      Φ₀ x = if ∃ Z ∈ H, Z.1 = x.toCols₂ then Φ x else 0 := by
    convert columnDatum_mul_ite_eq_ite_mem_rowStabilizer χ φ w e hF x.toCols₁ x.toCols₂
  have tr_Φ₀ (A : GL b 𝔪.ResidueRing) (x : Matrix b (n ⊕ b) 𝔪.ResidueRing) :
      tr A Φ₀ x = if ∃ Z : GL b 𝔪.ResidueRing, A⁻¹ * Z ∈ H ∧ Z.1 = x.toCols₂ then Φ x else 0 := by
    have shift : (∃ Z ∈ H, Z.1 = A⁻¹.1 * x.toCols₂) ↔ ∃ Z, A⁻¹ * Z ∈ H ∧ Z.1 = x.toCols₂ :=
      (Equiv.mulLeft A).exists_congr fun Z ↦ by simp [← Units.eq_inv_mul_iff_mul_eq]
    rw [← tr_Φ A, ← x.fromCols_toCols]
    simp only [tr, Pi.smul_apply, Φ₀_eq, smul_ite, smul_zero, mul_fromCols, toCols₂_fromCols, shift]
  -- An invertible x″ lies in exactly one coset; at any other x″ all terms vanish.
  have Φ_eq : Φ = ∑ q : GL b 𝔪.ResidueRing ⧸ H, tr q.out Φ₀ := funext fun x ↦ by
    rcases em (IsUnit x.toCols₂) with ⟨y, hy⟩ | hx
    · simp [tr_Φ₀, ← hy, -coe_units_inv, Units.val_inj, ← QuotientGroup.eq]
    · simp [tr_Φ₀, Φ, χ.map_nonunit ((isUnit_iff_isUnit_det _).not.1 hx)]
  have right_inv : stdLevel E b ≤ rightStabilizer (θ Φ) :=
    fun k hk h ↦ by simpa [tr_Φ] using θ_tr Φ ⟨k, hk⟩ h
  have right_inv₀ : 𝔪.levelOfSubgroup H ≤ rightStabilizer (θ Φ₀) := by
    rintro _ ⟨k, hk, rfl : k.1 = _⟩ h
    rw [θ_tr]
    congr with x
    simp only [tr_Φ₀, Φ₀_eq, H.mul_mem_cancel_left (inv_mem hk)]
  have θ_sum (h : Gf E b) : θ Φ h = ∑ q : GL b 𝔪.ResidueRing ⧸ H, θ Φ₀ (h * (liftMod q.out).1) := by
    simp [θ_tr, Φ_eq, θ, ← modKernelBilin_apply]
  exact stdClassSum_tower H right_inv (fixesLeft_modKernelStdSpace hα hP Φ₀) right_inv₀ θ_sum

end New.Rows

end
