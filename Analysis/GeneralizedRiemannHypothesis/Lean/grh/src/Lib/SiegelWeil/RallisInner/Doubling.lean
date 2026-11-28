import Lib.SiegelWeil.Formula.WeilRange
import Lib.SiegelWeil.UnramifiedSeries.VacuumCoefficients

/-!
# Doubling: clean data, the doubling identity and the inner product formula

This file defines the doubled datum `New.SiegelWeil.doubleDatum` on `Hom(S ⊕ S⁻, T)`, clean data
(`New.SiegelWeil.IsClean`) and sharp data (`New.SiegelWeil.IsSharp`), for hermitian spaces `S`,
`T` of ranks `n`, `m`. It applies Siegel–Weil to `S ⊕ S⁻` to prove the doubling identity for
`2 n < m`. It then integrates that identity to the inner product formula before the choice of a
sharp datum. It also computes the coefficient of a vacuum at points supported above a set of
places (`New.SiegelWeil.weilMatrixCoeff_mul`) and constructs an integral isotropic frame.
Conventions: `New.G E s` is the adelic unitary group, a pair of an archimedean and a finite part;
`New.pairWeil S T a b` is the twisted Weil representation of `U(S) × U(T)` on the data
`𝒮 (S.hom T)`, with inner product `New.Space.dataInner`; `New.localLevel n A` consists of the
finite points that are integral at the places of `A`, and `New.stdLevel E n` of those integral at
all places, the stabiliser of `Ô ^ n`.

## Main definitions and results

* `New.SiegelWeil.integral_conj_theta_mul_theta`: the doubling identity for `2 n < m`:
  apply Siegel–Weil (`New.SiegelWeil.siegel_weil`) to `S ⊕ S⁻`; for a clean datum
  (`New.SiegelWeil.IsClean`) only the Lagrangians that are graphs of isometries contribute
  (`New.SiegelWeil.exists_graph_eq_of_zeroTerm_ne_zero`, `New.SiegelWeil.zeroTerm_graphSplitting`).
* `New.SiegelWeil.inner_product_formula`: Rallis' inner product formula, obtained by integrating
  the doubling identity against two functions on `[U(S)]`.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by signs s, a matrix J over E and x in GL_n(𝔸)
  with xᴴJx equal to diag(s) at the infinite places and 1 at the finite places.
* `New.SiegelWeil.Lagrangian.zeroTerm`: the term of a Lagrangian L in the Siegel–Weil formula, the
  value at 0 in the Schrödinger model of a complete splitting along L.
* `New.Space.projOn`: the mean of the finite Heisenberg operators of the integral vectors above a
  set A of places and its conjugate; the data that it fixes are the vacua above A.

## Relation to the literature

Rallis inner product formula by doubling. Here only Weil's range is treated, with forms that are
rapidly decreasing rather than cuspidal. The boundary orbits are removed by the test datum. Source:
S. Rallis, L-functions and the oscillator representation, LNM 1245 (1987); J.-S. Li, Crelle 428
(1992); the unitary unfolding is written out in Y. Liu (2011) Prop 2.3 and
Eischen–Harris–Li–Skinner 4.1.4.
-/

noncomputable section

section InnerProductFormula

open Matrix MeasureTheory Filter ComplexConjugate Kronecker

namespace New.SiegelWeil

open WeilData Fintype Space Prod Lagrangian G Splitting Gf stdLattice Valued

variable {E n m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m] {s : n → ℤˣ} {t : m → ℤˣ} {S : Space E n s} {T : Space E m t}

/-- A chosen number `c` of modulus one with `θ (c • conj f) = conj (θ f)` for all data `f` on
`Hom(S, T)`, where `conj f = negSource.map f` is the transport of `f` to `Hom(S⁻, T)`; see
`norm_negSourceFactor` and `theta_negSourceFactor_smul`. -/
def negSourceFactor (S : Space E n s) (T : Space E m t) : ℂ := (exists_theta_negSource S T).choose

lemma norm_negSourceFactor (S : Space E n s) (T : Space E m t) : ‖negSourceFactor S T‖ = 1 :=
  (exists_theta_negSource S T).choose_spec.1

/-- The theta functional of `S⁻, T` at the transport of `f`, multiplied by `negSourceFactor S T`,
is the complex conjugate of the theta functional of `S, T` at `f`. -/
lemma theta_negSourceFactor_smul (f : 𝒮 (S.hom T)) :
    θ (S.neg.hom T) (negSourceFactor S T • negSource.map (V := S.neg.hom T) f) =
      conj (θ (S.hom T) f) :=
  (exists_theta_negSource S T).choose_spec.2 f

/-- The doubling map sending `(f', f)` to the datum `f ⊠ c • conj f'` on `Hom(S ⊕ S⁻, T)`,
conjugate-linear in `f'` and linear in `f`. Here `conj f' = negSource.map f'` is the transport of
`f'` to `Hom(S⁻, T)`, and `c = negSourceFactor S T`, so that `θ (c • conj f') = conj (θ f')`. -/
def doubleDatum : 𝒮 (S.hom T) →L⋆[ℂ] 𝒮 (S.hom T) →L[ℂ] 𝒮 ((S.sum S.neg).hom T) :=
  (Space.boxProd homSigns_sum_source).flip.comp
    (negSourceFactor S T • negSource.map (V := S.neg.hom T))

/-- For a rational isometry `δ` of `S`, the splitting of `S ⊕ S⁻` into hyperbolic planes whose
Lagrangian is the graph `{(δ y, -y)}`; the dual frame spans `{(δ y, y)}`. Here `k` is the isotropic
frame, `l` the dual frame (`lᴴ J k = 1`), and the anisotropic part `i` is empty. -/
@[simp]
def graphSplitting (S : Space E n s) (δ : U S.J) : CompleteSplitting (S.sum S.neg) n where
  k := fromRows δ (-1)
  l := fromRows (δ : Matrix n n E) 1 * (2⁻¹ : E) • S.J⁻¹
  i := 0
  gram_kk := by
    simp [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows, ← U.form_mul_inv_eq, mul_assoc]
  gram_ll := by
    simp [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows, ← U.form_mul_inv_eq, S.isHermitian_J.inv.eq, mul_assoc]
  gram_lk := by
    simp [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
      fromCols_mul_fromRows, ← U.form_mul_inv_eq, S.isHermitian_J.inv.eq, ← two_smul E, mul_assoc]
  gram_ii := by ext ⟨⟩
  gram_ik := by simp
  gram_il := by simp
  card_eq := by simp [two_mul]

/-- The term `ρ(g) ⟨y', g y⟩` of a coset `γ` of the finite points integral at `A`. Here
`g = cosetRep γ` is the representative of `γ` supported above `A` and its conjugate,
`ρ = vacuumCoeff M b`, and `y'`, `y` are forms of type `e` on `S`, on which `g` acts by right
translation. -/
def cosetTerm (M : ℕ) (b : AutChar E) (A : Set (FinPlace E)) {e : GInf E s → ℂ} (y' y : S.Form e)
    (γ : Gf E n ⧸ localLevel n A) : ℂ :=
  vacuumCoeff M b (cosetRep γ : Gf E n) * inner ℂ y' (S.formRep e (cosetRep γ) y)

/-- The matrix coefficient `g ↦ ⟨f', ω(g, 1) f⟩` of the twisted Weil representation
`ω = pairWeil S T 1 b`. The argument `f'` defaults to `f`: `weilMatrixCoeff b f` is the function
`g ↦ weilMatrixCoeff b f f g`. -/
abbrev weilMatrixCoeff (b : AutChar E) (f : 𝒮 (S.hom T)) (f' : 𝒮 (S.hom T) := f) (g : G E s) : ℂ :=
  dataInner (S.hom T) f' (pairWeil S T 1 b (g, 1) f)

/-- The datum `F` is clean: (a) all signs of `S` agree, or (b) `F` is a datum
`Ψ ⊗ f = (S.hom T).schrodingerOp A Ψ f`, where `A` is a set of places disjoint from its conjugate,
`Ψ` is Schwartz–Bruhat above `A`, and at some place `w` every matrix `y` with `Ψ y ≠ 0` has a left
inverse. In both cases the only Lagrangians with a nonzero term are graphs
(`New.SiegelWeil.exists_graph_eq_of_zeroTerm_ne_zero`). -/
def IsClean (F : 𝒮 (S.hom T)) : Prop :=
  (∀ i j : n, s i = s j) ∨
  ∃ (A : Set (FinPlace E)) (Ψ : (m × n → 𝔸f E) → ℂ) (w : FinPlace E) (f : 𝒮 (S.hom T)),
    A.IsConjDisjoint ∧ IsSchwartzBruhat A Ψ ∧
    (∀ y : m × n → 𝔸f E, Ψ y ≠ 0 → HasLeftInv ((vecToMatrix y).map (evalAt w))) ∧
    F = (S.hom T).schrodingerOp A Ψ f

open scoped Classical in
/-- The datum `F` of the finite part is sharp for the level `J` off `S₀`. With `K₀ = stdLevel E n`
the stabiliser of `Ô ^ n`, at the finite points `g` integral off `S₀` the coefficient `⟨F, ω(g) F⟩`
equals `⟨F, F⟩` if `g ∈ J ∩ K₀` and is zero otherwise, and the quotient of `⟨F, F⟩` by the index
`[K₀ : J ∩ K₀]` is the constant `c`. Also `⟨F, F⟩ ≠ 0`, and for each vector `v` of the Fock model
the datum `v ⊗ F = integrated (S.hom T) v F` is clean and a vacuum off `S₀`. The datum `Ψ ⊗ vac` of
a sharp function `Ψ` modulo `𝔪` has these properties if `𝔪 ≠ (1)` or all signs of `S` agree
(`New.SiegelWeil.IsSharpFn.isSharp`). -/
structure IsSharp (b : AutChar E) (S₀ : Set (FinPlace E)) (F : 𝒮 (S.hom T)) (J : Subgroup (Gf E n))
    (c : ℂ) : Prop where
  /-- The inner product `⟨F, F⟩` is not zero. -/
  self_ne_zero : dataInner (S.hom T) F F ≠ 0
  /-- The datum `F` lies in the finite part, the span of the finite translates of the vacuum. -/
  mem_finitePart : F ∈ finitePart (S.hom T)
  /-- For every `v`, the datum `v ⊗ F` is a vacuum above any set `A` of places disjoint from
  `S₀`. -/
  vacuum_off (A : Set (FinPlace E))
    (v : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns E (homSigns s t)))) :
    Disjoint S₀ A → projOn (S.hom T) A (integrated (S.hom T) v F) = integrated (S.hom T) v F
  /-- At the finite points `g` integral off `S₀`, the coefficient `⟨F, ω(g) F⟩` is `⟨F, F⟩` on
  `J ∩ stdLevel E n` and zero elsewhere. -/
  weilMatrixCoeff_eq : ∀ g ∈ localLevel n S₀ᶜ,
    weilMatrixCoeff b F F g = if g ∈ J ⊓ stdLevel E n then dataInner (S.hom T) F F else 0
  /-- The quotient of `⟨F, F⟩` by the index `stdLevelIndex J = [K₀ : J ∩ K₀]` is `c`. -/
  mass_eq : dataInner (S.hom T) F F / stdLevelIndex J = c
  /-- For every `v`, the datum `v ⊗ F` is clean (`IsClean`). -/
  clean (v : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns E (homSigns s t)))) :
    IsClean (integrated (S.hom T) v F)

lemma doubleDatum_apply (f f' : 𝒮 (S.hom T)) :
    doubleDatum f' f = boxProd homSigns_sum_source f
      (negSourceFactor S T • negSource.map (V := S.neg.hom T) f') := rfl

/-- The theta functional of `S ⊕ S⁻, T` at the doubled datum is `conj (θ f') * θ f`. -/
lemma theta_doubleDatum (f f' : 𝒮 (S.hom T)) :
    θ ((S.sum S.neg).hom T) (doubleDatum f' f) = conj (θ (S.hom T) f') * θ (S.hom T) f := by
  rw [doubleDatum_apply, theta_boxProd_source, theta_negSourceFactor_smul, mul_comm]

/-- The Heisenberg operator of a map on `S ⊕ S⁻` with blocks `X`, `Y` moves the first factor of
`f ⊠ f'` by `X` and the second by `Y`. -/
lemma rho_fromCols_boxProd (f : 𝒮 (S.hom T)) (f' : 𝒮 (S.neg.hom T)) (X Y : Matrix m n (𝔸 E)) :
    ((S.sum S.neg).hom T).ϱ (matrixToVec (fromCols X Y)) (boxProd homSigns_sum_source f f') =
      boxProd homSigns_sum_source ((S.hom T).ϱ (matrixToVec X) f)
        ((S.neg.hom T).ϱ (matrixToVec Y) f') :=
  rho_boxProd ..

/-- The value of the doubled datum `doubleDatum f' f` at a map on `S ⊕ S⁻` with blocks `X`, `Y` is
the value of `f` at `X` times the conjugate value of `f'` at `u⁻¹ Y`. Here `u = normNegOneIdele E`
is the idele by which the point of `S⁻` differs from the point of `S`. -/
lemma doubleDatum_apply_fromCols (f f' : 𝒮 (S.hom T)) (X Y : Matrix m n (𝔸 E)) :
    doubleDatum f' f (matrixToVec (fromCols X Y)) =
      f (matrixToVec X) * conj (f' ((normNegOneIdele E)⁻¹ • matrixToVec Y)) := by
  have h_neg : (negSource (E := E) (s := s) (s' := t)).φ (matrixToVec Y) =
      (normNegOneIdele E)⁻¹ • matrixToVec Y := rfl
  -- The value at a vector is `θ` of the translate, and `θ` is multiplicative on `⊠`.
  rw [doubleDatum_apply, ← theta_rho, rho_fromCols_boxProd, theta_boxProd_source, map_smul,
    ← CoordChange.map_rho, theta_negSourceFactor_smul, theta_rho, theta_rho, h_neg]

/-- The Heisenberg operator of a map on `S ⊕ S⁻` that vanishes on `S⁻` moves only the factor `f` of
`doubleDatum f' f`. -/
lemma rho_fromCols_zero_doubleDatum (f f' : 𝒮 (S.hom T)) (X : Matrix m n (𝔸 E)) :
    ((S.sum S.neg).hom T).ϱ (matrixToVec (fromCols X 0)) (doubleDatum f' f) =
      doubleDatum f' ((S.hom T).ϱ (matrixToVec X) f) := by
  simp [doubleDatum_apply, rho_fromCols_boxProd]

/-- For a rational isometry `δ` of `S`, the zero term of the Siegel–Weil formula along the graph of
`δ`, taken at the doubled datum `doubleDatum f' f`, is the matrix coefficient `⟨f', ω(δ⁻¹, 1) f⟩`
of the Weil representation `ω = pairWeil S T 1 b` twisted by the character `b`. -/
lemma zeroTerm_graphSplitting (b : AutChar E) (δ : U S.J) (f f' : 𝒮 (S.hom T)) :
    (graphSplitting S δ).lagrangian.zeroTerm T (doubleDatum f' f) =
      weilMatrixCoeff b f f' (S.ratEmbed δ⁻¹) := by
  -- Both sides are means over the adelic vectors modulo the rational ones: the left one by the
  -- formula for the zero term, the right one after the change of variables `P`.
  let P : Matrix (m × n) (m × n) (𝔸 E) := (S.hom T).x⁻¹.val * (T.J⁻¹ ⊗ₖ S.Jᵀ).map toAdele
  have hP_rat : ∀ x ∈ ratVectors E (m × n), P.toLin' x ∈ (S.hom T).ratVectors := by
    simp +contextual [P, map_mulVec_mem_ratVectors, mem_ratVectors_iff]
  have hP_unit : IsUnit P := by
    have hT : IsUnit (T.x⁻¹.val * T.J⁻¹.map toAdele) := by simp [map_J_inv]
    have hS : IsUnit (S.J.map toAdele * S.x.val)ᵀ := by simp [isUnit_transpose, S.map_J]
    simp only [P, hom_point_inv_mul_kronecker]
    exact (kroneckerGL hT.unit hS.unit).isUnit
  have h_per : IsContPeriodic (S.hom T).ratVectors fun x : m × n → 𝔸 E ↦
      pairWeil S T 1 b (S.ratEmbed δ⁻¹, 1) f x * conj (f' x) := by
    obtain ⟨h_invariant, -⟩ := (S.hom T).isThetaFunctional_rawTheta
    apply h_invariant.isContPeriodic h_invariant
  rw [weilMatrixCoeff, dataInner_eq_quotMean, zeroTerm_lagrangian_eq_theta, theta_apply,
    Splitting.zeroTerm_apply, ← quotMean_comp (ratVectors E (m × n)) P.toLin' h_per hP_rat
      (mulVec_surjective_iff_isUnit.2 hP_unit)]
  -- It remains to compare the integrands at `x`. Let `M` be the matrix of `P *ᵥ x`.
  congr! with x
  let M : Matrix m n (𝔸 E) := vecToMatrix (P *ᵥ x)
  have h_frame : ((graphSplitting S δ).homSource T).kAdelic *ᵥ x =
      matrixToVec (fromCols (M * (S.ratEmbed δ⁻¹).adeleMatrix) (normNegOneIdele E • M)) := by
    dsimp only [M, P, kAdelic, homSource, graphSplitting]
    simp_rw [hom_point_inv_mul_kronecker, kronecker_mulVec_eq_matrixToVec, adeleMatrix_ratEmbed]
    simp [Space.sum, Space.neg, ← U.form_mul_inv_eq, Matrix.mul_assoc,
      conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks, fromCols_map]
  have h_rat : pairWeil S T 1 b (S.ratEmbed δ⁻¹, 1) f (P *ᵥ x) =
      f (matrixToVec (M * (S.ratEmbed δ⁻¹).adeleMatrix)) := by
    rw [pairWeil_of_mem_Gamma S T 1 b ⟨δ⁻¹, rfl⟩ (one_mem _), kronecker_mulVec_eq_matrixToVec]
    simp [M]
  have h_scale : (normNegOneIdele E)⁻¹ • matrixToVec (normNegOneIdele E • M) = P *ᵥ x :=
    inv_smul_smul (normNegOneIdele E) (P *ᵥ x)
  rw [mulVec_zero, zero_add, h_frame, doubleDatum_apply_fromCols, h_scale, ← h_rat]
  rfl

/-- Let the isotropic frame of a complete splitting `D` of `S ⊕ S⁻` have blocks `K` (in `S`) and
`K'` (in `S⁻`), and let `K' c = 0`, so that the columns of `K c` are vectors of `S` in the
Lagrangian of `D`. Then the zero term at `doubleDatum f' f` does not change when `f` is moved by the
Heisenberg operator of `X⁻¹ Z Yᴴ ε`, where `Z` is any adelic matrix, `X` is the dual frame of `T`,
`Y` holds the adelic coordinates of `K c` and `ε` is the standard form. -/
lemma zeroTerm_doubleDatum_rho {p : Type} [Fintype p] [DecidableEq p]
    (D : CompleteSplitting (S.sum S.neg) p) {K K' : Matrix n p E} (hk : D.k = fromRows K K')
    {c : Matrix p n E} (hc : K' * c = 0) (Z : Matrix m n (𝔸 E)) (f f' : 𝒮 (S.hom T)) :
    D.lagrangian.zeroTerm T (doubleDatum f' ((S.hom T).ϱ
        (matrixToVec (T.dualFrame⁻¹.val * Z * ((S.coordMatrix 1 (K * c))ᴴ * stdForm E s))) f)) =
      D.lagrangian.zeroTerm T (doubleDatum f' f) := by
  -- The map on `S ⊕ S⁻` attached to `c` is the pairing with `K * c` on `S` and zero on `S⁻`.
  have h_block : (c.map toAdele)ᴴ * D.lCoord =
      fromCols ((S.coordMatrix 1 (K * c))ᴴ * stdForm E s) 0 := by
    simp [lCoord, kAdelic, ← map_inv, hk, hc, Space.sum, ← stdForm_sum, ← (c.map _)ᴴ.mul_assoc,
      ← conjTranspose_mul, ← Matrix.map_mul, -conjTranspose_map_toAdele, Matrix.mul_assoc,
      coordMatrix, fromRows_map, fromBlocks_mul_fromRows,
      conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks]
  have h_along : (D.homSource T).kAdelic *ᵥ matrixToVec (Z * (c.map toAdele)ᴴ) = matrixToVec
    (fromCols
      (T.dualFrame⁻¹.val * Z * ((S.coordMatrix 1 (K * c))ᴴ * stdForm E s)) 0) := by
    rw [homSource_kAdelic, kronecker_mulVec_eq_matrixToVec]
    simp [h_block, Matrix.mul_assoc, -conjTranspose_map_toAdele]
  rw [← rho_fromCols_zero_doubleDatum, ← h_along, zeroTerm_lagrangian_eq_theta,
    zeroTerm_lagrangian_eq_theta, zeroTerm_rho_kAdelic]

/-- Moving the Heisenberg operator of `shiftMatrix s X Y *ᵥ z = X z Yᴴ ε` (`ε` the standard form)
through the Weil operator `pairWeil S T a b (g, 1)` turns the adelic coordinates
`Y = S.coordMatrix g c` of a rational matrix `c` at `g` into its coordinates at `1`. -/
lemma pairWeil_rho_shiftMatrix (a b : AutChar E) (g : G E s) (X : Matrix m m (𝔸 E))
    (c : Matrix n n E) (z : m × n → 𝔸 E) (f : 𝒮 (S.hom T)) :
    pairWeil S T a b (g, 1) ((S.hom T).ϱ (shiftMatrix s X (S.coordMatrix g c) *ᵥ z) f) =
      (S.hom T).ϱ (matrixToVec (X * vecToMatrix z * ((S.coordMatrix 1 c)ᴴ * stdForm E s)))
        (pairWeil S T a b (g, 1) f) := by
  have h_coord : (S.coordMatrix g c)ᴴ * stdForm E s * g⁻¹.adeleMatrix =
      (S.coordMatrix 1 c)ᴴ * stdForm E s := by
    have h_form : g⁻¹.adeleMatrixᴴ * (stdForm E s * g⁻¹.adeleMatrix) = stdForm E s := by
      rw [← Matrix.mul_assoc, conjTranspose_adeleMatrix_mul_stdForm_mul_adeleMatrix]
    simp [coordMatrix, h_form, Matrix.mul_assoc]
  have h_vec : (1 : Matrix m m (𝔸 E)) ⊗ₖ g⁻¹.adeleMatrixᵀ *ᵥ shiftMatrix s X (S.coordMatrix g c) *ᵥ
    z =
      matrixToVec (X * vecToMatrix z * ((S.coordMatrix 1 c)ᴴ * stdForm E s)) := by
    rw [kronecker_mulVec_eq_matrixToVec, kronecker_mulVec_eq_matrixToVec, ← h_coord]
    simp [Matrix.mul_assoc]
  simp [pairWeil, omega_rho, ← h_vec]

/-- Let `f` be a clean datum (`IsClean`), and let the isotropic frame of a complete splitting `D` of
`S ⊕ S⁻` have blocks `K` (in `S`) and `K'` (in `S⁻`). If the zero term along the Lagrangian of `D`
is not zero at the doubled datum of `f'` and `ω(g, 1) f`, where `ω = pairWeil S T a b`, then the
Lagrangian contains no nonzero vector of `S`: `K' c = 0` forces `K c = 0`. -/
lemma mul_eq_zero_of_zeroTerm_ne_zero {p : Type} [Fintype p] [DecidableEq p] {a b : AutChar E}
    {f f' : 𝒮 (S.hom T)} {g : G E s} (hf : IsClean f) (D : CompleteSplitting (S.sum S.neg) p)
    (h_ne : D.lagrangian.zeroTerm T (doubleDatum f' (pairWeil S T a b (g, 1) f)) ≠ 0)
    {K K' : Matrix n p E} (hk : D.k = fromRows K K') {c : Matrix p n E} (hc : K' * c = 0) :
    K * c = 0 := by
  obtain hs | ⟨A, Ψ, w, f₀, hA, hΨ, hΨ_inj, rfl⟩ := hf
  · -- All signs agree: the columns of `K * c` are isotropic in an anisotropic space.
    have h_form : (K * c)ᴴ * (S.J * (K * c)) = 0 := calc
      _ = cᴴ * (D.kᴴ * (S.sum S.neg).J * D.k) * c := by
        simp [hk, hc, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, fromBlocks_mul_fromRows,
          conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]
      _ = 0 := by rw [D.gram_kk, Matrix.mul_zero, Matrix.zero_mul]
    exact ext_col fun j ↦ S.eq_zero_of_isotropic_of_definite hs _ (congrFun₂ h_form j j)
  · -- Otherwise the term is a bounded functional `ℓ` of the datum that is invariant under the
    -- translations attached to `K * c ≠ 0`. No point of the support of `Ψ` is orthogonal to all
    -- of them, as these points are injective at `w`; so `ℓ` vanishes at
    -- `(S.hom T).schrodingerOp A Ψ f₀`.
    by_contra hKc
    let ℓ : 𝒮 (S.hom T) →L[ℂ] ℂ :=
      D.lagrangian.zeroTerm T ∘L doubleDatum f' ∘L pairWeil S T a b (g, 1)
    have h_inv (z : m × n → 𝔸 E) (φ : 𝒮 (S.hom T)) :
        ℓ ((S.hom T).ϱ (shiftMatrix s T.dualFrame⁻¹.val (S.coordMatrix g (K * c)) *ᵥ z) φ) =
          ℓ φ := by
      simp only [ℓ, ContinuousLinearMap.comp_apply, pairWeil_rho_shiftMatrix,
        zeroTerm_doubleDatum_rho D hk hc]
    exact h_ne (map_schrodingerOp_eq_zero_of_invariant hA _ _ h_inv
      (fun y hy ↦ S.mul_coordMatrix_ne_zero hKc T.dualFrame⁻¹ (hΨ_inj y hy)) f₀)

/-- Let `f` be a clean datum (`IsClean`) and `L` a Lagrangian of `S ⊕ S⁻`. If the term of `L` in the
Siegel–Weil formula is not zero at the doubled datum of `f'` and `ω(g, 1) f`, where
`ω = pairWeil S T a b`, then `L` is the graph of a rational isometry of `S`. -/
lemma exists_graph_eq_of_zeroTerm_ne_zero {a b : AutChar E} {f : 𝒮 (S.hom T)} {g : G E s}
    {f' : 𝒮 (S.hom T)} (hf : IsClean f) (L : Lagrangian (S.sum S.neg))
    (h_ne : L.zeroTerm T (doubleDatum f' (pairWeil S T a b (g, 1) f)) ≠ 0) :
    ∃ δ : U S.J, (graphSplitting S δ⁻¹).lagrangian = L := by
  -- Write the frame of `L` as blocks `K` (in `S`) and `K'` (in `S⁻`). The term being nonzero forces
  -- `K'` to be invertible, and then `L` is the graph of the isometry `-K * K'⁻¹`.
  obtain ⟨⟨r, D⟩, rfl⟩ := L.completeSplitting
  obtain ⟨K, K', hk⟩ : ∃ K K' : Matrix n (Fin r) E, D.k = fromRows K K' :=
    ⟨D.k.toRows₁, D.k.toRows₂, D.k.fromRows_toRows.symm⟩
  have h_iso : Kᴴ * S.J * K = K'ᴴ * S.J * K' := by
    simpa [hk, add_neg_eq_zero, Matrix.mul_assoc, fromBlocks_mul_fromRows,
      conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows] using D.gram_kk
  obtain rfl : card n = r := by simpa [← two_mul] using D.card_eq
  -- As the frame `D.k` has the left inverse `D.lᴴ * J`, multiplication by `K'` is injective, hence
  -- surjective by counting dimensions.
  have h_inj : Function.Injective (mulLeftLinearMap n E K') := by
    refine (injective_iff_map_eq_zero _).2 fun c (hc : K' * c = 0) ↦ ?_
    have hkc : D.k * c = 0 := by simp [hk, hc, mul_eq_zero_of_zeroTerm_ne_zero hf D h_ne hk hc]
    rw [← c.one_mul, ← D.gram_lk, Matrix.mul_assoc, hkc, Matrix.mul_zero]
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin (card n)) n E, K' * B = 1 :=
    ((mulLeftLinearMap n E K').linearEquivOfInjective h_inj
      (by simp [Module.finrank_matrix])).surjective 1
  have h_unitary : (-K * B)ᴴ * S.J * (-K * B) = S.J := calc
    _ = Bᴴ * (Kᴴ * S.J * K) * B := by simp [Matrix.mul_assoc]
    _ = (K' * B)ᴴ * S.J * (K' * B) := by simp only [h_iso, conjTranspose_mul, Matrix.mul_assoc]
    _ = S.J := by simp [hB]
  -- The graph lies in `L`, since its vector at `y` is `D.k *ᵥ (-B *ᵥ y)`; Lagrangians are maximal.
  refine ⟨(U.of (by simp) (-K * B) h_unitary)⁻¹, eq_of_le ?_⟩
  rintro _ ⟨y, rfl⟩
  exact ⟨-B *ᵥ y, by simp [hk, hB]⟩

/-- Distinct isometries `δ` of `S` have distinct graphs, so `δ ↦ (graphSplitting S δ⁻¹).lagrangian`
is injective. -/
lemma graphSplitting_lagrangian_injective :
    Function.Injective fun δ : U S.J ↦ (graphSplitting S δ⁻¹).lagrangian := by
  -- Equal graphs have frames `(δ'⁻¹, -1) = (δ⁻¹, -1) * c`; the lower block forces `c = 1`.
  intro δ δ' h_eq
  have h_frames : ∃ c : Matrix n n E, (graphSplitting S δ⁻¹).k * c = (graphSplitting S δ'⁻¹).k :=
    Filling.exists_mul_eq_of_col_mem_range fun i ↦ h_eq.ge ⟨_, mulVec_single_one _ i⟩
  -- `-coe_units_inv` keeps the inverse of a unit from turning into a matrix inverse.
  simpa [fromRows_ext_iff, ← Units.ext_iff, -coe_units_inv] using h_frames

/-- For spaces `S`, `T` with data `f`, `f'`, the conjugate theta kernel of `f'` at
`(g', x)` times the theta kernel of `f` at `(g, x)` is the theta kernel of the pair `S ⊕ S⁻, T` at
`x`, acting by `splitWeil`, and the doubled datum `doubleDatum` of `ω(g', 1) f'` and `ω(g, 1) f`.
Here `θ` is the theta functional and `ω` is `pairWeil` with characters `a`, `b`; at a point `(g, 1)`
the character `a` does not matter and is taken to be `1`. -/
lemma theta_splitWeil_doubleDatum (a b : AutChar E) (f f' : 𝒮 (S.hom T)) (g g' : G E s)
    (x : G E t) :
    θ ((S.sum S.neg).hom T) (splitWeil (S.sum S.neg) T (1, x)
        (doubleDatum (pairWeil S T 1 b (g', 1) f') (pairWeil S T 1 b (g, 1) f))) =
      conj (θ (S.hom T) (pairWeil S T a b (g', x) f')) *
        θ (S.hom T) (pairWeil S T a b (g, x) f) := by
  -- At `(1, x)` the second character does not matter; `b'` is the one that negation produces.
  let b' : AutChar E := b⁻¹ * upsilonU1 ^ card m
  have h_char : splitWeil (S.sum S.neg) T (1, x) =
      pairWeil (S.sum S.neg) T (a * (a⁻¹ * upsilonU1 ^ card n)) b' (.sum (1, neg 1), x) := by
    simp [pairWeil, ← two_mul, mk_one_one]
  have h_act (u u' : 𝒮 (S.hom T)) : splitWeil (S.sum S.neg) T (1, x) (doubleDatum u' u) =
      doubleDatum (pairWeil S T a b (1, x) u') (pairWeil S T a b' (1, x) u) := by
    rw [h_char, doubleDatum_apply, pairWeil_boxProd_source, map_smul, pairWeil_negSource a b,
      doubleDatum_apply]
  have h_comp (c : AutChar E) (k : G E s) (u : 𝒮 (S.hom T)) :
      pairWeil S T a c (1, x) (pairWeil S T 1 b (k, 1) u) = pairWeil S T a b (k, x) u := by
    simp [pairWeil, ← map_mul, rep_apply_apply, smul_smul, mul_comm (a.val x.det : ℂ)]
  rw [h_act, h_comp, h_comp, theta_doubleDatum]

/-- For a rational isometry `δ` of `S`, the zero term of the Lagrangian `{(δ⁻¹ y, -y)}` of
`S ⊕ S⁻`, at the doubled datum of `ω(g', 1) f'` and `ω(g, 1) f`, is the matrix coefficient
`⟨f', ω(g'⁻¹ δ g, 1) f⟩`. -/
lemma zeroTerm_graphSplitting_doubleDatum (b : AutChar E) (f f' : 𝒮 (S.hom T)) (g g' : G E s)
    (δ : U S.J) :
    (graphSplitting S δ⁻¹).lagrangian.zeroTerm T
        (doubleDatum (pairWeil S T 1 b (g', 1) f') (pairWeil S T 1 b (g, 1) f)) =
      weilMatrixCoeff b f f' (g'⁻¹ * (S.ratEmbed δ * g)) := by
  rw [zeroTerm_graphSplitting b, weilMatrixCoeff, ← dataInner_pairWeil _ _ 1 b (g'⁻¹, 1)]
  simp [← mul_apply_eq_comp, ← map_mul, mk_one_one]

/-- Doubling. Let `T` have rank `m`, `S` rank `n`, with `2 n < m`, and let the datum `f` be clean
(`IsClean`: only graphs of isometries have nonzero terms). The integral over `[U(T)]` of the theta
kernel of `f` at `g` times the conjugate kernel of any datum `f'` at `g'` is the volume of `[U(T)]`
times the sum over the rational points `γ` of `U(S)` of `⟨f', ω(g'⁻¹ γ g) f⟩`. -/
theorem integral_conj_theta_mul_theta (h_rank : 2 * card n < card m) (a b : AutChar E)
    {f : 𝒮 (S.hom T)} (hf : IsClean f) (f' : 𝒮 (S.hom T)) (g g' : G E s) :
    ∫ x : G E t, conj (θ (S.hom T) (pairWeil S T a b (g', x) f')) *
        θ (S.hom T) (pairWeil S T a b (g, x) f) ∂T.quotMeasure =
      T.quotMeasure.real Set.univ * ∑' γ : S.Γ, weilMatrixCoeff b f f' (g'⁻¹ * (γ * g)) := by
  -- Siegel–Weil turns the integral into a sum over the Lagrangians of `S ⊕ S⁻`; only the graphs
  -- of isometries contribute, each once.
  let d : 𝒮 ((S.sum S.neg).hom T) :=
    doubleDatum (pairWeil S T 1 b (g', 1) f') (pairWeil S T 1 b (g, 1) f)
  let e : U S.J ≃ S.Γ := .ofInjective _ S.ratEmbed_injective
  have h_support : Function.support (fun L : Lagrangian (S.sum S.neg) ↦ L.zeroTerm T d) ⊆
      Set.range fun δ : U S.J ↦ (graphSplitting S δ⁻¹).lagrangian :=
    exists_graph_eq_of_zeroTerm_ne_zero hf
  obtain ⟨-, h_integral⟩ := (siegel_weil T (graphSplitting S 1) h_rank).2 d
  calc _ = T.quotMeasure.real Set.univ * ∑' L : Lagrangian (S.sum S.neg), L.zeroTerm T d := by
        simp_rw [← theta_splitWeil_doubleDatum a b, ← h_integral, d]
    _ = _ := by
        rw [← graphSplitting_lagrangian_injective.tsum_eq h_support, ← e.tsum_eq]
        exact congrArg _ (tsum_congr (zeroTerm_graphSplitting_doubleDatum b f f' g g'))

open ContinuousLinearMap in
/-- Let the rank of `T` exceed twice that of `S`. There is a finite constant `C` such that, with
absolute values inside, both sides of the doubling identity (the integral of the product of two
theta kernels over `[U(T)]` and the sum of matrix coefficients over the rational points of `U(S)`)
are at most `C ‖ω(g') f'‖ ‖ω(g) f‖`. -/
lemma exists_doubling_bound (h_rank : 2 * card n < card m) : ∃ C : ENNReal, C ≠ ⊤ ∧
    ∀ (a b : AutChar E) (f f' : 𝒮 (S.hom T)) (g g' : G E s),
      ∫⁻ x : G E t, ‖conj (θ (S.hom T) (pairWeil S T a b (g', x) f')) *
          θ (S.hom T) (pairWeil S T a b (g, x) f)‖ₑ ∂T.quotMeasure ≤
        C * (‖pairWeil S T 1 b (g', 1) f'‖ₑ * ‖pairWeil S T 1 b (g, 1) f‖ₑ) ∧
      ∑' γ : S.Γ, ‖weilMatrixCoeff b f f' (g'⁻¹ * (γ * g))‖ₑ ≤
        C * (‖pairWeil S T 1 b (g', 1) f'‖ₑ * ‖pairWeil S T 1 b (g, 1) f‖ₑ) := by
  -- The theta kernel of `S ⊕ S⁻, T` at a datum `d` is at most `N x * ‖d‖` with `N` integrable, and
  -- the sum `Z` of the norms of the terms of the graphs is finite by the Siegel–Weil theorem.
  obtain ⟨N, hN_meas, hN_int, hN⟩ := theta_normalisedTorus_le T (graphSplitting S 1) h_rank
  have h_kernel (x : G E t) (d : 𝒮 ((S.sum S.neg).hom T)) :
      ‖θ ((S.sum S.neg).hom T) (splitWeil (S.sum S.neg) T (1, x) d)‖ₑ ≤ N x * ‖d‖ₑ := by
    simpa [-theta_apply] using hN x 0 d
  let Z : ENNReal := ∑' δ : U S.J, ‖(graphSplitting S δ⁻¹).lagrangian.zeroTerm T‖ₑ
  have hZ : Z ≠ ⊤ := tsum_enorm_ne_top_iff_summable_norm.2 <|
    (siegel_weil T (graphSplitting S 1) h_rank).1.comp_injective graphSplitting_lagrangian_injective
  refine ⟨(∫⁻ x, N x ∂T.quotMeasure + Z) * ‖doubleDatum (S := S) (T := T)‖ₑ, by finiteness,
    fun a b f f' g g' ↦ ?_⟩
  let d : 𝒮 ((S.sum S.neg).hom T) :=
    doubleDatum (pairWeil S T 1 b (g', 1) f') (pairWeil S T 1 b (g, 1) f)
  have hd : ‖d‖ₑ ≤ ‖doubleDatum (S := S) (T := T)‖ₑ *
      (‖pairWeil S T 1 b (g', 1) f'‖ₑ * ‖pairWeil S T 1 b (g, 1) f‖ₑ) :=
    (le_opENorm₂ ..).trans_eq (mul_assoc ..)
  constructor
  · calc _ ≤ (∫⁻ x, N x ∂T.quotMeasure) * ‖d‖ₑ := by
          simp_rw [← theta_splitWeil_doubleDatum a b, ← lintegral_mul_const _ hN_meas]
          exact lintegral_mono fun x ↦ h_kernel x d
      _ ≤ _ := by grw [hd, mul_assoc, ← le_self_add]
  · let e : U S.J ≃ S.Γ := .ofInjective _ S.ratEmbed_injective
    calc _ ≤ Z * ‖d‖ₑ := by
          rw [← e.tsum_eq, ← ENNReal.tsum_mul_right]
          refine ENNReal.tsum_le_tsum fun δ ↦ .trans (le_of_eq ?_) (le_opENorm _ d)
          exact congrArg enorm (zeroTerm_graphSplitting_doubleDatum b f f' g g' δ).symm
      _ ≤ _ := by grw [hd, mul_assoc, ← le_add_self]

open ContinuousLinearMap in
/-- Let the rank of `T` exceed twice that of `S`. For any data `f`, `f'`, both sides of the doubling
identity, with absolute values inside (the integral over `[U(T)]` and the sum over the rational
points of `U(S)`), are at most a finite constant times a common power of the heights `S.height`
of `g` and `g'`. -/
lemma exists_doubling_le_height (h_rank : 2 * card n < card m) (a b : AutChar E)
    (f f' : 𝒮 (S.hom T)) : ∃ (l : ℕ) (C : ENNReal), C ≠ ⊤ ∧ ∀ g g' : G E s,
      ∫⁻ x : G E t, ‖conj (θ (S.hom T) (pairWeil S T a b (g', x) f')) *
          θ (S.hom T) (pairWeil S T a b (g, x) f)‖ₑ ∂T.quotMeasure ≤
        C * (.ofReal (S.height g' ^ l) * .ofReal (S.height g ^ l)) ∧
      ∑' γ : S.Γ, ‖weilMatrixCoeff b f f' (g'⁻¹ * (γ * g))‖ₑ ≤
        C * (.ofReal (S.height g' ^ l) * .ofReal (S.height g ^ l)) := by
  -- Both sides are invariant under rational points, so `g` may be replaced by a point `η g * g` at
  -- which `ω` grows at most like a power of the height.
  obtain ⟨C, hC, h_bound⟩ := exists_doubling_bound (S := S) (T := T) h_rank
  obtain ⟨l, hl⟩ : ∃ l : ℕ, ∀ g : G E s, ∃ γ ∈ S.Γ,
      ‖pairWeil S T 1 b (γ * g, 1)‖ ≤ 2 ^ l * S.height g ^ l :=
    ((pairThetaKer S T 1 b).swap.eventually_exists_norm_omega_le_mul_height_pow 1).exists
  choose η hη h_growth using hl
  have h_norm (φ : 𝒮 (S.hom T)) (g : G E s) : ‖pairWeil S T 1 b (η g * g, 1) φ‖ₑ ≤
      2 ^ l * ‖φ‖ₑ * .ofReal (S.height g ^ l) := by
    grw [le_opENorm, ← ofReal_norm, h_growth, ENNReal.ofReal_mul (by positivity), mul_right_comm]
    simp
  refine ⟨l, C * (2 ^ l * ‖f'‖ₑ * (2 ^ l * ‖f‖ₑ)), by finiteness, fun g g' ↦ ?_⟩
  have h_inv (φ : 𝒮 (S.hom T)) (g : G E s) (x : G E t) :
      θ (S.hom T) (pairWeil S T a b (η g * g, x) φ) = θ (S.hom T) (pairWeil S T a b (g, x) φ) :=
    (pairThetaKer S T a b).theta_rat_mul _ (hη g) g
  let e : S.Γ ≃ S.Γ := .trans (.mulLeft ⟨η g', hη g'⟩⁻¹) (.mulRight ⟨η g, hη g⟩)
  have h_shift : ∑' γ : S.Γ, ‖weilMatrixCoeff b f f' (g'⁻¹ * (γ * g))‖ₑ =
      ∑' γ : S.Γ, ‖weilMatrixCoeff b f f' ((η g' * g')⁻¹ * (γ * (η g * g)))‖ₑ := by
    rw [← e.tsum_eq]
    simp [e, mul_assoc]
  have h_moved := h_bound a b f f' (η g * g) (η g' * g')
  simp only [h_inv, ← h_shift] at h_moved
  grw [h_norm, h_norm, mul_mul_mul_comm, ← mul_assoc C] at h_moved
  exact h_moved

omit [WeilData E] in
/-- Unfolding: `((g', g), γ) ↦ (g', g'⁻¹ * (γ * g))` carries the measure of
`[U(S)] × [U(S)] × Γ` (counting measure on the rational points `Γ`) to that of
`[U(S)] × U(S)(𝔸)`. -/
lemma measurePreserving_quotMeasure_unfold (S : Space E n s) :
    MeasurePreserving (fun p : (G E s × G E s) × S.Γ ↦ (p.1.1, p.1.1⁻¹ * (p.2 * p.1.2)))
      ((S.quotMeasure.prod S.quotMeasure).prod .count) (S.quotMeasure.prod volume) :=
  -- Reassociate, map `(g, γ)` to `γ * g`, then translate the second component by `g'⁻¹`.
  (measurePreserving_prod_inv_mul S.quotMeasure volume).comp <|
    ((MeasurePreserving.id S.quotMeasure).prod measurePreserving_orbitMeasure).comp
      (measurePreserving_prodAssoc S.quotMeasure S.quotMeasure Measure.count)

omit [WeilData E] in
/-- If `‖y g‖ * height g ^ l ≤ B` and `‖y' g‖ * height g ^ l ≤ B'` for all `g`, then a constant `C`
times the two powers of the heights, weighted by `‖y' g'‖ * ‖y g‖`, is at most `C B' B`. -/
lemma enorm_mul_height_pow_le {y y' : G E s → ℂ} {l : ℕ} {B B' : ℝ}
    (hB : ∀ g : G E s, ‖y g‖ * S.height g ^ l ≤ B)
    (hB' : ∀ g : G E s, ‖y' g‖ * S.height g ^ l ≤ B') (C : ENNReal) (g g' : G E s) :
    ‖y' g'‖ₑ * ‖y g‖ₑ * (C * (.ofReal (S.height g' ^ l) * .ofReal (S.height g ^ l))) ≤
      C * (.ofReal B' * .ofReal B) :=
  calc _ = C * (.ofReal (‖y' g'‖ * S.height g' ^ l) * .ofReal (‖y g‖ * S.height g ^ l)) := by
        simp only [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
        ring
    _ ≤ C * (.ofReal B' * .ofReal B) := by grw [hB, hB']

open ContinuousLinearMap Continuous in
/-- The inner product formula before the choice of a sharp datum. Let `2 n < m` for the ranks of
`S`, `T`, let `f` be clean (`IsClean`) and `f'` any datum (by default `f`); `a`, `b` are the
characters that twist the Weil representation `ω`. For automorphic `y`, `y'` of rapid decay
(`rapidFunctions`), the Petersson product of the theta lifts `⟨Θ_{f'} y', Θ_f y⟩` (`lift`,
`petersson`) is the volume of `[U(T)]` times `∫ ⟨f', ω(g) f⟩ ⟨y', R(g) y⟩ dg` over the adelic
points of `U(S)`, with `⟨f', ω(g) f⟩ = weilMatrixCoeff b f f' g` and `R` the right translation,
and this integral converges absolutely. -/
theorem inner_product_formula (h_rank : 2 * card n < card m) (a b : AutChar E)
    {f : 𝒮 (S.hom T)} (hf : IsClean f) {y y' : G E s → ℂ} (hy : y ∈ S.rapidFunctions)
    (hy' : y' ∈ S.rapidFunctions) (f' : 𝒮 (S.hom T) := f) :
    let k (g : G E s) : ℂ :=
      weilMatrixCoeff b f f' g * S.petersson y' (rightRegular ℂ (G E s) ℂ g y)
    Integrable k ∧
    T.petersson (lift (pairThetaKer S T a b) f' y') (lift (pairThetaKer S T a b) f y) =
      T.quotMeasure.real Set.univ * ∫ g : G E s, k g := by
  -- Integrate the doubling identity against `conj (y' g') * y g` over `[U(S)] × [U(S)]`; the sum
  -- over the rational points unfolds one of the two integrals.
  let Θ (g g' : G E s) (x : G E t) : ℂ :=
    conj (θ (S.hom T) (pairWeil S T a b (g', x) f')) * θ (S.hom T) (pairWeil S T a b (g, x) f)
  let Φ (p : G E s × G E s) : ℂ := weilMatrixCoeff b f f' p.2 * (conj (y' p.1) * y (p.1 * p.2))
  obtain ⟨hy_aut, hy_rapid⟩ := hy
  obtain ⟨hy'_aut, hy'_rapid⟩ := hy'
  have hy_cont : Continuous y := hy_aut.continuous
  have hy'_cont : Continuous y' := hy'_aut.continuous
  -- Convergence: the decay of `y` and `y'` beats the powers of the heights.
  obtain ⟨l, C, hC, h_bound⟩ := exists_doubling_le_height h_rank a b f f'
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ g : G E s, ‖y g‖ * S.height g ^ l ≤ B := hy_rapid l
  obtain ⟨B', hB'⟩ : ∃ B' : ℝ, ∀ g : G E s, ‖y' g‖ * S.height g ^ l ≤ B' := hy'_rapid l
  have h_finite : ∫⁻ _ : G E s × G E s, C * (.ofReal B' * .ofReal B)
      ∂S.quotMeasure.prod S.quotMeasure < ⊤ := lintegral_const_lt_top (by finiteness)
  -- Unfolding turns the double integral of the sum over `S.Γ` into the integral of `Φ`.
  have h_unfold := measurePreserving_quotMeasure_unfold S
  have hΦ_unfold (g g' : G E s) (γ : S.Γ) : Φ (g', g'⁻¹ * (γ * g)) =
      conj (y' g') * y g * weilMatrixCoeff b f f' (g'⁻¹ * (γ * g)) := by
    simp only [Φ, mul_inv_cancel_left, hy_aut.rat_mul γ γ.2]
    exact mul_comm ..
  have hΦ : Integrable Φ (S.quotMeasure.prod volume) := by
    refine ⟨aestronglyMeasurable (by fun_prop), h_finite.trans_le' ?_⟩
    grw [← h_unfold.lintegral_comp (by fun_prop), lintegral_prod_le]
    gcongr with p
    calc ∫⁻ γ : S.Γ, ‖Φ (p.1, p.1⁻¹ * (γ * p.2))‖ₑ ∂.count
        = ‖y' p.1‖ₑ * ‖y p.2‖ₑ * ∑' γ : S.Γ, ‖weilMatrixCoeff b f f' (p.1⁻¹ * (γ * p.2))‖ₑ := by
          simp [lintegral_count, hΦ_unfold, enorm_mul, ENNReal.tsum_mul_left]
      _ ≤ _ := by grw [(h_bound p.2 p.1).2, enorm_mul_height_pow_le hB hB']
  have h_swap : Integrable
      (Function.uncurry fun (p : G E s × G E s) x ↦ conj (y' p.1) * y p.2 * Θ p.2 p.1 x)
      ((S.quotMeasure.prod S.quotMeasure).prod T.quotMeasure) := by
    refine ⟨by fun_prop, h_finite.trans_le' ?_⟩
    grw [lintegral_prod_le]
    gcongr with p
    calc ∫⁻ x, ‖conj (y' p.1) * y p.2 * Θ p.2 p.1 x‖ₑ ∂T.quotMeasure
        = ‖y' p.1‖ₑ * ‖y p.2‖ₑ * ∫⁻ x, ‖Θ p.2 p.1 x‖ₑ ∂T.quotMeasure := by
          simp [enorm_mul, lintegral_const_mul', ENNReal.mul_eq_top]
      _ ≤ _ := by grw [(h_bound p.2 p.1).1, enorm_mul_height_pow_le hB hB']
  have h_fubini (g : G E s) : weilMatrixCoeff b f f' g *
      S.petersson y' (rightRegular ℂ (G E s) ℂ g y) = ∫ g', Φ (g', g) ∂S.quotMeasure := by
    simp [Space.petersson, Φ, integral_const_mul]
  simp only [h_fubini]
  refine ⟨hΦ.integral_prod_right, ?_⟩
  calc _ = ∫ x, ∫ p : G E s × G E s, conj (y' p.1) * y p.2 * Θ p.2 p.1 x
          ∂S.quotMeasure.prod S.quotMeasure ∂T.quotMeasure := by
        simp_rw [petersson, lift, ← integral_conj, ← integral_prod_mul]
        congr! 4 with x p
        simp only [Θ, map_mul]
        ring
    _ = ∫ p : G E s × G E s, T.quotMeasure.real Set.univ *
          ∑' γ : S.Γ, Φ (p.1, p.1⁻¹ * (γ * p.2)) ∂S.quotMeasure.prod S.quotMeasure := by
        rw [← integral_integral_swap h_swap]
        simp_rw [integral_const_mul (conj (y' _) * y _), Θ,
          integral_conj_theta_mul_theta h_rank a b hf, hΦ_unfold, tsum_mul_left]
        exact integral_congr_ae (.of_forall fun p ↦ mul_left_comm ..)
    _ = T.quotMeasure.real Set.univ * ∫ g, ∫ g', Φ (g', g) ∂S.quotMeasure := by
        rw [integral_const_mul, ← integral_prod_symm _ hΦ, ← (h_unfold.fubini hΦ).2]
        simp_rw [integral_count_eq_tsum]

/-! ### The coefficient of the vacuum -/

/-- Let `f` be a vacuum above `A` (fixed by `projOn` at `A`), let the finite point `γ` be supported
on `A` and its conjugate, and let `g` be integral at `A`. Then `⟨f, ω(γ g, 1) f⟩` is
`⟨f, ω(g, 1) f⟩` times the vacuum coefficient `vacuumCoeff (card m) b γ`, the inverse of the product
of `b (det γ)` and the `card m`-th power of the multiplier of `γ`. -/
lemma weilMatrixCoeff_mul {A : Set (FinPlace E)} (b : AutChar E) {f : 𝒮 (S.hom T)}
    (hf : projOn (S.hom T) A f = f) {γ : Gf E n} (hγ : γ ∈ supportedOn n A) {g : G E s}
    (hg : g.2 ∈ localLevel n A) :
    weilMatrixCoeff b f f (γ * g) = vacuumCoeff (card m) b γ * weilMatrixCoeff b f f g := by
  -- The vector `u = ω(g, 1) f` is again a vacuum above `A`, so the projection of `ω(γ, 1) u` is
  -- a multiple of `u`.
  set u : 𝒮 (S.hom T) := pairWeil S T 1 b (g, 1) f with hu
  have hu_vac : projOn (S.hom T) A u = u :=
    projOn_pairWeil hf (g, 1) fun w hw ↦ onHom_atPlace_mem (hg w hw) (by simp)
  have h_char : pairChar (s' := t) 1 b ((γ : G E s), 1) = (b.1 (detFin 1 γ) : ℂ)⁻¹ := by
    -- The determinant of a finite point does not depend on the signs.
    have h_det : detFin 1 γ = detFin s γ := by ext <;> simp
    change _ = (Circle.coeHom (b.1 (detFin 1 γ)))⁻¹
    simp [pairChar, h_det]
  have h_mult : finMultiplier (onHom (s' := t) ((γ : G E s), 1)).2⁻¹ =
      finMultiplier γ ^ card m := by simp [finMultiplier_inv, finMultiplier_onHom_left]
  have h_proj : projOn (S.hom T) A (pairWeil S T 1 b ((γ : G E s), 1) u) =
      vacuumCoeff (card m) b γ • u := by
    have h_fin : onHom (s' := t) ((γ : G E s), 1) = ↑(onHom (s' := t) ((γ : G E s), 1)).2 :=
      onHom_fin γ 1
    rw [pairWeil_apply, map_smul, h_fin, projOn_omega _ (onHom_mem_supportedOn hγ (one_mem _))
      hu_vac,
      smul_smul, h_char, h_mult, vacuumCoeff, mul_inv]
  calc _ = dataInner (S.hom T) (projOn (S.hom T) A f) (pairWeil S T 1 b ((γ : G E s), 1) u) := by
        rw [hf, hu, rep_apply_apply, Prod.mk_mul_mk (γ : G E s) g, one_mul (1 : G E t)]
    _ = dataInner (S.hom T) f (vacuumCoeff (card m) b γ • u) := by rw [dataInner_projOn, h_proj]
    _ = vacuumCoeff (card m) b γ * weilMatrixCoeff b f f g := by rw [map_smul, smul_eq_mul]

/-! ### An integral isotropic frame -/

/-- If `2 n ≤ m` for the cardinalities of `n` and `m`, there is an `m × n` matrix `x` over the
integral adeles `Ô E` with `xᴴ x = 0` (an integral isotropic frame), some `n` of whose rows form the
identity matrix. -/
lemma exists_integral_isotropic_frame (h_rank : 2 * card n ≤ card m) :
    ∃ x : Matrix m n (𝔸f E), (∀ (i : m) (j : n), x i j ∈ Ô E) ∧ xᴴ * x = 0 ∧
      ∃ u : n ↪ m, ∀ i : n, x (u i) = Pi.single i 1 := by
  -- Pick `2 n` distinct rows; column `j` of `x` has `1` in row `ι (inl j)` and the integral element
  -- `ε = normNegOne` of norm `-1` in row `ι (inr j)`.
  obtain ⟨ι⟩ : Nonempty (n ⊕ n ↪ m) := Function.Embedding.nonempty_of_card_le (by grind [card_sum])
  let ε : 𝔸f E := Weil.normNegOne.val.val
  let col (j : n) : m → 𝔸f E := Pi.single (ι (.inl j)) 1 + Pi.single (ι (.inr j)) ε
  refine ⟨(of col)ᵀ, fun i j ↦ ?_, ?_, Function.Embedding.inl.trans ι, fun i ↦ ?_⟩
  · simp [col, ε, Pi.single_apply, ite_mem, add_mem]
  · -- Distinct columns have disjoint supports, and a column has norm `1 + ε̄ ε = 0`.
    refine Matrix.ext fun (j k : n) ↦ ?_
    have h_entry : ((of col)ᵀᴴ * (of col)ᵀ) j k = if j = k then 1 + star ε * ε else 0 := by
      by_cases h_eq : j = k <;> simp [col, Matrix.mul_apply, apply_ite star, Pi.single_apply,
        mul_add, add_mul, Finset.sum_add_distrib, h_eq, eq_comm (a := k)]
    exact h_entry.trans (by simp [ε, star_normNegOne_mul_self])
  · simp [col, funext_iff, eq_comm, Pi.single_apply]

end New.SiegelWeil

end InnerProductFormula

end
