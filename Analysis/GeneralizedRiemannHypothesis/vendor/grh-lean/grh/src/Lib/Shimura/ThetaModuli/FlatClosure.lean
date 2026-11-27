import Lib.General.Algebra.MultivariatePolynomials
import Lib.General.Geometry.GeometricPoints
import Lib.General.LinearAlgebra.MatrixPolynomials

/-!
# Flat families of ideals cut out by points and the flat closure of theta points

An ideal of polynomials is cut out by points in the chart `c` if it contains `X c - 1`, the forms of
degree `r ^ j` have prescribed ranks modulo the ideal, and its forms of degree `r ^ j` with `j ≤ i`
are those that vanish at given points. When the points are the images of the same `A`-valued points,
such ideals fit into a flat family over `A`, and a degree bound for monomial ideals shows that
finitely many degrees suffice.

## Main definitions and results

* `New.Variety.ThetaNull.IsCutDegree`, `New.Variety.ThetaNull.eventually_isCutDegree`: for every
  large enough `d`, a monomial ideal with at most `σ i` standard monomials of degree `r ^ i` for all
  `i ≤ d` has at most `σ i` of them in every degree `r ^ i`.
* `New.Variety.ThetaNull.eq_map_and_flat_of_isCutOut`: let `I₀` and the `I n` be cut out by the
  images of the same `A`-valued points along a local map `φ` and jointly injective maps `ψ n` to one
  field `K`, with `r > 1` and `i` such a bound. Let `T` be the polynomials over `A` that map into
  every `I n`. Then `I₀` is the reduction of `T`, and the quotient by `T` is flat.
* `New.Variety.ThetaNull.IsCutOutAt`: at a field-valued point `t` of `S`, the vanishing ideals of a
  set `Z` in the affine charts are cut out (`New.Variety.ThetaNull.IsCutOut`) by the values at `t`
  of given maps `P a` from `S` to projective space.
* `New.Variety.ThetaNull.exists_isFlatClosure`: for points `θ n z` of projective space over complex
  points `η n` of a reduced `S`, cut out (`New.Variety.ThetaNull.IsCutOutAt`) at each `η n` by
  linear systems `P`, with `r > 1` and `i` a degree bound (`New.Variety.ThetaNull.IsCutDegree`),
  where every point of `S` specialises to a geometric point at which some set is cut out, the
  reduced closure of the points over a finite dense set of the `η n` is flat over `S`, and every
  point of `S` specialises to a geometric point with reduced fibre.

Notions from other files:
* `AddSemigroupIdeal (J →₀ ℕ)` (Mathlib): a set of exponents that is closed under adding any
  exponent, that is, a monomial ideal.
* `New.LineBundle` with `New.LineBundle.IsLinearSystem`: a map from a scheme to projective space,
  given by charts and the ratios of coordinates on them.
* `New.IsDenseFamily`: a family of complex points of a scheme whose images are dense.
* `New.Variety.AllSpecializeTo`: every point of a scheme S specialises to the image of some point
  over an algebraically closed field that satisfies a property Q of field-valued points.

## Relation to the literature

Known; see `Lib.Shimura.ThetaModuli.UniversalFamily` for sources.
-/

noncomputable section

namespace New.Variety.ThetaNull

/-!
## Ideals cut out by points and a degree bound for monomial ideals

Commutative algebra for flat families of ideals cut out by points. Polynomials are in finitely many
variables `J`. Monomials are exponents `J →₀ ℕ`, and a monomial outside a monomial ideal is called
standard.

The idea: explicit determinants give forms in `T` with all needed leading monomials. Division by
them shows that the standard monomials span, and ranks give freeness.
-/

section CutOutIdeals

open AddSemigroupIdeal Finsupp Set

variable {ι κ J A k K : Type} [CommRing A] [Field k] (φ : A →+* k) {d : ℕ}
  (T : Ideal (MvPolynomial J A)) [IsLocalHom φ]

variable [Finite J] in
/-- In finitely many variables there are finitely many exponents of total degree `d`. -/
instance : Fintype (degree ⁻¹' {d} : Set (J →₀ ℕ)) := (finite_of_degree_eq d).fintype

/-! ### A degree bound for monomial ideals -/

/-- `d` is a degree bound for monomial ideals in the variables `J` with counts `σ`: every monomial
ideal `M` that leaves out at most `σ i` monomials of degree `r ^ i` for all `i ≤ d` does so for
all `i`. -/
def IsCutDegree (J : Type) (d r : ℕ) (σ : ℕ → ℕ) : Prop :=
  ∀ M : AddSemigroupIdeal (J →₀ ℕ), (∀ i ≤ d, (degree ⁻¹' {r ^ i} \ M.carrier).ncard ≤ σ i) →
      ∀ i : ℕ, (degree ⁻¹' {r ^ i} \ M.carrier).ncard ≤ σ i

/-- For a subgroup `T` of an additive group `G`, the integer part of the square root of the number
of `y` with `r ^ j • y ∈ T`. -/
def thetaRanks {G : Type*} [AddGroup G] (T : AddSubgroup G) (r j : ℕ) : ℕ :=
  (Nat.card {y : G // r ^ j • y ∈ T}).sqrt

/-- Every large enough `d` is a degree bound (`IsCutDegree`) for monomial ideals in finitely many
variables `J` with counts `σ`. -/
lemma eventually_isCutDegree (J : Type) [Finite J] (r : ℕ) (σ : ℕ → ℕ) :
    ∀ᶠ d : ℕ in Filter.atTop, IsCutDegree J d r σ := by
  -- Noetherian induction on a subideal `N` of `M`: either `N` already leaves few monomials in
  -- every degree `r ^ i`, or it leaves too many in one such degree, and then `M` contains one of
  -- these finitely many monomials, so a larger subideal.
  let Few (M : AddSemigroupIdeal (J →₀ ℕ)) (i : ℕ) : Prop :=
    (degree ⁻¹' {r ^ i} \ M.carrier).ncard ≤ σ i
  suffices h_above : ∀ N : AddSemigroupIdeal (J →₀ ℕ), ∀ᶠ d : ℕ in Filter.atTop,
      ∀ M ≥ N, (∀ i ≤ d, Few M i) → ∀ i : ℕ, Few M i from
    (h_above ⊥).mono fun d h_bot M ↦ h_bot M bot_le
  intro N
  induction N using WellFoundedGT.induction with | ind N ih => ?_
  by_cases h_few : ∀ i : ℕ, Few N i
  · exact .of_forall fun d M hNM _ i ↦ (ncard_le_ncard (sdiff_le_sdiff_left hNM)).trans (h_few i)
  obtain ⟨i, h_many⟩ := not_forall.mp h_few
  -- Adding a monomial of degree `r ^ i` outside `N` gives a larger ideal.
  have h_lt (m : J →₀ ℕ) (hm : m ∈ degree ⁻¹' {r ^ i} \ N.carrier) : N < N ⊔ closure {m} :=
    left_lt_sup.mpr fun h_le ↦ hm.2 (closure_le.mp h_le (mem_singleton m))
  -- One `d` serves for all the finitely many ideals `N ⊔ closure {m}`.
  have h_larger : ∀ᶠ d : ℕ in Filter.atTop, ∀ m ∈ degree ⁻¹' {r ^ i} \ N.carrier,
      ∀ M ≥ N ⊔ closure {m}, (∀ i ≤ d, Few M i) → ∀ i : ℕ, Few M i :=
    (finite_of_degree_eq _).sdiff.eventually_all.mpr fun m hm ↦ ih _ (h_lt m hm)
  filter_upwards [h_larger, Filter.mem_atTop i] with d h_cut hd M hNM hM
  -- `M` leaves out fewer monomials of degree `r ^ i` than `N`, so contains one outside `N`.
  obtain ⟨m, hm, hmM⟩ :
      ∃ m ∈ degree ⁻¹' {r ^ i} \ N.carrier, m ∉ degree ⁻¹' {r ^ i} \ M.carrier :=
    not_subset.mp fun h_sub ↦ h_many ((ncard_le_ncard h_sub).trans (hM i hd))
  have hm_mem : m ∈ M := not_not.mp fun hm_not ↦ hmM ⟨hm.1, hm_not⟩
  exact h_cut m hm M (sup_le hNM (closure_le.mpr (singleton_subset_iff.mpr hm_mem))) hM

open MvPolynomial Module Submodule Ideal.Quotient Matrix LinearMap Finite

/-- The image of a submodule of `A[X]` in the quotient `A[X] ⧸ T`. -/
abbrev imageMod : Submodule A (MvPolynomial J A) → Submodule A (MvPolynomial J A ⧸ T) :=
  Submodule.map (mkₐ A T).toLinearMap

/-- An ideal `I` of polynomials over the field `k` in the variables `J` is cut out by the points
`p a` of `k ^ J` in the chart `c`, with ranks `σ j` in every degree `r ^ j` and the vanishing
condition in the degrees `r ^ j` with `j ≤ i`: the ideal `I` contains `X c - 1`. For each `j`,
the forms of degree `r ^ j` span a space of dimension `σ j` modulo `I`. For `j ≤ i`, the forms of
degree `r ^ j` in `I` are exactly those that vanish at all the points `p a`. -/
structure IsCutOut (r i : ℕ) (σ : ℕ → ℕ) (c : J) (p : ι → J → k) (I : Ideal (MvPolynomial J k)) :
    Prop where
  /-- The coordinate `X c` is `1` modulo `I`: the ideal lives in the affine chart `c`. -/
  X_sub_one_mem : X c - 1 ∈ I
  /-- The forms of degree `r ^ j` span a space of dimension `σ j` modulo `I`. -/
  rank (j : ℕ) : finrank k (imageMod I (homogeneousSubmodule J k (r ^ j))) = σ j
  /-- For `j ≤ i`, a form of degree `r ^ j` lies in `I` iff it vanishes at all the points `p a`. -/
  mem_iff_vanish (j : ℕ) (hj : j ≤ i) (f : MvPolynomial J k)
    (hf : f ∈ homogeneousSubmodule J k (r ^ j)) : f ∈ I ↔ ∀ a : ι, eval (p a) f = 0

/-- A polynomial supported on exponents of total degree `d` outside a set `M` is a form of degree
`d`. -/
lemma restrictSupport_le_homogeneousSubmodule {M : Set (J →₀ ℕ)} :
    restrictSupport A (degree ⁻¹' {d} \ M) ≤ homogeneousSubmodule J A d :=
  (restrictSupport_mono A sdiff_le).trans (homogeneousSubmodule_eq_finsupp_supported J A d).ge

variable [Finite J] in
/-- In finitely many variables the forms of degree `d` form a finite `A`-module. -/
instance : Module.Finite A (homogeneousSubmodule J A d) := of_fg (homogeneousSubmodule_fg J A d)

/-! ### Flatness -/

/-- Division with remainder. Let `φ : A →+* k` be a local homomorphism to a field. If every exponent
in `W` leads the nonzero reduction along `φ` of a form in `T`, then modulo any ideal `I` containing
the image of `T` the monomials of degree `d` outside `W` span the forms of degree `d`. -/
lemma imageMod_homogeneousSubmodule_eq [Finite J] (o : MonomialOrder J) {W : Set (J →₀ ℕ)}
    (h_lead : ∀ m ∈ W, ∃ g ∈ T,
      m = o.degree (g.map φ) ∧ g.IsHomogeneous m.degree ∧ m ∈ (g.map φ).support)
    {B : Type} [CommRing B] (ρ : A →+* B) {I : Ideal (MvPolynomial J B)}
    (hI : ∀ f ∈ T, f.map ρ ∈ I) :
    imageMod I (homogeneousSubmodule J B d) =
      imageMod I (restrictSupport B (degree ⁻¹' {d} \ W)) := by
  classical
  -- The coefficients of the chosen forms `g m` at the exponents in `W` form an invertible matrix,
  -- so subtracting a combination of the `g m` from a form `f` removes all its monomials in `W`.
  let V : Set (J →₀ ℕ) := degree ⁻¹' {d} ∩ W
  have h_choice (m : V) : ∃ g ∈ T, (m : J →₀ ℕ) = o.degree (g.map φ) ∧ g.IsHomogeneous d ∧
      (g.map φ).coeff (m : J →₀ ℕ) ≠ 0 := by
    obtain ⟨hm_deg, hmW⟩ := m.prop
    obtain ⟨g, hgT, hg_lead, hg_form, hg_supp⟩ := h_lead m hmW
    rw [mem_singleton_iff.mp hm_deg] at hg_form
    exact ⟨g, hgT, hg_lead, hg_form, MvPolynomial.mem_support_iff.mp hg_supp⟩
  choose g hgT hg_lead hg_form hg_coeff using h_choice
  refine (map_mono restrictSupport_le_homogeneousSubmodule).antisymm' ?_
  rintro x ⟨f, hf, hfx⟩
  let G : Matrix V V A := of fun m m' : V ↦ (g m).coeff m'.val
  -- Modulo `φ` the matrix is lower triangular for the monomial order, with nonzero diagonal.
  have h_tri (m m' : V) (h_lt : o.toSyn m.val < o.toSyn m'.val) : φ (G m m') = 0 := by
    rw [hg_lead m] at h_lt
    simpa [G, coeff_map] using o.coeff_eq_zero_of_lt h_lt
  have h_diag (m : V) : φ (G m m) ≠ 0 := by simpa [G, coeff_map] using hg_coeff m
  have h_det : IsUnit (φ G.det) := by
    let synOrder : LinearOrder (J →₀ ℕ) := o.toSyn.linearOrder
    rw [φ.map_det, det_of_isLowerTriangular (φ.mapMatrix G) h_tri]
    exact (Finset.prod_ne_zero_iff.mpr fun m _ ↦ h_diag m).isUnit
  -- `φ` is a local homomorphism, so `G.det` itself is a unit.
  have hG_det : IsUnit G.det := .of_map φ G.det h_det
  have hG : IsUnit (ρ.mapMatrix G) := (G.isUnit_iff_isUnit_det.mpr hG_det).map ρ.mapMatrix
  obtain ⟨c, hc⟩ : ∃ c : V → B, c ᵥ* ρ.mapMatrix G = fun m : V ↦ f.coeff m.val :=
    vecMul_surjective_iff_isUnit.mpr hG fun m : V ↦ f.coeff m.val
  have h_form : f - ∑ m : V, c m • (g m).map ρ ∈ homogeneousSubmodule J B d :=
    sub_mem hf (sum_smul_mem _ c fun m _ ↦ (hg_form m).map ρ)
  refine ⟨f - ∑ m : V, c m • (g m).map ρ, (mem_restrictSupport_iff B).mpr fun a ha ↦ ?_, ?_⟩
  · have ha_deg : a ∈ degree ⁻¹' {d} := (h_form.degree_eq_sum_deg_support ha).symm
    -- If `a ∈ W`, the choice of `c` makes the coefficient at `a` vanish.
    refine ⟨ha_deg, fun haW ↦ ?_⟩
    have h_coeff : ∑ m : V, c m * ρ ((g m).coeff a) = f.coeff a := by
      simpa [vecMul_eq_sum, G] using congrFun hc ⟨a, ha_deg, haW⟩
    simp [← h_coeff, coeff_map] at ha
  · -- The forms `g m` lie in `T`, so their images lie in `I` and vanish modulo `I`.
    have h_sum : ∑ m : V, c m • (g m).map ρ ∈ I :=
      sum_mem fun m _ ↦ Submodule.smul_of_tower_mem I _ (hI (g m) (hgT m))
    rwa [AlgHom.toLinearMap_apply, map_sub, mkₐ_eq_mk, eq_zero_iff_mem.mpr h_sum, sub_zero]

/-- If the monomials in `S` span modulo `I` a space of dimension at least their number, they are
independent modulo `I`. -/
lemma eq_zero_of_ncard_le_finrank {I : Ideal (MvPolynomial J k)} {S : Set (J →₀ ℕ)} [Finite S]
    (h_rank : S.ncard ≤ finrank k (imageMod I (restrictSupport k S))) {s : MvPolynomial J k}
    (hs : s ∈ restrictSupport k S) (hsI : s ∈ I) : s = 0 := by
  let b : Basis S k (restrictSupport k S) := basisRestrictSupport k S
  have : Module.Finite k (restrictSupport k S) := of_basis b
  have h_disj : Disjoint (restrictSupport k S) (ker (mkₐ k I).toLinearMap) :=
    disjoint_ker_of_finrank_le _ ((finrank_eq_nat_card_basis b).trans_le h_rank)
  exact disjoint_def.mp h_disj s hs (eq_zero_iff_mem.mpr hsI)

/-- Among the monomials in `S` there are as many independent ones modulo `I` as the dimension of
the space they span modulo `I`. -/
lemma exists_independent_monomials (I : Ideal (MvPolynomial J k)) (S : Set (J →₀ ℕ)) [Finite S] :
    ∃ e : Fin (finrank k (imageMod I (restrictSupport k S))) → S,
      LinearIndependent k fun b : Fin (finrank k (imageMod I (restrictSupport k S))) ↦
        mkₐ k I (monomial (e b) 1) := by
  rw [restrictSupport_eq_span, imageMod, ← span_image, image_image]
  -- The classes of the monomials in `S` contain a basis `v` of their span.
  let C : Set (MvPolynomial J k ⧸ I) := (fun m : J →₀ ℕ ↦ mkₐ k I (monomial m 1)) '' S
  have h_finite : Module.Finite k (span k C) := Module.Finite.span_of_finite k (toFinite C)
  obtain ⟨v, hv, -, h_indep⟩ : ∃ v : Fin (finrank k (span k C)) → MvPolynomial J k ⧸ I,
      (∀ b : Fin (finrank k (span k C)), v b ∈ C) ∧
        span k (Set.range v) = span k C ∧ LinearIndependent k v :=
    exists_fun_fin_finrank_span_eq k C
  choose e he hev using hv
  refine ⟨fun b ↦ ⟨e b, he b⟩, ?_⟩
  rwa [← funext hev] at h_indep

/-- Let `I` be cut out by the points `p a` in the chart `c` (`IsCutOut`: ranks `σ j` in the
degrees `r ^ j`, vanishing conditions up to the degree `r ^ i`). Monomials `μ b`, `b < n`, of a
degree `r ^ j` with `j ≤ i` are dependent modulo `I` iff the `n × n` determinant of their values at
`n` of the points `p a` vanishes for every choice of the `n` points (repetitions allowed). -/
lemma IsCutOut.minors_eq_zero_iff {r i j n : ℕ} {σ : ℕ → ℕ} {c : J} {p : ι → J → k}
    {I : Ideal (MvPolynomial J k)} (hI : IsCutOut r i σ c p I) (hj : j ≤ i) {μ : Fin n → J →₀ ℕ}
    (hμ : ∀ b : Fin n, (μ b).degree = r ^ j) :
    (∀ a : Fin n → ι, (of fun s b : Fin n ↦ eval (p (a s)) (monomial (μ b) 1)).det = 0) ↔
      ¬LinearIndependent k fun b : Fin n ↦ mkₐ k I (monomial (μ b) 1) := by
  -- A combination of the monomials lies in `I` iff it vanishes at all the points.
  have h_rel (t : Fin n → k) : ∑ b : Fin n, t b • mkₐ k I (monomial (μ b) 1) = 0 ↔
      ∑ b : Fin n, t b • (fun x : ι ↦ eval (p x) (monomial (μ b) 1)) = 0 := by
    have h_form : ∑ b : Fin n, t b • monomial (μ b) (1 : k) ∈ homogeneousSubmodule J k (r ^ j) :=
      sum_smul_mem _ t fun b _ ↦ isHomogeneous_monomial 1 (hμ b)
    simp_rw [← map_smul (mkₐ k I)]
    rw [← map_sum, mkₐ_eq_mk, eq_zero_iff_mem, hI.mem_iff_vanish j hj _ h_form]
    simp [funext_iff]
  refine (New.det_eval_eq_zero_iff_not_linearIndependent
    (v := fun b x ↦ eval (p x) (monomial (μ b) 1))).trans ?_
  simp only [Fintype.linearIndependent_iff, h_rel]

/-- The determinant whose first row is the `n + 1` monomials `μ l` and whose other rows are their
values at the `n` points `p s`, expanded along the first row. -/
def cofactorForm {n : ℕ} (p : Fin n → J → A) (μ : Fin (n + 1) → J →₀ ℕ) : MvPolynomial J A :=
  ∑ l : Fin (n + 1),
    ((of fun s b : Fin n ↦ eval (p s) (monomial (μ (l.succAbove b)) 1)).det * (-1) ^ l.val) •
      monomial (μ l) 1

/-- Suppose `I`, an ideal of polynomials over `k` in the variables `J`, is cut out in the chart `c`
by the points `ρ ∘ P a` in the sense of `IsCutOut r i σ c`. This means `X c - 1 ∈ I`, forms of
degree `r ^ j` span a space of dimension `σ j` modulo `I`, and for `j ≤ i` the forms of degree
`r ^ j` in `I` are exactly those that vanish at all the points `ρ ∘ P a`. For `j ≤ i`, take
`σ j + 1` monomials `μ` of degree `r ^ j` and `σ j` of the points `P (a s)`, and form their
`cofactorForm`: the determinant whose first row is the monomials and whose other rows are their
values at the points, expanded along the first row. Its image under `ρ` lies in `I`. -/
lemma IsCutOut.map_cofactorForm_mem [Finite J]
    {ρ : A →+* k} {r i j : ℕ} {σ : ℕ → ℕ} {c : J} {P : ι → J → A}
    {I : Ideal (MvPolynomial J k)} (hI : IsCutOut r i σ c (fun a : ι ↦ ρ ∘ P a) I) (hj : j ≤ i)
    (a : Fin (σ j) → ι) {μ : Fin (σ j + 1) → J →₀ ℕ}
    (hμ : ∀ b : Fin (σ j + 1), (μ b).degree = r ^ j) :
    MvPolynomial.map ρ (cofactorForm (fun s : Fin (σ j) ↦ P (a s)) μ) ∈ I := by
  -- Modulo `I` the forms have rank `σ j` only, so the monomials are dependent.
  have h_dep : ¬LinearIndependent k fun b ↦ mkₐ k I (monomial (μ b) 1) := by
    intro h_indep
    let v (b : Fin (σ j + 1)) : imageMod I (homogeneousSubmodule J k (r ^ j)) :=
      ⟨mkₐ k I (monomial (μ b) 1), mem_map_of_mem (isHomogeneous_monomial 1 (hμ b))⟩
    have hv : LinearIndependent k v := .of_comp (Submodule.subtype _) h_indep
    simpa [hI.rank] using hv.fintype_card_le_finrank
  -- The cofactor form is a combination of monomials of degree `r ^ j`.
  have h_form : (cofactorForm (fun s : Fin (σ j) ↦ P (a s)) μ).IsHomogeneous (r ^ j) :=
    sum_smul_mem (homogeneousSubmodule J A _) _ fun l _ ↦ isHomogeneous_monomial 1 (hμ l)
  refine (hI.mem_iff_vanish j hj _ (h_form.map ρ)).mpr fun x ↦ ?_
  -- The value of the form at a point `x` is the minor at the points `x, a 0, a 1, …`, expanded
  -- along its first row.
  calc eval (ρ ∘ P x) (MvPolynomial.map ρ (cofactorForm (fun s ↦ P (a s)) μ))
    _ = ∑ l : Fin (σ j + 1), (-1) ^ (l : ℕ) * eval (ρ ∘ P x) (monomial (μ l) 1) *
          (of fun s b : Fin (σ j) ↦ eval (ρ ∘ P (a s)) (monomial (μ (l.succAbove b)) 1)).det := by
      simp [cofactorForm, smul_eq_C_mul, mul_rotate (det _), Function.comp_def, RingHom.map_det,
        Matrix.map, map_eval]
    _ = (of fun s b : Fin (σ j + 1) ↦ eval (ρ ∘ P (vecCons x a s)) (monomial (μ b) 1)).det := by
      rw [det_succ_row_zero]
      rfl
    _ = 0 := (hI.minors_eq_zero_iff hj hμ).mpr h_dep (vecCons x a)

open scoped Classical in
/-- The exponents that lead, for the monomial order `o`, the nonzero reduction along `φ` of a form
in `T`. They form a monomial ideal. -/
def leadingExponents (o : MonomialOrder J) : AddSemigroupIdeal (J →₀ ℕ) where
  carrier :=
    {m : J →₀ ℕ | ∃ g ∈ T, m = o.degree (g.map φ) ∧ g.IsHomogeneous m.degree ∧
      m ∈ (g.map φ).support}
  vadd_mem' n m := by
    -- If `g` shows that `m` is leading, then `X ^ n * g` shows that `n + m` is leading.
    rintro ⟨g, hgT, hm_lead, hg_form, hm_supp⟩
    have h_map : (monomial n 1 * g).map φ = monomial n 1 * g.map φ := by simp
    have hn_ne : (monomial n 1 : MvPolynomial J k) ≠ 0 := by simp
    have hg_ne : g.map φ ≠ 0 := ne_zero_iff.mpr ⟨m, MvPolynomial.mem_support_iff.mp hm_supp⟩
    have h_lead : n + m = o.degree ((monomial n 1 * g).map φ) := by
      rw [h_map, o.degree_mul hn_ne hg_ne, o.degree_monomial, ite_eq_right one_ne_zero, ← hm_lead]
    refine ⟨monomial n 1 * g, T.mul_mem_left _ hgT, h_lead, ?_, ?_⟩
    · simpa using (isHomogeneous_monomial 1 rfl).mul hg_form
    · simpa [h_lead, h_map] using o.degree_mem_support (mul_ne_zero hn_ne hg_ne)

/-- Let `φ : A →+* k` be a local homomorphism to a field, and let `I₀` be cut out in chart `c` by
the points `φ ∘ P a` (`IsCutOut`: `X c - 1 ∈ I₀`, the forms of degree `r ^ j` have rank `σ j` modulo
`I₀`, with the vanishing condition for `j ≤ i`). Let `T` reduce into `I₀`, let `j ≤ i`, and let `T`
contain the cofactor form (the determinant with first row the monomials, other rows their values at
the points) of any `σ j + 1` monomials of degree `r ^ j` at any `σ j` of the `P a`. Then at most
`σ j` monomials of degree `r ^ j` are not leading exponents of `T`. -/
lemma IsCutOut.ncard_diff_leadingExponents_le [Finite J]
    (o : MonomialOrder J) {r i j : ℕ} {σ : ℕ → ℕ} {c : J}
    {P : ι → J → A} {I₀ : Ideal (MvPolynomial J k)}
    (hI₀ : IsCutOut r i σ c (fun a : ι ↦ φ ∘ P a) I₀) (hj : j ≤ i)
    (h_reduce : ∀ f ∈ T, MvPolynomial.map φ f ∈ I₀)
    (h_cofactor : ∀ (a : Fin (σ j) → ι) (μ : Fin (σ j + 1) → J →₀ ℕ),
      (∀ b : Fin (σ j + 1), (μ b).degree = r ^ j) →
        cofactorForm (fun s : Fin (σ j) ↦ P (a s)) μ ∈ T) :
    (degree ⁻¹' {r ^ j} \ (leadingExponents φ T o).carrier).ncard ≤ σ j := by
  classical
  -- Choose `σ j` standard (not leading) monomials `e b` independent modulo `I₀`, and points `a`
  -- at which their minor is nonzero. Suppose that a standard monomial `m` is not among them.
  let std : Set (J →₀ ℕ) := degree ⁻¹' {r ^ j} \ (leadingExponents φ T o).carrier
  have h_fin : Finite std := (finite_of_degree_eq (r ^ j)).sdiff
  have h_div : imageMod I₀ (homogeneousSubmodule J k (r ^ j)) =
      imageMod I₀ (restrictSupport k std) :=
    imageMod_homogeneousSubmodule_eq φ T o (fun _ hm ↦ hm) φ h_reduce
  obtain ⟨e, he⟩ : ∃ e : Fin (σ j) → std,
      LinearIndependent k fun b ↦ mkₐ k I₀ (monomial (e b) 1) := by
    rw [← hI₀.rank j, h_div]
    exact exists_independent_monomials I₀ std
  have h_std_deg (m : J →₀ ℕ) (hm : m ∈ std) : m.degree = r ^ j := hm.left
  obtain ⟨a, ha⟩ : ∃ a : Fin (σ j) → ι,
      (of fun s b ↦ eval (φ ∘ P (a s)) (monomial (e b) 1)).det ≠ 0 := by
    by_contra! h_zero
    exact (hI₀.minors_eq_zero_iff hj fun b ↦ h_std_deg _ (e b).prop).mp h_zero he
  -- It suffices that every standard monomial is among the `e b`.
  suffices h_surj : Function.Surjective e by
    simpa using Nat.card_le_card_of_surjective e h_surj
  intro m
  by_contra! hm
  -- `g` is the cofactor form of `m` and the `e b`.
  let μ : Fin (σ j + 1) → J →₀ ℕ := vecCons m fun b ↦ e b
  have hμ (l : Fin (σ j + 1)) : μ l ∈ std := l.cases m.prop fun b ↦ (e b).prop
  let g : MvPolynomial J A := cofactorForm (fun s ↦ P (a s)) μ
  have hg_std : g ∈ restrictSupport A std :=
    sum_smul_mem _ _ fun l _ ↦ (monomial_mem_restrictSupport A).mpr (.inl (hμ l))
  have hg_mem : g ∈ T := h_cofactor a μ fun l ↦ h_std_deg _ (hμ l)
  -- As `m` is not among the `e b`, the coefficient of `m` in the reduction of `g` is the minor of
  -- the `e b` at the points `a`, which is nonzero.
  have h_coeff : (g.map φ).coeff m = (of fun s b ↦ eval (φ ∘ P (a s)) (monomial (e b) 1)).det := by
    simp [g, cofactorForm, μ, Fin.sum_univ_succ, SetCoe.ext_iff, hm, coeff_map, RingHom.map_det,
      Matrix.map, map_eval]
  have hg_ne : (g.map φ).coeff m ≠ 0 := h_coeff.trans_ne ha
  -- So the reduction has a leading exponent; it is leading, yet occurs in `g`, so is standard.
  have h_top : o.degree (g.map φ) ∈ (g.map φ).support :=
    o.degree_mem_support (ne_zero_iff.mpr ⟨m, hg_ne⟩)
  obtain ⟨h_deg, h_not_lead⟩ : o.degree (g.map φ) ∈ std := hg_std (support_map_subset _ g h_top)
  have hg_form : g.IsHomogeneous (o.degree (g.map φ)).degree := by
    rw [mem_singleton_iff.mp h_deg]
    exact restrictSupport_le_homogeneousSubmodule hg_std
  exact h_not_lead ⟨g, hg_mem, rfl, hg_form, h_top⟩

/-- Let `S j` be sets of exponents such that modulo `T` every polynomial of total degree at most `j`
is congruent to one supported on `S j`, and no nonzero polynomial supported on `S j` lies in `T`.
Then `A[X] ⧸ T` is flat over `A`. -/
private lemma flat_of_exists_restrictSupport_of_eq_zero {S : ℕ → Set (J →₀ ℕ)}
    (h_span : ∀ (j : ℕ) (x : MvPolynomial J A), x.totalDegree ≤ j →
      ∃ s ∈ restrictSupport A (S j), mkₐ A T s = mkₐ A T x)
    (h_free : ∀ (j : ℕ) (s : MvPolynomial J A), s ∈ restrictSupport A (S j) → s ∈ T → s = 0) :
    Flat A (MvPolynomial J A ⧸ T) := by
  -- Lift the `x l` to polynomials supported on one `S j`. The relation then holds in the
  -- polynomial ring, which is flat over `A`, so it is trivial there and in the quotient.
  refine .of_forall_isTrivialRelation fun {len b x} hx ↦ ?_
  have h_lift (l : Fin len) : ∃ s ∈ restrictSupport A (S (⨆ l, (x l).out.totalDegree)),
      mkₐ A T s = x l := by
    simpa using h_span _ (x l).out (le_ciSup (fun l ↦ (x l).out.totalDegree) l)
  choose s hs hsx using h_lift
  have h_sum_mem : ∑ l, b l • s l ∈ T := by
    rw [← eq_zero_iff_mem, ← mkₐ_eq_mk A]
    simpa only [map_sum, map_smul, hsx] using hx
  have h_rel : ∑ l, b l • s l = 0 := h_free _ _ (sum_smul_mem _ b fun l _ ↦ hs l) h_sum_mem
  obtain ⟨n, a, y, hy_s, hy_b⟩ := Flat.isTrivialRelation_of_sum_smul_eq_zero h_rel
  have hx_sum (l : Fin len) : x l = ∑ i, a l i • mk T (y i) := by simp [← hsx, hy_s]
  exact ⟨n, a, mk T ∘ y, hx_sum, hy_b⟩

/-- Let `φ : A → k` be a local homomorphism to a field, let the maps `ψ n : A → K` have no common
nonzero kernel element, let `1 < r`, and let `i` be a degree bound for the counts `σ`
(`IsCutDegree J i r σ`). Assume that `I₀` is cut out (`IsCutOut`) in the chart `c` by the points
`φ (P a)`, with ranks `σ` and the vanishing condition up to degree `r ^ i`, and that each `I n` is
cut out in the same way by the points `ψ n (P a)`. Then the ideal `T`, consisting of the polynomials
`f` over `A` with `ψ n f ∈ I n` for every `n`, generates `I₀` along `φ`, and `A[X] ⧸ T` is flat over
`A`. -/
lemma eq_map_and_flat_of_isCutOut [Finite J]
    [Field K] {ψ : κ → A →+* K} {r i : ℕ} {σ : ℕ → ℕ} {c : J}
    {I₀ : Ideal (MvPolynomial J k)} (hψ : ∀ a : A, (∀ n : κ, ψ n a = 0) → a = 0) (hr : 1 < r)
    (h_degree : IsCutDegree J i r σ) {P : ι → J → A} {I : κ → Ideal (MvPolynomial J K)}
    (hI₀ : IsCutOut r i σ c (fun a : ι ↦ φ ∘ P a) I₀)
    (hI : ∀ n : κ, IsCutOut r i σ c (fun a : ι ↦ ψ n ∘ P a) (I n))
    (hT : ∀ f : MvPolynomial J A, f ∈ T ↔ ∀ n : κ, MvPolynomial.map (ψ n) f ∈ I n) :
    I₀ = T.map (MvPolynomial.map φ) ∧
      Flat A (MvPolynomial J A ⧸ T) := by
  -- Fix a monomial order. Call an exponent leading if it leads the nonzero reduction of a form in
  -- `T₀ = T ⊓ φ⁻¹ I₀`, else standard. In degrees `r ^ j` the standard monomials span modulo `T₀`
  -- (division) and number at most `σ j` (determinants), so are independent modulo `I₀` and `T`;
  -- both claims follow.
  obtain ⟨o⟩ : Nonempty (MonomialOrder J) := by
    -- any linear order of `J` gives the lexicographic monomial order (`J` is finite)
    obtain ⟨linOrder, -⟩ := exists_wellFoundedLT (α := J)
    exact ⟨MonomialOrder.lex⟩
  let T₀ : Ideal (MvPolynomial J A) := T ⊓ I₀.comap (map φ)
  have hT₀_le : T₀ ≤ T := inf_le_left
  have h_reduce₀ (f : MvPolynomial J A) (hf : f ∈ T₀) : map φ f ∈ I₀ :=
    Ideal.mem_comap.mp (Ideal.mem_inf.mp hf).2
  let lead : AddSemigroupIdeal (J →₀ ℕ) := leadingExponents φ T₀ o
  let std (d : ℕ) : Set (J →₀ ℕ) := degree ⁻¹' {d} \ lead.carrier
  have h_fin (d : ℕ) : Finite (std d) := (finite_of_degree_eq d).sdiff
  have h_div {d : ℕ} {R : Type} [CommRing R] (ρ : A →+* R) {N : Ideal (MvPolynomial J R)}
      (hN : ∀ f ∈ T₀, map ρ f ∈ N) :
      imageMod N (homogeneousSubmodule J R d) = imageMod N (restrictSupport R (std d)) :=
    imageMod_homogeneousSubmodule_eq φ T₀ o (fun _ hm ↦ hm) ρ hN
  have h_rank₀ (j : ℕ) : σ j = finrank k (imageMod I₀ (restrictSupport k (std (r ^ j)))) := by
    rw [← h_div φ h_reduce₀, hI₀.rank]
  have h_rank (n : κ) (j : ℕ) :
      σ j = finrank K (imageMod (I n) (restrictSupport K (std (r ^ j)))) := by
    rw [← h_div (ψ n) fun f hf ↦ (hT f).mp (hT₀_le hf) n, (hI n).rank]
  -- Key step: at most `σ j` monomials of degree `r ^ j` are standard. By `h_degree`, `j ≤ i`
  -- suffices, and then the cofactor forms lie in `T₀`.
  have h_card : ∀ j : ℕ, (std (r ^ j)).ncard ≤ σ j := by
    refine h_degree lead fun j hj ↦ ?_
    exact hI₀.ncard_diff_leadingExponents_le φ T₀ o hj h_reduce₀ fun a μ hμ ↦
      ⟨(hT _).mpr fun n ↦ (hI n).map_cofactorForm_mem hj a hμ, hI₀.map_cofactorForm_mem hj a hμ⟩
  have h_chart : X c - 1 ∈ T₀ := by simp [T₀, hT, (hI _).X_sub_one_mem, hI₀.X_sub_one_mem]
  -- Spanning: along any `ρ : A →+* R` and modulo any `N` containing the image of `T₀`, a
  -- polynomial is homogenised by `X c`, which is `1` modulo `N`, and then divided.
  have h_span {R : Type} [CommRing R] {ρ : A →+* R} {N : Ideal (MvPolynomial J R)} {j : ℕ}
      {x : MvPolynomial J R} (hN : ∀ f ∈ T₀, map ρ f ∈ N) (hx : x.totalDegree ≤ j) :
      ∃ s ∈ restrictSupport R (std (r ^ j)), mkₐ R N s = mkₐ R N x := by
    have h_one : mkₐ R N (X c) = 1 := Ideal.Quotient.eq.mpr (by simpa using hN _ h_chart)
    obtain ⟨G, hG, hGx⟩ :=
      exists_homogenization (isHomogeneous_X R c) x (hx.trans (Nat.lt_pow_self hr).le)
    exact (h_div ρ hN).le ⟨G, hG, hGx _ h_one⟩
  -- Independence over `A`: the standard monomials are independent modulo each `I n`, so the
  -- coefficients of a relation modulo `T` are killed by every `ψ n`.
  have h_free {j : ℕ} {s : MvPolynomial J A} (hs : s ∈ restrictSupport A (std (r ^ j)))
      (hsT : s ∈ T) : s = 0 := by
    refine s.ext 0 fun m ↦ hψ (s.coeff m) fun n ↦ ?_
    have h_map : map (ψ n) s = 0 := eq_zero_of_ncard_le_finrank ((h_card j).trans_eq (h_rank n j))
      (fun _ h ↦ hs (support_map_subset _ _ h)) ((hT s).mp hsT n)
    simp [← coeff_map, h_map]
  -- An `f ∈ T` has remainder `0` modulo `T₀`, so lies in `T₀`, and its reduction lies in `I₀`.
  have h_le : T.map (map φ) ≤ I₀ := by
    refine T.map_le_of_le_comap fun f hf ↦ ?_
    obtain ⟨s, hs, hsf⟩ :=
      h_span (ρ := RingHom.id A) (N := T₀) (by simp [MvPolynomial.map_id]) f.totalDegree.le_refl
    have hs0 : s = 0 :=
      h_free hs ((T.sub_mem_iff_left hf).mp (hT₀_le (Ideal.Quotient.eq.mp hsf)))
    rw [hs0, map_zero, eq_comm, mkₐ_eq_mk, eq_zero_iff_mem] at hsf
    exact Ideal.mem_comap.mpr (h_reduce₀ f hsf)
  refine ⟨h_le.antisymm' fun f hf ↦ ?_, ?_⟩
  · -- The remainder of `f ∈ I₀` modulo the image of `T` lies in `I₀`, so is zero.
    obtain ⟨s, hs, hsf⟩ :=
      h_span (N := T.map (map φ)) (fun g hg ↦ T.mem_map_of_mem (map φ) (hT₀_le hg))
        f.totalDegree.le_refl
    have hs0 : s = 0 := eq_zero_of_ncard_le_finrank ((h_card _).trans_eq (h_rank₀ _)) hs
      ((sub_mem_iff_left _ hf).mp (h_le (Ideal.Quotient.eq.mp hsf)))
    rwa [hs0, map_zero, eq_comm, mkₐ_eq_mk, eq_zero_iff_mem] at hsf
  · -- The standard monomials of the degrees `r ^ j` span modulo `T` and are independent.
    exact flat_of_exists_restrictSupport_of_eq_zero T (S := fun j ↦ std (r ^ j))
      (fun j x hx ↦ h_span (ρ := RingHom.id A)
        (fun f hf ↦ by simpa [MvPolynomial.map_id] using hT₀_le hf) hx)
      (fun j s hs hsT ↦ h_free hs hsT)

end CutOutIdeals

/-!
## The flat projective closure of a dense family of theta points

A map to projective space is a line bundle `New.LineBundle` with `New.LineBundle.IsLinearSystem`.
Its transition functions `transition i j` are the ratios of coordinates `s j / s i` on the chart
`opens i`. `New.LineBundle.IsHomogeneousCoords` gives the homogeneous coordinates of a point.
`New.IsSeparatingFamily ξ` adds to `New.IsDenseFamily ξ` that the scheme is reduced.
-/

section FlatClosure

open CategoryTheory AlgebraicGeometry Limits LineBundle MvPolynomial Scheme RingHom Flat pullback
  Over PointFn

/-- The ideals of a set `Z ⊂ K ^ J` are cut out at a point `t` of `S` with values in the field `K`
by the maps `P a` to projective space. That is: for every choice of charts `l a` of the `P a` that
contain `t` and every chart `c`, the vanishing ideal of the points `v ∈ Z` with `v c ≠ 0`, scaled to
`v c = 1`, satisfies `New.Variety.ThetaNull.IsCutOut r i σ c` for the affine coordinates of the
points `P a` at `t` (ranks `σ j` in the degrees `r ^ j`, and in the degrees `r ^ j` with `j ≤ i`
the forms of the ideal are those that vanish at these points). -/
def IsCutOutAt {J I K : Type} [Field K] {S : Scheme} (r i : ℕ) (σ : ℕ → ℕ) (P : I → LineBundle S J)
    (t : Spec (CommRingCat.of K) ⟶ S) (Z : Set (J → K)) : Prop :=
  -- `l a` is a chart of `P a` that contains `t`, in which `P a` gives a point of `K ^ J`
  ∀ l : I → J,
    (∀ a : I, LandsIn t ((P a).opens (l a))) →
    ∀ c : J,
      IsCutOut r i σ c (fun a j ↦ (P a).transition (l a) j (CommRingCat.of K) t)
        (⨅ v ∈ {v ∈ Z | v c ≠ 0}, RingHom.ker (MvPolynomial.eval fun j ↦ v j / v c))

/-- Let the `P a` be linear systems on `S` with charts `l a` that contain the point
`s : Spec R ⟶ S`, and let `t = Spec φ ≫ s` for a ring map `φ : R → K` to a field. If the
ideals of `Z` are cut out by `P` at `t`, then in each chart `c` they are cut out by the images
under `φ` of the affine coordinates of the `P a` at `s`. -/
lemma isCutOut_of_isCutOutAt {J I K : Type} {S : Scheme} {r i : ℕ} {σ : ℕ → ℕ} [Field K]
    {P : I → LineBundle S J} (hP : ∀ a : I, (P a).IsLinearSystem) {R : CommRingCat} {s : Spec R ⟶ S}
    {l : I → J} (hl : ∀ a : I, LandsIn s ((P a).opens (l a))) {φ : R ⟶ CommRingCat.of K}
    {t : Spec (CommRingCat.of K) ⟶ S} {Z : Set (J → K)} (ht : Spec.map φ ≫ s = t)
    (hZ : IsCutOutAt r i σ P t Z) (c : J) :
    IsCutOut r i σ c (fun a : I ↦ φ.hom ∘ fun j : J ↦ (P a).transition (l a) j R s)
      (⨅ v ∈ {v ∈ Z | v c ≠ 0}, RingHom.ker (MvPolynomial.eval fun j : J ↦ v j / v c)) := by
  subst ht
  -- The coordinates are regular on the chart, so they commute with `φ`.
  have h_coord (a : I) (j : J) :
      (P a).transition (l a) j (CommRingCat.of K) (Spec.map φ ≫ s) =
        φ ((P a).transition (l a) j R s) :=
    ((hP a).isRegularOn_transition (l a) j) φ s (hl a)
  simpa only [h_coord, Function.comp_def] using hZ l (fun a ↦ (hl a).comp (Spec.map φ)) c

/-- `A` is a flat projective family over `S` spanned by points `e n z` over the complex points
`η n` of `S`, with homogeneous coordinates `θ n z` in the linear system `N`. -/
structure IsFlatClosure {J W κ : Type} {S : Scheme} {η : κ → (Spec (CommRingCat.of ℂ) ⟶ S)}
    (θ : κ → W → J → ℂ) {A : Over S} (N : LineBundle A.left J)
    (e : ∀ n : κ, W → (Over.mk (η n) ⟶ A)) : Prop where
  /-- `A` is proper over `S`, and the linear system `N` separates points with the same image
  in `S`. -/
  isProjEmbedding : IsProjEmbedding N A.hom
  /-- `A` is flat over `S`. -/
  flat : Flat A.hom
  /-- The point `e n z` has homogeneous coordinates `θ n z`. -/
  isHomogeneousCoords (n : κ) (z : W) : IsHomogeneousCoords N (e n z).left (θ n z)
  /-- The fibre over `η n` is reduced, and the points `e n z` are dense in it. -/
  isSeparatingFamily_fibre (n : κ) :
    IsSeparatingFamily (X := pullback A.hom (η n)) fun z : W ↦
      pullback.lift (e n z).left (𝟙 (Spec (CommRingCat.of ℂ))) (e n z).w
  /-- Every point of `S` specialises to a geometric point over which the fibre is reduced. -/
  allSpecializeTo_isReduced : AllSpecializeTo S fun t ↦ IsReduced (pullback A.hom t)
  /-- `A` is reduced, and all the points `e n z` together are dense in it. -/
  isSeparatingFamily : IsSeparatingFamily fun s : κ × W ↦ (e s.1 s.2).left

/-- The chart `c` of the linear system `L` on a scheme `X` over `Spec R` is affine, and `u` presents
its ring of sections as a quotient of the polynomial ring in the affine coordinates. Here
`specMap ψ` is the morphism of spectra given by a ring map `ψ`, and `ofSection g B t` is the value
of a section `g` at a `B`-valued point `t`. -/
structure IsChartPresentation {J : Type} {X : Scheme} {R : CommRingCat} (L : LineBundle X J)
    (s : X ⟶ Spec R) (c : J) (u : MvPolynomial J R →+* Γ(X, L.opens c)) : Prop where
  /-- The chart is affine. -/
  isAffineOpen : IsAffineOpen (L.opens c)
  /-- Every section over the chart is a polynomial in the coordinates. -/
  surjective : Function.Surjective u
  /-- `u` is compatible with the structure maps to `Spec R`. -/
  specMap_comp_C : specMap (u.comp C) = isAffineOpen.fromSpec ≫ s
  /-- At a point `t` of the chart, `u f` is the value of `f` at the affine coordinates of `t`. -/
  ofSection_eq {B : CommRingCat} {t : Spec B ⟶ X} (ht : LandsIn t (L.opens c))
    (f : MvPolynomial J R) :
    ofSection (u f) B t = eval₂Hom (Spec.preimage (t ≫ s)).hom (L.transition c · B t) f

section Charts

variable {J : Type} {X : Scheme} {R : CommRingCat} {L : LineBundle X J} {s : X ⟶ Spec R}
  {u : ∀ c : J, MvPolynomial J R →+* Γ(X, L.opens c)}

/-- `X` is flat over `Spec R` if the ring of each chart is a flat `R`-module. -/
lemma flat_of_isChartPresentation (hu : ∀ c : J, IsChartPresentation L s c (u c))
    (h_flat : ∀ c : J, Module.Flat R (MvPolynomial J R ⧸ ker (u c))) : Flat s := by
  let charts : X.OpenCover :=
    (AffineOpenCover.ofIsOpenCover _ (cover L) fun c ↦ (hu c).isAffineOpen).openCover
  refine HasRingHomProperty.instIsZariskiLocalAtSource.of_openCover charts fun c ↦ ?_
  -- (`RespectsIso` takes the property with its implicit arguments, hence `@`)
  obtain ⟨h_comp_equiv, -⟩ : RingHom.RespectsIso @RingHom.Flat := respectsIso
  have h_alg : ((u c).comp C).Flat := h_comp_equiv _
    (quotientKerEquivOfSurjective (hu c).surjective) (flat_algebraMap_iff.mpr (h_flat c))
  have h_spec : Flat (specMap ((u c).comp C)) := SpecMap_iff.mpr h_alg
  rwa [(hu c).specMap_comp_C] at h_spec

/-- `X` is reduced if the ideal of each chart is radical. -/
lemma isReduced_of_isChartPresentation (hu : ∀ c : J, IsChartPresentation L s c (u c))
    (h_rad : ∀ c : J, (ker (u c)).IsRadical) : IsReduced X := by
  let charts : X.OpenCover :=
    (AffineOpenCover.ofIsOpenCover _ (cover L) fun c ↦ (hu c).isAffineOpen).openCover
  have h_chart (c : charts.I₀) : IsReduced (charts.X c) :=
    (affine_isReduced_iff _).mpr
      ((ker_isRadical_iff_reduced_of_surjective (hu c).surjective).mp (h_rad c))
  exact IsReduced.of_openCover X charts

end Charts

/-- Complex points `x v` of a complex scheme `X`, with homogeneous coordinates `θ v`, are dense if
in each chart `c` a polynomial vanishing at all the `θ v` with `θ v c ≠ 0`, scaled to `θ v c = 1`,
lies in the ideal of the chart. -/
lemma isDenseFamily_of_isChartPresentation {J W : Type} {X : Scheme} {L : LineBundle X J}
    {s : X ⟶ Spec (CommRingCat.of ℂ)} {u : ∀ c : J, MvPolynomial J ℂ →+* Γ(X, L.opens c)}
    (hu : ∀ c : J, IsChartPresentation L s c (u c)) {x : W → (Spec (CommRingCat.of ℂ) ⟶ X)}
    (hx_over : ∀ v : W, x v ≫ s = 𝟙 (Spec (CommRingCat.of ℂ))) {θ : W → J → ℂ}
    (hx : ∀ v : W, L.IsHomogeneousCoords (x v) (θ v))
    (h_ideal : ∀ c : J,
      ⨅ v ∈ {v ∈ Set.range θ | v c ≠ 0}, ker (MvPolynomial.eval (v · / v c)) ≤ ker (u c)) :
    IsDenseFamily x := by
  -- Otherwise a basic open set of some `u c f` contains a point `y` and misses all the `x v`.
  -- Then `f` vanishes at the `θ v`, so `u c f = 0` and the basic open set is empty.
  show ∀ y : X, y ∈ closure (Set.range fun v : W ↦ x v (IsLocalRing.closedPoint ℂ))
  intro y
  by_contra hy
  obtain ⟨c, hc⟩ := TopologicalSpace.IsOpenCover.exists_mem (cover L) y
  -- the open complement of the closure of the points
  let V : X.Opens :=
    ⟨(closure (Set.range fun v : W ↦ x v (IsLocalRing.closedPoint ℂ)))ᶜ,
      isClosed_closure.isOpen_compl⟩
  obtain ⟨f, hf_sub, hf_y⟩ :
      ∃ f : MvPolynomial J ℂ, X.basicOpen (u c f) ≤ V ∧ y ∈ X.basicOpen (u c f) :=
    (hu c).surjective.exists.1 ((hu c).isAffineOpen.exists_basicOpen_le (V := V) ⟨y, hy⟩ hc)
  have hf_vanish (v : W) (hv : θ v c ≠ 0) : MvPolynomial.eval (θ v · / θ v c) f = 0 := by
    by_contra hf_v
    obtain ⟨h_lands_iff, h_ratio⟩ := hx v c
    have h_in : LandsIn (x v) (L.opens c) := h_lands_iff.2 hv.isUnit
    have h_value : ofSection (u c f) _ (x v) = MvPolynomial.eval (θ v · / θ v c) f := by
      simp [(hu c).ofSection_eq h_in, hx_over, h_ratio, hv, div_eq_mul_inv]
    have h_basic : LandsIn (x v) (X.basicOpen (u c f)) := by
      rw [landsIn_basicOpen h_in, h_value]
      exact Ne.isUnit hf_v
    exact hf_sub (landsIn_iff_mem.1 h_basic) (subset_closure ⟨v, rfl⟩)
  have hf_zero : u c f = 0 := h_ideal c (by simpa using hf_vanish)
  simp [hf_zero] at hf_y

/-- In the chart `c` of the base change of `z : A ⟶ S` along `b`, a map `φ` kills the ideal of the
chart exactly when the `φ (X j)` are the coordinates of a point of `A` in the chart `c` that lies
over the point of `S` given by `φ.comp C` and `b`. -/
lemma IsChartPresentation.ker_le_ker_iff {J B : Type} [CommRing B] {A S : Scheme}
    {N : LineBundle A J} {z : A ⟶ S} {R : CommRingCat} {b : Spec R ⟶ S} {c : J}
    {u : MvPolynomial J R →+* Γ(pullback z b, (N.pull (fst z b)).opens c)}
    (hu : IsChartPresentation (N.pull (fst z b)) (snd z b) c u) (φ : MvPolynomial J R →+* B) :
    ker u ≤ ker φ ↔ ∃ y : Spec (CommRingCat.of B) ⟶ A, LandsIn y (N.opens c) ∧
      y ≫ z = specMap (φ.comp C) ≫ b ∧
      ∀ j : J, N.transition c j (CommRingCat.of B) y = φ (X j) := by
  constructor
  · intro h_le
    -- `φ` factors as `ψ ∘ u`; the point is `Spec ψ` followed by the chart.
    obtain ⟨ψ, rfl⟩ : ∃ ψ : Γ(pullback z b, (N.pull (fst z b)).opens c) →+* B, ψ.comp u = φ :=
      ⟨u.liftOfSurjective hu.surjective ⟨φ, h_le⟩, u.liftOfSurjective_comp hu.surjective ⟨φ, h_le⟩⟩
    let y : Spec (CommRingCat.of B) ⟶ pullback z b := specMap ψ ≫ hu.isAffineOpen.fromSpec
    have h_in : LandsIn y ((N.pull (fst z b)).opens c) := landsIn_fromSpec _ _
    have h_eval : ψ.comp u = eval₂Hom (Spec.preimage (y ≫ snd z b)).hom
          ((N.pull (fst z b)).transition c · (CommRingCat.of B) y) :=
      ext fun f ↦ (ofSection_map_fromSpec _ (u f) _).symm.trans (hu.ofSection_eq h_in f)
    refine ⟨y ≫ fst z b, landsIn_preimage.1 h_in, ?_, ?_⟩
    · simp [h_eval, condition, specMap]
    · simp [h_eval]
  · rintro ⟨y, hy_in, hy_over, hy_coord⟩ f hf
    let y' : Spec (CommRingCat.of B) ⟶ pullback z b := lift y (specMap (φ.comp C)) hy_over
    have h_in : LandsIn y' ((N.pull (fst z b)).opens c) := by simpa [y', lift_fst]
    -- At the lift of `y`, the value of `u f` is `φ f`; it is zero as `u f = 0`.
    have h_value : ofSection (u f) (CommRingCat.of B) y' = φ f := by
      simpa [y', hy_coord, ← hom_eval₂, lift_snd, lift_fst] using hu.ofSection_eq h_in f
    simp [mem_ker, ← h_value, mem_ker.1 hf]

/-- Let `A` and `S` be reduced schemes with `z : A ⟶ S`, and let `u` present the chart `c` of the
pullback of the line bundle `N` to the base change of `A` to the local ring of `S` at `p`. Let the
complex points `x (a, v)` be dense in `A`, lie over the complex points `ξ a` of `S` (finitely many
`a`), and have homogeneous coordinates `θ a v` for `N`. Then a polynomial `f` over the local ring
lies in the kernel of `u` exactly when, for every `a` and every `ψ : stalk → ℂ` through which `ξ a`
factors, the image of `f` under `ψ` vanishes at every point `θ a v / (θ a v) c` with
`(θ a v) c ≠ 0`. -/
lemma IsChartPresentation.mem_ker_stalk_iff {J W ι : Type} [Finite ι] {A S : Scheme} [IsReduced A]
    [IsReduced S] {N : LineBundle A J} {z : A ⟶ S} {p : S} {c : J}
    {u : MvPolynomial J (S.presheaf.stalk p) →+*
      Γ(pullback z (S.fromSpecStalk p), (N.pull (fst z (S.fromSpecStalk p))).opens c)}
    (hu : IsChartPresentation (N.pull (fst z (S.fromSpecStalk p))) (snd z (S.fromSpecStalk p)) c u)
    {ξ : ι → (Spec (CommRingCat.of ℂ) ⟶ S)} {θ : ι → W → J → ℂ}
    {x : ι × W → (Spec (CommRingCat.of ℂ) ⟶ A)} (h_dense : IsDenseFamily x)
    (h_over : ∀ w : ι × W, x w ≫ z = ξ w.1)
    (h_coords : ∀ w : ι × W, N.IsHomogeneousCoords (x w) (θ w.1 w.2))
    (f : MvPolynomial J (S.presheaf.stalk p)) :
    f ∈ ker u ↔
      ∀ (a : ι) (ψ : S.presheaf.stalk p ⟶ CommRingCat.of ℂ),
        Spec.map ψ ≫ S.fromSpecStalk p = ξ a →
        MvPolynomial.map ψ.hom f ∈
          ⨅ v ∈ {v ∈ Set.range (θ a) | v c ≠ 0}, ker (MvPolynomial.eval (v · / v c)) := by
  have h_finite : (Set.range (x · ≫ z)).Finite :=
    (Set.finite_range ξ).subset (Set.range_subset_iff.2 fun w ↦ ⟨w.1, (h_over w).symm⟩)
  -- The lifts of the `x w` to the base change separate functions.
  have h_vanish : f ∈ ker u ↔ ∀ (w : ι × W) (ψ : S.presheaf.stalk p ⟶ CommRingCat.of ℂ)
      (hψ : Spec.map ψ ≫ S.fromSpecStalk p = x w ≫ z),
      LandsIn (lift (x w) (Spec.map ψ) hψ.symm) ((N.pull (fst z (S.fromSpecStalk p))).opens c) →
        ofSection (u f) (CommRingCat.of ℂ) (lift (x w) (Spec.map ψ) hψ.symm) = 0 := by
    constructor
    · intro hf w ψ hψ _
      simp [mem_ker.1 hf]
    · -- `u f` and `0` agree at the lifts, so they agree at the point `fromSpec` of the chart.
      intro h_pts
      have h_at_fromSpec :
          ofSection (u f) _ (Spec.map (𝟙 _) ≫ hu.isAffineOpen.fromSpec) = 0 :=
        (isSeparatingFamily_stalk h_dense h_finite p).pointFn_ext (g := 0) (isRegularOn_ofSection _)
          (by simp [IsRegularOn]) (fun ⟨w, ψ, hψ⟩ ↦ h_pts w ψ hψ) _ _ (landsIn_fromSpec _ _)
      rwa [ofSection_map_fromSpec] at h_at_fromSpec
  -- At a lift of `x w` in the chart, the value of `u f` is `eval (θ · / θ c)` of the image of `f`.
  have h_value (w : ι × W) (ψ : S.presheaf.stalk p ⟶ CommRingCat.of ℂ)
      (hψ : Spec.map ψ ≫ S.fromSpecStalk p = x w ≫ z)
      (h_in : LandsIn (lift (x w) (Spec.map ψ) hψ.symm)
        ((N.pull (fst z (S.fromSpecStalk p))).opens c)) (h_ne : θ w.1 w.2 c ≠ 0) :
      ofSection (u f) (CommRingCat.of ℂ) (lift (x w) (Spec.map ψ) hψ.symm) =
        MvPolynomial.eval (θ w.1 w.2 · / θ w.1 w.2 c) (MvPolynomial.map ψ.hom f) := by
    simp [hu.ofSection_eq h_in, h_coords .., h_ne, div_eq_mul_inv]
  -- The lift of `x w` lies in the chart `c` exactly when the coordinate `θ w.1 w.2 c` is nonzero.
  have h_in_iff (w : ι × W) (ψ : S.presheaf.stalk p ⟶ CommRingCat.of ℂ)
      (hψ : Spec.map ψ ≫ S.fromSpecStalk p = x w ≫ z) :
      LandsIn (lift (x w) (Spec.map ψ) hψ.symm) ((N.pull (fst z (S.fromSpecStalk p))).opens c) ↔
        θ w.1 w.2 c ≠ 0 := by
    simp [(h_coords w c).1]
  rw [h_vanish]
  simp only [Submodule.mem_iInf, Set.mem_ofPred_eq, and_imp, Set.forall_mem_range, mem_ker]
  constructor
  · intro h_pts a ψ hψ v hv
    have hψ' : Spec.map ψ ≫ S.fromSpecStalk p = x (a, v) ≫ z := hψ.trans (h_over (a, v)).symm
    have h_in := (h_in_iff (a, v) ψ hψ').mpr hv
    rw [← h_value (a, v) ψ hψ' h_in hv]
    exact h_pts (a, v) ψ hψ' h_in
  · intro h_pts w ψ hψ h_in
    have h_ne : θ w.1 w.2 c ≠ 0 := (h_in_iff w ψ hψ).mp h_in
    rw [h_value w ψ hψ h_in h_ne]
    exact h_pts w.1 ψ (hψ.trans (h_over w)) w.2 h_ne

/-- If the base change of `z` to the local ring at `p` is flat, then `z` is flat at every point
whose image generalises `p`. -/
lemma flat_stalkMap_of_flat_snd {A S : Scheme} {z : A ⟶ S} {p : S}
    (h_flat : Flat (snd z (S.fromSpecStalk p))) {a : A} (ha : z a ⤳ p) :
    (z.stalkMap a).hom.Flat := by
  let s : Spec (S.presheaf.stalk p) ⟶ S := S.fromSpecStalk p
  have h_flat_comp : Flat (fst z s ≫ z) := by
    rw [condition]
    infer_instance
  -- `a` comes from a point `y` of the base change, and `fst z s` is bijective on stalks.
  obtain ⟨y, rfl⟩ : a ∈ Set.range (fst z s) :=
    (Pullback.range_fst z s).ge (range_fromSpecStalk.ge ha)
  have h_bij : Function.Bijective ((fst z s).stalkMap y) :=
    ⟨stalkMap_injective_of_flat _ y, Hom.stalkMap_surjective _ y⟩
  have h_stalk : ((fst z s ≫ z).stalkMap y).hom.Flat := stalkMap _ y
  rw [Hom.stalkMap_comp] at h_stalk
  exact (comp_iff_of_bijective_left h_bij).1 h_stalk

/-- Complex points `ξ w` of `S` and nonzero vectors `θ w` give points of `ℙ^J × S`. Their reduced
closure `A` is projective over `S`, with dense points `x w` over `ξ w` with coordinates `θ w`. -/
lemma exists_reduced_projective_closure {J Ω : Type} [Finite J] {S : Scheme}
    (ξ : Ω → (Spec (CommRingCat.of ℂ) ⟶ S)) {θ : Ω → J → ℂ} (hθ : ∀ w : Ω, θ w ≠ 0) :
    ∃ (A : Scheme) (z : A ⟶ S) (N : LineBundle A J) (x : Ω → (Spec (CommRingCat.of ℂ) ⟶ A)),
      N.IsProjEmbedding z ∧
      IsSeparatingFamily x ∧
      (∀ w : Ω, x w ≫ z = ξ w) ∧
      ∀ w : Ω, N.IsHomogeneousCoords (x w) (θ w) := by
  -- Each `θ w` has a nonzero, hence unit, entry `θ w (c w)`.
  choose c hc using fun w : Ω ↦ Function.ne_iff.1 (hθ w)
  -- `p w` is a point of `ℙ^J × S` over `ξ w` with homogeneous coordinates `θ w` for `O(1)`.
  choose p hp_over hp_coords using fun w : Ω ↦
    ProjSpace.exists_isHomogeneousCoords (ξ w) (hc w).isUnit
  -- `A` is the reduced closure of the points `p w`, embedded by the pull-back of `O(1)`.
  obtain ⟨A, ε, x, h_closed, h_fac, h_sep⟩ := exists_reduced_closure p
  refine ⟨A, ε ≫ Limits.prod.snd, ((ProjSpace.hyperplaneBundle J).pull Limits.prod.fst).pull ε, x,
    isProjEmbedding_projSpace.comp ε, h_sep, ?_, ?_⟩
  · simpa [← h_fac] using hp_over
  · simpa [← h_fac, ← IsHomogeneousCoords.pull_iff] using hp_coords

/-- The main step towards `exists_isFlatClosure`. Let `S` be reduced, with finitely many dense
complex points `η (j a)`, and at every `η n` the ideals of the vectors `θ n v` are cut out by the
linear systems `P`, where `1 < r` and `i` is a degree bound for the ranks `σ`. Let `A` be reduced
over `S`, with dense complex points `x₀ (a, v)` over `η (j a)` with homogeneous coordinates
`θ (j a) v` for `N`, and let `u b c` present the chart `c` of the base change of `A` along each `b`.
At a field-valued point `t` of `S` where the ideals of `Z` are cut out by `P`: the base change of
`A` to the local ring of `S` at the image of `t` is flat, and in each chart `c` the ideal of the
fibre over `t` is the vanishing ideal of the `v ∈ Z` with `v c ≠ 0`, scaled to `v c = 1`. -/
lemma flat_snd_and_iInf_ker_eq_of_isCutOutAt {J W ι I κ : Type} {S : Scheme} {r i : ℕ}
    {σ : ℕ → ℕ} [Finite J] [Finite ι] [IsReduced S] {j : ι → κ}
    {η : κ → (Spec (CommRingCat.of ℂ) ⟶ S)} (hη_dense : IsDenseFamily fun a : ι ↦ η (j a))
    {P : I → LineBundle S J} (h_lin : ∀ a : I, (P a).IsLinearSystem) (hr : 1 < r)
    (h_deg : IsCutDegree J i r σ) {θ : κ → W → J → ℂ}
    (h_fib : ∀ n : κ, IsCutOutAt r i σ P (η n) (Set.range (θ n)))
    {A : Scheme} [IsReduced A] {z : A ⟶ S} {N : LineBundle A J}
    {x₀ : ι × W → (Spec (CommRingCat.of ℂ) ⟶ A)} (hx₀_dense : IsDenseFamily x₀)
    (h_over : ∀ w : ι × W, x₀ w ≫ z = η (j w.1))
    (h_coords : ∀ w : ι × W, N.IsHomogeneousCoords (x₀ w) (θ (j w.1) w.2))
    {u : ∀ {R : CommRingCat} (b : Spec R ⟶ S) (c : J),
      MvPolynomial J R →+* Γ(pullback z b, (N.pull (fst z b)).opens c)}
    (hu : ∀ {R : CommRingCat} (b : Spec R ⟶ S) (c : J),
      IsChartPresentation (N.pull (fst z b)) (snd z b) c (u b c))
    {k : Type} [Field k] {t : Spec (.of k) ⟶ S} {Z : Set (J → k)}
    (hZ : IsCutOutAt r i σ P t Z) :
    Flat (snd z (S.fromSpecStalk (t (IsLocalRing.closedPoint k)))) ∧
      ∀ c : J, ⨅ v ∈ {v ∈ Z | v c ≠ 0}, ker (eval (v · / v c)) = ker (u t c) := by
  -- In each chart, `eq_map_and_flat_of_isCutOut` over the local ring at `t` gives both claims.
  let p : S := t (IsLocalRing.closedPoint k)
  let s : Spec (S.presheaf.stalk p) ⟶ S := S.fromSpecStalk p
  have ht : Spec.map (stalkClosedPointTo t) ≫ s = t := Spec_stalkClosedPointTo_fromSpecStalk t
  choose l hl using fun a : I ↦ (P a).exists_landsIn s
  -- `ker (u s c)` is the intersection of the cut-out ideals at the `η (j a)` that factor through
  -- `s`, so it has a flat quotient and reduces at `t` to the ideal of `Z`.
  have h_map_eq_flat (c : J) : ⨅ v ∈ {v ∈ Z | v c ≠ 0}, ker (eval (v · / v c)) =
        (ker (u s c)).map (MvPolynomial.map (stalkClosedPointTo t).hom) ∧
      Module.Flat (S.presheaf.stalk p) (MvPolynomial J (S.presheaf.stalk p) ⧸ ker (u s c)) := by
    -- The other points are the complex points `ψ` of the local ring over some `η (j a)`; the ideal
    -- cut out there is that of the vectors `θ (j a) v`.
    let Pts : Type :=
      Σ' (a : ι) (ψ : S.presheaf.stalk p ⟶ CommRingCat.of ℂ), Spec.map ψ ≫ s = η (j a)
    let idealAt (n : Pts) : Ideal (MvPolynomial J ℂ) :=
      ⨅ v ∈ {v ∈ Set.range (θ (j n.fst)) | v c ≠ 0}, ker (eval (v · / v c))
    refine eq_map_and_flat_of_isCutOut (κ := Pts) (I := idealAt) (stalkClosedPointTo t).hom
      (ker (u s c)) (stalk_eq_zero_of_dense hη_dense) hr h_deg
        (isCutOut_of_isCutOutAt h_lin hl ht hZ c)
      (fun ⟨a, ψ, hψ⟩ ↦ isCutOut_of_isCutOutAt h_lin hl hψ (h_fib (j a)) c) fun f ↦ ?_
    rw [(hu s c).mem_ker_stalk_iff (ξ := fun a ↦ η (j a)) (θ := fun a ↦ θ (j a))
      hx₀_dense h_over h_coords f]
    exact ⟨fun h ⟨a, ψ, hψ⟩ ↦ h a ψ hψ, fun h a ψ hψ ↦ h ⟨a, ψ, hψ⟩⟩
  constructor
  · exact flat_of_isChartPresentation (hu s) fun c ↦ (h_map_eq_flat c).right
  · refine fun c ↦ (h_map_eq_flat c).left.trans (eq_of_forall_ge_iff fun 𝔞 ↦ ?_)
    -- The reduction of `ker (u s c)` is `ker (u t c)`: both lie in the same ideals `𝔞`.
    rw [← 𝔞.mk_ker, Ideal.map_le_iff_le_comap, comap_ker, (hu s c).ker_le_ker_iff,
      (hu t c).ker_le_ker_iff]
    simp [comp_assoc, ht, specMap]

/-- Let `N` embed `A` in projective space over `S` along `z`, let `ξ` be a complex point of `S`, and
let `u` present the chart `c` of the fibre of `A` over `ξ`. A vector `θ₀` with `θ₀ c ≠ 0` whose
evaluation (scaled to `θ₀ c = 1`) vanishes on the ideal of the chart is the vector of homogeneous
coordinates of a point of `A` over `ξ`. -/
lemma exists_isHomogeneousCoords_of_ker_le_ker {J : Type} {A S : Scheme} {z : A ⟶ S}
    {N : LineBundle A J} (h_emb : N.IsProjEmbedding z) {ξ : Spec (CommRingCat.of ℂ) ⟶ S} {c : J}
    {u : MvPolynomial J (CommRingCat.of ℂ) →+* Γ(pullback z ξ, (N.pull (fst z ξ)).opens c)}
    (hu : IsChartPresentation (N.pull (fst z ξ)) (snd z ξ) c u) {θ₀ : J → ℂ} (hc : θ₀ c ≠ 0)
    (h_le : ker u ≤ ker (eval (θ₀ · / θ₀ c))) :
    ∃ x : Over.mk ξ ⟶ Over.mk z, N.IsHomogeneousCoords x.left θ₀ := by
  obtain ⟨y, hy_in, hy_over, hy_coord⟩ : ∃ y : Spec (CommRingCat.of ℂ) ⟶ A, LandsIn y (N.opens c) ∧
      y ≫ z = specMap ((eval (θ₀ · / θ₀ c)).comp C) ≫ ξ ∧
      ∀ j : J, N.transition c j (CommRingCat.of ℂ) y = eval (θ₀ · / θ₀ c) (X j) :=
    (hu.ker_le_ker_iff _).mp h_le
  -- `θ₀` is `θ₀ c` times the affine coordinates of `y` in the chart `c`.
  have h_scale : θ₀ c • (N.transition c · (.of ℂ) y) = θ₀ :=
    funext fun k ↦ by simp [hy_coord, mul_div_cancel₀ _ hc]
  have hy : N.IsHomogeneousCoords y θ₀ := by
    rw [← h_scale]
    exact (h_emb.isLinearSystem.isHomogeneousCoords_transition hy_in).smul hc.isUnit
  have hy_w : y ≫ z = ξ := by simp [hy_over, MvPolynomial.eval, specMap]
  exact ⟨Over.homMk y hy_w, hy⟩

/-- Let `S` be reduced, with complex points `η n` of which finitely many, the `η (j a)`, are dense.
Let nonzero vectors `θ n v` be given whose ideals are cut out at `η n` by linear systems `P a`
(`IsCutOutAt`: ranks `σ m` in every degree `r ^ m`, vanishing in the degrees `r ^ m` with `m ≤ i`),
where `r > 1` and `i` is a degree bound for the ranks `σ`. Let every point of `S` specialise to a
geometric point where some set has its ideals cut out by `P`. Then the `θ n v` are the coordinates
of points spanning a flat projective family over `S`. -/
lemma exists_isFlatClosure {J W ι I κ : Type} {S : Scheme} {r i : ℕ} {σ : ℕ → ℕ} [Finite J]
    [Finite ι] [IsReduced S] (j : ι → κ) {η : κ → (Spec (CommRingCat.of ℂ) ⟶ S)}
    (hη_dense : IsDenseFamily fun a : ι ↦ η (j a)) {P : I → LineBundle S J}
    (h_lin : ∀ a : I, (P a).IsLinearSystem) (hr : 1 < r) (h_deg : IsCutDegree J i r σ)
    {θ : κ → W → J → ℂ} (hθ : ∀ (n : κ) (v : W), θ n v ≠ 0)
    (h_fib : ∀ n : κ, IsCutOutAt r i σ P (η n) (Set.range (θ n)))
    (h_specialize_cut : AllSpecializeTo S fun {k : Type} [Field k] (t : Spec (.of k) ⟶ S) ↦
      ∃ Z : Set (J → k), IsCutOutAt r i σ P t Z) :
    ∃ (A : Over S) (N : LineBundle A.left J) (e : ∀ n : κ, W → (Over.mk (η n) ⟶ A)),
      IsFlatClosure θ N e := by
  -- `A` is the reduced closure in `ℙ^J × S` of the points `θ (j a) v`. In each chart,
  -- `eq_map_and_flat_of_isCutOut` over the local ring at a point `t` with `IsCutOutAt` shows that
  -- `A` is flat there and that the fibre over `t` has the vanishing ideal of `Z`.
  obtain ⟨A, z, N, x₀, h_emb, ⟨hA_red, h_dense⟩, h_over, h_coords⟩ :
      ∃ (A : Scheme) (z : A ⟶ S) (N : LineBundle A J) (x₀ : ι × W → (Spec (.of ℂ) ⟶ A)),
        N.IsProjEmbedding z ∧ IsSeparatingFamily x₀ ∧ (∀ w : ι × W, x₀ w ≫ z = η (j w.1)) ∧
        ∀ w : ι × W, N.IsHomogeneousCoords (x₀ w) (θ (j w.1) w.2) :=
    exists_reduced_projective_closure (fun w : ι × W ↦ η (j w.1)) fun w ↦ hθ (j w.1) w.2
  -- After base change along `b`, the ring of the chart `c` is `MvPolynomial J R ⧸ ker (u b c)`.
  have h_chart {R : CommRingCat} (b : Spec R ⟶ S) (c : J) :
      ∃ u, IsChartPresentation (N.pull (fst z b)) (snd z b) c u := by
    obtain ⟨h_aff, u, h_surj, h_snd, h_ev⟩ :=
      (h_emb.of_isPullback (.of_hasPullback z b)).exists_affine_chart c
    exact ⟨u, h_aff, h_surj, h_snd, h_ev⟩
  -- (`@` keeps the ring `R` an implicit argument of `u`)
  choose u hu using @h_chart
  -- Main step, at a point `t` where the ideals of `Z` are cut out by `P`: flatness over the local
  -- ring at `t`, and the ideal of the fibre in each chart.
  have h_fibre {k : Type} [Field k] {t : Spec (.of k) ⟶ S} {Z : Set (J → k)}
      (hZ : IsCutOutAt r i σ P t Z) :
      Flat (snd z (S.fromSpecStalk (t (IsLocalRing.closedPoint k)))) ∧
      ∀ c : J, ⨅ v ∈ {v ∈ Z | v c ≠ 0}, ker (eval (v · / v c)) = ker (u t c) :=
    flat_snd_and_iInf_ker_eq_of_isCutOutAt hη_dense h_lin hr h_deg h_fib h_dense h_over h_coords hu
      hZ
  -- In each chart the ideal is an intersection of kernels of maps to a field, hence radical.
  have h_reduced {k : Type} [Field k] {t : Spec (.of k) ⟶ S} {Z : Set (J → k)}
      (hZ : IsCutOutAt r i σ P t Z) : IsReduced (pullback z t) := by
    obtain ⟨-, h_ker⟩ := h_fibre hZ
    refine isReduced_of_isChartPresentation (hu t) fun c ↦ ?_
    rw [← h_ker c]
    exact Ideal.isRadical_iInf _ fun v ↦ Ideal.isRadical_iInf _ fun _ ↦
      (ker_isPrime _).isRadical
  -- Every `θ n v` is a point of `A` over `η n`, as evaluation at it kills the ideal of the fibre.
  have h_point (n : κ) (v : W) : ∃ x : mk (η n) ⟶ mk z, N.IsHomogeneousCoords x.left (θ n v) := by
    obtain ⟨c, hc⟩ : ∃ c : J, θ n v c ≠ 0 := Function.ne_iff.1 (hθ n v)
    obtain ⟨-, h_ker⟩ := h_fibre (h_fib n)
    have h_le : ker (u (η n) c) ≤ RingHom.ker (eval (θ n v · / θ n v c)) :=
      (h_ker c).ge.trans (iInf₂_le _ ⟨⟨v, rfl⟩, hc⟩)
    exact exists_isHomogeneousCoords_of_ker_le_ker h_emb (hu (η n) c) hc h_le
  choose x hx using h_point
  -- Flatness at `a`: `z a` specialises to a point where ideals are cut out.
  have h_flat : Flat z := by
    refine .of_stalkMap _ fun a ↦ ?_
    obtain ⟨k, _, _, t, h_spec, Z, hZ⟩ := h_specialize_cut (z a)
    exact flat_stalkMap_of_flat_snd (h_fibre hZ).left h_spec
  -- Density in the fibre over `η n`, whose chart ideals are the vanishing ideals of the `θ n v`.
  have h_fibre_dense (n : κ) : IsDenseFamily fun v : W ↦
      pullback.lift (x n v).left (𝟙 (Spec (CommRingCat.of ℂ))) (x n v).w := by
    refine isDenseFamily_of_isChartPresentation (hu (η n))
      (fun v ↦ lift_snd (x n v).left (𝟙 (Spec (CommRingCat.of ℂ))) (x n v).w) (fun v ↦ ?_)
      fun c ↦ ((h_fibre (h_fib n)).right c).le
    have h_lift : pullback.lift (x n v).left (𝟙 (Spec (CommRingCat.of ℂ))) (x n v).w ≫ fst z (η n) =
        (x n v).left := lift_fst _ _ _
    rw [IsHomogeneousCoords.pull_iff, h_lift]
    exact hx n v
  -- Every `s` specialises to a point where ideals are cut out, and there the fibre is reduced.
  have h_specialize : AllSpecializeTo S fun t ↦ IsReduced (pullback z t) := fun s ↦
    let ⟨k, hk, hk', t, h_spec, _, hZ⟩ := h_specialize_cut s
    ⟨k, hk, hk', t, h_spec, h_reduced hZ⟩
  -- Finally, density in `A`: the points `x₀ w` are among the `x n v`, having the same coordinates.
  refine ⟨mk z, N, x,
    { isProjEmbedding := h_emb
      flat := h_flat
      isHomogeneousCoords := hx
      isSeparatingFamily_fibre := fun n ↦ ⟨h_reduced (h_fib n), h_fibre_dense n⟩
      allSpecializeTo_isReduced := h_specialize
      isSeparatingFamily := ⟨hA_red, h_dense.mono ?_⟩ }⟩
  have h_eq (a : ι) (v : W) : x₀ (a, v) = (x (j a) v).left :=
    h_emb.eq_of_isHomogeneousCoords ((h_over (a, v)).trans (x (j a) v).w.symm) (h_coords (a, v))
      (hx (j a) v) (LineBundle.exists_landsIn _ _)
  simp [Set.range_subset_iff, h_eq]

end FlatClosure

end New.Variety.ThetaNull

end
