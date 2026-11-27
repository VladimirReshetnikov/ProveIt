import New.Reduction.Lattices.Colength
import New.UpperBound.ElementaryDivisors.AveragingMap
import New.UpperBound.ElementaryDivisors.DefectCount
import New.UpperBound.ElementaryDivisors.Depth

/-!
# Elementary divisors of the edge Hecke operator

The main result `New.FrobeniusCycle.elementary_divisors` bounds the mean exponent of the elementary
divisors of an edge Hecke operator `A`, outside a small proportion of them, under the size
conditions `New.FrobeniusCycle.IsLargeDegree`. Colengths in the sense of `New.ColengthDvd` take
the place of lengths, because the ring of coefficients need not be discrete;
`New.FrobeniusCycle.elementary_divisors_length` is the statement in lengths.

Let `w ^ 2 = p`, let `N` be the number of letters of the Frobenius cycle `T` and
`c₀ = T.multinomialExponent k`. Write `M` for the integral functions on lattices, `M_all` for the
functions on edges that depend only on the origin (`New.FrobeniusCycle.originFunctions`) and
`M_edge` for all functions on edges. The operator `A` acts on `M°`, the functions whose value at `L`
is dual to the integral forms on the dual lattice `L*`. Let `𝒩 ⊆ M°` consist of the functions whose
value at `L` is dual to the forms in the halfway lattices of all edges from `L*`. The map
`Add : M_edge → 𝒩` (`New.pairingMap`) adds the values at the edges into `L`. It is written in
coordinates dual to these forms, with one basis for all lattices `L` at once. Then, on vectors
multiplied by the pairing `b`, `A` is the composite `M ⊆ M_all ⊆ M_edge → 𝒩 ⊆ M°`
(`New.FrobeniusCycle.IsEdgePairing.edgeHeckeOperator_regroup`), and the image of `Add` contains
`p ^ (N c₀) 𝒩` (`New.FrobeniusCycle.IsEdgePairing.pairingMap_mul_nearInverse_one`). At each edge
there are conditions modulo `w ^ c`, with the precision `c = T.congruencePrecision k`
(`New.FrobeniusCycle.exists_isEdgeCondition`).

1. The functions that satisfy the conditions have nearly the full image: `Add` has a near inverse
   `Inv` (`New.nearInverse`, `New.FrobeniusCycle.IsEdgeCondition.pow_dvd_mul_sub_smul_one`) whose
   values satisfy them.
2. The conditions hold on `M_all` and leave room for few further generators. By Nakayama's lemma the
   span of `Add M_all` and these generators contains `p ^ (2 N c₀) 𝒩`
   (`New.exists_finset_card_le_smul_top_le_sup_span`).
3. Both ends have small colength (`New.FrobeniusCycle.IsLargeDegree.exists_basis_det_dvd`, used
   twice), and the colengths add along the chain (`New.colengthDvd_mul_mul_of_smul_top_le`).

The three steps are put together in
`New.FrobeniusCycle.exists_colengthDvd_range_pairingMap_mul_edgeRestriction`.

Notions from other files:
* `New.FrobeniusCycle N W O`: a prime `p` with a square root `w` in `O`, a power `P` of `p` such
  that the residue field of `W` has `q = P ^ N` elements, and `N` maps `W → O` (the letters), each
  the `P`-th power of the one before modulo `p`.
* `New.FrobeniusCycle.allEdgesForms`: the forms that lie in the halfway lattices of all edges from a
  lattice; `New.FrobeniusCycle.IsEdgePairing`: the pairing of an edge with its dual.
* `New.FrobeniusCycle.divisorConstant`: the bound `c_div` for the mean depth of the forms that are
  deep for all edges.
-/

noncomputable section

namespace New

open Matrix IsLocalRing Function Module Finset Kronecker Pointwise Submodule

/-! ### Linear algebra of a near inverse -/

/-- Let `O` be a valuation domain, let the matrix `Q` have the left inverse `R`, so that its image
is a direct summand of `O ^ K`, and let `A` be a matrix of the same shape as `Q`. There are an
invertible matrix `U` and scalars `t j` such that the images of `Q` and `A` span the same module as
the image of `Q` and the vectors `t j • U.col j`, and `R` kills the columns of `U` with
`t j ≠ 0`. -/
lemma exists_elementary_divisors_mod_summand {O E : Type*} [CommRing O] [IsDomain O]
    [ValuationRing O] [Fintype E] [DecidableEq E] {K : Type*} [Fintype K] [DecidableEq K]
    {Q : Matrix K E O} {R : Matrix E K O} (hR : R * Q = 1) (A : Matrix K E O) :
    ∃ (U : GL K O) (t : K → O),
      (∀ j : K, t j ≠ 0 → R *ᵥ U.val.col j = 0) ∧
      Q.mulVecLin.range ⊔ A.mulVecLin.range =
        Q.mulVecLin.range ⊔ span O (Set.range fun j : K ↦ t j • U.val.col j) := by
  -- `A - Q * R * A` is the part of `A` in the complement `ker R`. It has the same image as the
  -- square matrix `(A - Q * R * A) * R`, of which we take a Smith form.
  obtain ⟨U, -, P, -, t, h_smith : (A - Q * R * A) * R = U.val * diagonal t * P.val⟩ :=
    isValuationPair_top.smith_normal_form ((A - Q * R * A) * R)
  have h_left : U.val * diagonal t = (A - Q * R * A) * R * P⁻¹.val :=
    (P.mul_inv_eq_iff_eq_mul.2 h_smith).symm
  have h_right : A = Q * (R * A) + U.val * diagonal t * (P.val * Q) := by
    rw [← Matrix.mul_assoc _ P.val, ← h_smith, Matrix.mul_assoc _ R Q, hR, Matrix.mul_one,
      ← Matrix.mul_assoc, add_sub_cancel]
  have h_col (j : K) : t j • U.val.col j = (U.val * diagonal t) *ᵥ Pi.single j 1 := by
    simp [funext_iff, mul_comm]
  refine ⟨U, t, fun j hj ↦ ?_, le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)⟩
  · have h_zero : R * (U.val * diagonal t) = 0 := by
      simp [h_left, ← Matrix.mul_assoc, Matrix.mul_sub, hR]
    rw [← smul_eq_zero_iff_right hj, ← mulVec_smul, h_col, mulVec_mulVec, h_zero, zero_mulVec]
  · rintro _ ⟨η, rfl⟩
    have h_sum : (U.val * diagonal t * (P.val * Q)) *ᵥ η =
        ∑ j : K, ((P.val * Q) *ᵥ η) j • t j • U.val.col j := by
      rw [← mulVec_mulVec, mulVec_eq_sum]
      simp [funext_iff, mul_left_comm]
    rw [mulVecLin_apply, h_right, add_mulVec, h_sum, ← mulVec_mulVec]
    exact add_mem_sup ⟨_, rfl⟩ (Submodule.sum_mem _ fun j _ ↦ smul_mem _ _ (subset_span ⟨j, rfl⟩))
  · rw [span_le]
    rintro _ ⟨j, rfl⟩
    let η : E → O := (R * P⁻¹.val) *ᵥ Pi.single j 1
    have h_diff : t j • U.val.col j = A *ᵥ η - Q *ᵥ (R * A) *ᵥ η := by
      simp only [h_col, h_left, η, mulVec_mulVec, Matrix.sub_mul, sub_mulVec, Matrix.mul_assoc]
    exact Set.mem_of_eq_of_mem h_diff (sub_mem (mem_sup_right ⟨η, rfl⟩) (mem_sup_left ⟨_, rfl⟩))

section LinearAlgebra

variable {O X I E : Type*} [CommRing O]

variable (X) in
/-- The functions on `X × I` whose values `i ↦ φ (x, i)` lie in `C` for every `x`. -/
def valuedIn (C : Submodule O (I → O)) : Submodule O (X × I → O) :=
  ⨅ x : X, C.comap (LinearMap.funLeft O O (Prod.mk x))

lemma mem_valuedIn {C : Submodule O (I → O)} {φ : X × I → O} :
    φ ∈ valuedIn X C ↔ ∀ x : X, (fun i : I ↦ φ (x, i)) ∈ C := mem_iInf _

variable [IsDomain O] [ValuationRing O] [Fintype E] [DecidableEq E]

/-- Let `Q` have the left inverse `R`, and let `R` kill the columns `j ∈ J` of an invertible matrix
`U`. If the columns of `Q` and these columns of `U` have all their values in `S` modulo the maximal
ideal, then `#E + #J ≤ #X * dim S`, because they are independent modulo the maximal ideal. -/
lemma card_add_card_le_mul_finrank [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]
    {Q : Matrix (X × I) E O} {R : Matrix E (X × I) O} {U : GL (X × I) O} {J : Finset (X × I)}
    {S : Submodule (ResidueField O) (I → ResidueField O)} (hR : R * Q = 1)
    (h_ker : ∀ j ∈ J, R *ᵥ U.val.col j = 0)
    (hQ : ∀ (j : E) (x : X), (fun i : I ↦ residue O (Q (x, i) j)) ∈ S)
    (hU : ∀ j ∈ J, ∀ x : X, (fun i : I ↦ residue O (U.val (x, i) j)) ∈ S) :
    Fintype.card E + #J ≤ Fintype.card X * finrank (ResidueField O) S := by
  -- The rows of `R` and of `U⁻¹ - U⁻¹ * Q * R` are dual to these columns.
  have h_blocks : R.fromRows (U⁻¹.val - U⁻¹.val * Q * R) * Q.fromCols U.val =
      fromBlocks 1 (R * U.val) 0 (1 - U⁻¹.val * Q * (R * U.val)) := by
    simp [Matrix.sub_mul, Matrix.mul_assoc, hR]
  have hRU (i : E) {j : X × I} (hj : j ∈ J) : (R * U.val) i j = 0 := congrFun (h_ker j hj) i
  rw [← card_univ, ← card_disjSum]
  refine card_le_mul_finrank_of_dual_rows (Q.fromCols U.val)
    (R.fromRows (U⁻¹.val - U⁻¹.val * Q * R)) ?_ ?_
  · rw [h_blocks]
    rintro (j | j) hj (i | i)
    · simp [one_apply]
    · simp
    · simp [hRU i (inr_mem_disjSum.1 hj)]
    · simp [one_apply, mul_apply (N := R * U.val), hRU _ (inr_mem_disjSum.1 hj)]
  · rintro (j | j) hj
    exacts [hQ j, hU j (inr_mem_disjSum.1 hj)]

omit [DecidableEq E] in
/-- If `u` is a multiple of `a * w` with `w` in the maximal ideal and `a • O ^ E` lies in
`G + u • O ^ E`, then `a • O ^ E` lies in `G`, by Nakayama's lemma. -/
lemma smul_top_le_of_le_sup_smul_top {a u w : O} {G : Submodule O (E → O)}
    (hw : w ∈ maximalIdeal O) (hu : a * w ∣ u)
    (h_le : a • (⊤ : Submodule O (E → O)) ≤ G ⊔ u • ⊤) :
    a • (⊤ : Submodule O (E → O)) ≤ G := by
  have h_small : u • ⊤ ≤ maximalIdeal O • a • (⊤ : Submodule O (E → O)) := by
    obtain ⟨v, rfl : u = a * w * v⟩ := hu
    rintro _ ⟨η, -, rfl⟩
    have h_assoc : (a * w * v) • η = w • a • v • η := by rw [mul_comm a w, mul_smul, mul_smul]
    exact Set.mem_of_eq_of_mem h_assoc (smul_mem_smul hw (smul_mem_pointwise_smul _ a ⊤ mem_top))
  exact le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top.map _)
    (maximalIdeal_le_jacobson ⊥) (h_le.trans (sup_le_sup_left h_small G))

/-- Let `O` be a valuation domain. Let the matrix `Q` have the left inverse `R`, so that its columns
are a basis of a direct summand of `O ^ (X × I)`, and let `B` be a near inverse of `A`: `A * B ≡ a`
modulo `u`, where `u` is a multiple of `a` times a non-unit `w`. Let every vector `φ` in the images
of `Q` and `B` have all its values `φ (x, ·)` in `C`, and let `h` reduce into `S` modulo the maximal
ideal whenever `u • h ∈ C`. Then `a • O ^ E` lies in the span of the image of `A * Q` and of at most
`#X * dim S - #E` further vectors. -/
lemma exists_finset_card_le_smul_top_le_sup_span [Fintype X] [Fintype I] [DecidableEq X]
    [DecidableEq I] {Q B : Matrix (X × I) E O} {R A : Matrix E (X × I) O}
    {a u w : O} {C : Submodule O (I → O)} {S : Submodule (ResidueField O) (I → ResidueField O)}
    (hR : R * Q = 1) (hw : w ∈ maximalIdeal O) (hu : a * w ∣ u)
    (h_near : ∀ i j : E, u ∣ (A * B - a • (1 : Matrix E E O)) i j)
    (hQ : Q.mulVecLin.range ≤ valuedIn X C) (hB : B.mulVecLin.range ≤ valuedIn X C)
    (hS : ∀ h : I → O, u • h ∈ C → (fun i : I ↦ residue O (h i)) ∈ S) :
    ∃ s : Finset (E → O),
      Fintype.card E + #s ≤ Fintype.card X * finrank (ResidueField O) S ∧
      a • (⊤ : Submodule O (E → O)) ≤ (A * Q).mulVecLin.range ⊔ span O (s : Set (E → O)) := by
  classical
  obtain ⟨U, t, h_ker : ∀ j : X × I, t j ≠ 0 → R *ᵥ U.val.col j = 0,
      h_span : Q.mulVecLin.range ⊔ B.mulVecLin.range =
        Q.mulVecLin.range ⊔ span O (Set.range fun j : X × I ↦ t j • U.val.col j)⟩ :=
    exists_elementary_divisors_mod_summand hR B
  -- The exceptional indices are those with `0 ≠ t j ∣ u`; at the others `u ∣ t j`.
  let J : Finset (X × I) := {j | t j ∣ u ∧ t j ≠ 0}
  have hJ {j : X × I} : j ∈ J ↔ t j ∣ u ∧ t j ≠ 0 := mem_filter_univ _
  have h_dvd (j : X × I) (hj : j ∉ J) : u ∣ t j := by
    grind [ValuationRing.dvd_total u (t j), dvd_zero]
  refine ⟨J.image fun j ↦ A *ᵥ U.val.col j, ?_, ?_⟩
  · -- The columns of `Q` and the exceptional columns of `U` reduce into `S`.
    have h_reduce {φ : X × I → O} (hφ : u • φ ∈ valuedIn X C) (x : X) :
        (fun i : I ↦ residue O (φ (x, i))) ∈ S :=
      hS _ (mem_valuedIn.1 hφ x)
    have hQ_col (j : E) : u • Q.col j ∈ valuedIn X C :=
      smul_mem _ u (hQ ⟨Pi.single j 1, by simp⟩)
    have hU_col (j : X × I) (hj : j ∈ J) : u • U.val.col j ∈ valuedIn X C := by
      obtain ⟨⟨v, hv : u = t j * v⟩, -⟩ := hJ.1 hj
      have h_mem : t j • U.val.col j ∈ valuedIn X C :=
        (h_span.ge.trans (sup_le hQ hB)) (mem_sup_right (subset_span ⟨j, rfl⟩))
      rw [hv, mul_comm, mul_smul]
      exact smul_mem _ v h_mem
    have h_count : Fintype.card E + #J ≤ Fintype.card X * finrank (ResidueField O) S :=
      card_add_card_le_mul_finrank hR (fun j hj ↦ h_ker j (hJ.1 hj).right)
        (fun j ↦ h_reduce (hQ_col j)) fun j hj ↦ h_reduce (hU_col j hj)
    exact (Nat.add_le_add_left card_image_le _).trans h_count
  · set G : Submodule O (E → O) :=
      (A * Q).mulVecLin.range ⊔ span O (J.image fun j ↦ A *ᵥ U.val.col j : Finset (E → O))
    -- Apply `A` to the module spanned by the images of `Q` and `B`.
    have h_map : Submodule.map A.mulVecLin (Q.mulVecLin.range ⊔ B.mulVecLin.range) ≤
        G ⊔ u • ⊤ := by
      rw [h_span, Submodule.map_sup, ← LinearMap.range_comp, ← mulVecLin_mul, map_span, sup_le_iff,
        span_le]
      refine ⟨le_sup_of_le_left le_sup_left, ?_⟩
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, map_smul, mulVecLin_apply]
      by_cases hj : j ∈ J
      · exact mem_sup_left (smul_mem _ _ (mem_sup_right (subset_span (mem_image_of_mem _ hj))))
      · obtain ⟨v, hv : t j = u * v⟩ := h_dvd j hj
        rw [hv, mul_smul]
        exact mem_sup_right (smul_mem_pointwise_smul _ u ⊤ mem_top)
    have h_mod : a • (⊤ : Submodule O (E → O)) ≤ G ⊔ u • ⊤ := by
      rintro _ ⟨η, -, rfl⟩
      choose Y hY using h_near
      have h_matrix : u • of Y = A * B - a • (1 : Matrix E E O) :=
        Matrix.ext fun i j ↦ (hY i j).symm
      have h_eq : a • η = A *ᵥ B *ᵥ η - u • of Y *ᵥ η := by
        rw [mulVec_mulVec, ← smul_mulVec, ← sub_mulVec, h_matrix, sub_sub_cancel, smul_mulVec,
          one_mulVec]
      change a • η ∈ G ⊔ u • ⊤
      rw [h_eq]
      have h_image : A *ᵥ B *ᵥ η ∈ G ⊔ u • ⊤ :=
        h_map (mem_map_of_mem (mem_sup_right (LinearMap.mem_range_self _ η)))
      exact sub_mem h_image (mem_sup_right (smul_mem_pointwise_smul _ u ⊤ mem_top))
    exact smul_top_le_of_le_sup_smul_top hw hu h_mod

/-- The colengths add along a product. If `a • O ^ E` lies in the span of the image of `A` and of a
finite set `s`, then the colength of the image of `d' * A * d` plus `z • O ^ E` in `O ^ E` divides
`det d' * a ^ #E * det d * z ^ #s`. -/
lemma colengthDvd_mul_mul_of_smul_top_le (d' A d : Matrix E E O) {a : O} {s : Finset (E → O)}
    (h_le : a • (⊤ : Submodule O (E → O)) ≤ A.mulVecLin.range ⊔ span O (s : Set (E → O))) (z : O) :
    ColengthDvd ⊤ ((d' * A * d).mulVecLin.range ⊔ z • ⊤)
      (d'.det * (a ^ Fintype.card E * (d.det * z ^ #s))) := by
  set G : Submodule O (E → O) := span O (s : Set (E → O))
  have h_det (B : Matrix E E O) : ColengthDvd ⊤ B.mulVecLin.range B.det :=
    .of_det_dvd dvd_rfl le_rfl
  have h_middle : ColengthDvd ⊤ (A.mulVecLin.range ⊔ G) (a ^ Fintype.card E) := by
    simpa only [mul_one] using (colengthDvd_top_smul_top a).trans (ColengthDvd.of_le (z := 1) h_le)
  have h_origin : ColengthDvd (A.mulVecLin.range ⊔ G) ((A * d).mulVecLin.range ⊔ G) d.det :=
    (h_det d).map A.mulVecLin (by simp [le_sup_of_le_right]) (by simp [LinearMap.range_comp])
  have h_chain : ColengthDvd ⊤ ((A * d).mulVecLin.range ⊔ z • ⊤)
      (a ^ Fintype.card E * (d.det * z ^ #s)) :=
    h_middle.trans (h_origin.trans (colengthDvd_sup_span _ s z))
  refine (h_det d').trans (h_chain.map d'.mulVecLin (by simp) ?_)
  rw [Submodule.map_sup, ← LinearMap.range_comp, ← mulVecLin_mul, map_pointwise_smul,
    Matrix.mul_assoc]
  exact sup_le_sup_left (smul_mono_right z le_top) _

end LinearAlgebra

/-! ### Coordinates for edges -/

section Edgewise

variable {O X H Ed I L : Type*} [CommRing O] [DecidableEq Ed]

/-- A vector indexed by `(H × X) × L`, read as a function `X → I → O` through `I ≃ L × H`. -/
def regroup (J : I ≃ L × H) : ((H × X) × L → O) →ₗ[O] X → I → O :=
  LinearMap.pi fun x : X ↦ LinearMap.funLeft O O fun i : I ↦ (((J i).2, x), (J i).1)

lemma regroup_apply (J : I ≃ L × H) (F : (H × X) × L → O) (x : X) (i : I) :
    regroup J F x i = F (((J i).2, x), (J i).1) := rfl

lemma regroup_surjective (J : I ≃ L × H) :
    Surjective (regroup J : ((H × X) × L → O) → X → I → O) :=
  fun G ↦ ⟨fun ((h, x), l) ↦ G x (J.symm (l, h)), by simp [funext_iff, regroup_apply]⟩

/-- The map on functions of edges with values in `O ^ H ⊗ O ^ L` that acts on the value at the edge
`e` by `u e ⊗ A`. -/
def edgewise (u : Ed → Matrix H H O) (A : Matrix L L O) :
    Matrix ((H × Ed) × L) ((H × Ed) × L) O := blockDiagonal u ⊗ₖ A

variable [Fintype H] [Fintype Ed] [Fintype L]

lemma edgewise_mul (u u' : Ed → Matrix H H O) (A A' : Matrix L L O) :
    edgewise u A * edgewise u' A' = edgewise (fun e : Ed ↦ u e * u' e) (A * A') := by
  simp only [edgewise, ← mul_kronecker_mul, ← blockDiagonal_mul]

/-- The value of `edgewise u A *ᵥ ψ` at `x = (h', e)` is `A` applied to the combination of the
values `ψ ((h, e), ·)` with the coefficients `u e h' h`. -/
lemma edgewise_mulVec (u : Ed → Matrix H H O) (A : Matrix L L O) (ψ : (H × Ed) × L → O)
    (x : H × Ed) :
    (fun l : L ↦ (edgewise u A *ᵥ ψ) (x, l)) =
      A *ᵥ ∑ h : H, u x.2 x.1 h • fun l : L ↦ ψ ((h, x.2), l) := by
  ext l
  simp [edgewise, mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply, mul_sum,
    sum_comm (γ := L), mul_left_comm, mul_assoc]

variable {E : Type*} [DecidableEq H] [DecidableEq L]

/-- The map `Add` that sends a function on edges to its pairings with the columns of `Q'`, which
are functions on the dual edges. At the edge `e` the pairing is by `u e` on the factor `O ^ H` and
by `(h, h') ↦ h' ⬝ᵥ (b * h)` on the factor `O ^ L`. -/
def pairingMap (u : Ed → GL H O) (b : L → O) (Q' : Matrix ((H × Ed) × L) E O) :
    Matrix E ((H × Ed) × L) O :=
  Q'ᵀ * edgewise (fun e : Ed ↦ (u e).val) (diagonal b)

/-- The map `Inv` in the direction opposite to `New.pairingMap`. It applies `R'ᵀ`, and then at the
edge `e` it applies `(u e)⁻¹` on the factor `O ^ H` and multiplication by `b'` followed by `Av` on
the factor `O ^ L`. -/
def nearInverse (u : Ed → GL H O) (Av : Matrix L L O) (b' : L → O)
    (R' : Matrix E ((H × Ed) × L) O) : Matrix ((H × Ed) × L) E O :=
  edgewise (fun e : Ed ↦ (u e)⁻¹.val) (Av * diagonal b') * R'ᵀ

/-- Let `Ed` be the set of edges, so that a vector indexed by `(H × Ed) × L` is a function on edges
with values in `O ^ H ⊗ O ^ L`, and let `E` index the columns of `Q'` and the rows of `R'`. The
entry `(i, j)` of `Add * Inv`, for `Add = pairingMap u b Q'` and `Inv = nearInverse u Av b' R'`, is
a sum over `x ∈ H × Ed`: the vector `Av` of `b'` times the part at `x` of row `j` of `R'` is paired,
with the weights `b`, with the part at `x` of column `i` of `Q'`. -/
lemma pairingMap_mul_nearInverse_apply (u : Ed → GL H O) (Av : Matrix L L O) (b b' : L → O)
    (Q' : Matrix ((H × Ed) × L) E O) (R' : Matrix E ((H × Ed) × L) O) (i j : E) :
    (pairingMap u b Q' * nearInverse u Av b' R') i j =
      ∑ x : H × Ed, (fun l : L ↦ Q' (x, l) i) ⬝ᵥ (b * Av *ᵥ (b' * fun l : L ↦ R' j (x, l))) := by
  let B : Matrix L L O := diagonal b * (Av * diagonal b')
  have h_cancel : edgewise (fun e : Ed ↦ (u e).val) (diagonal b) *
      edgewise (fun e : Ed ↦ (u e)⁻¹.val) (Av * diagonal b') =
        (1 : Matrix (H × Ed) (H × Ed) O) ⊗ₖ B := by
    have h_units : (fun e : Ed ↦ (u e).val * (u e)⁻¹.val) = 1 := funext fun e ↦ (u e).mul_inv
    rw [edgewise_mul, h_units, edgewise, blockDiagonal_one]
  have h_product : pairingMap u b Q' * nearInverse u Av b' R' =
      Q'ᵀ * ((1 : Matrix (H × Ed) (H × Ed) O) ⊗ₖ B * R'ᵀ) := by
    simp only [pairingMap, nearInverse, ← h_cancel, Matrix.mul_assoc]
  have hB (v : L → O) : B *ᵥ v = b * Av *ᵥ (b' * v) := by
    have h_diagonal (d w : L → O) : diagonal d *ᵥ w = d * w := funext (mulVec_diagonal d w)
    simp only [B, ← mulVec_mulVec, h_diagonal]
  calc (pairingMap u b Q' * nearInverse u Av b' R') i j
      = ∑ x : H × Ed, (fun l : L ↦ Q' (x, l) i) ⬝ᵥ (B *ᵥ fun l : L ↦ R' j (x, l)) := by
        -- The matrix `1 ⊗ₖ B` is block diagonal over `H × Ed`.
        rw [h_product]
        simp [mul_apply, Fintype.sum_prod_type (α₁ := H × Ed), one_apply, dotProduct, mulVec]
    _ = _ := by simp only [hB]

end Edgewise

/-- The edges of a Hecke operator in coordinates. The situation in mind is this: `p` is a
uniformizer of `W`, and a group `Γ` acts freely, with finitely many orbits, on pairs of a
`W`-lattice of rank `k` and a free `O`-module with a basis indexed by `H`. The points of `X` are
representatives of the orbits, each with a basis of its lattice and of its module, and
`e = (x, b)` is the edge `b` into `x`. The origin of `e` is `δ` times the representative
`origin e` for one `δ ∈ Γ`. In the chosen bases
`δ⁻¹ = originBasisChange e * diag(p⁻¹, …, p⁻¹, 1, …, 1) * terminusBasisChange b`, with `r` entries
`p⁻¹`. Only coordinates are recorded: `p`, `Γ` and `δ` are no part of the structure. -/
structure EdgeCoordinates (W O : Type) [CommRing W] [IsLocalRing W] [CommRing O] (k r : ℕ)
    (X H : Type*) [Fintype H] [DecidableEq H] where
  /-- The representative of the origin of an edge. -/
  origin : X × ParahoricCosets W k r → X
  /-- The matrix whose columns are a basis of the lattice of `origin e` adapted to `δ⁻¹ e`. -/
  originBasisChange : X × ParahoricCosets W k r → GL (Fin k) W
  /-- The change of basis at the terminus of an edge. -/
  terminusBasisChange : ParahoricCosets W k r → GL (Fin k) W
  /-- The matrix of `δ` from the module at `origin e` to the module at `x`. -/
  transition : X × ParahoricCosets W k r → GL H O
  /-- The inverse of `terminusBasisChange b` represents the coset `b`. -/
  mk_terminusBasisChange_inv : ∀ b : ParahoricCosets W k r,
    QuotientGroup.mk (terminusBasisChange b)⁻¹ = b
  /-- An edge is determined by its origin and the coset of its transposed change of basis there;
  this is where the action of `Γ` has to be free. -/
  eq_of_origin_eq : ∀ e e' : X × ParahoricCosets W k r, origin e = origin e' →
    transposeGL (originBasisChange e) * (transposeGL (originBasisChange e'))⁻¹ ∈ parahoric W
      (twoBlock k r) →
      e = e'

namespace FrobeniusCycle

open MvPolynomial Ideal

section ValuationRing

variable {N k n : ℕ} {W O : Type} [NeZero N] [CommRing W] [IsLocalRing W] [CommRing O]
  [IsDomain O] [ValuationRing O] [CharZero O] (T : FrobeniusCycle N W O)

/-! ### The standing assumptions and the sizes that follow -/

section Sizes

omit [IsDomain O] [ValuationRing O] [CharZero O]

/-- The size conditions in the theorem on elementary divisors, for the rank `k`, the degree `n`,
the size `r` of the first block and the proportion `θ` of exceptional elementary divisors. -/
structure IsLargeDegree (k n r : ℕ) (θ : ℝ) : Prop where
  /-- The first block is not empty. -/
  block_pos : 0 < r
  /-- The first block is at most half of the rank. -/
  two_mul_block_le : 2 * r ≤ k
  /-- The proportion `θ` is positive. -/
  proportion_pos : 0 < θ
  /-- The proportion `θ` is at most `1`. -/
  proportion_le_one : θ ≤ 1
  /-- The residue field is large against the degree. -/
  degree_pow_le : n ^ 4 ≤ T.q
  /-- The degree is large against `N k log q / θ` and `P ^ r`. -/
  le_degree : (N * k * Real.log T.q / θ) ^ 5 * T.P ^ (3 * r) ≤ n

/-- Half of the letters are even. -/
lemma card_isEven_add_self : #{s : ZMod N | T.isEven s} + #{s : ZMod N | T.isEven s} = N := by
  have h_shift : #({s | T.isEven s} : Finset (ZMod N))ᶜ = #{s | T.isEven s} :=
    card_equiv (.addRight 1) (by simp [T.isEven_succ])
  simpa only [h_shift, ZMod.card] using card_add_card_compl {s | T.isEven s}

include T in
/-- The number of letters is positive and even, hence at least `2`. -/
lemma two_le_card_letters : 2 ≤ N :=
  Nat.le_of_dvd (NeZero.pos N) (even_iff_two_dvd.1 ⟨_, T.card_isEven_add_self.symm⟩)

/-- The precision `c = 5 N c₀`, with `c₀ = T.multinomialExponent k`, of the congruences modulo
`w ^ c` that are imposed on the value of a function at an edge. -/
def congruencePrecision (k : ℕ) : ℕ := 5 * (N * T.multinomialExponent k)

/-- For rank `k ≥ 2` one has `N c₀ ≥ 2`, where `N` is the number of letters and
`c₀ = T.multinomialExponent k = k ^ 2 * (frobExp * N)` with `P = p ^ frobExp`. -/
lemma two_le_mul_multinomialExponent (hk : 2 ≤ k) : 2 ≤ N * T.multinomialExponent k := by
  have h_frobExp : 0 < T.frobExp := Nat.pos_of_ne_zero fun h ↦ by simpa [h] using T.five_le_P
  have hN : 0 < N := NeZero.pos N
  calc 2 ≤ k ^ 2 := hk.trans (Nat.le_self_pow two_ne_zero k)
    _ ≤ k ^ 2 * (T.frobExp * N) := Nat.le_mul_of_pos_right _ (Nat.mul_pos h_frobExp hN)
    _ ≤ N * T.multinomialExponent k := Nat.le_mul_of_pos_left _ hN

omit [NeZero N] in
/-- Let `T` be a Frobenius cycle with `N` letters and prime `p = T.p`, and let
`q = T.q = p ^ (T.frobExp * N)` be the size of the residue field of `W`. Then the number
`c₀ = T.multinomialExponent k = k ^ 2 log_p q` is at most `3 / 2 * k ^ 2 * log q`, because
`log p ≥ log 2 ≥ 2 / 3`. -/
lemma multinomialExponent_le_mul_log (k : ℕ) :
    (T.multinomialExponent k : ℝ) ≤ 3 / 2 * k ^ 2 * Real.log T.q := by
  have h_p : Real.log 2 ≤ Real.log T.p := Real.log_le_log two_pos (by exact_mod_cast T.prime.two_le)
  have h_eq : Real.log T.q = T.frobExp * N * Real.log T.p := by
    rw [FrobeniusCycle.q, FrobeniusCycle.P, ← pow_mul, Nat.cast_pow, Real.log_pow, Nat.cast_mul]
  have h_log : (T.frobExp * N : ℝ) ≤ 3 / 2 * Real.log T.q := by
    nlinarith [Real.log_two_gt_d9, show (0 : ℝ) ≤ T.frobExp * N by positivity]
  calc (T.multinomialExponent k : ℝ) = k ^ 2 * (T.frobExp * N) := by simp [multinomialExponent]
    _ ≤ k ^ 2 * (3 / 2 * Real.log T.q) := by gcongr
    _ = 3 / 2 * k ^ 2 * Real.log T.q := by ring

omit [NeZero N] in
lemma congruencePrecision_le_mul_log (k : ℕ) :
    (T.congruencePrecision k : ℝ) ≤ 15 / 2 * k ^ 2 * N * Real.log T.q := by
  grw [congruencePrecision, Nat.cast_mul, Nat.cast_mul, T.multinomialExponent_le_mul_log k]
  exact le_of_eq (by ring)

namespace IsLargeDegree

variable {T : FrobeniusCycle N W O} {r : ℕ} {θ : ℝ}

omit [NeZero N] in
/-- Large degree (`New.FrobeniusCycle.IsLargeDegree`) forces the rank `k ≥ 2 r` to be at least
`2`. -/
lemma two_le_rank (h_large : T.IsLargeDegree k n r θ) : 2 ≤ k := by
  linarith [h_large.block_pos, h_large.two_mul_block_le]

lemma four_le_mul (h_large : T.IsLargeDegree k n r θ) : 4 ≤ N * k :=
  Nat.mul_le_mul T.two_le_card_letters h_large.two_le_rank

omit [NeZero N] in
/-- Dividing `N k log q` by the proportion `θ ∈ (0, 1]` of exceptional elementary divisors does not
make it smaller; here `q = P ^ N` is the size of the residue field. -/
lemma mul_log_le_div (h_large : T.IsLargeDegree k n r θ) :
    N * k * Real.log T.q ≤ N * k * Real.log T.q / θ :=
  le_div_self (by positivity) h_large.proportion_pos h_large.proportion_le_one

/-- Let `T` be a Frobenius cycle: a prime `p`, a power `P = T.P` of `p` and `N` ring maps `W → O`
(the letters), each the `P`-th power of the one before modulo `p`, where the residue field of `W`
has `q = P ^ N` elements. Let the degree `n` be large: `0 < r ≤ k / 2`, `0 < θ ≤ 1`, `n ^ 4 ≤ q` and
`(N k log q / θ) ^ 5 P ^ (3 r) ≤ n`. Then `(N k) ^ 5 ≤ n`, because `log q ≥ 1`. -/
lemma mul_pow_le_degree (h_large : T.IsLargeDegree k n r θ) : (N * k) ^ 5 ≤ n := by
  have h_log : 1 ≤ Real.log T.q := by
    have h_five : (5 : ℝ) ≤ T.q := mod_cast T.five_le_P.trans (Nat.le_self_pow (NeZero.ne N) T.P)
    exact (Real.le_log_iff_exp_le (by linarith)).2 (by linarith [Real.exp_one_lt_three])
  have hθ : 0 < θ := h_large.proportion_pos
  have h_base : (N * k : ℝ) ≤ N * k * Real.log T.q / θ :=
    (le_mul_of_one_le_right (by positivity) h_log).trans h_large.mul_log_le_div
  rify
  calc ((N : ℝ) * k) ^ 5 ≤ (N * k * Real.log T.q / θ) ^ 5 := by gcongr
    _ ≤ (N * k * Real.log T.q / θ) ^ 5 * T.P ^ (3 * r) :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ T.one_lt_P.le)
    _ ≤ n := h_large.le_degree

/-- Under the size conditions `h_large`, `27 ≤ log T.q`: from `T.q ≥ n ^ 4` and
`n ≥ (N k) ^ 5 ≥ 4 ^ 5` follows `log T.q ≥ 40 log 2 ≥ 27`. -/
lemma twenty_seven_le_log_q (h_large : T.IsLargeDegree k n r θ) : 27 ≤ Real.log T.q := by
  have h_two : 2 ^ 40 ≤ T.q :=
    calc 2 ^ 40 = (4 ^ 5) ^ 4 := by norm_num
      _ ≤ ((N * k) ^ 5) ^ 4 := by grw [← h_large.four_le_mul]
      _ ≤ T.q := (Nat.pow_le_pow_left h_large.mul_pow_le_degree 4).trans h_large.degree_pow_le
  calc (27 : ℝ) ≤ 40 * Real.log 2 := by linarith [Real.log_two_gt_d9]
    _ = Real.log (2 ^ 40) := by simp
    _ ≤ Real.log T.q := Real.log_le_log (by positivity) (mod_cast h_two)

/-- Let `T` be a Frobenius cycle: a prime `p`, a power `P = T.P` of `p` and `N` ring maps `W → O`
(the letters), each the `P`-th power of the one before modulo `p`, where the residue field of `W`
has `q = P ^ N` elements. Let the degree `n` be large: `0 < r ≤ k / 2`, `0 < θ ≤ 1`, `n ^ 4 ≤ q` and
`(N k log q / θ) ^ 5 P ^ (3 r) ≤ n`. For `2 ℓ = N` one has `N k (ℓ + 2) n + n + k < P ^ ℓ`, because
`P ^ ℓ = √q ≥ n ^ 2` and `n ≥ (N k) ^ 2 + 2`. -/
lemma mul_degree_add_lt_P_pow (h_large : T.IsLargeDegree k n r θ) {ℓ : ℕ} (hℓ : ℓ + ℓ = N) :
    N * k * (ℓ + 2) * n + n + k < T.P ^ ℓ := by
  have hN : 2 ≤ N := T.two_le_card_letters
  have hk : 2 ≤ k := h_large.two_le_rank
  have h_sqrt : n ^ 2 ≤ T.P ^ ℓ := by
    rw [← Nat.pow_le_pow_iff_left two_ne_zero, ← pow_mul, ← pow_mul, mul_two ℓ, hℓ]
    exact h_large.degree_pow_le
  have hℓ_le : ℓ + 2 ≤ N * k := by nlinarith
  have h_sq : (N * k) ^ 2 + 2 ≤ n :=
    calc (N * k) ^ 2 + 2 ≤ (N * k) ^ 2 * 4 ^ 3 := by nlinarith
      _ ≤ (N * k) ^ 2 * (N * k) ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h_large.four_le_mul 3)
      _ = (N * k) ^ 5 := by ring
      _ ≤ n := h_large.mul_pow_le_degree
  have hk_lt : k < n := by nlinarith
  calc N * k * (ℓ + 2) * n + n + k ≤ N * k * (N * k) * n + n + k := by gcongr
    _ < ((N * k) ^ 2 + 2) * n := by linarith
    _ ≤ n ^ 2 := by grw [h_sq, sq n]
    _ ≤ T.P ^ ℓ := h_sqrt

/-- A large degree `n` is greater than `1`, because `n ≥ (N k) ^ 5`. -/
lemma one_lt_degree (h_large : T.IsLargeDegree k n r θ) : 1 < n :=
  h_large.mul_pow_le_degree.trans_lt' (one_lt_pow₀ (by linarith [h_large.four_le_mul]) (by simp))

/-- A large degree `n` is less than the size `q` of the residue field, because `n ^ 4 ≤ q`. -/
lemma degree_lt_q (h_large : T.IsLargeDegree k n r θ) : n < T.q :=
  (lt_self_pow₀ h_large.one_lt_degree (by norm_num)).trans_le h_large.degree_pow_le

omit [NeZero N] in
/-- Under the size conditions `h_large`, `(N k log T.q) ^ 5 T.P ^ (3 r) ≤ θ n`: clear the
denominator in the degree condition `(N k log T.q / θ) ^ 5 T.P ^ (3 r) ≤ n` and use `θ ^ 5 ≤ θ`. -/
lemma mul_log_pow_mul_le (h_large : T.IsLargeDegree k n r θ) :
    (N * k * Real.log T.q) ^ 5 * T.P ^ (3 * r) ≤ θ * n := by
  have hθ : 0 < θ := h_large.proportion_pos
  calc (N * k * Real.log T.q) ^ 5 * T.P ^ (3 * r)
      = θ ^ 5 * ((N * k * Real.log T.q / θ) ^ 5 * T.P ^ (3 * r)) := by field_simp
    _ ≤ θ ^ 5 * n := by grw [h_large.le_degree]
    _ ≤ θ * n := by grw [pow_le_of_le_one hθ.le h_large.proportion_le_one (by norm_num)]

/-- Let `T` be a Frobenius cycle with `N` letters and the prime power `P = T.P`, and let
`q = P ^ N`. Let the degree `n` be large: `0 < r ≤ k / 2`, `0 < θ ≤ 1`, `n ^ 4 ≤ q` and
`(N k log q / θ) ^ 5 P ^ (3 r) ≤ n`. Then `c₀ P ^ (2 r) ≤ n`, where
`c₀ = T.multinomialExponent k = k ^ 2 log_p q` for the prime `p = T.p` of which `P` is a power. -/
lemma multinomialExponent_mul_le_degree (h_large : T.IsLargeDegree k n r θ) :
    (T.multinomialExponent k : ℝ) * T.P ^ (2 * r) ≤ n := by
  set L : ℝ := Real.log T.q
  have hL : 27 ≤ L := h_large.twenty_seven_le_log_q
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast T.two_le_card_letters
  have hk : (2 : ℝ) ≤ k := by exact_mod_cast h_large.two_le_rank
  have hP : (1 : ℝ) ≤ T.P := T.one_lt_P.le
  have hNL : 2 ≤ N * L := by nlinarith
  have h_one_le : 1 ≤ N * k * L := by nlinarith
  have h_const : (3 / 2 : ℝ) ≤ N * (N * L) := by nlinarith
  calc (T.multinomialExponent k : ℝ) * T.P ^ (2 * r)
      ≤ 3 / 2 * k ^ 2 * L * T.P ^ (2 * r) := by grw [T.multinomialExponent_le_mul_log k]
    _ ≤ N * (N * L) * k ^ 2 * L * T.P ^ (2 * r) := by gcongr
    _ = (N * k * L) ^ 2 * T.P ^ (2 * r) := by ring
    _ ≤ (N * k * L) ^ 5 * T.P ^ (3 * r) := by gcongr <;> norm_num
    _ ≤ θ * n := h_large.mul_log_pow_mul_le
    _ ≤ n := mul_le_of_le_one_left n.cast_nonneg h_large.proportion_le_one

/-- Let `T` be a Frobenius cycle with `N` letters and the prime power `P = T.P`, and let
`q = P ^ N`. Let the degree `n` be large: `0 < r ≤ k / 2`, `0 < θ ≤ 1`, `n ^ 4 ≤ q` and
`(N k log q / θ) ^ 5 P ^ (3 r) ≤ n`. Then `N c₀ ≤ c_div`, where
`c₀ = T.multinomialExponent k = k ^ 2 log_p q` with `p = T.p`, and `c_div = T.divisorConstant k n
r = N n (1 / P ^ (2 r) + r ^ 2 / (k P))`. -/
lemma mul_multinomialExponent_le_divisorConstant (h_large : T.IsLargeDegree k n r θ) :
    (N * T.multinomialExponent k : ℝ) ≤ T.divisorConstant k n r := by
  have hP : (1 : ℝ) ≤ T.P := T.one_lt_P.le
  have h_div : (T.multinomialExponent k : ℝ) ≤ n / (T.P : ℝ) ^ (2 * r) :=
    (le_div_iff₀ (by positivity)).2 h_large.multinomialExponent_mul_le_degree
  calc (N * T.multinomialExponent k : ℝ) ≤ N * (n / (T.P : ℝ) ^ (2 * r)) := by gcongr
    _ = N * n * (1 / (T.P : ℝ) ^ (2 * r)) := by ring
    _ ≤ N * n * (1 / (T.P : ℝ) ^ (2 * r) + r ^ 2 / (k * T.P)) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)
    _ = T.divisorConstant k n r := by rw [divisorConstant]

/-- Let `T` be a Frobenius cycle with `N` letters and the prime power `P = T.P`, and let
`q = P ^ N`. Let the degree `n` be large: `0 < r ≤ k / 2`, `0 < θ ≤ 1`, `n ^ 4 ≤ q` and
`(N k log q / θ) ^ 5 P ^ (3 r) ≤ n`. Then `8 N k c* P ^ (2 r) ≤ θ n`, where
`c* = defectThreshold k c = 3 k c` for the precision
`c = T.congruencePrecision k = 5 N k ^ 2 log_p q`, `p = T.p`. -/
lemma mul_defectThreshold_le_mul_degree (h_large : T.IsLargeDegree k n r θ) :
    8 * N * k * defectThreshold k (T.congruencePrecision k) * T.P ^ (2 * r) ≤ θ * n := by
  -- With `u = N k log q ≥ 27 N k` the left side is at most `180 N k ^ 3 u P ^ (2 r)`.
  set L : ℝ := Real.log T.q
  set u : ℝ := N * k * L
  have hL : 27 ≤ L := h_large.twenty_seven_le_log_q
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast T.two_le_card_letters
  have hk : (2 : ℝ) ≤ k := by exact_mod_cast h_large.two_le_rank
  have hu : 27 * (N * k) ≤ u :=
    (mul_comm _ _).trans_le (mul_le_mul_of_nonneg_left hL (by positivity))
  have hc : (T.congruencePrecision k : ℝ) ≤ 15 / 2 * (k * u) :=
    (T.congruencePrecision_le_mul_log k).trans_eq (by ring)
  have h_const : (180 : ℝ) ≤ 27 ^ 4 * N ^ 3 * k := by
    nlinarith [pow_le_pow_left₀ zero_le_two hN 3]
  have h_power : (180 * N * k ^ 3 : ℝ) ≤ u ^ 4 :=
    calc (180 * N * k ^ 3 : ℝ) ≤ 27 ^ 4 * N ^ 3 * k * N * k ^ 3 := by gcongr
      _ = (27 * (N * k)) ^ 4 := by ring
      _ ≤ u ^ 4 := by gcongr
  calc (8 * N * k * defectThreshold k (T.congruencePrecision k) * T.P ^ (2 * r) : ℝ)
      = 24 * N * k ^ 2 * T.congruencePrecision k * T.P ^ (2 * r) := by
        simp only [defectThreshold, Nat.cast_mul, Nat.cast_ofNat]
        ring
    _ ≤ 24 * N * k ^ 2 * (15 / 2 * (k * u)) * T.P ^ (2 * r) := by gcongr
    _ = 180 * N * k ^ 3 * u * T.P ^ (2 * r) := by ring
    _ ≤ u ^ 4 * u * T.P ^ (3 * r) := by
        gcongr
        exacts [T.one_lt_P.le, by norm_num]
    _ = u ^ 5 * T.P ^ (3 * r) := by ring
    _ ≤ θ * n := h_large.mul_log_pow_mul_le

end IsLargeDegree

end Sizes

/-! ### Conditions on an edge -/

/-- Conditions modulo `w ^ c` on the value of a function at an edge. Vectors are coefficients in the
normalized monomials, and `(h, h') ↦ h' ⬝ᵥ (b * h)` is the pairing with the dual edge. The module
`C` consists of the values that satisfy the conditions, `Av` is the averaging map, and `S` contains
the reductions of the vectors `h` with `w ^ (c - 1) • h ∈ C`. -/
structure IsEdgeCondition {N k n : ℕ} {W O : Type} [NeZero N] [CommRing W] [IsLocalRing W]
    [CommRing O] [IsDomain O] [ValuationRing O] (T : FrobeniusCycle N W O) (r c : ℕ) (θ : ℝ)
    (b : Exponents N k n → O)
    (C : Submodule O (Exponents N k n → O))
    (S : Submodule (ResidueField O) (Exponents N k n → ResidueField O))
    (Av : Matrix (Exponents N k n) (Exponents N k n) O) : Prop where
  /-- The conditions hold for the forms in the halfway lattices of all edges from the origin. -/
  allEdgesForms_le : T.allEdgesForms k n r ≤ C
  /-- The conditions are congruences modulo `w ^ c`: multiples of `w ^ c` satisfy them. -/
  pow_smul_mem : ∀ h : Exponents N k n → O, T.sqrtPrime ^ c • h ∈ C
  /-- The values of `Av` satisfy the conditions. -/
  average_mem : ∀ h : Exponents N k n → O, Av *ᵥ h ∈ C
  /-- Against the forms in the halfway lattices of all edges from the origin of the dual edge, `Av`
  is multiplication by `p ^ (N c₀)` modulo `w ^ c`, with `c₀ = T.multinomialExponent k`. -/
  pow_dvd_pairing_average : ∀ h : Exponents N k n → O, ∀ h' ∈ T.allEdgesForms k n r,
    T.sqrtPrime ^ c ∣ h' ⬝ᵥ (b * Av *ᵥ h) - (T.p : O) ^ (N * T.multinomialExponent k) * h' ⬝ᵥ
      (b * h)
  /-- If `w ^ (c - 1) • h` satisfies the conditions, then `h` reduces into `S`. -/
  residue_mem : ∀ h : Exponents N k n → O,
    T.sqrtPrime ^ (c - 1) • h ∈ C → (fun β : Exponents N k n ↦ residue O (h β)) ∈ S
  /-- The number of edges into a lattice times `dim S` is at most `1 + θ` times the number of
  monomials. -/
  index_mul_finrank_le : ((parahoric W (twoBlock k r)).index * finrank (ResidueField O) S : ℝ) ≤
    (1 + θ) * Fintype.card (Exponents N k n)

omit [ValuationRing O] in
/-- The module `T.translatesIn n τ J B` consists of the vectors whose translates by the Levi
subgroup of `τ` have their coefficients at `B` in the ideal `J`. Let `0 < c`. If
`T.sqrtPrime ^ (c - 1) • h` lies in this module for the ideal `(T.sqrtPrime ^ c)`, then `h` lies in
it for every ideal `J` that contains `T.sqrtPrime`. -/
lemma mem_translatesIn_of_pow_smul_mem {τ : Fin k → ℕ} {B : Set (Exponents N k n)} {c : ℕ}
    (hc : 0 < c) {J : Ideal O} (hw : T.sqrtPrime ∈ J) {h : Exponents N k n → O}
    (h_mem : T.sqrtPrime ^ (c - 1) • h ∈ T.translatesIn n τ (span {T.sqrtPrime ^ c}) B) :
    h ∈ T.translatesIn n τ J B := by
  intro g hg β hβ
  have h_dvd : T.sqrtPrime ^ (c - 1) * T.sqrtPrime ∣ T.sqrtPrime ^ (c - 1) * (T.letterRep n g *ᵥ h)
    β := by
    simpa [pow_sub_one_mul hc.ne', mulVec_smul] using Ideal.mem_span_singleton.1 (h_mem g hg β hβ)
  exact mem_of_dvd J ((mul_dvd_mul_iff_left (pow_ne_zero _ T.sqrtPrime_ne_zero)).1 h_dvd) hw

omit [IsDomain O] [ValuationRing O] [CharZero O] [NeZero N] in
/-- If the prime `T.p` is not a unit of the local ring `O`, then its square root `T.sqrtPrime` (with
`T.sqrtPrime ^ 2 = T.p`) lies in the maximal ideal `maximalIdeal O`. -/
lemma sqrtPrime_mem_maximalIdeal [IsLocalRing O] (hp : ¬IsUnit (T.p : O)) :
    T.sqrtPrime ∈ maximalIdeal O :=
  fun hw ↦ hp (by simpa only [T.sqrtPrime_sq] using hw.pow 2)

omit [IsDomain O] [ValuationRing O] [CharZero O] [NeZero N] in
/-- If `p` is not a unit of `O`, then the residue field of `O` has characteristic `p`, the prime of
the reduced Frobenius cycle. -/
lemma charP_residueField [IsLocalRing O] (hp : ¬IsUnit (T.p : O)) :
    CharP (ResidueField O) (T.map (residue O)).p := by
  refine (CharP.charP_iff_prime_eq_zero T.prime).2 ?_
  simpa only [map_natCast] using (residue_eq_zero_iff (T.p : O)).2 hp

/-- Let `W` be a local ring, `O` a valuation domain of characteristic zero and `T` a Frobenius cycle
with `N` letters (ring maps `W → O`). Its prime `p = T.p = w ^ 2`, `w = T.sqrtPrime`, is not a unit
of `O`, and the residue field of `W` has `q = P ^ N` elements for the power `P = T.P` of `p`. Forms
have `k` variables and degree `n` in each letter and are given by their coefficients, and
`g ∈ GL_k(W)` acts on them by the matrix `ρ(g) = T.letterRep n g`. Let `0 < r ≤ k / 2`, `0 < θ ≤ 1`,
`n ^ 4 ≤ q` and `(N k log q / θ) ^ 5 P ^ (3 r) ≤ n` (`h_large`). Let `b` be weights such that `ρ(g)`
and `ρ(gᵀ)` are adjoint for `(h, h') ↦ h' ⬝ᵥ (b * h)`, with `b * b' = p ^ (N c₀)` for
`c₀ = T.multinomialExponent k` (`hb`). Put `c = T.congruencePrecision k = 5 N c₀`, and let
`M = T.allEdgesForms k n r` be the module of forms that lie in the halfway lattices of all edges
from a lattice. Then there are
* a module `C` of forms that contains `M` and the multiples of `w ^ c`,
* a matrix `Av` with values in `C` that, paired against `M`, is multiplication by `p ^ (N c₀)`
  modulo `w ^ c`,
* a space `S` over the residue field of `O` that contains the reductions of the `h` with
  `w ^ (c - 1) • h ∈ C`, such that `dim S` times the index in `GL_k(W)` of the parahoric subgroup
  with blocks `r` and `k - r` is at most `1 + θ` times the number of monomials. -/
theorem exists_isEdgeCondition (hp : ¬IsUnit (T.p : O)) {r : ℕ} {θ : ℝ}
    (h_large : T.IsLargeDegree k n r θ) {b b' : Exponents N k n → O} (hb : T.IsEdgePairing b b') :
    ∃ (C : Submodule O (Exponents N k n → O))
      (S : Submodule (ResidueField O) (Exponents N k n → ResidueField O))
      (Av : Matrix (Exponents N k n) (Exponents N k n) O),
      T.IsEdgeCondition r (T.congruencePrecision k) θ b C S Av := by
  -- `C` and `S` are the defect conditions over `O` modulo `w ^ c` and over the residue field;
  -- `Av` is the averaging map, and `dim S` is bounded by counting monomials of small defect.
  set c : ℕ := T.congruencePrecision k
  have hr_pos : 0 < r := h_large.block_pos
  have h_two : 2 ≤ N * T.multinomialExponent k :=
    T.two_le_mul_multinomialExponent h_large.two_le_rank
  have hc : 0 < c := Nat.mul_pos (by norm_num) (zero_lt_two.trans_le h_two)
  lift r to Fin k using by linarith [h_large.two_mul_block_le]
  obtain ⟨a, ha⟩ : ∃ a : Fin k, a + 1 = r.val := ⟨⟨r - 1, by lia⟩, by lia⟩
  have h_char : CharP (ResidueField O) (T.map (residue O)).p := T.charP_residueField hp
  let C : Submodule O (Exponents N k n → O) :=
    T.defectConditions n a r (span {T.sqrtPrime ^ c}) (3 * defectThreshold k c)
  let S : Submodule (ResidueField O) (Exponents N k n → ResidueField O) :=
    (T.map (residue O)).defectConditions n a r ⊥ (3 * defectThreshold k c)
  obtain ⟨Av, h_mem : ∀ h : Exponents N k n → O, Av *ᵥ h ∈ C, h_pairing⟩ :=
    T.exists_average_mem_defectConditions_and_dvd_sub hp ha T.card_isEven_add_self
      (h_large.mul_degree_add_lt_P_pow T.card_isEven_add_self) hb c
  have h_index : ((parahoric W (twoBlock k r)).index * finrank (ResidueField O) S : ℝ) ≤
      (1 + θ) * Fintype.card (Exponents N k n) := by
    have h_rank : 2 * (k + 1) ≤ defectThreshold k c :=
      (by lia : 2 * (k + 1) ≤ 3 * k).trans (Nat.le_mul_of_pos_right _ hc)
    simpa only [Fintype.card_fun, ZMod.card, Nat.cast_pow] using
      (T.map (residue O)).index_mul_finrank_defectConditions_le ha h_large.one_lt_degree.le h_rank
        h_large.proportion_le_one h_large.mul_defectThreshold_le_mul_degree
  exact ⟨C, S, Av,
    { allEdgesForms_le := T.allEdgesForms_le_defectConditions ha.le c
      pow_smul_mem := fun h g _ β _ ↦ by simp [mulVec_smul, Ideal.mem_span_singleton]
      average_mem := h_mem
      pow_dvd_pairing_average := h_pairing
      residue_mem := fun h h_cond ↦ T.residue_mem_translatesIn
        (T.mem_translatesIn_of_pow_smul_mem hc (T.sqrtPrime_mem_maximalIdeal hp) h_cond)
      index_mul_finrank_le := h_index }⟩

/-! ### The operator and its factorization -/

section Operator

variable {r : ℕ} {X H I : Type*} [Fintype (ParahoricCosets W k r)] [Fintype H] [DecidableEq H]
  [Fintype I]

omit [IsDomain O] [ValuationRing O] [CharZero O]

/-- The diagonal matrix that multiplies the coefficient of a monomial by `p ^ depth`. -/
abbrev depthPower (k n r : ℕ) : Matrix (Exponents N k n) (Exponents N k n) O :=
  diagonal fun β : Exponents N k n ↦ (T.p : O) ^ T.depth k n r β

/-- The edge Hecke operator on functions `F : X → O ^ I`, in coordinates. Here `J` identifies `I`
with (exponents) × `H`, and the values of `F` are coefficients in the basis `(n! ^ N / β!) z ^ β`,
in which the substitution `h ↦ h ∘ g` has the matrix `ρ(g)ᵀ`, `ρ = T.letterRep n`. The value at `x`
is the sum over the edges `e = (x, b)` into `x` of the matrix `(ρ(originBasisChange e) p ^ depth
ρ(terminusBasisChange b))ᵀ ⊗ transition e` applied to `F (origin e)`. In terms of forms this is
`p ^ (N n / 2)` times the sum of the values at the origins of the edges, each carried to `x` by the
element `δ` of its edge. -/
def edgeHeckeOperator (n : ℕ) (J : I ≃ Exponents N k n × H) (𝓔 : EdgeCoordinates W O k r X H) :
    End O (X → I → O) :=
  LinearMap.pi fun x : X ↦ ∑ b : ParahoricCosets W k r,
    (((T.letterRep n (𝓔.originBasisChange (x, b)) * T.depthPower k n r *
        T.letterRep n (𝓔.terminusBasisChange b))ᵀ ⊗ₖ
      (𝓔.transition (x, b)).val).submatrix J J).mulVecLin ∘ₗ LinearMap.proj (𝓔.origin (x, b))

/-- The edge Hecke operator entry by entry: at `x`, `i` it is the sum over `b`, `j` of
`𝓔.transition (x, b)` at `(J i).2`, `(J j).2`, times the `((J j).1, (J i).1)` entry of the matrix
product, times `F (𝓔.origin (x, b)) j`. -/
lemma edgeHeckeOperator_apply (n : ℕ) (J : I ≃ Exponents N k n × H)
    (𝓔 : EdgeCoordinates W O k r X H) (F : X → I → O) :
    T.edgeHeckeOperator n J 𝓔 F = fun (x : X) (i : I) ↦ ∑ b : ParahoricCosets W k r, ∑ j : I,
      𝓔.transition (x, b) (J i).2 (J j).2 *
        (T.letterRep n (𝓔.originBasisChange (x, b)) * T.depthPower k n r *
          T.letterRep n (𝓔.terminusBasisChange b)) (J j).1 (J i).1 * F (𝓔.origin (x, b)) j := by
  ext x i
  -- `-transpose_mul` keeps the product of the three matrices under one transpose.
  simp [edgeHeckeOperator, mul_comm (𝓔.transition _ _ _), -transpose_mul, mulVec, dotProduct]

variable {T} in
omit [Fintype (ParahoricCosets W k r)] in
/-- Let `T` be a Frobenius cycle with `N` letters (ring maps `W → O`) and prime `p = w ^ 2`,
`w = T.sqrtPrime`. Let `ρ = T.letterRep n` be the representation of `GL_k(W)` on the forms with `k`
variables and degree `n` in each letter, and let `ρ(g)` and `ρ(gᵀ)` be adjoint for the pairing with
weights `b` (`hb`). Let `D = T.depthScaling k n r` be diagonal with entries `w ^ depth β`, where
`depth β` is the degree of the monomial `β` in the deep variables: those after the first `r` in an
even letter, and the first `r` in an odd letter. So `D ^ 2 = T.depthPower k n r` has entries
`p ^ depth β`. Then `(D ρ(γ))ᵀ diag(b) D ρ(gᵀ) = (ρ(g) D ^ 2 ρ(γ))ᵀ diag(b)`. -/
lemma IsEdgePairing.transpose_mul_diagonal_mul {b b' : Exponents N k n → O}
    (hb : T.IsEdgePairing b b') (g γ : GL (Fin k) W) :
    (T.depthScaling k n r * T.letterRep n γ)ᵀ * diagonal b *
        (T.depthScaling k n r * T.letterRep n (transposeGL g)) =
      (T.letterRep n g * T.depthPower k n r * T.letterRep n γ)ᵀ * diagonal b := by
  set D : Matrix (Exponents N k n) (Exponents N k n) O := T.depthScaling k n r
  have h_adjoint : diagonal b * T.letterRep n (transposeGL g) =
      (T.letterRep n g)ᵀ * diagonal b := by
    ext β α
    rw [diagonal_mul, mul_diagonal, transpose_apply, hb.adjoint, mul_comm]
  have h_square : D * diagonal b * D = T.depthPower k n r * diagonal b := by
    simp [D, depthScaling, ← T.sqrtPrime_sq, ← pow_mul, two_mul, pow_add, mul_right_comm]
  calc (D * T.letterRep n γ)ᵀ * diagonal b * (D * T.letterRep n (transposeGL g))
      = (T.letterRep n γ)ᵀ * (D * diagonal b * D) * T.letterRep n (transposeGL g) := by
        simp only [D, depthScaling, transpose_mul, diagonal_transpose, Matrix.mul_assoc]
    _ = (T.letterRep n g * T.depthPower k n r * T.letterRep n γ)ᵀ * diagonal b := by
        simp only [h_square, h_adjoint, transpose_mul, diagonal_transpose, Matrix.mul_assoc]

variable {T} in
/-- Let `T` be a Frobenius cycle with `N` letters, and let forms have `k` variables and degree `n`
in each letter. The points of `X` represent lattices of rank `k`, each with a free `O`-module with
basis indexed by `H`. An edge is a pair `e = (x, q)` of its terminus `x ∈ X` and a coset `q` of the
parahoric subgroup of `GL_k(W)` with blocks `r` and `k - r`. The coordinates `𝓔` give the origin of
`e`, bases adapted to `e` at both ends, and the matrix `𝓔.transition e` on `O ^ H`. The bijection
`J` splits the index set `I` into exponents and `H`, and `regroup J` reads a vector indexed by
`(H × X) × exponents` as a function `X → I → O`. The operator sums, over the edges into `x`, the
values at their origins carried to `x`. Let `b` be the weights of a pairing of forms for which `g`
and `gᵀ` act adjointly (`hb`). On vectors multiplied by `b` the operator is the restriction to
edges, which gives an edge the value at its origin in the adapted basis (`T.edgeRestriction`),
followed by the pairing with the functions restricted to the dual edges from their origins, which
are dual to the termini of the edges. -/
lemma IsEdgePairing.edgeHeckeOperator_regroup [Fintype X] [DecidableEq X]
    [DecidableEq (ParahoricCosets W k r)] {b b' : Exponents N k n → O} (hb : T.IsEdgePairing b b')
    (J : I ≃ Exponents N k n × H) (𝓔 : EdgeCoordinates W O k r X H)
    (F : (H × X) × Exponents N k n → O) :
    T.edgeHeckeOperator n J 𝓔 (regroup J fun y : (H × X) × Exponents N k n ↦ b y.2 * F y) =
      regroup J
        ((pairingMap 𝓔.transition b (T.edgeRestriction n r (Prod.map id Prod.fst)
            (𝓔.terminusBasisChange ∘ Prod.snd ∘ Prod.snd)) *
          T.edgeRestriction n r (Prod.map id 𝓔.origin)
            fun e : H × X × ParahoricCosets W k r ↦
              transposeGL (𝓔.originBasisChange e.2)) *ᵥ F) := by
  -- At `(x, i)` both sides are sums over the edges `(x, q)` into `x`, and they agree term by term
  -- because `ρ(g)` and `ρ(gᵀ)` are adjoint for the pairing.
  ext x i
  let ψ : (H × X × ParahoricCosets W k r) × Exponents N k n → O :=
    T.edgeRestriction n r (Prod.map id 𝓔.origin)
      (fun e : H × X × ParahoricCosets W k r ↦ transposeGL (𝓔.originBasisChange e.2)) *ᵥ F
  let φ : (H × X × ParahoricCosets W k r) × Exponents N k n → O :=
    edgewise (fun e : X × ParahoricCosets W k r ↦ (𝓔.transition e).val) (diagonal b) *ᵥ ψ
  let A (q : ParahoricCosets W k r) : Matrix (Exponents N k n) (Exponents N k n) O :=
    T.letterRep n (𝓔.originBasisChange (x, q)) * T.depthPower k n r *
      T.letterRep n (𝓔.terminusBasisChange q)
  have hψ_value (h : H) (q : ParahoricCosets W k r) :
      (fun β : Exponents N k n ↦ ψ ((h, x, q), β)) =
        (T.depthScaling k n r * T.letterRep n (transposeGL (𝓔.originBasisChange (x, q)))) *ᵥ
          fun α : Exponents N k n ↦ F ((h, 𝓔.origin (x, q)), α) := by
    simp only [ψ, edgeRestriction_mulVec_apply, mulVec_mulVec, Prod.map_apply, id_eq]
  have h_term (h : H) (q : ParahoricCosets W k r) :
      (T.depthScaling k n r * T.letterRep n (𝓔.terminusBasisChange q))ᵀ *ᵥ
          (fun β : Exponents N k n ↦ φ ((h, x, q), β)) =
        ∑ h' : H, 𝓔.transition (x, q) h h' • ((A q)ᵀ * diagonal b) *ᵥ
          fun α : Exponents N k n ↦ F ((h', 𝓔.origin (x, q)), α) := by
    simp only [φ, A, edgewise_mulVec, hψ_value, mulVec_sum, mulVec_smul, mulVec_mulVec,
      ← Matrix.mul_assoc _ (diagonal b), hb.transpose_mul_diagonal_mul]
  -- The edges whose dual has the origin `(h, x)` are the `(h, x, q)`.
  have h_edges (h : H) (f : H × X × ParahoricCosets W k r → O) :
      ∑ e : H × X × ParahoricCosets W k r with Prod.map id Prod.fst e = (h, x), f e =
        ∑ q : ParahoricCosets W k r, f (h, x, q) := by
    simp [sum_filter, Fintype.sum_prod_type, ite_and, sum_comm (γ := X)]
  calc T.edgeHeckeOperator n J 𝓔 (regroup J fun y ↦ b y.2 * F y) x i
      = ∑ q : ParahoricCosets W k r, ∑ h' : H, ∑ α : Exponents N k n,
          𝓔.transition (x, q) (J i).2 h' * A q α (J i).1 *
            (b α * F ((h', 𝓔.origin (x, q)), α)) := by
        rw [edgeHeckeOperator_apply]
        refine sum_congr rfl fun q _ ↦ ?_
        rw [← J.symm.sum_comp, Fintype.sum_prod_type_right]
        simp only [A, regroup_apply, Equiv.apply_symm_apply]
    _ = ∑ q : ParahoricCosets W k r,
          ((T.depthScaling k n r * T.letterRep n (𝓔.terminusBasisChange q))ᵀ *ᵥ
            fun β : Exponents N k n ↦ φ (((J i).2, x, q), β)) (J i).1 := by
        refine sum_congr rfl fun q _ ↦ ?_
        rw [h_term]
        simp [mulVec, dotProduct, mul_sum, mul_assoc]
    _ = ((T.edgeRestriction n r (Prod.map id Prod.fst)
          (𝓔.terminusBasisChange ∘ Prod.snd ∘ Prod.snd))ᵀ *ᵥ φ) (((J i).2, x), (J i).1) := by
        simp only [transpose_edgeRestriction_mulVec, h_edges, Function.comp_apply]
    _ = _ := by simp only [regroup_apply, pairingMap, ← mulVec_mulVec, φ, ψ]

end Operator

/-! ### The proof of the theorem -/

omit [IsDomain O] [ValuationRing O] [CharZero O] [NeZero N] in
/-- The constant `T.divisorConstant k n r = N n (1 / P ^ (2 r) + r ^ 2 / (k P))` is nonnegative. -/
lemma divisorConstant_nonneg (k n r : ℕ) : 0 ≤ T.divisorConstant k n r := by
  rw [divisorConstant]
  positivity

variable {T} in
/-- Let `T` be a Frobenius cycle with `N` letters (ring maps `W → O`) whose prime `p = w ^ 2`,
`w = T.sqrtPrime`, is not a unit of `O`. Forms have `k` variables and degree `n` in each letter, and
their monomials are indexed by `Exponents N k n`. Let `0 < r ≤ k / 2`, `0 < θ ≤ 1`, `n ^ 4 ≤ q` and
`(N k log q / θ) ^ 5 P ^ (3 r) ≤ n` for `P = T.P` and `q = P ^ N` (`h_large`). The edge `e ∈ E` has
the origin `src e ∈ X` and the basis change `g e`, and every edge from every origin occurs: each
pair of a point of `X` and a coset of the parahoric subgroup of `GL_k(W)` with blocks `r` and
`k - r` is `(src e, (g e)⁻¹)` for some `e`. The functions on edges that depend only on the origin
(`T.originFunctions`) are the image of a matrix `Q` with a left inverse, so its columns are a basis,
and the inclusion `T.edgeRestriction` of the integral functions on origins is `Q * d`, where `det d`
divides `w ^ l` and `l` is at most `c_div = T.divisorConstant k n r` times the rank. -/
lemma IsLargeDegree.exists_basis_det_dvd {r : ℕ} {θ : ℝ} (h_large : T.IsLargeDegree k n r θ)
    (hp : ¬IsUnit (T.p : O)) {X E : Type*} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
    {src : E → X} {g : E → GL (Fin k) W}
    (h_surj : Surjective fun e : E ↦ ((src e, ↑(g e)⁻¹) : X × ParahoricCosets W k r)) :
    ∃ (Q : Matrix (E × Exponents N k n) (X × Exponents N k n) O)
      (R : Matrix (X × Exponents N k n) (E × Exponents N k n) O)
      (d : Matrix (X × Exponents N k n) (X × Exponents N k n) O),
      Q.mulVecLin.range = T.originFunctions n r src g ∧
      R * Q = 1 ∧
      Q * d = T.edgeRestriction n r src g ∧
      d.det ∣ T.sqrtPrime ^ (Fintype.card X * ⌊T.divisorConstant k n r * Fintype.card
        (Exponents N k n)⌋₊) := by
  have h_char : CharP (ResidueField O) (T.map (residue O)).p := T.charP_residueField hp
  obtain ⟨x, hx : ∀ β : Exponents N k n, T.depth k n r β ≤ x⟩ := Finite.exists_le (T.depth k n r)
  obtain ⟨Q, R, d, hQ : ∀ φ : X × Exponents N k n → O, Q *ᵥ φ ∈ T.originFunctions n r src g,
      hR, hQd, hd : d.det ∣ T.sqrtPrime ^ (Fintype.card X * ∑ δ ∈ range x,
        finrank (ResidueField O) ((T.map (residue O)).deepForms k n r (δ + 1)))⟩ :=
    T.exists_originFunctions_factorization_det_dvd h_surj hx
  have h_count :
      ∑ δ ∈ range x, finrank (ResidueField O) ((T.map (residue O)).deepForms k n r (δ + 1)) ≤
        ⌊T.divisorConstant k n r * Fintype.card (Exponents N k n)⌋₊ :=
    Nat.le_floor <| by
      simpa only [Nat.cast_sum, Fintype.card_fun, ZMod.card, Nat.cast_pow, divisorConstant_map]
        using
        (T.map (residue O)).sum_finrank_deepForms_le n h_large.block_pos h_large.two_mul_block_le x
  have h_range : Q.mulVecLin.range = T.originFunctions n r src g :=
    le_antisymm (Set.range_subset_iff.2 hQ)
      fun ψ hψ ↦ ⟨R *ᵥ ψ, T.mulVec_mulVec_eq_self_of_mem_originFunctions hR hQd hψ⟩
  exact ⟨Q, R, d, h_range, hR, hQd, hd.trans (pow_dvd_pow _ (Nat.mul_le_mul_left _ h_count))⟩

omit [IsDomain O] [ValuationRing O] [CharZero O] in
variable {T} in
/-- The sums over the edges nearly fill the target of `Add = pairingMap u b Q'`. Let `T` be a
Frobenius cycle with `N` letters and prime `p`, and `c₀ = T.multinomialExponent k`. Forms are given
by their coefficients, indexed by `Exponents N k n`, and the weights `b` pair forms, with
`b * b' = p ^ (N c₀)` (`hb`). Let `Ed` be the set of edges and `u e` an invertible matrix on `O ^ H`
for each edge `e`. The columns of `Q'`, indexed by `ι`, are functions from `H × Ed` to forms, and
`R'` is a left inverse of `Q'`. The map `nearInverse u 1 b' R'` applies `R'ᵀ` and then, at each
edge, `(u e)⁻¹` on `O ^ H` and multiplication by `b'` on forms. It is a right inverse of `Add` up to
the factor `p ^ (N c₀)`. -/
lemma IsEdgePairing.pairingMap_mul_nearInverse_one {H Ed ι : Type*} [Fintype H] [DecidableEq H]
    [Fintype Ed] [DecidableEq Ed] [DecidableEq ι] {b b' : Exponents N k n → O}
    (hb : T.IsEdgePairing b b') (u : Ed → GL H O) {Q' : Matrix ((H × Ed) × Exponents N k n) ι O}
    {R' : Matrix ι ((H × Ed) × Exponents N k n) O} (hR' : R' * Q' = 1) :
    pairingMap u b Q' * nearInverse u 1 b' R' =
      (T.p : O) ^ (N * T.multinomialExponent k) • (1 : Matrix ι ι O) := by
  ext i j
  set a : O := (T.p : O) ^ (N * T.multinomialExponent k)
  calc (pairingMap u b Q' * nearInverse u 1 b' R') i j
      = ∑ x : H × Ed, (fun β : Exponents N k n ↦ Q' (x, β) i) ⬝ᵥ
          (b * (b' * fun β : Exponents N k n ↦ R' j (x, β))) := by
        simp only [pairingMap_mul_nearInverse_apply, one_mulVec]
    _ = ∑ x : H × Ed, a * ∑ β : Exponents N k n, R' j (x, β) * Q' (x, β) i := by
        refine sum_congr rfl fun x _ ↦ ?_
        rw [hb.pairing_mul_eq_pow_mul_dotProduct, dotProduct_comm, dotProduct]
    _ = a * (R' * Q') j i := by rw [mul_apply, Fintype.sum_prod_type (α₁ := H × Ed), mul_sum]
    _ = (a • (1 : Matrix ι ι O)) i j := by simp [hR', one_apply, eq_comm]

/-- A near inverse. Let `T` be a Frobenius cycle with `N` letters and prime `p = w ^ 2`, `k` the
rank, `n` the degree and `c₀ = T.multinomialExponent k`. The weights `b` pair forms, with
`b * b' = p ^ (N c₀)` (`hb`). Let `M = T.allEdgesForms k n r` be the module of forms that lie in the
halfway lattices of all edges from a lattice, where `r` is the size of the first block of the
parahoric subgroup. Let `C, S, Av` be conditions on an edge of precision `c` (`hC`). Only one of
their properties is used, which involves neither `C`, `S` nor `θ`: the matrix `Av`, paired against
`M`, is multiplication by `p ^ (N c₀)` modulo `w ^ c`. Let `Ed` be the set of edges and `u e` an
invertible matrix on `O ^ H` for each edge `e`. Let the columns of `Q'`, indexed by `ι`, be
functions from `H × Ed` to forms with all values in `M` (`hQ'`), and let `R'` be a left inverse of
`Q'`.
The map `Add = pairingMap u b Q'` sends a function on edges to its pairings with these columns, by
`u e` on `O ^ H` and by `b` on forms. The map `Inv = nearInverse u Av b' R'` applies `R'ᵀ` and then,
at each edge, `(u e)⁻¹` on `O ^ H` and multiplication by `b'` followed by `Av` on forms. Then
`Add * Inv ≡ p ^ (2 N c₀)` modulo `w ^ c`, entry by entry. -/
lemma IsEdgeCondition.pow_dvd_mul_sub_smul_one {N k n : ℕ} {W O : Type} [NeZero N] [CommRing W]
    [IsLocalRing W] [CommRing O] [IsDomain O] [ValuationRing O] {T : FrobeniusCycle N W O}
    {H Ed ι : Type*} [Fintype H] [DecidableEq H]
    [Fintype Ed] [DecidableEq Ed] [Fintype ι] [DecidableEq ι] {r c : ℕ} {θ : ℝ}
    {b b' : Exponents N k n → O} {C : Submodule O (Exponents N k n → O)}
    {S : Submodule (ResidueField O) (Exponents N k n → ResidueField O)}
    {Av : Matrix (Exponents N k n) (Exponents N k n) O} (hC : T.IsEdgeCondition r c θ b C S Av)
    (hb : T.IsEdgePairing b b') (u : Ed → GL H O) {Q' : Matrix ((H × Ed) × Exponents N k n) ι O}
    {R' : Matrix ι ((H × Ed) × Exponents N k n) O} (hR' : R' * Q' = 1)
    (hQ' : Q'.mulVecLin.range ≤ valuedIn (H × Ed) (T.allEdgesForms k n r)) (i j : ι) :
    T.sqrtPrime ^ c ∣ (pairingMap u b Q' * nearInverse u Av b' R' -
      (T.p : O) ^ (2 * (N * T.multinomialExponent k)) • (1 : Matrix ι ι O)) i j := by
  -- Write `p ^ (2 N c₀)` as `a = p ^ (N c₀)` times the product with `1` in place of `Av`. Both
  -- terms are sums over the edges; at each edge the congruence is that of `Av`.
  let a : O := (T.p : O) ^ (N * T.multinomialExponent k)
  let col (x : H × Ed) : Exponents N k n → O := fun β ↦ Q' (x, β) i
  let row (x : H × Ed) : Exponents N k n → O := b' * fun β ↦ R' j (x, β)
  have h_scalar : (T.p : O) ^ (2 * (N * T.multinomialExponent k)) • (1 : Matrix ι ι O) =
      a • (pairingMap u b Q' * nearInverse u 1 b' R') := by
    rw [hb.pairingMap_mul_nearInverse_one u hR', two_mul, pow_add, mul_smul]
  have h_entry : (pairingMap u b Q' * nearInverse u Av b' R' -
        a • (pairingMap u b Q' * nearInverse u 1 b' R')) i j =
      ∑ x : H × Ed, (col x ⬝ᵥ (b * Av *ᵥ row x) - a * col x ⬝ᵥ (b * row x)) := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, pairingMap_mul_nearInverse_apply, one_mulVec,
      smul_eq_mul, mul_sum, sum_sub_distrib, col, row]
  have h_col : Q'.col i ∈ valuedIn (H × Ed) (T.allEdgesForms k n r) :=
    hQ' ⟨Pi.single i 1, by simp⟩
  rw [h_scalar, h_entry]
  exact dvd_sum fun x _ ↦ hC.pow_dvd_pairing_average (row x) (col x) (mem_valuedIn.1 h_col x)

end ValuationRing

/-- Few further generators for the image of a pairing matrix. Let `O` be a valuation domain of
characteristic zero and `T` a Frobenius cycle with `N` letters for `W` and `O`, whose prime
`p = w ^ 2`, `w = T.sqrtPrime`, is not a unit of `O`. Let `k ≥ 2` be the rank, `n` the degree and
`c₀ = T.multinomialExponent k`. A form is given by its coefficients, which are indexed by
`New.Exponents N k n`. The data are the following.
* The weights `b` pair forms by `(h, h') ↦ h' ⬝ᵥ (b * h)`, and `b * b' = p ^ (N c₀)` (`hb`).
* The module `C` of forms describes conditions modulo `w ^ c`, `c = 5 N c₀`, on the value of a
  function at an edge, and the averaging map `Av` has values in `C`. The space `S` over the residue
  field contains the reductions of the `h` with `w ^ (c - 1) • h ∈ C`, and `θ` bounds its dimension
  (`hC`, see `New.FrobeniusCycle.IsEdgeCondition`).
* A vector indexed by `(H × Ed) × exponents` is a function from `H × Ed` to forms, where `Ed` is
  the set of edges and `H` indexes a basis of the coefficient module. The columns of `Q` and `Q'`
  are such functions, indexed by `V × exponents` for a finite set `V` (the origins of the edges).
  Both matrices have left inverses, and their images have values in `T.allEdgesForms k n r`, the
  forms in the halfway lattices of all edges from a lattice.
* The number `|H × Ed|` is `|V|` times the index of the parahoric subgroup with blocks `r` and
  `k - r`.

The matrix `pairingMap u b Q' * Q` pairs the columns of `Q` with those of `Q'`, by `u e` on `O ^ H`
at the edge `e` and by `b` on forms. Then `p ^ (2 N c₀) O ^ (V × exponents)` lies in the span of its
image and of at most `θ |V × exponents|` further vectors. -/
lemma IsEdgeCondition.exists_finset_smul_top_le_range_sup_span {N k n : ℕ} {W O : Type} [NeZero N]
    [CommRing W] [IsLocalRing W] [CommRing O] [IsDomain O] [ValuationRing O] [CharZero O]
    {T : FrobeniusCycle N W O} (hp : ¬IsUnit (T.p : O)) {r : ℕ} {θ : ℝ}
    (hk : 2 ≤ k) {b b' : Exponents N k n → O} {C : Submodule O (Exponents N k n → O)}
    {S : Submodule (ResidueField O) (Exponents N k n → ResidueField O)}
    {Av : Matrix (Exponents N k n) (Exponents N k n) O}
    (hC : T.IsEdgeCondition r (T.congruencePrecision k) θ b C S Av) (hb : T.IsEdgePairing b b')
    {V H Ed : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] [Fintype Ed]
    [DecidableEq Ed] (u : Ed → GL H O)
    {Q Q' : Matrix ((H × Ed) × Exponents N k n) (V × Exponents N k n) O}
    {R R' : Matrix (V × Exponents N k n) ((H × Ed) × Exponents N k n) O}
    (hR : R * Q = 1) (hR' : R' * Q' = 1)
    (hQ : Q.mulVecLin.range ≤ valuedIn (H × Ed) (T.allEdgesForms k n r))
    (hQ' : Q'.mulVecLin.range ≤ valuedIn (H × Ed) (T.allEdgesForms k n r))
    (h_card : Fintype.card (H × Ed) = Fintype.card V * (parahoric W (twoBlock k r)).index) :
    ∃ s : Finset (V × Exponents N k n → O),
      (#s : ℝ) ≤ θ * (Fintype.card V * Fintype.card (Exponents N k n)) ∧
      (T.p : O) ^ (2 * (N * T.multinomialExponent k)) •
          (⊤ : Submodule O (V × Exponents N k n → O)) ≤
        (pairingMap u b Q' * Q).mulVecLin.range ⊔ span O (s : Set (V × Exponents N k n → O)) := by
  -- Apply `exists_finset_card_le_smul_top_le_sup_span` to the pairing map and its near inverse, and
  -- bound the number of generators by the dimension of `S`.
  let c : ℕ := T.congruencePrecision k
  let c₂ : ℕ := 2 * (N * T.multinomialExponent k)
  -- `O` need not be discrete, so the threshold is `w ^ (c - 1)`; it has to exceed `p ^ c₂`.
  have h_precision : (T.p : O) ^ c₂ * T.sqrtPrime ∣ T.sqrtPrime ^ (c - 1) := by
    have hc : 2 * c₂ + 1 ≤ c - 1 := by
      have h_two : 2 ≤ N * T.multinomialExponent k := T.two_le_mul_multinomialExponent hk
      grind [congruencePrecision]
    rw [← T.sqrtPrime_sq, ← pow_mul, ← pow_succ]
    exact pow_dvd_pow _ hc
  have h_near (i j : V × Exponents N k n) :
      T.sqrtPrime ^ (c - 1) ∣ (pairingMap u b Q' * nearInverse u Av b' R' - (T.p : O) ^ c₂ •
        (1 : Matrix (V × Exponents N k n) (V × Exponents N k n) O)) i j :=
    (pow_dvd_pow _ (Nat.sub_le c 1)).trans (hC.pow_dvd_mul_sub_smul_one hb u hR' hQ' i j)
  have hQ_cond : Q.mulVecLin.range ≤ valuedIn (H × Ed) C :=
    hQ.trans (iInf_mono fun _ ↦ Submodule.comap_mono hC.allEdgesForms_le)
  have hInv_cond : (nearInverse u Av b' R').mulVecLin.range ≤ valuedIn (H × Ed) C := by
    rintro _ ⟨η, rfl⟩
    refine mem_valuedIn.2 fun e ↦ ?_
    rw [mulVecLin_apply, nearInverse, ← mulVec_mulVec, edgewise_mulVec, ← mulVec_mulVec]
    exact hC.average_mem _
  obtain ⟨s, hs_card : Fintype.card (V × Exponents N k n) + #s ≤
        Fintype.card (H × Ed) * finrank (ResidueField O) S,
      hs_span⟩ :=
    exists_finset_card_le_smul_top_le_sup_span hR (T.sqrtPrime_mem_maximalIdeal hp) h_precision
      h_near hQ_cond hInv_cond hC.residue_mem
  refine ⟨s, ?_, hs_span⟩
  have h_count : (Fintype.card V * Fintype.card (Exponents N k n) + #s : ℝ) ≤
      Fintype.card V * ((parahoric W (twoBlock k r)).index * finrank (ResidueField O) S) := by
    rw [h_card, Fintype.card_prod, mul_assoc] at hs_card
    exact_mod_cast hs_card
  -- `dim S` times the index is at most `1 + θ` times the number of monomials.
  linarith [mul_le_mul_of_nonneg_left hC.index_mul_finrank_le (Fintype.card V).cast_nonneg]

/-- The elementary divisors of the operator factored through the functions on edges. Let `T` be a
Frobenius cycle with `N` letters whose prime `p = T.p` is not a unit of `O`. Forms have `k`
variables and degree `n` in each letter, and their monomials are indexed by `Exponents N k n`. Let
the degree be large for the size `r` of the first block and the proportion `θ ∈ (0, 1]` of
exceptional elementary divisors. Let `Ed` be a finite set of edges, let `H` index a basis of the
free module `O ^ H` of coefficients, and let `V` be a finite set of origins. A pair `e ∈ H × Ed` has
the origin `src e ∈ V` with basis change `g e`, and for the dual edge the origin `src' e ∈ V` with
basis change `g' e`. On both sides every pair of a point of `V` and a coset of the parahoric
subgroup of `GL_k(W)` with blocks `r` and `k - r` occurs, and there are no more pairs than that. The
weights `b` pair forms, with `b * b' = p ^ (N c₀)` for `c₀ = T.multinomialExponent k` (`hb`), and
`u` assigns to each edge an invertible matrix on `O ^ H`. Let `A` be the restriction to edges,
followed by the pairing with the functions restricted to the dual edges. Then the image of `A` plus
`p ^ m O ^ (V × exponents)` has colength dividing `p ^ l` (`New.ColengthDvd`) with `l` at most
`3 c_div + θ m` times `|V × exponents|`, where `c_div = T.divisorConstant k n r`. -/
lemma exists_colengthDvd_range_pairingMap_mul_edgeRestriction {N k n : ℕ} {W O : Type} [NeZero N]
    [CommRing W] [IsLocalRing W] [CommRing O] [IsDomain O] [ValuationRing O] [CharZero O]
    (T : FrobeniusCycle N W O) (hp : ¬IsUnit (T.p : O)) {r : ℕ} {θ : ℝ}
    (h_large : T.IsLargeDegree k n r θ) {b b' : Exponents N k n → O} (hb : T.IsEdgePairing b b')
    {V H Ed : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] [Fintype Ed]
    [DecidableEq Ed] {src src' : H × Ed → V} {g g' : H × Ed → GL (Fin k) W} (u : Ed → GL H O)
    (h_origin : Surjective fun e : H × Ed ↦ ((src e, ↑(g e)⁻¹) : V × ParahoricCosets W k r))
    (h_dual : Surjective fun e : H × Ed ↦ ((src' e, ↑(g' e)⁻¹) : V × ParahoricCosets W k r))
    (h_card : Fintype.card (H × Ed) = Fintype.card V * (parahoric W (twoBlock k r)).index) (m : ℕ) :
    ∃ l : ℕ,
      l ≤ (3 * T.divisorConstant k n r + θ * m) *
        (Fintype.card V * Fintype.card (Exponents N k n)) ∧
      ColengthDvd ⊤
        ((pairingMap u b (T.edgeRestriction n r src' g') *
          T.edgeRestriction n r src g).mulVecLin.range ⊔ (T.p : O) ^ m • ⊤) ((T.p : O) ^ l) := by
  let c₂ : ℕ := 2 * (N * T.multinomialExponent k)
  obtain ⟨C, S, Av, hC : T.IsEdgeCondition r (T.congruencePrecision k) θ b C S Av⟩ :=
    T.exists_isEdgeCondition hp h_large hb
  -- The two ends have small colength: the columns of `Q` and `Q'` are bases of the functions that
  -- depend only on the origin, for the edges and for the dual edges. Between them lie few further
  -- generators, and the colengths add along `d'ᵀ * (pairingMap u b Q' * Q) * d`.
  let D : ℕ := ⌊T.divisorConstant k n r * Fintype.card (Exponents N k n)⌋₊
  have hD : (D : ℝ) ≤ T.divisorConstant k n r * Fintype.card (Exponents N k n) :=
    Nat.floor_le (mul_nonneg (T.divisorConstant_nonneg k n r) (Nat.cast_nonneg _))
  obtain ⟨Q, R, d, hQ : Q.mulVecLin.range = T.originFunctions n r src g, hR : R * Q = 1,
      hQd : Q * d = T.edgeRestriction n r src g,
      hd : d.det ∣ T.sqrtPrime ^ (Fintype.card V * D)⟩ := h_large.exists_basis_det_dvd hp h_origin
  obtain ⟨Q', R', d', hQ' : Q'.mulVecLin.range = T.originFunctions n r src' g', hR' : R' * Q' = 1,
      hQd' : Q' * d' = T.edgeRestriction n r src' g',
      hd' : d'.det ∣ T.sqrtPrime ^ (Fintype.card V * D)⟩ := h_large.exists_basis_det_dvd hp h_dual
  have h_ends : d'ᵀ.det * d.det ∣ (T.p : O) ^ (Fintype.card V * D) := by
    rw [det_transpose, ← T.sqrtPrime_sq, ← pow_mul, two_mul, pow_add]
    exact mul_dvd_mul hd' hd
  obtain ⟨s, hs : (#s : ℝ) ≤ θ * (Fintype.card V * Fintype.card (Exponents N k n)), hs_span⟩ :=
    hC.exists_finset_smul_top_le_range_sup_span hp h_large.two_le_rank hb u hR hR'
      (fun ψ hψ ↦ mem_valuedIn.2 (T.apply_mem_allEdgesForms h_origin (hQ.le hψ)))
      (fun ψ hψ ↦ mem_valuedIn.2 (T.apply_mem_allEdgesForms h_dual (hQ'.le hψ))) h_card
  have h_loss : (c₂ : ℝ) ≤ 2 * T.divisorConstant k n r := by
    simpa [c₂] using h_large.mul_multinomialExponent_le_divisorConstant
  refine ⟨Fintype.card V * D + (c₂ * Fintype.card (V × Exponents N k n) + m * #s), ?_, ?_⟩
  · push_cast [Fintype.card_prod]
    calc (Fintype.card V * D +
          (c₂ * (Fintype.card V * Fintype.card (Exponents N k n)) + m * #s) : ℝ)
        ≤ Fintype.card V * (T.divisorConstant k n r * Fintype.card (Exponents N k n)) +
            (2 * T.divisorConstant k n r * (Fintype.card V * Fintype.card (Exponents N k n)) +
              m * (θ * (Fintype.card V * Fintype.card (Exponents N k n)))) := by gcongr
      _ = (3 * T.divisorConstant k n r + θ * m) *
            (Fintype.card V * Fintype.card (Exponents N k n)) := by ring
  · have h_factor :
        pairingMap u b (T.edgeRestriction n r src' g') * T.edgeRestriction n r src g =
          d'ᵀ * (pairingMap u b Q' * Q) * d := by
      simp only [pairingMap, ← hQd, ← hQd', transpose_mul, Matrix.mul_assoc]
    rw [h_factor]
    refine (colengthDvd_mul_mul_of_smul_top_le d'ᵀ _ d hs_span (T.p ^ m)).of_dvd ?_
    -- The bound is the product of two determinants, `p ^ c₂` for each dimension and `p ^ m` for
    -- each element of `s`.
    rw [pow_add _ (Fintype.card V * D)]
    calc d'ᵀ.det * (((T.p : O) ^ c₂) ^ Fintype.card (V × Exponents N k n) *
          (d.det * ((T.p : O) ^ m) ^ #s))
        = d'ᵀ.det * d.det * (T.p : O) ^ (c₂ * Fintype.card (V × Exponents N k n) + m * #s) := by
          ring
      _ ∣ _ := mul_dvd_mul_right h_ends _

/-! ### The theorem -/

/-- Every pair of a representative `x` and a coset of the parahoric subgroup is the origin and the
coset of the inverse transposed basis change of an edge of `𝓔`: this map is injective on a finite
set, hence onto. -/
lemma _root_.New.EdgeCoordinates.surjective_origin_originBasisChange {k : ℕ} {W O : Type}
    [CommRing W]
    [IsLocalRing W] [CommRing O] {r : ℕ} {X H : Type*} [Finite X] [Fintype H] [DecidableEq H]
    [Finite (ParahoricCosets W k r)] (𝓔 : EdgeCoordinates W O k r X H) :
    Surjective fun e : X × ParahoricCosets W k r ↦
      ((𝓔.origin e, ↑(transposeGL (𝓔.originBasisChange e))⁻¹) : X × ParahoricCosets W k r) := by
  refine Finite.surjective_of_injective fun e e' h ↦ ?_
  obtain ⟨h_origin, h_coset⟩ := Prod.mk.inj h
  exact 𝓔.eq_of_origin_eq e e' h_origin (by simpa only [inv_inv] using QuotientGroup.eq.1 h_coset)

/-- The theorem on elementary divisors. Let `O` be a valuation domain of characteristic zero and `T`
a Frobenius cycle with `N` letters, prime `p = T.p` and power `P = T.P` of `p`, so that the residue
field of `W` has `q = T.q = P ^ N` elements. Let `k` be the rank and `n` the degree in each letter,
and let `J` split the index set `I` into exponents and `H`. Let `p` be a non-unit of `O`, and let
`Y ∘ f = f ∘ A` for the edge Hecke operator `A` of the edges `𝓔` between the representatives `X`.
Let `0 < r ≤ k / 2`, `0 < θ ≤ 1`, `q ≥ n ^ 4` and `n ≥ (N k log q / θ) ^ 5 P ^ (3 r)`. Then `Y`
keeps the image `L` of `f`, and for every `m` the colength of `Y L + p ^ m L` in `L` divides `p ^ l`
for some `l ≤ (3 c_div + θ m) |X| |I|`, with `c_div = T.divisorConstant k n r`. -/
theorem elementary_divisors {N k n : ℕ} {W O : Type} [NeZero N] [CommRing W] [IsLocalRing W]
    [CommRing O] [IsDomain O] [ValuationRing O] [CharZero O] (T : FrobeniusCycle N W O)
    {X : Type*} [Fintype X] (hp : ¬IsUnit (T.p : O)) {r : ℕ} {θ : ℝ}
    (h_large : T.IsLargeDegree k n r θ) {H : Type*} {I M : Type} [Fintype H] [DecidableEq H]
    [Fintype (ParahoricCosets W k r)] [Fintype I] [AddCommGroup M] [Module O M]
    (J : I ≃ Exponents N k n × H) (𝓔 : EdgeCoordinates W O k r X H) (f : (X → I → O) →ₗ[O] M)
    {Y : End O M} (hY : Y ∘ₗ f = f ∘ₗ T.edgeHeckeOperator n J 𝓔) (m : ℕ) :
    IsOntoUpToColength (T.p : O) f.range m Y
      ((3 * T.divisorConstant k n r + θ * m) * (Nat.card X * Nat.card I)) := by
  classical
  have hY_apply (F : X → I → O) : Y (f F) = f (T.edgeHeckeOperator n J 𝓔 F) :=
    LinearMap.congr_fun hY F
  obtain ⟨b, b', hb⟩ := T.exists_isEdgePairing (k := k) hp h_large.degree_lt_q
  -- Every pair of a point of `H × X` and a coset occurs among the edges, and by construction
  -- also among the dual edges.
  have h_origin : Surjective fun e : H × X × ParahoricCosets W k r ↦
      ((Prod.map id 𝓔.origin e, ↑(transposeGL (𝓔.originBasisChange e.2))⁻¹) :
        (H × X) × ParahoricCosets W k r) :=
    (Equiv.prodAssoc H X _).symm.surjective.comp
      (surjective_id.prodMap 𝓔.surjective_origin_originBasisChange)
  have h_dual : Surjective fun e : H × X × ParahoricCosets W k r ↦
      ((Prod.map id Prod.fst e, ↑(𝓔.terminusBasisChange e.2.2)⁻¹) :
        (H × X) × ParahoricCosets W k r) :=
    fun q ↦ ⟨Equiv.prodAssoc H X _ q, Prod.ext rfl (𝓔.mk_terminusBasisChange_inv q.2)⟩
  let A : Matrix ((H × X) × Exponents N k n) ((H × X) × Exponents N k n) O :=
    pairingMap 𝓔.transition b (T.edgeRestriction n r (Prod.map id Prod.fst)
        (𝓔.terminusBasisChange ∘ Prod.snd ∘ Prod.snd)) *
      T.edgeRestriction n r (Prod.map id 𝓔.origin)
        fun e : H × X × ParahoricCosets W k r ↦ transposeGL (𝓔.originBasisChange e.2)
  obtain ⟨l, hl,
      h_colength : ColengthDvd ⊤ (A.mulVecLin.range ⊔ (T.p : O) ^ m • ⊤) ((T.p : O) ^ l)⟩ :=
    T.exists_colengthDvd_range_pairingMap_mul_edgeRestriction hp h_large hb 𝓔.transition h_origin
      h_dual
      (by simp only [Fintype.card_prod, Subgroup.index, Nat.card_eq_fintype_card, mul_assoc]) m
  -- Carry the colength along `f`; the factored operator is `Y` on vectors multiplied by `b`.
  let π : ((H × X) × Exponents N k n → O) →ₗ[O] M := f ∘ₗ regroup J
  have h_range : Submodule.map π ⊤ = f.range := by
    simp [π, LinearMap.range_comp, LinearMap.range_eq_top.2 (regroup_surjective J)]
  refine ⟨?_, l, hl.trans_eq ?_, h_colength.map π (le_sup_of_le_left h_range.ge) ?_⟩
  · rintro _ ⟨_, ⟨F, rfl⟩, rfl⟩
    exact ⟨T.edgeHeckeOperator n J 𝓔 F, (hY_apply F).symm⟩
  · simp only [Nat.card_eq_fintype_card, Fintype.card_congr J, Fintype.card_prod, Nat.cast_mul]
    ring
  · rw [Submodule.map_sup, Submodule.map_pointwise_smul, h_range]
    refine sup_le_sup_right ?_ _
    rintro _ ⟨_, ⟨F, rfl⟩, rfl⟩
    refine ⟨_, ⟨regroup J fun y ↦ b y.2 * F y, rfl⟩, ?_⟩
    rw [hY_apply, hb.edgeHeckeOperator_regroup]
    simp only [π, A, LinearMap.comp_apply, mulVecLin_apply]

/-- The theorem on elementary divisors in terms of lengths. Let `O` be a discrete valuation ring of
characteristic zero and `T` a Frobenius cycle: a prime `p = T.p`, not a unit of `O`, a power
`P = T.P` of `p` and `N` ring maps `W → O` (the letters), where the residue field of `W` has
`q = P ^ N` elements. The points of `X` represent `W`-lattices of rank `k`, each with a free
`O`-module with basis indexed by `H`. The edges into `x ∈ X` are indexed by the cosets of the
parahoric subgroup of `GL_k(W)` with blocks `r` and `k - r`, and `𝓔` records their origins and basis
changes. The bijection `J` splits `I` into `H` and the exponents of the monomials with `k` variables
and degree `n` in each letter. The edge Hecke operator `A` on functions `X → O ^ I` sums, over the
edges into `x`, the values at their origins carried to `x`. Let `Y ∘ f = f ∘ A`, and let
`0 < r ≤ k / 2`, `0 < θ ≤ 1`, `n ^ 4 ≤ q` and `(N k log q / θ) ^ 5 P ^ (3 r) ≤ n` (`h_large`). Then
`Y` keeps the image `L` of `f`, and the length of `L / (Y L + p ^ m L)` (`New.relLength`) is at most
`l` times the length of `O / p`, for a natural number `l ≤ (3 c_div + θ m) |X| |I|` with
`c_div = T.divisorConstant k n r = N n (1 / P ^ (2 r) + r ^ 2 / (k P))`. This is a corollary of
`New.FrobeniusCycle.elementary_divisors`. -/
theorem elementary_divisors_length {N k n : ℕ} {W : Type} [NeZero N] [CommRing W] [IsLocalRing W]
    {X : Type*} [Fintype X] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] (T : FrobeniusCycle N W O) (hp : ¬IsUnit (T.p : O)) {r : ℕ} {θ : ℝ}
    (h_large : T.IsLargeDegree k n r θ) {H : Type*} {I M : Type} [Fintype H] [DecidableEq H]
    [Fintype (ParahoricCosets W k r)] [Fintype I] [AddCommGroup M] [Module O M]
    (J : I ≃ Exponents N k n × H) (𝓔 : EdgeCoordinates W O k r X H) (f : (X → I → O) →ₗ[O] M)
    {Y : End O M} (hY : Y ∘ₗ f = f ∘ₗ T.edgeHeckeOperator n J 𝓔) (m : ℕ) :
    f.range.map Y ≤ f.range ∧
    ∃ l : ℕ, l ≤ (3 * T.divisorConstant k n r + θ * m) * (Nat.card X * Nat.card I) ∧
      relLength f.range (f.range.map Y ⊔ (T.p : O) ^ m • f.range) ≤
        l * length O (O ⧸ span {(T.p : O)}) := by
  have h_onto : IsOntoUpToColength (T.p : O) f.range m Y
      ((3 * T.divisorConstant k n r + θ * m) * (Nat.card X * Nat.card I)) :=
    T.elementary_divisors hp h_large J 𝓔 f hY m
  exact ⟨h_onto.left, h_onto.exists_relLength_le (Submodule.fg_range f)⟩

end FrobeniusCycle

end New

end
