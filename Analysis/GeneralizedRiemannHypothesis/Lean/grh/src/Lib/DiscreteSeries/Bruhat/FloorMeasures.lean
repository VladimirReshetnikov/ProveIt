import Lib.DiscreteSeries.Bruhat.FloorGroups
import Lib.General.Measure.IntegralOperators
import Lib.General.Measure.QuadricDisintegration

/-!
# Heisenberg elements, measures of the floors, hyperbolic bases and Plancherel at a place

Algebra and measure theory on the unitary group `G` of the form `New.Shape.Form.splitGram T`, first
over a ring with involution and a `τ` of trace one, then over a place `A` (`New.Floors.Place`),
along its floors. The basis is `e_a`, a middle block, `e*_a` (`a < ϱ`). `V_l` is spanned by the
basis vectors of floor at least `l`: for `l ≤ ϱ`, the middle block and the pairs with `l ≤ a`. `h`
is the form. The frame `f_0, …, f_ϱ` (`New.Shape.besselFrame`) is `e_0, …, e_(ϱ-1)` followed by
the last vector `z` of the middle block.

In `New.Floors.FloorGroups`, the groups `floorGroup`, `unipotentBelow`, `floorUnipotent` and
`partialUnitriangularGroup` are `G_l = U(V_l)`, `N_(<l)`, `N_l = G_l ∩ N_(<l+1)` and `Q_l`. The
group `Q_l` consists of the elements unitriangular on the first `l` frame vectors, for `l ≤ ϱ + 1`.

`∗ₘ` is convolution of measures, so `μ ∗ₘ dirac s` is the right translate of `μ` by `s`.

* `New.Floors.TraceOne.heisenbergElem`, `New.Floors.FloorGroups.exists_eq_heisenbergElem_of_mem`:
  `N_a` is a Heisenberg group, given by Eichler maps.
* `New.Floors.FloorGroups.bijOn_mulVec_eStar`: `u ↦ u e*_a` maps `N_a` bijectively onto the
  isotropic vectors `y` of `V_a` with `h(e_a, y) = 1`.
* `New.Floors.FloorGroups.existsUnique_prod_of_mem_besselU`: an element of `N_(<ϱ)` is a product in
  `N_0 ⋯ N_(ϱ-1)` with unique factors.
* `New.Floors.Place.heisenbergMeasure`, `New.Floors.ascConv`: invariant measures on `N_l` and, by
  convolution, on `N_(<j)`.
* `New.Floors.HyperbolicBasis`, `New.Floors.HyperbolicBasis.floorQuadricMeasure`: hyperbolic bases
  of `V_ϱ` and `V_b`, and measures on quadrics in `V_b`, which disintegrate the Haar measure
  (`New.Floors.HyperbolicBasis.isDisintegration_floorVolume`).
* `New.Floors.Place.plancherel_inequality`: Plancherel's inequality on `A ^ ι`.

Notions from other files:
* `New.SplitIndex`: The index set made of ϱ indices, a middle set μ, and ϱ further indices, as a
  disjoint union.
* `New.Shape.Form.splitGram`: The Gram matrix of ϱ hyperbolic planes and a middle space with Gram
  matrix T: identity blocks pair the first and last ϱ indices, T is the middle block, all else is
  zero.
* `New.Floors.FloorGroups.floorOf`: The floor of a basis index: `a` for `e_a` and `e*_a`, `ϱ` for
  `z`, `ϱ + 1` for the other middle indices.
* `New.inclMatrix`: For a map u: m → n of index sets, the n×m matrix whose j-th column is the
  standard basis vector e_{u(j)}.

## Relation to the literature

Known; see `Lib.DiscreteSeries.Bruhat.ComplexPlace` for sources.
-/

noncomputable section

namespace New.Floors

open Matrix MeasureTheory Measure Sum Function ENNReal Fintype FloorGroups Filter TraceOne Place U
  Subgroup

variable {A : Type} [CommRing A] [StarRing A] {𝔰 : Shape} {l : ℕ}

namespace FloorGroups

variable [TraceOne A] {T : 𝔰.Form A} (a : Fin 𝔰.ϱ)
  {g s : T.G} [H : IsHermitianUnit T.splitGram]
  (p q : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) × skewAdjoint A)

/-! ### The Heisenberg groups of the floors and the Bessel subgroup -/

/-- The isometry ν(v, β) of floor a: the Eichler transformation with
e*_a ↦ e*_a + v + (β − τh(v,v))e_a, for β skew. Here v is a vector of the floors at least a + 1,
extended by zero. -/
def _root_.New.Floors.TraceOne.heisenbergElem : U T.splitGram :=
  let v := inclMatrix A (↑) *ᵥ p.1
  U.of H.2
      (eichlerMap T.splitGram (Pi.single (inl a) 1) (-v)
        (element * star v ⬝ᵥ T.splitGram *ᵥ v - p.2)) <| by
    -- The Eichler map is unitary: `e_a` is isotropic and orthogonal to `v`, and the parameter has
    -- trace `h(v, v)` because `τ + star τ = 1` and `p.2` is skew.
    have h_trace : element * star v ⬝ᵥ T.splitGram *ᵥ v - p.2 +
        star (element * star v ⬝ᵥ T.splitGram *ᵥ v - (p.2 : A)) =
          star (-v) ⬝ᵥ T.splitGram *ᵥ (-v) := by
      simp [IsHermitianUnit.conjTranspose_eq, ↓ star_dotProduct_mulVec_comm, mulVec_neg]
      grind
    obtain ⟨e, he⟩ :=
      exists_unitary_eq_eichlerMap (x := Pi.single (inl a) 1) H.conjTranspose_eq (by simp)
        (by simp [v, inclMatrix_val_mulVec]) h_trace
    rw [← he]
    exact e.2

/-- The Heisenberg element ν(v, β) sends w to w + w(e*_a)v + ((β − τh(v, v))w(e*_a) − h(v, w))e_a.
Here w(e*_a) is the e*_a coordinate of w, and v is the vector of floors at least a + 1, extended by
zero. -/
@[local simp ↓]
lemma heisenbergElem_mulVec (w : SplitIndex 𝔰.ϱ 𝔰.MiddleIndex → A) :
    let v := inclMatrix A (↑) *ᵥ p.1
    heisenbergElem (T := T) a p *ᵥ w =
      w + w (eStar a) • v +
        ((p.2 - element * star v ⬝ᵥ T.splitGram *ᵥ v) * w (eStar a) - star v ⬝ᵥ T.splitGram *ᵥ w) •
          Pi.single (inl a) 1 := by
  have h_coe : (heisenbergElem (T := T) a p).val.val =
      eichlerMap T.splitGram (Pi.single (inl a) 1) (-(inclMatrix A (↑) *ᵥ p.1))
        (element * star (inclMatrix A (↑) *ᵥ p.1) ⬝ᵥ T.splitGram *ᵥ inclMatrix A (↑) *ᵥ p.1 -
          p.2) := rfl
  have h_pair : star (Pi.single (inl a) (1 : A)) ⬝ᵥ T.splitGram *ᵥ w = w (eStar a) := by simp
  rw [h_coe, eichlerMap_mulVec, h_pair]
  simp only [star_neg, neg_dotProduct]
  module

/-- Let `A` have a trace-one element τ (τ + τ̄ = 1) and let `T.splitGram` be hermitian and
invertible. For a < ϱ, a vector v on the basis indices of floor at least a + 1 and a skew-adjoint β,
the Heisenberg element ν(v, β) of floor a lies in N_a = G_a ∩ N_(<a+1). Here ν(v, β) is the Eichler
transformation e*_a ↦ e*_a + v + (β − τh(v,v))e_a, and G_a is the group of isometries fixing every
basis vector of floor below a. -/
lemma heisenbergElem_mem_floorUnipotent : heisenbergElem (T := T) a p ∈ floorUnipotent a := by
  -- The matrix differs from `1` only in row `e_a` and in column `e*_a`, and the entries of `v`
  -- vanish on the floors at most `a`: compare the entries with those of `1`.
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · simp [mem_floorGroup, heisenbergElem, eichlerMap, vecMulVec, Pi.single_apply,
      inclMatrix_val_mulVec, sub_eq_zero, -mulVec_mulVec]
    grind [star_zero]
  · simp [mem_unipotentBelow, heisenbergElem, eichlerMap, vecMulVec, Pi.single_apply,
      inclMatrix_val_mulVec, BesselIndex.level, sub_eq_zero, -mulVec_mulVec]
    grind [star_zero]

variable {a p q}

/-- Let `s` lie in `G_{a+1}` (`floorGroup (a + 1)`), the group fixing the basis vectors of floor at
most a. Let ν(v, β) = `heisenbergElem a (v, β)` be the Heisenberg isometry of floor a, where v is a
vector on the floors at least a + 1 and β is skew-adjoint. Then s ν(v, β) = ν(sv, β) s, where sv is
the block of s on the floors at least a + 1 applied to v. -/
lemma mul_heisenbergElem (h : s ∈ floorGroup (a + 1)) :
    s * heisenbergElem a p =
      heisenbergElem a (s.val.val.toSquareBlockProp (a + 1 ≤ floorOf ·) *ᵥ p.1, p.2) * s := by
  -- `s` fixes `e_a`, keeps the form and acts on `V_(a+1)` by its block
  set v : 𝔰.BesselIndex → A := inclMatrix A (↑) *ᵥ p.1 with hv
  have h_block :
      inclMatrix A (↑) *ᵥ s.val.val.toSquareBlockProp (a + 1 ≤ floorOf ·) *ᵥ p.1 = s.val.val *ᵥ v :=
    inclMatrix_mulVec_floor_block a.2 h p.1
  have h_fix : s.val.val *ᵥ Pi.single (inl a) (1 : A) = Pi.single (inl a) 1 := by
    have h_point : orbitPoint a.castSucc s = Pi.single (𝔰.besselFrame a.castSucc) 1 :=
      (mem_partialUnitriangularGroup_succ_iff (by grind)).1
        (mem_partialUnitriangularGroup_of_mem_floorGroup h)
    simpa using orbitPoint_eq_iff.1 h_point
  have h_coord (w : 𝔰.BesselIndex → A) : (s.val.val *ᵥ w) (eStar a) = w (eStar a) := by
    simpa [h_fix, -mulVec_mulVec] using form_mulVec_mulVec s (Pi.single (inl a) 1) w
  ext : 2
  refine ext_iff_mulVec.2 fun w ↦ ?_
  simp [h_block, ← hv, ← mulVec_mulVec, mulVec_add, mulVec_smul, h_fix, h_coord, form_mulVec_mulVec]

/-- The Heisenberg group law: ν(v, β)ν(v', β') = ν(v + v', β + β' + (x − x̄)), where x = τh(v', v).
Here v and v' are vectors of the floors at least a + 1, extended by zero, β and β' are skew, h is
the form of the Gram matrix, and τ is the given element with τ + τ̄ = 1.

A special case of the composition law of Eichler–Siegel transformations on the unipotent radical of
an isotropic line's stabiliser, in matrix coordinates for one floor. -/
lemma heisenbergElem_mul :
    (heisenbergElem a p * heisenbergElem a q : T.G) =
      heisenbergElem a
        (p.1 + q.1,
          p.2 + q.2 +
            skewPart
              (element * star (inclMatrix A (↑) *ᵥ q.1) ⬝ᵥ T.splitGram *ᵥ inclMatrix A (↑) *ᵥ
                p.1)) := by
  set v : 𝔰.BesselIndex → A := inclMatrix A (↑) *ᵥ p.1 with hv
  set v' : 𝔰.BesselIndex → A := inclMatrix A (↑) *ᵥ q.1 with hv'
  -- apply both sides to a vector; the vectors `v`, `v'` and `e_a` have coordinate `0` at `e*_a`
  have hv_coord : v (eStar a) = 0 := by simp [v, inclMatrix_val_mulVec]
  have hv'_coord : v' (eStar a) = 0 := by simp [v', inclMatrix_val_mulVec]
  have h_orth : star v ⬝ᵥ T.splitGram *ᵥ Pi.single (inl a) 1 = 0 := by
    simp [v, inclMatrix_val_mulVec]
  have h_star : star (star v' ⬝ᵥ T.splitGram *ᵥ v) = star v ⬝ᵥ T.splitGram *ᵥ v' :=
    star_dotProduct_mulVec_comm IsHermitianUnit.conjTranspose_eq v' v
  ext : 2
  refine ext_iff_mulVec.2 fun w ↦ ?_
  simp [← hv, ← hv', ← mulVec_mulVec, mulVec_add, mulVec_smul, hv_coord, hv'_coord, h_star]
  rw [eq_sub_of_add_eq' (element_add_star (A := A))]
  module

/-- An isotropic vector w that vanishes on the floors below a and has coordinate 1 at e*_a is
ν(v, β)e*_a for some Heisenberg element ν(v, β) of floor a. -/
lemma exists_heisenbergElem_mulVec_eq {w : 𝔰.BesselIndex → A}
    (h_lower : ∀ j : 𝔰.BesselIndex, floorOf j < a → w j = 0) (h_top : w (eStar a) = 1)
    (h_isotropic : star w ⬝ᵥ T.splitGram *ᵥ w = 0) :
    ∃ p : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) × skewAdjoint A,
      w = (heisenbergElem (T := T) a p).val.val *ᵥ Pi.single (eStar a) 1 := by
  obtain ⟨v, d, rfl⟩ : ∃ (v : {j // a + 1 ≤ floorOf j} → A) (d : A), w = Pi.single (eStar a) 1 +
      inclMatrix A (fun j : {j // a + 1 ≤ floorOf j} ↦ j.1) *ᵥ v + d • Pi.single (inl a) 1 := by
    refine ⟨fun j ↦ w j, w (inl a), ?_⟩
    simp [funext_iff, Pi.single_apply, inclMatrix_val_mulVec] at h_lower ⊢
    grind
  -- isotropy determines `d + star d`, and the skew parameter supplies the rest of `d`
  have h_trace : d + star d = -(star (inclMatrix A (↑) *ᵥ v) ⬝ᵥ T.splitGram *ᵥ
      inclMatrix A (↑) *ᵥ v) := by
    simp [mulVec_add, mulVec_smul, inclMatrix_val_mulVec, -mulVec_mulVec] at h_isotropic
    grind
  use ⟨v, skewPart (star element * d)⟩
  have h_coef : star element * d - element * star d - element * star (inclMatrix A (↑) *ᵥ v) ⬝ᵥ
    T.splitGram *ᵥ
      inclMatrix A (↑) *ᵥ v = d := by
    grind
  simp [inclMatrix_val_mulVec, h_coef, -mulVec_mulVec]

/-- Let g lie in G_a and let i be the index of e_a or e*_a. If c times column i of g has coordinate
1 at e*_a, then it equals ν(v, β)e*_a for some Heisenberg element ν(v, β) of floor a. -/
lemma exists_col_eq_heisenbergElem (i : 𝔰.BesselIndex) (c : A) (h : g ∈ floorGroup a)
    (h_floor : floorOf i = a) (h_entry : g.val (eStar a) i * c = 1) :
    ∃ p : ({ i // a + 1 ≤ floorOf i } → A) × skewAdjoint A,
      g *ᵥ Pi.single i c = (heisenbergElem (T := T) a p).val.val *ᵥ Pi.single (eStar a) 1 := by
  set w : 𝔰.BesselIndex → A := g.val.val *ᵥ Pi.single i c
  -- `w` vanishes on the floors below `a`, has the entry `1` at `e*_a`, and is isotropic
  have lower (j : 𝔰.BesselIndex) (hj : floorOf j < a) : w j = 0 := by
    simp [w, apply_eq_one_apply_of_mem_floorGroup h j i (by grind),
      one_apply_ne (show j ≠ i by grind)]
  have top : w (eStar a) = 1 := by simpa [w, mul_comm] using h_entry
  have isotropic : star w ⬝ᵥ T.splitGram *ᵥ w = 0 := by
    have h_zero : star (Pi.single i c) ⬝ᵥ T.splitGram *ᵥ Pi.single i c = 0 := by
      simp [h_floor]
      grind [oppositeIndex_involutive_and_floorOf_level]
    exact (form_mulVec_mulVec g _ _).trans h_zero
  exact exists_heisenbergElem_mulVec_eq lower top isotropic

omit [TraceOne A] [IsHermitianUnit T.splitGram] in
/-- If g⁻¹s lies in Q_{a+1} ∩ G_a and ge*_a = se*_a, then g⁻¹s lies in G_{a+1}. -/
lemma inv_mul_mem_floorGroup_succ (h : g⁻¹ * s ∈ partialUnitriangularGroup (a + 1) ⊓ floorGroup a)
    (h_eq : g.val.val *ᵥ Pi.single (eStar a) 1 = s.val.val *ᵥ Pi.single (eStar a) 1) :
    g⁻¹ * s ∈ floorGroup (a + 1) := by
  have h_fix : (g⁻¹ * s).val.val *ᵥ Pi.single (eStar a) 1 = Pi.single (eStar a) 1 := by
    rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, ← h_eq]
    simp [mulVec_mulVec, -mulVec_single]
  refine mem_floorGroup.2 fun i j hj ↦ ?_
  by_cases h_star : j = eStar a
  · rw [h_star]
    simpa [Pi.single_apply, one_apply] using congrFun h_fix i
  · -- the other columns of floor at most `a` are those of the identity matrix by `h`
    grind [level_le_or_exists_eq_eStar, mem_inf, Fin.ext_iff]

/-- For a < ϱ and g in Q_{a+1} ∩ G_a, there is a Heisenberg element ν(v, β) of floor a such that
g⁻¹ν(v, β) lies in G_{a+1}. -/
lemma exists_heisenbergElem_mem_floorGroup
    (h : g ∈ partialUnitriangularGroup (a + 1) ⊓ floorGroup a) :
    ∃ p : ({ i // a + 1 ≤ floorOf i } → A) × skewAdjoint A,
      g⁻¹ * heisenbergElem a p ∈ floorGroup (a + 1) := by
  -- `g e*_a` has the entry `1` at `e*_a`, so it is the image of `e*_a` under some
  -- `heisenbergElem a p`
  have entry : g.val (eStar a) (eStar a) * 1 = 1 := by
    grind [partialUnitriangularGroup_apply_eStar h.1, one_apply_eq]
  obtain ⟨p, hp⟩ : ∃ p : ({ i // a + 1 ≤ floorOf i } → A) × skewAdjoint A,
      g.val.val *ᵥ Pi.single (eStar a) 1 =
        (heisenbergElem (T := T) a p).val.val *ᵥ Pi.single (eStar a) 1 :=
    exists_col_eq_heisenbergElem (eStar a) 1 h.2 rfl entry
  obtain ⟨h_floor, h_unip⟩ := heisenbergElem_mem_floorUnipotent (T := T) a p
  have h_mem : g⁻¹ * heisenbergElem a p ∈ partialUnitriangularGroup (a + 1) ⊓ floorGroup a :=
    mul_mem (inv_mem h) ⟨unipotentBelow_le_partialUnitriangularGroup h_unip, h_floor⟩
  exact ⟨p, inv_mul_mem_floorGroup_succ h_mem hp⟩

/-- An element of `Q_(l+1) ∩ G_l` is a product of an element of `G_(l+1)` and one of `N_l`. -/
lemma exists_floorGroup_mul_floorUnipotent
    (h : s ∈ partialUnitriangularGroup (l + 1) ⊓ floorGroup l) :
    ∃ g ∈ floorGroup (l + 1), ∃ ν ∈ floorUnipotent l, s = g * ν := by
  by_cases hl : l < 𝔰.ϱ
  · obtain ⟨p, hp⟩ := exists_heisenbergElem_mem_floorGroup (a := ⟨l, hl⟩) (inv_mem h)
    refine ⟨s⁻¹⁻¹ * heisenbergElem ⟨l, hl⟩ p, hp, (heisenbergElem ⟨l, hl⟩ p)⁻¹, ?_, by simp⟩
    exact inv_mem (heisenbergElem_mem_floorUnipotent ⟨l, hl⟩ p)
  · -- floor `l` has no hyperbolic pair, and `s` itself lies in `floorGroup (l + 1)`
    exact ⟨s, by grind [mem_inf], 1, one_mem _, by simp⟩

/-- Every element s of Q_j (unitriangular on the first j frame vectors) is a product s = γν with γ
in G_j (fixing the basis vectors of floor below j) and ν in N_(<j) (`unipotentBelow j`). -/
lemma exists_floorGroup_mul_unipotentBelow {j : ℕ} (hs : s ∈ partialUnitriangularGroup j) :
    ∃ γ ∈ floorGroup j, ∃ ν ∈ unipotentBelow j, s = γ * ν := by
  induction j with
  | zero => exact ⟨s, by simp, 1, one_mem _, (mul_one s).symm⟩
  | succ j ih =>
    obtain ⟨γ, hγ, ν, hν, rfl⟩ := ih (by grind)
    have hν_succ : ν ∈ unipotentBelow (j + 1) := unipotentBelow_le_succ hν
    have hγ_unitri : γ ∈ partialUnitriangularGroup (j + 1) :=
      (mul_mem_cancel_right (unipotentBelow_le_partialUnitriangularGroup hν)).1 hs
    obtain ⟨g, hg, n, hn, rfl⟩ := exists_floorGroup_mul_floorUnipotent ⟨hγ_unitri, hγ⟩
    exact ⟨g, hg, n * ν, mul_mem hn.2 hν_succ, mul_assoc g n ν⟩

/-- Let `A` have a trace-one element and let the Gram matrix `T.splitGram` of the whole space be
hermitian and invertible. Then an isometry s lies in the Bessel subgroup `besselS`, the subgroup
generated by `besselU` and `besselH`, if and only if s = uh. Here u lies in `besselU`, the
isometries that are block upper unitriangular for the levels with identity middle block, and h lies
in `besselH`, the isometries fixing every basis vector of floor at most ϱ (the `e_a`, the `e*_a` and
`z`). -/
lemma _root_.New.mem_besselS : s ∈ besselS ↔ ∃ u ∈ besselU, ∃ h ∈ besselH, s = u * h := by
  constructor
  · -- `s = h * ν = (h * ν * h⁻¹) * h`, and `h` normalises `unipotentBelow`
    intro hs
    obtain ⟨h, hh, ν, hν, rfl⟩ := exists_floorGroup_mul_unipotentBelow hs
    exact ⟨h * ν * h⁻¹, unipotentBelow_le_besselU (conj_mem_unipotentBelow hh hν), h, hh, by simp⟩
  · rintro ⟨u, hu, h, hh, rfl⟩
    exact mul_mem (mem_partialUnitriangularGroup_of_mem_besselU hu)
      (mem_partialUnitriangularGroup_of_mem_floorGroup hh)

/-- If the Gram matrix of the whole space is hermitian and invertible, then the Bessel subgroup
`besselS` normalises `besselU0`, the group of the elements of `besselU` that fix the frame. -/
lemma besselS_le_normalizer_besselU0 : T.besselS ≤ Subgroup.normalizer T.besselU0 := by
  refine le_normalizer_iff.2 fun s hs u hu ↦ ?_
  obtain ⟨hu, h_frame⟩ := mem_besselU0_iff.1 hu
  refine mem_besselU0_iff.2 ⟨(besselS_le_normalizer_besselU hs u).1 hu, ?_⟩
  -- with `s⁻¹ = v * h`, the frame block ignores `h` and is multiplicative in `u` and `v`
  obtain ⟨v, hv, h, hh, hs_inv⟩ := mem_besselS.1 (inv_mem hs)
  calc
    frameMatrix (s * u * s⁻¹) = frameMatrix s * frameMatrix u * frameMatrix v := by
      rw [hs_inv, ← mul_assoc, frameMatrix_mul_besselH _ hh, frameMatrix_mul hv, frameMatrix_mul hu]
    _ = frameMatrix (s * s⁻¹) := by
      rw [h_frame, mul_one, hs_inv, ← mul_assoc, frameMatrix_mul_besselH _ hh, frameMatrix_mul hv]
    _ = 1 := by simpa using (mem_besselU0_iff.1 (one_mem T.besselU0)).2

/-- Induction along the groups N_(<j), for a hermitian invertible Gram matrix. Suppose C 0 1 holds,
and C j ν implies C (j+1) (γν) for all γ in N_j. Then C j s holds for every s in N_(<j). -/
lemma unipotentBelow_induction {C : ℕ → T.G → Prop} (h_one : C 0 1)
    (h_step : ∀ j : ℕ, ∀ γ ∈ floorUnipotent j, ∀ ν : T.G, C j ν → C (j + 1) (γ * ν)) (j : ℕ) :
    ∀ s ∈ unipotentBelow j, C j s := by
  induction j with
  | zero =>
    intro s hs
    have h_eq : s = 1 :=
      eq_one_of_mem_floorGroup_inf ⟨floorGroup_zero.ge (mem_top s), hs⟩ (Or.inl le_rfl)
    rwa [h_eq]
  | succ j ih =>
    intro s hs
    -- write `s = γ * ν` with `γ ∈ floorGroup j` and `ν ∈ unipotentBelow j`; then `γ = s * ν⁻¹` lies
    -- in `unipotentBelow (j + 1)`
    obtain ⟨γ, hγ, ν, hν, rfl⟩ :=
      exists_floorGroup_mul_unipotentBelow (j := j) (unipotentBelow_le_partialUnitriangularGroup hs)
    have γ_mem : γ ∈ unipotentBelow (j + 1) :=
      (mul_mem_cancel_right (unipotentBelow_le_succ hν)).1 hs
    exact h_step j γ ⟨hγ, γ_mem⟩ ν (ih ν hν)

/-- Let `A` have a trace-one element τ and let `T.splitGram` be hermitian and invertible. For a < ϱ,
every g in N_a = G_a ∩ N_(<a+1) equals a Heisenberg element ν(v, β) of floor a, for some vector v on
the indices of floor at least a + 1 and some skew-adjoint β. Here ν(v, β) is the Eichler
transformation e*_a ↦ e*_a + v + (β − τh(v,v))e_a.

A weaker form of the standard parametrization of the unipotent radical of an isotropic line's
stabiliser by Eichler–Siegel transformations. It gives existence only, for one floor, without
uniqueness of parameters. -/
lemma exists_eq_heisenbergElem_of_mem (h : g ∈ floorUnipotent a) :
    ∃ p : ({ i // a + 1 ≤ floorOf i } → A) × skewAdjoint A, g = heisenbergElem a p := by
  obtain ⟨p, hp⟩ : ∃ p : ({ i // a + 1 ≤ floorOf i } → A) × skewAdjoint A,
      g⁻¹ * heisenbergElem a p ∈ floorGroup (a + 1) :=
    exists_heisenbergElem_mem_floorGroup ⟨unipotentBelow_le_partialUnitriangularGroup h.2, h.1⟩
  -- `g⁻¹ * heisenbergElem a p` lies in both `floorGroup (a + 1)` and `unipotentBelow (a + 1)`, so
  -- it is `1`
  have h_nilp : g⁻¹ * heisenbergElem a p ∈ unipotentBelow (a + 1) :=
    (mul_mem (inv_mem h) (heisenbergElem_mem_floorUnipotent a p)).2
  exact ⟨p, inv_mul_eq_one.1 (eq_one_of_mem_floorGroup_inf ⟨hp, h_nilp⟩ (by simp))⟩

/-- The map u ↦ ue*_a is a bijection from N_a = `floorUnipotent a`, the group of Eichler maps along
e_a, onto the isotropic vectors y that vanish on the floors below a (they are orthogonal to the
first a hyperbolic planes) and have h(e_a, y) = 1. -/
lemma bijOn_mulVec_eStar (a : Fin 𝔰.ϱ) :
    Set.BijOn (fun u : T.G ↦ u.val.val *ᵥ Pi.single (eStar a) 1)
      (floorUnipotent a : Subgroup T.G)
      {y : 𝔰.BesselIndex → A |
        (∀ j : 𝔰.BesselIndex, floorOf j < a → y j = 0) ∧
        star y ⬝ᵥ T.splitGram *ᵥ y = 0 ∧
        star (Pi.single (inl a) 1 : 𝔰.BesselIndex → A) ⬝ᵥ T.splitGram *ᵥ y = 1} := by
  have h_pair (y : 𝔰.BesselIndex → A) :
      star (Pi.single (inl a) 1 : 𝔰.BesselIndex → A) ⬝ᵥ T.splitGram *ᵥ y = y (eStar a) := by
    rw [Pi.star_single, star_one, single_dotProduct, one_mul]
    exact splitGram_mulVec_apply (inl a) a.is_lt
  refine ⟨fun u hu ↦ ?_, fun u hu v hv huv ↦ ?_, fun y ⟨h_lower, h_iso, h_top⟩ ↦ ?_⟩
  · -- the image is the column of `u` at `e*_a`; it is isotropic as `u` is an isometry
    obtain ⟨h_group, h_unip⟩ : u ∈ floorGroup a ∧ u ∈ unipotentBelow (a + 1) := mem_inf.1 hu
    have h_col (j : 𝔰.BesselIndex) :
        (u.val.val *ᵥ Pi.single (eStar a) 1 : 𝔰.BesselIndex → A) j = u.val j (eStar a) := by
      rw [mulVec_single_one, col_apply]
    refine ⟨fun j hj ↦ (h_col j).trans ?_, ?_, (h_pair _).trans ((h_col _).trans ?_)⟩
    · have h_ne : j ≠ eStar a := fun h_eq ↦ by simp [h_eq] at hj
      rw [apply_eq_one_apply_of_mem_floorGroup h_group j _ (.inl ⟨hj, hj.trans a.is_lt⟩),
        one_apply_ne h_ne]
    · rw [form_mulVec_mulVec]
      simp
    · have h_ne (b : Fin 𝔰.ϱ) (hb : b < a) : (eStar a : 𝔰.BesselIndex) ≠ eStar b :=
        fun h_eq ↦ hb.ne' (by simpa using h_eq)
      rw [partialUnitriangularGroup_apply_eStar (unipotentBelow_le_partialUnitriangularGroup h_unip)
        a.val.lt_succ_self _ h_ne, one_apply_eq]
  · -- `u⁻¹ v` fixes `e*_a`, so it lies in `floorGroup (a + 1)`; being unipotent, it is `1`
    have h_mem : u⁻¹ * v ∈ floorUnipotent a := mul_mem (inv_mem hu) hv
    have h_floor : u⁻¹ * v ∈ floorGroup (a + 1) :=
      inv_mul_mem_floorGroup_succ ⟨unipotentBelow_le_partialUnitriangularGroup h_mem.2, h_mem.1⟩ huv
    exact inv_mul_eq_one.1 (eq_one_of_mem_floorGroup_inf ⟨h_floor, h_mem.2⟩ (.inl le_rfl))
  · obtain ⟨p, hp⟩ := exists_heisenbergElem_mulVec_eq h_lower ((h_pair y).symm.trans h_top) h_iso
    exact ⟨heisenbergElem a p, heisenbergElem_mem_floorUnipotent a p, hp.symm⟩

omit [TraceOne A] H in
/-- A product x_0 ⋯ x_(j-1) with x_l in N_l = `floorUnipotent l` lies in
N_(<j) = `unipotentBelow j`. -/
lemma prod_ofFn_mem_unipotentBelow {j : ℕ} {x : Fin j → T.G}
    (hx : ∀ l : Fin j, x l ∈ floorUnipotent l) : (List.ofFn x).prod ∈ unipotentBelow j := by
  induction j with
  | zero => simp [one_mem]
  | succ j ih =>
    rw [List.ofFn_succ', List.prod_concat]
    exact mul_mem (unipotentBelow_le_succ (ih fun l ↦ hx l.castSucc)) (hx (Fin.last j)).2

/-- Every element of N_(<j) = `unipotentBelow j` is a product x_0 ⋯ x_(j-1) with unique factors x_l
in N_l = `floorUnipotent l`. Here N_(<j) is the group of isometries of `splitGram T` that are
unitriangular when the basis vectors of floor below `j` keep their level and all others get the
middle level ϱ, and N_l = G_l ∩ N_(<l+1). The floor of a basis vector is `a` for the a-th hyperbolic
pair, ϱ for the last vector z of the middle block, and ϱ + 1 for the other middle vectors. -/
lemma existsUnique_prod_of_mem_unipotentBelow {j : ℕ} {u : T.G} (hu : u ∈ unipotentBelow j) :
    ∃! x : Fin j → T.G, (∀ l : Fin j, x l ∈ floorUnipotent l) ∧ u = (List.ofFn x).prod := by
  induction j generalizing u with
  | zero =>
    have h_one : u = 1 :=
      eq_one_of_mem_floorGroup_inf ⟨floorGroup_zero.ge (mem_top u), hu⟩ (.inl le_rfl)
    exact ⟨Fin.elim0, ⟨fun l ↦ l.elim0, h_one⟩, fun x _ ↦ Subsingleton.elim x _⟩
  | succ j ih =>
    -- `u = ν⁻¹ γ⁻¹` with `ν` in `unipotentBelow j` and `γ` in `floorGroup j`; these groups meet
    -- only in `1`, so the last factor is `γ⁻¹` and the others are the factors of `ν⁻¹`
    obtain ⟨γ, hγ, ν, hν, h_inv⟩ :
        ∃ γ ∈ floorGroup j, ∃ ν ∈ unipotentBelow j, u⁻¹ = γ * ν :=
      exists_floorGroup_mul_unipotentBelow
        (unipotentBelow_le_partialUnitriangularGroup (inv_mem hu))
    have h_eq : u = ν⁻¹ * γ⁻¹ := by rw [← _root_.mul_inv_rev, ← h_inv, inv_inv]
    have hγ_unip : γ⁻¹ ∈ unipotentBelow (j + 1) :=
      (mul_mem_cancel_left (inv_mem (unipotentBelow_le_succ hν))).1 (by rwa [← h_eq])
    obtain ⟨y, ⟨hy_mem, hy_prod⟩, hy_unique⟩ := ih (inv_mem hν)
    refine ⟨Fin.snoc y γ⁻¹, ⟨fun l ↦ ?_, ?_⟩, fun x ⟨hx_mem, hx_prod⟩ ↦ ?_⟩
    · cases l using Fin.lastCases with
      | last =>
        rw [Fin.snoc_last]
        exact mem_inf.2 ⟨inv_mem hγ, hγ_unip⟩
      | cast l => simpa using hy_mem l
    · simp only [List.ofFn_succ', List.prod_concat, Fin.snoc_castSucc, Fin.snoc_last, h_eq, hy_prod]
    · rw [List.ofFn_succ', List.prod_concat] at hx_prod
      set ν' : T.G := (List.ofFn fun l : Fin j ↦ x l.castSucc).prod
      have hν' : ν' ∈ unipotentBelow j := prod_ofFn_mem_unipotentBelow fun l ↦ hx_mem l.castSucc
      have h_cross : ν * ν' = γ⁻¹ * (x (Fin.last j))⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← hx_prod, h_eq, mul_inv_cancel_left]
      have h_one : ν * ν' = 1 := by
        refine eq_one_of_mem_floorGroup_inf (mem_inf.2 ⟨?_, mul_mem hν hν'⟩) (.inl le_rfl)
        rw [h_cross]
        exact mul_mem (inv_mem hγ) (inv_mem (hx_mem (Fin.last j)).1)
      have h_init : Fin.init x = y :=
        hy_unique _ ⟨fun l ↦ hx_mem l.castSucc, inv_eq_of_mul_eq_one_right h_one⟩
      have h_last : x (Fin.last j) = γ⁻¹ := by
        rw [h_one, eq_comm, mul_inv_eq_one] at h_cross
        exact h_cross.symm
      rw [← h_init, ← h_last, Fin.snoc_init_self]

/-- Every element of the unipotent group `besselU` is a product x_0 ⋯ x_(ϱ-1) with unique factors
x_l in N_l = `floorUnipotent l`, the group of Eichler maps along e_l. -/
lemma existsUnique_prod_of_mem_besselU {u : T.G} (hu : u ∈ besselU) :
    ∃! x : Fin 𝔰.ϱ → T.G, (∀ l : Fin 𝔰.ϱ, x l ∈ floorUnipotent l) ∧ u = (List.ofFn x).prod :=
  existsUnique_prod_of_mem_unipotentBelow ((unipotentBelow_eq_besselU le_rfl).ge hu)

/-- Let `A` have a trace-one element τ (τ + τ̄ = 1) and let `T.splitGram` be hermitian and
invertible, with h(v, w) = v* · `T.splitGram` · w. For a < ϱ, a vector v on the indices of floor at
least a + 1 (extended by zero) and a skew-adjoint β, the inverse of the Heisenberg element ν(v, β)
of floor a is ν(−v, x − x̄ − β), where x = τh(v, v). -/
lemma heisenbergElem_inv :
    (heisenbergElem (T := T) a p)⁻¹ =
      heisenbergElem a
        (-p.1,
          skewPart
            (element *
              star (inclMatrix A (↑) *ᵥ p.1) ⬝ᵥ T.splitGram *ᵥ inclMatrix A (↑) *ᵥ p.1) - p.2) := by
  refine inv_eq_of_mul_eq_one_right (heisenbergElem_mul.trans ?_)
  ext : 2
  -- the vectors cancel and so do the two corrections `x − x̄`
  simp [heisenbergElem, eichlerMap, mulVec_neg]

/-- The Heisenberg element ν(v, β) of floor a acts on the frame by a matrix that differs from `1`
only in row a, by the products −h(v, f_c) with the frame vectors. -/
lemma frameMatrix_heisenbergElem :
    frameMatrix (heisenbergElem (T := T) a p) =
      1 - vecMulVec (Pi.single a.castSucc 1) fun c : Fin (𝔰.ϱ + 1) ↦
        star (inclMatrix A (↑) *ᵥ p.1) ⬝ᵥ T.splitGram *ᵥ Pi.single (𝔰.besselFrame c) 1 := by
  refine Matrix.ext fun b c ↦ ?_
  have h_dual : (Pi.single (𝔰.besselFrame c) 1 : 𝔰.BesselIndex → A) (eStar a) = 0 := by
    cases c using Fin.lastCases <;> simp
  have h_col : frameMatrix (heisenbergElem (T := T) a p) b c =
      ((heisenbergElem (T := T) a p).val.val *ᵥ Pi.single (𝔰.besselFrame c) 1)
        (𝔰.besselFrame b) := by
    simp [frameMatrix, -heisenbergElem_mulVec]
  rw [h_col, heisenbergElem_mulVec, h_dual, ← besselFrame_castSucc]
  simp [vecMulVec_apply, Pi.single_apply, one_apply, besselFrame_injective.eq_iff, sub_eq_add_neg,
    -besselFrame_castSucc]

/-- Let s be in G_{a+1}, so that s fixes the basis vectors of floor below a + 1. Let v be a vector
of the floors at least a + 1, extended by zero, let β be skew, and let ν(v,
β) = `heisenbergElem a (v, β)` be the Eichler transformation e*_a ↦ e*_a + v + (β − τh(v,v))e_a.
Then the sum of the entries just above the diagonal of the block of sν(v, β)s⁻¹ on the frame (f_0,
…, f_ϱ) = (e_0, …, e_(ϱ-1), z) equals −h(v, s⁻¹f_{a+1}), where s⁻¹f_{a+1} is
`orbitPoint a.succ s`. -/
lemma simpleRootSum_conj_heisenbergElem (hs : s ∈ floorGroup (a + 1)) :
    simpleRootSum (s * heisenbergElem a p * s⁻¹) =
      -(star (inclMatrix A (↑) *ᵥ p.1) ⬝ᵥ T.splitGram *ᵥ orbitPoint a.succ s) := by
  -- conjugation by `s` applies `s` to the vector of the Heisenberg element
  rw [mul_heisenbergElem hs, mul_inv_cancel_right, ← form_mulVec_mulVec s,
    ← inclMatrix_mulVec_floor_block a.2 hs, orbitPoint_eq_iff.1 rfl]
  -- the entries at the simple roots are read off the matrix on the frame
  change ∑ b : Fin 𝔰.ϱ, frameMatrix (heisenbergElem (T := T) a _) b.castSucc b.succ = _
  simp [frameMatrix_heisenbergElem, vecMulVec_apply, Pi.single_apply, one_apply,
    (Fin.castSucc_lt_succ ..).ne]

end FloorGroups

variable [TopologicalSpace A] [MeasureSpace A] [P : Place A]
  (ι : Type) [Fintype ι] [DecidableEq ι] (T : 𝔰.Form A) (m : ℕ)
  {n k Z : Type} [Fintype n] [Fintype k] [DecidableEq k]

/-! ### The Haar measure of `V_l` -/

/-- Haar measure of `V_l`, as a measure on all vectors: the image of the volume on the coordinates
of floor at least `l` under extension by zero. -/
abbrev FloorGroups.floorVolume (l : ℕ) : Measure (𝔰.BesselIndex → A) :=
  Measure.map (fun v ↦ inclMatrix A (Subtype.val : {i // l ≤ floorOf i} → 𝔰.BesselIndex) *ᵥ v)
    volume

/-! ### Hyperbolic bases, Weyl elements and changes of coordinates -/

/-- A basis of the middle space `V_ϱ`, which has Gram matrix `T` and rank `𝔰.k + 1`: a first
hyperbolic pair, `m` more pairs and an orthonormal part indexed by `ι`. So there are
`card ι + 2 * m + 2` basis vectors, and the field `card_eq` equates the two counts. As the modulus
of `det T` is 1, the change of coordinates preserves volume
(`New.Floors.HyperbolicBasis.measurePreserving_mulVec`). -/
structure HyperbolicBasis where
  /-- The matrix whose columns are the basis vectors. -/
  basisMatrix : Matrix 𝔰.MiddleIndex (Fin 2 ⊕ SplitIndex m ι) A
  /-- The Gram matrix of the basis for `T`: m + 1 hyperbolic planes and an orthonormal part. -/
  gram_eq : basisMatrixᴴ * T * basisMatrix = planeSumGram (hyperbolicGram (Fin m) 1)
  /-- The number of basis vectors is the rank of V_ϱ. -/
  card_eq : 𝔰.k + 1 = card ι + 2 * m + 2
  /-- The modulus of the determinant of `T` is 1. -/
  modulus_det : P.modulus T.det = 1

variable {ι T m} (F : HyperbolicBasis ι T m) (b : Fin 𝔰.n) [MeasurableSpace Z] {ζ : Measure Z}

/-- The image of the measure md(c)^{d_l} dc on A under c ↦ w_l(c)⁻¹, where w_l(c) is the Weyl
element of floor l and d_l = `𝔰.k` + 1 + 2(ϱ − (l + 1)), the subtraction being truncated. -/
abbrev Place.weylLaw (l : ℕ) : Measure T.G :=
  (volume.withDensity fun c ↦ modulus c ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (l + 1)))).map fun c ↦
    (floorWeyl l c)⁻¹

/-- Reindexing the coordinates along a bijection preserves the volume. -/
lemma measurePreserving_inclMatrix (g : n ≃ k) : MeasurePreserving (inclMatrix A g *ᵥ ·) := by
  have h_eq : (inclMatrix A g *ᵥ ·) =
      (MeasurableEquiv.piCongrLeft (fun _ : n ↦ A) g.symm).symm := by
    ext v i
    simp [inclMatrix, submatrix_mulVec_equiv, MeasurableEquiv.piCongrLeft]
  rw [h_eq]
  exact (measurePreserving_piCongrLeft _ g.symm).symm

omit [TopologicalSpace A] [MeasureSpace A] [Place A] in
/-- The Gram matrix of the standard basis vectors `e_(g j)` for `J` is the submatrix of `J` on the
indices `g j`. -/
lemma gram_inclMatrix {n : Type*} (g : n → k) (J : Matrix k k A) :
    (inclMatrix A g)ᴴ * J * inclMatrix A g = J.submatrix g g := by
  simp [inclMatrix, mul_apply, ← ext_iff, Matrix.one_apply]

/-- If `f` enumerates the basis indices of `V_l` without repetition, then extension by zero along
`f` carries the volume of `n → A` to the Haar measure of `V_l`. -/
lemma map_inclMatrix_eq_floorVolume (f : n → 𝔰.BesselIndex)
    (hf_inj : Injective f := by intro; simp)
    (hf_range : ∀ i : 𝔰.BesselIndex, i ∈ Set.range f ↔ l ≤ floorOf i := by simp) :
    volume.map (inclMatrix A f *ᵥ ·) = floorVolume l := by
  -- `f` factors through a bijection `e` onto the indices of `V_l`, which permutes the coordinates
  let e : n ≃ {i : 𝔰.BesselIndex // l ≤ floorOf i} :=
    (Equiv.ofInjective f hf_inj).trans (.subtypeEquivRight hf_range)
  have h_incl : inclMatrix A (Subtype.val : {i : 𝔰.BesselIndex // l ≤ floorOf i} → 𝔰.BesselIndex) *
      inclMatrix A e = inclMatrix A f := mul_inclMatrix ..
  rw [floorVolume, ← (measurePreserving_inclMatrix e).map_eq]
  simp (disch := fun_prop) [Measure.map_map, comp_def, h_incl]

/-- Extension by zero from the middle block carries the volume to the Haar measure of `V_ϱ`. -/
lemma map_inclMatrix_middle_eq_floorVolume :
    volume.map (inclMatrix A (inr ∘ inl : 𝔰.MiddleIndex → 𝔰.BesselIndex) *ᵥ ·) =
      floorVolume 𝔰.top :=
  map_inclMatrix_eq_floorVolume _ (inr_injective.comp inl_injective) (by simp)

/-- The indices of the hyperbolic pairs of `V_b` after the first: the `m` other pairs of `V_ϱ`, and
the pairs `e_a`, `e*_a` with `b ≤ a`. -/
abbrev FloorPairs (m : ℕ) : Type := Fin m ⊕ {i : Fin 𝔰.ϱ // b.val ≤ i}

/-- The vector of index `j` of the basis `F` of `V_ϱ`, extended by zero to the coordinates of the
`e_a` and the `e*_a`. -/
def HyperbolicBasis.middleVector (j : Fin 2 ⊕ SplitIndex m ι) : 𝔰.BesselIndex → A
  | inl _ => 0
  | inr (inl i) => F.basisMatrix i j
  | inr (inr _) => 0

/-- The basis of `V_b` made of the basis `F` of `V_ϱ` and the pairs `e_a`, `e*_a` with `b ≤ a`, as
the columns of a matrix. It is the block matrix of `F.basisMatrix` and the identity on these pairs,
with its rows placed among the basis indices and its columns reordered. The columns are listed in
`New.Floors.HyperbolicBasis.col_floorBasis`, and the Gram matrix is computed in
`New.Floors.HyperbolicBasis.gram_floorBasis`. -/
def HyperbolicBasis.floorBasis :
    Matrix 𝔰.BesselIndex (Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m) A :=
  let S : Type := {i : Fin 𝔰.ϱ // b.val ≤ i}
  -- the basis indices of `V_b`: the middle block, then the `e_a` and the `e*_a` with `b ≤ a`
  let incl : 𝔰.MiddleIndex ⊕ S ⊕ S → 𝔰.BesselIndex := inr ∘ inl ⊕ᵥ Sum.map (↑) (inr ∘ (↑))
  -- the new order: the first pair of `F.basisMatrix`; the first vectors of the other pairs; the
  -- orthonormal part; the second vectors of the other pairs
  let order : Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m → (Fin 2 ⊕ SplitIndex m ι) ⊕ S ⊕ S :=
    inl ∘ inl ⊕ᵥ
      (Sum.map (inr ∘ inl) inl ⊕ᵥ (inl ∘ inr ∘ inr ∘ inl ⊕ᵥ Sum.map (inr ∘ inr ∘ inr) inr))
  inclMatrix A incl * F.basisMatrix.fromBlocks 0 0 (diagonal (n := S ⊕ S) 1) * inclMatrix A order

/-- The columns of `F.floorBasis b` are, in this order: the first pair of `F`; the first vectors of
the `m` other pairs of `F`, then the `e_a`; the orthonormal vectors of `F`; the second vectors of
the `m` other pairs of `F`, then the `e*_a`. -/
lemma HyperbolicBasis.col_floorBasis (j : Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m) :
    (F.floorBasis b).col j =
      match j with
      | inl i => F.middleVector (inl i)
      | inr (inl (inl c)) => F.middleVector (inr (inl c))
      | inr (inl (inr a)) => Pi.single (inl a) 1
      | inr (inr (inl i)) => F.middleVector (inr (inr (inl i)))
      | inr (inr (inr (inl c))) => F.middleVector (inr (inr (inr c)))
      | inr (inr (inr (inr a))) => Pi.single (eStar a) 1 := by
  rw [floorBasis, mul_inclMatrix]
  -- compare entries, for each kind of column
  rcases j with i | (c | a) | i | c | a
  all_goals
    simp [funext_iff, middleVector, inclMatrix, mul_apply, one_apply, Pi.single_apply, -ite_mul,
      Finset.sum_boole_mul]

/-- The Gram matrix of `F.floorBasis b` consists of a hyperbolic plane for the first pair, one for
each pair indexed by `FloorPairs b m`, and an orthonormal part indexed by `ι`. -/
lemma HyperbolicBasis.gram_floorBasis :
    (F.floorBasis b)ᴴ * T.splitGram * F.floorBasis b =
      planeSumGram (hyperbolicGram (FloorPairs b m) (1 : Matrix ι ι A)) := by
  -- on the basis vectors of `V_b` the form is `T` plus hyperbolic planes; `F.gram_eq` handles `T`
  let S : Type := {i : Fin 𝔰.ϱ // b.val ≤ i}
  let incl : 𝔰.MiddleIndex ⊕ S ⊕ S → 𝔰.BesselIndex := inr ∘ inl ⊕ᵥ Sum.map (↑) (inr ∘ (↑))
  have block : T.splitGram.submatrix incl incl = T.fromBlocks 0 0 (fromBlocks 0 1 1 0) := by
    simp [incl, S, splitGram, ← ext_iff, Matrix.one_apply]
  rw [floorBasis, gram_mul, gram_inclMatrix, gram_mul, gram_inclMatrix, block]
  simp [F.gram_eq, fromBlocks_conjTranspose, fromBlocks_multiply, ← ext_iff, Matrix.one_apply]

/-- Multiplication by `F.basisMatrix`, the matrix of the hyperbolic basis `F` of `V_ϱ`, preserves
the volume of coordinate vectors. -/
lemma HyperbolicBasis.measurePreserving_mulVec : MeasurePreserving (F.basisMatrix *ᵥ ·) := by
  -- Reindex the columns by `e` to get a square matrix `M`. Its Gram matrix has square one.
  let e : 𝔰.MiddleIndex ≃ Fin 2 ⊕ SplitIndex m ι := equivOfCardEq (by simp +arith [F.card_eq])
  let M : Matrix 𝔰.MiddleIndex 𝔰.MiddleIndex A := F.basisMatrix * inclMatrix A e
  have gram_sq : (Mᴴ * T * M) ^ 2 = 1 := by
    rw [gram_mul]
    simp [sq, gram_inclMatrix, F.gram_eq, ↓reindex_equiv e.symm, fromBlocks_multiply,
      fromCols_mul_fromRows, fromCols_mul_fromBlocks, fromBlocks_mul_fromRows, ← ext_iff,
      Matrix.one_apply]
  have h_left : Mᴴ * T * M * (Mᴴ * T) * M = 1 := by rw [Matrix.mul_assoc _ _ M, ← sq, gram_sq]
  have h_unit : IsUnit M.det := isUnit_det_of_left_inverse h_left
  -- Taking determinants, `modulus M.det ^ 4 = 1`, since `modulus T.det = 1`.
  have h_md : P.modulus M.det = 1 := by
    have h_det : P.modulus ((Mᴴ * T * M) ^ 2).det = 1 := by simp [gram_sq]
    simpa [F.modulus_det, ← sq, toNNReal_eq_one_iff] using congrArg ENNReal.toNNReal h_det
  have h_vol : volume.map (M *ᵥ ·) = volume := by simp [P.map_mulVec_volume _ M h_unit, h_md]
  refine ⟨by fun_prop, ?_⟩
  simpa (disch :=
    fun_prop) [← (measurePreserving_inclMatrix e).map_eq, Measure.map_map, ↓ comp_def] using h_vol

/-- The basis `F.floorBasis b` carries the volume of its coordinates to the Haar measure of
`V_b`. -/
lemma HyperbolicBasis.map_floorBasis_volume :
    volume.map (F.floorBasis b *ᵥ ·) = FloorGroups.floorVolume b := by
  let S : Type := {i : Fin 𝔰.ϱ // b.val ≤ i}
  let incl : 𝔰.MiddleIndex ⊕ S ⊕ S → 𝔰.BesselIndex := inr ∘ inl ⊕ᵥ Sum.map (↑) (inr ∘ (↑))
  let order : Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m → (Fin 2 ⊕ SplitIndex m ι) ⊕ S ⊕ S :=
    inl ∘ inl ⊕ᵥ
      (Sum.map (inr ∘ inl) inl ⊕ᵥ (inl ∘ inr ∘ inr ∘ inl ⊕ᵥ Sum.map (inr ∘ inr ∘ inr) inr))
  have h_incl : volume.map (inclMatrix A incl *ᵥ ·) = FloorGroups.floorVolume b :=
    map_inclMatrix_eq_floorVolume incl (by simp [incl, S, Injective]) (by simp [incl, S, b.is_le])
  have h_order : Bijective order := by simp [order, S, Bijective, Injective, Surjective]
  simp only [floorBasis, diagonal_one', ← mulVec_mulVec, fromBlocks_mulVec, zero_mulVec, add_zero,
    one_mulVec, zero_add]
  -- The map permutes the coordinates, splits off those of the pairs `e_a`, `e*_a` with `b ≤ a`,
  -- applies `F.basisMatrix` to the others, and includes the result as `V_b`. Each step preserves
  -- volume.
  exact (MeasurePreserving.comp ⟨by fun_prop, h_incl⟩
    (measurePreserving_sumElim.comp
      ((F.measurePreserving_mulVec.prod (.id _)).comp
        ((measurePreserving_sumPiEquivProdPi _).comp
          (measurePreserving_inclMatrix (.ofBijective order h_order)))))).map_eq

variable {μ ν : Measure T.G} [SFinite μ] [SFinite ν]
  (σ : ℕ → Measure T.G) [∀ l, SFinite (σ l)]
  {i j : ℕ} {s : T.G} {S : Subgroup T.G} {f : T.G → ℝ≥0∞}

/-- The measure `η_l` on the unitary group. For `l < ϱ` it is the image of the Haar measure of
`V_(l+1)` times the skew measure of the place, under the Heisenberg parametrisation
`New.Floors.TraceOne.heisenbergElem` of `N_l`. Otherwise it is the unit mass at `1`. -/
def Place.heisenbergMeasure [H : IsHermitianUnit T.splitGram] (l : ℕ) : Measure (U T.splitGram) :=
  if h : l < 𝔰.ϱ then (volume.prod P.skewMeasure).map (heisenbergElem (T := T) ⟨l, h⟩) else dirac 1

/-- The group `G_l` is a measurable set: finitely many entries are prescribed. -/
lemma measurableSet_floorGroup : MeasurableSet (T.floorGroup l : Set T.G) :=
  (isClosed_of_entries_eq_one mem_floorGroup).measurableSet

@[simp]
lemma heisenbergMeasure_eq_dirac_one [H : IsHermitianUnit T.splitGram]
    (h : 𝔰.ϱ ≤ l) : heisenbergMeasure l = dirac (1 : T.G) :=
  dite_eq_right h.not_gt

@[fun_prop]
lemma continuous_orbitPoint : Continuous (orbitPoint b : T.G → 𝔰.BesselIndex → A) := by
  fun_prop [orbitPoint]

variable [H : IsHermitianUnit T.splitGram] in
instance : SFinite (heisenbergMeasure l : Measure T.G) := by
  fun_cases heisenbergMeasure <;> infer_instance

/-- The unitary group is closed in the space of matrices, with the subspace topology. -/
lemma isClosedEmbedding_unitary_coe [H : IsHermitianUnit T.splitGram] :
    Topology.IsClosedEmbedding fun g : T.G ↦ (g : GL 𝔰.BesselIndex A).val :=
  isClosedEmbedding_coe H.2

/-- A function with values in the unitary group is measurable if it is measurable as a function
with values in matrices. -/
lemma measurable_unitary_of_coe [H : IsHermitianUnit T.splitGram] {f : Z → T.G}
    (hf : Measurable fun z : Z ↦ (f z : GL 𝔰.BesselIndex A).val) : Measurable f :=
  isClosedEmbedding_unitary_coe.measurableEmbedding.measurable_comp_iff.1 hf

@[fun_prop]
lemma continuous_weylElem [H : IsHermitianUnit T.splitGram] :
    Continuous (weylElem 𝔰.ϱ : (ℕ → Aˣ) → T.G) := by
  refine isClosedEmbedding_unitary_coe.continuous_iff.2 (continuous_matrix fun i j ↦ ?_)
  simp only [Function.comp_apply, weylElem, weylOn, Units.isUnit, and_true, and_self,
    ↓inverse_star_unit, Pi.star_apply, isUnit_star, star_star, Ring.inverse_invertible, invOf_units,
    of_apply]
  -- each entry is constant, a parameter, or its conjugate inverse
  split_ifs <;> fun_prop

@[fun_prop]
lemma measurable_floorWeyl [H : IsHermitianUnit T.splitGram] :
    Measurable (floorWeyl l : A → T.G) := by
  classical
  have h_isUnit : Measurable fun c : A ↦ IsUnit c :=
    measurableEmbedding_units_val.measurableSet_range.mem
  refine measurable_unitary_of_coe
    (measurable_pi_iff.2 fun i ↦ measurable_pi_iff.2 fun j ↦ ?_)
  simp only [floorWeyl, weylOn, eq_ite_iff, not_and, Pi.star_apply, isUnit_star, star_star,
    of_apply]
  -- each entry is constant, `c`, or its conjugate inverse, on pieces cut out by `IsUnit c`
  apply_rules [Measurable.ite] <;> measurability

@[fun_prop]
lemma continuous_heisenbergElem [H : IsHermitianUnit T.splitGram]
    {a : Fin 𝔰.ϱ} : Continuous (heisenbergElem (T := T) a) := by
  refine isClosedEmbedding_unitary_coe.continuous_iff.2 ?_
  simp only [↓comp_def, heisenbergElem, eichlerMap, star_neg, mulVec_mulVec, Pi.star_single,
    star_one, single_vecMul, one_smul, val_of_coe]
  fun_prop

/-- An element `s` of `G_l` acts on the coordinates of floor at least `l` by a block that preserves
their volume. -/
lemma measurePreserving_floor_block_mulVec [H : IsHermitianUnit T.splitGram]
    (h : s ∈ floorGroup l) :
    MeasurePreserving fun v : { a // l ≤ floorOf a } → A ↦
      (s : GL 𝔰.BesselIndex A).val.toSquareBlockProp (l ≤ floorOf ·) *ᵥ v := by
  -- `s` is block triangular with the identity on the indices of floor below `l`, so the block has
  -- the determinant of `s`, which has norm one
  have outside : s.val.val.toSquareBlockProp (¬l ≤ floorOf ·) = 1 := by
    ext i j
    have h_entry : s.val.val i j = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) i j :=
      h i j (by grind)
    simpa [toSquareBlockProp_def, one_apply, Subtype.ext_iff] using h_entry
  have h_det : s.val.val.det = (s.val.val.toSquareBlockProp (l ≤ floorOf ·)).det := by
    simp [twoBlockTriangular_det' s.val.val (l ≤ floorOf ·) (by grind [one_apply_ne]), outside]
  have h_unitary : s.val.val.det ∈ unitary A := (U.det (H.2.map detMonoidHom) s).property
  refine measurePreserving_mulVec _ ?_
  rw [← h_det]
  exact h_unitary.1

/-- The measure `η_l = heisenbergMeasure l` is carried by `N_l`. -/
lemma ae_mem_floorUnipotent [H : IsHermitianUnit T.splitGram] :
    ∀ᵐ x : T.G ∂heisenbergMeasure l, x ∈ floorUnipotent l := by
  fun_cases heisenbergMeasure
  · exact (ae_map_iff (by fun_prop) (measurableSet_floorGroup.inter
      (isClosed_of_entries_eq_one mem_unipotentBelow).measurableSet)).2
      (.of_forall (heisenbergElem_mem_floorUnipotent _))
  · simp

/-- The measure `η_l = heisenbergMeasure l` on the unitary group `T.G` is invariant under right and
under left translation by every element `s` of `N_l = floorUnipotent l = G_l ∩ N_(<l+1)`, that is,
`η_l ∗ δ_s = η_l` and `δ_s ∗ η_l = η_l`. For `l < ϱ`, `η_l` is the image of Haar measure on
`V_(l+1)` times the skew measure under the Heisenberg parametrisation of `N_l`; otherwise it is the
unit mass at `1`. -/
lemma heisenbergMeasure_mconv_dirac [H : IsHermitianUnit T.splitGram] (h : s ∈ floorUnipotent l) :
    heisenbergMeasure l ∗ₘ dirac s = heisenbergMeasure l ∧
    dirac s ∗ₘ heisenbergMeasure l = heisenbergMeasure l := by
  fun_cases heisenbergMeasure
  case case2 hl =>
    simp [eq_one_of_mem_floorGroup_inf h (by grind)]
  case case1 hl =>
    obtain ⟨⟨v, t⟩, rfl⟩ := exists_eq_heisenbergElem_of_mem (a := ⟨l, hl⟩) h
    -- By `heisenbergElem_mul`, multiplication by `heisenbergElem a (v, t)` on either side
    -- translates the skew parameter, which `P.skewMeasure` absorbs, and translates the vector by
    -- `v`, which volume absorbs.
    have skew_inv (Φ : T.G → ℝ≥0∞) (w : {i : 𝔰.BesselIndex // l + 1 ≤ floorOf i} → A)
        (β₀ : skewAdjoint A) :
        ∫⁻ β, Φ (heisenbergElem ⟨l, hl⟩ (w, β + β₀)) ∂P.skewMeasure =
          ∫⁻ β, Φ (heisenbergElem ⟨l, hl⟩ (w, β)) ∂P.skewMeasure :=
      lintegral_add_right_eq_self (fun β ↦ Φ (heisenbergElem ⟨l, hl⟩ (w, β))) β₀
    have vec_inv (Φ : T.G → ℝ≥0∞) :
        ∫⁻ w, ∫⁻ β, Φ (heisenbergElem ⟨l, hl⟩ (w + v, β)) ∂P.skewMeasure =
          ∫⁻ w, ∫⁻ β, Φ (heisenbergElem ⟨l, hl⟩ (w, β)) ∂P.skewMeasure :=
      lintegral_add_right_eq_self (fun w ↦ ∫⁻ β, Φ (heisenbergElem ⟨l, hl⟩ (w, β)) ∂P.skewMeasure) v
    constructor
    all_goals
      refine ext_of_lintegral _ fun Φ hΦ ↦ ?_
      simp (disch := fun_prop) [heisenbergElem_mul, add_assoc, add_comm t, add_comm v, skew_inv,
        vec_inv, ↓ mconv_dirac, ↓ lintegral_map, ↓ lintegral_prod, ↓ dirac_mconv]

/-- Let `η_l = heisenbergMeasure l` be the measure on the unitary group `T.G` carried by the
Heisenberg group `N_l`. For `l < ϱ` it is the image of Haar measure on `V_(l+1)` times the skew
measure of the place under `heisenbergElem`, and otherwise it is the unit mass at `1`. If `s` lies
in `G_(l+1) = floorGroup (l + 1)`, the unitary elements fixing every basis vector of floor below
`l + 1`, then `dirac s ∗ₘ η_l = η_l ∗ₘ dirac s`. -/
lemma dirac_mconv_heisenbergMeasure_comm [H : IsHermitianUnit T.splitGram]
    (h : s ∈ floorGroup (l + 1)) :
    dirac s ∗ₘ heisenbergMeasure l = heisenbergMeasure l ∗ₘ dirac s := by
  fun_cases heisenbergMeasure
  case case2 => simp
  case case1 hl =>
    -- by `mul_heisenbergElem`, moving `s` across applies its block to the vector, which keeps the
    -- volume
    nth_rw 2 [← ((measurePreserving_floor_block_mulVec h).prod (.id _)).map_eq]
    simp (disch := fun_prop) [↓Measure.map_map, mul_heisenbergElem (a := ⟨l, hl⟩) h, Prod.map_def,
      ↓ dirac_mconv, ↓ comp_def, ↓ mconv_dirac]

/-! ### Convolutions along the floors, quadric measures and Plancherel -/

/-- For measures σ_l on the unitary group, the convolution σ_{a+i−1} ∗ ⋯ ∗ σ_a in descending order
of i consecutive terms; the Dirac measure at 1 if i = 0. -/
def descConv : ℕ → ℕ → Measure T.G
  | _, 0 => dirac 1
  | a, i + 1 => descConv (a + 1) i ∗ₘ σ a

/-- For measures σ_l on the unitary group, the convolution σ_0 ∗ ⋯ ∗ σ_{j−1} in ascending order; the
Dirac measure at 1 if j = 0. -/
def ascConv : ℕ → Measure T.G
  | 0 => dirac 1
  | j + 1 => ascConv j ∗ₘ σ j

instance (a i : ℕ) : SFinite (descConv σ a i) := by fun_induction descConv <;> infer_instance

instance : SFinite (ascConv σ j) := by fun_induction ascConv <;> infer_instance

variable {σ}

lemma lintegral_mconv_dirac (f : T.G → ℝ≥0∞) :
    lintegral (μ ∗ₘ dirac s) f = ∫⁻ x : T.G, f (x * s) ∂μ := by
  simpa [↓ mconv_dirac] using lintegral_map_equiv f (.mulRight s)

lemma lintegral_dirac_mconv (f : T.G → ℝ≥0∞) (s : T.G) :
    lintegral (dirac s ∗ₘ μ) f = ∫⁻ x : T.G, f (s * x) ∂μ := by
  simpa [↓ dirac_mconv] using lintegral_map_equiv f (.mulLeft s)

/-- If `dirac s ∗ₘ μ = μ ∗ₘ dirac t`, then the substitution `x ↦ s⁻¹ * x * t` preserves integrals
against `μ`. -/
lemma lintegral_eq_of_dirac_mconv_eq {t : T.G} (h : dirac s ∗ₘ μ = μ ∗ₘ dirac t) :
    lintegral μ f = ∫⁻ x : T.G, f (s⁻¹ * x * t) ∂μ := by
  simpa [↓lintegral_dirac_mconv, ↓lintegral_mconv_dirac, mul_assoc] using
    congrArg (lintegral · fun x : T.G ↦ f (s⁻¹ * x)) h

/-- The integral against a convolution as an iterated integral, with the right factor outside. -/
lemma lintegral_mconv_symm (hf : Measurable f) :
    lintegral (μ ∗ₘ ν) f = ∫⁻ y : T.G, ∫⁻ x : T.G, f (x * y) ∂μ ∂ν :=
  (lintegral_mconv hf).trans (lintegral_lintegral_swap (by fun_prop))

/-- The mass of `Y` under `μ ∗ₘ ν` is the `ν`-integral of the mass of `Y * y⁻¹` under `μ`. -/
lemma mconv_apply_eq_lintegral {Y : Set T.G} (hY : MeasurableSet Y) :
    (μ ∗ₘ ν) Y = ∫⁻ y : T.G, μ {x : T.G | x * y ∈ Y} ∂ν :=
  (map_apply measurable_mul hY).trans (prod_apply_symm (measurable_mul hY))

omit [SFinite μ] in
/-- The convolution of two measures carried by a measurable subgroup `S` is carried by `S`. -/
lemma ae_mem_mconv (hμ : ∀ᵐ x : T.G ∂μ, x ∈ S) (hν : ∀ᵐ x : T.G ∂ν, x ∈ S)
    (hS : MeasurableSet (S : Set T.G) := by exact measurableSet_floorGroup) :
    ∀ᵐ x : T.G ∂μ ∗ₘ ν, x ∈ S :=
  (ae_map_iff (by fun_prop) hS).2
    (.mono (measure_prod_compl_eq_zero hμ hν) fun _ hx ↦ S.mul_mem hx.1 hx.2)

/-- If `dirac s` commutes with `ν` for `μ`-almost every `s`, then `μ` commutes with `ν` under
convolution. -/
lemma mconv_comm_of_ae (h : ∀ᵐ s : T.G ∂μ, dirac s ∗ₘ ν = ν ∗ₘ dirac s) : μ ∗ₘ ν = ν ∗ₘ μ := by
  refine ext_of_lintegral _ fun f hf ↦ ?_
  calc lintegral (μ ∗ₘ ν) f = ∫⁻ s, ∫⁻ y, f (s * y) ∂ν ∂μ := lintegral_mconv hf
    _ = ∫⁻ s, ∫⁻ y, f (y * s) ∂ν ∂μ :=
      lintegral_congr_of_ae_imp h fun s hs ↦ by
        rw [← lintegral_dirac_mconv, hs, lintegral_mconv_dirac]
    _ = lintegral (ν ∗ₘ μ) f := (lintegral_mconv_symm hf).symm

/-- A descending convolution of `i + j` terms splits after the first `i` indices. -/
lemma descConv_add (i j a : ℕ) :
    descConv σ a (i + j) = descConv σ (a + i) j ∗ₘ descConv σ a i := by
  fun_induction descConv σ a i with
  | case1 a => simp
  | case2 a i ih =>
    rw [show i + 1 + j = i + j + 1 by ring, descConv, ih, mconv_assoc,
      show a + 1 + i = a + (i + 1) by ring]

/-- A descending convolution starting at `0` gains its next term `σ i` on the left. -/
lemma descConv_succ (i : ℕ) : descConv σ 0 (i + 1) = σ i ∗ₘ descConv σ 0 i := by
  simp [↓descConv_add, descConv]

omit [TopologicalSpace A] [Place A] [SFinite μ] in
/-- A function with nonzero integral is nonzero at some point where a given almost everywhere
property holds. -/
lemma exists_ne_zero_of_ae {p : T.G → Prop} (h : ∀ᵐ x : T.G ∂μ, p x) (hf : lintegral μ f ≠ 0) :
    ∃ x : T.G, p x ∧ f x ≠ 0 := by
  by_contra! h_zero
  exact hf (lintegral_eq_zero_of_ae_eq_zero (h.mono h_zero))

/-- The measure on a quadric in V_b: the image of `New.Floors.Place.quadricMeasure` with parameter β
under the basis `F.floorBasis b`. By default, β is obtained from h(f_b, f_b) by `skewUnitMul`. -/
abbrev HyperbolicBasis.floorQuadricMeasure [_H : IsHermitianUnit T.splitGram]
    (β : skewAdjoint A := skewUnitMul (T.splitGram (𝔰.besselFrame b) (𝔰.besselFrame b))
      (IsHermitian.apply IsHermitianUnit.conjTranspose_eq (𝔰.besselFrame b) (𝔰.besselFrame b))) :
    Measure (𝔰.BesselIndex → A) :=
  (quadricMeasure (hyperbolicGram (FloorPairs b m) 1) β).map (F.floorBasis b *ᵥ ·)

/-- Let `V_b` be the span of the basis vectors of floor at least `b`, with Haar measure
`floorVolume b` (the volume on those coordinates, extended by zero). The measures
`F.floorQuadricMeasure b β`, images under the basis `F.floorBasis b` of the quadric measures with
skew parameter `β`, disintegrate this Haar measure along `h(x, x)`, where `h = T.splitGram`. -/
lemma HyperbolicBasis.isDisintegration_floorVolume [H : IsHermitianUnit T.splitGram]
    {μ : Measure (𝔰.BesselIndex → A)} (hμ : μ = FloorGroups.floorVolume b) :
    IsDisintegration μ T.splitGram (F.floorQuadricMeasure b ·) := by
  -- Transport `isDisintegration_quadricMeasure` along `F.floorBasis b`. Its Gram matrix has square
  -- one, which gives a left inverse of `F.floorBasis b`.
  have gram : (F.floorBasis b)ᴴ * T.splitGram * F.floorBasis b =
      planeSumGram (hyperbolicGram (FloorPairs b m) (1 : Matrix ι ι A)) := F.gram_floorBasis b
  have left_inv :
      (F.floorBasis b)ᴴ * T.splitGram * F.floorBasis b * ((F.floorBasis b)ᴴ * T.splitGram) *
        F.floorBasis b = 1 := by
    rw [Matrix.mul_assoc _ _ (F.floorBasis b), gram]
    simp [fromBlocks_multiply, fromCols_mul_fromRows, fromCols_mul_fromBlocks,
      fromBlocks_mul_fromRows, ← ext_iff, Matrix.one_apply]
  rw [hμ, ← F.map_floorBasis_volume b]
  exact (isDisintegration_quadricMeasure (by simp [fromBlocks_conjTranspose,
    conjTranspose_fromRows_eq_fromCols_conjTranspose,
    conjTranspose_fromCols_eq_fromRows_conjTranspose])).map gram left_inv

/-- Let `b ≤ ϱ` and let `Z` be a nonempty standard Borel space. Let `Φ : T.G → Z` be a measurable
function that is left invariant under `Q_(b+1) ∩ G_b`, where `Q_(b+1)` is the partially
unitriangular group `partialUnitriangularGroup (b + 1)` and `G_b = floorGroup b` is the group of
isometries fixing every basis vector of floor below `b`. Then there is a measurable `Ψ` on vectors
with `Φ σ = Ψ (orbitPoint b σ)` for every `σ ∈ G_b`, where `orbitPoint b σ = σ⁻¹ f_b` and `f_b` is
the vector of index `b` in the frame `(e_0, …, e_{ϱ-1}, z)`. -/
lemma exists_factor_orbitPoint [StandardBorelSpace Z] [Nonempty Z] {Φ : T.G → Z} (hΦ : Measurable Φ)
    (h_inv : (partialUnitriangularGroup (b + 1) ⊓ floorGroup b).FixesLeft Φ) :
    ∃ Ψ : (𝔰.BesselIndex → A) → Z, Measurable Ψ ∧ ∀ σ ∈ floorGroup b, Φ σ = Ψ (orbitPoint b σ) := by
  -- On `floorGroup b` the invariant function `Φ` factors through `orbitPoint b`, as
  -- `Ψ ∘ orbitPoint b`. The source is standard Borel and the range of `orbitPoint b` is countably
  -- separated, so `Ψ` is measurable on that range; it extends measurably to all vectors because `Z`
  -- is standard Borel and nonempty.
  have : StandardBorelSpace (T.floorGroup b) := measurableSet_floorGroup.standardBorel
  have h_factors : FactorsThrough (Φ ∘ (↑)) fun σ : T.floorGroup b ↦ orbitPoint b σ.1 :=
    fun σ τ h ↦ by simpa using h_inv _ (inv_mul_mem_of_orbitPoint_eq σ⁻¹.2 τ⁻¹.2 h) τ
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (𝔰.BesselIndex → A) → Z,
      Φ ∘ (↑) = Ψ ∘ fun σ : T.floorGroup b ↦ orbitPoint b σ.1 :=
    (factorsThrough_iff _).1 h_factors
  have h_meas : Measurable (Ψ ∘ fun σ : T.floorGroup b ↦ orbitPoint b σ.1) := by
    rw [← hΨ]
    exact hΦ.comp (by fun_prop)
  rw [Measurable.measurable_comp_iff_restrict (by fun_prop)] at h_meas
  obtain ⟨Ψ', hΨ'_meas, hΨ'⟩ := h_meas.exists_eq_measurable_comp
  refine ⟨Ψ', hΨ'_meas, fun σ hσ ↦ ?_⟩
  calc Φ σ = Ψ (orbitPoint b σ) := congrFun hΨ ⟨σ, hσ⟩
    _ = Ψ' (orbitPoint b σ) := congrFun hΨ' ⟨orbitPoint b σ, ⟨σ, hσ⟩, rfl⟩

/-- If every `σ l` is carried by `G_l`, then so is the descending convolution starting at `l`. -/
lemma ae_descConv_mem (h : ∀ {l : ℕ}, ∀ᵐ x : T.G ∂σ l, x ∈ floorGroup l) :
    ∀ᵐ x : T.G ∂descConv σ l i, x ∈ floorGroup l := by
  fun_induction descConv with
  | case1 => simp
  | case2 a i ih =>
    exact ae_mem_mconv (ih.mono (floorGroup_anti a.le_succ)) h measurableSet_floorGroup

variable [H : IsHermitianUnit T.splitGram]

/-- Let `η_i = heisenbergMeasure i` be the measure on the unitary group `T.G` carried by the
Heisenberg group `N_i`: the image of Haar measure on `V_(i+1)` times the skew measure of the place
for `i < ϱ`, and the unit mass at `1` otherwise. Let `η_{<j} = ascConv heisenbergMeasure j` be the
convolution `η₀ ∗ ⋯ ∗ η_{j−1}`, which is the Dirac mass at `1` if `j = 0`. For every `s` in
`G_j = T.floorGroup j`, the unitary elements fixing every basis vector of floor below `j`, the Dirac
mass at `s` commutes with `η_{<j}` under convolution. -/
lemma ascConv_heisenbergMeasure_dirac_comm :
    ∀ s ∈ T.floorGroup j,
      dirac s ∗ₘ ascConv heisenbergMeasure j = ascConv heisenbergMeasure j ∗ₘ dirac s := by
  induction j with
  | zero => simp [ascConv]
  | succ j ih =>
    intro s hs
    rw [ascConv, ← mconv_assoc, ih s (floorGroup_anti j.le_succ hs), mconv_assoc,
      dirac_mconv_heisenbergMeasure_comm hs, mconv_assoc]

/-- η_{<j+1} = η_j ∗ η_{<j}: the last factor may be moved to the front, as η_j is carried by G_j. -/
lemma ascConv_heisenbergMeasure_succ :
    (ascConv heisenbergMeasure (j + 1) : Measure T.G) =
      heisenbergMeasure j ∗ₘ ascConv heisenbergMeasure j :=
  (mconv_comm_of_ae
    (ae_mem_floorUnipotent.mono fun x hx ↦ ascConv_heisenbergMeasure_dirac_comm x hx.1)).symm

/-- Let `A` be a place and `T` a middle Gram matrix whose split Gram matrix `T.splitGram` is
hermitian and invertible. In the unitary group of `T.splitGram`, let η_{<j} = η₀ ∗ ⋯ ∗ η_{j−1} be
the ascending convolution of the Heisenberg measures. Here η_l is the image of Haar measure on
V_(l+1) times the skew measure under the parametrisation of N_l for l < ϱ, and the unit mass at 1
otherwise. Then η_{<j} ∗ δ_s = η_{<j} and δ_s ∗ η_{<j} = η_{<j} for every s in N_(<j), the group of
elements that are unitriangular when basis vectors of floor below j keep their level and all others
get the middle level. -/
lemma ascConv_heisenbergMeasure_invariant (hs : s ∈ unipotentBelow j) :
    ascConv heisenbergMeasure j ∗ₘ dirac s = ascConv heisenbergMeasure j ∧
    dirac s ∗ₘ ascConv heisenbergMeasure j = ascConv heisenbergMeasure j := by
  refine unipotentBelow_induction
    (C := fun (i : ℕ) (x : T.G) ↦
      ascConv heisenbergMeasure i ∗ₘ dirac x = ascConv heisenbergMeasure i ∧
      dirac x ∗ₘ ascConv heisenbergMeasure i = ascConv heisenbergMeasure i)
    ?_ ?_ j s hs
  · simp
  · -- `heisenbergMeasure j` absorbs `γ` and `ascConv heisenbergMeasure j` absorbs `ν`; the two
    -- measures commute
    intro j γ hγ ν ⟨asc_ν, ν_asc⟩
    obtain ⟨η_γ, γ_η⟩ := heisenbergMeasure_mconv_dirac hγ
    rw [← dirac_mconv_dirac]
    constructor
    · rw [← mconv_assoc, ascConv, mconv_assoc _ (heisenbergMeasure j), η_γ, ← ascConv,
        ascConv_heisenbergMeasure_succ, mconv_assoc, asc_ν]
    · rw [mconv_assoc, ascConv, ← mconv_assoc (dirac ν), ν_asc, ← ascConv,
        ascConv_heisenbergMeasure_succ, ← mconv_assoc, γ_η]

/-- The measure η_{<j} = η₀ ∗ ⋯ ∗ η_{j−1} is carried by `N_(<j)`. -/
lemma ae_ascConv_mem_unipotentBelow :
    ∀ᵐ x : T.G ∂ascConv heisenbergMeasure j, x ∈ T.unipotentBelow j := by
  induction j with
  | zero => simp [ascConv]
  | succ j ih =>
    exact ae_mem_mconv (ih.mono (by grind)) (ae_mem_floorUnipotent.mono fun _ hx ↦ hx.2)
      (isClosed_of_entries_eq_one mem_unipotentBelow).measurableSet

/-- Plancherel's inequality with a damping factor `∏ i, G (v i)`, for `G ≥ 0` continuous and
integrable and the additive character `ψ` of the place `A`: the constant is the `L¹` norm of the
transform of `G` (dilated by `ξ`), to the power `card ι`. -/
lemma Place.lintegral_damped_fourier_le (ξ : A) {G : A → ℝ} (hG : Continuous G)
    (hG_int : Integrable G) (hG_pos : 0 ≤ G) {f : (ι → A) → ℂ} (hf : Integrable f)
    (hf_meas : Measurable f) :
    ∫⁻ v : ι → A, ‖(‖∫ w : ι → A, P.ψ (ξ * star v ⬝ᵥ w) * f w‖ ^ 2 * ∏ i : ι, G (v i) : ℂ)‖ₑ ≤
      (∫⁻ a : A, ‖∫ v : A, G v * P.ψ (star v * ξ * a)‖ₑ) ^ card ι * ∫⁻ w : ι → A, ‖f w‖ₑ ^ 2 := by
  -- Expand the square as a double integral over `x = (w, w')` and integrate over `v` first.
  let g (v : ι → A) (x : (ι → A) × (ι → A)) : ℂ :=
    P.ψ (ξ * star v ⬝ᵥ (x.2 - x.1)) * ((∏ i, G (v i)) * (star (f x.1) * f x.2))
  have hg : Integrable g.uncurry :=
    .mono ((Integrable.fintype_prod fun _ ↦ hG_int).smul_prod (hf.mul_prod hf))
      (Measurable.aestronglyMeasurable (by fun_prop)) (by simp [g, uncurry])
  have h_expand (v : ι → A) :
      ‖∫ w : ι → A, P.ψ (ξ * star v ⬝ᵥ w) * f w‖ ^ 2 * ∏ i : ι, (G (v i) : ℂ) =
        ∫ x : (ι → A) × (ι → A), g v x := by
    rw [← Complex.conj_mul', ← integral_conj, ← integral_prod_mul, ← integral_mul_const]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp [g, mul_sub, P.ψ.map_sub_eq_div, division_def, Complex.inv_eq_conj]
    ring
  -- The transform of the damping factor is a product of transforms of `G`.
  have h_factor (z : ι → A) : ‖∫ v : ι → A, P.ψ (ξ * star v ⬝ᵥ z) * ∏ i : ι, (G (v i) : ℂ)‖ₑ ≤
      ∏ i : ι, ‖∫ v : A, G v * P.ψ (star v * ξ * z i)‖ₑ := by
    have ψ_sum (s : Finset ι) (x : ι → A) : P.ψ (∑ i ∈ s, x i) = ∏ i ∈ s, P.ψ (x i) := by
      induction s using Finset.cons_induction <;> simp [*, AddChar.map_add_eq_mul]
    simp [enorm, ← ofNNReal_finsetProd, ← nnnorm_prod, ← integral_fintype_prod_volume_eq_prod,
      dotProduct, Finset.mul_sum, Finset.prod_mul_distrib, mul_comm, mul_left_comm, ψ_sum]
  -- For a fixed difference `z = w' - w`, Cauchy–Schwarz bounds `∫ |f w| |f (w + z)|`.
  have h_cauchy (z : ι → A) :
      ∫⁻ w : ι → A, ‖f w‖ₑ * ‖f (w + z)‖ₑ ≤ ∫⁻ w : ι → A, ‖f w‖ₑ ^ 2 := by
    simpa [← rpow_add_of_nonneg, ← two_mul, lintegral_add_right_eq_self (‖f ·‖ₑ ^ 2)] using
      lintegral_mul_le_Lp_mul_Lq _ .two_two hf.1.enorm (hf.comp_add_right z).1.enorm
  have h_diff (z : ι → A) : ∫⁻ w : ι → A, ‖∫ v : ι → A, g v (w, w + z)‖ₑ ≤
      (∏ i : ι, ‖∫ v : A, G v * P.ψ (star v * ξ * z i)‖ₑ) * ∫⁻ w : ι → A, ‖f w‖ₑ ^ 2 := by
    simpa [g, ← mul_assoc (ψ _), integral_mul_const, lintegral_const_mul'] using
      mul_le_mul' (h_factor z) (h_cauchy z)
  have h_nonneg (v : ι → A) :
      (‖∫ x : (ι → A) × (ι → A), g v x‖ : ℂ) = ∫ x : (ι → A) × (ι → A), g v x := by
    simp [← h_expand, abs_of_nonneg (hG_pos _)]
  simp only [Complex.ofReal_prod, h_expand]
  calc ∫⁻ v, ‖∫ x, g v x‖ₑ
    _ ≤ ‖∫ v, ∫ x, g v x‖ₑ := by
      -- The inner integrals are non-negative reals.
      grw [← ofReal_integral_norm_eq_lintegral_enorm (by exact hg.integral_prod_left),
        Real.ofReal_le_enorm]
      rw [← integral_congr_ae (.of_forall h_nonneg), integral_complex_ofReal]
      simp [enorm]
    _ ≤ ∫⁻ x : (ι → A) × (ι → A), ‖∫ v, g v x‖ₑ := by
      grw [integral_integral_swap hg, enorm_integral_le_lintegral_enorm]
    _ ≤ ∫⁻ z : ι → A, ∫⁻ w, ‖∫ v, g v (w, w + z)‖ₑ := by
      grw [volume_eq_prod, ← (measurePreserving_prod_add_swap ..).map_eq, lintegral_map_le,
        lintegral_prod_le]
      fun_prop
    _ ≤ ∫⁻ z : ι → A, (∏ i, ‖∫ v, G v * P.ψ (star v * ξ * z i)‖ₑ) * ∫⁻ w, ‖f w‖ₑ ^ 2 :=
      lintegral_mono h_diff
    _ = (∫⁻ a : A, ‖∫ v : A, G v * P.ψ (star v * ξ * a)‖ₑ) ^ card ι *
          ∫⁻ w : ι → A, ‖f w‖ₑ ^ 2 := by
      rw [lintegral_mul_const _ (by fun_prop), card, ← Finset.prod_const (lintegral ..),
        ← lintegral_pi_prod _ (by fun_prop), volume_pi]
/-- Plancherel's inequality at a place A: for a unit η and f measurable and integrable on A^ι,
∫ |∫ ψ(η v*w) f(w) dw|² dv ≤ (c/md η)^{|ι|} ∫ |f|². Here v*w is `star v ⬝ᵥ w`, ψ is the additive
character of the place, and md is its `modulus`. The constant c = `kernelBound` is part of the data
of the place: a bound in [0, ∞] on the L¹ norm of the Fourier transform of a kernel that the place
provides. -/
lemma Place.plancherel_inequality (η : Aˣ) {f : (ι → A) → ℂ} (hf : Integrable f)
    (hf_meas : Measurable f) :
    ∫⁻ v : ι → A, ‖∫ w : ι → A, P.ψ (η * star v ⬝ᵥ w) * f w‖ₑ ^ 2 ≤
      (P.kernelBound / P.modulus η) ^ card ι * ∫⁻ w : ι → A, ‖f w‖ₑ ^ 2 := by
  -- Damp the integrand by `∏ i, G (star x * v i)`, which tends to `1` as `x → 0`. By Fatou's lemma
  -- it suffices to bound the damped integral for units `x`, which accumulate at `0`.
  obtain ⟨G, hG, hG_int, hG_pos, hG_zero, hG_mass⟩ := P.exists_plancherel_kernel
  let damped (x : A) (v : ι → A) : ℝ≥0∞ :=
    ‖(‖∫ w, P.ψ (η * star v ⬝ᵥ w) * f w‖ ^ 2 * ∏ i, G (star x * v i) : ℂ)‖ₑ
  have h_limit (v : ι → A) :
      Tendsto (damped · v) (nhds 0) (nhds (‖∫ w, P.ψ (η * star v ⬝ᵥ w) * f w‖ₑ ^ 2)) :=
    Continuous.tendsto' (by fun_prop) 0 _ (by simp [damped, enorm, hG_zero])
  have h_unit (u : Aˣ) : ∫⁻ v : ι → A, damped u v ≤
      (P.kernelBound / P.modulus η) ^ card ι * ∫⁻ w : ι → A, ‖f w‖ₑ ^ 2 := by
    -- Substitute `v ↦ (star u)⁻¹ • v` on the left and `z ↦ η * u⁻¹ * z` in the mass of the kernel;
    -- both sides acquire the factor `(modulus u)⁻¹ ^ card ι`.
    grw [lintegral_eq_mul_lintegral_map (map_mulVec_volume _ (star u⁻¹.1 • 1) _), lintegral_map_le,
        ← hG_mass,
        lintegral_eq_mul_lintegral_map (map_mul_volume (η * u⁻¹)) (modulus_ne_zero _)
          (modulus_ne_top _),
        lintegral_map]
    · have h_cancel (a : A) : star u.1 * (star u⁻¹.1 * a) = a := by simp [← mul_assoc, ← star_mul]
      simpa [damped, smul_mulVec, mul_pow, ENNReal.mul_div_right_comm, ENNReal.div_self,
        mul_assoc, h_cancel] using
        mul_le_mul_right (lintegral_damped_fourier_le (η.1 * u⁻¹.1) hG hG_int hG_pos hf hf_meas)
          ((P.modulus u)⁻¹ ^ card ι)
    -- the side goals: measurability, and the determinant is a unit
    any_goals fun_prop
    all_goals simp [IsUnit.pow]
  grw [lintegral_mono fun v ↦ (h_limit v).liminf_eq.ge, lintegral_liminf_le (by fun_prop)]
  exact liminf_le_of_frequently_le'
    ((mem_closure_iff_frequently.1 (dense_of_ae ae_isUnit 0)).mono (Set.forall_mem_range.2 h_unit))

end New.Floors

end
