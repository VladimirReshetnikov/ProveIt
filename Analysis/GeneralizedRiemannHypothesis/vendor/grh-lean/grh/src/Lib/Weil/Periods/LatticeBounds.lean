import Lib.Weil.Periods.PointLattice

/-!
# Finitely many orbits of lattices satisfy the bounds

Let `V` be a hermitian space presented as a part `X` plus a string of vectors. For a finite point
`x` let `Λ'⁻` be the intersection of its lattice with `X^⊥`, and `Λ⁻` the same for the point `1`.
The bounds are `q̄ ^ k Λ⁻ ⊆ Λ'⁻` and `q ^ k Λ'⁻ ⊆ Λ⁻`, for a finite adele `q` and a natural number
`k`.

* `New.Grading.finite_image_latticeMinus`: if `q` is invertible, finitely many `Λ'⁻` satisfy the
  bounds.
* `New.Grading.HasLatticeBounds.latticeMinus_componentOn`: under the bounds, `Λ'⁻` does not change
  when the components of `x` outside `Q ∪ Q̄` are replaced by `1`, for a set `Q` of places outside
  which `q` has valuation `1`.
* `New.Grading.exists_finite_representatives`: let `E` contain a primitive root of unity of order
  5040, let `q` be invertible and have valuation `1` outside `Q`. Among the double cosets under the
  finite Bessel subgroup and the stabiliser of the standard lattice, those with bounded orbit have
  finitely many representatives, supported on `Q ∪ Q̄`.

Notions from other files:
* `New.Grading`: an indexing of the basis of `V` by `X` and a string of vectors, with Gram matrix
  `1` on `X` and anti-diagonal on the string, which spans `X^⊥`; `stringProj` projects onto `X^⊥`.
  It gives each basis vector an integer grade; the part of a vector in a grade is its projection to
  the span of the basis vectors of that grade.
* `New.Space.lattice`: the lattice of a point `x`, the vectors with integral coordinates (entries in
  `Ô E`) in its frame, the columns of the matrix `V.xFin * x`, where `V.xFin` is the fixed
  invertible finite adelic matrix whose columns span the lattice of the point `1`.
* `New.idem`: the finite adele that is `1` at the places of a set and `0` at the others.
* `atPlace`: the component of a finite point at a place; `v`: the valuation of such a place.

## Relation to the literature

Known result: there are finitely many lattices between two given ones, and a lattice is determined
by its local components. Source: O'Meara, Introduction to Quadratic Forms, §81.
-/

open Matrix Pointwise Valued

noncomputable section

namespace New

variable {E X ι : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι]
  [DecidableEq X] {ε : ι → ℤˣ} {s : ℕ} {N : E} {V : Space E ι ε}

namespace Space

/-- The lattice of a finite point is open: it is the preimage of the integral vectors under the
inverse of the matrix of its frame. -/
lemma isOpen_lattice (x : Gf E ι) : IsOpen (V.lattice x : Set (ι → 𝔸f E)) := by
  have h_preimage : (V.lattice x : Set (ι → 𝔸f E)) =
      (V.xFin * x.val)⁻¹.val.mulVec ⁻¹' {z | ∀ i, z i ∈ Ô E} := Set.ext fun y ↦ mem_lattice
  rw [h_preimage]
  exact (isOpen_intVectors isOpen_Ô).preimage (continuous_const.matrix_mulVec continuous_id)

/-- The lattice of a finite point is compact: it is the image of the integral vectors under the
matrix of its frame. -/
lemma isCompact_lattice (x : Gf E ι) : IsCompact (V.lattice x : Set (ι → 𝔸f E)) := by
  have h_image : (V.lattice x : Set (ι → 𝔸f E)) =
      (V.xFin * x.val).val.mulVec '' {z : ι → 𝔸f E | ∀ i : ι, z i ∈ Ô E} := by
    refine Set.ext fun y ↦ ⟨fun hy ↦ ?_, ?_⟩
    · exact ⟨_, mem_lattice.1 hy, by simp only [mulVec_mulVec, Units.mul_inv, one_mulVec]⟩
    · rintro ⟨z, hz, rfl⟩
      exact mulVec_mem_lattice.2 hz
  rw [h_image]
  exact (isCompact_pi_infinite fun _ ↦ isCompact_Ô).image
    (continuous_const.matrix_mulVec continuous_id)

variable {x x' : Gf E ι} {y : ι → 𝔸f E} {T : Set (FinPlace E)}

/-- The part `idem T • y` of `y` at the places of `T` lies in the lattice of `x` if and only if the
coordinates of `y` in the frame `V.xFin * x` of that lattice are integral at these places. -/
lemma idem_smul_mem_lattice : idem T • y ∈ V.lattice x ↔
    ∀ i : ι, ∀ w ∈ T, v (((V.xFin * x.val)⁻¹.val *ᵥ y) i w) ≤ 1 := by
  simp only [mem_lattice, mulVec_smul, Pi.smul_apply, smul_eq_mul, idem_mul_mem_Ô]

/-- If two points have the same components at the places of `T`, then the part `idem T • y` of a
vector `y` at these places lies in both of their lattices or in neither. -/
lemma idem_smul_mem_lattice_congr (h_atPlace : ∀ w ∈ T, x.atPlace w = x'.atPlace w) :
    idem T • y ∈ V.lattice x ↔ idem T • y ∈ V.lattice x' := by
  -- The component at `w` of the coordinates depends only on the component of the point at `w`.
  have h_coord (g : Gf E ι) (i : ι) (w : FinPlace E) : ((V.xFin * g.val)⁻¹.val *ᵥ y) i w =
      ((V.xFin.map (evalAt w) * g.atPlace w)⁻¹.val *ᵥ (evalAt w ∘ y)) i := by
    change evalAt w (((V.xFin * g.val)⁻¹.val *ᵥ y) i) =
      ((V.xFin.map (evalAt w) * g.val.map (evalAt w))⁻¹.val *ᵥ (evalAt w ∘ y)) i
    rw [← map_mul, ← map_inv, RingHom.map_mulVec, GeneralLinearGroup.val_map_apply]
  simp +contextual only [idem_smul_mem_lattice, h_coord, h_atPlace]

/-- For a scalar `c` of valuation `1` at the places of `T`, the part `idem T • y` of `y` at `T`
lies in a lattice if and only if its product with `c` does. -/
lemma smul_idem_smul_mem_lattice {c : 𝔸f E} (hc : ∀ w ∈ T, v (c w) = 1) :
    c • idem T • y ∈ V.lattice x ↔ idem T • y ∈ V.lattice x := by
  rw [smul_comm]
  simp +contextual only [idem_smul_mem_lattice, mulVec_smul, Pi.smul_apply, smul_eq_mul,
    finAdele_mul_apply, map_mul, hc, one_mul]

/-- A vector lies in a lattice if and only if its parts at the places of `T` and off `T` do. -/
lemma mem_lattice_iff_idem_smul (T : Set (FinPlace E)) :
    y ∈ V.lattice x ↔ idem T • y ∈ V.lattice x ∧ idem Tᶜ • y ∈ V.lattice x := by
  rw [idem_smul_mem_lattice, idem_smul_mem_lattice, mem_lattice]
  -- Being integral means being integral at every place, and each place lies in `T` or in `Tᶜ`.
  grind [mem_Ô]

end Space

namespace Grading

variable {Y : Grading V N X s}

variable (Y) in
/-- For an invertible finite adele `q`, the points `x` of the finite adelic unitary group with the
bounds `q̄ ^ k Λ⁻ ⊆ Λ'⁻`, `q ^ k Λ'⁻ ⊆ Λ⁻` give only finitely many intersections `Λ'⁻` of their
lattice with `X^⊥`. Here `Λ⁻` is the intersection for `x = 1`. -/
lemma finite_image_latticeMinus (q : (𝔸f E)ˣ) (k : ℕ) :
    (Y.latticeMinus '' {x : Gf E ι | Y.HasLatticeBounds q.val k x}).Finite := by
  -- Such a lattice lies in the compact set `C` and is determined by its image modulo the open
  -- subgroup `U`; the image of `C` modulo `U` is finite.
  let U : Submodule (Ô E) (ι → 𝔸f E) := star q.val ^ k • V.lattice 1
  let C : Set (ι → 𝔸f E) := (q ^ k)⁻¹ • (V.lattice 1 : Set (ι → 𝔸f E))
  have : DiscreteTopology ((ι → 𝔸f E) ⧸ U) := QuotientAddGroup.discreteTopology
    (N := U.toAddSubgroup) ((q.isUnit.star.pow k).isOpenMap_smul _ (V.isOpen_lattice 1))
  have h_finite : (U.mkQ '' C).Finite :=
    (((V.isCompact_lattice 1).smul _).image U.continuous_mkQ).finite_of_discrete
  let P : Submodule (Ô E) (ι → 𝔸f E) := Y.stringProj.range.restrictScalars (Ô E)
  have h_inter : U ⊓ P ≤ star q.val ^ k • Y.latticeMinus 1 := by
    rintro _ ⟨⟨u, hu, rfl⟩, z, hz : Y.stringProj z = star q.val ^ k • u⟩
    exact Submodule.smul_mem_pointwise_smul u _ _ (mem_latticeMinus.2 ⟨hu,
      (q.isUnit.star.pow k).smul_left_cancel.1 <| by rw [← map_smul, ← hz, stringProj_stringProj]⟩)
  -- By the modular law `(Λ'⁻ + U) ∩ X^⊥ = Λ'⁻ + (U ∩ X^⊥) = Λ'⁻`.
  have h_recover {x : Gf E ι} (hx : Y.HasLatticeBounds q.val k x) :
      ((Y.latticeMinus x).map U.mkQ).comap U.mkQ ⊓ P = Y.latticeMinus x := by
    have h_le : Y.latticeMinus x ≤ P := inf_le_right
    rw [Submodule.comap_map_mkQ, sup_comm, sup_inf_assoc_of_le U h_le,
      sup_eq_left.2 (h_inter.trans hx.lower)]
  refine Set.Finite.of_injOn (f := fun L : Submodule (Ô E) (ι → 𝔸f E) ↦ U.mkQ '' L) ?_ ?_
    h_finite.finite_subsets
  · rintro _ ⟨x, hx : Y.HasLatticeBounds q.val k x, rfl⟩
    exact Set.image_mono fun y hy ↦ Set.mem_inv_smul_set_iff.2
      (latticeMinus_le_lattice (smul_le_iff_forall.1 hx.upper y hy))
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ h_image
    have h_map : (Y.latticeMinus x).map U.mkQ = (Y.latticeMinus x').map U.mkQ :=
      SetLike.coe_injective h_image
    rw [← h_recover hx, h_map, h_recover hx']

/-- Let `Y` present the hermitian space `V` as a part `X` plus a string of `s` vectors, which spans
`X^⊥`. For a point `g` of the finite adelic unitary group `Gf E ι`, `Y.latticeMinus g` is the
intersection with `X^⊥` of the lattice `V.lattice g`, the adelic vectors with integral coordinates
in the frame `V.xFin * g`. Write `Λ'⁻ = Y.latticeMinus x` and `Λ⁻ = Y.latticeMinus 1`, and assume
the bounds `q̄ ^ k Λ⁻ ⊆ Λ'⁻` and `q ^ k Λ'⁻ ⊆ Λ⁻` for a finite adele `q`. Let `Q` be a set of finite
places outside which `q` is a local unit (its multiplicative valuation `v` is `1`). Let
`x' = Gf.componentOn ι Q x` be the point with the components of `x` at the places of `Q` and their
conjugates, and with component `1` at the other places. Then `Y.latticeMinus x' = Λ'⁻`. -/
lemma HasLatticeBounds.latticeMinus_componentOn {V : Space E ι ε} {Y : Grading V N X s}
    {q : 𝔸f E} {k : ℕ} {x : Gf E ι} (h_bounds : Y.HasLatticeBounds q k x) {Q : Set (FinPlace E)}
    (hq : ∀ w : FinPlace E, w ∉ Q → v (q w) = 1) :
    Y.latticeMinus (Gf.componentOn ι Q x) = Y.latticeMinus x := by
  -- Split `y ∈ X^⊥` into its parts at `T = Q ∪ Q̄` and off `T`. Off `T` both `q` and its conjugate
  -- have valuation `1`, so the bounds say that `Λ'⁻` and `Λ⁻` agree there.
  suffices h_iff : ∀ y : ι → 𝔸f E, Y.stringProj y = y →
      (y ∈ V.lattice (Gf.componentOn ι Q x) ↔ y ∈ V.lattice x) by
    ext y
    rw [mem_latticeMinus, mem_latticeMinus]
    exact and_congr_left (h_iff y)
  intro y hy
  let T : Set (FinPlace E) := Q.conjClosure
  have h_on : idem T • y ∈ V.lattice (Gf.componentOn ι Q x) ↔ idem T • y ∈ V.lattice x :=
    V.idem_smul_mem_lattice_congr fun w hw ↦ by rw [Gf.atPlace_componentOn, ite_eq_left hw]
  have h_off : idem Tᶜ • y ∈ V.lattice (Gf.componentOn ι Q x) ↔ idem Tᶜ • y ∈ V.lattice 1 :=
    V.idem_smul_mem_lattice_congr fun w hw ↦ by rw [Gf.atPlace_componentOn, ite_eq_right hw,
      map_one]
  have h_incl {c : 𝔸f E} {g g' : Gf E ι} (hc : ∀ w ∈ Tᶜ, v (c w) = 1)
      (h_le : c • Y.latticeMinus g ≤ Y.latticeMinus g') (hg : idem Tᶜ • y ∈ V.lattice g) :
      idem Tᶜ • y ∈ V.lattice g' := by
    have h_smul : c • idem Tᶜ • y ∈ Y.latticeMinus g' :=
      smul_le_iff_forall.1 h_le _ (mem_latticeMinus.2 ⟨hg, by rw [map_smul, hy]⟩)
    exact (V.smul_idem_smul_mem_lattice hc).1 (latticeMinus_le_lattice h_smul)
  have hq_pow : ∀ w ∈ Tᶜ, v ((q ^ k) w) = 1 := by
    simp +contextual [T, finAdele_pow_apply, hq]
  have hq_star_pow : ∀ w ∈ Tᶜ, v ((star q ^ k) w) = 1 := by
    simp +contextual [T, finAdele_pow_apply, hq]
  have h_agree : idem Tᶜ • y ∈ V.lattice 1 ↔ idem Tᶜ • y ∈ V.lattice x :=
    ⟨h_incl hq_star_pow h_bounds.lower, h_incl hq_pow h_bounds.upper⟩
  rw [V.mem_lattice_iff_idem_smul T, V.mem_lattice_iff_idem_smul (x := x) T, h_on, h_off, h_agree]

variable (Y) in
/-- Let `q` be an invertible finite adele of valuation `1` at the places outside `Q`, let `R` be the
finite Bessel subgroup `Y.besselFin` (it contains the image `Y.inclXFin a` of each point `a` of the
unitary group of `X`) and `J°` the stabiliser `stdLevel E ι` of the standard lattice. Assume that
`E` contains a primitive root of unity of order 5040. Then there is a finite set `T` of points
supported on `Q` and its conjugate such that `R x J°` meets `T` whenever the `R`-orbit of `x` is
bounded (`HasBoundedOrbit`: some point of it has a graded lattice whose intersection with `X^⊥`
satisfies the bounds given by `q` and `k`; graded means that it contains the part in each grade of
each of its vectors). -/
lemma exists_finite_representatives [Fintype X] [HasPrimitiveRoot5040 E] (q : (𝔸f E)ˣ) (k : ℕ)
    {Q : Set (FinPlace E)} (hq : ∀ w : FinPlace E, w ∉ Q → v (q.val w) = 1) :
    ∃ T : Set (Gf E ι), T.Finite ∧ T ⊆ Gf.supportedOn ι Q ∧
      ∀ x : Gf E ι, Y.HasBoundedOrbit q.val k x →
        ∃ r ∈ Y.besselFin, r * x ∈ T * (stdLevel E ι : Set (Gf E ι)) := by
  -- Take one point for each `Λ'⁻` and keep its components at `Q ∪ Q̄`. Lattices with the same
  -- `Λ'⁻` are translates of each other by the unitary group of `X`, which lies in `R`.
  let B : Set (Gf E ι) := {x : Gf E ι | Y.HasLatticeBounds q.val k x}
  obtain ⟨T, hT_bounds, hT_finite, hT_image⟩ :
      ∃ T ⊆ B, T.Finite ∧ Y.latticeMinus '' B ⊆ Y.latticeMinus '' T :=
    Set.exists_subset_image_finite_and.1
      ⟨Y.latticeMinus '' B, subset_rfl, Y.finite_image_latticeMinus q k, subset_rfl⟩
  refine ⟨Gf.componentOn ι Q '' T, hT_finite.image _,
    Set.image_subset_iff.2 fun _ _ ↦ Gf.componentOn_mem_supportedOn, ?_⟩
  rintro x ⟨r, hr, -, h_bounds⟩
  obtain ⟨t, ht, h_eq⟩ : ∃ t ∈ T, Y.latticeMinus t = Y.latticeMinus (r * x) :=
    hT_image ⟨r * x, h_bounds, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : Gf E X,
      V.lattice (Y.inclXFin a * (r * x)) = V.lattice (Gf.componentOn ι Q t) :=
    exists_lattice_inclXFin_mul_eq
      (h_eq.symm.trans ((hT_bounds ht).latticeMinus_componentOn hq).symm)
  refine ⟨Y.inclXFin a * r,
    mul_mem (Y.snd_mem_besselFin (Y.inclX_mem_besselGroup (1, a))) hr, ?_⟩
  rw [mul_assoc, ← mul_inv_cancel_left (Gf.componentOn ι Q t) (Y.inclXFin a * (r * x))]
  exact Set.mul_mem_mul ⟨t, ht, rfl⟩ (Space.lattice_eq_iff.1 ha.symm)

end Grading

end New

end
