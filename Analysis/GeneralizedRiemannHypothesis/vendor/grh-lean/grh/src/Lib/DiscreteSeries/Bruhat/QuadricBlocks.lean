import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Lib.DiscreteSeries.Bruhat.FloorGroups
import Lib.General.Measure.QuadricDisintegration

/-!
# Solving the equation of a quadric in a block of coordinates

Let a hermitian form T on A^κ be the orthogonal sum of an orthonormal block and of its complement.
On a quadric in a hyperbolic plane plus T the part w of a vector outside the block is free, and the
part in the block lies on a quadric of the block, whose value is that of the given quadric minus
h(w, w). The measure of the quadric is the volume in w times the measures of these quadrics of the
block. This holds at any place, for any s-finite kernel that disintegrates the volume of the block
along its form.

## Main definitions and results
* `New.Floors.Place.IsSolvedIn`: a measure is the volume in the coordinates outside a block times
  an s-finite kernel of measures in the coordinates of the block, each of mass at most M on a box.
* `New.Floors.Place.IsDisintegration.lintegral_lintegral_comm`: on the orthogonal sum of two
  spaces, each with an s-finite kernel that disintegrates its measure, the equation of a quadric
  may be solved in either of them.
* `New.Floors.Place.IsDisintegration.isSolvedIn_quadricMeasure`: the measure of a quadric is solved
  in an orthonormal block, given an s-finite kernel on the quadrics of the block that disintegrates
  the volume and gives mass at most M to a box.

Notions from other files:
* `New.Floors.Place`: a star ring A with Haar volume, an element τ of trace one, a skew unit δ and
  a Haar measure ν on the skew elements.
* `New.Floors.Place.quadricMeasure`: the measure on the quadric h(y, y) = δ⁻¹ b in a hyperbolic
  plane plus T, the image of a product measure under `New.Floors.Place.flatChart`. Here b, the
  index of the quadric, is skew.
* `New.Floors.Place.IsDisintegration`: a family of measures on the quadrics of a form, continuous
  in the index, whose integral over the index is a given measure.

## Relation to the literature
Elementary: Tonelli's theorem and the invariance of Haar measure.
-/

noncomputable section

namespace New.Floors

open Matrix MeasureTheory Measure ProbabilityTheory ENNReal Fintype Set Sum Function FloorGroups

variable {A : Type} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P : Place A]
  {B κ : Type} [Fintype B] [Fintype κ] {S : Set A} {M : ℝ≥0∞}

/-- The vectors with all coordinates in S. -/
abbrev coordinateBox (κ : Type) (S : Set A) : Set (κ → A) := {x : κ → A | ∀ i : κ, x i ∈ S}

/-- The box of S in A^κ has volume vol(S)^(card κ). -/
lemma volume_coordinateBox (κ : Type) [Fintype κ] (S : Set A) :
    volume (coordinateBox κ S) = volume S ^ card κ := by
  have h_box : coordinateBox κ S = univ.pi fun _ : κ ↦ S := Set.ext fun x ↦ by simp
  rw [h_box, volume_pi_pi, Finset.prod_const, Finset.card_univ]

/-- An injective map to a finite type κ extends to a bijection onto κ from the disjoint union of
its source with a finite type. -/
lemma exists_equiv_comp_inr_eq {α κ : Type} [Finite κ] {j : α → κ} (hj : Injective j) :
    ∃ (η : Type) (_ : Fintype η) (e : η ⊕ α ≃ κ), e ∘ inr = j := by
  classical
  -- The bijection is the inclusion off the range of `j`, and `j` itself on α.
  let e : {k : κ // k ∉ range j} ⊕ α ≃ κ := (Equiv.sumComm _ α).trans
    (((Equiv.ofInjective j hj).sumCongr (.refl _)).trans (.sumCompl (· ∈ range j)))
  exact ⟨{k : κ // k ∉ range j}, .ofFinite _, e, funext fun _ ↦ rfl⟩

/-- The images of an s-finite measure under a measurable family of maps form an s-finite kernel. -/
lemma exists_kernel_eq_map {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (ζ : Measure Z) [SFinite ζ] {K : X × Z → Y} (hK : Measurable K) :
    ∃ l : Kernel X Y, IsSFiniteKernel l ∧ ∀ x : X, l x = ζ.map fun z : Z ↦ K (x, z) := by
  refine ⟨(Kernel.id ×ₖ Kernel.const X ζ).map K, inferInstance, fun x ↦ ?_⟩
  rw [Kernel.map_apply _ hK, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, dirac_prod,
    Measure.map_map hK measurable_prodMk_left]
  rfl

/-- Joining two vectors along a bijection of indices preserves the volume. -/
lemma measurePreserving_sumElim_comp_symm {η : Type} [Fintype η] (e : η ⊕ B ≃ κ) :
    MeasurePreserving (fun p : (η → A) × (B → A) ↦ (p.1 ⊕ᵥ p.2) ∘ e.symm) (volume.prod volume) := by
  classical
  exact (volume_measurePreserving_piCongrLeft (fun _ : η ⊕ B ↦ A) e.symm).symm.comp
    measurePreserving_sumElim

namespace Place

/-- The measure ρ on A^κ is solved in the block of coordinates `blk`: it is the volume in the other
coordinates w times measures ζ(w) in the coordinates of the block. The ζ(w) form an s-finite kernel,
and each gives mass at most M to the box of S, the vectors with all coordinates in S. -/
def IsSolvedIn (blk : B → κ) (ρ : Measure (κ → A)) (S : Set A) (M : ℝ≥0∞) : Prop :=
  ∃ (η : Type) (_ : Fintype η) (e : η ⊕ B ≃ κ) (ζ : Kernel (η → A) (B → A)),
    e ∘ inr = blk ∧ IsSFiniteKernel ζ ∧
    MeasurePreserving (fun p : (η → A) × (B → A) ↦ (p.1 ⊕ᵥ p.2) ∘ e.symm) (volume ⊗ₘ ζ) ρ ∧
    ∀ w : η → A, ζ w (coordinateBox B S) ≤ M

/-- The volume is solved in any block: it is the volume in the other coordinates times the volume in
the coordinates of the block. Any bound M for the volume of the box of S in A^B may be taken. -/
lemma isSolvedIn_volume {blk : B → κ} (h_inj : Injective blk) (hM : volume S ^ card B ≤ M) :
    IsSolvedIn blk (volume : Measure (κ → A)) S M := by
  obtain ⟨η, _, e, he⟩ := exists_equiv_comp_inr_eq h_inj
  let ζ : Kernel (η → A) (B → A) := .const _ volume
  refine ⟨η, inferInstance, e, ζ, he, inferInstance, ?_, fun _ ↦ ?_⟩
  · rw [compProd_const]
    exact measurePreserving_sumElim_comp_symm e
  · rwa [Kernel.const_apply, volume_coordinateBox]

/-- The index of the quadric h(x, x) = r: the skew element τδr − star (τδr), with τ of trace one and
δ the skew unit of the place. It is δr if r is hermitian. -/
def quadricIndex (r : A) : skewAdjoint A := skewPart (P.element * P.skewUnit * r)

/-- The index of the quadric h(x, x) = r is a measurable function of r. -/
@[fun_prop]
lemma measurable_quadricIndex : Measurable (quadricIndex : A → skewAdjoint A) := by
  unfold quadricIndex
  fun_prop

/-- For hermitian r the index `quadricIndex r` is δr, where δ is the skew unit of the place. -/
lemma coe_quadricIndex {r : A} (hr : star r = r) : (quadricIndex r : A) = P.skewUnit * r := by
  simp only [quadricIndex, star_mul', star_skewUnit, hr]
  linear_combination P.skewUnit * r * P.element_add_star

/-- Let the measures l(b) disintegrate μ along h(x, x) = x̄ᵀJx. Then ∫ G(index of h(x, x), x) dμ is
the double integral of G(b, x) against dl(b) and the Haar measure ν = `skewMeasure` of skew b. Here
the index of r is `quadricIndex r`, which is δr for hermitian r. -/
lemma IsDisintegration.lintegral_quadricIndex {μ : Measure (κ → A)} {J : Matrix κ κ A}
    {l : skewAdjoint A → Measure (κ → A)} (hl : IsDisintegration μ J l)
    {G : skewAdjoint A × (κ → A) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x : κ → A, G (quadricIndex (star x ⬝ᵥ J *ᵥ x), x) ∂μ =
      ∫⁻ b : skewAdjoint A, ∫⁻ x : κ → A, G (b, x) ∂l b ∂skewMeasure := by
  have h_index (b : skewAdjoint A) : quadricIndex (P.skewUnit⁻¹.val * b.val) = b := by
    have h_hermitian : star (P.skewUnit⁻¹.val * b.val) = P.skewUnit⁻¹.val * b.val := by simp
    ext
    rw [coe_quadricIndex h_hermitian, Units.mul_inv_cancel_left]
  simpa only [h_index] using
    hl.lintegral_eq (fun p : A × (κ → A) ↦ G (quadricIndex p.1, p.2)) (by fun_prop)

/-- Let the s-finite kernels l and l' disintegrate μ and μ' along the forms J and J', so that l(b)
lives on the vectors whose value under the form has index b (`quadricIndex`). On the quadric of
index β of the sum of the forms, one may let the first vector run freely and solve for the second,
or the reverse: the two iterated integrals agree. -/
theorem IsDisintegration.lintegral_lintegral_comm {μ : Measure (κ → A)} {μ' : Measure (B → A)}
    {J : Matrix κ κ A} {J' : Matrix B B A} {l : Kernel (skewAdjoint A) (κ → A)}
    {l' : Kernel (skewAdjoint A) (B → A)} [IsSFiniteKernel l] [IsSFiniteKernel l']
    (hl : IsDisintegration μ J l) (hl' : IsDisintegration μ' J' l') (β : skewAdjoint A)
    {f : (κ → A) × (B → A) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y : κ → A, ∫⁻ z : B → A, f (y, z) ∂l' (β - quadricIndex (star y ⬝ᵥ J *ᵥ y)) ∂μ =
      ∫⁻ z : B → A, ∫⁻ y : κ → A, f (y, z) ∂l (β - quadricIndex (star z ⬝ᵥ J' *ᵥ z)) ∂μ' := by
  let k : Kernel (skewAdjoint A × (κ → A)) (B → A) :=
    l'.comap (fun p : skewAdjoint A × (κ → A) ↦ β - p.1) (by fun_prop)
  let k' : Kernel (skewAdjoint A × (B → A)) (κ → A) :=
    l.comap (fun p : skewAdjoint A × (B → A) ↦ β - p.1) (by fun_prop)
  have h_meas : Measurable fun p : skewAdjoint A × (κ → A) ↦
      ∫⁻ z : B → A, f (p.2, z) ∂l' (β - p.1) :=
    Measurable.lintegral_kernel_prod_right (κ := k) (by fun_prop)
  have h_meas' : Measurable fun p : skewAdjoint A × (B → A) ↦
      ∫⁻ y : κ → A, f (y, p.2) ∂l (β - p.1) :=
    Measurable.lintegral_kernel_prod_right (κ := k') (by fun_prop)
  calc
    _ = ∫⁻ b : skewAdjoint A, ∫⁻ y : κ → A, ∫⁻ z : B → A, f (y, z) ∂l' (β - b) ∂l b ∂skewMeasure :=
      hl.lintegral_quadricIndex h_meas
    _ = ∫⁻ b : skewAdjoint A, ∫⁻ y : κ → A, ∫⁻ z : B → A, f (y, z) ∂l' b ∂l (β - b)
          ∂skewMeasure := by
      rw [← lintegral_sub_left_eq_self _ β]
      simp only [_root_.sub_sub_cancel]
    _ = ∫⁻ b : skewAdjoint A, ∫⁻ z : B → A, ∫⁻ y : κ → A, f (y, z) ∂l (β - b) ∂l' b ∂skewMeasure :=
      lintegral_congr fun b ↦ lintegral_lintegral_swap (by fun_prop)
    _ = _ := (hl'.lintegral_quadricIndex h_meas').symm

omit [TopologicalSpace A] [MeasureSpace A] [Place A] [Fintype B] [Fintype κ] in
/-- Let T be hermitian and let e split κ into κ₂ and B so that the basis vectors indexed by B are
orthonormal and orthogonal to the others. Then T is block diagonal along e, with block 1 on B. -/
lemma submatrix_eq_fromBlocks_one_of_orthonormal [DecidableEq B] [DecidableEq κ] {κ₂ : Type}
    {T : Matrix κ κ A} (hT : Tᴴ = T) (e : κ₂ ⊕ B ≃ κ)
    (h_orth : ∀ (i : B) (k : κ), T (e (inr i)) k = (1 : Matrix κ κ A) (e (inr i)) k) :
    T.submatrix e e = fromBlocks (T.submatrix (e ∘ inl) (e ∘ inl)) 0 0 1 := by
  have h_col (k : κ) (i : B) : T k (e (inr i)) = star ((1 : Matrix κ κ A) (e (inr i)) k) := by
    rw [← hT, conjTranspose_apply]
    exact congrArg star (h_orth i k)
  ext (i | i) (j | j)
  · rfl
  · simp [h_col]
  · simpa using h_orth i (e (inl j))
  · simpa [Matrix.one_apply] using h_orth i (e (inr j))

/-- Let T be block diagonal along e, with blocks T₂ and 1. In the flat chart of the quadric of index
β of a hyperbolic plane plus T, the part z in the second block is free, and the rest is the flat
chart of the quadric of index β − (index of h(z, z)) of the plane plus T₂. -/
lemma flatChart_sumElim_comp_symm [DecidableEq B] [DecidableEq κ] {κ₂ : Type} [Fintype κ₂]
    [DecidableEq κ₂] {T : Matrix κ κ A} {T₂ : Matrix κ₂ κ₂ A} {e : κ₂ ⊕ B ≃ κ}
    (h_split : T.submatrix e e = fromBlocks T₂ 0 0 1) (β : skewAdjoint A) (t : A) (w : κ₂ → A)
    (z : B → A) (a : skewAdjoint A) :
    flatChart T β ((t, (w ⊕ᵥ z) ∘ e.symm), a) =
      (flatChart T₂ (β - quadricIndex (star z ⬝ᵥ (1 : Matrix B B A) *ᵥ z)) ((t, w), a) ⊕ᵥ z) ∘
        ((Equiv.sumAssoc (Fin 2) κ₂ B).trans (.sumCongr (.refl (Fin 2)) e)).symm := by
  have h_form : star ((w ⊕ᵥ z) ∘ e.symm) ⬝ᵥ T *ᵥ ((w ⊕ᵥ z) ∘ e.symm) =
      star w ⬝ᵥ T₂ *ᵥ w + star z ⬝ᵥ z := by
    refine (comp_equiv_symm_dotProduct (star (w ⊕ᵥ z)) _ e).trans ?_
    rw [← submatrix_mulVec_equiv, h_split]
    simp [fromBlocks_mulVec, Function.star_sumElim, sumElim_dotProduct_sumElim]
  have h_index : (quadricIndex (star z ⬝ᵥ z)).val = P.skewUnit * star z ⬝ᵥ z :=
    coe_quadricIndex (star_dotProduct z z).symm
  funext k
  obtain ⟨(i | i) | i, rfl⟩ :=
    ((Equiv.sumAssoc (Fin 2) κ₂ B).trans (.sumCongr (.refl _) e)).surjective k
  · simp [flatChart, h_form, h_index, mul_sub, sub_sub, add_comm]
  · simp [flatChart]
  · simp [flatChart]

/-- The volume in (z, (t, w), a) is carried to that in ((t, x), a), where x joins w and z along e
and a is skew. -/
lemma measurePreserving_join_coordinates {κ₂ : Type} [Fintype κ₂] (e : κ₂ ⊕ B ≃ κ) :
    MeasurePreserving
      (fun p : (B → A) × (A × (κ₂ → A)) × skewAdjoint A ↦
        ((p.2.1.1, (p.2.1.2 ⊕ᵥ p.1) ∘ e.symm), p.2.2))
      (volume.prod (volume.prod skewMeasure)) (volume.prod skewMeasure) :=
  ((((MeasurePreserving.id volume).prod (measurePreserving_sumElim_comp_symm e)).comp
    (volume_preserving_prodAssoc.comp measurePreserving_swap)).prod (.id skewMeasure)).comp
    ((measurePreserving_prodAssoc volume volume skewMeasure).symm _)

/-- Let the measures l(b) on A^B, for skew b, disintegrate the volume along x ↦ x*x, so l(b) is the
fibre measure on x*x = δ⁻¹b with δ the skew unit of the place, and let each give mass at most M to
the box of S (vectors with all coordinates in S). For a hermitian form T on A^κ, let `blk` inject B
into indices whose rows of T are those of the identity. Then `quadricMeasure T β`, the fibre measure
dv / dh(v, v) on the quadric h(v, v) = δ⁻¹β with h a hyperbolic plane plus T, is solved in this
block: it is the volume in the other coordinates times an s-finite kernel of block measures, each of
mass at most M on the box. -/
theorem IsDisintegration.isSolvedIn_quadricMeasure [DecidableEq B] [DecidableEq κ]
    {l : Kernel (skewAdjoint A) (B → A)} [IsSFiniteKernel l]
    (hl : IsDisintegration volume (1 : Matrix B B A) l)
    (h_mass : ∀ b : skewAdjoint A, l b (coordinateBox B S) ≤ M) {T : Matrix κ κ A} (hT : Tᴴ = T)
    {blk : B → κ} (h_inj : Injective blk)
    (h_orth : ∀ (i : B) (k : κ), T (blk i) k = (1 : Matrix κ κ A) (blk i) k) (β : skewAdjoint A) :
    IsSolvedIn (inr ∘ blk) (quadricMeasure T β) S M := by
  -- Split `T` as `T₂` plus the block. In `flatChart` the part `z` in the block is free, and the
  -- rest lies on a quadric of the plane plus `T₂`. Exchange the roles of the two parts.
  classical
  obtain ⟨κ₂, _, e, rfl⟩ := exists_equiv_comp_inr_eq h_inj
  let T₂ : Matrix κ₂ κ₂ A := T.submatrix (e ∘ inl) (e ∘ inl)
  have hT₂ : T₂ᴴ = T₂ := by rw [conjTranspose_submatrix, hT]
  have h_split : T.submatrix e e = fromBlocks T₂ 0 0 1 :=
    submatrix_eq_fromBlocks_one_of_orthonormal hT e h_orth
  let ε : (Fin 2 ⊕ κ₂) ⊕ B ≃ Fin 2 ⊕ κ := (Equiv.sumAssoc ..).trans (.sumCongr (.refl _) e)
  let join (p : (Fin 2 ⊕ κ₂ → A) × (B → A)) : Fin 2 ⊕ κ → A := (p.1 ⊕ᵥ p.2) ∘ ε.symm
  have h_join : Measurable join := (measurePreserving_sumElim_comp_symm ε).measurable
  have h_chart (t : A) (w : κ₂ → A) (z : B → A) (a : skewAdjoint A) :
      flatChart T β ((t, (w ⊕ᵥ z) ∘ e.symm), a) =
        join (flatChart T₂ (β - quadricIndex (star z ⬝ᵥ 1 *ᵥ z)) ((t, w), a), z) :=
    flatChart_sumElim_comp_symm h_split β t w z a
  obtain ⟨q, _, hq⟩ : ∃ q : Kernel (skewAdjoint A) (Fin 2 ⊕ κ₂ → A), IsSFiniteKernel q ∧
      ∀ b : skewAdjoint A, q b = quadricMeasure T₂ b :=
    exists_kernel_eq_map (volume.prod skewMeasure) (measurable_flatChart (T := T₂))
  have h_dis : IsDisintegration volume (planeSumGram T₂) q := by
    rw [funext hq]
    exact isDisintegration_quadricMeasure hT₂
  let ζ : Kernel (Fin 2 ⊕ κ₂ → A) (B → A) :=
    l.comap (fun y ↦ β - quadricIndex (star y ⬝ᵥ planeSumGram T₂ *ᵥ y)) (by fun_prop)
  have h_map : (volume ⊗ₘ ζ).map join = quadricMeasure T β := by
    refine ext_of_lintegral _ fun f hf ↦ ?_
    -- Join `z` in the block and `w` outside it to one vector of A^κ.
    let coords (p : (B → A) × (A × (κ₂ → A)) × skewAdjoint A) : (A × (κ → A)) × skewAdjoint A :=
      ((p.2.1.1, (p.2.1.2 ⊕ᵥ p.1) ∘ e.symm), p.2.2)
    have h_coords : MeasurePreserving coords
        (volume.prod (volume.prod skewMeasure)) (volume.prod skewMeasure) :=
      measurePreserving_join_coordinates e
    have h_meas : Measurable fun x : (A × (κ → A)) × skewAdjoint A ↦ f (flatChart T β x) := by
      fun_prop
    calc
      ∫⁻ x, f x ∂(volume ⊗ₘ ζ).map join = ∫⁻ y, ∫⁻ z, f (join (y, z)) ∂ζ y ∂volume := by
        rw [lintegral_map hf h_join, lintegral_compProd (f := fun p ↦ f (join p)) (hf.comp h_join)]
      _ = ∫⁻ z, ∫⁻ y, f (join (y, z)) ∂q (β - quadricIndex (star z ⬝ᵥ 1 *ᵥ z)) ∂volume :=
        h_dis.lintegral_lintegral_comm hl β (hf.comp h_join)
      _ = ∫⁻ z, ∫⁻ x, f (flatChart T β (coords (z, x))) ∂volume.prod skewMeasure ∂volume := by
        refine lintegral_congr fun z ↦ ?_
        rw [hq, lintegral_map (by fun_prop) (by fun_prop)]
        exact lintegral_congr fun ⟨⟨t, w⟩, a⟩ ↦ congrArg f (h_chart t w z a).symm
      _ = ∫⁻ x, f x ∂quadricMeasure T β := by
        have h_pullback : Measurable fun p ↦ f (flatChart T β (coords p)) :=
          h_meas.comp h_coords.measurable
        rw [← lintegral_prod _ h_pullback.aemeasurable, h_coords.lintegral_comp h_meas,
          lintegral_map hf (by fun_prop)]
  exact ⟨_, inferInstance, ε, ζ, rfl, inferInstance, ⟨h_join, h_map⟩, fun _ ↦ h_mass _⟩

end Place

end New.Floors
