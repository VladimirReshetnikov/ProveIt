import Lib.Adelic.TraceFormula.TestFunction
import Lib.LocalGL.Green.LabelCharacters

/-!
# An irreducible label in a tuple gives a cuspidal test function

Green's class function of a monic irreducible polynomial is cuspidal: over a finite field, it has
mean zero on the unipotent radical of every proper parabolic subgroup of `GL_n` that is cut out by
coordinates. If the polynomial is a label of degree `n` (so its constant term is nonzero), it
follows that the coefficients of its idempotent have sum zero over each coset of such a radical.
Inflated to the finite adelic group, the idempotent of a tuple of polynomials, one of which is an
irreducible label, gives a test function that is cuspidal at the place of that member.

Notions from other files:
* `labelChar θ c` is the class function of Green that belongs to the polynomial `c` and the
  multiplicative character `θ`, here always the chosen `faithfulChar k`; `labelIdem n c`
  is its idempotent in the group algebra of `GL_n`, and `tupleIdem n c` the tensor product of these.
* `radicalHom` at the projector `p` on a set `T` of coordinates sends `Z` to the element
  `1 + p Z (1-p)` of the unipotent radical of the parabolic subgroup of `T`. Sums over the radical
  are taken over all matrices `Z`, so that every element is counted equally often.
* `levelOf w ⊥` is the kernel of the reduction `stdLevel.reduceFamily w` of `stdLevel E n`, the
  maximal compact subgroup of the finite adelic unitary group `Gf E n`, at the places `w i`;
  `liftResidue` is a section of that reduction.
* `convIndicator _ _ a` is the convolution of `a` with the indicator of an open compact subgroup,
  and `IsCuspidalAt _ φ` says that all translates of `φ` have sum zero over the cosets of the proper
  radicals at a split place.

## Relation to the literature

The finite-field input is part of Green's theory of the characters of `GL_n(F_q)`; see
`Lib.LocalGL.Green.TauFunctions`.
-/

open NumberField MonoidAlgebra Matrix Multiplicative Finset Polynomial

namespace New

section FiniteField

variable {n k : Type} [Fintype n] [DecidableEq n] [Field k] [Finite k]

/-- For a set `T` of coordinates, the block of a matrix with rows in `T` and columns outside `T`,
as a linear map. -/
noncomputable def upperRightBlock (T : Finset n) :
    Matrix n n k →+ (({i // i ∉ T} → k) →ₗ[k] ({i // ¬i ∉ T} → k)) :=
  AddMonoidHom.mk' (fun Z : Matrix n n k ↦ toLin' (Z.submatrix Subtype.val Subtype.val))
    fun Y Z : Matrix n n k ↦ by simp [submatrix_add]

omit [Finite k] in
/-- Every linear map from the coordinates outside `T` to those in `T` is the upper right block of
some matrix. -/
lemma upperRightBlock_surjective (T : Finset n) :
    Function.Surjective (upperRightBlock (k := k) T) := by
  intro X
  let Z : Matrix n n k := of fun i j ↦
    if h : ¬i ∉ T ∧ j ∉ T then LinearMap.toMatrix' X ⟨i, h.1⟩ ⟨j, h.2⟩ else 0
  have h_block : Z.submatrix Subtype.val Subtype.val = LinearMap.toMatrix' X := by
    ext i j; simp [Z, i.2, j.2]
  exact ⟨Z, by simp [upperRightBlock, h_block]⟩

omit [Finite k] in
/-- The element `radicalHom _ (ofAdd Z)` of the radical of `T` has the similarity class of the block
triangular endomorphism with identity blocks on the diagonal and the upper right block of `Z` off
it. -/
lemma simClassOf_radicalHom (T : Finset n) (Z : Matrix n n k) :
    simClassOf (toLin' (radicalHom (isIdempotentElem_coordProjector T) (ofAdd Z)).1) =
      simClassOf (blockTriangularEnd 1 1 (upperRightBlock T Z)) := by
  let e : {i // i ∉ T} ⊕ {i // ¬i ∉ T} ≃ n := Equiv.sumCompl (· ∉ T)
  have h_entry (i j : n) : (radicalHom (isIdempotentElem_coordProjector T) (ofAdd Z)).1 i j =
      (1 : Matrix n n k) i j + if i ∈ T ∧ j ∉ T then Z i j else 0 := by
    by_cases hi : i ∈ T <;> by_cases hj : j ∈ T <;>
      simp [coe_radicalHom, coordProjector, mul_sub, hi, hj]
  have h_blocks : (radicalHom (isIdempotentElem_coordProjector T) (ofAdd Z)).1.submatrix e e =
      fromBlocks 1 0 (Z.submatrix Subtype.val Subtype.val) 1 := by
    ext (⟨i, hi⟩ | ⟨i, hi⟩) (⟨j, hj⟩ | ⟨j, hj⟩) <;> simp [h_entry, e, one_apply] <;> grind
  rw [← simClassOf_submatrix e, h_blocks]
  -- splitting a vector into its coordinates outside and in `T` intertwines the two endomorphisms
  refine simClassOf_eq_iff.2
    ⟨LinearEquiv.sumArrowLequivProdArrow _ _ k k, fun x ↦ Prod.ext ?_ ?_⟩
  all_goals
    ext i
    simp [fromBlocks_mulVec, upperRightBlock, Function.comp_def,
      LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow]

/-- A function of the upper right block of a matrix has the same mean over all matrices as over all
linear maps. -/
lemma finMean_comp_upperRightBlock (T : Finset n)
    (f : (({i // i ∉ T} → k) →ₗ[k] ({i // ¬i ∉ T} → k)) → ℂ) :
    finMean (fun Z : Matrix n n k ↦ f (upperRightBlock T Z)) = finMean f :=
  finMean_comp_surjective (upperRightBlock T) (upperRightBlock_surjective T) f

/-- For a monic irreducible polynomial `c` over a finite field and a set `T` of coordinates that is
neither empty nor everything, Green's class function `labelChar (faithfulChar k) c` of `c`,
evaluated on `GL n k`, has mean zero on the unipotent radical of the parabolic subgroup of `T`
(the range of `radicalHom`). -/
lemma finMean_labelChar_radicalHom {c : k[X]} (hc_monic : c.Monic) (hc_irr : Irreducible c)
    {T : Finset n} (hT_empty : T ≠ ∅) (hT_univ : T ≠ univ) :
    finMean (fun Z : Matrix n n k ↦ (labelChar (faithfulChar k) c).evalGL
      (radicalHom (isIdempotentElem_coordProjector T) (ofAdd Z))) = 0 := by
  let V : Type := {i // ¬i ∉ T} → k
  let W : Type := {i // i ∉ T} → k
  let χ : Hall k := greenTau (faithfulChar k) c
  let f : (W →ₗ[k] V) → ℂ := fun X ↦ χ (simClassOf (blockTriangularEnd 1 1 X))
  have hV : Module.finrank k V ≠ 0 := by simpa [V] using hT_empty
  have hW : Module.finrank k W ≠ 0 := by
    simpa [W, Nat.sub_eq_zero_iff_le, card_lt_iff_ne_univ] using hT_univ
  calc _ = finMean fun Z : Matrix n n k ↦ f (upperRightBlock T Z) := by
        simp [f, χ, labelChar_eq_greenTau _ hc_irr hc_monic, Hall.evalGL, simClassOf_radicalHom]
    _ = χ.blockAverage (simClassOf (1 : Module.End k V)) (simClassOf (1 : Module.End k W)) :=
      (finMean_comp_upperRightBlock T f).trans (Hall.blockAverage_simClassOf χ 1 1).symm
    _ = 0 := by apply isCuspidal_greenTau <;> rwa [dim_simClassOf]

/-- For a finite field `k`, let `c` be an irreducible label of degree `card n` (a monic squarefree
polynomial of that degree with nonzero constant term), and let `labelIdem n c` be the idempotent
e_c = ∑ (Ξ_c(1)/|G|)·conj Ξ_c(g)·g of the complex group algebra ℂ[G], G = GL_n(k), where Ξ_c is the
character attached to `c`. For a proper nonempty set `T` of coordinates, let ε be the coordinate
projector onto `T`; the elements `1 + ε Z (1 - ε)` form the unipotent radical of the parabolic
subgroup keeping the span of the coordinates in `T`. Then for all `y z : GL n k`, the coefficients
of e_c at `y (1 + ε Z (1 - ε)) z` sum to zero as `Z` runs over all `n × n` matrices. -/
lemma sum_coeff_labelIdem_radicalHom {c : k[X]} (hc : IsLabel (Fintype.card n) c)
    (hc_irr : Irreducible c) {T : Finset n} (hT_empty : T ≠ ∅) (hT_univ : T ≠ univ) (y z : GL n k) :
    ∑ᶠ Z : Matrix n n k,
      (labelIdem n c).coeff (y * (radicalHom (isIdempotentElem_coordProjector T) (ofAdd Z) * z)) =
        0 := by
  let _ : Fintype (Matrix n n k) := .ofFinite _
  let χ : GL n k → ℂ := (labelChar (faithfulChar k) c).evalGL
  let U : Multiplicative (Matrix n n k) →* GL n k := radicalHom (isIdempotentElem_coordProjector T)
  -- The radical fixes no nonzero vector of the representation with character `χ`, so `χ` has sum
  -- zero over each coset.
  have h_mean : finMean (χ ∘ U *
      (Representation.trivial ℂ (Multiplicative (Matrix n n k)) ℂ).character) = 0 := by
    have h_triv : (Representation.trivial ℂ (Multiplicative (Matrix n n k)) ℂ).character = 1 := by
      ext Z; simp [Representation.character, Representation.trivial]
    rw [h_triv, mul_one]
    obtain ⟨hc_monic, -⟩ := hc
    exact finMean_labelChar_radicalHom hc_monic hc_irr hT_empty hT_univ
  have h_sum : ∑ Z : Matrix n n k, χ (U (ofAdd Z) * (z * y)) = 0 := by
    obtain ⟨h_char, -⟩ : IsIrreducibleChar χ := hc.isIrreducibleChar_labelChar (faithfulChar k)
    have h_elem : (Representation.trivial ℂ (Multiplicative (Matrix n n k)) ℂ).asAlgebraHom
        (groupAlgElem fun Z : Multiplicative (Matrix n n k) ↦ χ (U Z * (z * y))) = 0 :=
      h_char.asAlgebraHom_groupAlgElem_eq_zero U (z * y) h_mean
    -- the trivial representation sends a group algebra element to the sum of its coefficients
    simpa [asAlgebraHom_eq_sum, ← ofAdd.sum_comp] using LinearMap.congr_fun h_elem 1
  -- The coefficients are a multiple of the conjugate character, which is a class function.
  have h_coeff (u : GL n k) : (labelIdem n c).coeff (y * (u * z)) =
      χ 1 / Nat.card (GL n k) * starRingEnd ℂ (χ (u * (z * y))) := by
    have h_conj : χ (y * (u * z)) = χ (u * (z * y)) := by
      rw [show y * (u * z) = y * (u * (z * y)) * y⁻¹ by group]
      exact isClassFunction_evalGL _ y
    simp [← h_conj, labelIdem, hc, χ, groupAlgElem]
  calc ∑ᶠ Z : Matrix n n k, (labelIdem n c).coeff (y * (U (ofAdd Z) * z))
      = χ 1 / Nat.card (GL n k) *
          starRingEnd ℂ (∑ Z : Matrix n n k, χ (U (ofAdd Z) * (z * y))) := by
        simp only [finsum_eq_sum_of_fintype, h_coeff, map_sum, mul_sum]
    _ = 0 := by simp [h_sum]

end FiniteField

variable {E n ι : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] [DecidableEq n]
  {w : ι → FinPlace E} [Fintype ι]

omit [Fintype ι] in
lemma coe_mem_levelOf_bot {k : stdLevel E n} :
    k.1 ∈ levelOf w ⊥ ↔ stdLevel.reduceFamily w k = 1 := by
  rw [mem_levelOf, exists_prop_of_true k.2, Subgroup.mem_bot]

/-- For places `w i`, none conjugate to another or to itself, lift an element `a` of the group
algebra of their finite groups by `liftResidue` and convolve it with the indicator of `levelOf w ⊥`.
On the maximal compact subgroup, this test function is the coefficient function of `a`, composed
with reduction. -/
lemma convIndicator_mapDomain_liftResidue [hw : IsConjApart w]
    {hK_open : IsOpen (levelOf (n := n) w ⊥ : Set (Gf E n))}
    {hK_compact : IsCompact (levelOf (n := n) w ⊥ : Set (Gf E n))}
    (a : ℂ[∀ i : ι, GL n (ResField (w i))]) (k : stdLevel E n) :
    (convIndicator hK_open hK_compact
      (mapDomain (fun s : ∀ i : ι, GL n (ResField (w i)) ↦ (liftResidue s).1) a)).1 k.1 =
      a.coeff (stdLevel.reduceFamily w k) := by
  classical
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb =>
    simp [mapDomain_add, ha, hb]
  | single s c =>
    have h_iff : (liftResidue s).1⁻¹ * k.1 ∈ levelOf w ⊥ ↔ s = stdLevel.reduceFamily w k := by
      rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, coe_mem_levelOf_bot, map_mul, map_inv,
        reduceFamily_liftResidue, inv_mul_eq_one]
    simp [convIndicator_single, Finsupp.single_apply, h_iff]

/-- For places `w i`, none conjugate to another or to itself, the test function `convIndicator` of
an element of the group algebra of their finite groups, lifted by the section `liftResidue` of
reduction and convolved with the indicator of `levelOf w ⊥`, vanishes off the maximal compact
subgroup `stdLevel E n`. -/
lemma convIndicator_mapDomain_liftResidue_of_notMem [hw : IsConjApart w]
    {hK_open : IsOpen (levelOf (n := n) w ⊥ : Set (Gf E n))}
    {hK_compact : IsCompact (levelOf (n := n) w ⊥ : Set (Gf E n))}
    (a : ℂ[∀ i : ι, GL n (ResField (w i))]) {g : Gf E n} (hg : g ∉ stdLevel E n) :
    (convIndicator hK_open hK_compact
      (mapDomain (fun s : ∀ i : ι, GL n (ResField (w i)) ↦ (liftResidue s).1) a)).1 g = 0 := by
  classical
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb => simp [mapDomain_add, ha, hb]
  | single s c =>
    have h_notMem : (liftResidue s).1⁻¹ * g ∉ levelOf w ⊥ := fun h_mem ↦
      hg (((stdLevel E n).mul_mem_cancel_left (inv_mem (liftResidue s).2)).1
        (levelOf_le_stdLevel h_mem))
    rw [mapDomain_single, convIndicator_single, ite_eq_right h_notMem]

variable [DecidableEq ι]

/-- Let `c` be a tuple of polynomials over finite fields `k i` whose member at `x` is an irreducible
label of degree `card n` (monic, squarefree, nonzero constant term), and `T` a proper nonempty set
of coordinates. Then the coefficients of `tupleIdem n c`, the tensor product of the idempotents of
the `c i`, have sum zero over each coset of the radical of `T` in the factor at `x`. -/
lemma sum_coeff_tupleIdem_radicalHom {k : ι → Type} [∀ i : ι, Field (k i)]
    [∀ i : ι, Finite (k i)] {c : ∀ i : ι, (k i)[X]} {x : ι}
    (hc : IsLabel (Fintype.card n) (c x)) (hc_irr : Irreducible (c x))
    {T : Finset n} (hT_empty : T ≠ ∅) (hT_univ : T ≠ univ)
    (s : ∀ i : ι, GL n (k i)) (t : GL n (k x)) :
    ∑ᶠ Z : Matrix n n (k x), (tupleIdem n c).coeff
      (s * Pi.mulSingle x (radicalHom (isIdempotentElem_coordProjector T) (ofAdd Z) * t)) = 0 := by
  -- The coefficient is a product over `ι`, and only the factor at `x` depends on `Z`.
  have h_coeff (u : GL n (k x)) : (tupleIdem n c).coeff (s * Pi.mulSingle x u) =
      (labelIdem n (c x)).coeff (s x * u) * ∏ i ∈ {x}ᶜ, (labelIdem n (c i)).coeff (s i) := by
    have h_prod : (tupleIdem n c).coeff (s * Pi.mulSingle x u) = ∏ i : ι,
        (labelIdem n (c i)).coeff (s i * Pi.mulSingle (M := fun i : ι ↦ GL n (k i)) x u i) := by
      simp [tupleIdem]
    rw [h_prod, Fintype.prod_eq_mul_prod_compl x, Pi.mulSingle_eq_same]
    exact congrArg _ (prod_congr rfl fun i hi ↦ by
      simp_all [Pi.mulSingle_eq_of_ne])
  simp only [h_coeff]
  rw [← finsum_mul, sum_coeff_labelIdem_radicalHom hc hc_irr hT_empty hT_univ, zero_mul]

/-- Let `w` be a family of places, none conjugate to another or to itself, and `c` a tuple of
polynomials over their residue fields whose member at `x` is an irreducible label of degree
`card n`. Then for every element `b` of the group algebra of the finite adelic unitary group, the
product of `b` with the lift of `tupleIdem n c` by `liftResidue`, convolved with the indicator of
the kernel `levelOf w ⊥` of reduction, gives a test function that is cuspidal at the split place
`w x` (`IsCuspidalAt`: the translates have sum zero over each coset of each proper radical). -/
theorem isCuspidalAt_convIndicator_tupleIdem [hw : IsConjApart w]
    {hK_open : IsOpen (levelOf (n := n) w ⊥ : Set (Gf E n))}
    {hK_compact : IsCompact (levelOf (n := n) w ⊥ : Set (Gf E n))}
    {c : ∀ i : ι, (ResField (w i))[X]} {x : ι}
    (hc : IsLabel (Fintype.card n) (c x)) (hc_irr : Irreducible (c x)) (b : ℂ[Gf E n]) :
    IsCuspidalAt (hw.star_ne x x) (convIndicator hK_open hK_compact
      (b * mapDomain (fun s : ∀ i : ι, GL n (ResField (w i)) ↦ (liftResidue s).1)
        (tupleIdem n c))) := by
  -- Left convolution by `b` preserves cuspidality, so it suffices to treat the lifted idempotent.
  refine IsCuspidalAt.convIndicator_mul ?_ b
  intro T hT_empty hT_univ t lift h_lift g
  let u (Z : Matrix n n (ResField (w x))) : stdLevel E n :=
    ⟨ofSplitPlace (hw.star_ne x x) (lift Z), (ofSplitPlace_mem_stdLevel _ _).2 (lift Z).2⟩
  by_cases hg : g ∈ stdLevel E n
  · -- On the maximal compact subgroup the sum is that of the coefficients of the idempotent.
    lift g to stdLevel E n using hg
    have h_red (Z : Matrix n n (ResField (w x))) : stdLevel.reduceFamily w (g * u Z) =
        stdLevel.reduceFamily w g *
          Pi.mulSingle x (radicalHom (isIdempotentElem_coordProjector T) (ofAdd Z) * t) := by
      rw [map_mul, ← h_lift, ← reduceFamily_ofSplitPlace x (lift Z)]
    calc ∑ᶠ Z : Matrix n n (ResField (w x)), (convIndicator hK_open hK_compact
            (mapDomain (fun s : ∀ i : ι, GL n (ResField (w i)) ↦ (liftResidue s).1)
              (tupleIdem n c))).1 (g * u Z : stdLevel E n)
        = ∑ᶠ Z : Matrix n n (ResField (w x)), (tupleIdem n c).coeff (stdLevel.reduceFamily w g *
            Pi.mulSingle x (radicalHom (isIdempotentElem_coordProjector T) (ofAdd Z) * t)) :=
          finsum_congr fun Z ↦ by rw [convIndicator_mapDomain_liftResidue, h_red]
      _ = 0 := sum_coeff_tupleIdem_radicalHom hc hc_irr hT_empty hT_univ (stdLevel.reduceFamily w g)
        t
  · exact finsum_eq_zero_of_forall_eq_zero fun Z ↦ convIndicator_mapDomain_liftResidue_of_notMem _
      fun h_mem ↦ hg (((stdLevel E n).mul_mem_cancel_right (u Z).2).1 h_mem)

end New
