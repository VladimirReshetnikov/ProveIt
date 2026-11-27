import Lib.Cohomology.Hodge.DepthVanishing
import Lib.General.Groups.CongruenceSubgroups
import Lib.PadicComparison.HodgeTate.ExtCocycles

/-!
# Grothendieck's symbol [dT/T], cut-out loci and Hodge classes of points

Let `k` be a field (of characteristic zero for `symbolClass_succ`). Spaces are functors `X` from
`k`-algebras to sets. `New.Variety.HodgeH (relFreeAb U) d` is the Hodge cohomology of `X` relative
to a subfunctor `U`, and `New.Variety.offPoints s` is the complement of a set `s` of `k`-points;
`ComesFromPoints s K x` says that `x ∈ X(K)` is the image of some `z ∈ s`. Grothendieck's symbol
`New.Variety.symbolClass` is a class in the Hodge cohomology of affine d-space relative to the
complement of the origin. `[dg / g]` denotes its pull-back along a tuple of functions `g`.

## Main definitions and results

* `New.Variety.CutsOutLocus X P x f` says that the elements `f i` of `R` cut out the locus of
  `Spec R` where the point `x` of `X(R)` satisfies `P`.
* `New.Variety.symbolClass`: the class, given by the cocycle (v, l_1, …, l_d) ↦ det(l) · dT(v).
* `New.Variety.symbolClass_transformation`: the transformation law between the pull-backs along two
  tuples.
* `New.Variety.symbolClass_succ`: the class in degree d + 1 restricts to the product of the classes
  in degrees d and 1.
* `New.Variety.IsPointSum`: near each `z ∈ s`, a relative class is `n z • [dg / g]` for functions
  `g` that cut out `z`; `New.Variety.pointClass` is the image of a chosen class of multiplicity `1`.
* `New.Variety.IsPointSum.map_eq_smul_pointClass`, `New.Variety.IsPointSum.map_eq_sum_pointClass`:
  on a separated `X`, a class with support in a finite set `s` and multiplicities `n` maps to
  `∑ z ∈ s, n z • pointClass d z`. The proof is by excision for one point and by Mayer–Vietoris for
  several.

Notions from other files:
* `New.Variety.unimodular`: The subfunctor of affine d-space of vectors whose entries generate the
  unit ideal.
* `New.Variety.pointMap`: The map Hom(A, −) → Y given by a point y of Y(A) (Yoneda).
* `New.Variety.IsSeparatedFunctor`: X is separated: for x, y in X(A) there is an ideal J of A such
  that φ: A → B makes x and y equal exactly when φ kills J.
* `New.Variety.HodgeTest`: a test for Hodge cohomology over k, namely a commutative k-algebra A and
  a finite index set ι, standing for the pair (A, M) with M = A^ι.
* `New.Variety.HodgeTest.sqZeroExt`: The functor sending a pair (A, M) to the square-zero extension
  A ⊕ M, as a k-algebra.
* `New.Variety.hodgeCoeff`: The functor (A, M) ↦ ⋀_A M to abelian groups, the coefficients.
* `New.Variety.EtaleChart`: A chart of X: a k-algebra R with finitely many étale coordinates and a
  point of X(R) that embeds Spec R as an open subfunctor (its image is `a.locus`).
* `New.Variety.HodgeH`: Hodge cohomology: for a functor N from k-algebras to abelian groups, Ext^q
  from (A, M) ↦ N(A ⊕ M) to (A, M) ↦ ⋀_A M, in functors on pairs.

## Relation to the literature

Known; see `Lib.Cohomology.Hodge.FixedPointFormula` and
`Lib.Cohomology.PointClass.LinearIndependence` for sources.
-/

noncomputable section

namespace New.Variety

/-!
## Functions cutting out a locus of points, and its complement

* `New.Variety.CutsOutLocus.preimage_fieldLocus_not`: the locus where `P` fails at every field point
  pulls back to the locus where `g` is a unimodular vector.
-/

section LocusEquations

open CategoryTheory RingHom Set Ideal

variable {k : Type} [Field k] {X : CommAlg k ⥤ Type 1} {d : ℕ} {R K : CommAlg k}

/-- Let `ζ : R ⟶ k` be a `k`-point of `Spec R` and `φ : R ⟶ K` a map of `k`-algebras. If the
kernel of `ζ` lies in the kernel of `φ`, then `φ` is `ζ` followed by the structure map `k ⟶ K`. -/
lemma eq_comp_structureMap_of_ker_le {ζ : R ⟶ CommAlgCat.of k k} {φ : R ⟶ K}
    (h_ker : ker ζ.hom ≤ ker φ.hom) :
    φ = ζ ≫ structureMap := by
  ext r
  -- `r - ζ r` lies in the kernel of `ζ`, hence in that of `φ`
  have h_zero : φ (r - algebraMap k R (ζ r)) = 0 := mem_ker.mp (h_ker (by simp))
  simpa [sub_eq_zero] using h_zero

/-- The elements `f i` of `R` cut out the locus where the point `x` of `X(R)` satisfies `P`: a map
`α : R ⟶ C` kills every `f i` exactly when the image of `x` in `X(C)` satisfies `P`. -/
def CutsOutLocus (X : CommAlg k ⥤ Type 1) (P : (K : CommAlg k) → X.obj K → Prop) (x : X.obj R)
    (f : Fin d → R) : Prop :=
  ∀ (C : CommAlg k) (α : R ⟶ C), span (Set.range f) ≤ ker α.hom ↔ P C (X.map α x)

section OffPoints

variable {x : X.obj K} {s : Set (X.obj (CommAlgCat.of k k))}

/-- Let `X` be separated, `K` a field and `s` a set of `k`-points of `X`. A point `x` of `X(K)`
lies in `offPoints s`, the points none of whose images in fields comes from `s`, exactly when `x`
itself is not the image of a point of `s`. -/
lemma mem_offPoints_iff [IsSeparatedFunctor X] (hK : IsField K) :
    x ∈ offPoints s K ↔ ¬ComesFromPoints (X := X) s K x := by
  constructor
  · -- take the identity map of the field `K`
    intro hx
    simpa [X.map_id_apply] using hx K (𝟙 K) hK
  · rintro hx C φ hC ⟨z, hz, h_eq⟩
    -- `x` and the image of `z` differ over the field `K`; as `X` is separated, they stay
    -- different in the field `C`
    have hx_ne : x ≠ X.map structureMap z := fun h_eq_z ↦ hx ⟨z, hz, h_eq_z⟩
    have h_ne : X.map φ x ≠ X.map φ (X.map structureMap z) :=
      mem_offDiagonal_of_ne hK hx_ne C φ hC
    exact h_ne (h_eq.trans (map_map_structureMap φ z).symm)

end OffPoints

section CutsOut

variable {g : Fin d → R} {x : X.obj R} {P : (K : CommAlg k) → X.obj K → Prop}

/-- If `g` cuts out the locus where `x` satisfies `P`, then the preimage in `Spec R` of the locus
where `P` fails at every field point is the locus where the `g i` generate the unit ideal. -/
lemma CutsOutLocus.preimage_fieldLocus_not (h : CutsOutLocus X P x g) :
    (fieldLocus fun (K : CommAlg k) (y : X.obj K) ↦ ¬P K y).preimage (pointMap x) =
      unimodular.preimage (pointMap ⟨g⟩) := by
  ext C ⟨φ⟩
  -- Both sides say that no map `ψ` from `C` to a field kills the image of the ideal of the `g i`.
  have h_left : ⟨φ⟩ ∈ ((fieldLocus fun (K : CommAlg k) (y : X.obj K) ↦ ¬P K y).preimage
        (pointMap x)).obj C ↔
      ∀ (K : CommAlg k) (ψ : C ⟶ K), IsField K → ¬span (range g) ≤ ker (φ ≫ ψ).hom := by
    refine forall₃_congr fun K ψ _ ↦ ?_
    rw [h K (φ ≫ ψ), X.map_comp_apply]
    rfl
  have h_right : ⟨φ⟩ ∈ (unimodular.preimage (pointMap ⟨g⟩)).obj C ↔
      (span (range g)).map φ.hom = ⊤ := by
    rw [map_span, ← range_comp]
    rfl
  rw [h_left, h_right, map_eq_top_iff_forall_isField]

end CutsOut

end LocusEquations

/-!
## Grothendieck's symbol [dT/T] and its product formula

A point v of (A ⊕ M)^d off the origin has a witness: a linear form l ∈ A^d with value 1 on the
A-part of v (`New.Variety.jouanolouRel`). Points with several witnesses turn cocycles into relative
classes. The cocycle condition and the product formula are Laplace expansions
(`New.Variety.sum_minor_eq_mul_det`).

* `New.Variety.symbolClass_one`: in degree 1 the class is the boundary of dT/T.
-/

section GrothendieckSymbol

open CategoryTheory Function MonoidalCategory TensorProduct Finset Abelian Ext RingHom TrivSqZeroExt
  Matrix exteriorPower Set Ideal Fin ULift witnessed HodgeTest Comparison H TotalH freeAb

set_option backward.isDefEq.respectTransparency false

variable {k : Type} [Field k]
  {d : ℕ} {V : HodgeTest k ⥤ Type 1} (f : V ⟶ HodgeTest.sqZeroExt ⋙ affineSpace k d)

/-! ### Witnesses and the cocycle of the symbol -/

/-- For f from V to d-tuples in A ⊕ M, the subfunctor of pairs (v, l), l ∈ A^d, with l · f̄(v) = 1,
where f̄ is the A-component of f. The second factor is the functor (A, M) ↦ A^d. -/
def jouanolouRel :
    Subfunctor (V ⊗ CategoryTheory.Functor.mk (·.baseAlg) (·.fst) ⋙ affineSpace k d) where
  obj c := {(v, l) | l.down ⬝ᵥ TrivSqZeroExt.fst ∘ (f.app c v).down = 1}
  map {c c' : HodgeTest k} (φ : c ⟶ c') x hx := by
    -- apply the ring map `φ.fst` to the equation at `c`, and use that `f` is natural
    change (φ.fst ∘ x.snd.down) ⬝ᵥ fst ∘ (f.app c' (V.map φ x.fst)).down = 1
    rw [f.naturality_apply]
    have h_image := congrArg φ.fst.hom.toRingHom
      (hx : x.snd.down ⬝ᵥ TrivSqZeroExt.fst ∘ (f.app c x.fst).down = 1)
    rw [map_one, map_dotProduct] at h_image
    exact h_image

/-- A unimodular tuple v in A ⊕ M has a witness: some l ∈ A^d (a point of affine d-space over A)
has dot product 1 with the A-part of v. Here A ⊕ M is the square-zero extension of the test `c`. -/
lemma exists_jouanolouRel_of_unimodular (c : HodgeTest k)
    (v : (HodgeTest.sqZeroExt ⋙ affineSpace k d).obj c)
    (h : v ∈ ((unimodular : Subfunctor (affineSpace k d)).whisker HodgeTest.sqZeroExt).obj c) :
    ∃ l, (v, l) ∈ (jouanolouRel (𝟙 (HodgeTest.sqZeroExt ⋙ affineSpace k d))).obj c := by
  -- The A-parts of the entries of `v` generate the unit ideal, so `1` is a combination of them.
  have h_top : span (Set.range (TrivSqZeroExt.fst ∘ v.down)) = ⊤ := unimodular.map c.baseProj h
  obtain ⟨l, hl⟩ : ∃ l : Fin d → c.baseAlg, ∑ i, l i • (TrivSqZeroExt.fst ∘ v.down) i = 1 :=
    mem_span_range_iff_exists_fun.mp (h_top.ge trivial)
  exact ⟨⟨l⟩, hl⟩

variable {R : Subfunctor (V ⊗ CategoryTheory.Functor.mk (·.baseAlg) (·.fst) ⋙ affineSpace k d)}
  (ω : freeAb.obj V ⟶ hodgeCoeff) {c : HodgeTest k}

/-- The exterior algebra ⋀_A M of a test c = (A, M) as a module over A. -/
instance : Module c.baseAlg (hodgeCoeff.obj c) := module' (M := ExteriorAlgebra ..)

/-- The map (v, l_1, …, l_d) ↦ det(l_1, …, l_d)·ω(v) from the free abelian group on points v with d
witnesses l_i ∈ A^d, that is, (v, l_i) ∈ R for each i (the functor `witnessed R d`), to ⋀_A M. -/
@[simp]
def detCochain : freeAb.obj (witnessed R d) ⟶ hodgeCoeff :=
  desc (Y := witnessed R d)
    (fun c t ↦ det (fun i ↦ (t.val.snd i).down) • ω.app c (FreeAbelianGroup.of t.val.fst))
    fun c c' φ t ↦ by
      -- `φ` commutes with `det`, and `ω` is natural
      refine congrArg up (.symm ((exteriorMap_smul ..).trans (congrArg₂ _ (map_det ..) ?_)))
      exact (congrArg ULift.down (ω.naturality_apply φ (FreeAbelianGroup.of t.val.fst))).symm

/-- If every row of t has dot product 1 with f, then the signed sum over j of the minors of t
without row j and column i is f i · det t. -/
lemma sum_minor_eq_mul_det (t : Matrix (Fin (d + 1)) (Fin (d + 1)) c.baseAlg)
    (f : Fin (d + 1) → c.baseAlg) (i : Fin (d + 1)) (h : ∀ j : Fin (d + 1), t j ⬝ᵥ f = 1) :
    ∑ j : Fin d.succ, (-1) ^ (j.val + i.val) • (t.submatrix j.succAbove i.succAbove).det =
      f i * t.det := by
  -- Replacing column `i` of `t` by `t *ᵥ f`, the column of ones, multiplies the determinant by
  -- `f i`; the left side is the Laplace expansion of the new determinant along column `i`.
  have h_col : (fun j ↦ ∑ l, f l • t j l) = fun _ ↦ (1 : c.baseAlg) := by
    ext j
    simpa [dotProduct, mul_comm] using h j
  have h_scale : (t.updateCol i fun _ ↦ 1).det = f i * t.det := by
    rw [← h_col, t.det_updateCol_sum i f, smul_eq_mul]
  rw [← h_scale, Matrix.det_succ_column _ i]
  refine sum_congr rfl fun j _ ↦ ?_
  simp [submatrix_updateCol_succAbove]

/-- The map (v, l_1, …, l_d) ↦ det(l_1, …, l_d)·ω(v), on points with d witnesses for
`New.Variety.jouanolouRel` f, kills boundaries. This is the induced map on the cokernel. -/
def detCocycle : abCoker (boundary (jouanolouRel f) d) ⟶ hodgeCoeff :=
  abCoker.desc (detCochain ω) <|
    freeAb.hom_ext fun c ⟨⟨v, l⟩, hl_one⟩ ↦ by
      -- The boundary of `(v, l)` goes to the alternating sum of the `d × d` minors of `l`. Border
      -- `l` with a zero column and apply `sum_minor_eq_mul_det` there: the right side is `0`.
      have h_rows (j : Fin (d + 1)) :
          vecCons 0 (l j).down ⬝ᵥ vecCons 0 (TrivSqZeroExt.fst ∘ (f.app c v).down) = 1 := by
        have h_row : (l j).down ⬝ᵥ TrivSqZeroExt.fst ∘ (f.app c v).down = 1 := hl_one j
        simpa using h_row
      -- The minors of the bordered matrix without its new column are the minors of `l`.
      have h_minor (j : Fin (d + 1)) :
          (submatrix (fun j ↦ vecCons 0 (l j).down) j.succAbove succ).det =
            det fun i ↦ (l (j.succAbove i)).down :=
        rfl
      have h_sum :
          ∑ j : Fin (d + 1), (-1) ^ (j : ℕ) * (det fun i ↦ (l (j.succAbove i)).down) = 0 := by
        simpa [h_minor] using sum_minor_eq_mul_det (fun j ↦ vecCons 0 (l j).down) _ 0 h_rows
      -- `NatTrans.app_sum` is left out so that `sum_app_apply` evaluates the sum at the generator
      simpa [boundary, sum_app_apply, -NatTrans.app_sum, ← smul_assoc, sum_smul, reindexWitness]
        using congrArg (· • ω.app c (.of v)) h_sum

@[simp]
lemma pi_comp_detCocycle :
    abCoker.π (boundary (jouanolouRel f) d) ≫ detCocycle f ω = detCochain ω :=
  rfl

/-- The natural map from the free abelian group on (A⊕M)^d to ⋀_A M sending a tuple (a_i,m_i) to
m_1∧…∧m_d. -/
def volumeForm : freeAb.obj (HodgeTest.sqZeroExt ⋙ affineSpace k d) ⟶ hodgeCoeff :=
  desc (fun c v ↦ ⟨(ιMulti c.baseAlg d (TrivSqZeroExt.snd ∘ v.down)).val⟩) fun _ _ _ _ ↦
    congrArg up (exteriorMap_iotaMulti ..).symm

/-- The class [dT/T], in the Hodge cohomology of degree d of 𝔸^d relative to 𝔸^d ∖ 0, of the
cocycle det(l_1, …, l_d)·dT_1 ∧ … ∧ dT_d on tuples of linear forms with l_j(T) = 1. -/
def symbolClass : HodgeH (relFreeAb (unimodular : Subfunctor (affineSpace k d))) d :=
  cocycleClass exists_jouanolouRel_of_unimodular
    (detCocycle (𝟙 (HodgeTest.sqZeroExt ⋙ affineSpace k d)) volumeForm)

/-- For v ∈ A^d and a d-tuple f in A ⊕ A^ι, the map α of relative chains, defined relative to the
locus where some v i becomes a unit, sends each point σ of Hom(c, −) to the tuple σ f. -/
abbrev IsInducedByCoords (v : Fin d → c.baseAlg)
    (f : Fin d → TrivSqZeroExt c.baseAlg (c.Index → c.baseAlg))
    (α : relFreeAb (someUnitLocus v) ⟶ relFreeAb ((unimodular (d := d)).whisker sqZeroExt)) :
    Prop :=
  ∀ (C : HodgeTest k) (σ : (reprBy c).obj C), α.app C (relFreeAb.mk (someUnitLocus v) σ) =
    relFreeAb.mk (unimodular.whisker sqZeroExt) ⟨sqZeroExt.map σ.down ∘ f⟩

/-- For a test c = (A, A^ι) and a d-tuple g in A ⊕ A^ι, the subfunctor of Hom(c, −) of the maps
that make g unimodular. -/
abbrev unimodularLocus (g : Fin d → TrivSqZeroExt c.baseAlg (c.Index → c.baseAlg)) :
    Subfunctor (reprBy c) :=
  ((unimodular (d := d)).whisker sqZeroExt).preimage (pointMap ⟨g⟩)

/-- If v = M ḡ, a map that makes some v i a unit makes g unimodular. -/
lemma someUnitLocus_le_unimodularLocus {v : Fin d → c.baseAlg}
    {g : Fin d → TrivSqZeroExt c.baseAlg (c.Index → c.baseAlg)}
    {M : Matrix (Fin d) (Fin d) c.baseAlg} (hM : v = M *ᵥ fst ∘ g) :
    someUnitLocus v ≤ unimodularLocus g := by
  rintro C σ ⟨i, hi⟩
  -- The image of `∑ l, M i l * g l` lies in the span and has the unit `σ (v i)` as ring part.
  let g' : Fin d → TrivSqZeroExt C.baseAlg (C.Index → C.baseAlg) := sqZeroExt.map σ.down ∘ g
  have h_mem : ∑ l, inl (σ.down.fst (M i l)) * g' l ∈ span (Set.range g') :=
    Ideal.sum_mem _ fun l _ ↦ mul_mem_left _ _ (subset_span ⟨l, rfl⟩)
  have h_fst : (∑ l, inl (σ.down.fst (M i l)) * g' l).fst = σ.down.fst (v i) := by
    simp [g', hM, mulVec, dotProduct, fst_sum, HodgeTest.sqZeroExt]
  refine eq_top_of_isUnit_mem (span (Set.range g')) h_mem ?_
  rw [isUnit_iff_isUnit_fst, h_fst]
  exact hi

section Symbol

variable {U : Subfunctor (reprBy c)} {f g : Fin d → TrivSqZeroExt c.baseAlg (c.Index → c.baseAlg)}

/-- The symbol [η/ḡ] of a d-tuple g = (ḡ, η) in A ⊕ A^ι: the pull-back of [dT/T] along g, in the
cohomology of Hom(c, −) relative to a subfunctor U (`H N F d` is Ext^d from N to F in functors on
tests) on which g is unimodular. -/
def grothendieckSymbol (g : Fin d → TrivSqZeroExt c.baseAlg (c.Index → c.baseAlg))
    (hg : U ≤ unimodularLocus g) : H (relFreeAb U) hodgeCoeff d :=
  H.map hodgeCoeff (relFreeAb.map (U := unimodular.whisker sqZeroExt) (pointMap ⟨g⟩) hg) d
    symbolClass

/-- On U, where f is unimodular, every point σ has a linear form l ∈ A^d with value 1 at σ f. -/
lemma exists_jouanolouRel_of_le_unimodularLocus (hf : U ≤ unimodularLocus f) (C : HodgeTest k) :
    ∀ σ ∈ U.obj C, ∃ l, (σ, l) ∈ (jouanolouRel (pointMap ⟨f⟩)).obj C :=
  fun _ hσ ↦ exists_jouanolouRel_of_unimodular C _ (hf C hσ)

/-- A d-form x on A^ι, as the map σ ↦ σ x from Hom(c, −) to forms. -/
def formOfExteriorPower (x : ⋀[c.baseAlg]^d (c.Index → c.baseAlg)) :
    freeAb.obj (reprBy c) ⟶ hodgeCoeff :=
  ((homReprEquiv c hodgeCoeff).trans .ulift).symm x.val

/-- The generalized fraction [x/f̄] of a d-form x: the class, relative to a subfunctor U on which
f is unimodular, of the cocycle (σ, l) ↦ det l • σ x, where the l j take the value 1 at σ f̄. -/
def fractionClass (hf : U ≤ unimodularLocus f) :
    ⋀[c.baseAlg]^d (c.Index → c.baseAlg) →+ H (relFreeAb U) hodgeCoeff d :=
  (cocycleClass (exists_jouanolouRel_of_le_unimodularLocus hf)).comp
    (.mk' (fun x ↦ detCocycle (pointMap ⟨f⟩) (formOfExteriorPower x)) fun x y ↦
      (cancel_epi (abCoker.π _)).1 (hom_ext (by simp [formOfExteriorPower])))

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- For a test c = (A, A^ι), let `f` and `g` be d-tuples in A ⊕ A^ι with first components
f̄ = `fst ∘ f` and ḡ, and write g = (ḡ, η). Let `U` be a subfunctor of Hom(c, −) on which both `f`
and `g` are unimodular, and suppose f̄ = M ḡ for a d × d matrix `M` over A. Then for every a ∈ k,
the scaled Grothendieck symbol a • [η/ḡ] equals the generalized fraction
[a det M · η₁ ∧ ⋯ ∧ η_d / f̄], both taken in the cohomology of Hom(c, −) relative to `U`. -/
lemma smul_grothendieckSymbol_eq_fractionClass (hf : U ≤ unimodularLocus f)
    (hg : U ≤ unimodularLocus g) {M : Matrix (Fin d) (Fin d) c.baseAlg}
    (hM : fst ∘ f = M *ᵥ fst ∘ g) (a : k) :
    a • grothendieckSymbol g hg =
      fractionClass hf ((algebraMap k c.baseAlg a * M.det) • ιMulti c.baseAlg d (snd ∘ g)) := by
  -- A witness `l` for `f` at `σ` gives the witness `l ᵥ* σ M` for `g`.
  let L : HodgeTest k ⥤ Type 1 := .mk (·.baseAlg) (·.fst) ⋙ affineSpace k d
  let w : reprBy c ⊗ L ⟶ L :=
    { app C := ↾fun ((σ, l) : ULift (c ⟶ C) × L.obj C) ↦ ⟨l.down ᵥ* M.map σ.down.fst⟩
      naturality _ _ _ := by
        ext
        exact congrArg _ (funext (map_vecMul _ _ _)).symm }
  have hw (C : HodgeTest k) (x : (reprBy c ⊗ L).obj C)
      (hx : x ∈ (jouanolouRel (pointMap ⟨f⟩)).obj C) :
      ((pointMap (Y := sqZeroExt ⋙ affineSpace k d) ⟨g⟩).app C x.fst, w.app C x) ∈
        (jouanolouRel (𝟙 _)).obj C := by
    obtain ⟨⟨σ⟩, ⟨l⟩⟩ := x
    have h_map : σ.fst ∘ fst ∘ f = M.map σ.fst *ᵥ σ.fst ∘ fst ∘ g := by
      rw [hM]
      exact funext (map_mulVec _ _ _)
    change (l ᵥ* M.map σ.fst) ⬝ᵥ σ.fst ∘ fst ∘ g = 1
    rwa [← dotProduct_mulVec, ← h_map]
  -- Read `a • H.map _ _ d` as a pull-back along the comparison given by the action of `a`.
  -- `pull_cocycleClass` reduces the claim to the witnesses, the cocycles and the points.
  unfold grothendieckSymbol
  -- (`erw`: the scalar action matches `smul_eq_push` only after unfolding instances)
  erw [smul_eq_push, ← pull_id_eq_push, ← map_pull_eq_pull_map rfl, H.map_id]
  refine pull_cocycleClass exists_jouanolouRel_of_unimodular
    (exists_jouanolouRel_of_le_unimodularLocus hf) _ (pointMap ⟨g⟩) w hw
    (fun C t ↦ ?_) fun _ _ ↦ rfl
  -- The cocycles agree since `det (l * σ M) = det l * σ (det M)`.
  simp [volumeForm, formOfExteriorPower, w]
  -- (`erw`: the rows `l i ᵥ* σ M` are the product matrix only up to unfolding `Matrix.mul`)
  erw [det_mul, ← map_det]
  refine congrArg up (.trans ?_
    (congrArg (_ • ·) ((add_zero _).trans (exteriorMap_smul ..))).symm)
  simp [exteriorMap_iotaMulti, mul_smul, ← smul_comm a]
  rfl

/-- The fraction [x/f̄] vanishes when the coefficient of x lies in the ideal spanned by f̄. -/
lemma fractionClass_smul_eq_zero (hf : U ≤ unimodularLocus f) {r : c.baseAlg}
    (hr : r ∈ span (Set.range (fst ∘ f))) (m : Fin d → c.Index → c.baseAlg) :
    fractionClass hf (r • ιMulti c.baseAlg d m) = 0 := by
  -- For `ḡ` the `i`-th basis vector, `f̄ = M ḡ` with `M = updateCol 1 i f̄` of determinant `f̄ i`.
  -- As `ḡ` is unimodular everywhere, its symbol is `0`. The factor `s` is put into `η i`.
  have h_gen (i : Fin d) (s : c.baseAlg) :
      fractionClass hf ((s * (f i).fst) • ιMulti c.baseAlg d m) = 0 := by
    let g (j : Fin d) : TrivSqZeroExt c.baseAlg (c.Index → c.baseAlg) :=
      (if j = i then 1 else 0, update m i (s • m i) j)
    have hM : fst ∘ f = updateCol 1 i (fst ∘ f) *ᵥ fst ∘ g := by
      simp [g, funext_iff, mulVec, dotProduct]
    have h_top (C : HodgeTest k) (σ : (reprBy c).obj C) : σ ∈ (unimodularLocus g).obj C :=
      projSpace.span_eq_top_of_isUnit i (by
        change IsUnit (sqZeroExt.map σ.down (g i))
        simp [g, isUnit_iff_isUnit_fst, HodgeTest.sqZeroExt])
    have hg : U ≤ unimodularLocus g := fun C σ _ ↦ h_top C σ
    have h_map : relFreeAb.map (U := unimodular.whisker sqZeroExt) (pointMap ⟨g⟩) hg = 0 :=
      relFreeAb.hom_ext fun C σ ↦ relFreeAb.mk_eq_zero (h_top C σ)
    have h_frac := smul_grothendieckSymbol_eq_fractionClass hf hg hM 1
    simp only [grothendieckSymbol, h_map, H.map] at h_frac
    simpa [g, ← cramer_apply, smul_smul, Function.comp_def, mul_comm, eq_comm] using h_frac
  obtain ⟨t, rfl⟩ := mem_span_range_iff_exists_fun.1 hr
  simp [sum_smul, h_gen]

/-- Transformation law for Grothendieck symbols. Let f = (f̄, ω) and g = (ḡ, η) be d-tuples in
A ⊕ A^ι, unimodular on U, and I the ideal spanned by f̄. If f̄ = M ḡ, ω ≡ N η modulo I
coordinatewise and det N ≡ a det M modulo I with a ∈ k, then [ω/f̄] = a [η/ḡ]. -/
lemma grothendieckSymbol_transformation (hf : U ≤ unimodularLocus f) (hg : U ≤ unimodularLocus g)
    (M N : Matrix (Fin d) (Fin d) c.baseAlg) (a : k) (hM : fst ∘ f = M *ᵥ fst ∘ g)
    (hN : ∀ (i : Fin d) (j : c.Index),
      (f i).snd j - ∑ l, N i l * (g l).snd j ∈ span (Set.range (fst ∘ f)))
    (ha : N.det - algebraMap k c.baseAlg a * M.det ∈ span (Set.range (fst ∘ f))) :
    grothendieckSymbol f hf = a • grothendieckSymbol g hg := by
  -- Both sides are fractions with denominator `f̄`, and their numerators agree modulo `I`.
  have h_left : grothendieckSymbol f hf = fractionClass hf (ιMulti c.baseAlg d (snd ∘ f)) := by
    simpa using smul_grothendieckSymbol_eq_fractionClass hf hf (one_mulVec _).symm 1
  -- The coordinates of `ω₁ ∧ ⋯ ∧ ω_d - (a * det M) • η₁ ∧ ⋯ ∧ η_d` are differences of minors.
  -- Modulo `I` the minor of `ω` is `det N` times the minor of `η`, and `det N ≡ a * det M`.
  have h_minor (s : Fin d → c.Index) :
      (Matrix.of fun i j ↦ (f i).snd (s j)).det -
        algebraMap k c.baseAlg a * M.det * (Matrix.of fun i j ↦ (g i).snd (s j)).det ∈
          span (Set.range (fst ∘ f)) := by
    rw [← Ideal.Quotient.eq]
    set toQuot : c.baseAlg →+* c.baseAlg ⧸ span (Set.range (fst ∘ f)) := Ideal.Quotient.mk _
    -- Modulo `I`, the matrix of the `ω i (s j)` is `N` times the matrix of the `η i (s j)`.
    have h_rows : (Matrix.of fun i j ↦ (f i).snd (s j)).map toQuot =
        (N * Matrix.of fun i j ↦ (g i).snd (s j)).map toQuot := by
      ext i j
      exact Ideal.Quotient.eq.mpr (hN i (s j))
    have ha_quot : toQuot N.det = toQuot (algebraMap k c.baseAlg a * M.det) :=
      Ideal.Quotient.eq.mpr ha
    have h_det : toQuot (Matrix.of fun i j ↦ (f i).snd (s j)).det =
        toQuot N.det * toQuot (Matrix.of fun i j ↦ (g i).snd (s j)).det := by
      rw [← map_mul, ← det_mul, RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply,
        RingHom.mapMatrix_apply, h_rows]
    rw [h_det, ha_quot, ← map_mul]
  rw [h_left, smul_grothendieckSymbol_eq_fractionClass hf hg hM, ← sub_eq_zero, ← map_sub]
  -- Expand the difference of the numerators in the basis of `d`-fold wedges; by `h_minor` each
  -- coefficient lies in `I`, so each summand has fraction `0`.
  rw [← ((Pi.basisFun c.baseAlg c.Index).exteriorPower d).sum_repr
    (ιMulti c.baseAlg d (snd ∘ f) -
      (algebraMap k c.baseAlg a * M.det) • ιMulti c.baseAlg d (snd ∘ g))]
  simpa [basis_repr_apply, ιMulti_family] using
    sum_eq_zero fun s _ ↦ fractionClass_smul_eq_zero hf (h_minor _) _

/-- A map of relative chains induced by the tuple f = (f̄, ω) pulls [dT/T] back to [ω/f̄]. -/
lemma IsInducedByCoords.map_symbolClass {v : Fin d → c.baseAlg}
    {α : relFreeAb (someUnitLocus v) ⟶ relFreeAb ((unimodular (d := d)).whisker sqZeroExt)}
    (hα : IsInducedByCoords v f α) (hf : someUnitLocus v ≤ unimodularLocus f) :
    H.map hodgeCoeff α d symbolClass = grothendieckSymbol f hf := by
  have h_map : α = relFreeAb.map (U := unimodular.whisker sqZeroExt) (pointMap ⟨f⟩) hf :=
    relFreeAb.hom_ext hα
  rw [h_map, grothendieckSymbol]

/-! ### Transformation law -/

/-- Transformation law for Grothendieck symbols, for maps α and β of relative chains induced by
f = (f̄, ω) and g = (ḡ, η). Let v = f̄ and let I be the ideal spanned by v. If v = M ḡ, ω ≡ N η
modulo I coordinatewise and det N ≡ a det M modulo I with a ∈ k, then the pull-back of [dT/T]
along α is a times its pull-back along β. -/
lemma symbolClass_transformation {v : Fin d → c.baseAlg}
    {α β : relFreeAb (someUnitLocus v) ⟶ relFreeAb ((unimodular (d := d)).whisker sqZeroExt)}
    (hα : IsInducedByCoords v f α) (hβ : IsInducedByCoords v g β) (hf : fst ∘ f = v)
    (M N : Matrix (Fin d) (Fin d) c.baseAlg) (a : k) (hM : v = M *ᵥ fst ∘ g)
    (hN : ∀ (i : Fin d) (j : c.Index),
      (f i).snd j - ∑ l, N i l * (g l).snd j ∈ span (Set.range v))
    (ha : N.det - algebraMap k c.baseAlg a * M.det ∈ span (Set.range v)) :
    H.map hodgeCoeff α d symbolClass = a • H.map hodgeCoeff β d symbolClass := by
  subst hf
  have hf_le : someUnitLocus (fst ∘ f) ≤ unimodularLocus f :=
    someUnitLocus_le_unimodularLocus (one_mulVec _).symm
  have hg_le : someUnitLocus (fst ∘ f) ≤ unimodularLocus g := someUnitLocus_le_unimodularLocus hM
  rw [hα.map_symbolClass hf_le, hβ.map_symbolClass hg_le]
  exact grothendieckSymbol_transformation hf_le hg_le M N a hM hN ha

end Symbol

section

variable (k : Type) [Field k] (d : ℕ)

/-! ### Product formula -/

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- In degree 1 the symbol is a boundary: there is a form ω on the complement of the origin in 𝔸^1
with (a) ω(a + m) = w for some w with a w = m, that is ω = dT/T, and (b) `New.Variety.symbolClass`
of degree 1 is the image of ω under the connecting map of 0 → ℤ[𝔸^1 ∖ 0] → ℤ[𝔸^1] → ℤ[𝔸^1]/ℤ[𝔸^1 ∖
0] → 0. -/
lemma symbolClass_one :
    ∃ ω : HodgeTest.sqZeroExt ⋙ freeAb.obj (unimodular : Subfunctor (affineSpace k 1)).toFunctor ⟶
        hodgeCoeff,
    -- (a)
    (∀ (c : HodgeTest k) (v : unimodular.toFunctor.obj (HodgeTest.sqZeroExt.obj c)),
      ∃ w : c.Index → c.baseAlg, (v.val.down 0).fst • w = (v.val.down 0).snd ∧
        ω.app c (FreeAbelianGroup.of v) = ⟨ExteriorAlgebra.ι c.baseAlg w⟩) ∧
    -- (b)
    symbolClass (k := k) (d := 1) = (relFreeAb.shortExact
      (unimodular.whisker HodgeTest.sqZeroExt)).2.extClass.comp (Ext.mk₀ ω) rfl := by
  -- `symbolClass` is `fromRel` followed by the extension class of `shortExact_boundaryFromCoker`
  -- and the cocycle `detCocycle _ volumeForm`. `exists_map_extClass_comp` moves it to the sequence
  -- of `relFreeAb` (`h_class`) and produces `ω`: its value at `v` is that of the cocycle at any
  -- chain with boundary `v` (`hω`).
  obtain ⟨ω, hω, h_class⟩ := exists_map_extClass_comp (relFreeAb.shortExact _).2
    shortExact_boundaryFromCoker.2 (detCocycle (𝟙 (sqZeroExt ⋙ affineSpace k 1)) volumeForm)
    (.mk₀ (𝟙 _)) _ (fromRel exists_jouanolouRel_of_unimodular) rfl
  refine ⟨ω, fun c v ↦ ?_, by
    simp_all [symbolClass, cocycleClass_apply, universalClass_succ, universalClass_zero, push]⟩
  -- Write `v = a + m`. A witness `l` has `l * a = 1`, so `w = l • m` is "`m / a`".
  obtain ⟨l, hl⟩ := exists_jouanolouRel_of_unimodular _ _ v.2
  have hl_one : l.down 0 * (v.val.down 0).fst = 1 := (Fin.sum_univ_one _).symm.trans hl
  refine ⟨l.down 0 • (v.val.down 0).snd, ?_,
    .symm (hω c _ _ ⟨⟦.of ⟨(v.1, fun _ ↦ l), fun _ ↦ hl⟩⟧, ?_, ?_⟩)⟩
  · rw [smul_smul, mul_comm, hl_one, one_smul]
  · -- the boundary of `v` with the one witness `l` is `v` with no witness
    with_unfolding_all congrm .of ⟨⟨_, $(funext nofun)⟩, _⟩
  · -- the cocycle sends it to `det l • volumeForm v = l • ι m`
    refine congrArg up ?_
    simp [volumeForm]
    rfl

/-- The natural map 𝔸^d × 𝔸^1 → 𝔸^{d+1} appending a last coordinate. -/
@[simp]
def affineSpace.snoc : affineSpace k d ⊗ affineSpace k 1 ⟶ affineSpace k d.succ where
  app _ := ↾fun v ↦ ⟨Fin.snoc v.1.1 (v.2.1 0)⟩
  naturality := by aesop_cat (add simp [affineSpace, comp_snoc])

/-- The subfunctor of 𝔸^d × 𝔸^1 of the pairs (v, x) in which v or x is unimodular, that is, has
entries that generate the unit ideal. -/
abbrev unimodularSup : Subfunctor (affineSpace k d ⊗ affineSpace k 1) :=
  (unimodular (d := d)).preimage
      (CartesianMonoidalCategory.fst (affineSpace k d) (affineSpace k 1)) ⊔
    (unimodular (d := 1)).preimage
      (CartesianMonoidalCategory.snd (affineSpace k d) (affineSpace k 1))

/-- If v or x is unimodular, then so is the tuple (v, x) ∈ 𝔸^(d+1) obtained by appending x to v:
the entries of v, and the entry of x, are among its entries. -/
lemma unimodularSup_le_preimage_snoc :
    unimodularSup k d ≤ unimodular.preimage (affineSpace.snoc k d) := by
  rintro A ⟨v, x⟩ (hv | hx)
  · refine eq_top_mono (span_mono ?_) hv
    rintro _ ⟨i, rfl⟩
    exact ⟨i.castSucc, snoc_castSucc (α := fun _ ↦ A) (x.down 0) v.down i⟩
  · refine eq_top_mono (span_mono ?_) hx
    rintro _ ⟨i, rfl⟩
    obtain rfl : i = 0 := Subsingleton.elim i 0
    exact ⟨last d, snoc_last (α := fun _ ↦ A) (x.down 0) v.down⟩

/-- For a test (A, M) and a pair (v, x) ∈ 𝔸^d × 𝔸^1 with entries in A ⊕ M, the subfunctor of the
pairs ((v, x), l) in which l ∈ A^(d+1) has dot product 1 with the A-part of the tuple (v, x) and
the last entry of l is 0 unless x is unimodular. -/
abbrev snocRel :
    Subfunctor ((sqZeroExt ⋙ (affineSpace k d ⊗ affineSpace k 1 : CommAlg k ⥤ Type 1)) ⊗
      ((.mk (·.baseAlg) (·.fst) : HodgeTest k ⥤ CommAlg k) ⋙ affineSpace k d.succ)) :=
  jouanolouRel (sqZeroExt.whiskerLeft (affineSpace.snoc k d)) ⊓
    { obj c := {p | p.fst.snd ∈ (unimodular.whisker sqZeroExt).obj c ∨ p.snd.down (last d) = 0}
      map φ _ hx := hx.imp ((unimodular.whisker sqZeroExt).map φ ·) fun h_last ↦ by
        simpa using! congrArg φ.fst h_last }

end

section

variable {k : Type} [Field k] {d : ℕ} {c : HodgeTest k}

/-- Every pair x = (v, x₁) over a test c = (A, M) in which v or x₁ is unimodular has a witness
l ∈ A^(d+1) for `snocRel`: a witness of v followed by 0 if v is unimodular, a witness of the tuple
(v, x₁) if x₁ is. -/
lemma exists_snocRel (c : HodgeTest k) :
    ∀ x : (sqZeroExt ⋙ (affineSpace k d ⊗ affineSpace k 1)).obj c,
      x ∈ ((unimodularSup k d).whisker sqZeroExt).obj c → ∃ l, (x, l) ∈ (snocRel k d).obj c := by
  rintro x (hv | hx)
  · -- a witness `l` of `v`, followed by `0`
    obtain ⟨l, hl⟩ := exists_jouanolouRel_of_unimodular _ _ hv
    refine ⟨⟨snoc l.down 0⟩, ?_, by simp⟩
    -- the dot product splits off the last entry, where the witness is `0`
    have h_dot : ∑ i, l.down i * TrivSqZeroExt.fst (x.fst.down i) = 1 := hl
    exact (sum_univ_castSucc _).trans (by simpa using h_dot)
  · -- a witness of the unimodular tuple `(v, x₁)`
    obtain ⟨l, hl⟩ :=
      exists_jouanolouRel_of_unimodular _ _ (unimodularSup_le_preimage_snoc k d _ (.inr hx))
    exact ⟨l, hl, .inl hx⟩

/-- Let V be a functor from tests to sets, G a subfunctor, x a point of V over the test c, and [x]
its class in ℤ[V]/ℤ[G]. For a and b in an abelian group B, a ⊗ [x] = b ⊗ [x] as soon as x ∉ G
implies a = b, since [x] = 0 when x ∈ G. -/
lemma relFreeAb.tmul_mk_congr {V : HodgeTest k ⥤ Type 1} {c : HodgeTest k} {G : Subfunctor V}
    {B : Ab.{1}} {x : V.obj c} {a b : B} (h_eq : x ∉ G.obj c → a = b) :
    a ⊗ₜ[ℤ] relFreeAb.mk G x = b ⊗ₜ[ℤ] relFreeAb.mk G x := by
  by_cases hx_mem : x ∈ G.obj c
  · simp [relFreeAb.mk_eq_zero hx_mem]
  · rw [h_eq hx_mem]

/-- The first d coordinates v of a point (v, x) ∈ 𝔸^d × 𝔸^1 with m witnesses for `snocRel`. -/
abbrev snocRel.firstPoint {m : ℕ} (t : (witnessed (snocRel k d) m).obj c) :
    (sqZeroExt ⋙ affineSpace k d).obj c :=
  t.val.fst.fst

/-- The last coordinate x of a point (v, x) ∈ 𝔸^d × 𝔸^1 with m witnesses for `snocRel`. -/
abbrev snocRel.lastPoint {m : ℕ} (t : (witnessed (snocRel k d) m).obj c) :
    (sqZeroExt ⋙ affineSpace k 1).obj c :=
  t.val.fst.snd

/-- Let t be a point (v, x) with m witnesses for `snocRel`. If x is not unimodular, the last entry
of each witness is 0, and dropping it gives m witnesses for v. -/
def snocRel.dropLast {m : ℕ} (t : (witnessed (snocRel k d) m).obj c)
    (hx : lastPoint t ∉ (unimodular.whisker sqZeroExt).obj c) :
    (witnessed (jouanolouRel (𝟙 (sqZeroExt ⋙ affineSpace k d))) m).obj c :=
  ⟨(firstPoint t, fun i ↦ ⟨init (t.val.snd i).down⟩), fun i ↦ by
    have h_last : (t.val.snd i).down (last d) = 0 := (t.property i).right.resolve_left hx
    simpa [h_last] using! (sum_univ_castSucc _).symm.trans (t.property i).left⟩

end

section

variable (k : Type) [Field k] (d : ℕ)

open scoped Classical in
/-- The map of chains that sends a point (v, x) with m witnesses l for `snocRel` to
(v, init l) ⊗ [x], where init l drops the last entry of each witness and [x] is the class of x in
ℤ[𝔸^1]/ℤ[unimodular points]. It is 0 when x is unimodular. -/
def snocRel.split (m : ℕ) : freeAb.obj (witnessed (snocRel k d) m) ⟶
    (abTensor.flip.obj (relFreeAb ((unimodular (d := 1)).whisker sqZeroExt))).obj
      (freeAb.obj (witnessed (jouanolouRel (𝟙 (sqZeroExt ⋙ affineSpace k d))) m)) :=
  desc
    (fun c t ↦
      (if hx : lastPoint t ∈ (unimodular.whisker sqZeroExt).obj c then 0 else .of (dropLast t hx))
        ⊗ₜ relFreeAb.mk (unimodular.whisker sqZeroExt) (lastPoint t))
    fun _ _ φ t ↦ relFreeAb.tmul_mk_congr fun hx ↦ by
      erw [dite_eq_right hx, dite_eq_right fun h ↦ hx ((unimodular.whisker sqZeroExt).map φ h)]
      rfl

/-- The maps `snocRel.split` commute with reindexing the witnesses along g : Fin m → Fin n. -/
lemma snocRel.reindexWitness_comp_split (m n : ℕ) (g : Fin m → Fin n) :
    freeAb.map (reindexWitness (snocRel k d) g) ≫ split k d m =
      split k d n ≫ (abTensor.flip.obj (relFreeAb (unimodular.whisker sqZeroExt))).map
        (freeAb.map (reindexWitness (jouanolouRel (𝟙 (sqZeroExt ⋙ affineSpace k d))) g)) := by
  refine hom_ext fun c t ↦ relFreeAb.tmul_mk_congr fun hx ↦ ?_
  -- For `x` not unimodular, both sides are `dropLast` of the reindexed point.
  rw [dite_eq_right hx, dite_eq_right (show lastPoint t ∉ (unimodular.whisker sqZeroExt).obj c
    from hx)]
  rfl

/-- The cochain on points (v, x) with d witnesses l for `snocRel` that sends ((v, x), l) to
((-1)^d det(init l) · dT(v)) ⊗ [x]. Here init l drops the last entry of each witness, dT(v) is
`New.Variety.volumeForm` at v, and [x] is the generator of ℤ[𝔸^1] at x. -/
def snocRel.detTensor : freeAb.obj (witnessed (snocRel k d) d) ⟶
    (abTensor.obj hodgeCoeff).obj (freeAb.obj (sqZeroExt ⋙ affineSpace k 1)) :=
  desc
    (fun c ⟨⟨⟨v, x⟩, l⟩, _⟩ ↦ ((-1) ^ d • (detCochain (R := ⊤) volumeForm).app c
      (.of ⟨(v, fun i ↦ ⟨init (l i).down⟩), by simp⟩)) ⊗ₜ .of x)
    fun _ _ _ _ ↦ .symm congr($(((_ : ℤ) • detCochain _).naturality_apply ..) ⊗ₜ _).symm

end

section

variable {k : Type} [Field k] {d : ℕ} {c : HodgeTest k}

/-- Work over tests `(A, M)` and let ω be a form on the unimodular points x = a + m of 𝔸^1 with
ω(x) = w for some w with a • w = m, that is, the form dT/T. Let t be a point (v, x) ∈ 𝔸^d × 𝔸^1
with d + 1 witnesses l for `snocRel`: each l ∈ A^(d+1) has dot product 1 with the A-part of (v, x),
and its last entry is 0 unless x is unimodular. Apply `detTensor`, the cochain
((v, x), l) ↦ ((-1)^d det(init l) · dT(v)) ⊗ [x], to the boundary of t, the alternating sum over
dropping one witness. The result is the image of a tensor s in ⋀_A M ⊗ ℤ[unimodular points of 𝔸^1],
and applying ω to the second factor of s and multiplying in ⋀_A M gives det l · dT(v, x), with dT
the `volumeForm` on 𝔸^(d+1). -/
lemma snocRel.exists_detTensor_boundary_eq
    {ω : freeAb.obj ((unimodular (d := 1)).whisker sqZeroExt).toFunctor ⟶ hodgeCoeff}
    (hω : ∀ (c : HodgeTest k) (x : ((unimodular (d := 1)).whisker sqZeroExt).toFunctor.obj c),
      ∃ w : c.Index → c.baseAlg, (x.val.down 0).fst • w = (x.val.down 0).snd ∧
        ω.app c (.of x) = ⟨.ι c.baseAlg w⟩)
    (t : (witnessed (snocRel k d) (d + 1)).obj c) :
    ∃ s, ((abTensor.obj hodgeCoeff).map (freeAb.map (unimodular.whisker sqZeroExt).ι)).app c s =
        (detTensor k d).app c ((boundary (snocRel k d) d).app c (.of t)) ∧
      ((abTensor.obj hodgeCoeff).map ω ≫ exteriorAlg.mulPairing).app c s =
        det (fun i ↦ (t.val.snd i).down) • volumeForm.app c
          (.of ((sqZeroExt.whiskerLeft (affineSpace.snoc k d)).app c t.val.fst)) := by
  obtain ⟨⟨⟨v, x⟩, l⟩, hl⟩ := t
  -- As all `l i` take the value `1` at `(v, x)`, the signed sum of the minors of `l` without the
  -- last column is `a * det l`, with `a` the ring part of `x`.
  let A : Matrix (Fin d.succ) (Fin d.succ) c.baseAlg := fun i ↦ (l i).down
  let a : c.baseAlg :=
    (fst ∘ ((sqZeroExt.whiskerLeft (affineSpace.snoc k d)).app c (v, x)).down) (last d)
  have h_laplace : ∑ j : Fin d.succ, (-1) ^ (j.val + (last d).val) •
      (A.submatrix j.succAbove (last d).succAbove).det = a * A.det :=
    sum_minor_eq_mul_det A _ (last d) fun i ↦ (hl i).left
  -- Expand the boundary as an alternating sum and apply `detTensor` term by term.
  have h_boundary :
      (detTensor k d).app c ((boundary (snocRel k d) d).app c (.of ⟨((v, x), l), hl⟩)) =
        ((a * A.det) • volumeForm.app c (.of v)) ⊗ₜ[ℤ] FreeAbelianGroup.of x := by
    have h_sum := congrArg (fun r ↦ (r • volumeForm.app c (.of v)) ⊗ₜ[ℤ] FreeAbelianGroup.of x)
      h_laplace
    conv in (boundary ..).app _ _ => erw [sum_app_apply]
    -- (`using!` sees through the match in `detTensor` on the reindexed points.)
    simpa [detTensor, A, sum_smul, sum_tmul, pow_add, mul_zsmul, -zsmul_eq_mul] using! h_sum
  rw [h_boundary]
  by_cases hx : x ∈ (unimodular.whisker sqZeroExt).obj c
  · -- Here `ω x = ι w` with `a • w` the module part of `x`; hence `volumeForm (v, x)` is
    -- `a • volumeForm v * ι w`.
    obtain ⟨w, hw, hωx⟩ := hω c ⟨x, hx⟩
    refine ⟨_ ⊗ₜ .of ⟨x, hx⟩, rfl, congrArg up ?_⟩
    simp [volumeForm, ExteriorAlgebra.ιMulti, ↓List.ofFn_succ', a, smul_smul, ← hw, mul_comm]
    -- `erw`, because `hωx` is stated on the subtype of unimodular points.
    erw [hωx]
  · -- Otherwise the last column of `l` vanishes, and so do both sides.
    have h_det : det (fun i ↦ (l i).down) = 0 :=
      det_eq_zero_of_column_eq_zero (last d) fun i ↦ (hl i).right.resolve_left hx
    refine ⟨0, ?_, ?_⟩
    · simp [A, h_det]
    · simp [h_det]

end

section

variable (k : Type) [Field k] [CharZero k] (d : ℕ)

/-- The symbol is multiplicative. On 𝔸^d × 𝔸^1, relative to the pairs (v, x) with v or x
unimodular, the product of [dT/T] in degrees d and 1 is the restriction of [dT/T] in degree
d + 1. -/
lemma symbolClass_succ :
    ∃ h_le : unimodularSup k d ≤ unimodular.preimage (affineSpace.snoc k d),
      HodgeH.map (relFreeAb.prod (unimodular (d := d)) (unimodular (d := 1)))
          (cup exteriorAlg.mulPairing (symbolClass (k := k) (d := d)) symbolClass
            (add_comm 1 d) :) =
        HodgeH.map (relFreeAb.map (affineSpace.snoc k d) h_le) symbolClass := by
  -- Write the class in degree `1` as a connecting class and move it past the class in degree `d`.
  -- With the witnesses `snocRel` the product becomes the class of a cocycle `z` on `d + 1`
  -- witnesses, and Laplace expansion shows that `z` is the pull-back of the determinant cocycle.
  obtain ⟨ω, hω, h_one⟩ := symbolClass_one k
  rw [h_one]
  refine ⟨unimodularSup_le_preimage_snoc k d, ?_⟩
  let G : Subfunctor (sqZeroExt ⋙ affineSpace k 1) := unimodular.whisker sqZeroExt
  -- The maps `split` are compatible with `fromRel` and with reindexing. So
  -- `(-1) ^ d • (symbolClass ⊗ relFreeAb G)` pulls back to the class of a cocycle `y`.
  obtain ⟨y, hy, h_coc⟩ := map_cocycleClass exists_jouanolouRel_of_unimodular exists_snocRel
    (abTensor.flip.obj (relFreeAb G)) ((-1) ^ d • 𝟙 _)
    (α := sqZeroExt.whiskerLeft (relFreeAb.prod unimodular unimodular)) (snocRel.split k d)
    (fun c x ↦ relFreeAb.tmul_mk_congr fun hx ↦
      .symm (congrArg _ ((dite_eq_right hx).trans congr(.of ⟨⟨_, $(funext nofun)⟩, _⟩))))
    (snocRel.reindexWitness_comp_split k d) (detCocycle _ volumeForm)
  -- The cochain `detTensor` lifts `y` to the sequence of `G` tensored with `hodgeCoeff`. So `y`
  -- followed by the connecting class and `β` is the class of a cocycle `z`.
  have hS := (relFreeAb.shortExact G).2.map_of_exact (abTensor.obj hodgeCoeff)
  let β : (abTensor.obj hodgeCoeff).obj (freeAb.obj G.toFunctor) ⟶ hodgeCoeff :=
    (abTensor.obj hodgeCoeff).map ω ≫ exteriorAlg.mulPairing
  have h_lift_y : abCoker.π (boundary (snocRel k d) d) ≫ y =
      snocRel.detTensor k d ≫ (abTensor.obj hodgeCoeff).map (relFreeAb.π G) :=
    hy.trans (hom_ext fun c t ↦ relFreeAb.tmul_mk_congr fun hx ↦
      congrArg _ (congrArg _ (dite_eq_right hx)))
  obtain ⟨z, hz, h_lift⟩ := exists_map_extClass_comp shortExact_boundaryFromCoker.2 hS β
    (universalClass exists_snocRel d) (snocRel.detTensor k d) y h_lift_y
  -- The cocycle `z` sends `((v, x), l)` to `det l • volumeForm (v, x)`.
  have hz_val (c : HodgeTest k) (t : (witnessed (snocRel k d) (d + 1)).obj c) :
      det (fun i ↦ (t.val.snd i).down) • volumeForm.app c
          (.of ((sqZeroExt.whiskerLeft (affineSpace.snoc k d)).app c t.val.fst)) =
        z.app c ((abCoker.π (boundary (snocRel k d) (d + 1))).app c (.of t)) :=
    hz c _ _ (snocRel.exists_detTensor_boundary_eq hω t)
  calc
    _ = (cocycleClass exists_snocRel y).comp (hS.extClass.comp (.mk₀ β) rfl) rfl := by
      -- In total Ext, moving the connecting class past `symbolClass` costs the sign `(-1) ^ d`.
      have h_sign := extClass_sign_comm (abTensor_shortExact (relFreeAb.shortExact G).2)
        (symbolClass (k := k) (d := d))
      have map_comp {N N' F F' : AbFunctor (HodgeTest k)} (α : N' ⟶ N) (x : H N F d)
          (ε : H F F' 1) :
          (H.map F α d x).comp ε rfl = H.map F' α (d + 1) (x.comp ε rfl) := by
            simp [H.map, Ext.comp_assoc (h₂₃ := rfl)]
      rw [← h_coc, map_comp]
      refine congrArg _ (.symm ?_)
      apply DirectSum.of_injective (β := H _ hodgeCoeff)
      rw [← comp_of, ← of_comp_homClass]
      refine .trans ?_ (cup_of exteriorAlg.mulPairing symbolClass _ (add_comm 1 d))
      rw [← comp_of _ (mk₀ ω), cup_comp_homClass_right, TotalH.cup]
      rcases neg_one_pow_eq_or ℤ d with h_parity | h_parity <;>
        simpa [h_parity, β, TotalH.comp_assoc, -Functor.flip_obj_obj, ← comp_of, TotalH.homClass,
          ← homClass_comp, mapExactFunctor_extClass] using!
          congrArg ((-1 : ℤ) ^ d • ·) (comp_assoc_of_eq h_sign _)
    _ = cocycleClass exists_snocRel z := h_lift
    _ = (Comparison.id _).pull (sqZeroExt.whiskerLeft (relFreeAb.map (affineSpace.snoc k d)
          (unimodularSup_le_preimage_snoc k d))) (d + 1) symbolClass :=
      (pull_cocycleClass exists_jouanolouRel_of_unimodular exists_snocRel _
        (sqZeroExt.whiskerLeft (affineSpace.snoc k d)) { app _ := ↾Prod.snd }
        (fun _ _ ↦ And.left)
        (by exact fun c t ↦ (FreeAbelianGroup.lift_apply_of _ _).trans (hz_val c t))
        (by exact fun _ _ ↦ rfl)).symm
    _ = _ := congr($(id_pull _) _ _)

/-- The product formula in natural form: restricted to the pairs (v, x) with v or x unimodular,
the cup product of [dT/T] in degrees d and 1 is the pull-back of [dT/T] in degree d + 1 along
the map (v, x) ↦ (v, x) ∈ 𝔸^(d+1). -/
lemma map_cup_symbolClass_eq_map_symbolClass :
    HodgeH.map (relFreeAb.prod (unimodular (d := d)) (unimodular (d := 1)))
        (cup exteriorAlg.mulPairing (symbolClass (k := k) (d := d)) symbolClass
          (add_comm 1 d) :) =
      HodgeH.map (relFreeAb.map (affineSpace.snoc k d) (unimodularSup_le_preimage_snoc k d))
        symbolClass := by
  obtain ⟨_, h_eq⟩ := symbolClass_succ k d
  exact h_eq

end

end GrothendieckSymbol

/-! ## Point classes, excision and classes supported at finitely many points -/

section PointClass

open CategoryTheory Function Ideal TrivSqZeroExt relFreeAb Field HodgeTest

variable {k : Type} [Field k]
  {X X' : CommAlg k ⥤ Type 1} {d e : ℕ} {R R' : CommAlg k} {U : Subfunctor X} {g : Fin d → R}
  {m : k} {ξ : HodgeH (relFreeAb U) d} (a : EtaleChart e X) {z : X (CommAlgCat.of k k)}

seal H.map

/-! ### Symbols on a chart and excision -/

/-- Let `a` be a chart with ring `R` and `e` coordinates. Some ring map `μ : R → R ⊕ R ^ e` is a
section of the projection such that, for `f ∈ R ^ d` and `S` the locus of `Spec R` where `f` spans
the unit ideal, `μ` maps the test `(R, R ^ e)` relative to `someUnitLocus f` (where some `f i` is a
unit) into `Spec R` relative to `S`, by an inclusion `h`, bijectively on Hodge cohomology in all
degrees. -/
lemma EtaleChart.exists_section_isCohomEquiv : ∃ μ : a.coordRing ⟶ HodgeTest.sqZeroExt ⟨_, Fin e⟩,
    LeftInverse fst μ ∧
    ∀ {d : ℕ} {f : Fin d → a.coordRing} {S},
      S = (unimodular (k := k)).preimage (pointMap ⟨f⟩) → ∃ h,
      IsCohomEquiv hodgeCoeff (relFreeAb.map (U' := someUnitLocus (c := ⟨_, Fin e⟩) f) (𝟙 _) h ≫
        relFreeAb.map (U := S.whisker HodgeTest.sqZeroExt) (pointMap ⟨μ⟩) le_rfl) := by
  -- A unit `f i` generates the unit ideal. The first map is an equivalence because
  -- `someUnitLocus f` is dense where `f` is unimodular, the second because the universal point
  -- represents the chart.
  obtain ⟨μ, μ_fst, μ_bij⟩ := a.exists_univPoint
  obtain ⟨μ_inj, μ_surj⟩ := forall_and.mp μ_bij
  refine ⟨μ, μ_fst, fun {d f S} hS ↦ ?_⟩
  -- Read `f` as `fst ∘ μ ∘ f`, so that both sides speak of the point `μ ∘ f`.
  rw [show f = fun i ↦ fst (μ (f i)) by simp [μ_fst _], hS]
  refine ⟨fun _ _ ⟨i, hi⟩ ↦ projSpace.span_eq_top_of_isUnit i (isUnit_iff_isUnit_fst.mpr hi),
    Iff.mpr (IsCohomEquiv.comp_iff (isCohomEquiv_of_le _ fun c y ↦
      isCohomEquiv_someUnitLocus_of_span_eq_top ?_))
      ?_⟩
  · -- `f` is unimodular at `y`; project from `A ⊕ M` to `A`
    apply unimodular.map c.baseProj y.property
  · -- by `μ_surj` the range of the universal point is everything, so excision applies
    exact relFreeAb.excision _ (.of_top_le (by tauto)) (m := mono_of_app_injective μ_inj) rfl

/-- On a chart `a` of `X`, let `x` be a point of a functor `X'` with values in the coordinate ring,
and let `P` be a property of points of `X'`. Suppose two `d`-tuples `f`, `g` of functions both cut
out the locus where `x` satisfies `P`, meaning an algebra map kills all their entries exactly when
the image of `x` satisfies `P`. Then they have the same symbol, `[df / f] = [dg / g]`, relative to
the preimage of the complement of that locus. -/
lemma EtaleChart.symbolClass_eq_of_cutsOutLocus {f g : Fin d → a.coordRing}
    {P : (K : CommAlg k) → X'.obj K → Prop} {x : X'.obj a.coordRing} (hf : CutsOutLocus X' P x f)
    (hg : CutsOutLocus X' P x g) :
    symbolClass.map (relFreeAb.map _ hf.preimage_fieldLocus_not.le) =
      symbolClass.map (relFreeAb.map _ hg.preimage_fieldLocus_not.le) := by
  -- Both families cut out `P`, so they span one ideal: test against the quotient by any ideal.
  have h_span : span (.range f) = span (.range g) := by
    refine eq_of_forall_ge_iff fun I ↦ ?_
    rw [← I.mk_ker]
    exact (hf _ (CommAlgCat.ofHom (Quotient.mkₐ k I))).trans (hg ..).symm
  -- Write `f = M g`. Pull both classes back along the universal point `μ` and apply the
  -- transformation law `symbolClass_transformation` with both matrices equal to `M` and scalar `1`.
  have h_comb (i : Fin d) : ∃ M_i : Fin d → a.coordRing, ∑ j, M_i j * g j = f i :=
    mem_span_range_iff_exists_fun.mp (h_span.le (subset_span ⟨i, rfl⟩))
  choose M hM using h_comb
  obtain ⟨⟨μ : _ →ₐ[k] TrivSqZeroExt a.coordRing (Fin e → a.coordRing)⟩, μ_fst : LeftInverse _ μ,
    h_eqv⟩ :=
    a.exists_section_isCohomEquiv
  -- By the Leibniz rule, `d f = M d g` modulo the ideal.
  have h_leibniz (i : Fin d) (j : Fin e) :
      (μ (f i)).snd j - ∑ l, M i l * (μ (g l)).snd j ∈ span (.range f) := by
    rw [h_span]
    simp [← hM, snd_sum, μ_fst _, Ideal.sum_mem, mul_mem_right, mem_span_range_self,
      Finset.sum_add_distrib]
  have hf_eq : f = Matrix.mulVec M (fst ∘ μ ∘ g) := by
    simp [funext_iff, ← hM, Matrix.mulVec, dotProduct, μ_fst _]
  -- The pull-back is injective, so compare there. The two composite maps of relative chains are
  -- induced by the tuples `μ ∘ f` and `μ ∘ g`.
  obtain ⟨h_le, h_bij⟩ := h_eqv hf.preimage_fieldLocus_not
  apply (h_bij d).injective
  erw [← H.map_comp, ← H.map_comp]
  refine (symbolClass_transformation (f := μ ∘ f) (g := μ ∘ g) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (by simp [comp_def, μ_fst _]) M M 1 hf_eq h_leibniz (by simp)).trans (one_smul ..)

/-- Excision. Let `u : X' ⟶ X` be injective on points with open image, and let every point in a
field outside the image lie in an open subfunctor contained in `U`. Then pull-back along `u`
is bijective from the Hodge cohomology of `(X, U)` to that of `(X', u⁻¹ U)` in all degrees. -/
lemma hodge_excision {u : X' ⟶ X} [Mono u] (hu_open : IsOpenSubfunctor (Subfunctor.range u))
    (h_cover : ∀ K : CommAlg k, IsField K.carrier → ∀ x ∉ Subfunctor.range u K, ∃ O : Subfunctor X,
      IsOpenSubfunctor O ∧ x ∈ O K ∧ O ≤ U)
    {U' : Subfunctor X'} (hU' : U' = U.preimage u) :
    IsCohomEquiv hodgeCoeff (sqZeroExt.whiskerLeft (relFreeAb.map u hU'.le)) := by
  -- Every point in a field lies in an open set contained in the range of `u` or in `U`.
  have h_open (K : CommAlg k) (hK : IsField K.1) (x : X K) :
      ∃ O : Subfunctor X, IsOpenSubfunctor O ∧ x ∈ O K ∧
        O.whisker sqZeroExt ≤ .range (sqZeroExt.whiskerLeft u) ⊔ U.whisker sqZeroExt := by
    by_cases hx : x ∈ Subfunctor.range u K
    · exact ⟨_, hu_open, hx, le_sup_left⟩
    · obtain ⟨O, hO_open, hx_O, hO_le⟩ := h_cover K hK x hx
      exact ⟨O, hO_open, hx_O, le_sup_of_le_right fun c ↦ hO_le _⟩
  -- So their union is dense by Zariski descent, and `relFreeAb.excision` applies.
  have h_dens : IsCohomDense hodgeCoeff (.range (sqZeroExt.whiskerLeft u) ⊔ U.whisker sqZeroExt) :=
    hasZariskiDescent_hodgeCoeff (isZariskiLocallyTop_of_open_cover h_open)
  subst hU'
  exact excision (U := U.whisker _) ((restrictAlong _).map u) h_dens rfl

/-- Pulling a Hodge class back along α ≫ β is pulling it back along β, then along α. -/
@[local simp ←]
lemma HodgeH.map_comp {N : CommAlg k ⥤ AddCommGrpCat} {N' M : AbFunctor (CommAlg k)} (α : M ⟶ N')
    (β : N' ⟶ N) (x : HodgeH (k := k) N d) :
    x.map (α ≫ β) = (x.map β).map α := .symm (H.map_comp ..).symm

@[simp]
lemma HodgeH.map_zero {N : AbFunctor (CommAlg k)} : ξ.map (N' := N) 0 = 0 :=
  ((H.mapHom ..).flip ξ).map_zero

/-! ### Local multiplicities and the class of a point -/

/-- Let `y ∈ X(R)` be a point, `P` a locus of `X`, and `g ∈ R ^ d` functions. Then
`IsLocalSymbol ξ y P g m` says three things. First, `g` cuts out `P` at `y`. Second, the point `y`
maps the part of `Spec R` off the preimage of `P` into `U`. Third, the pull-back of `ξ` along `y` is
`m • [dg / g]` in the Hodge cohomology of `Spec R` relative to that part. -/
def IsLocalSymbol (ξ : HodgeH (relFreeAb U) d) (y : X.obj R) (P : (K : CommAlg k) → X.obj K → Prop)
    (g : Fin d → R) (m : k) : Prop :=
  ∃ᵉ (D : CutsOutLocus X P y g) (h),
    HodgeH.map (relFreeAb.map (pointMap (A := R) y) (U := U) h) ξ =
      m • HodgeH.map (relFreeAb.map _ D.preimage_fieldLocus_not.le) (symbolClass (k := k) (d := d))

/-- A local description `m • [dg / g]` at `y` is preserved by a ring map `φ : R ⟶ R'`. -/
lemma IsLocalSymbol.map {y : X.obj R} {P : (K : CommAlg k) → X.obj K → Prop}
    (h_symbol : IsLocalSymbol ξ y P g m) (φ : R ⟶ R') :
    IsLocalSymbol ξ (X.map φ y) P (φ ∘ g) m := by
  -- Pull the equation back along the map `Spec R' ⟶ Spec R` induced by `φ`.
  obtain ⟨h_cut, h_le, h_eq⟩ := h_symbol
  have cut : CutsOutLocus X P (X.map φ y) (φ ∘ g) := fun A ψ ↦ by
    simpa [span_le, Set.range_subset_iff] using h_cut A (φ ≫ ψ)
  use cut
  rw! (transparency := .all) [← pointMap_comp _ (pointMap y)]
  exact ⟨_, by simpa using! congr($(h_eq).map (relFreeAb.map _ le_rfl))⟩

/-- The relative class `ξ` has multiplicity `n z` at each `z ∈ s`: some chart contains `z`,
some `d` functions `g` on it cut out `z`, and there `ξ` restricts to `n z • [dg / g]`
relative to the complement of `z`. Nothing is asked of `ξ` away from `s`. -/
def IsPointSum (s : Set (X (CommAlgCat.of k k))) (n : X (CommAlgCat.of k k) → k)
    (ξ : HodgeH (relFreeAb U) d) :
    Prop :=
  ∀ z ∈ s, ∃ᵉ (a : EtaleChart d X) (g : Fin d → a.coordRing),
    z ∈ a.locus (CommAlgCat.of k k) ∧ IsLocalSymbol ξ a.point (ComesFromPoints {z}) g (n z)

/-- The class of a `k`-point `z` in the Hodge cohomology of degree `d`: the image of a chosen
class with support `z` and multiplicity `1` at `z`; if there is no such class, the image of
an arbitrary class with support `z`. -/
noncomputable def pointClass (d : ℕ) (z : X (CommAlgCat.of k k)) : HodgeH (freeAb.obj X) d :=
  HodgeH.map (q := d) (π (offPoints {z})) (Classical.epsilon (IsPointSum {z} 1))

variable [IsSeparatedFunctor X]

/-- Let X be separated and z a k-point of X that lies in U. A point x of X over a field K that is
not in U lies in an open subfunctor contained in the complement of z, namely that complement. -/
lemma exists_isOpenSubfunctor_le_offPoints (hz : z ∈ U.obj (CommAlgCat.of k k)) ⦃K : CommAlg k⦄
    (hK : IsField K.carrier) ⦃x : X.obj K⦄ (hx : x ∉ U K) :
    ∃ O : Subfunctor X, IsOpenSubfunctor O ∧ x ∈ O K ∧ O ≤ offPoints {z} := by
  -- The image of `z` lies in `U K`, so it is not `x`; take `O = offPoints {z}`.
  have hz_mem : X.map structureMap z ∈ U K := U.map structureMap hz
  have hx_off : x ∈ offPoints {z} K := by aesop (add simp [mem_offPoints_iff, ComesFromPoints])
  exact ⟨offPoints {z}, isOpenSubfunctor_offPoints, hx_off, le_rfl⟩

/-- Let `X` be separated, `a` a chart of dimension `e` that contains `z`, and `g` functions on `a`
that cut out `z`. Some class with support `z` restricts to `[dg / g]` on `a`, and so has
multiplicity `1` at `z`. -/
lemma EtaleChart.exists_isLocalSymbol {g : Fin e → a.coordRing}
    (h_cut : CutsOutLocus X (ComesFromPoints {z}) a.point g)
    (hz : z ∈ a.locus.obj (CommAlgCat.of k k)) :
    ∃ ξ : HodgeH (relFreeAb (offPoints {z})) e,
      IsLocalSymbol ξ a.point (ComesFromPoints {z}) g 1 ∧ IsPointSum {z} 1 ξ := by
  -- By excision, the symbol of `g` on the chart comes from a class with support `z`.
  obtain ⟨ξ, hξ⟩ := (hodge_excision a.isOpenSubfunctor
    (exists_isOpenSubfunctor_le_offPoints hz) rfl e).surjective _
  have h_loc : IsLocalSymbol ξ a.point (ComesFromPoints {z}) g 1 := ⟨h_cut, _, hξ⟩
  exact ⟨ξ, h_loc, forall_eq.mpr ⟨a, g, hz, h_loc⟩⟩

/-- On a separated `X`, a class with support `z` and multiplicity `n z` at `z` maps to
`n z • pointClass d z` in the Hodge cohomology of `X`. -/
lemma IsPointSum.map_eq_smul_pointClass {n : X.obj (CommAlgCat.of k k) → k}
    {ξ : HodgeH (relFreeAb (offPoints {z})) d} (h_mult : IsPointSum {z} n ξ) :
    HodgeH.map (π (offPoints {z})) ξ = n z • pointClass d z := by
  -- Compare `ξ` with the class `ξ₀` chosen in `pointClass`, on the intersection `c` of their two
  -- charts.
  obtain ⟨a, g, hz, hξ⟩ := h_mult z rfl
  let ξ₀ : HodgeH (relFreeAb (offPoints {z})) d := Classical.epsilon (IsPointSum {z} 1)
  have h₀ : IsPointSum {z} 1 ξ₀ :=
    Classical.epsilon_spec ((a.exists_isLocalSymbol hξ.fst hz).imp fun _ ↦ And.right)
  obtain ⟨b, g₀, hz₀, hξ₀⟩ := h₀ z rfl
  obtain ⟨c, hc⟩ := a.exists_locus_eq_inf b
  obtain ⟨⟨⟨φ : a.coordRing ⟶ c.coordRing⟩, hφ : X.map φ a.point = c.point⟩,
    ⟨ψ : b.coordRing ⟶ c.coordRing⟩, hψ : X.map ψ b.point = c.point⟩ := hc.le _ c.point_mem_locus
  obtain ⟨cut, _, local_eq⟩ : IsLocalSymbol ξ c.point (ComesFromPoints {z}) (φ ∘ g) (n z) := by
    simpa only [hφ] using hξ.map φ
  obtain ⟨cut₀, _, local_eq₀⟩ : IsLocalSymbol ξ₀ c.point (ComesFromPoints {z}) (ψ ∘ g₀) 1 := by
    simpa only [hψ, Pi.one_apply] using hξ₀.map ψ
  -- Both families cut out `z` on `c`, so they have the same symbol.
  rw [c.symbolClass_eq_of_cutsOutLocus cut cut₀, ← local_eq₀.trans (one_smul ..), ← map_smul]
    at local_eq
  -- By excision, restriction to the chart `c` is injective on classes with support `z`.
  obtain rfl : ξ = n z • ξ₀ := (hodge_excision c.isOpenSubfunctor
    (exists_isOpenSubfunctor_le_offPoints (hc.ge _ ⟨hz, hz₀⟩)) rfl d).injective local_eq
  exact map_smul ..

/-- On a separated `X`, every class with support `z` and multiplicity `1` at `z` maps to
`pointClass d z`. So `pointClass d z` does not depend on the choice made in its definition. -/
lemma IsPointSum.map_eq_pointClass {d : ℕ} {z : X (CommAlgCat.of k k)}
    {ξ₀ : HodgeH (relFreeAb (offPoints {z})) d} (h_mult : IsPointSum {z} 1 ξ₀) :
    HodgeH.map (π (offPoints {z})) ξ₀ = pointClass d z := by
  rw [h_mult.map_eq_smul_pointClass, Pi.one_apply, one_smul]

/-- On a separated `X`, a class with support in a finite set `s` of `k`-points and
multiplicities `n` maps to `∑ z ∈ s, n z • pointClass d z` in the Hodge cohomology of `X`. -/
lemma IsPointSum.map_eq_sum_pointClass {s : Finset (X (CommAlgCat.of k k))}
    {n : X.obj (CommAlgCat.of k k) → k} (h_mult : IsPointSum s n ξ) (hU : U = offPoints s) :
    HodgeH.map (π U) ξ = ∑ z ∈ s, n z • pointClass d z := by
  classical
  induction s using Finset.induction generalizing U with
  | empty =>
    -- no point lies in the empty set, so every class is `0` relative to `offPoints ∅`
    have h_zero : π U = 0 := freeAb.hom_ext fun _ _ ↦ mk_eq_zero (hU.ge _ nofun)
    simp [h_zero]
  | insert z s hz ih => ?_
  obtain rfl : U = offPoints {z} ⊓ offPoints s := by
    aesop (add simp [offPoints, fieldLocus]) (add simp ComesFromPoints)
  -- Mayer–Vietoris: `ξ` is the sum of classes `x` with support `z` and `y` with support `s`.
  -- Excision gives `x` that agrees with `ξ` on `V = offPoints s`.
  let V : Subfunctor X := offPoints s
  have hV_open : IsOpenSubfunctor (Subfunctor.range V.ι) := by simp [V, isOpenSubfunctor_offPoints]
  have hz_V : z ∈ (Subfunctor.range V.ι).obj (CommAlgCat.of k k) := by
    simpa [V, toIsField, mem_offPoints_iff, ComesFromPoints]
  have h_restrict : (offPoints {z} ⊓ V).preimage V.ι = (offPoints {z}).preimage V.ι :=
    Subfunctor.ext (funext fun _ ↦ Set.ext fun p ↦ and_iff_left p.property)
  obtain ⟨x : HodgeH (relFreeAb (offPoints {z})) d,
      hx : x.map (map V.ι h_restrict.le) = ξ.map (map V.ι le_rfl)⟩ :=
    (hodge_excision hV_open (exists_isOpenSubfunctor_le_offPoints hz_V) h_restrict d).2 _
  -- `ξ - x` restricts to `0` on `V`, so by the long exact sequence of the triple
  -- `offPoints {z} ⊓ V ≤ V ≤ X` it comes from a class `y` relative to `V`.
  have h_diff : (ξ - x.map (map (𝟙 X) (by simp))).map (map V.ι le_rfl) = 0 :=
    (HodgeH.map _).sub_mem_ker_iff.mpr (by simpa using! hx.symm)
  obtain ⟨y : HodgeH .., hy : y.map (relFreeAb.map _ (by simp)) = _⟩ :=
    ((LongExactSeq.contravariant ((shortExact_triple ..).2.map_of_exact (restrictAlong _))
      _).exact_f_g d _).1 h_diff
  -- In such a sum, a class with support `t'` vanishes on the chart at a point `w ∉ t'`, as that
  -- chart misses `t'`; so the other summand has the multiplicity of `ξ` at `w`.
  have h_isPointSum_of_eq_add {t : Set (X (CommAlgCat.of k k))} {A B : Subfunctor X}
      {l : offPoints {z} ⊓ V ≤ A.preimage (𝟙 X)} {l' : offPoints {z} ⊓ V ≤ B.preimage (𝟙 X)}
      {x : HodgeH (relFreeAb A) d} {y : HodgeH (relFreeAb B) d} (t' : Set (X (CommAlgCat.of k k)))
      (h_sum : ξ = .map (map (𝟙 X) (U := A) l) x + .map (map (𝟙 X) (U := B) l') y)
      (hB : B = offPoints t') (ht : t = ↑(insert z s) \ t') : IsPointSum t n x := by
    subst hB ht
    rintro w ⟨hw, hw'⟩
    obtain ⟨a, g, ha, cut, h_le_chart, local_eq⟩ := h_mult w hw
    have h_vanish : map _ h_le_chart ≫ map _ l' = 0 := by
      refine hom_ext fun C σ ↦ mk_eq_zero fun K φ hK ↦ (mem_offPoints_iff hK).mp ?_
      -- a point of the chart in `t'` is not `w`, so by `h_le_chart` and `l'` it lies in
      -- `offPoints t'`
      change X.map φ (X.map σ.down a.point) ∈ (offPoints t').obj K
      rw [← X.map_comp_apply]
      by_contra h_notMem
      have hw_mem : w ∈ (offPoints t').obj (CommAlgCat.of k k) := by
        aesop (add simp [mem_offPoints_iff, ComesFromPoints, toIsField])
      obtain ⟨O, -, h_mem_O, hO_le⟩ := exists_isOpenSubfunctor_le_offPoints hw_mem hK h_notMem
      tauto
    exact ⟨a, g, ha, cut, _, by simpa [h_sum, h_vanish] using local_eq⟩
  obtain rfl := add_eq_of_eq_sub' hy
  -- The case of one point applies to `x`, the induction hypothesis to `y`.
  have hx_sum : IsPointSum {z} n x := h_isPointSum_of_eq_add s rfl (by simp [V]) (by grind)
  have hy_sum : IsPointSum s n y := h_isPointSum_of_eq_add {z} (add_comm ..) rfl (by grind)
  simp [V, hz, ← ih hy_sum, ← hx_sum.map_eq_smul_pointClass, π_map]

end PointClass

end New.Variety

end
