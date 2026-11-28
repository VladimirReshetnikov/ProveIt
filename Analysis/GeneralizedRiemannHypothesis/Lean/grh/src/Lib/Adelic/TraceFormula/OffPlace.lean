import Lib.Adelic.TraceFormula.TestFunction
import Lib.Shimura.HeckeTower.HeckeData
import Lib.Weil.Unramified.SplitHecke

/-!
# Test functions with a deeper level at an auxiliary place

Let `v` be a split place at which the level `K` is maximal, and let `K'` be the part of `K` whose
component at `v` lies in a subgroup `J` of `GL_n(E_v)`. For a group algebra element `a` that is
integral at `v`, removing the components at `v` and its conjugate gives an element whose function
of level `K'` is the function of `a` of level `K`, cut off to the points with component at `v` in
`J`. So it is cuspidal at a place `w` other than `v` and its conjugate if the function of `a` is.
The function of a product with a factor at `v` in a set `S` is supported at `v` in `S J`.

Notions from other files:

* `Gf E n` is the finite adelic unitary group, and `g.atPlace v` is the component of `g` at `v`.
* For a split place `v` (one that differs from its conjugate), `ofSplitPlace hv k` is the element
  with component `k` at `v`, the inverse conjugate transpose of `k` at the conjugate of `v`, and `1`
  at all other places.
* `spanOn ℂ S` is the space of the group algebra elements that are combinations of the elements
  of the set `S`.
* `convIndicator` sends a group algebra element `a` to the test function `a ⋆ 1_K` of level `K`.
* `maxCompactAt n v` is the group of integral elements supported at `v` and its conjugate, and
  `localIntGL n v` is `GL_n(O_v)`.

## Relation to the literature

Known result: Test functions with a deeper level at an auxiliary split place, by removing the
components there. It serves `Lib.Adelic.TraceFormula.CuspidalComparison`.
-/

open NumberField MonoidAlgebra

namespace New

open Variety

variable {E n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] [DecidableEq n]
  {v w : FinPlace E}

/-- The homomorphism that removes from an element its components at the split place `v` and at
the conjugate of `v`. -/
noncomputable def offPlace (hv : v.IsSplit) : Gf E n →* Gf E n :=
  MonoidHom.mk' (fun g ↦ g * (ofSplitPlace hv (g.atPlace v))⁻¹) fun g h ↦ by
    have h_comm : Commute (ofSplitPlace hv (g.atPlace v)) (h * (ofSplitPlace hv (h.atPlace v))⁻¹) :=
      Gf.commute_supportedOn_trivialOn (ofSplitPlace_mem_supportedOn hv _) (by simp)
    simp only [map_mul, mul_inv_rev, mul_assoc, h_comm.inv_left.eq]

/-- Removing the components of `g` at `v` and its conjugate is dividing `g` by the element
`ofSplitPlace hv (g.atPlace v)`, which has these components and is `1` at all other places. -/
lemma offPlace_apply (hv : v.IsSplit) (g : Gf E n) :
    offPlace hv g = g * (ofSplitPlace hv (g.atPlace v))⁻¹ := rfl

@[simp] lemma atPlace_offPlace (hv : v.IsSplit) (g : Gf E n) : (offPlace hv g).atPlace v = 1 := by
  simp [offPlace_apply]

variable {K : Subgroup (Gf E n)} {J : Subgroup (GL n (LocField v))}

open scoped Classical in
/-- Let `v` be a split place, let `K` be a compact open subgroup of the adelic unitary group
`Gf E n` that contains the maximal compact group at `v`, let `J` be a subgroup of `GL_n(E_v)`
such that `K ⊓ J.comap (Gf.atPlace v)` is compact open, and let `a` be a combination (`spanOn`)
of elements with component at `v` in `localIntGL n v = GL_n(O_v)`. Removing (`offPlace`)
the components of `a` at `v` and its conjugate and deepening the level to
`K ⊓ J.comap (Gf.atPlace v)` gives the function of `a` of level `K`, cut off outside the points
with component at `v` in `J`. Here `convIndicator` sends a group algebra element to its
convolution with the characteristic function of the level. -/
lemma convIndicator_mapDomain_offPlace {hK_open : IsOpen (K : Set (Gf E n))}
    {hK_compact : IsCompact (K : Set (Gf E n))}
    {hK'_open : IsOpen (↑(K ⊓ J.comap (Gf.atPlace v)) : Set (Gf E n))}
    {hK'_compact : IsCompact (↑(K ⊓ J.comap (Gf.atPlace v)) : Set (Gf E n))}
    (hv : v.IsSplit) (hK_max : maxCompactAt n v ≤ K) {a : ℂ[Gf E n]}
    (ha : a ∈ spanOn ℂ {x : Gf E n | x.atPlace v ∈ localIntGL n v}) (g : Gf E n) :
    (convIndicator hK'_open hK'_compact (mapDomain (offPlace hv) a)).1 g =
      if g.atPlace v ∈ J then (convIndicator hK_open hK_compact a).1 g else 0 := by
  -- By linearity we may take `a` to be a single element `x` that is integral at `v`. Its part at
  -- `v` then lies in `K`, so removing that part changes only the condition at `v`.
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨x, hx, rfl⟩ : ∃ x : Gf E n, x.atPlace v ∈ localIntGL n v ∧ of ℂ (Gf E n) x = a := ha
    have h_mem : ofSplitPlace hv (x.atPlace v) ∈ K :=
      hK_max ⟨(ofSplitPlace_mem_stdLevel hv _).2 hx, ofSplitPlace_mem_supportedOn hv _⟩
    have h_coset : (offPlace hv x)⁻¹ * g ∈ K ⊓ J.comap (Gf.atPlace v) ↔
        g.atPlace v ∈ J ∧ x⁻¹ * g ∈ K := by
      simp [offPlace_apply, mul_assoc, K.mul_mem_cancel_left h_mem, and_comm]
    simp [convIndicator_single, h_coset, ← ite_and]
  | zero => simp
  | add a b _ _ ha hb => simp [mapDomain_add, ha, hb, ite_add_zero]
  | smul c a _ ha => simp [mapDomain_smul, ha]

/-- Let `v` be a split place, let `K` be a compact open subgroup of the adelic unitary group
`Gf E n` that contains the maximal compact group at `v`, let `J` be a subgroup of `GL_n(E_v)`,
let `a` be a combination (`spanOn`) of elements that are integral at `v` (component in
`localIntGL n v`), and let `w` be a split place other than `v` and its conjugate. If the function
`a ⋆ 1_K` (`convIndicator`) is cuspidal at `w` (its sums of translates over the cosets of each
unipotent radical at `w` vanish), then so is the function of level `K ⊓ J.comap (Gf.atPlace v)`
of `a` with the components at `v` and its conjugate removed (`offPlace`). -/
lemma IsCuspidalAt.convIndicator_offPlace {hK_open : IsOpen (K : Set (Gf E n))}
    {hK_compact : IsCompact (K : Set (Gf E n))}
    {hK'_open : IsOpen (↑(K ⊓ J.comap (Gf.atPlace v)) : Set (Gf E n))}
    {hK'_compact : IsCompact (↑(K ⊓ J.comap (Gf.atPlace v)) : Set (Gf E n))}
    {hw : w.IsSplit} (hv : v.IsSplit) (h_ne : v ≠ w) (h_star_ne : star v ≠ w)
    (hK_max : maxCompactAt n v ≤ K) {a : ℂ[Gf E n]}
    (ha : a ∈ spanOn ℂ {x : Gf E n | x.atPlace v ∈ localIntGL n v})
    (h_cusp : IsCuspidalAt hw (convIndicator hK_open hK_compact a)) :
    IsCuspidalAt hw (convIndicator hK'_open hK'_compact (mapDomain (offPlace hv) a)) := by
  classical
  intro T hT_empty hT_univ t lift h_lift g
  -- A translation at `w` does not change the component at `v`.
  have h_place (k : GL n (LocField w)) : (g * ofSplitPlace hw k).atPlace v = g.atPlace v := by
    rw [map_mul, atPlace_ofSplitPlace_of_ne hw k h_ne h_star_ne, mul_one]
  simp only [convIndicator_mapDomain_offPlace (hK_open := hK_open) (hK_compact := hK_compact)
    hv hK_max ha, h_place]
  split_ifs
  exacts [h_cusp T hT_empty hT_univ t lift h_lift g, finsum_zero]

/-- Let `u` be a combination (`spanOn`) of elements of a set `S` of `GL_n(E_v)`, let `J` be a
subgroup of `GL_n(E_v)`, and let `b` be any element of the group algebra of the adelic unitary
group `Gf E n`. Form the product of `u`, placed at `v` by `ofSplitPlace`, with `b` after removing
(`offPlace`) its components at `v` and its conjugate, and take the function (`convIndicator`) of
level `K ⊓ J.comap (Gf.atPlace v)` of this product. Where it is not zero, the component at `v`
lies in `S J`. -/
lemma exists_atPlace_eq_of_convIndicator_ne_zero
    {hK'_open : IsOpen (↑(K ⊓ J.comap (Gf.atPlace v)) : Set (Gf E n))}
    {hK'_compact : IsCompact (↑(K ⊓ J.comap (Gf.atPlace v)) : Set (Gf E n))}
    (hv : v.IsSplit) {S : Set (GL n (LocField v))}
    {u : ℂ[GL n (LocField v)]} (hu : u ∈ spanOn ℂ S) (b : ℂ[Gf E n]) {g : Gf E n}
    (hg : (convIndicator hK'_open hK'_compact
      (mapDomain (ofSplitPlace hv) u * mapDomain (offPlace hv) b)).1 g ≠ 0) :
    ∃ x ∈ S, ∃ k ∈ J, g.atPlace v = x * k := by
  contrapose! hg
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    have h_notMem : x⁻¹ * g.atPlace v ∉ J := fun h_mem ↦
      hg x hx _ h_mem (mul_inv_cancel_left x _).symm
    induction b using induction_linear with
    | zero => simp
    | add b b' hb hb' => simp_all [mapDomain_add, mul_add]
    | single y c =>
      have h_coset : (ofSplitPlace hv x * offPlace hv y)⁻¹ * g ∉ K ⊓ J.comap (Gf.atPlace v) := by
        simp [mul_assoc, h_notMem]
      -- `mul_inv_rev` would rewrite the element in the goal that `h_coset` is about.
      simp [convIndicator_single, h_coset, -mul_inv_rev]
  | zero => simp
  | add u u' _ _ hu hu' => simp [mapDomain_add, add_mul, hu, hu']
  | smul c u _ hu => simp [mapDomain_smul, hu]

end New
