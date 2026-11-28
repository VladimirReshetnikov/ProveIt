import Lib.Adelic.AutomorphicForms.HeckeEigenforms
import Lib.Adelic.TraceFormula.LevelCut
import Lib.Adelic.TraceFormula.TraceComparison

/-!
# Comparison of traces for a cuspidal test function

The comparison of traces `trace_comparison` asks for a test function that is cuspidal at a split
place `w` and is supported at a second place on elements whose characteristic polynomial has a
simple zero at `0` modulo that place. The second condition is removed here: at an auxiliary split
place `v` the level is cut down to the stabiliser of a line, where `T⁺ = lineHecke` forces the
simple zero and counts the spherical vectors through its determinant (`trace_eq_of_isCuspidalAt`).

## Relation to the literature

Known; see `Lib.Adelic.TraceFormula.TraceComparison` for sources.
-/

noncomputable section

namespace New

open NumberField Module LinearMap MonoidAlgebra Filter Variety Fintype

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]

/-- An element `a` of the group algebra of the finite adelic group is integral at almost all places
`v`: it is a combination of group elements whose component at `v` lies in
`localIntGL n v = GL_n(O_v)`. -/
lemma eventually_mem_spanOn_atPlace_mem_localIntGL (a : ℂ[Gf E n]) :
    ∀ᶠ v : FinPlace E in cofinite, a ∈ spanOn ℂ {g : Gf E n | g.atPlace v ∈ localIntGL n v} := by
  have h_support : ∀ᶠ v : FinPlace E in cofinite,
      ∀ g ∈ a.coeff.support, g.atPlace v ∈ localIntGL n v :=
    a.coeff.support.eventually_all.2 fun g _ ↦ g.eventually_atPlace_mem_localIntGL
  filter_upwards [h_support] with v hv
  exact Submodule.span_mono (Set.image_mono hv) a.mem_span_support_coeff

variable [HasPrimitiveRoot5040 E]

/-- The auxiliary place: let `E` contain the 5040th roots of unity. For an open subgroup `K`, an
element `a` of the group algebra and a place `w`, some split place `v` is neither `w` nor its
conjugate, `K` contains `maxCompactAt n v` (the integral elements that are `1` away from `v` and its
conjugate), and `a` is a combination of elements that are integral at `v`. -/
lemma exists_auxiliary_place {K : Subgroup (Gf E n)} (hK : K.IsOpen) (a : ℂ[Gf E n])
    (w : FinPlace E) :
    ∃ v : FinPlace E, v.IsSplit ∧
      v ∉ Set.conjClosure {w} ∧
      maxCompactAt n v ≤ K ∧
      a ∈ spanOn ℂ {g : Gf E n | g.atPlace v ∈ localIntGL n v} := by
  -- There are infinitely many split places, and the other conditions hold at almost all places.
  have h_split : ∃ᶠ v : FinPlace E in cofinite, v.IsSplit :=
    frequently_prime_q.mono fun _ ↦ isSplit_of_q_prime
  have h_ne : ∀ᶠ v : FinPlace E in cofinite, v ∉ Set.conjClosure {w} :=
    (Set.finite_singleton w).conjClosure.eventually_cofinite_notMem
  exact (h_split.and_eventually (h_ne.and ((eventually_maxCompactAt_le hK).and
    (eventually_mem_spanOn_atPlace_mem_localIntGL a)))).exists

variable [Nonempty n] {s s' : n → ℤˣ}

/-- Comparison of traces without the condition at a second place. Let the CM field `E` contain the
5040th roots of unity and have an even number of infinite places, let `V`, `V'` be hermitian spaces
of rank `N = card n ≥ 2` over `E` with signs `s`, `s'`, and let `l = 2λ` be a doubled Harish-Chandra
parameter whose `toHCParam s (l v)` and `toHCParam s' (l v)` have gap at least `500 N³ + 10 N⁵` at
every infinite place `v` (`HasLargeGap A` means gap `500 N³ + A`). Let `K` be a level (`IsLevel K`,
so `K` is open and compact), let `a` keep the `K`-fixed vectors in every representation
(`universalLevelAlgebra K`), and let the test function `a ⋆ 1_K` (`convIndicator`) be cuspidal at a
split place `w`. Then operators that act as `a` on the forms of parameter `l` and level `K`
(`levelSpace` of `formRep` at `typeKernel l s`, resp. `typeKernel l s'`, which the gap bound makes a
cusp kernel by `isCuspKernel_typeKernel`) on `V` and on `V'` have the same trace. -/
theorem trace_eq_of_isCuspidalAt (hE : Even (Core.numInfPlaces E)) (hn : 2 ≤ card n)
    (V : Space E n s) (V' : Space E n s') {l : InfinitePlace E → n → ℤ}
    (h_gap : ∀ v : InfinitePlace E, (toHCParam s (l v)).HasLargeGap (10 * card n ^ 5))
    (h_gap' : ∀ v : InfinitePlace E, (toHCParam s' (l v)).HasLargeGap (10 * card n ^ 5))
    {K : Subgroup (Gf E n)} [hK : IsLevel K] {a : ℂ[Gf E n]} (ha : a ∈ universalLevelAlgebra K)
    {w : FinPlace E} (hw : w.IsSplit)
    (h_cusp : IsCuspidalAt hw (convIndicator hK.isOpen hK.isCompact a))
    {T : End ℂ (levelSpace (V.formRep (typeKernel l s)) K)}
    (hT : ∀ y : levelSpace (V.formRep (typeKernel l s)) K,
      (T y).1 = (V.formRep (typeKernel l s)).asAlgebraHom a y.1)
    {T' : End ℂ (levelSpace (V'.formRep (typeKernel l s')) K)}
    (hT' : ∀ y : levelSpace (V'.formRep (typeKernel l s')) K,
      (T' y).1 = (V'.formRep (typeKernel l s')).asAlgebraHom a y.1) :
    trace ℂ (levelSpace (V.formRep (typeKernel l s)) K) T =
      trace ℂ (levelSpace (V'.formRep (typeKernel l s')) K) T' := by
  -- Cut the level at an auxiliary split place `v` down to the stabiliser of a line. There the
  -- positive powers of `T⁺ = lineHecke v i` make `0` a simple root modulo `v` of the
  -- characteristic polynomial on the support, so `trace_comparison` applies.
  obtain ⟨v, hv, hv_ne, h_max, h_int⟩ := exists_auxiliary_place hK.isOpen a w
  obtain ⟨i⟩ : Nonempty n := inferInstance
  let K' : OpenSubgroup (Gf E n) := ⟨cutLevel K v (lineStabilizer v i), IsLevel.isOpen⟩
  have : Module.Finite ℂ (levelSpace (V.formRep (typeKernel l s)) K'.1) :=
    V.finite_levelSpace (isCuspKernel_typeKernel h_gap) K'
  have : Module.Finite ℂ (levelSpace (V'.formRep (typeKernel l s')) K'.1) :=
    V'.finite_levelSpace (isCuspKernel_typeKernel h_gap') K'
  refine trace_eq_of_trace_cutLevel_eq hv h_max i V.inner_formRep V'.inner_formRep ha h_int
    (fun j m S S' hS hS' ↦ ?_) hT hT'
  refine trace_comparison hE hn V V' h_gap h_gap' (w' := v) hw ?_ (fun g hg ↦ ?_) hS hS'
  · -- Cuspidality at `w` survives the cut at `v` and convolution on the left.
    obtain ⟨h_ne, h_star_ne⟩ : v ≠ w ∧ star v ≠ w := not_or.1 hv_ne
    rw [pow_succ a, mapDomain_mul, ← mul_assoc]
    exact (h_cusp.convIndicator_offPlace hv h_ne h_star_ne h_max h_int).convIndicator_mul _
  · -- At `v` an element of the support is `x * k` with `k` in the stabiliser of a line and `x` in
    -- a set that carries the positive powers of `T⁺` and on which `x * k` has a simple zero.
    obtain ⟨x, hx, k, hk, h_eq⟩ : ∃ x ∈ {x : GL n (LocField v) |
        ∀ k ∈ lineStabilizer v i, HasSimpleZero (x * k)},
        ∃ k ∈ lineStabilizer v i, g.atPlace v = x * k :=
      exists_atPlace_eq_of_convIndicator_ne_zero hv
        (lineHecke_pow_mem_spanOn v i m.succ_pos) (a ^ (j + 1)) hg
    rw [h_eq]
    exact hx k hk

end New

end
