import Lib.Adelic.TraceFormula.LevelAlgebra
import Lib.Adelic.TraceFormula.LineDeterminant
import Lib.Adelic.TraceFormula.LineStabiliser
import Lib.Adelic.TraceFormula.OffPlace

/-!
# Passage to the stabiliser of a line at an auxiliary place

Let `w` be a split place at which the level `K` is maximal, and let `K'` be the level that is the
stabiliser `J` of a line at `w` and agrees with `K` elsewhere. On the vectors of level `K'` of a
representation, an operator `A` that comes from the places off `w` commutes with the operators `T⁺`,
`T⁻` of `J`, and the mean `e` over `GL_n(𝒪_w)` projects onto the vectors of level `K`. If the
representation is unitary and the vectors of level `K'` form a finite-dimensional space, then the
traces of the `A ^ l * T⁺ ^ m`, `l, m ≥ 1`, at level `K'` determine the trace of `A` at level `K`
(`trace_eq_of_trace_cutLevel_eq`).

Notions from other files:
* `levelSpace ρ K`: the vectors of the representation `ρ` that are fixed by `K`; `levelAlgebra ρ K`:
  the elements of the group algebra that map this space to itself.
* `Gf E n`: the group of finite-adelic unitary elements, whose component at `w` is `g.atPlace w` in
  `GL n (LocField w)`; `localIntGL n w`: the group `GL_n(𝒪_w)`; `stdLevel E n`: the finite-adelic
  unitary elements that are integral at every place; `maxCompactAt n w`: those elements of
  `stdLevel E n` that are trivial away from `w` and its conjugate.
* `ofSplitPlace hw x`: the finite-adelic unitary element with component `x` at the split place `w`;
  `offPlace hw g`: the part of `g` away from `w` and its conjugate.
* `lineStabilizer w i`: the stabiliser in `GL_n(𝒪_w)` of the `i`-th coordinate line modulo `w`;
  `lineHecke w i` and `lineHeckeLower w i` act as its Hecke operators `T⁺` and `T⁻`.
* `LineRelation d c A T⁺ T⁻ e`: `T⁻` is adjoint to `T⁺`, `T⁺ T⁻ = d (1 + c e)`, `e` is idempotent,
  `A` commutes with `T⁺` and `T⁻`, and `d, c > 0`.
-/

noncomputable section

namespace New

open NumberField Module LinearMap MonoidAlgebra InnerProductSpace

open Variety (spanOn)

variable {E n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] [DecidableEq n]
  {w : FinPlace E}

/-- The part of `K` whose component at `w` lies in `J`. -/
abbrev cutLevel (K : Subgroup (Gf E n)) (w : FinPlace E) (J : Subgroup (GL n (LocField w))) :
    Subgroup (Gf E n) := K ⊓ J.comap (Gf.atPlace w)

/-- The cut of a level by the stabiliser of a line at `w` is again a level: it is open and lies in
`stdLevel E n`, the subgroup of elements that are integral at every place. -/
instance isLevel_cutLevel_lineStabilizer (K : Subgroup (Gf E n)) [IsLevel K] (w : FinPlace E)
    (i : n) : IsLevel (cutLevel K w (lineStabilizer w i)) where
  le := inf_le_left.trans IsLevel.le
  isOpen := IsLevel.isOpen.inter ((isOpen_lineStabilizer w i).preimage (Gf.continuous_atPlace w))

/-- The part of `g` off the split place `w` commutes with every element supported at `w`. -/
lemma commute_offPlace_ofSplitPlace (hw : w.IsSplit) (g : Gf E n) (x : GL n (LocField w)) :
    Commute (offPlace hw g) (ofSplitPlace hw x) := by
  refine (Gf.commute_supportedOn_trivialOn (ofSplitPlace_mem_supportedOn hw x) ?_).symm
  simp [Gf.mem_trivialOn, atPlace_offPlace]

/-- If `K` contains the maximal compact subgroup at the split place `w`, it contains the image of
`GL_n(𝒪_w)` under `ofSplitPlace`. -/
lemma ofSplitPlace_mem_of_maxCompactAt_le (hw : w.IsSplit) {K : Subgroup (Gf E n)}
    (hK : maxCompactAt n w ≤ K) {x : GL n (LocField w)} (hx : x ∈ localIntGL n w) :
      ofSplitPlace hw x ∈ K :=
  hK ⟨(ofSplitPlace_mem_stdLevel hw x).2 hx, ofSplitPlace_mem_supportedOn hw x⟩

section Algebraic

variable (hw : w.IsSplit) {K : Subgroup (Gf E n)} {J : Subgroup (GL n (LocField w))}
  {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (Gf E n) M) [IsLevel K]

/-- The action of an element through its part off `w`. -/
abbrev offRep : Representation ℂ (Gf E n) M := ρ.comp (offPlace hw)

/-- The action of the group at `w`. -/
abbrev localRep : Representation ℂ (GL n (LocField w)) M := ρ.comp (ofSplitPlace hw)

/-- An element acts as its component at `w` followed by its part off `w`. -/
lemma apply_eq_offRep_localRep (g : Gf E n) (y : M) :
    ρ g y = offRep hw ρ g (localRep hw ρ (g.atPlace w) y) := by
  simp [← End.mul_apply, ← map_mul, offPlace_apply]

/-- The action of an element off `w` commutes with the action of the group algebra at `w`. -/
lemma commute_offRep_localRep (g : Gf E n) (u : ℂ[GL n (LocField w)]) :
    Commute (offRep hw ρ g) ((localRep hw ρ).asAlgebraHom u) :=
  commute_asAlgebraHom (fun x ↦ (commute_offPlace_ofSplitPlace hw g x).map ρ) u

/-- The action of an element at `w` commutes with the action of the group algebra through the parts
off `w`. -/
lemma commute_localRep_offRep (x : GL n (LocField w)) (a : ℂ[Gf E n]) :
    Commute (localRep hw ρ x) ((offRep hw ρ).asAlgebraHom a) :=
  commute_asAlgebraHom (fun g ↦ (commute_offPlace_ofSplitPlace hw g x).symm.map ρ) a

/-- Let `a` be a combination of group elements whose components at the split place `w` lie in
`GL_n(𝒪_w)`. On vectors that are spherical at `w` (fixed by the maximal compact subgroup there),
`a` acts through its part off `w`. -/
lemma asAlgebraHom_offRep_apply {a : ℂ[Gf E n]}
    (ha : a ∈ spanOn ℂ {g : Gf E n | g.atPlace w ∈ localIntGL n w}) {y : M}
      (hy : y ∈ sphericalAt ρ w) :
    (offRep hw ρ).asAlgebraHom a y = ρ.asAlgebraHom a y := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨g, hg, rfl⟩ := ha
    have h_fixed : localRep hw ρ (g.atPlace w) y = y :=
      ((mem_sphericalAt_iff hw).1 hy ⟨g.atPlace w, hg⟩).trans (one_smul ℂ y)
    simp only [Representation.asAlgebraHom_of, apply_eq_offRep_localRep hw ρ g, h_fixed]
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul c a _ ha => simp [ha]

/-- The inclusion of the vectors of level `K` in those of the level that is cut down to the
stabiliser of the `i`-th coordinate line at `w`. -/
def cutInclusion (w : FinPlace E) (K : Subgroup (Gf E n)) {M : Type} [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ (Gf E n) M) (i : n) :
    levelSpace ρ K →ₗ[ℂ] levelSpace ρ (cutLevel K w (lineStabilizer w i)) :=
  Submodule.inclusion (levelSpace_anti inf_le_left)

/-- If `K` contains the maximal compact subgroup at the split place `w` and `J ≤ GL_n(𝒪_w)`, a
vector is fixed by the cut level `{k ∈ K | k_w ∈ J}` exactly when it is fixed by the part of `K`
off `w` and by `J` acting at `w`. -/
lemma mem_levelSpace_cutLevel_iff (hK : maxCompactAt n w ≤ K) (hJ : J ≤ localIntGL n w) {y : M} :
    y ∈ levelSpace ρ (cutLevel K w J) ↔
      y ∈ levelSpace (offRep hw ρ) K ∧ y ∈ levelSpace (localRep hw ρ) J := by
  refine ⟨fun hy ↦ ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨k, hk⟩
    have hk_off : offPlace hw k ∈ K := K.mul_mem hk <| K.inv_mem <|
      ofSplitPlace_mem_of_maxCompactAt_le hw hK (mem_stdLevel_iff.1 (IsLevel.le hk) w)
    exact hy ⟨offPlace hw k, hk_off, by simp [atPlace_offPlace]⟩
  · rintro ⟨x, hx⟩
    exact hy ⟨ofSplitPlace hw x, ofSplitPlace_mem_of_maxCompactAt_le hw hK (hJ hx),
      by simpa [atPlace_ofSplitPlace] using hx⟩
  · rintro ⟨h_off, h_local⟩ ⟨k, hk, hk_local⟩
    rw [apply_eq_offRep_localRep hw, h_local ⟨k.atPlace w, hk_local⟩, MonoidHom.one_apply, one_smul]
    exact h_off ⟨k, hk⟩

/-- If `K` is maximal at `w`, a vector is fixed by `K` exactly when it is fixed by the part of `K`
off `w` and by `GL_n(𝒪_w)`. -/
lemma mem_levelSpace_iff_offRep_localRep (hK : maxCompactAt n w ≤ K) {y : M} :
    y ∈ levelSpace ρ K ↔
      y ∈ levelSpace (offRep hw ρ) K ∧ y ∈ levelSpace (localRep hw ρ) (localIntGL n w) := by
  have h_cut : cutLevel K w (localIntGL n w) = K :=
    inf_eq_left.2 fun k hk ↦ mem_stdLevel_iff.1 (IsLevel.le hk) w
  rw [← mem_levelSpace_cutLevel_iff hw ρ hK le_rfl, h_cut]

/-- The elements of the group algebra that map the space of vectors fixed by the part of `K` off
`w` to itself act on the vectors of the cut level through their parts off `w`. -/
def offAction (hK : maxCompactAt n w ≤ K) (hJ : J ≤ localIntGL n w) :
    levelAlgebra (offRep hw ρ) K →ₐ[ℂ] End ℂ (levelSpace ρ (cutLevel K w J)) :=
  (levelAction ρ (cutLevel K w J)).comp <|
    ((mapDomainAlgHom ℂ ℂ (offPlace hw)).comp (levelAlgebra (offRep hw ρ) K).val).codRestrict _
      fun a y hy ↦ by
        obtain ⟨h_off, h_local⟩ := (mem_levelSpace_cutLevel_iff hw ρ hK hJ).1 hy
        change ρ.asAlgebraHom (mapDomain (offPlace hw) a) y ∈ levelSpace ρ (cutLevel K w J)
        rw [asAlgebraHom_mapDomain, mem_levelSpace_cutLevel_iff hw ρ hK hJ]
        exact ⟨a.2 y h_off, map_mem_levelSpace_of_commute h_local
          fun x ↦ commute_localRep_offRep hw ρ x a⟩

/-- The elements of the group algebra at `w` that map the space of vectors fixed by `J` to itself
act on the vectors of the cut level. -/
def localAction (hK : maxCompactAt n w ≤ K) (hJ : J ≤ localIntGL n w) :
    levelAlgebra (localRep hw ρ) J →ₐ[ℂ] End ℂ (levelSpace ρ (cutLevel K w J)) :=
  (levelAction ρ (cutLevel K w J)).comp <|
    ((mapDomainAlgHom ℂ ℂ (ofSplitPlace hw)).comp (levelAlgebra (localRep hw ρ) J).val).codRestrict
      _ fun u y hy ↦ by
        obtain ⟨h_off, h_local⟩ := (mem_levelSpace_cutLevel_iff hw ρ hK hJ).1 hy
        change ρ.asAlgebraHom (mapDomain (ofSplitPlace hw) u) y ∈ levelSpace ρ (cutLevel K w J)
        rw [asAlgebraHom_mapDomain, mem_levelSpace_cutLevel_iff hw ρ hK hJ]
        exact ⟨map_mem_levelSpace_of_commute h_off fun k ↦ commute_offRep_localRep hw ρ k u,
          u.2 y h_local⟩

/-- On the vectors of the cut level, `offAction` of `a` is the action of `a` through the parts off
`w`. -/
lemma coe_offAction_apply (hK : maxCompactAt n w ≤ K) (hJ : J ≤ localIntGL n w)
    (a : levelAlgebra (offRep hw ρ) K) (y : levelSpace ρ (cutLevel K w J)) :
    (offAction hw ρ hK hJ a y : M) = (offRep hw ρ).asAlgebraHom a y := by
  change ρ.asAlgebraHom (mapDomain (offPlace hw) (a : ℂ[Gf E n])) y = _
  rw [asAlgebraHom_mapDomain]

/-- On the vectors of the cut level, `localAction` of `u` is the action of `u` at `w`. -/
lemma coe_localAction_apply (hK : maxCompactAt n w ≤ K) (hJ : J ≤ localIntGL n w)
    (u : levelAlgebra (localRep hw ρ) J) (y : levelSpace ρ (cutLevel K w J)) :
    (localAction hw ρ hK hJ u y : M) = (localRep hw ρ).asAlgebraHom u y := by
  change ρ.asAlgebraHom (mapDomain (ofSplitPlace hw) (u : ℂ[GL n (LocField w)])) y = _
  rw [asAlgebraHom_mapDomain]

/-- On the vectors of the cut level, the operators from the parts off `w` commute with those from
the component at `w`. -/
lemma commute_offAction_localAction (hK : maxCompactAt n w ≤ K) (hJ : J ≤ localIntGL n w)
    (a : levelAlgebra (offRep hw ρ) K) (u : levelAlgebra (localRep hw ρ) J) :
    Commute (offAction hw ρ hK hJ a) (localAction hw ρ hK hJ u) := by
  have h_comm : Commute ((offRep hw ρ).asAlgebraHom a) ((localRep hw ρ).asAlgebraHom u) :=
    commute_asAlgebraHom (fun x ↦ (commute_localRep_offRep hw ρ x a).symm) u
  ext y
  simpa [coe_offAction_apply, coe_localAction_apply] using LinearMap.congr_fun h_comm.eq y

/-- Let `a` map the vectors fixed by the part of `K` off `w` to themselves, and `u` those fixed by
`J` at `w`. On the cut level, the operator of `a` times that of `u` is the action of the product of
the images of `u` under `ofSplitPlace` and of `a` under `offPlace`. -/
lemma coe_offAction_mul_localAction_apply (hK : maxCompactAt n w ≤ K) (hJ : J ≤ localIntGL n w)
    (a : levelAlgebra (offRep hw ρ) K) (u : levelAlgebra (localRep hw ρ) J)
    (y : levelSpace ρ (cutLevel K w J)) :
    ((offAction hw ρ hK hJ a * localAction hw ρ hK hJ u) y : M) =
      ρ.asAlgebraHom (mapDomain (ofSplitPlace hw) u * mapDomain (offPlace hw) a) y := by
  calc ((offAction hw ρ hK hJ a * localAction hw ρ hK hJ u) y : M)
    _ = (localRep hw ρ).asAlgebraHom u ((offRep hw ρ).asAlgebraHom a y) := by
      rw [(commute_offAction_localAction hw ρ hK hJ a u).eq, End.mul_apply, coe_localAction_apply,
        coe_offAction_apply]
    _ = _ := by rw [map_mul, End.mul_apply, asAlgebraHom_mapDomain, asAlgebraHom_mapDomain]

/-- The operator `T⁺` at `w` on the vectors whose level is the stabiliser of the `i`-th coordinate
line at `w` and `K` elsewhere. -/
def raiseAt (hK : maxCompactAt n w ≤ K) (i : n) :
    End ℂ (levelSpace ρ (cutLevel K w (lineStabilizer w i))) :=
  localAction hw ρ hK (lineStabilizer_le_localIntGL w i) ⟨lineHecke w i, fun y hy ↦ by
    simpa only [asAlgebraHom_lineHecke] using lineRaise_mem hy⟩

/-- The operator `T⁻` at `w` on the vectors whose level is the stabiliser of the `i`-th coordinate
line at `w` and `K` elsewhere. -/
def lowerAt (hK : maxCompactAt n w ≤ K) (i : n) :
    End ℂ (levelSpace ρ (cutLevel K w (lineStabilizer w i))) :=
  localAction hw ρ hK (lineStabilizer_le_localIntGL w i) ⟨lineHeckeLower w i, fun y hy ↦ by
    simpa only [asAlgebraHom_lineHeckeLower] using lineLower_mem hy⟩

/-- The mean over `GL_n(𝒪_w)`, from the level that is cut at `w` to the level `K`. -/
def meanAt (hK : maxCompactAt n w ≤ K) (i : n) :
    levelSpace ρ (cutLevel K w (lineStabilizer w i)) →ₗ[ℂ] levelSpace ρ K :=
  (sphericalMean (localRep hw ρ)).restrict fun y hy ↦ by
    obtain ⟨h_off, h_local⟩ := (mem_levelSpace_cutLevel_iff hw ρ hK
      (lineStabilizer_le_localIntGL w i)).1 hy
    rw [mem_levelSpace_iff_offRep_localRep hw ρ hK]
    refine ⟨map_mem_levelSpace_of_commute h_off fun k ↦ ?_, sphericalMean_mem h_local⟩
    simpa only [asAlgebraHom_sphericalMeanElement] using commute_offRep_localRep hw ρ k
      (sphericalMeanElement n w)

/-- `raiseAt` is the restriction of the operator `T⁺ = lineRaise` of the representation at `w`. -/
lemma coe_raiseAt_apply (hK : maxCompactAt n w ≤ K) (i : n)
    (y : levelSpace ρ (cutLevel K w (lineStabilizer w i))) :
    (raiseAt hw ρ hK i y : M) = lineRaise i (localRep hw ρ) y := by
  rw [raiseAt, coe_localAction_apply, asAlgebraHom_lineHecke]

/-- `lowerAt` is the restriction of the operator `T⁻ = lineLower` of the representation at `w`. -/
lemma coe_lowerAt_apply (hK : maxCompactAt n w ≤ K) (i : n)
    (y : levelSpace ρ (cutLevel K w (lineStabilizer w i))) :
    (lowerAt hw ρ hK i y : M) = lineLower i (localRep hw ρ) y := by
  rw [lowerAt, coe_localAction_apply, asAlgebraHom_lineHeckeLower]

omit [IsLevel K] in
lemma coe_cutInclusion_apply (i : n) (y : levelSpace ρ K) : (cutInclusion w K ρ i y : M) = y := rfl

/-- `meanAt`, followed by the inclusion of the vectors of level `K`, is `sphericalMean`, the mean
over `GL_n(𝒪_w)`. -/
lemma coe_cutInclusion_meanAt_apply (hK : maxCompactAt n w ≤ K) (i : n)
    (y : levelSpace ρ (cutLevel K w (lineStabilizer w i))) :
    ((cutInclusion w K ρ i ∘ₗ meanAt hw ρ hK i) y : M) = sphericalMean (localRep hw ρ) y := rfl

/-- If `K` contains the maximal compact subgroup at the split place `w`, the mean over `GL_n(𝒪_w)`
fixes the vectors of level `K`: `meanAt` is a left inverse of the inclusion `cutInclusion` of these
vectors in those of the level cut by the stabiliser of the `i`-th coordinate line at `w`. -/
lemma meanAt_comp_cutInclusion (hK : maxCompactAt n w ≤ K) (i : n) :
    meanAt hw ρ hK i ∘ₗ cutInclusion w K ρ i = .id := by
  ext ⟨y, hy⟩
  exact sphericalMean_eq_self ((mem_levelSpace_iff_offRep_localRep hw ρ hK).1 hy).right

/-- Let `K` contain the maximal compact subgroup at the split place `w`, and let the vectors of the
level cut by the stabiliser of a line at `w` form a finite-dimensional space. Let `a` map the space
of vectors fixed by the part of `K` off `w` to itself, let `A` and `T` be its actions through the
parts off `w` at the cut level and at level `K`, and let `e` be the mean over `GL_n(𝒪_w)`
(`meanAt` followed by the inclusion `cutInclusion`). Then `A * e` and `T` have the same trace. -/
lemma trace_offAction_mul_mean (hK : maxCompactAt n w ≤ K) (i : n)
    [Module.Finite ℂ (levelSpace ρ (cutLevel K w (lineStabilizer w i)))]
    (a : levelAlgebra (offRep hw ρ) K) {T : End ℂ (levelSpace ρ K)}
    (hT : ∀ y : levelSpace ρ K, (T y : M) = (offRep hw ρ).asAlgebraHom a y) :
    trace ℂ (levelSpace ρ (cutLevel K w (lineStabilizer w i)))
        (offAction hw ρ hK (lineStabilizer_le_localIntGL w i) a *
          (cutInclusion w K ρ i ∘ₗ meanAt hw ρ hK i)) =
      trace ℂ (levelSpace ρ K) T := by
  have : Module.Finite ℂ (levelSpace ρ K) :=
    .of_injective (cutInclusion w K ρ i) (Submodule.inclusion_injective _)
  have h_restrict : offAction hw ρ hK (lineStabilizer_le_localIntGL w i) a ∘ₗ cutInclusion w K ρ i =
      cutInclusion w K ρ i ∘ₗ T := by
    ext y
    simp [coe_offAction_apply, coe_cutInclusion_apply, hT]
  rw [End.mul_eq_comp, ← comp_assoc, h_restrict, trace_comp_comm', ← comp_assoc,
    meanAt_comp_cutInclusion, id_comp]

/-- Let `K` contain the maximal compact subgroup at the split place `w` and let `a` map the space of
vectors fixed by the part of `K` off `w` to itself. On the level cut by the stabiliser of the `i`-th
coordinate line at `w`, the `l`-th power of the operator of `a` times `(T⁺) ^ m` (`T⁺ = raiseAt`)
is the action of the group algebra element obtained from `lineHecke w i ^ m` by `ofSplitPlace`
(placing it at `w`), times the one obtained from `a ^ l` by `offPlace` (taking the part off `w`). -/
lemma coe_offAction_pow_mul_raiseAt_pow_apply (hK : maxCompactAt n w ≤ K) (i : n)
    (a : levelAlgebra (offRep hw ρ) K) (l m : ℕ)
    (y : levelSpace ρ (cutLevel K w (lineStabilizer w i))) :
    ((offAction hw ρ hK (lineStabilizer_le_localIntGL w i) a ^ l * raiseAt hw ρ hK i ^ m) y : M) =
      ρ.asAlgebraHom (mapDomain (ofSplitPlace hw) (lineHecke w i ^ m) *
        mapDomain (offPlace hw) ((a : ℂ[Gf E n]) ^ l)) y := by
  simp only [raiseAt, ← map_pow, coe_offAction_mul_localAction_apply, SubmonoidClass.coe_pow]

end Algebraic

variable {K : Subgroup (Gf E n)} {M M' : Type}
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [NormedAddCommGroup M'] [InnerProductSpace ℂ M']
  {ρ : Representation ℂ (Gf E n) M} {ρ' : Representation ℂ (Gf E n) M'} [IsLevel K]

/-- Let `K` contain the maximal compact subgroup at the split place `w`, whose residue field has
`q` elements, and let `a` map the vectors fixed by the part of `K` off `w` to themselves. In a
unitary representation, on the level cut by the stabiliser of a line at `w`, the operator `A` of
`a`, the operators `T⁺`, `T⁻` and the mean `e` over `GL_n(𝒪_w)` satisfy `LineRelation d c` with
`d = q ^ (n - 2)` and `c = q ^ n - 1`: `T⁻` is adjoint to `T⁺`, `T⁺ T⁻ = d (1 + c e)`, `e` is
idempotent, and `A` commutes with `T⁺` and `T⁻`. -/
lemma lineRelation_offAction (hw : w.IsSplit) (hK : maxCompactAt n w ≤ K) (i : n)
    (hρ : ∀ (g : Gf E n) (x y : M), ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (a : levelAlgebra (offRep hw ρ) K) :
    LineRelation ((w.q : ℝ) ^ (Fintype.card n - 2 : ℤ)) ((w.q : ℝ) ^ Fintype.card n - 1)
      (offAction hw ρ hK (lineStabilizer_le_localIntGL w i) a) (raiseAt hw ρ hK i)
        (lowerAt hw ρ hK i)
      (cutInclusion w K ρ i ∘ₗ meanAt hw ρ hK i) := by
  have hq : (1 : ℝ) < w.q := Nat.one_lt_cast.2 w.one_lt_q
  have h_local (y : levelSpace ρ (cutLevel K w (lineStabilizer w i))) :
      (y : M) ∈ levelSpace (localRep hw ρ) (lineStabilizer w i) :=
    ((mem_levelSpace_cutLevel_iff hw ρ hK (lineStabilizer_le_localIntGL w i)).1 y.property).right
  exact
    { d_pos := by positivity
      c_pos := sub_pos.2 (one_lt_pow₀ hq (Fintype.card_pos_iff.2 ⟨i⟩).ne')
      idem := by
        rw [IsIdempotentElem, End.mul_eq_comp, comp_assoc, ← comp_assoc (meanAt hw ρ hK i),
          meanAt_comp_cutInclusion, id_comp]
      adjoint x y := by
        simpa only [Submodule.coe_inner, coe_raiseAt_apply, coe_lowerAt_apply] using
          inner_lineRaise (fun g ↦ hρ (ofSplitPlace hw g)) (h_local x) (h_local y)
      mul_eq := by
        ext y
        simp [coe_raiseAt_apply, coe_lowerAt_apply, lineRaise_lineLower (h_local y),
          ← coe_cutInclusion_meanAt_apply hw ρ hK i]
      commute_plus := commute_offAction_localAction hw ρ hK (lineStabilizer_le_localIntGL w i) a _
      commute_minus :=
        commute_offAction_localAction hw ρ hK (lineStabilizer_le_localIntGL w i) a _ }

/-- Let the level `K` contain the maximal compact subgroup at the split place `w`, and let `a` be
in `universalLevelAlgebra K` (it maps the space of `K`-fixed vectors to itself in every
representation) and be a combination of elements that are integral at `w`. Consider two unitary
representations whose spaces of vectors of level `K'`, the level cut by the stabiliser of a line at
`w`, are finite-dimensional. Suppose that for all `l`, `m` the element
`b = (T⁺) ^ (m + 1) * a' ^ (l + 1)` of the group algebra, with `T⁺ = lineHecke w i` placed at `w`
and `a'` the part of `a` off `w`, has the same trace in both at level `K'` (`h_trace`, where `S`,
`S'` are the two operators by which `b` acts there). Then `a` has the same trace at level `K` in
both. -/
theorem trace_eq_of_trace_cutLevel_eq (hw : w.IsSplit) (hK : maxCompactAt n w ≤ K) (i : n)
    (hρ : ∀ (g : Gf E n) (x y : M), ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hρ' : ∀ (g : Gf E n) (x y : M'), ⟪ρ' g x, ρ' g y⟫_ℂ = ⟪x, y⟫_ℂ)
    [Module.Finite ℂ (levelSpace ρ (cutLevel K w (lineStabilizer w i)))]
    [Module.Finite ℂ (levelSpace ρ' (cutLevel K w (lineStabilizer w i)))]
    {a : ℂ[Gf E n]} (ha : a ∈ universalLevelAlgebra K)
    (h_int : a ∈ spanOn ℂ {g : Gf E n | g.atPlace w ∈ localIntGL n w})
    (h_trace : ∀ (l m : ℕ) (S : End ℂ (levelSpace ρ (cutLevel K w (lineStabilizer w i))))
      (S' : End ℂ (levelSpace ρ' (cutLevel K w (lineStabilizer w i)))),
      let K' : Subgroup (Gf E n) := cutLevel K w (lineStabilizer w i)
      let b : ℂ[Gf E n] := mapDomain (ofSplitPlace hw) (lineHecke w i ^ (m + 1)) *
        mapDomain (offPlace hw) (a ^ (l + 1))
      (∀ y : levelSpace ρ K', (S y : M) = ρ.asAlgebraHom b y) →
      (∀ y : levelSpace ρ' K', (S' y : M') = ρ'.asAlgebraHom b y) →
        trace ℂ (levelSpace ρ K') S = trace ℂ (levelSpace ρ' K') S')
    {T : End ℂ (levelSpace ρ K)} {T' : End ℂ (levelSpace ρ' K)}
    (hT : ∀ y : levelSpace ρ K, (T y : M) = ρ.asAlgebraHom a y)
    (hT' : ∀ y : levelSpace ρ' K, (T' y : M') = ρ'.asAlgebraHom a y) :
    trace ℂ (levelSpace ρ K) T = trace ℂ (levelSpace ρ' K) T' := by
  let a₁ : levelAlgebra (offRep hw ρ) K := ⟨a, universalLevelAlgebra_le K (offRep hw ρ) ha⟩
  let a₂ : levelAlgebra (offRep hw ρ') K := ⟨a, universalLevelAlgebra_le K (offRep hw ρ') ha⟩
  -- Vectors of level `K` are spherical at `w`, so `a` acts on them through its part off `w`.
  have hT_off (y : levelSpace ρ K) : (T y : M) = (offRep hw ρ).asAlgebraHom a y :=
    (hT y).trans (asAlgebraHom_offRep_apply hw ρ h_int (levelSpace_anti hK y.2)).symm
  have hT_off' (y : levelSpace ρ' K) : (T' y : M') = (offRep hw ρ').asAlgebraHom a y :=
    (hT' y).trans (asAlgebraHom_offRep_apply hw ρ' h_int (levelSpace_anti hK y.2)).symm
  rw [← trace_offAction_mul_mean hw ρ hK i a₁ hT_off,
    ← trace_offAction_mul_mean hw ρ' hK i a₂ hT_off']
  -- By the line relation it suffices to compare the traces of the products of positive powers.
  refine (lineRelation_offAction hw hK i hρ a₁).trace_mul_mean_eq
    (lineRelation_offAction hw hK i hρ' a₂) fun l m ↦ ?_
  exact h_trace l m _ _ (coe_offAction_pow_mul_raiseAt_pow_apply hw ρ hK i a₁ (l + 1) (m + 1))
    (coe_offAction_pow_mul_raiseAt_pow_apply hw ρ' hK i a₂ (l + 1) (m + 1))

end New


end
