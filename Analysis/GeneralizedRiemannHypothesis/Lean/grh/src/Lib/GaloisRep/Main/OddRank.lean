import Lib.GaloisRep.BaseChange.PrimeDegreeTransfer
import Lib.GaloisRep.Main.SplitCase

/-!
# Attached Galois representations in odd rank and their descent along weak base change

This file proves that eigenforms on the definite space `New.stdSpace` of odd rank over stably
unramified CM fields have attached Galois representations. It first proves a descent result along
a step of weak base change. The general odd-rank case is then reduced to the split case of
`Lib.GaloisRep.Main.SplitCase` by quadratic base changes, whose representations are glued on open
subgroups of the Galois group.

## Main definitions and results

* `New.IsWeakBaseChange.hasHeckePolyAt_of_decompGroup_le`: along a step of weak base change from f
  to f', at a split place off S and its conjugate whose decomposition group lies in the open
  subgroup N of the step, the Hecke polynomial of f passes to f'.
* `New.IsWeakBaseChange.attached_comp_stepKerInclusion`: a representation r' attached to f',
  restricted to N (`New.QZChar.stepKer`), is attached to the polynomials of f.
* `New.IsWeakBaseChange.descendsAt`: the local conditions on r' pass to every representation
  attached to f (`New.GaloisRep.DescendsAt`).
* `New.GaloisRep.sphericalCompat_of_odd`: the statement `New.GaloisRep.SphericalCompat` (an
  eigenform has an attached Galois representation, and every attached representation is compatible
  at a spherical place w) for the definite space `New.stdSpace` of odd rank over a stably unramified
  CM field (`New.HasPrimitiveRoot5040`). The split case is applied to base changes of f along
  quadratic steps. The representations obtained on open subgroups are glued
  (`New.GaloisRep.exists_attached_of_open_subgroups`), and the local properties at w descend from
  one step (`New.IsWeakBaseChange.isCompatibleAt_of_attached`).

Notions from other files:
* `New.IsWeakBaseChange` μ Z f f': the set Z is finite and, for u above w ∉ Z ∪ Z̄, sphericity
  passes from f to f' at `New.IsStepUnramifiedAt` places, and Hecke polynomials pass from f to f' at
  `New.IsMatched` places.
* `New.IsEigenform`: f ≠ 0, and almost all places w of prime norm are split and f has the Hecke
  polynomial P w at w.
* `New.GaloisRep.Attached` P r i: r is continuous with non-degenerate trace form, i (by default the
  identity) is an open map to Gal(Ω/E), and at most Frobenius elements the characteristic
  polynomials of r are ℓ-adically close to those given by P.

## Relation to the literature

Galois representations attached to forms on definite unitary groups. The form proved
is for the standard definite unitary group of odd rank over a stably unramified CM field
(`New.HasPrimitiveRoot5040`). At a place whose local compact group fixes the form,
each attached ℓ-adic representation is unramified or crystalline with the Hodge–Tate jumps of the
weight, and each Hecke polynomial there kills geometric Frobenius. Here "attached" asks, beyond
continuity and a non-degenerate trace form, only that Hecke polynomials are ℓ-adically close to
characteristic polynomials at most Frobenius elements. The construction uses ℓ-adic limits, and
quadratic base changes whose representations are glued on open subgroups of the Galois group.
Source: Chenevier, Harris, Construction of automorphic Galois
representations II, Camb. J. Math. 1 (2013), Thm 3.2.3; with Labesse, Changement de base CM et
séries discrètes (2011), Cor. 5.3, and Barnet-Lamb, Gee, Geraghty, Taylor, Potential automorphy and
change of weight (2014), Thm 2.1.1.
-/

/-!
## Descent along a step of weak base change

A continuous character χ of Gal(Ω/E) with values in ℚ/ℤ gives the field L = `New.QZChar.stepField` χ
cut out by g ↦ χ g + χ (gᶜ), the idele character `New.QZChar.ideleChar` χ, and the open subgroup
N = `New.QZChar.stepKer` χ = Gal(Ω/L) ∩ ker χ of Gal(Ω/E).

Places of Ω are valuation subrings A (`New.IsPlaceOver`, decomposition group `New.decompGroup`).
-/

namespace New

open NumberField Subgroup GaloisRep QZChar

variable {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ]
  {E n M M' : Type} [Field E] [CMType E] [EmbeddedNumberField E] [Fintype n] [DecidableEq n]
  {χ : QZChar Gal(Ω/E)} {f : Gf E n → M → ℂ} {f' : Gf (stepField χ) n → M' → ℂ}
  {S : Set (FinPlace E)} {P : FinPlace E → Polynomial ℂ}
  {P' : FinPlace (stepField χ) → Polynomial ℂ} {r' : GalRep ℓ (stepField χ) n}

/-- The subgroup Gal(Ω/L) ∩ ker χ of Gal(Ω/E), where L = `New.QZChar.stepField` χ: the elements
killed by χ and by its symmetrisation. -/
noncomputable abbrev QZChar.stepKer (χ : QZChar Gal(Ω/E)) : Subgroup Gal(Ω/E) :=
  ker (symmetrise χ) ⊓ ker χ

lemma QZChar.isOpen_stepKer (χ : QZChar Gal(Ω/E)) : (stepKer χ).IsOpen :=
  (isOpen_ker (symmetrise χ)).inter (isOpen_ker χ)

lemma QZChar.stepKer_le_fixingSubgroup (χ : QZChar Gal(Ω/E)) :
    stepKer χ ≤ (stepField χ).fixingSubgroup :=
  fun s hs x ↦ x.prop ⟨s, (mem_inf.1 hs).1⟩

/-- The inclusion of Gal(Ω/L) ∩ ker χ in Gal(Ω/L), where L = `New.QZChar.stepField` χ. -/
noncomputable def QZChar.stepKerInclusion (χ : QZChar Gal(Ω/E)) :
    stepKer χ →* Gal(Ω/stepField χ) :=
  (stepField χ).fixingSubgroupEquiv.toMonoidHom.comp (inclusion (stepKer_le_fixingSubgroup χ))

/-- The local conditions at the valuation subring A of Ω pass from the representation r' of
Gal(Ω/L), where L = `New.QZChar.stepField` χ, to the representation r of Gal(Ω/E). -/
structure GaloisRep.DescendsAt (χ : QZChar Gal(Ω/E)) (r' : GalRep ℓ (stepField χ) n)
    (r : GalRep ℓ E n) (A : ClosurePlace) : Prop where
  /-- If r' is of finite type at A, so is r. -/
  isFiniteTypeAt (h : IsFiniteTypeAt r' A) : IsFiniteTypeAt r A
  /-- If r' has the jumps of the weight κ pulled back to L, in rank m, then r has those of κ. -/
  hasJumpsAt {κ : Weight E} (m : ℕ) (h : HasJumpsAt r' A (jumps κ.baseChange m)) :
    HasJumpsAt r A (jumps κ m)
  /-- For s in Gal(Ω/L) ∩ ker χ, a polynomial that kills the image of s in Gal(Ω/L) for r' kills s
  for r. -/
  polyKillsAt (s : stepKer χ) (Q : Polynomial (PadicAlgCl ℓ))
    (h : PolyKillsAt r' A (stepKerInclusion χ s) Q) : PolyKillsAt r A s.val Q

/-- If the decomposition group of a place `A` of the closure above `w` is killed by `χ` and by its
symmetrisation, so that it fixes the field of the step, then `w` is matched: `ideleChar χ` is
trivial on the local ideles at `w`, and `w` splits completely in the field of the step. -/
lemma IsPlaceOver.isMatched_of_decompGroup_le {A : ClosurePlace} {w : FinPlace E}
    (hA : IsPlaceOver A w) (h_dec : decompGroup Gal(Ω/E) A ≤ stepKer χ) :
    IsMatched (stepField χ) (ideleChar χ) w := by
  refine ⟨fun x ↦ ?_, hA.q_eq_and_comap_ne_self_of_decompGroup_le (h_dec.trans inf_le_left)⟩
  simp [(hA.artinAt_trivial_iff_decompGroup_le χ).2 (h_dec.trans inf_le_right)]

/-- Let `f'` be a weak base change of `f` to the field `stepField χ`, off `S` and its conjugate.
Let the place `A` of `Ω` lie over a split place `w` of `E` outside these sets, with
decomposition group killed by `χ` and by its symmetrisation. If `f` has the Hecke polynomial `Q`
at `w`, then every place `u` of `stepField χ` above `w` has the norm of `w` and is split, and `f'`
has the Hecke polynomial `Q` at `u`. -/
lemma IsWeakBaseChange.hasHeckePolyAt_of_decompGroup_le
    (hs : IsWeakBaseChange (ideleChar χ) S f f') {w : FinPlace E} (h_off : w ∉ S.conjClosure)
    {A : ClosurePlace} (hA : IsPlaceOver A w) (h_dec : decompGroup Gal(Ω/E) A ≤ stepKer χ)
    {u : FinPlace (stepField χ)} (h_below : u.below E = w)
    {hw : w.IsSplit} {Q : Polynomial ℂ} (hQ : HasHeckePolyAt f w hw Q) :
    u.q = w.q ∧ ∃ hu : u.IsSplit, HasHeckePolyAt f' u hu Q := by
  have h_matched : IsMatched (stepField χ) (ideleChar χ) w := hA.isMatched_of_decompGroup_le h_dec
  exact ⟨(h_matched.2 u h_below).1, (hs.2 w h_off u h_below).2 h_matched hw Q hQ⟩

/-- A nonzero function has at most one Hecke polynomial at a split place. -/
lemma HasHeckePolyAt.unique (hf : f ≠ 0) {w : FinPlace E} {hw hw' : w.IsSplit}
    {Q Q' : Polynomial ℂ} (hQ : HasHeckePolyAt f w hw Q) (hQ' : HasHeckePolyAt f w hw' Q') :
    Q = Q' := by
  obtain ⟨-, t, rfl, ht⟩ := hQ
  obtain ⟨-, t', rfl, ht'⟩ := hQ'
  have h_eq : t = t' := funext fun j ↦ smul_left_injective ℂ hf ((ht j).symm.trans (ht' j))
  rw [h_eq]

/-- Let `χ` be a continuous `ℚ/ℤ`-valued character of Gal(Ω/E), and let `L = New.QZChar.stepField χ`
be the fixed field of the kernel of `g ↦ χ g + χ (gᶜ)`. Let `f` and `f'` be eigenforms on the
unitary groups over `E` and `L` with systems of polynomials `P` and `P'`, let `f'` be a weak base
change of `f` off `S` relative to the idele character of `χ`, and let `r'` be attached to `P'`. Then
the restriction of `r'` to the subgroup Gal(Ω/L) ∩ ker χ of Gal(Ω/E) is attached to `P` along the
inclusion of this subgroup in Gal(Ω/E). -/
lemma IsWeakBaseChange.attached_comp_stepKerInclusion
    (hs : IsWeakBaseChange (ideleChar χ) S f f') (hr' : Attached P' r') (he' : IsEigenform f' P')
    (he : IsEigenform f P) :
    Attached P (r'.comp (stepKerInclusion χ)) (stepKer χ).subtype := by
  -- Almost all places with a Frobenius element in `stepKer χ` split in `L` with the same Hecke
  -- polynomial, so the estimate for `r'` above such a place is the estimate wanted.
  let res : Gal(Ω/stepField χ) →* Gal(Ω/E) := AlgEquiv.restrictScalarsHom E
  have h_res : Topology.IsOpenEmbedding res := isOpenEmbedding_galois_restrict res (by simp [res])
  have h_cont : Continuous (stepKerInclusion χ) := h_res.continuous_iff.2 continuous_subtype_val
  have h_normal : (stepKerInclusion χ).range.Normal := by
    rw [stepKerInclusion, MonoidHom.range_comp, inclusion_range]
    exact Normal.map inferInstance _ (stepField χ).fixingSubgroupEquiv.surjective
  have h_nondeg : IsTraceNondeg (r'.comp (stepKerInclusion χ)) :=
    hr'.isTraceNondeg.comp (stepKerInclusion χ) h_normal
  refine ⟨hr'.continuous.comp h_cont, h_nondeg, (isOpen_stepKer χ).isOpenMap_subtype_val,
    fun η hη ↦ ?_⟩
  -- At most Frobenius data of `L`, `f'` has the polynomial given by `P'`.
  have h_most' : ∀ᶠ y : FrobeniusDatum (stepField χ) in mostFrobenii (stepField χ),
      ∃ hy : y.place.IsSplit, HasHeckePolyAt f' y.place hy (P' y.place) :=
    eventually_mostFrobenii he'.2 fun y hy ↦ hy y.prime_q
  -- At most Frobenius data `x` of `E`, `f` has the polynomial `P x.place`, inertia lies in
  -- `stepKer χ`, and neither `x.place` nor its conjugate is in `S`.
  have h_most : ∀ᶠ x : FrobeniusDatum E in mostFrobenii E,
      (∃ hx : x.place.IsSplit, HasHeckePolyAt f x.place hx (P x.place)) ∧
      inertiaGroup Gal(Ω/E) x.valuationSubring ≤ stepKer χ ∧ x.place ∉ S.conjClosure :=
    eventually_mostFrobenii
      (he.2.and ((finite_ramified (isOpen_stepKer χ)).and hs.1.conjClosure.compl_mem_cofinite))
      fun x ⟨h_eigen, h_inertia, h_off⟩ ↦ ⟨h_eigen x.prime_q, h_inertia _ x.isPlaceOver, h_off⟩
  filter_upwards [h_most,
    eventually_mostFrobenii_of_isOpenEmbedding h_res (FinPlace.below E)
      ((hr'.eventually_norm_coeff_le hη).and h_most')]
  rintro x ⟨⟨hx_split, h_hecke⟩, h_inertia, h_off⟩ h_above s (hs_eq : s.val = x.frob)
  obtain ⟨u, hu, h_below⟩ := x.isPlaceOver.exists_above (L := stepField χ)
  -- Inertia and the Frobenius element lie in `stepKer χ`, hence so does the decomposition group.
  -- So `x.place` is matched, and `f'` has the polynomial `P x.place` at `u`.
  have h_dec : decompGroup Gal(Ω/E) x.valuationSubring ≤ stepKer χ :=
    x.isPlaceOver.decompGroup_le x.isFrob_inv (isOpen_stepKer χ) h_inertia (by simp [← hs_eq])
  obtain ⟨hq, hu_split, h_hecke_u⟩ :=
    hs.hasHeckePolyAt_of_decompGroup_le h_off x.isPlaceOver h_dec h_below h_hecke
  -- The image of `s` is a geometric Frobenius element of `L` at `u`.
  have hu_prime : u.q.Prime := by simpa [hq] using x.prime_q
  have hu_frob : IsFrob x.valuationSubring u.q (stepKerInclusion χ s)⁻¹ :=
    show IsFrob x.valuationSubring u.q s.val⁻¹ by simpa only [hq, hs_eq] using x.isFrob_inv
  obtain ⟨h_close, hu_split', h_hecke_u'⟩ :=
    h_above ⟨u, x.valuationSubring, stepKerInclusion χ s, hu_prime, hu, hu_frob⟩ h_below hs_eq
  have hP : P' u = P x.place := h_hecke_u'.unique he'.1 h_hecke_u
  simpa only [hP, MonoidHom.comp_apply] using h_close (stepKerInclusion χ s) rfl

/-- Let `χ` be a continuous `ℚ/ℤ`-valued character of `Gal(Ω/E)`, and let
`L = New.QZChar.stepField χ` be the field cut out by `g ↦ χ g + χ (gᶜ)`. Let `f'` on `L` be a weak
base change of `f` off the finite set `S` of places of `E`, relative to the idele character
`exp(2πi χ ∘ Art)`, with both eigenforms for the systems `P'` and `P`. If `r'` is attached to `P'`
and `r` to `P`, then the local conditions at every valuation subring `A` of `Ω` pass from `r'` to
`r` (`New.GaloisRep.DescendsAt`). -/
lemma IsWeakBaseChange.descendsAt (hs : IsWeakBaseChange (ideleChar χ) S f f')
    (hr' : Attached P' r') (he' : IsEigenform f' P') (he : IsEigenform f P) {r : GalRep ℓ E n}
    (hr : Attached P r) (A : ClosurePlace) :
    DescendsAt χ r' r A := by
  classical
  -- On `stepKer χ`, both `r` and `r'` are attached to `P`. So they have the same trace and are
  -- conjugate there, and the local conditions pass.
  let L : IntermediateField E Ω := stepField χ
  let res : Gal(Ω/L) →* Gal(Ω/E) := AlgEquiv.restrictScalarsHom E
  have h_res : Topology.IsOpenEmbedding res := isOpenEmbedding_galois_restrict res (by simp [res])
  have h_att : Attached P (r'.comp (stepKerInclusion χ)) (stepKer χ).subtype :=
    hs.attached_comp_stepKerInclusion hr' he' he
  have h_trace (s : stepKer χ) : (r' (stepKerInclusion χ s)).val.trace = (r s).val.trace :=
    h_att.trace_eq hr s rfl
  have h_normal : (stepKer χ).subtype.range.Normal := by
    rw [range_subtype]
    infer_instance
  obtain ⟨Z, hZ⟩ : ∃ Z : GL n (PadicAlgCl ℓ),
      ∀ s : stepKer χ, (r' (stepKerInclusion χ s)).val * Z = Z * r s :=
    h_att.isTraceNondeg.exists_conj_of_trace_eq _ (AlgHom.id (PadicAlgCl ℓ) _)
      (hr.isTraceNondeg.comp (stepKer χ).subtype h_normal).hasSemiprimeSpan h_trace
  -- `Z` intertwines `r ∘ res` with `r'` on the neighbourhood `res ⁻¹' stepKer χ` of `1`.
  have h_nhds : res ⁻¹' stepKer χ ∈ nhds 1 :=
    ((isOpen_stepKer χ).preimage h_res.continuous).mem_nhds (stepKer χ).one_mem
  obtain ⟨h_finite, h_jumps, h_kills⟩ := local_clauses_of_retract (A := A) 1 (algebraMap E L)
    (by simp) (by simp [res]) h_res h_nhds (fun g hg ↦ hZ ⟨res g, hg⟩) Z.inv_val
  refine ⟨h_finite, fun {κ} m hm ↦ h_jumps Z.val_inv ?_,
    fun s Q ↦ h_kills (stepKerInclusion χ s) s.prop⟩
  -- `τ` lies in the CM type of `L` exactly when its restriction lies in that of `E`.
  have h_baseChange :
      jumps κ.baseChange m = fun τ : L →+* ℂ ↦ jumps κ m (τ.comp (algebraMap E L)) := by
    ext1 τ
    simp only [jumps, CMTypeOver.eq_chosen_iff (K := E) τ]
    rfl
  rwa [h_baseChange] at hm

/-- Let `f'` be a weak base change of `f` to `stepField χ`, both eigenforms, with `r'` and `r`
attached to their systems of polynomials. Let `A` lie over `w ∉ S ∪ S̄` and let `u` be a place of
`stepField χ` above `w`. If `χ` and its symmetrisation kill inertia at `A`, and also decomposition
when `w` is split, then compatibility of `r'` with `f'` at `u` (`New.GaloisRep.IsCompatibleAt`:
good, with the jumps of the weight in rank `a`, and at a split place each Hecke polynomial kills
geometric Frobenius) gives that of `r` with `f` at `w`. -/
lemma IsWeakBaseChange.isCompatibleAt_of_attached {κ : Weight E} {a : ℕ}
    {f : Gf E n → WeylIndex n κ.1 → ℂ} {f' : Gf (stepField χ) n → WeylIndex n κ.baseChange.1 → ℂ}
    (hs : IsWeakBaseChange (ideleChar χ) S f f') (hr' : Attached P' r')
    (he' : IsEigenform f' P') (he : IsEigenform f P) {r : GalRep ℓ E n} (hr : Attached P r)
    {w : FinPlace E} (h_off : w ∉ S.conjClosure) {A : ClosurePlace} (hA : IsPlaceOver A w)
    (h_ine : inertiaGroup Gal(Ω/E) A ≤ stepKer χ)
    (h_dec : w.IsSplit → decompGroup Gal(Ω/E) A ≤ stepKer χ) {u : FinPlace (stepField χ)}
    (h_below : u.below E = w) (h_compat : IsCompatibleAt f' a u r' A) :
    IsCompatibleAt f a w r A := by
  obtain ⟨h_fin, h_jump, h_poly⟩ := hs.descendsAt hr' he' he hr A
  obtain ⟨h_good, h_jump', h_poly'⟩ := h_compat
  refine ⟨?_, h_jump _ h_jump', fun hw Q hQ s hs_frob ↦ ?_⟩
  · obtain ⟨h_fin', h_one⟩ := isGoodAt_iff.1 h_good
    exact isGoodAt_iff.2 ⟨h_fin h_fin', fun s s_mem ↦ h_poly ⟨s, h_ine s_mem⟩ _ (h_one _ s_mem)⟩
  · -- The split place `w` is matched, so `f'` has the polynomial `Q` above `w`.
    obtain ⟨hq, hu_split, hQ'⟩ :=
      hs.hasHeckePolyAt_of_decompGroup_le h_off hA (h_dec hw) h_below hQ
    exact h_poly ⟨s, inv_mem (h_dec hw hs_frob.1)⟩ _ (h_poly' hu_split Q hQ' _ (by rwa [hq]))

end New

/-! ## The general odd-rank case -/

section QuadraticDescent

open NumberField Ideal Subgroup Module.End New.QZChar

/-- Let `μ` be the character of a step `E' / E` (`New.IsStep`: a CM extension of prime degree with
an idele character), with `E'` stably unramified (`New.HasPrimitiveRoot5040`), and `f` a nonzero
form of weight `κ` over `E`. Some eigenform `F` over `E'`, of the pulled back weight, is a weak
base change of `f` with empty exceptional set (`New.IsWeakBaseChange`). -/
lemma New.GaloisRep.exists_weak_baseChange {E E' n : Type} [Field E] [CMType E] [Field E']
    [Algebra E E'] [CMTypeOver E E'] [Fintype n] [DecidableEq n] [HasPrimitiveRoot5040 E']
    {μ : (𝔸f E)ˣ →* ℂˣ} (hμ : IsStep (E := E) E' μ) {κ : Weight E}
    {f : Gf E n → WeylIndex n κ.1 → ℂ} (hf : f ∈ (stdSpace E n).forms κ) (hf_ne : f ≠ 0) :
    ∃ (F : (stdSpace E' n).forms κ.baseChange) (P' : FinPlace E' → Polynomial ℂ),
      IsEigenform F.val P' ∧ IsWeakBaseChange μ ∅ f F.val := by
  classical
  -- This is the transfer for trivial local data, whose only operator is the identity; its trace
  -- on a space containing `f ≠ 0` is not zero.
  let π : Representation ℂ Unit ((stdSpace E n).forms κ) :=
    localFormTranslation κ (1 : Unit →* Gf E n)
  have h_id : heckeFun π ⊤ 1 = 1 := by
    have : Unique (Unit ⧸ (⊤ : Subgroup Unit)) := .mk' _
    simp [heckeFun, finsum_unique, π]
  have h_trace : HasNonzeroTraceAround π (heckeFun π ⊤ 1)
      (heckeGenEigenspace π ⊤ ((1 : Unit → Unit → ℂ) ∘ ![]) 0) ⟨f, hf⟩ := by
    intro W hW _
    refine trace_restrict_ne_zero one_ne_zero (fun h_bot ↦ hf_ne ?_) fun x _ ↦ ?_
    · exact congrArg Subtype.val (h_bot.le ⟨by simp [π], hW⟩)
    · exact eigenspace_le_maxGenEigenspace (by simp [h_id])
  obtain ⟨F, P', hF, h_bc, -⟩ := exists_isWeakBaseChange_of_matching (hμ := hμ) ⟨f, hf⟩
    isLocalMatching_empty (o := ![]) (θ := 0) (j₀ := ()) (hj₀ := rfl) (h_comm := by simp)
    (h_stable := nofun) (h_trace := h_trace)
  exact ⟨F, P', hF, h_bc⟩

/-- Let the step given by `χ` be an extension of prime degree with idele character
(`New.IsStep`). If the decomposition group of `A` is killed by the symmetrisation of `χ`, so fixes
the field of the step, and `χ` kills inertia, then the step is unramified at the place below `A`
(`New.IsStepUnramifiedAt`: the extension and the character are unramified at each place above). -/
lemma New.GaloisRep.isStepUnramifiedAt_of_decompGroup_le {E : Type} [Field E]
    [EmbeddedNumberField E] [CMType E]
    {χ : QZChar Gal(Ω/E)} (h_step : IsStep (stepField χ) (ideleChar χ))
    {x : FinPlace E} {A : ClosurePlace} (hA : IsPlaceOver A x)
    (h_dec : decompGroup Gal(Ω/E) A ≤ QZChar.ker (symmetrise χ))
    (h_inertia : inertiaGroup Gal(Ω/E) A ≤ QZChar.ker χ) :
    IsStepUnramifiedAt (stepField χ) (ideleChar χ) x := by
  rintro v rfl
  -- No nontrivial automorphism of the field of the step fixes `v`, so none is in inertia at `v`.
  obtain ⟨-, comap_ne⟩ := hA.q_eq_and_comap_ne_self_of_decompGroup_le h_dec v rfl
  -- As `χ` kills inertia, it kills the Artin symbols of the local units below `v`.
  have h_units : ∀ z : (LocField (v.below E))ˣ, Valued.v z.val = 1 →
      abelianLift χ (artinAt Gal(Ω/E) (v.below E) z) = 1 :=
    (hA.artinAt_units_trivial_iff_inertiaGroup_le χ).mpr fun _ h ↦ h_inertia h
  refine ⟨h_step.exists_gal_ne_one.imp fun σ hσ ↦
    notMem_inertia_of_comap_ne (comap_ne σ hσ), fun y hy ↦ ?_⟩
  change ideleChar χ (locIdele (v.below E) (localNorm E v y)) = 1
  simp [localNorm, ideleAt, h_units, v_adeleNorm_eq_one, locIdele_mem_idelesUnitOff hy]

/-- Let `ρ₀` on a normal subgroup `N₀` of `Gal(Ω/E)` and the `ρ T` on open normal subgroups `N T`
be attached to the same system `P` along the inclusions (`New.GaloisRep.Attached`: the
representation is continuous with non-degenerate trace form, the inclusion is open, and the
characteristic polynomials are `ℓ`-adically close to those of `P` at most Frobenius elements). Let
`I` be a set such that every subgroup containing `I` meets every coset of `N₀`, and such that each
conjugate of an element of `I` lies in every `N T` and is killed by `ρ T`. If every arithmetic
Frobenius element at a place `A` of `Ω` over a place `y` of prime norm lies in some `N T`, then a
representation of `Gal(Ω/E)` is attached to `P`. -/
lemma New.GaloisRep.exists_attached_of_open_subgroups {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ]
    {E n : Type} [Field E] [EmbeddedNumberField E] [CMType E] [Fintype n] [DecidableEq n]
    {P : FinPlace E → Polynomial ℂ} {N₀ : Subgroup Gal(Ω/E)} [N₀.Normal]
    {ρ₀ : N₀ →* GL n (PadicAlgCl ℓ)} (hρ₀ : Attached P ρ₀ N₀.subtype)
    {N : ℕ → Subgroup Gal(Ω/E)} [∀ T : ℕ, (N T).Normal] (N_open : ∀ T : ℕ, (N T).IsOpen)
    {ρ : (T : ℕ) → N T →* GL n (PadicAlgCl ℓ)} (hρ : ∀ T : ℕ, Attached P (ρ T) (N T).subtype)
    {I : Set Gal(Ω/E)}
    (h_gen : ∀ H : Subgroup Gal(Ω/E), I ⊆ H → ∀ g : Gal(Ω/E), ∃ h ∈ H, g * h ∈ N₀)
    (h_kill : ∀ s ∈ I, ∀ (c : Gal(Ω/E)) (T : ℕ),
      ∃ h_mem : c * s * c⁻¹ ∈ N T, ρ T ⟨c * s * c⁻¹, h_mem⟩ = 1)
    (h_frob : ∀ (y : FinPlace E) (A : ClosurePlace) (s : Gal(Ω/E)),
      y.q.Prime → IsPlaceOver A y → IsFrob A y.q s → ∃ T : ℕ, s ∈ N T) :
    ∃ R : GalRep ℓ E n, Attached P R := by
  -- Extend `ρ₀` by `1` on the largest normal subgroup `K` inside the kernels of all the `ρ T`.
  let K : Subgroup Gal(Ω/E) := (⨅ T : ℕ, (ρ T).ker.map (N T).subtype).normalCore
  -- `ρ₀` and `ρ T` are attached to the same `P`, so where both are defined they have the same
  -- traces and are conjugate, by `Q T`; and `ρ T` is trivial on `K`.
  have exists_conj (T : ℕ) : ∃ Q : GL n (PadicAlgCl ℓ), ∀ g : ↥(N₀ ⊓ N T),
      (ρ₀ (inclusion inf_le_left g)).val * Q = Q * ρ T (inclusion inf_le_right g) := by
    have normal_range {M : Subgroup Gal(Ω/E)} (h_le : N₀ ⊓ N T ≤ M) :
        (inclusion h_le).range.Normal := by
      rw [inclusion_range]
      infer_instance
    have h_left : IsTraceNondeg (ρ₀.comp (inclusion (inf_le_left : N₀ ⊓ N T ≤ N₀))) :=
      hρ₀.isTraceNondeg.comp _ (normal_range inf_le_left)
    have h_right : IsTraceNondeg ((ρ T).comp (inclusion (inf_le_right : N₀ ⊓ N T ≤ N T))) :=
      (hρ T).isTraceNondeg.comp _ (normal_range inf_le_right)
    have h_trace (g : ↥(N₀ ⊓ N T)) :
        (ρ₀ (inclusion inf_le_left g)).val.trace = (ρ T (inclusion inf_le_right g)).val.trace :=
      hρ₀.trace_eq (hρ T) _ rfl
    exact h_left.exists_conj_of_trace_eq _ (AlgHom.id (PadicAlgCl ℓ) _) h_right.hasSemiprimeSpan
      h_trace
  choose Q hQ using exists_conj
  have h_conj (T : ℕ) (g : N T) (y : Gal(Ω/E)) (hy : y ∈ K) (hgy : g.val * y ∈ N₀) :
      ρ₀ ⟨g.val * y, hgy⟩ = Q T * ρ T g * (Q T)⁻¹ := by
    obtain ⟨y, hy_ker, rfl⟩ := mem_iInf.1 (normalCore_le _ hy) T
    have h_mul : ρ T g = ρ T (g * y) := by rw [map_mul, MonoidHom.mem_ker.1 hy_ker, mul_one]
    rw [h_mul]
    exact eq_mul_inv_of_mul_eq (Units.ext (hQ T ⟨g.val * y, hgy, (g * y).prop⟩))
  have I_subset : I ⊆ (K : Set Gal(Ω/E)) := by
    refine fun s hs c ↦ mem_iInf.2 fun T ↦ ?_
    obtain ⟨h_mem, h_one⟩ := h_kill s hs c T
    exact ⟨⟨c * s * c⁻¹, h_mem⟩, h_one, rfl⟩
  -- So for every `g` there is `σ g ∈ K` with `g * σ g ∈ N₀`. As `ρ₀` kills `K ⊓ N₀`, the map
  -- `R g = ρ₀ (g * σ g)` is a homomorphism that extends `ρ₀`.
  choose σ σ_mem mul_σ_mem using h_gen K I_subset
  have ρ₀_kills (y : N₀) (hy : y.val ∈ K) : ρ₀ y = 1 := by
    simpa using h_conj 0 1 y hy (by simp)
  have ρ₀_congr {x z : N₀} (h : (z.val : Gal(Ω/E) ⧸ K) = x.val) : ρ₀ x = ρ₀ z :=
    ρ₀.eq_iff.2 (ρ₀_kills (z⁻¹ * x) (QuotientGroup.eq.1 h))
  have ρ₀_mul (g g' : Gal(Ω/E)) : ρ₀ ⟨g * g' * σ (g * g'), mul_σ_mem (g * g')⟩ =
      ρ₀ ⟨g * σ g, mul_σ_mem g⟩ * ρ₀ ⟨g' * σ g', mul_σ_mem g'⟩ := by
    rw [← map_mul]
    exact ρ₀_congr (by simp [σ_mem])
  let R : GalRep ℓ E n := .mk' (fun g ↦ ρ₀ ⟨g * σ g, mul_σ_mem g⟩) ρ₀_mul
  have R_eq (x : N₀) : ρ₀ x = R x := ρ₀_congr (by simp [σ_mem])
  -- `R` agrees with `ρ₀` on the open subgroup `N₀`, and both have the same image.
  have R_cont : Continuous R := by
    have h_cont : Continuous fun x : N₀ ↦ R x := hρ₀.continuous.congr R_eq
    exact continuous_of_continuousAt_one R fun W hW ↦
      hρ₀.isOpenMap.nhds_le 1 (h_cont.tendsto 1 hW)
  have R_nondeg : IsTraceNondeg R := by
    intro x hx h_zero
    have h_range : (Set.range fun g : Gal(Ω/E) ↦ (R g).val) ⊆
        Set.range fun g : N₀ ↦ (ρ₀ g).val := by simp [R, Set.range_subset_iff]
    exact hρ₀.isTraceNondeg x (Submodule.span_mono h_range hx) fun g ↦ by rw [R_eq, h_zero]
  have R_conj (T : ℕ) (g : N T) : R g = Q T * ρ T g * (Q T)⁻¹ :=
    h_conj T g (σ g) (σ_mem g) (mul_σ_mem g)
  refine ⟨R, R_cont, R_nondeg, .id, fun η hη V hV hV_ne ↦ ?_⟩
  -- By Chebotarev `V` holds a Frobenius element at a place of prime norm, so `V` meets some
  -- `N T`. The estimate for `ρ T` on an open part `O` of `V ∩ N T` passes to its conjugate `R`.
  obtain ⟨y, -, hy, A, hA, s, s_mem_V, s_frob, -⟩ := chebotarev hV hV_ne Set.finite_empty
  obtain ⟨T, s_mem_N⟩ : ∃ T : ℕ, s ∈ N T := h_frob y A s hy hA s_frob
  obtain ⟨O, hO, O_open, O_nonempty, h_close⟩ :=
    (hρ T).eventually_norm_coeff_le hη (V ∩ N T) (hV.inter (N_open T)) ⟨s, s_mem_V, s_mem_N⟩
  refine ⟨O, hO.trans Set.inter_subset_left, O_open, O_nonempty, ?_⟩
  filter_upwards [h_close] with v hv B g hv_prime hB g_frob hg
  have g_mem : g ∈ N T := Set.mem_of_mem_inter_right (hO hg)
  have h_charpoly : (R g).val.charpoly = (ρ T ⟨g, g_mem⟩).val.charpoly := by
    simp [R_conj T ⟨g, g_mem⟩]
  simpa [h_charpoly] using hv B g hv_prime hB g_frob hg ⟨g, g_mem⟩ rfl

open scoped Pointwise in

/-- Let `a` be odd, `E` a CM field containing a primitive 5040th root of unity, and `w` any finite
place. Then eigenforms of any weight on the standard definite unitary group of rank `a` satisfy
`New.GaloisRep.SphericalCompat` at `w`: each has an attached representation. If the form is
spherical at `w`, every representation attached to its Hecke polynomials satisfies the local
conditions `IsCompatibleAt` at the places of `Ω` over `w`: it is good there, has the jumps of the
weight, and at a split `w` the Hecke polynomial kills geometric Frobenius elements. -/
lemma New.GaloisRep.sphericalCompat_of_odd {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {E : Type} [Field E]
    [EmbeddedNumberField E] [CMType E] [HasPrimitiveRoot5040 E] {a : ℕ} (ha : Odd a)
    (w : FinPlace E) :
    SphericalCompat (ℓ := ℓ) E (Fin a) a w := by
  -- For each `T` take a quadratic step in which the places dividing `n T` split, a base change
  -- `F T` of `f`, and a representation `ρ T` of an open subgroup attached to `P`. Extend `ρ 0` to
  -- `Gal(Ω/E)` with the help of the `ρ T` for large `T` (`exists_attached_of_open_subgroups`); the
  -- local clauses at `w` descend from step `0`.
  intro P κ f hf he
  -- `f` is fixed by the integral points that are trivial at a finite set `S` of places.
  obtain ⟨S, -, hS⟩ := exists_inf_trivialOn_le hf.1
  -- The modulus `n T` is divisible by `ℓ`, by `w`, by the places of `S` and by all places of norm
  -- at most `T`.
  let n (T : ℕ) : ℕ := ℓ * (T + w.q + S.sup FinPlace.q).factorial
  have n_mem (T : ℕ) (v : FinPlace E) (hv : v.q ≤ T + w.q + S.sup FinPlace.q) :
      ↑(n T) ∈ v.asIdeal :=
    mem_of_dvd _ ((Nat.dvd_factorial v.one_lt_q.le hv).mul_left ℓ).natCast (absNorm_mem _)
  have n_mem_w (T : ℕ) : ↑(n T) ∈ w.asIdeal := n_mem T w (by omega)
  have not_mem_S (x : FinPlace E) (hx : ↑(n 0) ∉ x.asIdeal) : x ∉ S :=
    fun hxS ↦ hx (n_mem 0 x (le_add_left (S.le_sup hxS)))
  -- Step `T` is the field `stepField (χ T) ⊇ ℚ(√-D T)`. Its group, cut down to `ker (χ T)`, and
  -- the inertia groups at small places prime to `n T` generate `Gal(Ω/E)` (`h_gen`). At places
  -- dividing `n T`: the places of `ℚ(√-D T)` below are split (`h_spl`), decomposition groups fix
  -- the field, and `χ T` kills inertia, and decomposition if the place is split (`h_loc`).
  have exists_step (T : ℕ) : ∃ (χ : QZChar Gal(Ω/E)) (D : ℕ) (_ : HasQuadSubfield D (stepField χ)),
      IsStep (stepField χ) (ideleChar χ) ∧
      (∃ m : ℕ, ∀ H : Subgroup Gal(Ω/E),
        inertiaAbove {x : FinPlace E | ↑(n T) ∉ x.asIdeal ∧ x.q ≤ m} ⊆ H →
        ∀ g : Gal(Ω/E), ∃ h ∈ H, g * h ∈ stepKer χ) ∧
      (∀ v : FinPlace (stepField χ),
        ↑(n T) ∈ v.asIdeal → IsSplitPrimeToDisc (v.below (QuadField D))) ∧
      ∀ {A : ClosurePlace} {x : FinPlace E}, IsPlaceOver A x → ↑(n T) ∈ x.asIdeal →
        decompGroup Gal(Ω/E) A ≤ QZChar.ker (symmetrise χ) ∧ inertiaGroup Gal(Ω/E) A ≤ stepKer χ ∧
        (x.IsSplit → decompGroup Gal(Ω/E) A ≤ stepKer χ) :=
    exists_isStep_hasQuadSubfield E (n T) NeZero.out
  choose χ D D_subfield h_step h_gen h_spl h_loc using exists_step
  -- `F T` is an eigenform over step `T`, with polynomials `P' T`: a weak base change of `f`.
  have exists_form (T : ℕ) : ∃ (F : (stdSpace (stepField (χ T)) (Fin a)).forms κ.baseChange)
      (P' : FinPlace (stepField (χ T)) → Polynomial ℂ),
      IsEigenform F.val P' ∧ IsWeakBaseChange (ideleChar (χ T)) ∅ f F.val :=
    exists_weak_baseChange (h_step T) hf he.1
  choose F P' hF h_bc using exists_form
  -- For `A` over the place `x` of `E`, `u T hA` is a place of step `T` between them.
  have exists_place (T : ℕ) {x : FinPlace E} {A : ClosurePlace} (hA : IsPlaceOver A x) :
      ∃ u : FinPlace (stepField (χ T)), IsPlaceOver A u ∧ u.below E = x := hA.exists_above
  choose u hu h_below using exists_place
  -- The split case applies to step `T` at every place dividing `n T`, as `ℓ ∣ n T`.
  have h_split_case (T : ℕ) {x : FinPlace E} {A : ClosurePlace} (hA : IsPlaceOver A x)
      (hx : ↑(n T) ∈ x.asIdeal) :
      SphericalCompat (ℓ := ℓ) (stepField (χ T)) (Fin a) a (u T hA) := by
    refine sphericalCompat_of_split ha fun v hv ↦ h_spl T v ?_
    obtain hℓ | rfl := hv
    · exact mem_of_dvd _ (by simp [n]) hℓ
    · rw [← h_below T hA] at hx
      simpa using hx
  -- The theorem for step `T` at a place above `w` gives `r T` attached to `P' T`.
  have exists_rep (T : ℕ) : ∃ r : GalRep ℓ (stepField (χ T)) (Fin a), Attached (P' T) r :=
    (h_split_case T w.isPlaceOver_placeOver (n_mem_w T)).exists_attached (F T).prop (hF T)
  choose r hr using exists_rep
  -- The spherical clause for `r T` above a place `x ∣ n T` where `f` is spherical.
  have h_sph (T : ℕ) {x : FinPlace E} {A : ClosurePlace} (hA : IsPlaceOver A x)
      (hx : ↑(n T) ∈ x.asIdeal)
      (hfx : f ∈ sphericalAt (rightRegular ℂ (Gf E (Fin a)) (WeylIndex (Fin a) κ.1 → ℂ)) x) :
      IsCompatibleAt (F T).val a (u T hA) (r T) A := by
    -- Step `T` is unramified at `x`, so `F T` is spherical above `x`.
    obtain ⟨h_dec, h_inertia, -⟩ := h_loc T hA hx
    have h_unram : IsStepUnramifiedAt (stepField (χ T)) (ideleChar (χ T)) x :=
      isStepUnramifiedAt_of_decompGroup_le (h_step T) hA h_dec (h_inertia.trans inf_le_right)
    exact (h_split_case T hA hx).isCompatibleAt (F T).prop (hF T) (hr T)
      (((h_bc T).2 x nofun _ (h_below T hA)).1 h_unram hfx) (hu T hA)
  -- The representation `ρ T` above: the restriction of `r T` to `stepKer (χ T)`, attached to `P`.
  have hρ (T : ℕ) : Attached P ((r T).comp (stepKerInclusion (χ T))) (stepKer (χ T)).subtype :=
    (h_bc T).attached_comp_stepKerInclusion (hr T) (hF T) he
  obtain ⟨m, h_gen₀⟩ := h_gen 0
  refine ⟨?_, fun R' hR' f_sph_w A hA ↦ ?_⟩
  · -- Glue the `ρ (T + m)` to `ρ 0`.
    refine exists_attached_of_open_subgroups (hρ 0) (fun T ↦ isOpen_stepKer (χ (T + m)))
      (fun T ↦ hρ (T + m)) h_gen₀ ?_ fun y A s hy hA h_frob ↦ ⟨y.q, ?_⟩
    · -- A place `x ∤ n 0` of norm at most `m` and its conjugate are off `S`, `x` is prime to `ℓ`
      -- and divides `n (T + m)`, so `r (T + m)` is trivial on inertia at `x`.
      rintro s ⟨x, ⟨hx, hxm⟩, A, hA, hs⟩ c T
      have hA' : IsPlaceOver (c • A) x := hA.smul c
      have hs' := hs.conj c
      have hfx : f ∈ sphericalAt (rightRegular ℂ (Gf E (Fin a)) (WeylIndex (Fin a) κ.1 → ℂ)) x :=
        levelSpace_le_sphericalAt (not_mem_S x hx) (not_mem_S (star x) (by simpa using hx))
          (by simpa [LE.le, funext_iff] using hS)
      have hℓ : ↑ℓ ∉ x.asIdeal := fun hℓ ↦ hx (mem_of_dvd _ (by simp [n]) hℓ)
      have hx_dvd : ↑(n (T + m)) ∈ x.asIdeal := n_mem (T + m) x (by omega)
      obtain ⟨-, h_inertia, -⟩ := h_loc (T + m) hA' hx_dvd
      exact ⟨h_inertia hs',
        (h_sph (T + m) hA' hx_dvd hfx).isGoodAt.1 (hA'.valuation_natCast_eq_one_iff.2 hℓ) _ hs'⟩
    · -- A place `y` of prime norm is split and divides `n (y.q + m)`.
      obtain ⟨-, -, h_dec⟩ := h_loc (y.q + m) hA (n_mem (y.q + m) y (by omega))
      exact h_dec (isSplit_of_q_prime hy) h_frob.1
  -- The clause at `w` descends from step `0`, where the decomposition group fixes the field.
  obtain ⟨-, h_inertia, h_dec⟩ := h_loc 0 hA (n_mem_w 0)
  exact (h_bc 0).isCompatibleAt_of_attached (hr 0) (hF 0) he hR' (by simp [Set.conjClosure]) hA
    h_inertia h_dec (h_below 0 hA) (h_sph 0 hA (n_mem_w 0) f_sph_w)

end QuadraticDescent
