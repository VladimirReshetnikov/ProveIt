import Lib.Adelic.Unitary.ComponentsAndBlockSums

/-!
# Principal levels and levels defined by reductions in the finite adelic unitary group

Let G_f = `New.Gf` be the finite adelic unitary group of the CM field E. Let Ô = `New.Ô` be the
integral finite adeles of E. Let K₀ = `New.stdLevel` be the elements of G_f lying in GL_n(Ô). This
file studies open subgroups (levels) of K₀ of two kinds. The first is the principal level of a
nonzero integer a of E. It consists of the g in K₀ with all entries of g - 1 in aÔ. The second is
the level `New.levelOf w H` of the elements whose reductions at a family of places w_i lie in a
subgroup H. If the places are finitely many, distinct, and none is conjugate to any w_j, then
reduction is onto the product. For a character χ of H, the vectors on which this level acts through
reduction and χ carry an action of the groups that normalise H and fix χ.

## Main definitions and results

* `New.exists_congruenceGL_subset`: every neighbourhood of `1` in `GL n` of the finite adeles
  contains a principal congruence subgroup of integer level. Here `New.Ô` is the ring of integral
  finite adeles, and `New.congruenceGL I id` is the group of matrices in `GL n` of it that are `1`
  modulo `I`.
* `New.principalLevel`, `New.isOpen_principalLevel`: the principal level of an integer a, open for
  a ≠ 0.
* `New.levelOf`: the k in K₀ whose reductions at a family of places w_i lie in a subgroup H of ∏
  GL_n(k_{w_i}); it is open for a finite family (`New.isOpen_levelOf`).
* `New.exists_reduceFamily_eq`, `New.relIndex_levelOf`: if the w_i are finitely many, distinct, and
  none is conjugate to a w_j, reduction is onto the product and the level has index [∏ GL_n : H].
* `New.relIndex_principalLevel_le`: the index of the principal level of `a ≠ 0` is at most
  `N(a) ^ (n ^ 2)`, where `N(a)` is the norm of `a`.
* `New.levelRep`: a group that normalises `H` and fixes `χ` acts on the vectors on which the level
  `New.levelOf w H` acts through reduction and `χ`.

Notions from other files:
* `New.Gf.atPlace`, `New.stdLevel.reduceAt`: The component at w of an element of G_f, and the
  reduction modulo w of an element of K₀. Elements of `trivialOn n P` have component 1 at each place
  in P.
* `New.ResField`: The residue field of the completion E_w of E at the finite place w.
* `New.levelSpace`: The vectors v with π(k)v = χ(k)v for all k in the level.

## Relation to the literature

Known result: Congruence subgroups and level structures of adelic groups. Here levels are preimages
of subgroups of the reductions at a family of places, or principal levels of a global modulus, in
the unitary group of the identity form. Source: V. Platonov, A. Rapinchuk, Algebraic groups and
number theory, ch. 3 and 5; B. H. Gross, Algebraic modular forms, Israel J. Math. 113 (1999) 61-93.
-/

noncomputable section

/-! ## Principal congruence subgroups in adelic GL_n -/

/-- Every neighbourhood of `1` in `GL n` of the finite adeles of `E` contains a principal congruence
subgroup. This is the group `New.congruenceGL` of level `M` times the integral finite adeles
`New.Ô E`, for some nonzero natural number `M`. -/
lemma New.exists_congruenceGL_subset {E : Type*} [Field E] [NumberField E] {n : Type*} [Fintype n]
    [DecidableEq n] {s : Set (GL n (𝔸f E))} (hs : s ∈ nhds 1) :
    ∃ M : ℕ, M ≠ 0 ∧
      ∀ g : GL n (𝔸f E), g ∈ congruenceGL (Ô E ∙ (M : 𝔸f E)) (id : n → n) → g ∈ s := by
  -- Along the filter `l` on `ℕ` for which the levels `M • Ô` shrink to `0`, the congruence
  -- subgroups eventually lie in `s` (`eventually_congruenceGL_subset`); and `M ≠ 0` frequently,
  -- because every neighbourhood of `0` contains some `M • Ô` with `M ≠ 0`.
  let l : Filter ℕ :=
    Filter.comap (fun M : ℕ ↦ (↑(Ô E ∙ (M : 𝔸f E)) : Set (𝔸f E))) (nhds 0).smallSets
  have h_freq : ∃ᶠ M in l, M ≠ 0 := by
    refine ((nhds 0).hasBasis_smallSets.comap _).frequently_iff.2 fun U hU ↦ ?_
    obtain ⟨M, hM, hMU⟩ := mem_nhds_zero_finAdele_iff.1 hU
    refine ⟨M, fun x hx ↦ ?_, hM⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    simpa [Subring.smul_def, mul_comm] using hMU a a.2
  exact (h_freq.and_eventually (eventually_congruenceGL_subset Filter.map_comap_le hs)).exists

namespace New

/-!
## Reduction at places, principal levels and levels defined by reductions

`star w` is the complex conjugate place; `New.ofSplitPlace` puts a matrix of GL_n(E_w) into G_f at a
place w ≠ `star w`, with component 1 away from w and `star w`.
-/

section Levels

open Function Matrix NumberField IsLocalRing Subgroup stdLevel Gf Ideal Valued algebraMap

variable {n ι R S E : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S] [Field E]
  [NumberField E] {w : FinPlace E} {a b : 𝓞 E}

/-! ### Reduction of GL_n and divisibility in the integral finite adeles -/

/-- Entrywise application of a surjective local ring homomorphism gives a surjective map on
GL_n. -/
lemma GL_map_surjective (f : R →+* S) [IsLocalHom f] (hf : Surjective f) :
    Surjective (GeneralLinearGroup.map (n := n) f) := by
  -- The entrywise map on matrices is surjective, and local because `f` commutes with `det`.
  refine surjective_units_map_of_local_ringHom _ hf.comp_left.comp_left ⟨fun M hM ↦ ?_⟩
  rw [isUnit_iff_isUnit_det, ← f.map_det] at hM
  exact (isUnit_iff_isUnit_det M).2 ((isUnit_map_iff f M.det).1 hM)

/-- The reduction homomorphism from GL_n(O_w) to GL_n of the residue field at w. -/
def reduceGL : intGL n (Valued.v (R := LocField w)).integer →* GL n (ResField w) :=
  intGL.map (n := n) (O := v.integer) (S := ResField w) (residue (LocInt w))

/-- Reduction GL_n(O_w) → GL_n(k_w) to the residue field k_w at the place w is surjective. -/
lemma reduceGL_surjective : Surjective (reduceGL (n := n) (w := w)) := fun s ↦ by
  obtain ⟨g, rfl⟩ := GL_map_surjective (residue (LocInt w)) residue_surjective s
  -- The matrix `g`, read in GL_n(E_w), is integral, and its reduction is by definition that of `g`.
  exact ⟨⟨GeneralLinearGroup.map (LocInt w).subtype g, g, rfl⟩, rfl⟩

lemma isUnit_algebraMap_finAdele (ha_ne : a ≠ 0) : IsUnit (a : 𝔸f E) :=
  (RingOfIntegers.coe_ne_zero_iff.2 ha_ne).isUnit.map (algebraMap E (𝔸f E))

/-- For an integer a of E, a finite adele y lies in aÔ if and only if y lies in the ring Ô of
integral finite adeles and |y|_u ≤ |a|_u at every finite place u dividing a. -/
lemma mem_span_iff_valuation_le {y : 𝔸f E} :
    y ∈ Ô E ∙ (a : 𝔸f E) ↔ y ∈ Ô E ∧ ∀ u : IsDedekindDomain.HeightOneSpectrum (𝓞 E),
      a ∈ u.asIdeal → v (y u) ≤ u.intValuation a := by
  have h_a (u : FinPlace E) : v ((a : 𝔸f E) u) = u.intValuation a := v_algebraMap_eq_intValuation a
  -- Where `u` does not divide `a`, its valuation of `a` is `1` and the bound is integrality.
  have h_local (u : FinPlace E) : v (y u) ≤ u.intValuation a ↔
      v (y u) ≤ 1 ∧ (a ∈ u.asIdeal → v (y u) ≤ u.intValuation a) := by
    grind [u.intValuation_le_one a, u.intValuation_eq_one_iff]
  -- Membership in `aÔ` means `v (y u) ≤ v (a u)` at every place `u`. The arrow applies that
  -- rewriting before `simp` unfolds `Ô`.
  simpa [↓exists_eq_mul_iff_v_le, mem_Ô, ← forall_and, h_a] using forall_congr' h_local

variable [IsCMField E] (n a) {f : Ô E →+* S}

/-- The entries of the image of g ∈ K₀ = `stdLevel E n` under `stdLevel.map n f` are the images
under f of the entries of g. -/
@[simp]
lemma stdLevel.map_apply (g : stdLevel E n) (i j : n) :
    map n f g i j = f ⟨g.val.val.val i j, mem_stdLevel.mp g.2 i j⟩ := rfl

/-- An element g of K₀ = `stdLevel E n` maps to 1 under the entrywise homomorphism
`stdLevel.map n f` if and only if f kills every entry of g - 1, read in Ô. -/
lemma stdLevel.map_eq_one {g : stdLevel E n} :
    map n f g = 1 ↔ ∀ i j : n,
      f (⟨(g.val.val : Matrix n n (𝔸f E)) i j, mem_stdLevel.mp g.2 i j⟩ -
        ⟨(1 : Matrix n n (𝔸f E)) i j, mem_stdLevel.mp (one_mem (stdLevel E n)) i j⟩) = 0 :=
  intGL.map_eq_one

/-! ### Principal levels -/

/-- The principal level K(a) for an integer a of E is the subgroup of g in K₀ = `New.stdLevel` such
that every entry of g - 1 is a·y for some y in Ô. It is the principal congruence subgroup
`New.congruenceGL` of level aÔ intersected with G_f, here the unitary group `U 1` of the identity
form, a subgroup of GL_n of the finite adeles; `Subgroup.copy` only restates the carrier so that
membership unfolds to the displayed condition. -/
def principalLevel : Subgroup (Gf E n) :=
  Subgroup.copy ((congruenceGL (Ô E ∙ algebraMap (𝓞 E) (𝔸f E) a) id).subgroupOf (U 1))
    {g ∈ stdLevel E n | ∀ i j : n, ∃ y ∈ Ô E,
      ((g.val : Matrix n n (𝔸f E)) - 1) i j = algebraMap (𝓞 E) (𝔸f E) a * y}
    (by aesop (add simp congruenceGL))

variable {n a}

/-- An element g of G_f is in the principal level of a if and only if it lies in K₀ = `stdLevel E n`
and every entry of g - 1 is a times an element of Ô. -/
lemma mem_principalLevel {g : Gf E n} :
    g ∈ principalLevel n a ↔ g ∈ stdLevel E n ∧ ∀ i j : n, ∃ y ∈ Ô E,
      ((g.val : Matrix n n (𝔸f E)) - 1) i j = algebraMap (𝓞 E) (𝔸f E) a * y := Iff.rfl

/-- If f : Ô → S kills the integer a, then an element k of the principal level of a maps to 1 in
GL_n(S) under entrywise application of f. -/
lemma map_eq_one_of_mem_principalLevel {k : Gf E n} (hk : k ∈ principalLevel n a) (ha : f a = 0) :
    stdLevel.map n f ⟨k, hk.1⟩ = 1 := by
  -- Each entry of `k - 1` is a multiple of `a`, which `f` kills.
  refine (map_eq_one n).2 fun i j ↦ (RingHom.ker f).mem_of_dvd ?_ ha
  obtain ⟨y, hy, h_entry⟩ := (mem_principalLevel.1 hk).2 i j
  exact ⟨⟨y, hy⟩, Subtype.ext h_entry⟩

omit [IsCMField E] in
/-- For a nonzero integer a, the congruence subgroup of GL_n of the finite adeles of level aÔ is
open. -/
lemma Variety.isOpen_congruenceGL_span (ha_ne : a ≠ 0) :
    (congruenceGL (Ô E ∙ (a : 𝔸f E)) (id : n → n)).IsOpen := by
  refine isOpen_congruenceGL isOpen_Ô ?_
  -- `a Ô` is the image of the open set `Ô` under multiplication by the unit `a` of `𝔸f E`.
  have h_image : ((Ô E ∙ (a : 𝔸f E) : Submodule (Ô E) (𝔸f E)) : Set (𝔸f E)) =
      (fun x : 𝔸f E ↦ (a : 𝔸f E) • x) '' (Ô E : Set (𝔸f E)) := by aesop
  rw [h_image]
  exact (isUnit_algebraMap_finAdele ha_ne).isOpenMap_smul _ (isOpen_Ô (E := E))

lemma isOpen_principalLevel (ha_ne : a ≠ 0) : (principalLevel n a).IsOpen := by
  rw [principalLevel, copy_eq]
  exact (Variety.isOpen_congruenceGL_span ha_ne).preimage_val

lemma principalLevel_le_stdLevel : principalLevel n a ≤ stdLevel E n := fun _ hg ↦ hg.1

instance [Fact (a ≠ 0)] : IsLevel (principalLevel n a) where
  le := principalLevel_le_stdLevel
  isOpen := isOpen_principalLevel Fact.out

lemma principalLevel_le_of_dvd (hab : a ∣ b) : principalLevel n b ≤ principalLevel n a := by
  obtain ⟨c, rfl⟩ := hab
  refine fun x ⟨hx, h_cong⟩ ↦ ⟨hx, fun i j ↦ ?_⟩
  obtain ⟨y, hy, h_entry⟩ := h_cong i j
  exact ⟨c * y, mul_mem (algebraMap_mem_Ô.2 c.2) hy, by simp [h_entry, mul_assoc]⟩

/-- Every neighbourhood of 1 in G_f contains the principal level `New.principalLevel` of some
nonzero natural number M. -/
lemma exists_principalLevel_subset {s : Set (Gf E n)} (hs : s ∈ nhds 1) :
    ∃ M : ℕ, M ≠ 0 ∧ (principalLevel n (M : 𝓞 E) : Set (Gf E n)) ⊆ s := by
  -- `s` contains the trace on the unitary group of a neighbourhood of `1` in `GL n`.
  obtain ⟨t, ht, h_sub⟩ := (mem_nhds_induced _ _ _).1 hs
  obtain ⟨M, hM, h_cong⟩ := exists_congruenceGL_subset ht
  refine ⟨M, hM, fun g hg ↦ h_sub (h_cong _ ?_)⟩
  rw [principalLevel, copy_eq] at hg
  simpa using mem_subgroupOf.1 hg

instance : NonarchimedeanGroup (Gf E n) where
  is_nonarchimedean _ hs :=
    let ⟨M, hM, h_sub⟩ := exists_principalLevel_subset hs
    ⟨⟨principalLevel n M, isOpen_principalLevel (mod_cast hM)⟩, h_sub⟩

/-! ### Reduction of an element with given component -/

/-- If the component at w of k ∈ K₀ is the integral matrix t, the reduction of k at w is t modulo
w. -/
lemma stdLevel.reduceAt_eq_of_atPlace {k : stdLevel E n} {t : GL n (LocInt w)}
    (h_atPlace : k.val.atPlace w = GeneralLinearGroup.map (LocInt w).subtype t) :
    reduceAt w k = GeneralLinearGroup.map (residue (LocInt w)) t := by
  -- Both sides are `reduceGL` of integral matrices with the same image in GL_n(E_w).
  have h_comp : (⟨k.val.atPlace w, t, h_atPlace.symm⟩ : intGL n (v (R := LocField w)).integer) =
      ⟨GeneralLinearGroup.map (LocInt w).subtype t, t, rfl⟩ := Subtype.ext h_atPlace
  exact congrArg reduceGL h_comp

/-- An element of K₀ with component 1 at w reduces to 1 modulo w. -/
lemma stdLevel.reduceAt_eq_one_of_atPlace {k : stdLevel E n} (h_atPlace : k.val.atPlace w = 1) :
    reduceAt w k = 1 := by
  simpa using reduceAt_eq_of_atPlace (t := 1) (by simpa using h_atPlace)

end Levels

/-! ### Levels cut out by reductions at a family of places -/

section LevelsAtPlaces

open Function NumberField IsLocalRing Subgroup stdLevel Gf Ideal algebraMap

variable {n ι R S E : Type*} [Fintype n] [DecidableEq n] [Field E] [NumberField E] {a : 𝓞 E}
  [IsCMField E]
variable {w : ι → FinPlace E} {H : Subgroup (∀ i : ι, GL n (ResField (w i)))}

/-- The family w of finite places of the CM field E is injective and no w j is the conjugate of
any w i; in particular no w i is its own conjugate. -/
class IsConjApart (w : ι → FinPlace E) : Prop where
  /-- The places of the family are pairwise distinct. -/
  injective : w.Injective
  /-- The conjugate of a place of the family is never a place of the family. -/
  star_ne (i j : ι) : star (w i) ≠ w j

/-- The homomorphism from K₀ to ∏_i GL_n(k_{w_i}) given by reduction modulo each place of the
family w_i. -/
def stdLevel.reduceFamily (w : ι → FinPlace E) : stdLevel E n →* ∀ i : ι, GL n (ResField (w i)) :=
  MonoidHom.pi fun i ↦ reduceAt (w i)

/-- The subgroup of G_f of elements of K₀ whose reductions modulo the places w_i form an element
of the subgroup H of ∏_i GL_n(k_{w_i}). -/
def levelOf (w : ι → FinPlace E) (H : Subgroup (∀ i : ι, GL n (ResField (w i)))) :
    Subgroup (Gf E n) :=
  (H.comap (reduceFamily w)).map (stdLevel E n).subtype

lemma levelOf_le_stdLevel : levelOf w H ≤ stdLevel E n := map_subtype_le _

/-- An element of G_f is in `levelOf w H` if and only if it lies in K₀ = `stdLevel E n` and its
family of reductions at the places w_i lies in H. -/
lemma mem_levelOf {g : Gf E n} :
    g ∈ levelOf w H ↔ ∃ h : g ∈ stdLevel E n, reduceFamily w ⟨g, h⟩ ∈ H := by
  simp [levelOf]

/-- The homomorphism from the level `New.levelOf` w H to H given by reduction modulo the places
w_i. -/
def levelOf.reduction (w : ι → FinPlace E) (H : Subgroup (∀ i : ι, GL n (ResField (w i)))) :
    levelOf w H →* H :=
  ((reduceFamily w).comp (inclusion levelOf_le_stdLevel)).codRestrict H fun g ↦
    (mem_levelOf.1 g.2).2

lemma inf_trivialOn_le_levelOf : stdLevel E n ⊓ trivialOn n (Set.range w) ≤ levelOf w H :=
  -- An element of the left side has component `1` at each `w i`, so it reduces to `1 ∈ H`.
  fun _ ⟨hg, h_trivial⟩ ↦ mem_levelOf.2 ⟨hg, H.ker_le_comap _ <| funext fun i ↦
    reduceAt_eq_one_of_atPlace (by simp_all [trivialOn])⟩

/-- If the integer a lies in every w_i, the principal level of a is contained in
`levelOf w H`. -/
lemma principalLevel_le_levelOf (ha_mem : ∀ i : ι, a ∈ (w i).asIdeal) :
    principalLevel n a ≤ levelOf w H :=
  -- `a` vanishes in each residue field, so an element of the level reduces to `1 ∈ H`.
  fun _ hg ↦ mem_levelOf.2 ⟨hg.1, H.ker_le_comap _ <| funext fun i ↦
    map_eq_one_of_mem_principalLevel hg (algebraMap_ResField_eq_zero.2 (ha_mem i))⟩

/-- For a finite family of places, the level `levelOf w H` is open in G_f. -/
lemma isOpen_levelOf [Finite ι] : (levelOf w H).IsOpen := by
  -- The level contains `principalLevel n a` for `a` the norm of `⨅ i, w i`, a nonzero element of
  -- each `w i`.
  set I : Ideal (𝓞 E) := ⨅ i : ι, (w i).asIdeal
  have h_fin : Finite (𝓞 E ⧸ I) := .of_injective _ (quotientInfToPiQuotient_inj _)
  have h_ne : (I.absNorm : 𝓞 E) ≠ 0 := mod_cast (absNorm_ne_zero_iff I).2 h_fin
  exact isOpen_mono (principalLevel_le_levelOf (mem_iInf.1 (absNorm_mem I)))
    (isOpen_principalLevel h_ne)

/-- For finite `ι`, `levelOf w H` is a level (an instance of `IsLevel`): it is open and contained in
the standard level. -/
instance instIsLevelLevelOf [Finite ι] : IsLevel (levelOf w H) where
  le := levelOf_le_stdLevel
  isOpen := isOpen_levelOf

/-- A level K, that is an open subgroup of G_f inside K₀, has finite index in the compact group
K₀. -/
@[simp]
lemma relIndex_ne_zero_of_isLevel (K : Subgroup (Gf E n)) [IsLevel K] :
    K.relIndex (stdLevel E n) ≠ 0 :=
  isCompact_stdLevel.relIndex_ne_zero IsLevel.isOpen

/-- For distinct places `w i`, none conjugate to a `w j` (`IsConjApart w`, whose field `star_ne`
says that `w i` is split), a matrix `k` in `localIntGL n (w i)` = GL_n(O_{w i}) put at the split
place `w i` by `New.ofSplitPlace` reduces to `reduceGL k`, the reduction of `k` modulo `w i`, at
`w i` and to `1` at the other places of the family. -/
lemma reduceFamily_ofSplitPlace [Finite ι] [IsConjApart w] [DecidableEq ι] (i : ι)
    (k : localIntGL n (w i)) :
    reduceFamily w ⟨ofSplitPlace (IsConjApart.star_ne (w := w) i i) k, by simp⟩ =
      Pi.mulSingle i (reduceGL k) := by
  refine eq_update_iff.2 ⟨reduceAt_eq_of_atPlace (atPlace_ofSplitPlace ..), fun j hj ↦ ?_⟩
  -- For `j ≠ i` the place `w j` is neither `w i` nor its conjugate.
  exact reduceAt_eq_one_of_atPlace
    (atPlace_ofSplitPlace_of_ne _ _ (IsConjApart.injective.ne hj) (IsConjApart.star_ne j i))

/-- For finitely many distinct places w_i, none conjugate to a w_j, every family s of matrices in
GL_n(k_{w_i}) is the reduction of some k in K₀ with component 1 away from the w_i and their
conjugates. -/
lemma exists_reduceFamily_eq [Finite ι] [IsConjApart w] (s : ∀ i : ι, GL n (ResField (w i))) :
    ∃ k : stdLevel E n, k.val ∈ supportedOn n (Set.range w) ∧ reduceFamily w k = s := by
  classical
  -- It suffices to lift an element with a single nontrivial component `s i`.
  refine (((supportedOn n (.range w)).subgroupOf (stdLevel E n)).map
    (reduceFamily w)).pi_mem_of_mulSingle_mem s fun i ↦ ?_
  -- Lift `s i` to `GL_n(O_w)` and place the lift at the split place `w i`; it is then supported
  -- on `{w i, star (w i)}`, that is, has component `1` at all other places.
  obtain ⟨k, hk⟩ : ∃ k : localIntGL n (w i), reduceGL k = s i := reduceGL_surjective (s i)
  let g : stdLevel E n := ⟨ofSplitPlace (IsConjApart.star_ne (w := w) i i) k, by simp⟩
  have hg_supp : g.val ∈ supportedOn n (Set.range w) :=
    mem_supportedOn.2 fun u hu hu_star ↦
      atPlace_ofSplitPlace_of_ne _ _ (fun h_eq ↦ hu ⟨i, h_eq.symm⟩)
        (fun h_eq ↦ hu_star ⟨i, h_eq.symm⟩)
  have hg : reduceFamily w g = Pi.mulSingle i (s i) := by rw [reduceFamily_ofSplitPlace i k, hk]
  exact ⟨g, hg_supp, hg⟩

/-- For finitely many distinct places w_i, none conjugate to a w_j, the index of the level
`New.levelOf` w H in K₀ is the index of H in ∏ GL_n(k_{w_i}). -/
lemma relIndex_levelOf [Finite ι] [h : IsConjApart w] :
    (levelOf w H).relIndex (stdLevel E n) = H.index := by
  -- The level is the preimage of `H` under the surjection `reduceFamily w`.
  have h_surj : Surjective (reduceFamily (n := n) w) :=
    fun s ↦ (exists_reduceFamily_eq s).imp fun _ hk ↦ hk.2
  simp [levelOf, relIndex, subgroupOf, comap_map_eq_self, H.index_comap_of_surjective h_surj]

end LevelsAtPlaces

/-!
## Index bounds for principal levels and auxiliary facts on Ô and integers

* `New.relIndex_principalLevel_le`: the principal level of `a ≠ 0` has index at most
  `N(a) ^ (n ^ 2)` in K₀.
* `New.bijective_quot_Ô`, `New.card_Ô_quot_span`: `𝓞 / J ≃ Ô / I` when the ideal `I` of `Ô`
  contracts to `J` and `J` contains a nonzero integer. For `a ≠ 0`, `Ô / a Ô` has `N(a)` elements.
* Further lemmas on characters of nonarchimedean groups, on divisibility by an integer in `Ô` and
  on products of distinct places.
-/

section CongruenceLevel

open Nat Circle NumberField Ideal Quotient RingOfIntegers Subgroup stdLevel algebraMap

variable {E : Type*} [Field E] [NumberField E] {n : Type*} [Fintype n] [DecidableEq n]
  {a b : 𝓞 E} {ι : Type*} [Fintype ι] {w : ι → FinPlace E}

/-- A continuous character χ : G → S¹ of a nonarchimedean topological group G is trivial on a
neighbourhood of 1. -/
lemma char_eventually_eq_one {G : Type*} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    (χ : G →* Circle) (hχ : Continuous χ) : ∀ᶠ k : G in nhds 1, χ k = 1 := by
  -- The preimage of the open arc of radius `π / 2` around `1` contains an open subgroup `K`, and
  -- only `1` has all its positive powers in that arc.
  obtain ⟨K, hK⟩ := NonarchimedeanGroup.is_nonarchimedean _
    (((isOpen_centeredArc (.pi / 2)).preimage hχ).mem_nhds ⟨0, by simp [Real.pi_pos]⟩)
  filter_upwards [K.mem_nhds_one] with k hk
  exact eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun m _ ↦ by simpa using hK (pow_mem hk m)

/-- For a finite commutative ring R, the group GL_n(R) has at most |R|^(n²) elements. -/
lemma card_GL_le (R : Type*) [CommRing R] [Finite R] :
    Nat.card (GL n R) ≤ Nat.card R ^ Fintype.card n ^ 2 :=
  (card_le_card_of_injective (β := Matrix n n R) _ Units.val_injective).trans_eq
    (by simp [Matrix, card_pi, sq, pow_mul])

/-- Let `a` vanish to order one at each place that contains it. Then `a` divides `y ∈ Ô` if and only
if the reduction `reduceAt w y` of `y` modulo w is `0` for every place w that contains `a`. -/
lemma dvd_iff_reduceAt_eq_zero
    (h_val : ∀ {v : FinPlace E}, a ∈ v.asIdeal → v.intValuation a = WithZero.exp (-1)) (y : Ô E) :
    (a : Ô E) ∣ y ↔ ∀ w : FinPlace E, a ∈ w.asIdeal → reduceAt w y = 0 := by
  -- Both sides are conditions place by place: `a ∣ y` says `v(y_u) ≤ v_u(a)` for all `u`, the right
  -- side says `v(y_u) < 1` for the places `u` containing `a`.
  have h_local (u : FinPlace E) :
      Valued.v (y.1 u) ≤ u.valuation E (a : E) ↔ (a ∈ u.1 → Valued.v (y.1 u) < 1) := by
    by_cases ha : a ∈ u.1
    · -- here `v_u(a) = exp (-1)`, and `x ≤ exp (-1)` means `x < 1`
      simp [ha, u.valuation_of_algebraMap, h_val ha, ← WithZero.lt_mul_exp_iff_le,
        ← WithZero.exp_add]
    · -- here `v_u(a) = 1`, and `y` is integral
      simp [ha, u.valuation_of_algebraMap, u.intValuation_eq_one_iff.2 ha, mem_Ô.1 y.2]
  simp [exists_eq_mul_iff_v_le, reduceAt_eq_zero, h_local, dvd_def, Subtype.ext_iff]

/-- For distinct places w_i, an integer x of E lies in their product if and only if it lies in
each w_i. -/
lemma mem_prod_finPlace_iff (hw : w.Injective) {x : 𝓞 E} :
    x ∈ ∏ i : ι, (w i).asIdeal ↔ ∀ i : ι, x ∈ (w i).asIdeal := by
  -- Distinct places are coprime, so their product is their intersection.
  rw [prod_eq_iInf_of_pairwise_isCoprime fun i _ j _ hij ↦ (w i).isCoprime_of_ne _ (hw.ne hij)]
  simp

/-- For integers a ≠ 0 and b of E, a divides b in Ô if and only if it does so in 𝓞_E. -/
lemma dvd_iff_Ô (ha_ne : a ≠ 0) : (a : Ô E) ∣ b ↔ a ∣ b := by
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, map_dvd _⟩
  -- The quotient `b / a ∈ E` equals `y ∈ Ô` in the adeles, so it is an integer.
  have h_int : algebraMap E (𝔸f E) ((a : E)⁻¹ * b) ∈ Ô E := by
    simp_all [← mul_assoc, ← map_mul _ _⁻¹, Subtype.ext_iff]
  exact ⟨⟨(a : E)⁻¹ * b, algebraMap_mem_Ô.1 h_int⟩,
    RingOfIntegers.ext (mul_inv_cancel_left₀ (coe_ne_zero_iff.2 ha_ne) _).symm⟩

/-- If an ideal I of Ô contracts to the ideal J of 𝓞_E and J contains a nonzero element a, then
𝓞_E/J → Ô/I is bijective. -/
lemma bijective_quot_Ô (ha_ne : a ≠ 0) {I : Ideal (Ô E)} {J : Ideal (𝓞 E)}
    (hJ : Ideal.comap (algebraMap (𝓞 E) (Ô E)) I = J) (ha : a ∈ J) :
    Function.Bijective (quotientMap I (algebraMap (𝓞 E) (Ô E)) hJ.ge) := by
  refine ⟨quotientMap_injective' hJ.le, Quot.ind fun x ↦ ?_⟩
  -- Every `x ∈ Ô` is congruent to an integer `b` modulo `a`, hence modulo `I`.
  obtain ⟨b, hb⟩ := exists_dvd_algebraMap_sub ha_ne x
  exact ⟨b, SModEq.sub_mem.2 (mem_of_dvd _ hb (hJ.ge ha))⟩

/-- An ideal I of Ô that contains a nonzero element a of 𝓞_E is generated by its contraction to
𝓞_E. -/
lemma map_under_Ô (ha_ne : a ≠ 0) {I : Ideal (Ô E)} (hI : algebraMap (𝓞 E) (Ô E) a ∈ I) :
    (under (𝓞 E) I).map (algebraMap (𝓞 E) (Ô E)) = I := by
  refine map_comap_le.antisymm fun x hx ↦ ?_
  -- Write `x = b - (b - x)` with `b` an integer and `a ∣ b - x`; then `b ∈ I`, as `x, a ∈ I`.
  obtain ⟨b, h_dvd⟩ := exists_dvd_algebraMap_sub ha_ne x
  have hb : b ∈ under (𝓞 E) I := by simpa using add_mem (mem_of_dvd _ h_dvd hI) hx
  simpa using Ideal.sub_mem _ (mem_map_of_mem _ hb) (mem_of_dvd _ h_dvd (mem_map_of_mem _ hI))

/-- For a nonzero integer a of E, the quotient Ô/aÔ has N(a) elements, where N(a) is the absolute
norm of (a). -/
lemma card_Ô_quot_span (ha_ne : a ≠ 0) :
    Nat.card (Ô E ⧸ span {(a : Ô E)}) = absNorm (span {a}) := by
  have h_comap : (span {algebraMap _ (Ô E) a}).comap (algebraMap (𝓞 E) (Ô E)) = span {a} :=
    Ideal.ext (by simp [dvd_iff_Ô ha_ne, mem_span_singleton])
  exact (card_eq_of_bijective _ (bijective_quot_Ô ha_ne h_comap (by simp))).symm

/-- For a CM field `E` and an integer `a` of `E`, the principal level K(a) (the g in K₀ with g -
1 ≡ 0 mod aÔ) is the kernel of reduction K₀ → GL_n(Ô/aÔ). Here K₀ = `stdLevel E n` is G_f ∩ GL_n(Ô),
the stabiliser of Ô^n in the finite adelic unitary group G_f. -/
lemma principalLevel_subgroupOf_stdLevel_eq_ker [IsCMField E] :
    (principalLevel n a).subgroupOf (stdLevel E n) =
      (stdLevel.map n (Ideal.Quotient.mk (span {algebraMap (𝓞 E) (Ô E) a}))).ker := by
  ext g
  -- Both sides say that `a` divides every entry of `g - 1`; `map_sub` would split such an entry.
  simp [mem_subgroupOf, eq_zero_iff_dvd, -map_sub, principalLevel, Subgroup.copy, map_eq_one,
    Matrix.one_apply, dvd_def, Subtype.ext_iff, IsScalarTower.algebraMap_apply (𝓞 E) E (𝔸f E)]

/-- For a nonzero integer a of E, the index of the principal level K(a) in K₀ = `New.stdLevel` is at
most N(a)^(n²). Here N(a) is the absolute norm of (a) and n in the exponent is the size of the index
type. -/
lemma relIndex_principalLevel_le (ha_ne : a ≠ 0) [IsCMField E] :
    (principalLevel n a).relIndex (stdLevel E n) ≤ absNorm (span {a}) ^ Fintype.card n ^ 2 := by
  -- `principalLevel n a` is the kernel of reduction `stdLevel → GL n (Ô / aÔ)`, so the index is the
  -- size of the image; `Ô / aÔ` has `N(a)` elements, so the target has at most `N(a)^(n²)`.
  have : Finite (Ô E ⧸ span {algebraMap (𝓞 E) (Ô E) a}) :=
    finite_of_card_ne_zero (by simpa [card_Ô_quot_span ha_ne])
  rw [relIndex, principalLevel_subgroupOf_stdLevel_eq_ker, index_ker, ← card_Ô_quot_span ha_ne]
  exact (card_le_card_group _).trans (card_GL_le _)

end CongruenceLevel

/-!
## Action on vectors of a level through lifts

* `New.liftResidue`: a chosen lift of an element of the product, supported at the `w i` and their
  conjugates.
* `New.apply_liftResidue_eq`: on vectors of level `levelOf w H` and character `χ` composed with
  reduction, all lifts act alike.
-/

section FiniteGroupAction

variable {n ι A W E : Type*} [Fintype n] [DecidableEq n] [Field E] [NumberField E]
  [NumberField.IsCMField E] {w : ι → FinPlace E} [CommRing A] [AddCommGroup W] [Module A W]
  {π : Representation A (Gf E n) W} {H : Subgroup (∀ i : ι, GL n (ResField (w i)))} {χ : H →* A}

/-- An element `k` of `New.stdLevel E n` with reduction `x ∈ H` acts on vectors of level
`New.levelOf w H` and character `χ` by the scalar `χ x`. -/
lemma levelSpace_levelOf_apply {v : W}
    (hv : v ∈ levelSpace π (levelOf w H) (χ.comp (levelOf.reduction w H))) (k : stdLevel E n)
    (x : H) (hk : stdLevel.reduceFamily w k = x.val) :
    π k v = χ x • v := by
  obtain ⟨x, hx⟩ := x
  subst hk
  exact mem_levelSpace.1 hv ⟨k, mem_levelOf.2 ⟨k.2, hx⟩⟩

variable [Finite ι] [IsConjApart w] (s : ∀ i : ι, GL n (ResField (w i)))

/-- For finitely many distinct places w_i, none conjugate to another or itself, a chosen element
of K₀ supported at the w_i and their conjugates whose reductions modulo the w_i are s. -/
@[local grind]
noncomputable def liftResidue : stdLevel E n := (exists_reduceFamily_eq s).choose

lemma liftResidue_mem_supportedOn : (liftResidue s).val ∈ Gf.supportedOn n (Set.range w) :=
  (exists_reduceFamily_eq s).choose_spec.1

@[local simp]
lemma reduceFamily_liftResidue : stdLevel.reduceFamily w (liftResidue s) = s :=
  (exists_reduceFamily_eq s).choose_spec.2

/-- On a vector `v` of level `New.levelOf w H` and character `χ`, the chosen lift of `s` acts as any
`k` in `New.stdLevel E n` with reduction `s` does. -/
lemma apply_liftResidue_eq (v : levelSpace π (levelOf w H) (χ.comp (levelOf.reduction w H)))
    (k : stdLevel E n) {s : ∀ i : ι, GL n (ResField (w i))} (hk : stdLevel.reduceFamily w k = s) :
    π (liftResidue s).val v = π k v := by
  -- `k⁻¹ * liftResidue s` reduces to `1`, so it fixes `v`; now apply `π k`.
  have h_fix : π (k⁻¹ * liftResidue s : stdLevel E n) v = v.1 := by
    simpa using levelSpace_levelOf_apply v.2 (k⁻¹ * liftResidue s) 1 (by simp [hk])
  simpa using congr_arg (π k.val) h_fix

/-- If s normalises H and fixes χ, then π of the chosen lift of s maps vectors of level
`New.levelOf` w H and character χ to vectors of the same kind. -/
lemma map_liftResidue_mem_levelSpace {s : ∀ i : ι, GL n (ResField (w i))}
    (h_norm : ∀ x : H, ∃ hx : s⁻¹ * x * s ∈ H, χ ⟨s⁻¹ * x * s, hx⟩ = χ x) {v : W}
    (hv : v ∈ levelSpace π (levelOf w H) (χ.comp (levelOf.reduction w H))) :
    π (liftResidue s).val v ∈ levelSpace π (levelOf w H) (χ.comp (levelOf.reduction w H)) := by
  refine mem_levelSpace.2 fun g ↦ ?_
  -- With `l` the lift of `s`, the conjugate `l⁻¹ * g * l` acts on `v` by the same scalar as `g`;
  -- apply `π l` to this equation.
  let l : stdLevel E n := liftResidue s
  let x : H := levelOf.reduction w H g
  obtain ⟨hx, hχ⟩ := h_norm x
  let c : stdLevel E n := l⁻¹ * ⟨g, levelOf_le_stdLevel g.2⟩ * l
  -- The reduction of `g` is `x` by definition.
  have h_red : stdLevel.reduceFamily w c = s⁻¹ * x.val * s := by
    simp [c, l]
    rfl
  have h_conj : π c v = χ ⟨s⁻¹ * x * s, hx⟩ • v := levelSpace_levelOf_apply hv c _ h_red
  calc π g.val (π l.val v)
    _ = π l.val (π c v) := by simp [c]
    _ = χ x • π l.val v := by rw [h_conj, hχ, map_smul]

variable (π χ) in
/-- For finitely many distinct places w_i, none conjugate to a w_j, and φ : S → ∏ GL_n(k_{w_i})
normalising H and fixing χ, the representation s ↦ π(`New.liftResidue` φ(s)) of S on vectors of
level `New.levelOf` w H and character χ. -/
noncomputable def levelRep {S : Type*} [Group S] (φ : S →* (i : ι) → GL n (ResField (w i)))
    (h : ∀ (s : S) (x : H), ∃ hx : (φ s)⁻¹ * x * φ s ∈ H, χ ⟨(φ s)⁻¹ * x * φ s, hx⟩ = χ x) :
    Representation A S (levelSpace π (levelOf w H) (χ.comp (levelOf.reduction w H))) where
  toFun s :=
    (π (liftResidue (φ s))).restrict fun _ hv ↦ map_liftResidue_mem_levelSpace (h s) hv
  map_one' := by
    ext
    simp [apply_liftResidue_eq _ 1]
  map_mul' s t := by
    -- The lift of `φ (s * t)` and the product of the lifts have the same reduction.
    ext v
    change π (liftResidue (φ (s * t))).val v.1 =
      π (liftResidue (φ s)).val (π (liftResidue (φ t)).val v.1)
    simp [apply_liftResidue_eq v (liftResidue (φ s) * liftResidue (φ t))]

end FiniteGroupAction

end New

end
