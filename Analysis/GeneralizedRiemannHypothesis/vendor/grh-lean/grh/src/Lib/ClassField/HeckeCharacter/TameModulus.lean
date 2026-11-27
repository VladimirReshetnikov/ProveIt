import Lib.ClassField.HeckeCharacter.SplittingCharacters
import Lib.SiegelWeil.SingularForms.CentreCoefficients
import Lib.Weil.DualPair.KernelDecay
import Lib.Weil.DualPair.KernelLaws

/-!
# Characters on determinants, local values and characters tame for a modulus

This file evaluates characters of U(1)(𝔸), the norm-one ideles of the CM field E, on determinants of
elements of K₀ = `New.stdLevel E n`. Here `New.stdLevel E n` is the stabiliser of the standard
lattice in the finite adelic unitary group `New.Gf E n`. A character of weight `e` and residue
characters `ψ` (`New.AutChar.HasWeight`) takes at `det k`, for `k` in K₀, the product of the `ψ w`
at the determinants of the reductions of `k`. Local values are read through `New.atPlaces P`, the
map to the components at the places of a finite set `P`, and through `New.Exchange.localChar P ξ k`,
the character `ξ |·| ^ (k / 2)` of the product of the completions at `P`. For a modulus 𝔪
(`New.Modulus`, an ideal of O_E prime to its conjugate), the reduction K₀ → GL_n(O_E/𝔪) is onto, and
a character tame for 𝔪 is given on determinants of K₀ by a character of O_E/𝔪.

## Main definitions and results

* `New.Exchange.SplitTameChar.character_detFin_eq_of_mem_stdLevel`,
  `New.Exchange.upsilonU1_detFin_eq_one_of_mem_stdLevel`: on determinants of `stdLevel E n`, a tame
  character is its local character at the ramified places, and `New.WeilData.upsilonU1` is trivial.
* `New.Rows.exists_reductionGL_eq`, `New.Rows.liftMod`: reduction `New.Modulus.reductionGL` :
  K₀ → GL_n(O_E/𝔪) is onto, with lifts supported at the places dividing 𝔪 and their conjugates.
* `New.Modulus.charOfTamePart`: the character of O_E/𝔪 with given components at the residue fields.
* `New.Exchange.IsTameFor`, `New.Exchange.IsTameFor.apply_det`: ν is tame for 𝔪 with character χ;
  then ν(det k) = χ(det(k mod 𝔪)) for k in K₀.

Notions from other files:
* `New.AutChar`: The group of continuous circle-valued characters of U(1)(𝔸), the norm-one adeles of
  the CM field E, trivial on elements coming from E.
* `New.Gf`: The finite adelic unitary group G_f: matrices g in GL_n(𝔸_f) with gᴴg = 1; K₀ = G_f ∩
  GL_n(Ô) is the stabiliser of the standard lattice.
* `New.G.det`: The determinant, from the adelic unitary group of signs s (pairs of an archimedean
  and a finite part) to the adeles x of E with x x̄ = 1.
* `New.Exchange.SplitTameChar.semilocalChar`: The character t ↦ ν(t/t̄) of ∏_{w∈S} E_w, t read as an
  idele supported on S, extended by 0 to non-invertible elements.

## Relation to the literature

Known; see `Lib.ClassField.Global.CMSplittingCharacters` for sources.
-/

noncomputable section

/-! ## Characters of given weight on determinants of integral unitary points -/

namespace New.AutChar.HasWeight

open Matrix Prod IsIntMatrix

variable {E n : Type _} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {μ : AutChar E} {e : NumberField.InfinitePlace E → ℤ}
  {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ} {s : n → ℤˣ}

/-- Let `μ` have weight `e` and tame part `ψ` (`μ.HasWeight e ψ`, with `ψ u` a character of the
residue field at `u`), and let `ψ` be trivial outside the distinct places `w i`. Then for `k` in the
stabiliser `K₀ = stdLevel E n` of the standard lattice, `μ (det k) = ∏ i, ψ (w i) (det (k mod w
i))`, where `detFin s k` is the determinant of `k` as a norm-one adele. -/
lemma apply_det_eq_prod (h : μ.HasWeight e ψ) {ι : Type*} [Fintype ι] {w : ι → FinPlace E}
    (hw : w.Injective) (hψ : ∀ u : FinPlace E, u ∉ Set.range w → ψ u = 1) (k : stdLevel E n) :
    μ.val (detFin s k.val) = ∏ i : ι, ψ (w i) (stdLevel.reduceAt (w i) k).val.det := by
  -- Reduction modulo a place is a ring homomorphism on `Ô E`, so it commutes with `det`.
  have h_red (u : FinPlace E) (h_int : (G.adeleMatrix (s := s) (1, k.val)).det.snd ∈ Ô E) :
      reduceAt u ⟨_, h_int⟩ = (stdLevel.reduceAt u k).val.det := by
    -- `convert!` matches `RingHom.map_det` across the coercions between `Ô E`, `𝔸f E` and the
    -- finite part of `(1, k)`; the remaining goal is the finite part of the determinant.
    convert! RingHom.map_det ..
    -- `simp` reduces both sides to the entries of `k`; they agree up to the coercion into `Ô E`.
    simp [det_apply', snd_sum, snd_prod]
    rfl
  -- `μ (det k)` is the archimedean part, which is `1`, times the tame product, which is a product
  -- over the places `w i` because `ψ` is trivial elsewhere.
  have hψ_map : ∀ u : FinPlace E, u ∉ Finset.univ.map ⟨w, hw⟩ → ψ u = 1 := by simpa using hψ
  have h_int : (detFin s k.val : 𝔸 E).snd ∈ Ô E := by simp [det_mem (mem_stdLevel.mp k.property)]
  rw [h.apply_eq _ h_int, finprod_tame_eq_prod_reduceU1 (u := detFin s k.val) hψ_map h_int]
  simp [reduceU1, h_red]

/-- A character `μ` with trivial tame part (`μ.HasWeight e 1`) is trivial on the determinant
`detFin s k` of every `k` in the stabiliser `stdLevel E n` of the standard lattice. -/
lemma apply_det_eq_one (h : μ.HasWeight e 1) {k : Gf E n} (hk : k ∈ stdLevel E n) :
    μ.val (detFin s k) = 1 := by
  -- The archimedean part of `det (1, k)` is `1`, and the tame part is trivial at every place.
  ext
  -- `↓` turns the tame product into a product over `∅` before simp unfolds it; without it
  -- `∏ᶠ w, 1 (reduceAt w (det k))` is left.
  simp [h.apply_eq, det_mem (mem_stdLevel.mp hk), ↓finprod_tame_eq_prod_reduceU1 (S := ∅)]

/-- Let `μ` have weight `e` and tame part `ψ`, trivial at the places of `A` and their conjugates.
Then `μ` is trivial on `det k` for every integral point `k` supported on `A` and its conjugate. -/
lemma apply_det_eq_one_of_supportedOn (h : μ.HasWeight e ψ) {A : Set (FinPlace E)}
    (hψ : ∀ w ∈ A.conjClosure, ψ w = 1) {k : Gf E n} (hk : k ∈ stdLevel E n ⊓ Gf.supportedOn n A) :
    μ.val (detFin s k) = 1 := by
  -- `μ (det k)` is a product over the places where `ψ` is not trivial, and there `k` is `1`.
  obtain ⟨k_int, k_supp⟩ := hk
  have : Fintype {w : FinPlace E | ψ w ≠ 1} := h.finite_ramification.fintype
  have h_red (w : FinPlace E) (hw : ψ w ≠ 1) : stdLevel.reduceAt w ⟨k, k_int⟩ = 1 := by
    obtain ⟨h_not, h_star_not⟩ : w ∉ A ∧ star w ∉ A := not_or.1 fun h_mem ↦ hw (hψ w h_mem)
    exact stdLevel.reduceAt_eq_one_of_atPlace (Gf.mem_supportedOn.1 k_supp w h_not h_star_not)
  have h_prod : (μ.val (detFin s k) : ℂ) =
      ∏ w : {w : FinPlace E | ψ w ≠ 1}, ψ w (stdLevel.reduceAt w.val ⟨k, k_int⟩).val.det :=
    h.apply_det_eq_prod Subtype.val_injective (by simp) ⟨k, k_int⟩
  exact Circle.ext (h_prod.trans (Finset.prod_eq_one fun w _ ↦ by simp [h_red w.val w.property]))

end New.AutChar.HasWeight

/-!
## Values of the local characters at determinants

* `New.Exchange.spaceChar_rankTwist`: in even rank the two twists by the splitting character cancel.
-/

namespace New.Exchange

open Matrix Fintype WeilData Gf Finset

variable {E : Type} [Field E] [CMType E] {n : Type _} [Fintype n] [DecidableEq n]
  {s : n → ℤˣ} {P : Finset (FinPlace E)} {μ : NumberField.InfinitePlace E → ℤ}
  (𝔠 : SplitTameChar E μ) {k : Gf E n}

/-- Given Weil data on E, `upsilonU1` is the restriction of its splitting character υ to the
norm-one ideles, a character of U(1)(𝔸) trivial on E, with trivial tame part. It is trivial on
`detFin s k`, the determinant of (1, k) in G, for every `k` in the stabiliser `stdLevel E n` of the
standard lattice Ô^n. -/
@[simp]
lemma upsilonU1_detFin_eq_one_of_mem_stdLevel [WeilData E] (hk : k ∈ stdLevel E n) :
    upsilonU1.val (detFin s k) = 1 :=
  upsilonU1_hasWeight.apply_det_eq_one hk

omit [DecidableEq n] in
/-- In even rank `n`, multiplying `ν` by `upsilonU1 ^ (n / 2)`, taking the base change and dividing
by `υ ^ n`, for the splitting character `υ`, gives the base change `ν.baseChange`, the character
t ↦ ν(t/t̄) of the ideles of E: the two twists by the splitting character cancel. -/
lemma spaceChar_rankTwist [WeilData E] {ν : AutChar E} (hn : 2 ∣ card n) :
    (rankTwist ν n).spaceChar (card n) = ν.baseChange := by
  rw [ν.spaceChar_rankTwist_eq_ite, ite_eq_left (even_iff_two_dvd.mpr hn)]

lemma atPlaces_eq_one_of_mem_trivialOn (hk : k ∈ Gf.trivialOn n P) : atPlaces P k = 1 := by
  -- The entries of `k` are those of `1` at every place of `P`, so are their components at `P`.
  have h_entry : ∀ w ∈ P, ∀ i j : n, (k.val.val i j) w = if i = j then 1 else 0 := by
    simpa [GeneralLinearGroup.ext_iff, atPlace, Matrix.one_apply] using hk
  ext i j w
  simp [atPlaces, evalPlaces, Matrix.one_apply, ite_apply, h_entry w.val w.property i j]

/-- The local character `localChar P ξ k` at the determinant of the components of `g` at `P` is
`ξ t * |t| ^ (k / 2)`, for the idele `t = detOn P g.val` that is `det g` at `P` and `1`
elsewhere. -/
@[simp]
lemma localChar_det (ξ : HeckeChar E) (k : ℤ) (g : Gf E n) :
    localChar P ξ k (atPlaces P g).val.det =
      ξ.val (detOn P g.val) * √(ideleAbs (detOn P g.val)) ^ k := by
  -- Both sides are products over the places `w` of `P` of `ξ (t w) * √‖t w‖ ^ k`, where `t w` is
  -- the idele with the component of the determinant of `g` at `w` and `1` elsewhere.
  let t (w : P) : (𝔸 E)ˣ := locFullIdele w.val (GeneralLinearGroup.det (atPlace w.val g))
  -- The inclusion of the circle into `ℂ` is multiplicative.
  have h_coe (s : Finset P) (f : P → Circle) : ((∏ w ∈ s, f w : Circle) : ℂ) = ∏ w ∈ s, (f w : ℂ) :=
    map_prod Circle.coeHom f s
  calc localChar P ξ k (atPlaces P g).val.det
    _ = ∏ w : P, (ξ.val (t w) * √(ideleAbs (t w)) ^ k : ℂ) := by
      rw [← GeneralLinearGroup.val_det_apply, localChar, MulChar.ofUnitHom_coe]
      simp [t, g.val.map_det, atPlaces, atPlace, ideleAbs_locFullIdele, prod_mul_distrib]
      -- The values of `ξ` agree factor by factor, by the definitions of `finPart` and
      -- `locFullIdele`.
      exact .inl rfl
    _ = ξ.val (∏ w, t w) * √(ideleAbs (∏ w, t w)) ^ k := by
      simp [t, h_coe, Real.sqrt_prod, ideleAbs_locFullIdele, prod_zpow, prod_mul_distrib]
    _ = _ := by rw [detOn_eq_prod, ← P.prod_coe_sort]

/-- Every invertible matrix over the product of the completions at the ramified places
`𝔠.ramifiedPlaces` is the family of components at `𝔠.ramifiedPlaces` of an element of the finite
adelic unitary group supported on `𝔠.ramifiedPlaces` and its conjugate
(`supportedOn n 𝔠.ramifiedPlaces`). -/
lemma SplitTameChar.exists_atPlaces_eq (g : GL n (LocProd 𝔠.ramifiedPlaces)) :
    ∃ k ∈ supportedOn n 𝔠.ramifiedPlaces, atPlaces 𝔠.ramifiedPlaces k = g := by
  -- Place the component `c w` of `g` at each `w ∈ 𝔠.ramifiedPlaces` by `ofSplitPlaces`.
  let c (w : 𝔠.ramifiedPlaces) : GL n (LocField w.val) := g.map (Pi.evalRingHom _ w)
  refine ⟨ofSplitPlaces 𝔠.star_notMem c, ofSplitPlaces_mem_supportedOn 𝔠.star_notMem c, ?_⟩
  ext i j w : 3
  -- At `w` the element `ofSplitPlaces c` has the component `c w`.
  exact congrArg (fun A : GL n (LocField w.val) ↦ A i j) (atPlace_ofSplitPlaces 𝔠.star_notMem c w)

/-- On the determinant of an integral finite point `k`, the character `𝔠.character` of the tame
character `𝔠` of weight `μ`, ramified at the finite set `𝔠.ramifiedPlaces` of split places, is the
local character `𝔠.semilocalChar` at the determinant of the components of `k` at
`𝔠.ramifiedPlaces`. -/
lemma SplitTameChar.character_detFin_eq_of_mem_stdLevel (hk : k ∈ stdLevel E n) :
    𝔠.character.val (detFin s k) = 𝔠.semilocalChar (atPlaces 𝔠.ramifiedPlaces k).val.det := by
  simp [character_apply_of_integral, IsIntMatrix.det_mem (mem_stdLevel.mp hk), RingHom.map_det,
    atPlaces]

end New.Exchange

/-! ## Reduction of K₀ modulo 𝔪 and characters tame for a modulus -/

namespace New

open Ideal MulChar NumberField stdLevel Rows Set Modulus Function AutChar Finset Subgroup

attribute [local instance low] Fintype.ofFinite

section

variable {E n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] [DecidableEq n]
  {𝔪 : Modulus E} {a : 𝓞 E} (g : GL n 𝔪.ResidueRing) {H : Subgroup (GL n 𝔪.ResidueRing)}

/-! ### Reduction modulo 𝔪 -/

/-- Let `𝔪` be a modulus of the CM field `E`, that is, a nonzero ideal of O_E that no prime divides
together with its conjugate. Then every `g` in GL_n(O_E/𝔪) is the reduction modulo `𝔪` of some `k`
in K₀ = `stdLevel E n`, the stabiliser of Ô^n in the finite adelic unitary group `Gf`. Moreover `k`
can be chosen supported on the places dividing `𝔪` and their conjugates, meaning its component is 1
at every other place. -/
lemma Rows.exists_reductionGL_eq :
    ∃ k : stdLevel E n, k.val ∈ Gf.supportedOn n 𝔪.places ∧ 𝔪.reductionGL k = g := by
  -- Lift the entries of `g` to `Ô`. At each place dividing `𝔪` the component of the lift is
  -- invertible over the local integers; `ofSplitPlaces` glues these components to a unitary
  -- element.
  have h_lift (i j : n) : ∃ m : Ô E, 𝔪.reduction m = g i j := 𝔪.reduction_surjective (g i j)
  choose M hM using h_lift
  obtain ⟨S, hS⟩ : ∃ S : Finset (FinPlace E), ↑S = 𝔪.places := 𝔪.places.toFinite.exists_finset_coe
  have h_split (w : FinPlace E) (hw : w ∈ S) : star w ∉ S :=
    fun hw' ↦ 𝔪.isConjDisjoint_places.le_compl_right (hS.le hw) (hS.le hw')
  let Mloc (w : S) : Matrix n n (LocInt w.val) :=
    fun i j ↦ ⟨(M i j).val w, mem_Ô.mp (M i j).property w⟩
  -- The residue of `Mloc w` is the invertible matrix `g` read modulo `w`.
  have h_unit (w : S) : IsUnit (Mloc w) := by
    refine isUnit_of_mapMatrix (IsLocalRing.residue _)
      ⟨g.map (modulusResidue 𝔪 (hS.le w.property)), ?_⟩
    -- Both sides are the residue at `w` of the entry `M i j`.
    have h_res (i j : n) :
        reduceAt w.val (M i j) = IsLocalRing.residue (LocInt w.val) (Mloc w i j) := rfl
    ext i j
    simp [← hM, h_res]
  let γ (w : S) : GL n (LocField w.val) := .map (LocInt w.val).subtype (h_unit w).unit
  -- `ofSplitPlaces` glues the local components `γ w`, which are integral, into an element of `K₀`.
  have h_int : ofSplitPlaces h_split γ ∈ stdLevel E n :=
    (ofSplitPlaces_mem_stdLevel h_split γ).mpr fun w ↦ ⟨(h_unit w).unit, rfl⟩
  refine ⟨⟨ofSplitPlaces h_split γ, h_int⟩, ?_, ?_⟩
  · simpa only [← hS] using ofSplitPlaces_mem_supportedOn h_split γ
  -- Reduction modulo `𝔪` only sees the components at `𝔪.places`, where the entries agree with `M`.
  have h_comp (i j : n) (w : FinPlace E) (hw : w ∈ 𝔪.places) :
      (ofSplitPlaces h_split γ).val.val i j w = (M i j).val w := by
    have h_at : (ofSplitPlaces h_split γ).atPlace w = γ ⟨w, hS.ge hw⟩ :=
      atPlace_ofSplitPlaces h_split γ ⟨w, hS.ge hw⟩
    exact congrArg (fun A : GL n (LocField w) ↦ A i j) h_at
  ext i j
  rw [← hM]
  exact reduction_congr 𝔪 (h_comp i j)

/-- A chosen lift of g ∈ GL_n(O_E/𝔪) to K₀, with component 1 outside the places dividing 𝔪 and their
conjugates. -/
def Rows.liftMod : stdLevel E n := (exists_reductionGL_eq g).choose

@[simp]
lemma Rows.reductionGL_liftMod : 𝔪.reductionGL (liftMod g) = g :=
  (exists_reductionGL_eq g).choose_spec.right

@[simp]
lemma Rows.reductionGL_surjective : Surjective (𝔪.reductionGL (n := n)) :=
  fun g ↦ ⟨liftMod g, reductionGL_liftMod g⟩

/-- The level cut out by a subgroup H of GL_n(O_E/𝔪): the elements of K_0 (`New.stdLevel`) whose
reduction modulo 𝔪 lies in H, as a subgroup of G_f. -/
abbrev Modulus.levelOfSubgroup (𝔪 : Modulus E) (H : Subgroup (GL n 𝔪.ResidueRing)) :
    Subgroup (Gf E n) :=
  (Subgroup.comap (reductionGL 𝔪) H).map (stdLevel E n).subtype

/-- If `a ∈ 𝔪`, the principal level of `a` (the elements of `K₀` congruent to `1` modulo `a`) lies
in the level `𝔪.levelOfSubgroup H` of every subgroup `H`. -/
lemma Modulus.principalLevel_le_levelOfSubgroup (ha : a ∈ 𝔪.ideal) :
    principalLevel n a ≤ 𝔪.levelOfSubgroup H := by
  -- An element of level `a` reduces to `1` modulo `𝔪`, because `a` reduces to `0`.
  intro k hk
  have hk_int : k ∈ stdLevel E n := hk.left
  have h_red : 𝔪.reduction (algebraMap (𝓞 E) (Ô E) a) = 0 := by simpa [← RingHom.mem_ker] using ha
  have h_one : 𝔪.reductionGL ⟨k, hk_int⟩ = 1 := map_eq_one_of_mem_principalLevel hk h_red
  exact ⟨⟨k, hk_int⟩, H.ker_le_comap _ h_one, rfl⟩

/-- `𝔪.levelOfSubgroup H` is a level: it lies in `K₀` and is open. -/
instance : IsLevel (𝔪.levelOfSubgroup H) where
  le := map_subtype_le _
  -- it contains the open principal level of the norm of `𝔪`
  isOpen := isOpen_mono (principalLevel_le_levelOfSubgroup 𝔪.ideal.absNorm_mem)
    (isOpen_principalLevel (by simp [ne_bot, absNorm_eq_zero_iff]))

/-- Let `𝔪` be a modulus of the CM field `E` and `H` a subgroup of `GL_n(O_E/𝔪)`. Let
`𝔪.levelOfSubgroup H` be the preimage of `H` under reduction mod `𝔪` inside `K₀ = stdLevel`, the
stabiliser G_f ∩ GL_n(Ô) of the standard lattice. Then the index of `𝔪.levelOfSubgroup H` in `K₀`
equals the index of `H` in `GL_n(O_E/𝔪)`. -/
lemma Modulus.stdLevelIndex_levelOfSubgroup : stdLevelIndex (𝔪.levelOfSubgroup H) = H.index := by
  simp [relIndex, subgroupOf, comap_map_eq, index_comap_of_surjective]

/-- If 𝔪 = (a), an element of K₀ has principal level a exactly when it reduces to 1 modulo 𝔪. -/
lemma Modulus.mem_principalLevel_iff (h𝔪 : 𝔪.ideal = span {a}) (k : stdLevel E n) :
    k.val ∈ principalLevel n a ↔ 𝔪.reductionGL k = 1 := by
  -- both sides say that the entries of `k - 1` are multiples of `a` in `Ô E`
  -- `↓` applies `reduction_eq_zero_iff` before simp splits `reduction (k - 1)` into a difference.
  simpa [principalLevel, h𝔪, reductionGL, stdLevel.map_eq_one, ↓reduction_eq_zero_iff, map_span,
    mem_span_singleton, dvd_def, Subtype.ext_iff, Subgroup.copy] using .rfl

/-! ### Tame characters -/

/-- The multiplicative character x ↦ ∏_{w∣𝔪} ψ_w(x mod w) of O_E/𝔪, for characters ψ_w of the
residue fields. -/
@[simps -isSimp]
def Modulus.charOfTamePart (𝔪 : Modulus E) (ψ : ∀ w : FinPlace E, MulChar (ResField w) ℂ) :
    MulChar 𝔪.ResidueRing ℂ :=
  MulChar.mk
    { toFun x := ∏ᶠ w : places 𝔪, ψ w (modulusResidue 𝔪 w.2 x)
      map_one' := by simp
      map_mul' := by simp [finprod_eq_prod_of_fintype, Finset.prod_mul_distrib] }
    (by
      -- a non-unit lies in a maximal ideal `M`; the factor at the place under `M` vanishes
      rintro ⟨x⟩ hx
      obtain ⟨M, hM_max, hM⟩ := exists_max_ideal_of_mem_nonunits hx
      let w : places 𝔪 := ⟨⟨M.under _, inferInstance, NeZero.out⟩, le_comap_of_map_le (by simp)⟩
      refine finprod_eq_zero _ w ?_ (toFinite _)
      -- The residue of `x` at `w` is `0`, as `x` lies in the maximal ideal `M` over `w`.
      show ψ w.val (algebraMap (𝓞 E) (ResField w.val) x) = 0
      rw [algebraMap_ResField_eq_zero.mpr hM, MulChar.map_zero])

/-- ν is tame for 𝔪 with weight e and character χ: 𝔪 ≠ (1), ν has weight e and a tame part (ψ_w)
that is nontrivial exactly at the primes w dividing 𝔪, and χ = ∏_{w∣𝔪} ψ_w on O_E/𝔪. -/
def Exchange.IsTameFor {E : Type} [Field E] [CMType E] (𝔪 : Modulus E) (ν : AutChar E)
    (e : InfinitePlace E → ℤ) (χ : MulChar 𝔪.ResidueRing ℂ) : Prop :=
  Nonempty 𝔪.places ∧ ∃ ψ : (w : FinPlace E) → MulChar (ResField w) ℂ,
    ν.HasWeight e ψ ∧ (∀ w : FinPlace E, ψ w ≠ 1 ↔ w ∈ 𝔪.places) ∧ χ = 𝔪.charOfTamePart ψ

end

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] {𝔪 : Modulus E} {a : 𝓞 E}
  {ν : AutChar E} {e : InfinitePlace E → ℤ} {χ : MulChar 𝔪.ResidueRing ℂ} {s : n → ℤˣ}

/-- Let `ν` be a character of `[U(1)]`, that is, an `AutChar E`, a character of U(1)(𝔸) trivial on
elements coming from E, that has weight `e` and tame part `ψ` (`HasWeight`), where `ψ` is a family
of residue-field characters ψ_w that are trivial for every finite place w not dividing the modulus
`𝔪`. Then for `k` in K₀ = `stdLevel E n`, the value of `ν` at the norm-one adele `detFin s k` is
`𝔪.charOfTamePart ψ` at the determinant of `k` mod `𝔪`. Here `𝔪.charOfTamePart ψ` is the character
x ↦ ∏_{w∣𝔪} ψ_w(x mod w) of O_E/𝔪. -/
lemma AutChar.HasWeight.apply_det_eq_charOfTamePart {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ}
    (hν : HasWeight ν e ψ) (hψ : ∀ w : FinPlace E, w ∉ 𝔪.places → ψ w = 1) (k : stdLevel E n) :
    ν.val (detFin s k.val) = 𝔪.charOfTamePart ψ (𝔪.reductionGL k).val.det := by
  -- `apply_det_eq_prod`: `ν (det k)` is the product over `w ∣ 𝔪` of `ψ w (det (k mod w))`.
  rw [hν.apply_det_eq_prod (ι := 𝔪.places) Subtype.val_injective (by simpa using hψ)]
  simp [charOfTamePart, Matrix.det_apply, stdLevel.reduceAt, finprod_eq_prod_of_fintype,
    reductionGL]

namespace Exchange.IsTameFor

/-- If ν is tame for 𝔪 with weight e and character χ, then ν⁻¹ is so with -e and χ⁻¹. -/
lemma inv (h : IsTameFor 𝔪 ν e χ) : IsTameFor 𝔪 ν⁻¹ (-e) χ⁻¹ := by
  obtain ⟨h_ne, ψ, hν, h_ram, rfl⟩ := h
  refine ⟨h_ne, ψ⁻¹, hν.inv, by simpa using h_ram, ?_⟩
  ext x
  simp [charOfTamePart_apply, inv_apply_eq_inv, finprod_eq_prod_of_fintype]

/-- Multiplying by a character of weight d with trivial tame part keeps ν tame with the same χ. -/
lemma mul (h : IsTameFor 𝔪 ν e χ) {μ : AutChar E} {d : InfinitePlace E → ℤ}
    (hμ : μ.HasWeight d 1) : IsTameFor 𝔪 (ν * μ) (e + d) χ := by
  obtain ⟨h_ne, ψ, hν, h_ram, rfl⟩ := h
  exact ⟨h_ne, ψ, by simpa using hν.mul hμ, h_ram, rfl⟩

/-- If ν is tame for 𝔪 with character χ, then ν(det k) = χ(det(k mod 𝔪)) for k in K₀. -/
lemma apply_det (h : IsTameFor 𝔪 ν e χ) (k : stdLevel E n) :
    ν.val (detFin s k.val) = χ (𝔪.reductionGL k).val.det := by
  obtain ⟨-, ψ, hν, h_ram, rfl⟩ := h
  exact hν.apply_det_eq_charOfTamePart (fun w hw ↦ by simpa [hw] using h_ram w) k

end Exchange.IsTameFor

end New

/-!
## The tame character on unit ideles and the idele of the uniformisers

Two facts on ideles for a tame character 𝔠 (`New.Exchange.SplitTameChar`) ramified at a finite set S
of split places.
-/

namespace New.Exchange

open Finset SemilocalField

variable {E : Type} [Field E] [CMType E] {μ : NumberField.InfinitePlace E → ℤ}
  (𝔠 : SplitTameChar E μ)

/-- For a finite idele `u` that is a unit at every place, `χ(u_S)⁻¹ · ν(u/ū) / χ(ū_S)⁻¹ = 1`.
Here `χ` is `New.Exchange.SplitTameChar.semilocalChar`, `u_S = evalPlaces 𝔠.ramifiedPlaces u`
denotes the components of `u` at `S`, and `invOnUnits χ x` is `(χ x)⁻¹` when `x` is a unit at every
place of `S`. -/
lemma SplitTameChar.invOnUnits_mul_finPart_div_star_eq_one {u : (𝔸f E)ˣ}
    (hu : u ∈ idelesUnitOff ∅) :
    invOnUnits 𝔠.semilocalChar (evalPlaces 𝔠.ramifiedPlaces u) * 𝔠.character.baseChange.finPart u /
      invOnUnits 𝔠.semilocalChar (evalPlaces 𝔠.ramifiedPlaces (star u)) = 1 := by
  obtain ⟨u_mem, inv_mem⟩ : u.val ∈ Ô E ∧ u⁻¹.val ∈ Ô E := idelesUnitOff_empty.le hu
  -- The base change of `ν` at `u` is `ν` at the integral idele `u / star u`, whose archimedean
  -- components are `1`, so it is a value of `𝔠.semilocalChar`.
  have h_bc : 𝔠.character.baseChange.finPart u =
      (∏ v, (1 * star 1) ^ μ v) * 𝔠.semilocalChar
        (evalPlaces 𝔠.ramifiedPlaces (u * star u⁻¹.val)) :=
    𝔠.character_apply_of_integral (divStar (finIdeleIncl u)) (mul_mem u_mem (star_mem_Ô inv_mem))
  -- `u` and `star u` are units at every place, so both `invOnUnits` factors are values of `χ⁻¹`.
  suffices (𝔠.semilocalChar (evalPlaces 𝔠.ramifiedPlaces u))⁻¹ *
    (𝔠.semilocalChar (evalPlaces 𝔠.ramifiedPlaces u) *
      𝔠.semilocalChar (evalPlaces 𝔠.ramifiedPlaces (star u⁻¹.val))) * 𝔠.semilocalChar
        (evalPlaces 𝔠.ramifiedPlaces (star u.val)) = 1 by
    simpa [h_bc, invOnUnits, isIntegralUnit_iff_v_eq_one, mem_idelesUnitOff.mp hu]
  -- `star u⁻¹ * star u = 1`, and `χ (u_S) ≠ 0` since `u_S` is a unit.
  simp [mul_assoc, ← map_mul, ← star_mul, MulChar.apply_eq_zero_iff, IsUnit.map]

/-- There is a finite idele `c` with component `1` outside `S̄` (the conjugates of
`S = 𝔠.ramifiedPlaces`), whose conjugate has at `S` the chosen uniformisers `ϖ` (the uniformiser
`SemilocalField.ϖ` of the product `LocProd S` of the completions at `S`), and whose inverse has
absolute value `finIdeleAbs c⁻¹ = ∏_{w∈S} q_w`, with `q_w` the order of the residue field at `w`. -/
lemma exists_idele_star_eq_uniformizer :
    ∃ c : (𝔸f E)ˣ, (∀ v : FinPlace E, star v ∉ 𝔠.ramifiedPlaces → c.val v = 1) ∧
      evalPlaces 𝔠.ramifiedPlaces (star c.val) = (ϖ : (LocProd 𝔠.ramifiedPlaces)ˣ).val ∧
      finIdeleAbs c⁻¹ = ∏ i : 𝔠.ramifiedPlaces, ↑i.val.q := by
  -- Take the conjugate of the idele with the uniformisers at the places of `𝔠.ramifiedPlaces`.
  refine ⟨star (∏ i : 𝔠.ramifiedPlaces, locIdele _ (uniformizer i)), fun v hv ↦ ?_, funext fun i ↦
    ?_, ?_⟩
  · -- Each factor is `locIdele (star x) _` with `x ∈ 𝔠.ramifiedPlaces`; its component at
    -- `v ≠ star x` is `1`.
    have h_ne (x : 𝔠.ramifiedPlaces) : v ≠ star x.val := fun h_eq ↦ hv (by simp [h_eq])
    simp only [star_prod, star_locIdele, Units.coe_prod, ← evalAt_apply, map_prod]
    exact Finset.prod_eq_one fun x _ ↦ by rw [evalAt_apply, locIdele_apply_of_ne (h_ne x)]
  · -- At the place `i` only the factor at `i` is not `1` (`prod_eq_single i`); it is the
    -- uniformiser at `i`, which is the component of `ϖ` at `i`.
    simp_all [evalPlaces, prod_eq_single i, eq_comm, ϖ]
  · simp [star_locIdele, norm_locField_eq_q_zpow]

end New.Exchange

end
