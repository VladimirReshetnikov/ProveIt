import Lib.Shimura.AbelianScheme.IsogenyFlatness
import Lib.Shimura.HeckeTower.HeckeData
import Lib.Shimura.ThetaModuli.ThetaFamilyRigidity
import Lib.Shimura.Uniformisation.LieExponential
import Lib.Weil.Unramified.SplitHecke

/-!
# Properties of a Kuga–Sato tower, Hecke operators at split places, torsion counts and levels

The structure `New.Variety.Model` collects the geometry of a tower of Kuga–Sato varieties that the
point count uses. K(𝔑) denotes the principal level `New.Variety.levelGU n 𝔑`. τ_{w,j} denotes the
Hecke element `New.Variety.heckeSum` at a safe split place w of E. The file shows that these
elements lie in the Hecke algebra of K(𝔑). It counts the `I`-torsion of the adelic module
`New.AdelicTorsion E n`: it has N(I) ^ card n elements, where N(I) is the norm of the ideal I. It
proves finiteness statements for multiplication by integers on the abelian schemes of a family
`X : New.ThetaFamily D Z τ`.

## Main definitions and results

* `New.Variety.Model`: the tower of varieties with its properties.
* `New.Variety.asAlgebraHom_heckeSum`: τ_{w,j} acts on K(𝔑)-fixed vectors as a central element times
  the j-th Hecke operator of GL_n(E_w); `New.Variety.tauHecke` is τ_{w,j} in the Hecke algebra.
* `New.Variety.Model.exists_isHeckeAction`: the commuting operators on F(Z), for the base Z of a
  model and a functor F with descent.
* `New.card_torsionBySet_adelicTorsion`: for `I ≠ 0` the `I`-torsion of `New.AdelicTorsion E n` has
  `N(I) ^ card n` elements.
* `New.Variety.exists_level_conj_mem`: a principal level deep enough for finitely many isogenies.

Notions from other files:
* `New.Variety.SplitFinPlace`: The finite places w of E with w̄ ≠ w, that is, those split over the
  maximal real subfield.
* `New.Variety.levelGU`: the principal level K(𝔑), the similitudes in `GL_n(Ô E)` that are congruent
  to `1` modulo `𝔑`.
* `New.Variety.conjAtSplit w g`: for a split place w, the adelic matrix that is g⁻ᵀ at w, the
  conjugate of g at w̄, and 1 elsewhere.
* `New.Variety.heckeSum n k w j`: the Hecke element τ_{w,j}, the sum of
  `New.Variety.invHeckeIsogeny w U` over the subspaces U of dimension j.
* `New.Variety.IsSafe`: Safe places w of E: the place u of ℚ(√−d₀) below w satisfies
  `New.GaloisRep.IsSplitPrimeToDisc`, and 𝔑 lies neither in w nor in any place above ū.

## Relation to the literature

Known result: Hecke algebra of a pair acting by correspondences on the base of a tower. Here only a
semigroup acts, and only far enough up the tower, and the algebra is a subalgebra of the group ring.
The cohomology theory may be any functor to modules for which the base is the invariants of each
cover. Source: Shimura, Introduction to the arithmetic theory of automorphic functions, 1971, ch. 3
and 7–8.

See also `Lib.Shimura.IntegralModel.TowerExistence`, `Lib.Shimura.Uniformisation.AppellHumbert` and
`Lib.Shimura.AbelianScheme.IsogenyFlatness`.
-/

noncomputable section

/-!
## The tower of varieties and its required properties

Conventions: `New.Variety.levelGU n 𝔑` is the principal level K(𝔑) in the similitude group
`New.Variety.GU`; `New.Variety.GUPlus` is the monoid of similitudes with integral inverse;
`New.Variety.ModuliPoint E n ν` is the type of analytic points a = (frame, reflection, ν marked
vectors), with isomorphisms `New.Variety.ModuliPoint.IsLevelIso` and the action a·(g, α)
`New.Variety.ModuliPoint.act`.
-/

section Model

open NumberField CategoryTheory AlgebraicGeometry Fintype Module

/-- The tower of Kuga–Sato varieties over `R`, given by a list of properties. A level `i` is a
finite set of pairs (non-zero integer of `E`, element of `New.Variety.GUPlus`), ordered by
inclusion. The data are a base Z = `base`, schemes W_i = `cover i` with legs p_g = `leg i g` from
W_i to Z (π = p_1), sets s_i = `legIndices i`, finite groups Δ_i = `deckGroup i` acting through
`deck i`, maps m_α = `mulMap α` of Z, complex points `point i` and the relative dimension
`dimension` of Z; the other fields are properties of these. -/
structure New.Variety.Model {E : Type} [Field E] [CMBase E] (n : Type)
    [Fintype n] [DecidableEq n] (d₀ : ℕ) [HasQuadSubfield d₀ E] (𝔑 : 𝓞 E) (ν : ℕ)
    (R : Subalgebra (𝓞 E) E) where
  /-- The base scheme Z over `Spec R`. -/
  base : Over (Spec ⟨R⟩)
  /-- The scheme W_i over `Spec R` at level `i`. -/
  cover : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n) → Over (Spec ⟨R⟩)
  /-- The set s_i of adelic matrices whose legs the fields at level `i` speak about. -/
  legIndices (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)) : Set (GL n (𝔸f E))
  /-- The legs p_g : W_i → Z, one for each coset gK(𝔑); the leg of `1` is called π. -/
  leg (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)) :
    GL n (𝔸f E) ⧸ levelGU n 𝔑 → (cover i ⟶ base)
  /-- The identity lies in every s_i. -/
  one_mem (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)) : 1 ∈ legIndices i
  /-- For `g` in `GUPlus E n` and any level `j`, all large levels `i` have g ∈ s_i and a map
  f : W_i → W_j with p_q ∘ f = p_{gq} for all q ∈ s_j. -/
  eventually_translate {g : GL n (𝔸f E)} (j : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)) :
    g ∈ GUPlus E n →
      ∀ᶠ i in Filter.atTop, g ∈ legIndices i ∧ ∃ f, ∀ q ∈ legIndices j, f ≫ leg j q = leg i (g * q)
  /-- The finite group Δ_i at level `i`. -/
  deckGroup (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)) : FiniteGrp
  /-- The action of Δ_i on W_i. -/
  deck (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)) :
    deckGroup i →* CategoryTheory.End (cover i)
  /-- For each δ ∈ Δ_i there is κ ∈ K(𝔑) with p_q ∘ δ = p_{κq} for all q ∈ s_i. -/
  deck_comp_leg (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)) (δ : (deckGroup i).toGrp) :
    ∃ κ : levelGU n 𝔑, ∀ q ∈ legIndices i, (deck i δ).asHom ≫ leg i q = leg i (κ.1 * q)
  /-- The maps m_α : Z → Z, one for each family `α` of `ν` integers of `E`. -/
  mulMap (α : Fin ν → 𝓞 E) : base ⟶ base
  /-- The complex point [a]_i of W_i attached to `a`. -/
  point (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)) :
    ModuliPoint E n ν → (specOver R ℂ ⟶ cover i)
  /-- Every complex point of W_i is some [a]_i. -/
  point_surjective (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)) : (point i).Surjective
  /-- π[a]_i = π[b]_i exactly when `a` and `b` are isomorphic at level K(𝔑). -/
  point_eq_iff (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)) (a b : ModuliPoint E n ν) :
    point i a ≫ leg i ⟦1⟧ = point i b ≫ leg i ⟦1⟧ ↔
      ∃ z : GL n E, a.IsLevelIso (levelGU n 𝔑) z b
  /-- For `g` in `GUPlus E n` with g ∈ s_i, m_α p_g [a]_i = π[a·(g, α)]_i. -/
  point_leg {i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)} g (α : Fin ν → 𝓞 E)
    (a : ModuliPoint E n ν) : ↑g ∈ legIndices i →
    point i a ≫ leg i g.1 ≫ mulMap α = point i (a.act g α) ≫ leg i ⟦1⟧
  /-- The relative dimension of Z over `Spec R`. -/
  dimension : ℕ
  /-- Z is smooth over `Spec R` of relative dimension `dimension`. -/
  smooth : SmoothOfRelativeDimension dimension base.hom
  /-- Z is proper over `Spec R`. -/
  [proper : IsProper base.hom]
  /-- W_i is a closed subscheme of a projective space over `Spec R`. -/
  [projective (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)) : HasProjEmbedding (cover i).hom]
  /-- W_i is reduced. -/
  [isReduced (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)) :
      AlgebraicGeometry.IsReduced (cover i).left]
  /-- π is onto, and its fibres in characteristic `0` are torsors under Δ_i. -/
  covering (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)) : IsGaloisCovering (leg i ⟦1⟧) (deck i)
  /-- Let g ∈ s_i and let z : a·(g, α) ≅ a at level K(𝔑) have separable characteristic polynomial,
  with `a.reflection` the involution `markedReflection` of `z` at its `μ`-th listed root. Then at
  [a]_i the polynomial `localTerm` is a constant times det(1 - X (dπ)⁻¹ d(m_α p_g)), in the sense
  of `IsTangentPoly`. -/
  tangent (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)) (g : GUPlus E n) (α : Fin ν → 𝓞 E)
    (a : ModuliPoint E n ν) (z : GL n E) (μ : n) :
    g.1 ∈ legIndices i → z.val.charpoly.Separable → a.reflection = markedReflection z μ →
      (a.act g α).IsLevelIso (levelGU n 𝔑) z a →
      IsTangentPoly dimension ((algPoints (ℂ) (CommRingCat.of R)).map (leg i ⟦1⟧))
        ((algPoints (ℂ) (CommRingCat.of R)).map (leg i g.1 ≫ mulMap α))
        ⟨point i a⟩ (localTerm α z.val.charpoly μ)
  /-- The congruence relation at a split place `w` satisfying `IsSafe`, with residue field k_w of
  order q = p^f: if `𝔭` contains the image of `w` and all g_A = `invHeckeIsogeny w A` lie in s_i, A
  a subspace of k_wⁿ of dimension r, then ∑_A (-1)^r q^{r(r-1)/2} [Frob_p^{(n-r)f} p_{g_A}(x)] = 0
  in the sense of `CongruenceRelation`. -/
  congruence (w : SplitFinPlace E) : IsSafe 𝔑 w.1 →
    ∀ i (𝔭 : Set R), (∀ c ∈ w.1.1, algebraMap (𝓞 E) R c ∈ 𝔭) →
      (∀ A, invHeckeIsogeny w A ∈ legIndices i) →
      let r (A : Submodule (ResField (w : FinPlace E)) (n → ResField (w : FinPlace E))) :=
        finrank (ResField w.1) A
      ∀ ⦃p f : ℕ⦄ [Fact p.Prime], w.1.q = p ^ f →
        CongruenceRelation (fun A ↦ (-1) ^ r A * w.1.q ^ (r A).choose 2) 𝔭 p
          (fun A ↦ (card n - r A) * f)
          (leg i <| invHeckeIsogeny w ·)

end Model

/-!
## Hecke elements τ_{w,j} at safe split places and their operators

* `New.Variety.conj_conjAtSplit`, `New.Variety.conjAtSplit_dualComponent` (with its two parts
  `New.Variety.conjAtSplit_dualComponent_mem_levelGU` and
  `New.Variety.commute_inv_conjAtSplit_dualComponent_mul`): the embedding `New.Variety.conjAtSplit`
  of GL_n(E_w) into the similitudes `New.Variety.GU` and its retraction `New.Variety.dualComponent`.
-/

section LocalHecke

open NumberField Matrix CategoryTheory Set Module WithZero Valued

namespace New.Variety

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
  {n : Type} [Fintype n] [DecidableEq n]
  {𝔑 : 𝓞 E} {d₀ : ℕ} [HasQuadSubfield d₀ E]
  {k W : Type} [CommRing k] [AddCommGroup W] [Module k W]
  {π : Representation k (GL n (𝔸f E)) W} {w : SplitFinPlace E} (g : GL n (LocField w.1))
  (s s' : SafePlace 𝔑 × ℕ) {x : W}

/-- The endomorphism of the unitary group {g : gᴴg = 1} of matrices over R indexed by `n` that
applies the involution of R to each entry. -/
def entryConj {R : Type*} [CommRing R] [StarRing R] :
    U (1 : Matrix n n R) →* U (1 : Matrix n n R) :=
  (invTransposeGL.toMonoidHom.comp (U 1).subtype).codRestrict (U (1 : Matrix n n R)) fun g ↦
    -- transpose the equation that makes `g⁻¹` unitary
    mul_eq_one_comm.1 (by
      show g⁻¹.1.1ᵀ * (g⁻¹.1.1ᵀᴴ * 1) = 1
      simpa [U, -coe_units_inv, conjTranspose, transpose_map] using
        congrArg Matrix.transpose g⁻¹.2)

@[simp]
lemma conjAtSplit_unitary : (conjAtSplit w g).1ᴴ * conjAtSplit w g = 1 := by
  simpa [U] using show conjAtSplit w g ∈ U (1 : Matrix n n (𝔸f E)) from
    (entryConj (ofSplitPlace w.2 g)).property

/-- `conjAtSplit w g` is a unitary similitude (with multiplier `1`). -/
@[simp]
lemma conjAtSplit_mem_GU : conjAtSplit w g ∈ GU E n := ⟨1, rfl, 1, by simp⟩

@[simp]
lemma evalAt_conjAtSplit : (conjAtSplit w g).map (evalAt w.1) = invTransposeGL g := by
  show invTransposeGL ((ofSplitPlace w.2 g).atPlace w.1) = invTransposeGL g
  rw [atPlace_ofSplitPlace]

/-- At a place `u` other than `w` and its conjugate, the component of `conjAtSplit w g` is `1`. -/
lemma evalAt_conjAtSplit_of_ne {u : FinPlace E} (hu : u ≠ w.val) (hu' : star u ≠ w) :
    (conjAtSplit w g).map (evalAt u) = 1 :=
  invTransposeGL.map_eq_one_iff.mpr (atPlace_ofSplitPlace_of_ne w.2 _ hu hu')

@[simp]
lemma dualComponent_conjAtSplit : dualComponent w (conjAtSplit w g) = g := by simp [dualComponent]

/-- Let w be a split place and g a unitary similitude. Then conjugating `conjAtSplit w m` by g gives
`conjAtSplit w` of the conjugate of m by the component `dualComponent w g`. -/
lemma conj_conjAtSplit {g : GL n (𝔸f E)} (hg : g ∈ GU E n) (m : GL n (LocField (w : FinPlace E))) :
    g * conjAtSplit w m * g⁻¹ = conjAtSplit w (dualComponent w g * m * (dualComponent w g)⁻¹) := by
  obtain ⟨c, hc, ε, hframe⟩ := hg
  -- `gᴴ * g` is a scalar matrix, so every unitary matrix preserves this form too.
  have h_scalar : g.1ᴴ * g.1 = (c⁻¹ : E) • finAdeleIncl ℚ E ε • 1 := by
    simpa [hc.ne', map_smul'] using congrArg (fun M : Matrix n n (𝔸f E) ↦ (c⁻¹ : E) • M) hframe
  have h_mem : conjAtSplit w m ∈ U (g.1ᴴ * 1 * g.1) := by simp [U, h_scalar]
  -- Hence both sides are unitary. They are trivial off `w` and its conjugate, and they have the
  -- same component at `w`.
  have h_conj_eq : U.conj g rfl ⟨conjAtSplit w m, h_mem⟩ =
      ⟨conjAtSplit w (dualComponent w g * m * (dualComponent w g)⁻¹), (entryConj _).property⟩ := by
    refine Gf.eq_of_supportedOn (S := {w.1}) ?_ ?_ ?_ <;>
      simp_all [Gf.atPlace, dualComponent, evalAt_conjAtSplit_of_ne]
  exact congrArg Subtype.val h_conj_eq

/-- A unitary similitude whose component `dualComponent w g` is `1` commutes with the image of
`conjAtSplit w`. -/
lemma commute_conjAtSplit {g : GL n (𝔸f E)} (hg : g ∈ GU E n ⊓ (dualComponent w).ker)
    (m : GL n (LocField w.1)) : Commute g (conjAtSplit w m) := by
  obtain ⟨hg_GU, hg_ker⟩ := hg
  have h_one : dualComponent w g = 1 := MonoidHom.mem_ker.mp hg_ker
  have h_conj : g * conjAtSplit w m * g⁻¹ = conjAtSplit w m := by
    simp [conj_conjAtSplit hg_GU, h_one]
  exact eq_mul_of_mul_inv_eq h_conj

/-- `conjAtSplit w g` is an integral matrix exactly when `g` lies in the maximal compact subgroup
`localIntGL n w` of `GL_n(E_w)`. -/
lemma conjAtSplit_mem_intGL_iff {g : GL n (LocField (w : FinPlace E))} :
    conjAtSplit w g ∈ intGL n (Ô E) ↔ g ∈ localIntGL n w.1 := by
  show invTransposeGL (ofSplitPlace w.2 g).val ∈ intGL n (Ô E) ↔ g ∈ localIntGL n w.1
  rw [invTransposeGL_mem_intGL]
  exact ofSplitPlace_mem_stdLevel w.2 g

/-! ### The level, place by place -/

/-- A similitude g in GL_n(Ô) lies in the principal level K(𝔑) if at each place u dividing 𝔑 it
has the same u-component as some element of K(𝔑). -/
lemma mem_levelGU_of_map_evalAt_eq {g : GL n (𝔸f E)} (hGU : g ∈ GU E n) (hint : g ∈ intGL n (Ô E))
    (h_places : ∀ u : FinPlace E, 𝔑 ∈ u.asIdeal → ∃ κ ∈ levelGU n 𝔑,
      g.map (evalAt u) = κ.map (evalAt u)) :
    g ∈ levelGU n 𝔑 := by
  -- Divisibility of an entry of `g - 1` by `𝔑` is read at the places `u` that divide `𝔑`, and
  -- there `g` agrees with an element `κ` of the level.
  have h_entry (i j : n) : (g.1 - 1) i j ∈ Ô E ∙ algebraMap (𝓞 E) (𝔸f E) 𝔑 := by
    refine mem_span_iff_valuation_le.mpr ⟨?_, fun u hu ↦ ?_⟩
    · aesop (add simp [mem_intGL, Matrix.one_apply])
    obtain ⟨κ, hκ, h_loc⟩ := h_places u hu
    have hκ_entries : ∀ i j : n, (κ.1 - 1) i j ∈ Ô E ∙ algebraMap (𝓞 E) (𝔸f E) 𝔑 :=
      (Subgroup.mem_inf.mp hκ).right.right
    obtain ⟨-, hκ_le⟩ := mem_span_iff_valuation_le.mp (hκ_entries i j)
    have h_entry_u : g.1 i j u = κ.1 i j u := congrArg (fun M : GL n (LocField u) ↦ M.1 i j) h_loc
    simpa [h_entry_u] using hκ_le u hu
  exact ⟨hGU, hint, h_entry⟩

/-- For `𝔑 ≠ 0`, the preimage of the principal level K(𝔑) under `conjAtSplit w` is open in
`GL_n(E_w)`. -/
lemma isOpen_comap_conjAtSplit (h𝔑 : 𝔑 ≠ 0) :
    IsOpen ((levelGU n 𝔑).comap (conjAtSplit w)).carrier := by
  have h_cont : Continuous (conjAtSplit (n := n) w) := .of_coeHom_comp
    (Units.continuous_coe_inv.comp (continuous_ofSplitPlace w.2).subtype_val).matrix_transpose
  exact .and (by simp) ((isOpen_congruenceGL_span h𝔑).preimage h_cont)

/-- Let w be split with 𝔑 ∉ w̄, and let κ ∈ K(𝔑). Then `conjAtSplit w (dualComponent w κ)`, the
unitary element equal to κ at w and to 1 away from w and w̄, lies in K(𝔑). -/
lemma conjAtSplit_dualComponent_mem_levelGU (h_notMem : 𝔑 ∉ (star w.val).asIdeal)
    {κ : GL n (𝔸f E)} (hκ : κ ∈ levelGU n 𝔑) :
    conjAtSplit w (dualComponent w κ) ∈ levelGU n 𝔑 := by
  have hκ_int : κ ∈ intGL n (Ô E) := (Subgroup.mem_inf.mp hκ).right.left
  have h_int : conjAtSplit w (dualComponent w κ) ∈ intGL n (Ô E) :=
    conjAtSplit_mem_intGL_iff.mpr ((invTransposeGL_mem_intGL _).mpr (mem_intGL_Ô.mp hκ_int _))
  -- At a place `u` containing `𝔑` the element agrees with `κ` (if `u = w`) or with `1`, since
  -- `u ≠ star w` by `h_notMem`.
  refine mem_levelGU_of_map_evalAt_eq (conjAtSplit_mem_GU _) h_int fun u hu ↦ ?_
  by_cases huw : w = u
  · subst huw
    exact ⟨κ, hκ, evalAt_conjAtSplit _⟩
  · refine ⟨1, one_mem _, ?_⟩
    simp (disch := grind [star_star]) [evalAt_conjAtSplit_of_ne]

/-- Let κ be a unitary similitude and c = `conjAtSplit w (dualComponent w κ)`. Then c⁻¹κ commutes
with every element `conjAtSplit w m` of the image of `conjAtSplit w`. -/
lemma commute_inv_conjAtSplit_dualComponent_mul {κ : GL n (𝔸f E)} (hκ_GU : κ ∈ GU E n)
    (m : GL n (LocField w.1)) :
    Commute ((conjAtSplit w (dualComponent w κ))⁻¹ * κ) (conjAtSplit w m) := by
  -- The element `(conjAtSplit w (dualComponent w κ))⁻¹ * κ` is trivial at `w`.
  have h_GU : (conjAtSplit w (dualComponent w κ))⁻¹ * κ ∈ GU E n :=
    mul_mem (inv_mem (conjAtSplit_mem_GU _)) hκ_GU
  have h_ker : (conjAtSplit w (dualComponent w κ))⁻¹ * κ ∈ (dualComponent w).ker := by simp
  exact commute_conjAtSplit ⟨h_GU, h_ker⟩ m

/-- Both `conjAtSplit_dualComponent_mem_levelGU` and `commute_inv_conjAtSplit_dualComponent_mul`:
for w split with 𝔑 ∉ w̄ and κ ∈ K(𝔑), c = `conjAtSplit w (dualComponent w κ)` lies in K(𝔑), and
c⁻¹κ commutes with the whole image of `conjAtSplit w`. -/
lemma conjAtSplit_dualComponent (h_notMem : 𝔑 ∉ (star w.val).asIdeal) {κ : GL n (𝔸f E)}
    (hκ : κ ∈ levelGU n 𝔑) :
    conjAtSplit w (dualComponent w κ) ∈ levelGU n 𝔑 ∧
    ∀ m : GL n (LocField (w : FinPlace E)),
      Commute ((conjAtSplit w (dualComponent w κ))⁻¹ * κ) (conjAtSplit w m) :=
  ⟨conjAtSplit_dualComponent_mem_levelGU h_notMem hκ,
    commute_inv_conjAtSplit_dualComponent_mul (Subgroup.mem_inf.mp hκ).left⟩

/-- Let w̄ ∤ 𝔑 and let b be a combination of elements g of D. Assume that each g in D lies in
`New.Variety.GUPlus` and commutes with everything commuting with the local group at w. If in every
representation b sends K(𝔑)-fixed vectors to vectors fixed by the preimage of K(𝔑) under
`New.Variety.conjAtSplit` at w, then b lies in the Hecke algebra `heckeAlgebra n k 𝔑`: the
combinations of elements of `GUPlus E n` that in every representation send K(𝔑)-fixed vectors to
K(𝔑)-fixed vectors. -/
lemma mem_heckeAlgebra_of_mem_fixedToEigen (h_notMem : 𝔑 ∉ (star w.val).asIdeal)
    {D : Set (GL n (𝔸f E))} {b : MonoidAlgebra k (GL n (𝔸f E))} (hb : b ∈ spanOn k D)
    (hD_GUPlus_comm : ∀ g ∈ D, g ∈ GUPlus E n ∧
      ∀ d : GL n (𝔸f E), (∀ m : GL n (LocField (w : FinPlace E)), Commute d (conjAtSplit w m)) →
        Commute d g)
    (h_fixed : b ∈ fixedToEigen (levelGU n 𝔑) (conjAtSplit w)) :
    b ∈ heckeAlgebra n k 𝔑 := by
  have hD_GUPlus : D ⊆ GUPlus E n := fun g hg ↦ (hD_GUPlus_comm g hg).left
  refine ⟨Submodule.span_mono (Set.image_mono hD_GUPlus) hb, fun W' _ _ π y hy κ ↦ ?_⟩
  -- Write `κ = c * (c⁻¹ * κ)` with `c = conjAtSplit w (dualComponent w κ)`: the second factor
  -- commutes with `b` and fixes `y`, and `c` fixes `b y` by `h_fixed`.
  have hκ_GU : κ.1 ∈ GU E n := (Subgroup.mem_inf.mp κ.prop).left
  set c : GL n (𝔸f E) := conjAtSplit w (dualComponent w κ.1)
  have hc : c ∈ levelGU n 𝔑 := conjAtSplit_dualComponent_mem_levelGU h_notMem κ.prop
  have hb_comm : Commute (MonoidAlgebra.of k _ (c⁻¹ * κ.1)) b := by
    refine .span_right ?_ _ hb
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨-, hg_comm⟩ := hD_GUPlus_comm g hg
    exact (hg_comm _ (commute_inv_conjAtSplit_dualComponent_mul hκ_GU)).map _
  have h_comm_y : π c (π.asAlgebraHom (MonoidAlgebra.of k _ (c⁻¹ * κ.1) * b) y) =
      π c (π.asAlgebraHom (b * MonoidAlgebra.of k _ (c⁻¹ * κ.1)) y) := by
    rw [hb_comm.eq]
  calc π κ.1 (π.asAlgebraHom b y) = π c (π.asAlgebraHom b y) := by
        simpa [hy κ, hy ⟨c⁻¹, inv_mem hc⟩] using h_comm_y
    _ = (1 : k) • π.asAlgebraHom b y := h_fixed hy ⟨dualComponent w κ, hc⟩

/-! ### The Hecke elements -/

omit [IsCMField E] in
lemma commute_scalar_GL (z : (𝔸f E)ˣ) (g : GL n (𝔸f E)) : Commute g (.scalar n z) :=
  (g.scalar_commute z).symm

/-- For a finite idele x of K₀ and z = `centralScalar x`, the scalar matrix of the conjugate of x,
the matrix zᴴz is the scalar matrix of the norm of x to ℚ. -/
private lemma conjTranspose_centralScalar_mul_centralScalar (x : (𝔸f (QuadField d₀))ˣ) :
    ((centralScalar (n := n) x : GL n (𝔸f E)) : Matrix n n (𝔸f E))ᴴ *
        (centralScalar (n := n) x : GL n (𝔸f E)) =
      finAdeleIncl ℚ E ((x.map (adeleNorm ℚ (QuadField d₀)) : (𝔸f ℚ)ˣ) : 𝔸f ℚ) • 1 := by
  -- The norm from the quadratic field to `ℚ` is `y * star y`: this holds for field elements
  -- (`norm_maximalRealSubfield_eq_mul_star`, the maximal real subfield being `ℚ`), hence for adeles
  -- by density.
  have h_norm (y : 𝔸f (QuadField d₀)) :
      finAdeleIncl _ E y * star (finAdeleIncl _ E y) = finAdeleIncl ℚ E (adeleNorm ℚ _ y) := by
    revert y
    refine denseRange_algebraMap_finAdele.eq fun i ↦ ?_
    simp [← map_mul, ← map_star_CM, ← norm_maximalRealSubfield_eq_mul_star, RingHom.ext_iff,
      ← Algebra.norm_eq_of_ringEquiv (CMExtension.equivMaximalRealSubfield ℚ _)]
  simp [smul_one_eq_diagonal, h_norm, starRingEnd_apply]

/-- The scalar matrix `centralScalar x` of a finite idele x of K₀ is a unitary similitude. -/
lemma mem_GU_centralScalar (x : (𝔸f (QuadField d₀))ˣ) : centralScalar x ∈ GU E n :=
  mem_GU_of_gram_eq _ (conjTranspose_centralScalar_mul_centralScalar x)

/-- For a finite idele x of K₀ and a rational c equal to the idelic absolute value of the norm of x
to ℚ, the scalar matrix `centralScalar x` is a frame for the scalar form c·1. -/
lemma isScalarFrame_centralScalar (x : (𝔸f (QuadField d₀))ˣ) {c : ℚ}
    (hc : c = finIdeleAbs (x.map (adeleNorm ℚ (QuadField d₀)))) :
    IsScalarFrame (centralScalar x : GL n (𝔸f E)) c :=
  isScalarFrame_of_gram_eq _ (conjTranspose_centralScalar_mul_centralScalar x) hc

/-- For a finite idele x of K₀, both `mem_GU_centralScalar` and `isScalarFrame_centralScalar`:
`centralScalar x` is a unitary similitude, and a frame for c·1 whenever the rational c is the
idelic absolute value of the norm of x to ℚ. -/
lemma centralScalar_mem_GU (x : (𝔸f (QuadField d₀))ˣ) :
    centralScalar x ∈ GU E n ∧
    ∀ c : ℚ,
      c = finIdeleAbs (x.map (adeleNorm ℚ (QuadField d₀))) →
      IsScalarFrame (centralScalar x : GL n (𝔸f E)) c :=
  ⟨mem_GU_centralScalar x, fun _ hc ↦ isScalarFrame_centralScalar x hc⟩

/-- The Hecke element `τ_{w,j} = heckeSum n k w j` is a combination of the elements
`invHeckeIsogeny w U`. -/
lemma heckeSum_mem_spanOn {j : ℕ} : heckeSum n k w j ∈ spanOn k (range (invHeckeIsogeny w)) :=
  sum_mem fun U _ ↦ Submodule.subset_span ⟨invHeckeIsogeny w U, ⟨U, rfl⟩, rfl⟩

/-- Let `x` be a unit of the completion at `w`, and let `u` be a place whose restriction to `K₀` is
not the conjugate of that of `w`. Then the `u`-component of the scalar matrix `centralScalar` of
the norm of the local idele of `x` is `1`. -/
lemma evalAt_centralScalar_of_ne {w u : FinPlace E}
    (h_below : u.below (QuadField d₀) ≠ star (w.below (QuadField d₀))) (x : (LocField w)ˣ) :
    (centralScalar (n := n) ((locIdele w x).map (adeleNorm (QuadField d₀) E))).map
      (evalAt u) = 1 := by
  -- The norm of a local idele is local at `w.below _`. Since `centralScalar` conjugates, the value
  -- is read at `star u`, which does not lie above that place.
  ext1
  simp (disch :=
    grind [below_star, star_star]) [adeleNorm_locIdele, adeleMap_apply _ rfl, starRingEnd_apply]

/-- The matrix of the inverse of `centralScalar x` is the scalar matrix of the conjugate of
`x⁻¹`. -/
private lemma val_inv_centralScalar (x : (𝔸f (QuadField d₀))ˣ) :
    (((centralScalar (n := n) x)⁻¹ : GL n (𝔸f E)) : Matrix n n (𝔸f E)) =
      diagonal fun _ : n ↦
        starRingEnd (𝔸f E) (finAdeleIncl (QuadField d₀) E ((x⁻¹ : (𝔸f (QuadField d₀))ˣ) : 𝔸f _)) :=
  rfl

private lemma val_inv_conjAtSplit (g : GL n (LocField (w : FinPlace E))) :
    (((conjAtSplit w g)⁻¹ : GL n (𝔸f E)) : Matrix n n (𝔸f E)) =
      ((singleGL (w : FinPlace E) g : Matrix n n (𝔸f E)) *
        star (singleGL (w : FinPlace E) g⁻¹ : Matrix n n (𝔸f E)))ᵀ :=
  rfl

/-- For a split finite place w of E and a subspace U of k_wⁿ of dimension r, where k_w is the
residue field at w, the matrix `invHeckeIsogeny w U` lies in `GUPlus E n`: it is a similitude whose
inverse has integral entries. This matrix is the scalar matrix of the conjugate of the (−r)-th power
of `uniformizerNorm w`, the norm to K₀ of the idele that is a uniformiser at w and 1 elsewhere,
times `conjAtSplit w` of the transpose of `basicCosetRep U`, an integral matrix at w whose
determinant has order r. -/
lemma invHeckeIsogeny_mem_GUPlus (w : SplitFinPlace E)
    (U : Submodule (ResField (w : FinPlace E)) (n → ResField (w : FinPlace E))) :
    invHeckeIsogeny w U ∈ GUPlus E n := by
  -- Put `D = (basicCosetRep U)ᵀ` and `q = uniformizerNorm w`. The inverse of `invHeckeIsogeny w U`
  -- is the transpose of the product of `singleGL w D` and the conjugate transpose of
  -- `q ^ dim U • singleGL w D⁻¹`; both are integral.
  obtain ⟨h_int, -, h_det⟩ := (basicCosetRep_mem_and_residueKer_eq U).left
  have h_mul_locGL_mem (g : GL n (LocField w.1)) (a : 𝔸f E) (ha : a ∈ Ô E)
      (hg : ∀ i j : n, v (a w * g i j) ≤ 1) (i j : n) :
      a * singleGL _ g i j ∈ Ô E := by
    rw [mem_Ô, ← and_forall_ne w.1]
    by_cases h_ij : i = j <;> simp_all [singleGL, mem_Ô]
  -- `q` is integral, and its image in the adeles of `E` is not a unit at `w`.
  have h_loc_mem : ((locIdele w.1 (uniformizer w.1) : (𝔸f E)ˣ) : 𝔸f E) ∈ Ô E := by
    simp +decide +contextual [mem_Ô, ← and_forall_ne w.1]
  have hq_int : (uniformizerNorm w).val ∈ Ô (QuadField d₀) := adeleNorm_mem_Ô h_loc_mem
  have hq_lt : v (finAdeleIncl (QuadField d₀) E (uniformizerNorm w).val w) < 1 := by
    -- `erw`: `norm_localNorm` meets `uniformizerNorm w` at the place below `w` only by unfolding
    -- `uniformizerNorm` and the local idele.
    erw [(isEquiv_comap_locMap _ rfl).lt_one_iff_lt_one, ← toNormedField.norm_lt_one_iff,
      norm_localNorm]
    simp +decide
  -- `D⁻¹ = (det D)⁻¹ • adjugate D`, and `q ^ dim U` absorbs `det D`, of order `dim U` at `w`.
  have h_inv (i j : n) :
      v (finAdeleIncl (QuadField d₀) E ((uniformizerNorm w).1 ^ finrank (ResField w.1) U) w *
        (transposeGL (basicCosetRep U))⁻¹ i j) ≤ 1 := by
    have h_adj : v ((basicCosetRep U).1ᵀ.adjugate i j) ≤ 1 :=
      (IsIntMatrix.transpose (R := (LocInt _).1) h_int).adjugate i j
    have h_pow := pow_le_one' (v_uniformizer_inv_mul_le_one_iff.2 hq_lt) (finrank (ResField w.1) U)
    simpa [mul_comm (exp _), inv_def, h_det, mul_pow, mul_assoc] using mul_le_one' h_pow h_adj
  refine ⟨mul_mem (mem_GU_centralScalar _) (conjAtSplit_mem_GU _), ?_⟩
  unfold invHeckeIsogeny
  -- write the inverse as the transpose of `singleGL w D * (q ^ dim U • singleGL w D⁻¹)ᴴ`
  rw [_root_.mul_inv_rev, Units.val_mul, val_inv_centralScalar, ← smul_eq_mul_diagonal,
    val_inv_conjAtSplit, ← transpose_smul, ← mul_smul_comm, starRingEnd_apply, ← star_smul]
  refine IsIntMatrix.transpose (.mul ?_ (.conjTranspose ?_))
  · have h_loc : ∀ i j : n,
        (singleGL _ (transposeGL (basicCosetRep U)) : Matrix n n (𝔸f E)) i j ∈ Ô E := by
      simpa [h_int] using h_mul_locGL_mem (transposeGL (basicCosetRep U)) 1
    exact h_loc
  · exact h_mul_locGL_mem _ _ ((adeleMap_mem_Ô _).2 (pow_mem hq_int _)) h_inv

/-- Let `x` be fixed by the level K(𝔑), and let `w` be the safe place of the pair `s = (w, j)`. Then
`x` is fixed by GL_n(O_w) (`New.localIntGL`), acting through `New.Variety.conjAtSplit w`. -/
lemma SafePlace.mem_levelSpace_conjAtSplit (hx : x ∈ levelSpace π (levelGU n 𝔑)) :
    x ∈ levelSpace (π.comp (conjAtSplit s.1)) (localIntGL n (s.1.val : FinPlace E)) := by
  intro a
  -- `conjAtSplit _ a` is a unitary similitude with integral entries, and it is `1` at every place
  -- dividing `𝔑`, which is neither the safe place nor its conjugate.
  have h_int : conjAtSplit s.1 a ∈ intGL n (Ô E) := conjAtSplit_mem_intGL_iff.mpr a.prop
  have h_one (u : FinPlace E) (hu : 𝔑 ∈ u.asIdeal) :
      (conjAtSplit s.1 a).map (evalAt u) = (1 : GL n (𝔸f E)).map (evalAt u) := by
    simp (disch := grind [IsSafe, below_star, star_star]) [evalAt_conjAtSplit_of_ne]
  exact hx ⟨_, mem_levelGU_of_map_evalAt_eq (conjAtSplit_mem_GU _) h_int
    fun u hu ↦ ⟨1, one_mem _, h_one u hu⟩⟩

/-- Let `s = (w, j)` with `w` a safe place, and let `x` be fixed by K(𝔑) in the representation `π`.
Then τ_{w,j} sends `x` to the j-th Hecke operator of GL_n(E_w) (acting through
`conjAtSplit w`) applied to `x`, followed by the central scalar of the inverse of
`New.Variety.uniformizerNorm w ^ j`. -/
lemma asAlgebraHom_heckeSum (h : x ∈ levelSpace π (levelGU n 𝔑)) :
    π.asAlgebraHom (heckeSum n k s.1 s.2) x =
      π (centralScalar (uniformizerNorm s.1.val ^ s.2)⁻¹)
        (heckeGL (π.comp (conjAtSplit s.1)) s.2 x) := by
  -- Both sides are sums over the subspaces `U` of dimension `s.2`, and they agree term by term:
  -- in each term of τ the power of the uniformiser's norm is `finrank U`, that is `s.2`.
  have h_sum : heckeSum n k s.1 s.2 =
      ∑ U ∈ {U : Submodule (ResField (s.1.val : FinPlace E)) (n → ResField (s.1.val : FinPlace E)) |
          finrank (ResField (s.1.val : FinPlace E)) U = s.2},
        MonoidAlgebra.of k (GL n (𝔸f E)) (centralScalar (uniformizerNorm s.1.val ^ s.2)⁻¹ *
          conjAtSplit s.1 (transposeGL (basicCosetRep U))) :=
    Finset.sum_congr rfl fun U hU ↦ by rw [invHeckeIsogeny, (Finset.mem_filter.mp hU).right]
  simp [h_sum, heckeGL_eq_sum (SafePlace.mem_levelSpace_conjAtSplit s h)]

/-- For `s = (w, j)` with `w` a safe place, τ_{w,j} lies in the Hecke algebra of the level K(𝔑). -/
lemma heckeSum_mem_heckeAlgebra : heckeSum n k s.1 s.2 ∈ heckeAlgebra n k 𝔑 := by
  -- the level is prime to the conjugate of the safe place
  obtain ⟨-, -, h_conj_prime⟩ := s.1.prop
  have h_notMem : 𝔑 ∉ (star (s.1.val : FinPlace E)).asIdeal := h_conj_prime _ (below_star _)
  -- the last argument is membership in `fixedToEigen`: for every representation `π` on a module
  -- `W` and every `y` fixed by K(𝔑), `τ y` is fixed by the preimage of K(𝔑) under `conjAtSplit`
  refine mem_heckeAlgebra_of_mem_fixedToEigen h_notMem heckeSum_mem_spanOn ?_ fun W _ _ π y hy a ↦
    ?_
  · -- The terms of `τ` are a central element times an element in the image of `conjAtSplit`.
    rintro _ ⟨U, rfl⟩
    refine ⟨invHeckeIsogeny_mem_GUPlus _ U, fun d hd ↦ ?_⟩
    rw [invHeckeIsogeny]
    exact (commute_scalar_GL _ d).mul_right (hd _)
  · -- `τ y` is a central translate of a Hecke operator applied to `y`, and the latter vector is
    -- fixed by `localIntGL`.
    have h_sph : heckeGL (π.comp (conjAtSplit s.1)) s.2 y ∈
        levelSpace (π.comp (conjAtSplit s.1)) (localIntGL n _) :=
      (isHeckeFunction_basicDoubleCoset _).heckeFun_mem (SafePlace.mem_levelSpace_conjAtSplit s hy)
    -- `a` maps into the level, so it is integral at the safe place
    have h_a_int : conjAtSplit s.1 a ∈ intGL n (Ô E) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp a.prop)).right.left
    rw [asAlgebraHom_heckeSum s hy]
    refine map_mem_levelSpace_of_commute h_sph (fun κ ↦ ?_)
      ⟨a, conjAtSplit_mem_intGL_iff.mp h_a_int⟩
    -- the central element commutes with the image of `conjAtSplit`
    simp [commute_scalar_GL, Commute.map]

/-- For s = (w, j), with w a safe split place and j a natural number, the element τ_{w,j} as a
member of the Hecke algebra of level K(𝔑) over k. The pair is one argument so that words in
these elements are lists. -/
def tauHecke : heckeAlgebra n k 𝔑 := ⟨heckeSum n k s.1 s.2, heckeSum_mem_heckeAlgebra s⟩

/-- The element τ_{w,j} of the Hecke algebra keeps the vectors fixed by K(𝔑). -/
lemma asAlgebraHom_tauHecke_mem_levelSpace (h : x ∈ levelSpace π (levelGU n 𝔑)) :
    π.asAlgebraHom (tauHecke s).val x ∈ levelSpace π (levelGU n 𝔑) :=
  (heckeSum_mem_heckeAlgebra s).right h

/-- Let π be a representation of GL_n(𝔸f E) on the k-module W, and let s = (w, j) and s' be pairs of
a split place of E that is safe for the level 𝔑 (`SafePlace 𝔑`) and a natural number. The Hecke
elements τ_{w,j} = `tauHecke s` and `tauHecke s'` of level K(𝔑) over k then act through π by
commuting operators on any vector `x` fixed by K(𝔑) = `levelGU n 𝔑`, the similitudes in GL_n(Ô_E)
congruent to 1 modulo 𝔑. -/
lemma asAlgebraHom_tauHecke_comm (h : x ∈ levelSpace π (levelGU n 𝔑)) :
    π.asAlgebraHom (tauHecke s).val (π.asAlgebraHom (tauHecke s').val x) =
      π.asAlgebraHom (tauHecke s').val (π.asAlgebraHom (tauHecke s).val x) := by
  -- By `asAlgebraHom_heckeSum`, τ_{w,j} is a central element `z w j` times a Hecke operator
  -- `H w j`.
  let z (w : SafePlace 𝔑) (j : ℕ) : GL n (𝔸f E) := centralScalar (uniformizerNorm w.val ^ j)⁻¹
  let H (w : SafePlace 𝔑) (j : ℕ) (y : W) : W := heckeGL (π.comp (conjAtSplit w.val)) j y
  have h_central (w : SafePlace 𝔑) (j : ℕ) (g : GL n (𝔸f E)) (y : W) :
      π (z w j) (π g y) = π g (π (z w j) y) :=
    LinearMap.congr_fun ((commute_scalar_GL _ g).symm.map π).eq y
  -- The inner central element moves out of the outer Hecke operator.
  have h_prod (w : SafePlace 𝔑) (i : ℕ) (w' : SafePlace 𝔑) (j : ℕ) :
      π.asAlgebraHom (tauHecke (w, i)).val (π.asAlgebraHom (tauHecke (w', j)).val x) =
        π (z w i) (π (z w' j) (H w i (H w' j x))) :=
    calc
      _ = π (z w i) (H w i (π.asAlgebraHom (tauHecke (w', j)).val x)) :=
        asAlgebraHom_heckeSum (w, i) (asAlgebraHom_tauHecke_mem_levelSpace (w', j) h)
      _ = π (z w i) (H w i (π (z w' j) (H w' j x))) :=
        congrArg (fun y ↦ π (z w i) (H w i y)) (asAlgebraHom_heckeSum (w', j) h)
      _ = π (z w i) (π (z w' j) (H w i (H w' j x))) :=
        congrArg (π (z w i)) (map_heckeFun (π := π.comp (conjAtSplit w.val)) (π (z w' j))
          (by simp) fun g ↦ h_central w' j (conjAtSplit w.val g) (H w' j x)).symm
  -- Through the inverse transpose, `π` is a representation of the unitary group in which `x` is
  -- spherical at every safe place; there the Hecke operators commute.
  let ρ : Representation k (Gf E n) W := π.comp (invTransposeGL.toMonoidHom.comp (U 1).subtype)
  have h_sph (w : SafePlace 𝔑) : x ∈ sphericalAt ρ (w.val : FinPlace E) :=
    (mem_sphericalAt_iff w.val.property).mpr (SafePlace.mem_levelSpace_conjAtSplit (w, 0) h)
  obtain ⟨⟨w, i⟩, w', j⟩ := s, s'
  have h_comm : H w i (H w' j x) = H w' j (H w i x) :=
    heckeSplit_comm w.val.property w'.val.property i j (h_sph w) (h_sph w')
  rw [h_prod, h_prod, h_comm, h_central]

end

open LinearMap Submodule

variable {E : Type} [Field E] [CMBase E] {n : Type} [Fintype n] [DecidableEq n] {𝔑 : 𝓞 E} {d₀ : ℕ}
  [HasQuadSubfield d₀ E] {k : Type} [CommRing k] {ν : ℕ} {R : Subalgebra (𝓞 E) E}
  (T : Model n d₀ 𝔑 ν R)
  (F : (Over (AlgebraicGeometry.Spec (CommRingCat.of R)))ᵒᵖ ⥤ ModuleCat.{2} k)

/-- For a contravariant functor F to k-modules, the pull-back F(Z) → F(W_i) along the leg of level
`i` at the coset `q`. -/
def Model.legPullback (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n))
    (q : GL n (𝔸f E) ⧸ levelGU n 𝔑) : F.obj (Opposite.op T.base) →ₗ[k] F.obj
      (Opposite.op (T.cover i)) :=
  (F.map (T.leg i q).op).hom

/-- The operators t(w, j) on F(Z), indexed by a safe place w and a natural number j, are the action
of the Hecke elements τ_{w,j}, read on the level `I w`. -/
structure Model.IsHeckeAction (I : SafePlace 𝔑 → Finset (nonZeroDivisors (𝓞 E) × GUPlus E n))
    (t : SafePlace 𝔑 × ℕ → Module.End k (F.obj (Opposite.op T.base))) : Prop where
  /-- The operators commute. -/
  commute (s s' : SafePlace 𝔑 × ℕ) : Commute (t s) (t s')
  /-- Pulled back to the level `I w`, t(w, j) is the sum of the legs over τ_{w,j}. -/
  legPullback_comp (w : SafePlace 𝔑) (j : ℕ) :
    T.legPullback F (I w) ⟦1⟧ ∘ₗ t (w, j) = cosetSum (T.legPullback F (I w)) (heckeSum n k w j)
  /-- On deep levels, a word L in the Hecke elements acts as the same word in the operators: for a
  ring k', b ∈ k'[G] supported on `GUPlus E n` and Ψ additive, the sum of Ψ of the legs over
  b · L(τ) is the sum over b of Ψ of the legs composed with L(t). -/
  eventually_cosetSum_mul_prod (k' : Type) [CommRing k'] (L : List (SafePlace 𝔑 × ℕ))
      {b : MonoidAlgebra k' (GL n (𝔸f E))} (hb : b ∈ spanOn k' (GUPlus E n)) :
    ∀ᶠ i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n) in Filter.atTop,
      ∀ {N : Type 2} [AddCommGroup N] [Module k' N]
      (Ψ : (F.obj (Opposite.op T.base) →ₗ[k] F.obj (Opposite.op (T.cover i))) →+ N),
      cosetSum (fun q : GL n (𝔸f E) ⧸ levelGU n 𝔑 ↦ Ψ (T.legPullback F i q))
        (b * (L.map tauHecke).prod.val) =
        cosetSum (fun q : GL n (𝔸f E) ⧸ levelGU n 𝔑 ↦ Ψ (T.legPullback F i q ∘ₗ (L.map t).prod)) b

variable {T : Model n d₀ 𝔑 ν R}
  {F : (Over (AlgebraicGeometry.Spec (CommRingCat.of R)))ᵒᵖ ⥤ ModuleCat.{2} k}

/-- Suppose the level `I w` has legs for all `invHeckeIsogeny w U`, and each t(w, j), pulled back to
the level `I w`, is the sum of the legs over τ_{w,j} (`cosetSum`: the legs at the cosets of the
terms of τ_{w,j}, weighted by their coefficients). Then on deep levels a word in the Hecke elements
acts as the same word in the operators t. -/
lemma Model.eventually_cosetSum_mul_prod_of_legPullback_comp
    {I : SafePlace 𝔑 → Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)}
    (hI : ∀ (w : SafePlace 𝔑) (U : Submodule (ResField (w.val : FinPlace E))
      (n → ResField (w.val : FinPlace E))), invHeckeIsogeny w.val U ∈ T.legIndices (I w))
    {t : SafePlace 𝔑 × ℕ → Module.End k (F.obj (Opposite.op T.base))}
    (ht : ∀ (w : SafePlace 𝔑) (j : ℕ),
      T.legPullback F (I w) ⟦1⟧ ∘ₗ t (w, j) = cosetSum (T.legPullback F (I w)) (heckeSum n k w j))
    (k' : Type) [CommRing k'] (L : List (SafePlace 𝔑 × ℕ))
    {b : MonoidAlgebra k' (GL n (𝔸f E))} (hb : b ∈ spanOn k' (GUPlus E n)) :
    ∀ᶠ i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n) in Filter.atTop,
      ∀ {N : Type 2} [AddCommGroup N] [Module k' N]
      (Ψ : (F.obj (Opposite.op T.base) →ₗ[k] F.obj (Opposite.op (T.cover i))) →+ N),
      cosetSum (fun q : GL n (𝔸f E) ⧸ levelGU n 𝔑 ↦ Ψ (T.legPullback F i q))
        (b * (L.map tauHecke).prod.val) =
        cosetSum (fun q ↦ Ψ (T.legPullback F i q ∘ₗ (L.map t).prod)) b := by
  -- Induction on the word `L`; for its first letter, induction on `b` in the span. For a single
  -- element `g`, a deep level has a map `f` that translates the legs by `g`
  -- (`eventually_translate`), and pulling `ht` back along `f` removes the letter.
  induction L generalizing b with
  | nil => simp [End.one_eq_id]
  | cons s L ih =>
    obtain ⟨w, j⟩ := s
    induction hb using span_induction with
    | zero => simp [cosetSum, cosetFn]
    | add b b' _ _ hb hb' =>
      filter_upwards [hb, hb'] with i h_b h_b' N _ _ Ψ
      -- both sides are additive in `b`: add the two cases
      simpa [add_mul, cosetSum, cosetFn] using congrArg₂ (· + ·) (h_b Ψ) (h_b' Ψ)
    | smul c b _ hb =>
      filter_upwards [hb] with i h_b N _ _ Ψ
      -- both sides are linear in `b`: scale the case of `b` by `c`
      simpa [cosetSum, cosetFn] using congrArg (c • ·) (h_b Ψ)
    | mem b hb =>
      have h_supp : b * (tauHecke (w, j)).val ∈ spanOn k' (GUPlus E n) :=
        spanOn.mul (subset_span hb) (heckeSum_mem_heckeAlgebra (w, j)).left
          fun g₁ hg₁ g₂ hg₂ ↦ mul_mem hg₁ hg₂
      obtain ⟨g, hg, rfl⟩ := hb
      filter_upwards [ih h_supp, T.eventually_translate (I w) hg] with i h_ih ⟨hg_s, f, hf⟩ N _ _ Ψ
      -- On a deep level, `f` translates the legs by `g`; pull `ht w j` back along `f`.
      have h_leg :
          ∑ U ∈ {U : Submodule (ResField (w.val : FinPlace E)) (n → ResField (w.val : FinPlace E)) |
              finrank (ResField (w.val : FinPlace E)) U = j},
            T.legPullback F i ↑(g * invHeckeIsogeny w.val U) ∘ₗ (L.map t).prod =
              T.legPullback F i g ∘ₗ (t (w, j) * (L.map t).prod) := by
        -- apply `F.map f.op` to `ht w j` at `(L.map t).prod y`
        ext y
        have h_apply := LinearMap.congr_fun (ht w j) ((L.map t).prod y)
        simpa [← F.map_comp_apply, ← op_comp, legPullback, hf, hI, T.one_mem, cosetSum, cosetFn,
          heckeSum] using congrArg (F.map f.op) h_apply.symm
      -- Remove the word `L` by `h_ih`; what is left is the sum over `g * tauHecke (w, j)`.
      calc
        _ = cosetSum (fun q ↦ Ψ (T.legPullback F i q)) (MonoidAlgebra.of k' (GL n (𝔸f E)) g *
              (tauHecke (w, j)).val * (L.map tauHecke).prod.val) := by simp [cosetSum, cosetFn]
        _ = cosetSum (fun q ↦ Ψ (T.legPullback F i q ∘ₗ (L.map t).prod))
              (MonoidAlgebra.of k' (GL n (𝔸f E)) g * (tauHecke (w, j)).val) := h_ih Ψ
        _ = cosetSum (fun q ↦ Ψ (T.legPullback F i q ∘ₗ (((w, j) :: L).map t).prod))
              (MonoidAlgebra.of k' (GL n (𝔸f E)) g) := by
          simpa [tauHecke, cosetSum, cosetFn, heckeSum] using congrArg Ψ h_leg

/-! ### The operators on the base of a model -/

/-- Let `T` be a model of the Kuga–Sato tower over `R`, with base Z = `T.base`, schemes
W_i = `T.cover i` over levels `i`, legs W_i → Z and finite deck groups Δ_i = `T.deckGroup i`, and
let F be a contravariant functor to k-modules. Suppose each pull-back along the leg of 1 is
injective with image containing the Δ_i-invariants, and that for every safe place w and subspace U
of the residue-field space, `invHeckeIsogeny w U` lies in `T.legIndices (I w)`, the set of matrices
g whose legs p_g at level `I w` the fields of `T` speak about. Then the Hecke elements act on F(Z)
by commuting operators, in the sense of `New.Variety.Model.IsHeckeAction`.

Known result: Hecke algebra of a pair and its action by correspondences on the base of a tower. -/
lemma Model.exists_isHeckeAction
    (h_inj : ∀ i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n),
      Function.Injective (T.legPullback F i ⟦1⟧))
    (h_descent : ∀ (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E n))
      (y : F.obj (Opposite.op (T.cover i))),
      (∀ δ : T.deckGroup i, F.map (T.deck i δ).asHom.op y = y) → y ∈ (T.legPullback F i ⟦1⟧).range)
    {I : SafePlace 𝔑 → Finset (nonZeroDivisors (𝓞 E) × GUPlus E n)}
    (hI : ∀ (w : SafePlace 𝔑) (U : Submodule (ResField (w.val : FinPlace E))
      (n → ResField (w.val : FinPlace E))), invHeckeIsogeny w.val U ∈ T.legIndices (I w)) :
    ∃ t : SafePlace 𝔑 × ℕ → Module.End k (F.obj (Opposite.op T.base)), T.IsHeckeAction F I t := by
  -- The sum of the legs over τ_{w,j} is invariant under the deck group, since the function of
  -- τ_{w,j} on the cosets is left invariant under the level. So it factors through the injective
  -- pull-back along the leg of 1, and this defines t(w, j).
  have exists_t (w : SafePlace 𝔑) (j : ℕ) : ∃ t : Module.End k (F.obj (Opposite.op T.base)),
      T.legPullback F (I w) ⟦1⟧ ∘ₗ t = cosetSum (T.legPullback F (I w)) (heckeSum n k w j) := by
    refine ⟨_, codRestrictOfInjective_comp _ _ (h_inj _) fun x ↦ h_descent _ _ fun δ ↦ ?_⟩
    -- `δ` moves the leg at `q` to the leg at `κ * q`, for some `κ` in the level.
    obtain ⟨κ, hδ⟩ := T.deck_comp_leg (I w) δ
    -- The image `a` of τ_{w,j} in the permutation module on the cosets is fixed by `κ`.
    let ρ := Representation.ofMulAction k (GL n (𝔸f E)) (GL n (𝔸f E) ⧸ levelGU n 𝔑)
    let a : MonoidAlgebra k (GL n (𝔸f E) ⧸ levelGU n 𝔑) :=
      ρ.asAlgebraHom (heckeSum n k w j) (MonoidAlgebra.single ⟦1⟧ 1)
    have h_fixed : ρ κ a = a :=
      (asAlgebraHom_tauHecke_mem_levelSpace (w, j) single_one_mem_levelSpace κ).trans (one_smul k a)
    -- sum the legs against the coefficients of `ρ κ a = a`
    simpa [ρ, a, ← F.map_comp_apply, ← op_comp, legPullback, hδ, hI, cosetSum, cosetFn, heckeSum]
      using congrArg (fun b ↦ Finsupp.linearCombination k (T.legPullback F (I w)) b.coeff x) h_fixed
  choose t₀ ht using exists_t
  let t (s : SafePlace 𝔑 × ℕ) : Module.End k (F.obj (Opposite.op T.base)) := t₀ s.1 s.2
  have h_word := eventually_cosetSum_mul_prod_of_legPullback_comp (t := t) hI ht
  refine ⟨t, fun s s' ↦ ?_, ht, h_word⟩
  -- Commutation: on a deep level, a word of two letters at `b = 1` computes a product `t a * t b`,
  -- and the two products of `tauHecke` act alike on the trivial coset.
  have h_deep (a b : SafePlace 𝔑 × ℕ) : ∀ᶠ i in Filter.atTop, T.legPullback F i ⟦1⟧ ∘ₗ (t a * t b) =
      cosetSum (T.legPullback F i) (tauHecke a * tauHecke b : heckeAlgebra n k 𝔑).val := by
    filter_upwards [h_word k [a, b] (b := 1) (subset_span ⟨1, (GUPlus E n).one_mem, rfl⟩)]
      with i hi
    simpa [cosetSum, cosetFn] using (hi (AddMonoidHom.id _)).symm
  obtain ⟨i, h_left, h_right⟩ := ((h_deep s s').and (h_deep s' s)).exists
  refine (cancel_left (h_inj i)).mp ?_
  rw [h_left, h_right]
  -- `↓`: the fixed coset vector must be recognised before `cosetSum` unfolds around it
  simp [asAlgebraHom_tauHecke_comm s, ↓single_one_mem_levelSpace, cosetSum, cosetFn]

end New.Variety

end LocalHecke

/-!
## Adelic torsion and multiplication by integers

Degrees and torsion on the abelian schemes of a family `X : New.ThetaFamily D Z τ`.

`New.ThetaObject X T` is a point `T ⟶ Z` of the base `Z` of the family. For such a point `y`,
`y.groupScheme` is the abelian scheme over `T` pulled back along it, and `𝟙_ _ ⟶ y.groupScheme` is
the group of its sections. `New.AdelicTorsion E n` is the module `(𝔸f E / Ô E)ⁿ`, an adelic model of
`(E / 𝓞 E)ⁿ`.
-/

namespace New

open CategoryTheory AlgebraicGeometry AddSubgroup NumberField Submodule Variety FractionalIdeal
  Module LinearMap Ideal Nat MonoidalCategory

section

variable {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n]

/-- For a non-zero ideal I of O_E, the submodule of (𝔸_f / Ô)ⁿ killed by I has N(I)^|n|
elements, where N(I) is the absolute norm and |n| the size of the index set. -/
lemma card_torsionBySet_adelicTorsion {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) :
    Nat.card (torsionBySet (𝓞 E) (AdelicTorsion E n) I) = I.absNorm ^ Fintype.card n := by
  classical
  -- Under `frameTorsionClass 1 : Eⁿ → AdelicTorsion E n`, onto with kernel `𝓞ⁿ`, the `I`-torsion is
  -- the image of `(I⁻¹)ⁿ`. So it is `(I⁻¹ ⧸ 𝓞)ⁿ`, and `I⁻¹ ⧸ 𝓞 ≃ 𝓞 ⧸ I`.
  let 𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := I
  have h𝔞 : 𝔞 ≠ 0 := coeIdeal_ne_zero.2 hI
  let J : 𝔞⁻¹.coeToSubmodule →ₗ[𝓞 E] E := 𝔞⁻¹.coeToSubmodule.subtype
  have h_comap : (torsionBySet (𝓞 E) (AdelicTorsion E n) I).comap (frameTorsionClass 1) =
      (J.compLeft n).range := by
    -- the class of `y` is killed by `I` iff `c * y i ∈ 𝓞` for all `c ∈ I` and `i`
    ext
    simp_rw [Submodule.mem_comap, mem_torsionBySet_iff, ← map_smul, ← mem_ker]
    simp [ker_frameTorsionClass_one, J, 𝔞, range_compLeft, mem_inv_iff h𝔞, Algebra.smul_def,
      mul_comm, forall_comm (α := n)]
  have h_index : (comap J 1).toAddSubgroup.index = I.absNorm := by
    -- `e : 𝔞⁻¹ ⧸ 1 ≃ 1 ⧸ 𝔞`, since `𝔞⁻¹ * 𝔞 = 1 * 1`
    let A : Submodule (𝓞 E) E := (𝔞⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    let B : Submodule (𝓞 E) E := (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    let C : Submodule (𝓞 E) E := 𝔞
    have e : (↥A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (↥B ⧸ C.comap B.subtype) :=
      quotientEquiv 𝔞⁻¹ 1 1 𝔞 (by simp [h𝔞]) (by simp [𝔞, mem_inv_iff h𝔞]) coeIdeal_le_one
        h𝔞 (inv_ne_zero h𝔞)
    let ι : 𝓞 E →+ E := AddSubgroupClass.subtype (integralClosure ℤ E)
    calc
      _ = (I.toAddSubgroup.map ι).relIndex (.map ι ⊤) := by
        -- `using!`: the index is the cardinality of the quotient only after unfolding
        -- `AddSubgroup.index` and the coercions of the fractional ideals
        simpa [ι, 𝔞, A, B, C] using! card_congr e.toEquiv
      _ = I.toAddSubgroup.relIndex ⊤ := relIndex_map_map_of_injective _ ⊤ Subtype.val_injective
      _ = I.absNorm := relIndex_top_right _
  -- the torsion is `(I⁻¹)ⁿ` modulo the vectors in `𝓞ⁿ`, a subgroup whose index is a product
  calc Nat.card (torsionBySet (𝓞 E) (AdelicTorsion E n) I)
    _ = Nat.card (frameTorsionClass (E := E) (n := n) 1 ∘ₗ J.compLeft n).range := by
      rw [range_comp, ← h_comap, map_comap_eq_of_surjective frameTorsionClass_surjective]
    _ = (AddSubgroup.pi Set.univ fun _ : n ↦ (comap J 1).toAddSubgroup).index := by
      rw [← card_congr (quotKerEquivRange _).toEquiv, ker_comp, ker_frameTorsionClass_one]
      rfl
    _ = I.absNorm ^ Fintype.card n := by simp [index_pi, h_index]

end

variable {E : Type} [Field E] [CMBase E] {D : PEL E} {R : CommRingCat} {Z : Scheme}
  {τ : Z ⟶ Spec (CommRingCat.of (𝓞 E))} {X : ThetaFamily D Z τ} (y : ThetaObject X (Spec R))
  [IsLocalRing R] (x : ThetaObject X (Spec ⟨ℂ⟩))

/-- On the abelian scheme of an object y over a local ring, multiplication by a non-zero element
a of O_E is finite, flat and surjective. -/
lemma ThetaObject.isIsogeny_smul_id {a : 𝓞 E} (ha : a ≠ 0) :
    IsIsogeny (a • 𝟙 y.groupScheme) := by
  -- `a` divides its norm `N ≠ 0`. Multiplication by `N` is quasi-finite and onto, and it factors
  -- through `a` on either side; so `a` is quasi-finite and onto, hence an isogeny.
  let N : ℕ := (span {a}).absNorm
  obtain ⟨c, hc⟩ : ∃ c : 𝓞 E, c * a = N := mem_span_singleton'.mp (span {a}).absNorm_mem
  have hN : N ≠ 0 := by simpa [N]
  have h_comp {b c : 𝓞 E} (h : c * b = N) :
      (N • 𝟙 y.groupScheme).left = (b • 𝟙 y.groupScheme).left ≫ (c • 𝟙 y.groupScheme).left := by
    simp [← Over.comp_left, smul_smul, h, cast_smul_eq_nsmul]
  -- `N` pulls the embedding class back to `N ^ 2` times itself, so its fibres are finite
  have h_fin : LocallyQuasiFinite (N • 𝟙 y.groupScheme).left :=
    locallyQuasiFinite_of_pull_picClass y.isProjEmbedding (pow_ne_zero 2 hN)
      (pull_nsmul_eq_sq_smul y.hasClassLaws.1 N)
  have h_onto : Surjective (N • 𝟙 y.groupScheme).left := IsAbelianScheme.nsmul_surjective N hN
  rw [h_comp hc] at h_fin
  rw [h_comp ((mul_comm a c).trans hc)] at h_onto
  exact isIsogeny_of_locallyQuasiFinite _ (.of_comp _ (c • 𝟙 y.groupScheme).left)
    (.of_comp (c • 𝟙 y.groupScheme).left _)

/-- Let A be the abelian variety of an object of the family over ℂ. Every injective O_E-linear map
from `New.AdelicTorsion E D.Index` to A(ℂ) has all torsion points of A(ℂ) in its image. -/
lemma ThetaObject.exists_apply_eq_of_torsion
    {f : AdelicTorsion E D.Index →ₗ[𝓞 E] 𝟙_ (Over (Spec (CommRingCat.of ℂ))) ⟶ x.groupScheme}
    (hf : Function.Injective f) (y : 𝟙_ (Over (Spec (CommRingCat.of ℂ))) ⟶ x.groupScheme)
    (hy_torsion : ∃ m : ℕ, m ≠ 0 ∧ m • y = 0) : ∃ l : AdelicTorsion E D.Index, f l = y := by
  -- `f` embeds the `m`-torsion of `AdelicTorsion E D.Index` into the `m`-torsion `T` of
  -- `x.groupScheme`; both have `m ^ (2 * abelianDim E D.Index)` elements.
  obtain ⟨m, hm, hy⟩ := hy_torsion
  let T : Type _ := {z : 𝟙_ _ ⟶ x.groupScheme // m • z = 0}
  have h_card : Nat.card T = m ^ (finrank ℂ (Fin (abelianDim E D.Index) → ℂ) * 2) :=
    (x.isProjEmbedding.nonempty_uniformisation x.smoothOfRelativeDimension).some.card_torsion hm
  have h_finite : Finite T := finite_of_card_ne_zero (h_card.trans_ne (pow_ne_zero _ hm))
  let I : Ideal (𝓞 E) := span {↑m}
  have h_maps (l : AdelicTorsion E D.Index)
      (hl : l ∈ torsionBySet (𝓞 E) (AdelicTorsion E D.Index) I) : m • f l = 0 := by
    simp_all [I, ← map_nsmul, cast_smul_eq_nsmul]
  have h_eq : Nat.card T = Nat.card (torsionBySet (𝓞 E) (AdelicTorsion E D.Index) I) := by
    -- the norm of `m` is `m ^ [E : ℚ]`, and `[E : ℚ]` is twice the number of infinite places
    rw [h_card, card_torsionBySet_adelicTorsion (by simpa [I]), absNorm_span_natCast,
      finrank_fin_fun, RingOfIntegers.rank, finrank_eq_two_mul_card_infinitePlace, abelianDim]
    ring
  have h_bij := (Subtype.map_injective h_maps hf).bijective_of_nat_card_le h_eq.le
  obtain ⟨l, hl⟩ := h_bij.surjective ⟨y, hy⟩
  exact ⟨l, congrArg Subtype.val hl⟩

end New

/-! ## Levels for finitely many isogenies, torsion classes and finite index -/

section TowerLevels

open NumberField Subgroup Submodule nonZeroDivisors

namespace New.Variety

variable {E n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] [DecidableEq n] {𝔑 : 𝓞 E}
  (𝔪 : (𝓞 E)⁰)

@[simp]
lemma levelGU_inf_one : levelGU n 𝔑 ⊓ levelGU n 1 = levelGU n 𝔑 :=
  -- No place divides the level `1`, so the local condition is empty.
  inf_eq_left.mpr fun _ hg ↦ mem_levelGU_of_map_evalAt_eq (Subgroup.mem_inf.mp hg).left
    (Subgroup.mem_inf.mp hg).right.left fun w hw ↦ (w.isPrime.one_notMem hw).elim

open scoped Classical in
/-- Let `𝔑 ≠ 0` and let `s` be a finite set of pairs `(𝔞, g)` of a nonzero integer of `E` and a
similitude in `New.Variety.GUPlus`. There is a level `m` with `g⁻¹ K(m) g ⊆ K(𝔑) ∩ K(𝔞)` for all
`(𝔞, g)` in `s` and for the pairs `(1, 1)` and `(m, 1)`. -/
lemma exists_level_conj_mem (h𝔑 : 𝔑 ≠ 0) (s : Finset ((𝓞 E)⁰ × GUPlus E n)) :
    ∃ m : (𝓞 E)⁰, ∀ x ∈ insert (m, 1) (insert 1 s), ∀ k ∈ levelGU n (m : 𝓞 E),
      (x.2 : GL n (𝔸f E))⁻¹ * k * x.2 ∈ levelGU n 𝔑 ⊓ levelGU n x.1 := by
  -- Each condition on `k` is open and holds at `k = 1`, so the finitely many of them hold on a
  -- congruence subgroup of some non-zero integer level `M`.
  let C (a : 𝓞 E) : Subgroup (GL n (𝔸f E)) := congruenceGL (Ô E ∙ algebraMap _ _ a) id
  have h_near : ∀ᶠ k : GL n (𝔸f E) in nhds 1,
      ∀ x ∈ insert 1 s, (x.2 : GL n (𝔸f E))⁻¹ * k * x.2 ∈ C 𝔑 ⊓ C x.1 := by
    refine (insert 1 s).eventually_all.mpr fun x _ ↦ ContinuousAt.preimage_mem_nhds (by fun_prop) ?_
    exact ((isOpen_congruenceGL_span h𝔑).inter (isOpen_congruenceGL_span (by simp))).mem_nhds
      (by simp)
  obtain ⟨M, hM, h_level⟩ := exists_congruenceGL_subset h_near
  have h_conj : ∀ x ∈ insert 1 s, ∀ k ∈ levelGU n (M : 𝓞 E),
      (x.2 : GL n (𝔸f E))⁻¹ * k * x.2 ∈ levelGU n 𝔑 ⊓ levelGU n x.1 := by
    rintro x hx k ⟨hk_GU, hk_cong⟩
    -- the similitude `x.2` lies in `GU E n`, and so does the conjugate of `k` by it
    have hx_GU : (x.2 : GL n (𝔸f E)) ∈ GU E n := x.2.prop.left
    refine and_and_left.mp ⟨?_, h_level k (by simpa using hk_cong) x hx⟩
    exact (GU E n).mul_mem (mul_mem (inv_mem hx_GU) hk_GU) hx_GU
  refine ⟨⟨M, by simpa⟩, (Finset.forall_mem_insert ..).mpr ⟨fun k hk ↦ ?_, h_conj⟩⟩
  -- The pair `(M, 1)` asks only for `levelGU n M ≤ levelGU n 𝔑`, the case of the pair `1`.
  simpa [hk] using (Subgroup.mem_inf.mp (h_conj 1 (Finset.mem_insert_self 1 s) k hk)).left

/-- For a non-zero element 𝔪 of O_E, the set of non-zero elements of (𝔸_f / Ô)ⁿ ≅ (E / O_E)ⁿ
killed by 𝔪. -/
abbrev NonzeroTorsion (n : Type) : Type := {s : torsionBy (𝓞 E) (AdelicTorsion E n) 𝔪.val // s ≠ 0}

/-- For a non-zero element 𝔪 of O_E, the 𝔪-torsion of (𝔸_f / Ô)ⁿ is finite. -/
instance finite_torsionBy : Finite (torsionBy (𝓞 E) (AdelicTorsion E n) 𝔪.1) := by
  apply Nat.finite_of_card_ne_zero
  rw [← torsionBySet_span_singleton_eq, card_torsionBySet_adelicTorsion (by simp)]
  simp

/-- For non-zero 𝔪, the level K(𝔪) ∩ K(𝔑) has finite index in K(𝔑). -/
instance : ((levelGU n 𝔪).subgroupOf (levelGU n 𝔑)).FiniteIndex := by
  -- `levelGU n 𝔪` is the intersection of `GU E n` with a congruence subgroup; treat each.
  refine ⟨relIndex_inf_ne_zero ?_ ?_⟩
  · simp [relIndex_eq_one.mpr, levelGU]
  · -- An open subgroup has finite index in the compact group of integral matrices, which
    -- contains `levelGU n 𝔑`.
    have h_le : levelGU n 𝔑 ≤ intGL n (Ô E) := fun g hg ↦ (Subgroup.mem_inf.mp hg).right.left
    exact mt (relIndex_eq_zero_of_le_right h_le)
      ((isCompact_intGL isCompact_Ô).relIndex_ne_zero (isOpen_congruenceGL_span (by simp)))

end New.Variety

end TowerLevels

end
