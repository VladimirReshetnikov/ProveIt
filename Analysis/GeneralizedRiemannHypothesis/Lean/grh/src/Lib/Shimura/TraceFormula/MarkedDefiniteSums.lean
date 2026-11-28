import Lib.General.Combinatorics
import Lib.General.LinearAlgebra.IdempotentRadical
import Lib.Shimura.HeckeTower.Model
import Lib.Shimura.Transfer.MarkedPairs

/-!
# For a function with a cuspidal type at one place, marked and definite orbit sums agree

* `New.Variety.finsum_orbits_eq_zero_of_free_of_blocks`: a sum over orbits vanishes if it vanishes
  on each block of a partition that the group permutes, with finite support there, and the
  stabiliser of each point where it is non-zero is trivial.
* `New.Variety.finsum_markedTerm_eq_finsum_definiteTerm`: the marked and the definite sums agree for
  every weight; `New.Variety.finsum_countTerm_marked_eq_definite` says this in terms of `countTerm`.

Idea: both sums run over the classes of triples `(xK, y, μ)` under `GL n E`. Classes with
irreducible characteristic polynomial are matched by a change of signs. For a reducible one, an
idempotent at the split place gives a unipotent group, whose orbits cut the triples into blocks;
translation along it multiplies the terms by a value of the character that is not 1, so they sum to
zero on each block.

Notions from other files:
* `New.Variety.MarkedTriple`: triples `(xK, y, μ)` of an adelic coset, an element `y` of `GL n E`
  and an index `μ` of an eigenvalue of `y`.
* `New.Variety.countTerm`: the term `f(x⁻¹ y⁻¹ x K) * u(charpoly y, μ)` of the class of
  `(xK, y, μ)` if `IsSignedFrame x (eigenReflection ε y μ)` holds (the sign condition), else `0`;
  `ε = True` gives the marked count and `ε = False` the definite count.
* `New.Variety.conjAtSplit`: places an element of `GL n` over the completion at a split place `w₀`
  in the adelic similitude group; `New.Variety.dualComponent` is a left inverse.
* `New.Variety.IsRegularHecke`: `f(x⁻¹ y⁻¹ x K) ≠ 0` forces the characteristic polynomial of `y` to
  be separable.
* `New.Variety.IsCuspidalType`: for every idempotent matrix `e ≠ 0, 1`, the character `χ` is
  non-trivial on the elements of `J` in the unipotent group `1 + e M_n (1 - e)`.

## Relation to the literature

Known result: Simple trace formula on a definite group, with vanishing non-elliptic terms. This
file proves the comparison of orbit sums that is used, for unitary similitudes at a neat level, with
Haar integrals replaced by finite sums over cosets. The non-elliptic terms cancel for a regular test
function with a cuspidal type at one split place; the elliptic terms match for n odd.
Source: Dummigan, A simple trace formula for algebraic modular forms, Exp. Math. 22 (2013); Arthur
and Clozel, Simple algebras, base change and the advanced theory of the trace formula (1989), ch. 1
§2, after Deligne and Kazhdan.
-/

open Function NumberField Matrix Polynomial Set MulAction Pointwise Multiplicative

noncomputable section

namespace New.Variety

/-! ### Sums over blocks and cosets -/

section Orbits

variable {Γ X : Type*} [Group Γ] [MulAction Γ X]

lemma orbit_mk_smul (z : Γ) (p : X) : (⟦z • p⟧ : orbitRel.Quotient Γ X) = ⟦p⟧ :=
  Quotient.sound (mem_orbit p z)

/-- Let `Γ` permute the blocks `π p` of a partition of `X`. If the stabiliser of `p` is trivial,
the points of its block that lie in its orbit are as many as the elements of the stabiliser of
the block. -/
lemma card_block_inter_orbit {π : X → Set X} (h_block : ∀ p q : X, p ∈ π q ↔ π p = π q)
    (h_smul : ∀ (z : Γ) (p : X), π (z • p) = z • π p) {p : X} (hp : stabilizer Γ p = ⊥) :
    Nat.card {s ∈ π p | (⟦s⟧ : orbitRel.Quotient Γ X) = ⟦p⟧} = Nat.card (stabilizer Γ (π p)) := by
  have h_inj : Injective fun z : Γ ↦ z • p := fun a b (hab : a • p = b • p) ↦ by
    have h_mem : a⁻¹ * b ∈ stabilizer Γ p := by simp [mul_smul, ← hab]
    rwa [hp, Subgroup.mem_bot, inv_mul_eq_one] at h_mem
  have h_image : (fun z : Γ ↦ z • p) '' stabilizer Γ (π p) =
      {s ∈ π p | (⟦s⟧ : orbitRel.Quotient Γ X) = ⟦p⟧} := by
    refine subset_antisymm ?_ fun s ⟨hs, h_orbit⟩ ↦ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨(h_block _ p).2 ((h_smul z p).trans hz), orbit_mk_smul z p⟩
    · obtain ⟨z, rfl⟩ : s ∈ orbit Γ p := Quotient.exact h_orbit
      exact ⟨z, (h_smul z p).symm.trans ((h_block _ p).1 hs), rfl⟩
  rw [← h_image, Nat.card_image_of_injective h_inj, SetLike.coe_sort_coe]

/-- Let `Γ` permute the blocks `π p` of a partition of `X`. An orbit `a` meets the block of `s` if
and only if the block of the chosen point of `a` is a translate of the block of `s`. -/
lemma mem_image_block_iff {π : X → Set X} (h_block : ∀ p q : X, p ∈ π q ↔ π p = π q)
    (h_smul : ∀ (z : Γ) (p : X), π (z • p) = z • π p) (s : X) (a : orbitRel.Quotient Γ X) :
    a ∈ Quotient.mk (orbitRel Γ X) '' π s ↔ π a.out ∈ orbit Γ (π s) := by
  rw [mem_orbit_symm]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z : Γ, z • (⟦p⟧ : orbitRel.Quotient Γ X).out = p :=
      mem_orbit_symm.1 (Quotient.mk_out (s := orbitRel Γ X) p)
    exact ⟨z, by simpa only [← h_smul, hz] using (h_block p s).1 hp⟩
  · rintro ⟨z, hz⟩
    exact ⟨z • a.out, (h_block _ s).2 ((h_smul z _).trans hz), by simp⟩

/-- Let `Γ` permute the blocks `π p` of a partition of `X`, and let `F` be a function on the orbits.
Suppose that at every point where `F` is not zero the stabiliser is trivial, and that the block of
such a point has finite intersection with the support of `F` and sum zero. Then the sum of `F` over
the orbits is zero. -/
lemma finsum_orbits_eq_zero_of_free_of_blocks {F : orbitRel.Quotient Γ X → ℂ} (π : X → Set X)
    (h_self : ∀ p : X, p ∈ π p) (h_equivariant : ∀ (z : Γ) {p q : X}, p ∈ π q → π (z • p) = z • π q)
    (h_free : ∀ s : X, F ⟦s⟧ ≠ 0 → stabilizer Γ s = ⊥)
    (h_finite : ∀ s : X, F ⟦s⟧ ≠ 0 → (π s ∩ {p : X | F ⟦p⟧ ≠ 0}).Finite)
    (h_sum : ∀ s : X, F ⟦s⟧ ≠ 0 → ∑ᶠ p ∈ π s, F ⟦p⟧ = 0) :
    ∑ᶠ c : orbitRel.Quotient Γ X, F c = 0 := by
  classical
  -- Group the classes `c` by the orbit of the block `π c.out` and show each group sums to zero.
  have h_block (p q : X) : p ∈ π q ↔ π p = π q :=
    ⟨fun h ↦ by simpa using h_equivariant 1 h, fun h ↦ by simpa only [← h] using h_self p⟩
  have h_smul (z : Γ) (p : X) : π (z • p) = z • π p := h_equivariant z (h_self p)
  obtain hF | hF := F.support.finite_or_infinite.symm
  · exact finsum_of_infinite_support hF
  rw [finsum_eq_sum F hF]
  refine Finset.sum_cancels_of_partition_cancels
    ((orbitRel Γ (Set X)).comap fun c ↦ π c.out) fun c hc ↦ ?_
  have hc_ne : F ⟦c.out⟧ ≠ 0 := by rwa [Quotient.out_eq, ← mem_support, ← hF.mem_toFinset]
  set T : Set X := π c.out ∩ {p : X | F ⟦p⟧ ≠ 0}
  -- The action is free on `T`, so all fibres of the map from `T` to the orbits have one size.
  have h_card (p : X) (hp : p ∈ T) : Nat.card {s ∈ T | (⟦s⟧ : orbitRel.Quotient Γ X) = ⟦p⟧} =
      Nat.card (stabilizer Γ (π c.out)) := by
    obtain ⟨hp_mem : p ∈ π c.out, hp_ne : F ⟦p⟧ ≠ 0⟩ := hp
    have h_fibre : {s ∈ T | (⟦s⟧ : orbitRel.Quotient Γ X) = ⟦p⟧} =
        {s ∈ π c.out | (⟦s⟧ : orbitRel.Quotient Γ X) = ⟦p⟧} :=
      Set.ext fun s ↦ and_congr_left fun hs ↦ and_iff_left (by rwa [mem_ofPred_eq, hs])
    rw [h_fibre, ← (h_block p c.out).1 hp_mem,
      card_block_inter_orbit h_block h_smul (h_free p hp_ne)]
  have h_sum_T : ∑ᶠ p ∈ T, F ⟦p⟧ = 0 :=
    (finsum_mem_inter_support (fun p ↦ F ⟦p⟧) (π c.out)).trans (h_sum c.out hc_ne)
  have h_sum_image : ∑ᶠ a ∈ Quotient.mk (orbitRel Γ X) '' T, F a = 0 :=
    finsum_image_eq_zero_of_fibers (h_finite c.out hc_ne) _ h_sum_T fun p hp ↦ by rw [h_card p hp]
  -- On the support of `F`, the image of `T` is the group of `c`.
  have h_image (a : orbitRel.Quotient Γ X) (ha : F a ≠ 0) :
      a ∈ Quotient.mk (orbitRel Γ X) '' T ↔ π a.out ∈ orbit Γ (π c.out) := by
    rw [← mem_image_block_iff h_block h_smul]
    exact ⟨fun h ↦ image_mono inter_subset_left h,
      fun ⟨p, hp, h⟩ ↦ ⟨p, ⟨hp, by rwa [mem_ofPred_eq, h]⟩, h⟩⟩
  rw [← h_sum_image]
  refine (finsum_cond_eq_sum_of_cond_iff F fun {a} ha ↦ ?_).symm
  rw [Finset.mem_filter, hF.mem_toFinset, mem_support, and_iff_right ha]
  exact h_image a ha

/-- The form of `finsum_orbits_eq_zero_of_free_of_blocks` with one hypothesis `h_cancel`: at a point
where `F` is not zero the stabiliser is trivial, and `F` has finite support and sum zero on the
block. -/
lemma finsum_orbits_eq_zero_of_blocks {F : orbitRel.Quotient Γ X → ℂ} (π : X → Set X)
    (h_self : ∀ p : X, p ∈ π p) (h_equivariant : ∀ (z : Γ) {p q : X}, p ∈ π q → π (z • p) = z • π q)
    (h_cancel : ∀ s : X, F ⟦s⟧ ≠ 0 → stabilizer Γ s = ⊥ ∧
      (π s ∩ {p : X | F ⟦p⟧ ≠ 0}).Finite ∧ ∑ᶠ p ∈ π s, F ⟦p⟧ = 0) :
    ∑ᶠ c : orbitRel.Quotient Γ X, F c = 0 :=
  finsum_orbits_eq_zero_of_free_of_blocks π h_self h_equivariant (fun s hs ↦ (h_cancel s hs).1)
    (fun s hs ↦ (h_cancel s hs).2.1) (fun s hs ↦ (h_cancel s hs).2.2)

end Orbits

section Cosets

variable {M X : Type*} [Group M] {L : Subgroup M} {r : M → X} {F : X → ℂ}

/-- Let the fibres of `r` be the cosets of `L`. If translation by `a` multiplies `F ∘ r` by a
constant other than `1`, the sum of `F` over the image of `r` is zero. -/
lemma finsum_mem_range_eq_zero_of_translate (hr : ∀ m m' : M, r m = r m' ↔ m⁻¹ * m' ∈ L)
    {a : M} {c : ℂ} (hc : c ≠ 1) (h_translate : ∀ m : M, F (r (a * m)) = c * F (r m)) :
    ∑ᶠ p ∈ range r, F p = 0 := by
  let r' : M ⧸ L → X :=
    Quotient.lift r fun m m' h ↦ (hr m m').2 (QuotientGroup.leftRel_apply.1 h)
  have h_inj : Injective r' :=
    Quotient.ind₂ fun m m' h ↦ QuotientGroup.eq.2 ((hr m m').1 h)
  have h_sum : c * ∑ᶠ q : M ⧸ L, F (r' q) = ∑ᶠ q : M ⧸ L, F (r' q) := by
    rw [mul_finsum]
    exact finsum_eq_of_bijective (toPerm a) (toPerm a).bijective
      (Quotient.ind fun m ↦ (h_translate m).symm)
  rw [show range r = range r' from QuotientGroup.mk_surjective.range_comp r',
    finsum_mem_range h_inj]
  exact eq_zero_of_mul_eq_self_left hc h_sum

/-- Let the fibres of `r` be the cosets of an open subgroup `L`. If every point of the image of `r`
where `F` is not zero comes from a compact set `C`, there are finitely many such points. -/
lemma finite_range_inter_support [TopologicalSpace M] [IsTopologicalGroup M]
    (hL : IsOpen (L : Set M)) (hr : ∀ m m' : M, r m = r m' ↔ m⁻¹ * m' ∈ L) {C : Set M}
    (hC : IsCompact C) (h_supp : ∀ m : M, F (r m) ≠ 0 → ∃ m' ∈ C, r m' = r m) :
    (range r ∩ {p : X | F p ≠ 0}).Finite := by
  let r' : M ⧸ L → X :=
    Quotient.lift r fun m m' h ↦ (hr m m').2 (QuotientGroup.leftRel_apply.1 h)
  refine ((finite_quotient_image_of_isCompact hL hC).image r').subset ?_
  rintro _ ⟨⟨m, rfl⟩, hm⟩
  obtain ⟨m', hm', h_eq⟩ := h_supp m hm
  exact ⟨m', ⟨m', hm', rfl⟩, h_eq⟩

end Cosets

/-! ### An idempotent that is a polynomial in the element, and its radical -/

section Splitting

variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

/-- Every polynomial `P` over a field has an idempotent `p` modulo `P` such that, if `P` is
separable, not irreducible and not a unit, neither `p` nor `1 - p` is coprime to `P`. -/
lemma exists_idempotent_mod (P : F[X]) :
    ∃ p : F[X], P ∣ p * p - p ∧
      (P.Separable → ¬Irreducible P → ¬IsUnit P → ¬IsCoprime P (1 - p) ∧ ¬IsCoprime P p) := by
  by_cases hP : P.Separable ∧ ¬Irreducible P ∧ ¬IsUnit P
  · -- Factor `P = A * B` into coprime non-units, `u * A + v * B = 1`, and take `p = u * A`.
    obtain ⟨h_sep, h_red, h_unit⟩ := hP
    obtain ⟨A, B, hA, hB, rfl⟩ : ∃ A B : F[X], ¬IsUnit A ∧ ¬IsUnit B ∧ P = A * B :=
      (irreducible_or_factor h_unit).resolve_left h_red
    obtain ⟨u, v, huv⟩ : IsCoprime A B := h_sep.isCoprime
    have h_dvd : A * B ∣ u * A * (u * A) - u * A := ⟨-u * v, by linear_combination u * A * huv⟩
    have h_one_sub : ¬IsCoprime (A * B) (1 - u * A) := fun h ↦ by
      rw [← huv, add_sub_cancel_left] at h
      exact hB (isCoprime_self.1 h.of_mul_left_right.of_mul_right_right)
    have h_self : ¬IsCoprime (A * B) (u * A) := fun h ↦
      hA (isCoprime_self.1 h.of_mul_left_left.of_mul_right_right)
    exact ⟨u * A, h_dvd, fun _ _ _ ↦ ⟨h_one_sub, h_self⟩⟩
  · exact ⟨0, by simp, fun h_sep h_red h_unit ↦ absurd ⟨h_sep, h_red, h_unit⟩ hP⟩

/-- A fixed choice of the idempotent modulo `P` of `exists_idempotent_mod`. -/
def splittingPoly (P : F[X]) : F[X] := (exists_idempotent_mod P).choose

/-- The idempotent `p(g)`, where `p` is the chosen idempotent modulo the characteristic polynomial
of `g`. -/
def splittingIdempotent (g : GL n F) : Matrix n n F := aeval g.val (splittingPoly g.val.charpoly)

/-- The matrix `splittingIdempotent g = p(g)` is idempotent, by the Cayley-Hamilton theorem. -/
lemma isIdempotentElem_splittingIdempotent (g : GL n F) :
    IsIdempotentElem (splittingIdempotent g) := by
  have h_dvd := aeval_dvd g.1 (exists_idempotent_mod g.1.charpoly).choose_spec.1
  rwa [aeval_self_charpoly, zero_dvd_iff, map_sub, map_mul, sub_eq_zero] at h_dvd

/-- If the characteristic polynomial of `g` is separable and not irreducible, the idempotent
`splittingIdempotent g` is neither `0` nor `1`. -/
lemma splittingIdempotent_ne_zero_and_ne_one [Nonempty n] {g : GL n F}
    (h_sep : g.val.charpoly.Separable) (h_red : ¬Irreducible g.val.charpoly) :
    splittingIdempotent g ≠ 0 ∧ splittingIdempotent g ≠ 1 := by
  have h_unit : ¬IsUnit g.1.charpoly := not_isUnit_of_natDegree_pos _ (by simp [Fintype.card_pos])
  obtain ⟨h_one_sub, h_self⟩ : ¬IsCoprime g.1.charpoly (1 - splittingPoly g.1.charpoly) ∧
      ¬IsCoprime g.1.charpoly (splittingPoly g.1.charpoly) :=
    (exists_idempotent_mod g.1.charpoly).choose_spec.2 h_sep h_red h_unit
  rw [splittingIdempotent]
  exact ⟨fun h ↦ h_one_sub (isUnit_aeval_iff_isCoprime.1 (by simp [h])),
    fun h ↦ h_self (isUnit_aeval_iff_isCoprime.1 (by simp [h]))⟩

lemma aeval_units_conj (b g : GL n F) (p : F[X]) :
    aeval (b⁻¹ * g * b).val p = b⁻¹.val * aeval g.val p * b.val := by
  have h_semiconj : b.1 * (b⁻¹ * g * b).1 = g.1 * b.1 := by simp [← mul_assoc]
  rw [mul_assoc b⁻¹.1, ← aeval_semiconj h_semiconj p, Units.inv_mul_cancel_left]

/-- Conjugating `g` conjugates its idempotent. -/
lemma splittingIdempotent_conj (b g : GL n F) :
    splittingIdempotent (b⁻¹ * g * b) = b⁻¹.val * splittingIdempotent g * b.val := by
  rw [splittingIdempotent, aeval_units_conj, Units.val_mul, Units.val_mul, coe_units_inv,
    charpoly_units_conj', splittingIdempotent]

/-- The parametrisation `Y ↦ 1 + e Y (1 - e)` of the unipotent radical attached to the idempotent
`e = splittingIdempotent g`. Its range is called the radical of `g`. -/
def splittingRadical (g : GL n F) : Multiplicative (Matrix n n F) →* GL n F :=
  radicalHom (isIdempotentElem_splittingIdempotent g)

/-- Conjugating `g` conjugates its radical: if `a` lies in the radical of `g`, then `b⁻¹ a b` lies
in the radical of `b⁻¹ g b`. -/
lemma mem_range_splittingRadical_conj {b g a : GL n F} (ha : a ∈ (splittingRadical g).range) :
    b⁻¹ * a * b ∈ (splittingRadical (b⁻¹ * g * b)).range := by
  obtain ⟨Y, rfl⟩ := ha
  refine ⟨ofAdd (b⁻¹.1 * Y.toAdd * b.1), Units.ext ?_⟩
  simp only [splittingRadical, Units.val_mul, coe_radicalHom, splittingIdempotent_conj, toAdd_ofAdd]
  simp [mul_add, add_mul, mul_sub, sub_mul, mul_assoc]

/-- An element `a` of the radical of `g` is recovered from the conjugate `a⁻¹ g a`: its parameter
can be taken to be `p(a⁻¹ g a)`, for the polynomial `p` that gives the idempotent of `g`. -/
lemma splittingRadical_aeval_conj {g a : GL n F} (ha : a ∈ (splittingRadical g).range) :
    splittingRadical g (ofAdd (aeval (a⁻¹ * g * a).val (splittingPoly g.val.charpoly))) = a := by
  obtain ⟨Y, hY⟩ := ha
  have he : IsIdempotentElem (splittingIdempotent g) := isIdempotentElem_splittingIdempotent g
  set e : Matrix n n F := splittingIdempotent g
  have h_coe : a.val = 1 + e * Y.toAdd * (1 - e) := by rw [← hY, splittingRadical, coe_radicalHom]
  have h_fix : a⁻¹.val * e = e := by rw [← hY, ← map_inv, splittingRadical,
    coe_radicalHom_mul_idempotent]
  have h_aeval : aeval (a⁻¹ * g * a).val (splittingPoly g.val.charpoly) = e * a.val := by
    rw [aeval_units_conj, ← splittingIdempotent, h_fix]
  -- As `a⁻¹ e = e`, the parameter of the left side is `e a`, and `e (e a) (1 - e) = e Y (1 - e)`.
  have h_param : e * (e * a.val) * (1 - e) = e * Y.toAdd * (1 - e) := by
    simp [h_coe, mul_add, add_mul, mul_assoc, he.mul_self_mul, he.one_sub.eq, he.mul_one_sub_self]
  exact Units.ext (by rw [h_aeval, splittingRadical, coe_radicalHom, toAdd_ofAdd, h_param, h_coe])

/-- A translate `j g` of `g` by an element `j` of its radical is conjugate to `g` under the
radical. -/
lemma exists_splittingRadical_conj {g j : GL n F} (hj : j ∈ (splittingRadical g).range) :
    ∃ D : Multiplicative (Matrix n n F),
      (splittingRadical g D)⁻¹ * g * splittingRadical g D = j * g := by
  -- With `x = j g` and `p(g)` the idempotent of `g`, the parameter `D = p(x) - p(g)` works, by
  -- `semiconjBy_radicalHom_aeval_sub` for the factorisation `x = j g 1`.
  obtain ⟨Y, rfl⟩ := hj
  have he : IsIdempotentElem (splittingIdempotent g) := isIdempotentElem_splittingIdempotent g
  set p : F[X] := splittingPoly g.1.charpoly
  set x : GL n F := splittingRadical g Y * g
  set D : Multiplicative (Matrix n n F) := ofAdd (aeval x.1 p - aeval g.1 p)
  have h_semiconj : SemiconjBy (splittingRadical g D) x g :=
    semiconjBy_radicalHom_aeval_sub he (h_range := he.eq) (h_fix := he.eq) Y 1
      (by simp [x, splittingRadical])
  exact ⟨D, by rw [mul_assoc, ← h_semiconj.eq, inv_mul_cancel_left]⟩

/-- Conjugating `g` by an element `b` of its radical does not change the radical, as this group is
commutative. -/
lemma range_splittingRadical_conj_self {g b : GL n F} (hb : b ∈ (splittingRadical g).range) :
    (splittingRadical (b⁻¹ * g * b)).range = (splittingRadical g).range := by
  have h_le {g b : GL n F} (hb : b ∈ (splittingRadical g).range) :
      (splittingRadical g).range ≤ (splittingRadical (b⁻¹ * g * b)).range := by
    intro a ha
    have h_comm : Commute a b := by
      obtain ⟨Y, rfl⟩ := ha
      obtain ⟨Z, rfl⟩ := hb
      exact (Commute.all Y Z).map (splittingRadical g)
    have h_fix : b⁻¹ * a * b = a := by rw [mul_assoc, h_comm.eq, inv_mul_cancel_left]
    simpa only [h_fix] using mem_range_splittingRadical_conj (b := b) ha
  -- For the other inclusion, conjugate back by `b⁻¹`, which lies in the radical of `b⁻¹ * g * b`.
  have h_back : b⁻¹⁻¹ * (b⁻¹ * g * b) * b⁻¹ = g := by group
  exact le_antisymm (by simpa only [h_back] using h_le (inv_mem (h_le hb hb))) (h_le hb)

end Splitting

/-- If the characteristic polynomial of `g` is separable and reducible, a cuspidal type `(J, χ)`
has an element `j` in the radical of `g` with `χ j ≠ 1`. -/
lemma IsCuspidalType.exists_mem_range_splittingRadical {F : Type*} {n : Type} [Field F]
    [Fintype n] [DecidableEq n] [Nonempty n] {J : Subgroup (GL n F)} {χ : J →* ℂ}
    (hχ : IsCuspidalType J χ) {g : GL n F} (h_sep : g.1.charpoly.Separable)
    (h_red : ¬Irreducible g.1.charpoly) :
    ∃ j : J, j.1 ∈ (splittingRadical g).range ∧ χ j ≠ 1 := by
  obtain ⟨h_ne_zero, h_ne_one⟩ := splittingIdempotent_ne_zero_and_ne_one h_sep h_red
  obtain ⟨j, Y, hj, hχj⟩ : ∃ (j : J) (Y : Matrix n n F),
      1 + splittingIdempotent g * Y * (1 - splittingIdempotent g) = j.1 ∧ χ j ≠ 1 :=
    hχ _ (isIdempotentElem_splittingIdempotent g) h_ne_zero h_ne_one
  exact ⟨j, ⟨ofAdd Y, Units.ext hj⟩, hχj⟩

/-! ### The blocks of triples -/

section Blocks

variable {E n : Type} [Field E] [CMBase E] [Fintype n] [DecidableEq n] {K : Subgroup (GL n (𝔸f E))}
  (w₀ : SplitFinPlace E)

variable (K) in
/-- The triple `(xK, y, μ)`. -/
def markedTriple (x : GL n (𝔸f E)) (y : GL n E) (μ : n) : MarkedTriple K n := (↑x, y, μ)

/-- A triple `p = (q, y, μ)` is the triple of the chosen representative of its coset `q`. -/
lemma markedTriple_out (p : MarkedTriple K n) : markedTriple K p.1.out p.2.1 p.2.2 = p :=
  Prod.ext (QuotientGroup.out_eq' p.1) rfl

/-- The triples `(xK, y, μ)` and `(x'K, y', μ)` are equal if and only if `xK = x'K` and `y = y'`. -/
lemma markedTriple_eq_iff {x x' : GL n (𝔸f E)} {y y' : GL n E} {μ : n} :
    markedTriple K x y μ = markedTriple K x' y' μ ↔ x⁻¹ * x' ∈ K ∧ y = y' := by
  simp [markedTriple, MarkedTriple, QuotientGroup.eq]

/-- An element `z` of `GL n E` sends `(xK, y, μ)` to `(z x K, z y z⁻¹, μ)`. -/
lemma smul_markedTriple (z : GL n E) (x : GL n (𝔸f E)) (y : GL n E) (μ : n) :
    z • markedTriple K x y μ = markedTriple K (toFinGL z * x) (z * y * z⁻¹) μ := rfl

/-- Moving the frame `x` to `x k` conjugates `invAutInFrame y x = x⁻¹ y⁻¹ x` by `k`. -/
lemma invAutInFrame_mul (y : GL n E) (x k : GL n (𝔸f E)) :
    invAutInFrame y (x * k) = k⁻¹ * invAutInFrame y x * k := by
  simp [invAutInFrame, mul_assoc]

/-- The element `invAutInFrame y x = x⁻¹ y⁻¹ x` does not change under `(y, x) ↦ (z y z⁻¹, z x)`. -/
lemma invAutInFrame_conj (z y : GL n E) (x : GL n (𝔸f E)) :
    invAutInFrame (z * y * z⁻¹) (toFinGL z * x) = invAutInFrame y x := by
  simp [invAutInFrame, mul_assoc]

/-- The automorphism `y` in the frame `x` at the split place `w₀`: the inverse transpose of the
component of `x⁻¹ y⁻¹ x` at `w₀`. -/
def localAut (y : GL n E) (x : GL n (𝔸f E)) : GL n (LocField w₀.1) :=
  dualComponent w₀ (invAutInFrame y x)

/-- Moving the frame `x` to `x k` conjugates `localAut w₀ y x` by the inverse transpose of the
component of `k` at `w₀`. -/
lemma localAut_mul (y : GL n E) (x k : GL n (𝔸f E)) :
    localAut w₀ y (x * k) = (dualComponent w₀ k)⁻¹ * localAut w₀ y x * dualComponent w₀ k := by
  simp [localAut, invAutInFrame_mul]

/-- Moving the frame `x` by an element `a` placed at `w₀` conjugates `localAut w₀ y x` by `a`. -/
lemma localAut_mul_conjAtSplit (y : GL n E) (x : GL n (𝔸f E)) (a : GL n (LocField w₀.1)) :
    localAut w₀ y (x * conjAtSplit w₀ a) = a⁻¹ * localAut w₀ y x * a := by
  rw [localAut_mul, dualComponent_conjAtSplit]

/-- The matrix of `dualComponent w₀ a` is the transpose of the component of `a⁻¹` at `w₀`. -/
lemma coe_dualComponent (a : GL n (𝔸f E)) :
    (dualComponent w₀ a).val = (a⁻¹.val.map (evalAt w₀.1))ᵀ := rfl

/-- The characteristic polynomial of `localAut w₀ y x` is that of `y`, read in the completion of
`E` at `w₀`. -/
lemma charpoly_localAut (y : GL n E) (x : GL n (𝔸f E)) :
    (localAut w₀ y x).val.charpoly =
      y.val.charpoly.map ((evalAt w₀.1).comp (algebraMap E (𝔸f E))) := by
  have h_inv : (invAutInFrame y x)⁻¹ = x⁻¹ * toFinGL y * x := by simp [invAutInFrame, mul_assoc]
  have h_conj :
      (x⁻¹ * toFinGL y * x).val.charpoly = y.val.charpoly.map (algebraMap E (𝔸f E)) := by
    rw [Units.val_mul, Units.val_mul, coe_units_inv, charpoly_units_conj', ← charpoly_map]
    rfl
  rw [localAut, coe_dualComponent, charpoly_transpose, charpoly_map, h_inv, h_conj,
    Polynomial.map_map]

variable (K) in
/-- The block of `(xK, y, μ)`: the triples `(x a K, y, μ)`, where `a` runs over the radical of
`localAut w₀ y x`, placed at `w₀`. -/
def tripleBlock (x : GL n (𝔸f E)) (y : GL n E) (μ : n) : Set (MarkedTriple K n) :=
  range fun Y : Multiplicative (Matrix n n (LocField w₀.1)) ↦
    markedTriple K (x * conjAtSplit w₀ (splittingRadical (localAut w₀ y x) Y)) y μ

/-- The points of the block of `(xK, y, μ)` are the triples `(x a K, y, μ)` with `a` in the radical
of `localAut w₀ y x`. -/
lemma mem_tripleBlock {x : GL n (𝔸f E)} {y : GL n E} {μ : n} {p : MarkedTriple K n} :
    p ∈ tripleBlock K w₀ x y μ ↔ ∃ a ∈ (splittingRadical (localAut w₀ y x)).range,
      markedTriple K (x * conjAtSplit w₀ a) y μ = p := by
  simp [tripleBlock]

/-- If `K` consists of unitary similitudes, the block of `(xK, y, μ)` does not depend on the
representative `x` of the coset `xK`. -/
lemma tripleBlock_mul_of_mem (hK : K ≤ GU E n) (x : GL n (𝔸f E)) (y : GL n E) (μ : n)
    {k : GL n (𝔸f E)} (hk : k ∈ K) : tripleBlock K w₀ (x * k) y μ = tripleBlock K w₀ x y μ := by
  -- One inclusion suffices, for `x`, `k` and for `x * k`, `k⁻¹`.
  suffices h_subset : ∀ (x k : GL n (𝔸f E)), k ∈ K →
      tripleBlock K w₀ x y μ ⊆ tripleBlock K w₀ (x * k) y μ by
    refine subset_antisymm ?_ (h_subset x k hk)
    simpa only [mul_inv_cancel_right] using h_subset (x * k) k⁻¹ (inv_mem hk)
  intro x k hk p hp
  obtain ⟨a, ha, rfl⟩ := (mem_tripleBlock w₀).1 hp
  set b : GL n (LocField w₀.1) := dualComponent w₀ k with hb
  have h_mem : b⁻¹ * a * b ∈ (splittingRadical (localAut w₀ y (x * k))).range := by
    simpa only [localAut_mul] using mem_range_splittingRadical_conj ha
  have h_conj : k * conjAtSplit w₀ (b⁻¹ * a * b) * k⁻¹ = conjAtSplit w₀ a := by
    rw [conj_conjAtSplit (hK hk), ← hb]
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  refine (mem_tripleBlock w₀).2 ⟨b⁻¹ * a * b, h_mem, markedTriple_eq_iff.2 ⟨?_, rfl⟩⟩
  rw [← h_conj]
  simpa only [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left] using inv_mem hk

/-- All points of a block have the same block: for `b` in the radical of `localAut w₀ y x`, the
triples `(x b K, y, μ)` and `(xK, y, μ)` have the same block. -/
lemma tripleBlock_mul_conjAtSplit (x : GL n (𝔸f E)) (y : GL n E) (μ : n)
    {b : GL n (LocField w₀.1)} (hb : b ∈ (splittingRadical (localAut w₀ y x)).range) :
    tripleBlock K w₀ (x * conjAtSplit w₀ b) y μ = tripleBlock K w₀ x y μ := by
  -- Both blocks have the same radical, which contains `b`; so `a ↦ b * a` is a change of parameter.
  ext p
  rw [mem_tripleBlock, mem_tripleBlock, localAut_mul_conjAtSplit,
    range_splittingRadical_conj_self hb]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨b * a, mul_mem hb ha, by rw [map_mul, mul_assoc]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨b⁻¹ * a, mul_mem (inv_mem hb) ha, by rw [mul_assoc, ← map_mul, mul_inv_cancel_left]⟩

/-- An element `z` of `GL n E` carries the block of `(xK, y, μ)` to the block of
`(z x K, z y z⁻¹, μ)`. -/
lemma smul_tripleBlock (z : GL n E) (x : GL n (𝔸f E)) (y : GL n E) (μ : n) :
    z • tripleBlock K w₀ x y μ = tripleBlock K w₀ (toFinGL z * x) (z * y * z⁻¹) μ := by
  simp only [tripleBlock, smul_set_range, smul_markedTriple, localAut, invAutInFrame_conj,
    mul_assoc (toFinGL z)]

/-- The block of a triple `p = (q, y, μ)`, read at the chosen representative of the coset `q`. -/
def blockOf (p : MarkedTriple K n) : Set (MarkedTriple K n) :=
  tripleBlock K w₀ p.1.out p.2.1 p.2.2

/-- If `K` consists of unitary similitudes, the block of `(xK, y, μ)` can be read at `x`. -/
lemma blockOf_markedTriple (hK : K ≤ GU E n) (x : GL n (𝔸f E)) (y : GL n E) (μ : n) :
    blockOf w₀ (markedTriple K x y μ) = tripleBlock K w₀ x y μ := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
  change tripleBlock K w₀ (x : GL n (𝔸f E) ⧸ K).out y μ = tripleBlock K w₀ x y μ
  rw [hk, tripleBlock_mul_of_mem w₀ hK x y μ k.2]

lemma mem_blockOf_self (p : MarkedTriple K n) : p ∈ blockOf w₀ p :=
  (mem_tripleBlock w₀).2 ⟨1, one_mem _, by rw [map_one, mul_one, markedTriple_out]⟩

/-- If `K` consists of unitary similitudes, then for `p` in the block of `q` the block of `z • p` is
the translate by `z` of the block of `q`. -/
lemma blockOf_smul (hK : K ≤ GU E n) (z : GL n E) {p q : MarkedTriple K n}
    (hp : p ∈ blockOf w₀ q) : blockOf w₀ (z • p) = z • blockOf w₀ q := by
  obtain ⟨a, ha, rfl⟩ := (mem_tripleBlock w₀).1 hp
  rw [smul_markedTriple, blockOf_markedTriple w₀ hK, ← smul_tripleBlock,
    tripleBlock_mul_conjAtSplit (hb := ha), blockOf]

end Blocks

/-! ### The classes with reducible polynomial -/

section Reducible

variable {E n : Type} [Field E] [CMBase E] [Fintype n] [DecidableEq n] {𝔑 : 𝓞 E}
  {f : heckeAlgebra n ℂ 𝔑} {w₀ : SplitFinPlace E} {ε : Prop} {u : E[X] → n → ℂ} {x : GL n (𝔸f E)}
  {y : GL n E} {μ : n}

/-- If the level `𝔑` is neat (it is non-zero, and an automorphism of a signed frame that lies in the
level is trivial), a triple `(xK, y, μ)` with `K = levelGU n 𝔑` whose frame `x` satisfies the sign
condition `h_sign` has trivial stabiliser in `GL n E`. -/
lemma stabilizer_markedTriple (hN : IsNeat n 𝔑)
    (h_sign : IsSignedFrame x (eigenReflection ε y μ)) :
    stabilizer (GL n E) (markedTriple (levelGU n 𝔑) x y μ) = ⊥ := by
  refine eq_bot_iff.2 fun z hz ↦ ?_
  rw [mem_stabilizer_iff, smul_markedTriple, eq_comm, markedTriple_eq_iff] at hz
  obtain ⟨h_level, h_comm : y = z * y * z⁻¹⟩ := hz
  have h_mem : x⁻¹ * toFinGL z * x ∈ levelGU n 𝔑 := by rwa [mul_assoc]
  have h_fix : ratConj z (eigenReflection ε y μ) = eigenReflection ε y μ := by
    rw [ratConj_eigenReflection, ← h_comm]
  exact hN.2 h_sign h_mem h_fix

/-- Let the Hecke function `f` have type `(J, χ)` at `w₀`: it sends vectors of level `𝔑` to
`χ`-eigenvectors of `J`. Then left translation by `j ∈ J`, placed at `w₀`, multiplies the function
`heckeCosetFn f` on cosets of the level by `χ j⁻¹`. -/
lemma heckeCosetFn_conjAtSplit_mul {J : Subgroup (GL n (LocField w₀.1))} {χ : J →* ℂ}
    (hJ : f.val ∈ fixedToEigen (levelGU n 𝔑) (conjAtSplit w₀) J χ) (j : J) (t : GL n (𝔸f E)) :
    heckeCosetFn f (conjAtSplit w₀ j * t : GL n (𝔸f E)) = χ j⁻¹ * heckeCosetFn f t := by
  -- The values of `heckeCosetFn f` are the coefficients of `v`, the image under `f` of the trivial
  -- coset, which is a vector of level `levelGU n 𝔑`; evaluate the eigenvector equation at `t`.
  let π := Representation.ofMulAction ℂ (GL n (𝔸f E)) (GL n (𝔸f E) ⧸ levelGU n 𝔑)
  let v : MonoidAlgebra ℂ (GL n (𝔸f E) ⧸ levelGU n 𝔑) :=
    π.asAlgebraHom f (MonoidAlgebra.single (QuotientGroup.mk 1) 1)
  have h_eigen : π (conjAtSplit w₀ j.val⁻¹) v = χ j⁻¹ • v := hJ single_one_mem_levelSpace j⁻¹
  rw [show heckeCosetFn f = v.coeff from rfl]
  calc _ = v.coeff ((conjAtSplit w₀ j.val⁻¹)⁻¹ • (t : GL n (𝔸f E) ⧸ levelGU n 𝔑)) := by
        rw [map_inv, inv_inv, Quotient.smul_mk, smul_eq_mul]
    _ = (π (conjAtSplit w₀ j.val⁻¹) v).coeff t := (Representation.coeff_ofMulAction _ _ _).symm
    _ = χ j⁻¹ * v.coeff t := by
        rw [h_eigen, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]

/-- If the Hecke function `f` is not zero on the coset of `t`, the inverse transpose of the
component of `t` at `w₀` is an integral matrix. -/
lemma dualComponent_mem_matrix {t : GL n (𝔸f E)} (ht : heckeCosetFn f t ≠ 0) :
    (dualComponent w₀ t).val ∈ (LocInt w₀.1 : Set (LocField w₀.1)).matrix :=
  fun i j ↦ mem_Ô.1 ((heckeAlgebra.mem_GUPlus_of_ne_zero ht).2 j i) w₀.1

/-- Moving a frame `x` that satisfies the sign condition by an element `a` at `w₀` keeps the sign
condition and the weight, so the term of `(x a K, y, μ)` is the value of `f` times the weight. -/
lemma countTerm_mul_conjAtSplit (h_sign : IsSignedFrame x (eigenReflection ε y μ))
    (a : GL n (LocField w₀.1)) :
    countTerm ε f u ⟦markedTriple (levelGU n 𝔑) (x * conjAtSplit w₀ a) y μ⟧ =
      heckeCosetFn f (invAutInFrame y (x * conjAtSplit w₀ a)) * u y.val.charpoly μ := by
  have h_sign' : IsSignedFrame (x * conjAtSplit w₀ a) (eigenReflection ε y μ) := by
    simpa [isSignedFrame_mul_iff 1 (conjAtSplit_mem_GU a), ratConj_eigenReflection] using h_sign
  exact countTerm_mk.trans (ite_eq_left h_sign')

/-- Let `x⁻¹ y⁻¹ x` be a unitary similitude. Moving the frame `x` by an element `a` at `w₀`
conjugates its factor `localAut w₀ y x` at `w₀` by `a` and leaves the rest alone. -/
lemma invAutInFrame_mul_conjAtSplit (h_mem : invAutInFrame y x ∈ GU E n)
    (a : GL n (LocField w₀.1)) :
    invAutInFrame y (x * conjAtSplit w₀ a) = conjAtSplit w₀ (a⁻¹ * localAut w₀ y x * a) *
      ((conjAtSplit w₀ (localAut w₀ y x))⁻¹ * invAutInFrame y x) := by
  have h_comm : invAutInFrame y x * conjAtSplit w₀ a =
      conjAtSplit w₀ (localAut w₀ y x * a * (localAut w₀ y x)⁻¹) * invAutInFrame y x :=
    eq_mul_of_mul_inv_eq (conj_conjAtSplit h_mem a)
  rw [invAutInFrame_mul, mul_assoc, h_comm]
  simp only [map_mul, map_inv, mul_assoc]

variable (𝔑 w₀ x y μ) in
/-- The point of the block of `(xK, y, μ)` with parameter `Y`, for the principal level
`K = levelGU n 𝔑`. -/
abbrev blockPoint (Y : Multiplicative (Matrix n n (LocField w₀.1))) :
    MarkedTriple (levelGU n 𝔑) n :=
  markedTriple (levelGU n 𝔑) (x * conjAtSplit w₀ (splittingRadical (localAut w₀ y x) Y)) y μ

lemma tripleBlock_eq_range_blockPoint :
    tripleBlock (levelGU n 𝔑) w₀ x y μ = range (blockPoint 𝔑 w₀ x y μ) := rfl

/-- Two parameters `Y`, `Y'` give the same point of the block if and only if the element of the
radical with parameter `Y⁻¹ * Y'`, placed at `w₀`, lies in the level `levelGU n 𝔑`. -/
lemma blockPoint_eq_iff (Y Y' : Multiplicative (Matrix n n (LocField w₀.1))) :
    blockPoint 𝔑 w₀ x y μ Y = blockPoint 𝔑 w₀ x y μ Y' ↔ Y⁻¹ * Y' ∈
      ((levelGU n 𝔑).comap (conjAtSplit w₀)).comap (splittingRadical (localAut w₀ y x)) := by
  simp only [markedTriple_eq_iff, and_true, Subgroup.mem_comap, map_mul, map_inv,
    _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]

/-- If `𝔑 ≠ 0` and the frame `x` satisfies the sign condition `h_sign`, then `countTerm ε f u`
(the value of `f` times the weight `u`, at classes with the sign condition) is non-zero at only
finitely many points `(x a K, y, μ)` of the block of `(xK, y, μ)`. Here `K = levelGU n 𝔑` and `a`
runs over the radical `1 + e M_n (1 - e)` of `localAut w₀ y x`, placed at `w₀` by `conjAtSplit w₀`;
`localAut w₀ y x` is the inverse transpose of the component of `x⁻¹ y⁻¹ x` at `w₀`, and `e` is its
chosen idempotent. -/
lemma finite_tripleBlock_inter_support (h𝔑 : 𝔑 ≠ 0)
    (h_sign : IsSignedFrame x (eigenReflection ε y μ)) :
    (tripleBlock (levelGU n 𝔑) w₀ x y μ ∩
      {p : MarkedTriple (levelGU n 𝔑) n | countTerm ε f u ⟦p⟧ ≠ 0}).Finite := by
  -- Let `g = localAut w₀ y x` have idempotent `p(g)`. If the term at `a` is not zero then
  -- `a⁻¹ g a` is integral, and `p(a⁻¹ g a)` is a parameter of `a`; these lie in a compact set.
  set g : GL n (LocField w₀.1) := localAut w₀ y x
  set p : (LocField w₀.1)[X] := splittingPoly g.1.charpoly
  have h_compact : IsCompact ((fun M : Matrix n n (LocField w₀.1) ↦ ofAdd (aeval M p)) ''
      (LocInt w₀.1 : Set (LocField w₀.1)).matrix) :=
    (isCompact_LocInt w₀.1).matrix.image (continuous_ofAdd.comp p.continuous_aeval)
  rw [tripleBlock_eq_range_blockPoint]
  refine finite_range_inter_support (F := fun q ↦ countTerm ε f u ⟦q⟧) ?_ blockPoint_eq_iff
    h_compact fun Y hY ↦ ?_
  · exact (isOpen_comap_conjAtSplit h𝔑).preimage (continuous_radicalHom _)
  set a : GL n (LocField w₀.1) := splittingRadical g Y
  have h_int : (a⁻¹ * g * a).1 ∈ (LocInt w₀.1 : Set (LocField w₀.1)).matrix := by
    rw [countTerm_mul_conjAtSplit h_sign] at hY
    rw [← localAut_mul_conjAtSplit]
    exact dualComponent_mem_matrix (left_ne_zero_of_mul hY)
  -- This parameter gives the same element `a` of the radical, so the same point of the block.
  exact ⟨ofAdd (aeval (a⁻¹ * g * a).1 p), mem_image_of_mem _ h_int,
    by rw [blockPoint, splittingRadical_aeval_conj ⟨Y, rfl⟩]⟩

/-- Let `f` have type `(J, χ)` at the split place `w₀` (it turns vectors fixed by the level into
`χ`-eigenvectors of `J`), let the frame `x` satisfy the sign condition and let `x⁻¹ y⁻¹ x` be a
unitary similitude. The block of `(xK, y, μ)` consists of the `(x a K, y, μ)` with `a` in the
radical of `localAut w₀ y x`, placed at `w₀`. If `χ` is not trivial at some `j ∈ J` in this radical,
the sum over the block of `countTerm ε f u` (the value of `f` times the weight `u`) is zero. -/
lemma finsum_tripleBlock_eq_zero {J : Subgroup (GL n (LocField w₀.1))} {χ : J →* ℂ}
    (hJ : f.val ∈ fixedToEigen (levelGU n 𝔑) (conjAtSplit w₀) J χ)
    (h_sign : IsSignedFrame x (eigenReflection ε y μ)) (h_mem : invAutInFrame y x ∈ GU E n)
    {j : J} (hj : j.val ∈ (splittingRadical (localAut w₀ y x)).range) (hχ : χ j ≠ 1) :
    ∑ᶠ p ∈ tripleBlock (levelGU n 𝔑) w₀ x y μ, countTerm ε f u ⟦p⟧ = 0 := by
  -- Write `j g = d⁻¹ g d` with `d` in the radical. Translation by `d` permutes the block and
  -- multiplies each term by `χ j⁻¹ ≠ 1`.
  set g : GL n (LocField w₀.1) := localAut w₀ y x
  obtain ⟨D, hD⟩ := exists_splittingRadical_conj hj
  rw [tripleBlock_eq_range_blockPoint]
  refine finsum_mem_range_eq_zero_of_translate (F := fun p ↦ countTerm ε f u ⟦p⟧) (a := D)
    (c := χ j⁻¹) blockPoint_eq_iff (by simpa using hχ) fun Y ↦ ?_
  set d : GL n (LocField w₀.1) := splittingRadical g D
  set a : GL n (LocField w₀.1) := splittingRadical g Y
  have h_comm : Commute a⁻¹ j.1 := by
    obtain ⟨Z, hZ⟩ := hj
    simpa only [hZ] using ((Commute.all Y Z).map (splittingRadical g)).inv_left
  have h_conj : (d * a)⁻¹ * g * (d * a) = j * (a⁻¹ * g * a) :=
    calc _ = a⁻¹ * (d⁻¹ * g * d) * a := by group
      _ = j * (a⁻¹ * g * a) := by simp only [hD, mul_assoc, h_comm.left_comm]
  have h_value : heckeCosetFn f (invAutInFrame y (x * conjAtSplit w₀ (d * a))) =
      χ j⁻¹ * heckeCosetFn f (invAutInFrame y (x * conjAtSplit w₀ a)) := by
    rw [invAutInFrame_mul_conjAtSplit h_mem, invAutInFrame_mul_conjAtSplit h_mem, h_conj, map_mul,
      mul_assoc (conjAtSplit w₀ j.1), heckeCosetFn_conjAtSplit_mul hJ]
  rw [countTerm_mul_conjAtSplit h_sign, countTerm_mul_conjAtSplit h_sign,
    map_mul (splittingRadical g), h_value, mul_assoc]

/-- Let `𝔑` be neat (non-zero, with only trivial automorphisms of signed frames) and let `f` be a
regular Hecke function of level `𝔑` (its terms vanish unless the characteristic polynomial is
separable) with the cuspidal type `(J, χ)` at the split place `w₀` (`f` turns vectors fixed by the
level into `χ`-eigenvectors of `J`, and `χ` is non-trivial on `J` in each proper unipotent
radical). If the weight `u` vanishes on irreducible polynomials, so that only classes with reducible
characteristic polynomial contribute, then `countTerm ε f u` (the value of `f` times `u`, at classes
with the sign condition of `ε`) has sum zero over all classes, for the marked count (`ε` true) and
for the definite count (`ε` false). -/
lemma finsum_countTerm_eq_zero_of_reducible (hN : IsNeat n 𝔑) (h_regular : IsRegularHecke f)
    {J : Subgroup (GL n (LocField w₀.1))} {χ : J →* ℂ} (hχ : IsCuspidalType J χ)
    (hJ : f.val ∈ fixedToEigen (levelGU n 𝔑) (conjAtSplit w₀) J χ)
    (hu : ∀ P : E[X], Irreducible P → u P = 0) (ε : Prop) :
    ∑ᶠ c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n), countTerm ε f u c = 0 := by
  classical
  have hK : levelGU n 𝔑 ≤ GU E n := inf_le_left
  refine finsum_orbits_eq_zero_of_blocks (blockOf w₀) (mem_blockOf_self w₀) (blockOf_smul w₀ hK)
    fun s hs ↦ ?_
  obtain ⟨x, y, μ, rfl⟩ : ∃ x y μ, markedTriple (levelGU n 𝔑) x y μ = s :=
    ⟨_, _, _, markedTriple_out s⟩
  obtain ⟨h_sign, hf_ne, hu_ne⟩ : IsSignedFrame x (eigenReflection ε y μ) ∧
      heckeCosetFn f (invAutInFrame y x) ≠ 0 ∧ u y.val.charpoly μ ≠ 0 := by
    rwa [markedTriple, countTerm_mk, ite_ne_right_iff, mul_ne_zero_iff] at hs
  -- The characteristic polynomial of `g = localAut w₀ y x` is that of `y`: separable as `f` is
  -- regular, and not irreducible as the weight `u` is not zero at it. So the idempotent of `g` is
  -- not `0` or `1`, and `χ` is not trivial on the radical of `g`.
  have h_sep : (localAut w₀ y x).val.charpoly.Separable := by
    simpa only [charpoly_localAut] using (h_regular hf_ne).map
  have h_red : ¬Irreducible (localAut w₀ y x).val.charpoly := fun h ↦ by
    rw [charpoly_localAut] at h
    exact hu_ne (congrFun (hu _ ((charpoly_monic y.val).irreducible_of_irreducible_map _ _ h)) μ)
  have : Nonempty n := ⟨μ⟩
  obtain ⟨j, hj, hχj⟩ := hχ.exists_mem_range_splittingRadical h_sep h_red
  rw [blockOf_markedTriple w₀ hK]
  exact ⟨stabilizer_markedTriple hN h_sign, finite_tripleBlock_inter_support hN.1 h_sign,
    finsum_tripleBlock_eq_zero hJ h_sign (heckeAlgebra.mem_GUPlus_of_ne_zero hf_ne).1 hj hχj⟩

end Reducible

/-! ### The classes with irreducible polynomial -/

section Irreducible

variable {E n : Type} [Field E] [CMBase E] [Fintype n] [DecidableEq n] {𝔑 : 𝓞 E}

open Classical in
/-- The signs of `eigenReflection ε y μ` at the roots of `y`, place by place: `-1` at the place
`v₀` and the roots other than `μ` if `ε` holds, and `1` in all other cases. -/
def reflectionSigns (ε : Prop) (μ : n) (v : InfinitePlace E) (i : n) : ℤˣ :=
  if v = v₀ ∧ ε ∧ i ≠ μ then -1 else 1

omit [Fintype n] in
/-- In the definite case all signs are `1`. -/
lemma reflectionSigns_false (μ : n) : reflectionSigns (E := E) False μ = 1 :=
  funext₂ fun v i ↦ by simp [reflectionSigns]

/-- In odd rank the marked signs have product one: `-1` occurs `card n - 1` times. -/
lemma prod_reflectionSigns (hn : Odd (Fintype.card n)) (μ : n) :
    ∏ v : InfinitePlace E, ∏ i : n, reflectionSigns True μ v i = 1 := by
  refine Finset.prod_eq_one fun v _ ↦ ?_
  by_cases hv : v = v₀
  · simpa [reflectionSigns, hv, Finset.prod_ite, Finset.filter_ne'] using
      (hn.tsub_odd odd_one).neg_one_pow (α := ℤˣ)
  · simp [reflectionSigns, hv]

/-- The matrix that enters the sign condition at the infinite place `v` is `p(y)` under the
embedding `Φ v`, where `p` takes the values `reflectionSigns ε μ v` at the numbered roots of the
characteristic polynomial of `y`. -/
lemma ite_eigenReflection_eq (ε : Prop) (y : GL n E) (μ : n) (v : InfinitePlace E) :
    (if v = v₀ then eigenReflection ε y μ else 1) =
      aeval (y.val.map (Φ v)) (Lagrange.interpolate Finset.univ (numberedRoots (Φ v) y.val.charpoly)
        fun i : n ↦ (reflectionSigns ε μ v i : ℂ)) := by
  by_cases h : v = v₀ ∧ ε
  · obtain ⟨rfl, hε⟩ := h
    have h_signs : (fun i : n ↦ (reflectionSigns ε μ (v₀ : InfinitePlace E) i : ℂ)) =
        fun i : n ↦ if i = μ then 1 else -1 := by
      ext i
      by_cases hi : i = μ <;> simp [reflectionSigns, hε, hi]
    rw [ite_eq_left rfl, eigenReflection, ite_eq_left hε, h_signs]
  · -- All signs are `1`, and both sides are the identity matrix.
    have h_signs : (fun i : n ↦ (reflectionSigns ε μ v i : ℂ)) = 1 := by
      ext i; simp [reflectionSigns, ← and_assoc, h]
    rw [h_signs, Lagrange.interpolate_one (numberedRoots (Φ v) y.1.charpoly).injective.injOn
      ⟨μ, Finset.mem_univ μ⟩, map_one]
    refine ite_eq_right_iff.2 fun hv ↦ ?_
    rw [eigenReflection, ite_eq_right fun hε ↦ h ⟨hv, hε⟩, map_one]

/-- Let `y` have irreducible characteristic polynomial, and let `x⁻¹ y⁻¹ x` be a frame for the
scalar form `ν • 1`. Then `x` is a signed frame for `eigenReflection ε y μ` (a frame for some
hermitian form with the positivity that this matrix prescribes at `v₀`) if and only if `y` is an
elliptic similitude of multiplier `ν`, with the signs `reflectionSigns ε μ` at its roots, of a form
whose Gram matrix in the frame `x` is `c • 1` for a unit `c` of the integral adeles `Ô ℚ`. -/
lemma isSignedFrame_iff_hasSignType {x : GL n (𝔸f E)} {y : GL n E} {ν : ℚ}
    (h_irr : Irreducible y.val.charpoly) (hν : IsScalarFrame (invAutInFrame y x) ν) (ε : Prop)
    (μ : n) :
    IsSignedFrame x (eigenReflection ε y μ) ↔ HasSignType (reflectionSigns ε μ) ν y
      {m : Matrix n n (𝔸f E) | ∃ c : (Ô ℚ)ˣ, m = finAdeleIncl ℚ E c • 1} x := by
  have : Nonempty n := ⟨μ⟩
  have h_inv : (x⁻¹ * toFinGL y * x)⁻¹ = invAutInFrame y x := by simp [invAutInFrame, mul_assoc]
  have h_fix : ratConj y (eigenReflection ε y μ) = eigenReflection ε y μ := by
    rw [ratConj_eigenReflection, mul_inv_cancel_right]
  -- For a form `β`, both sides have the same frame condition and the same positivity conditions.
  constructor
  · rintro ⟨β, h_frame, h_pos⟩
    obtain ⟨h_form, h_root⟩ :=
      IsSignedFrameFor.similitude_and_root_norm ⟨h_frame, h_pos⟩ (by rwa [h_inv]) h_fix
    exact ⟨β, ⟨h_irr, hν.1.ne', h_form, h_root⟩, h_frame,
      by simpa only [ite_eigenReflection_eq] using h_pos⟩
  · rintro ⟨β, -, h_frame, h_pos⟩
    exact ⟨β, h_frame, by simpa only [ite_eigenReflection_eq] using h_pos⟩

/-- The term of the marked count: `countTerm` with the sign condition on the class of
`(xK, y, μ)` taken for the reflection attached to the marked root `μ` of `y`. -/
abbrev markedTerm (f : heckeAlgebra n ℂ 𝔑) (w : E[X] → n → ℂ) :
    orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n) → ℂ :=
  countTerm True f w

/-- The term of the definite count: `countTerm` with the sign condition on the class of
`(xK, y, μ)` taken with all signs `+1`. -/
abbrev definiteTerm (f : heckeAlgebra n ℂ 𝔑) (w : E[X] → n → ℂ) :
    orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n) → ℂ :=
  countTerm False f w

/-- Let the rank be odd and let `f` be a Hecke function of level `𝔑`. If the weight `u` vanishes on
the polynomials that are not irreducible, so that only classes with irreducible characteristic
polynomial contribute, the sum over all classes of `markedTerm f u` (`f` times `u`, with the signs
of the marked root) is that of `definiteTerm f u` (the same with all signs `+1`): a change of signs
of the frame matches the classes. -/
lemma finsum_markedTerm_eq_of_irreducible (hn : Odd (Fintype.card n)) (f : heckeAlgebra n ℂ 𝔑)
    {u : E[X] → n → ℂ} (hu : ∀ P : E[X], ¬Irreducible P → u P = 0) :
    ∑ᶠ c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n), markedTerm f u c =
      ∑ᶠ c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n), definiteTerm f u c := by
  classical
  -- The marked signs have product one, so they give a permutation `σ` of the classes, induced on
  -- the triples `(xK, y, μ)` by a move `x ↦ U * x` of the frame, with `U` depending on `y`, `μ`.
  obtain ⟨σ, hσ⟩ :=
    exists_hasSignType_mul_iff (reflectionSigns True) (prod_reflectionSigns hn) (levelGU n 𝔑)
  refine finsum_eq_of_bijective σ σ.bijective ?_
  rintro ⟨⟨x⟩, y, μ⟩
  -- `U` changes the signs, commutes with the centraliser of `y`, and induces `σ` on this orbit.
  obtain ⟨U, hU_type, hU_comm, hU_move⟩ : ∃ U : GL n (𝔸f E),
      (∀ (ν : ℚ) (η : InfinitePlace E → n → ℤˣ) (S : Set (Matrix n n (𝔸f E))) (x : GL n (𝔸f E)),
        HasSignType (η * reflectionSigns True μ) ν y S x ↔ HasSignType η ν y S (U * x)) ∧
      (∀ z : GL n E, Commute y z → Commute (toFinGL z) U) ∧
      ∀ q : GL n (𝔸f E) ⧸ levelGU n 𝔑, σ ⟦(q, y, μ)⟧ = ⟦(U • q, y, μ)⟧ := hσ y μ
  have h_move : σ ⟦markedTriple (levelGU n 𝔑) x y μ⟧ =
      ⟦markedTriple (levelGU n 𝔑) (U * x) y μ⟧ := hU_move x
  -- The move keeps the argument of `f`; it remains to match the two sign conditions.
  have h_aut : invAutInFrame y (U * x) = invAutInFrame y x := by
    have h_comm : Commute (toFinGL y)⁻¹ U := by
      simpa using hU_comm y⁻¹ (Commute.refl y).inv_right
    simp [invAutInFrame, mul_assoc, h_comm.left_comm]
  change countTerm True f u ⟦markedTriple (levelGU n 𝔑) x y μ⟧ =
    countTerm False f u (σ ⟦markedTriple (levelGU n 𝔑) x y μ⟧)
  rw [h_move, markedTriple, markedTriple, countTerm_mk, countTerm_mk, h_aut]
  by_cases h_zero : heckeCosetFn f (invAutInFrame y x) * u y.val.charpoly μ = 0
  · rw [h_zero, ite_self, ite_self]
  have h_irr : Irreducible y.val.charpoly :=
    by_contra fun h ↦ right_ne_zero_of_mul h_zero (congrFun (hu _ h) μ)
  obtain ⟨ν, hν : IsScalarFrame (invAutInFrame y x) ν⟩ :=
    (heckeAlgebra.mem_GUPlus_of_ne_zero (left_ne_zero_of_mul h_zero)).1
  refine if_congr ?_ rfl rfl
  rw [isSignedFrame_iff_hasSignType h_irr hν,
    isSignedFrame_iff_hasSignType (ν := ν) h_irr (by rwa [h_aut]),
    ← hU_type, reflectionSigns_false, one_mul]

end Irreducible

/-! ### The comparison -/

section Comparison

variable {E n : Type} [Field E] [CMBase E] [Fintype n] [DecidableEq n] {𝔑 : 𝓞 E}

/-- The marked and the definite orbit sums agree. Assume that `𝔑` is neat and the rank is odd; that
`f` is a regular Hecke function of level `levelGU n 𝔑`; that in every representation `f` sends
vectors of that level to `χ`-eigenvectors of `J`, acting through `conjAtSplit` at the split place
`w₀`, where `(J, χ)` is a cuspidal type (`χ` is non-trivial on `J` within each proper unipotent
radical); and that with weight `1` finitely many classes have a non-zero marked term and finitely
many a non-zero definite term. Then for every weight `w` the sums over all classes of the marked and
of the definite terms are equal. -/
lemma finsum_markedTerm_eq_finsum_definiteTerm (hN : IsNeat n 𝔑) (hn : Odd (Fintype.card n))
    {f : heckeAlgebra n ℂ 𝔑} (h_regular : IsRegularHecke f) {w₀ : SplitFinPlace E}
    {J : Subgroup (GL n (LocField w₀.1))} {χ : J →* ℂ} (hχ : IsCuspidalType J χ)
    (hJ : f.val ∈ fixedToEigen (levelGU n 𝔑) (conjAtSplit w₀) J χ) (w : E[X] → n → ℂ)
    (h_marked : (markedTerm f 1).support.Finite)
    (h_definite : (definiteTerm f 1).support.Finite) :
    ∑ᶠ c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n), markedTerm f w c =
      ∑ᶠ c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n), definiteTerm f w c := by
  classical
  -- Split `w` into the part `u` on the polynomials that are not irreducible, for which both sums
  -- vanish, and the rest `w - u`, for which a change of signs matches the classes.
  let u (P : E[X]) : n → ℂ := if Irreducible P then 0 else w P
  have h_split (ε : Prop) (h_finite : (countTerm ε f 1).support.Finite) :
      ∑ᶠ c, countTerm ε f w c = ∑ᶠ c, countTerm ε f (w - u) c := by
    have h_red : ∑ᶠ c, countTerm ε f u c = 0 :=
      finsum_countTerm_eq_zero_of_reducible hN h_regular hχ hJ (fun P hP ↦ ite_eq_left hP) ε
    rw [finsum_countTerm_eq_sum u h_finite] at h_red
    simp only [finsum_countTerm_eq_sum _ h_finite, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
      h_red, sub_zero]
  calc ∑ᶠ c, markedTerm f w c = ∑ᶠ c, markedTerm f (w - u) c := h_split True h_marked
    _ = ∑ᶠ c, definiteTerm f (w - u) c :=
      finsum_markedTerm_eq_of_irreducible hn f fun P hP ↦ sub_eq_zero.2 (ite_eq_right hP).symm
    _ = ∑ᶠ c, definiteTerm f w c := (h_split False h_definite).symm

/-- The sums of `countTerm ε f w` over all classes agree for `ε = True` (the marked count) and
`ε = False` (the definite count): the level `𝔑` is neat, the rank is odd, `f` is a regular Hecke
function (its terms vanish unless the characteristic polynomial is separable) of cuspidal type
`(J, χ)` at the split place `w₀`, and with weight `1` finitely many classes have a non-zero term.

Known result: the comparison of orbit sums in the simple trace formula on a definite group. -/
lemma finsum_countTerm_marked_eq_definite (hN : IsNeat n 𝔑) (hn : Odd (Fintype.card n))
    {f : heckeAlgebra n ℂ 𝔑} (h_regular : IsRegularHecke f) {w₀ : SplitFinPlace E}
    {J : Subgroup (GL n (LocField w₀.1))} {χ : J →* ℂ} (hχ : IsCuspidalType J χ)
    (hJ : f.val ∈ fixedToEigen (levelGU n 𝔑) (conjAtSplit w₀) J χ) (w : E[X] → n → ℂ)
    (h_finite : ∀ ε : Prop, (countTerm ε f 1).support.Finite) :
    ∑ᶠ c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n), countTerm True f w c =
      ∑ᶠ c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n), countTerm False f w c :=
  finsum_markedTerm_eq_finsum_definiteTerm hN hn h_regular hχ hJ w (h_finite True) (h_finite False)

end Comparison

end New.Variety

end
