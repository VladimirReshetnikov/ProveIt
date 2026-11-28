import New.Congruences.GaloisRepresentations.SelmerHypotheses
import New.Congruences.LocalLoss.CrystallineCocycles

/-!
# Tame classes from roots of unity and lattices read at a place above ℓ

This file passes local properties of an ℓ-adic representation R of the Galois group of E to lattices
over a coefficient ring O. Classes of polynomials defined by roots of unity are shown to be tame.
Conjugate self-dual representations of given level are shown to be trivial on inertia away from ℓ, M
and their level, where M = p₀p₁ is the product of the primes p₀, p₁ of the data.

## Main definitions and results

* `New.Selmer.isTameType_of_roots`: a class of polynomials containing those that vanish on a given
  multiset of at most N roots of unity of orders dividing ℓ^a - 1, 1 ≤ a ≤ r, is
  `New.Lift.IsTameType`.
* `New.Selmer.localLattice`: a lattice restricted to the decomposition group at a place above ℓ.
* `New.Selmer.IsConjSelfDualOfLevel.hasJumps_localLattice`: a lattice in a conjugate self-dual
  representation of given level has the jumps of the representation at a place above ℓ.
* `New.Selmer.IsConjSelfDualOfLevel.inClass_localLattice`: a lattice in a conjugate self-dual
  representation of given level inherits admissibility at a place above ℓ and, if the place divides
  M, the polynomials that kill inertia.

Notions from other files:
* `New.Data.E`: The field E = K(ζ), ζ a primitive root of unity of order q₁ = 3^c 2^s q₀, for the
  exponent s of the data.
* `New.Selmer.AbsGal`: The absolute Galois group of the field E of the data D: automorphisms of an
  algebraic closure of E fixing E.
* `New.CoeffRing`: Rings of integers of finite Galois extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`.
* `New.Selmer.IsConjSelfDualOfLevel`: R is conjugate self-dual, and at every place outside the level
  S or above ℓ M it is of finite type, has the prescribed jumps, and is good away from M.
* `New.Lift.InClass`: a lattice over O at a place above ℓ is admissible along the supremum of a
  given filter and the filter near 1, has its jumps in given sets, and inertia elements are killed
  on its periods by given polynomials.

## Relation to the literature

See `New.Congruences.FirstOrder.RibetElement` for related work.
-/

namespace New.Selmer

open Period Lift Polynomial GaloisRep Multiset minpoly Pi Filter Function

variable {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ] {O : CoeffRing ℓ}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Let M be a multiset of at most N elements of ℚ̄_ℓ, each a root of X^(ℓ^a − 1) − 1 for some
1 ≤ a ≤ r, and K a property of polynomials over O that holds for all those vanishing on M. Then
`IsTameType ℓ r (N * r) K` holds, that is, K holds for X^e − 1, with e the least common multiple of
the ℓ^i − 1 for 1 ≤ i ≤ r, and for (the image over O of) some monic polynomial over ℤ_ℓ of degree
at most Nr. -/
lemma isTameType_of_roots {N r : ℕ} {K : O[X] → Prop} {M : Multiset (PadicAlgCl ℓ)}
    (h_card : card M ≤ N) (h_root : ∀ y ∈ M, ∃ a ∈ Set.Icc 1 r, y ^ (ℓ ^ a - 1) = 1)
    (hK : ∀ Q : O[X], (∀ y ∈ M, Q.aeval y = 0) → K Q) :
    Lift.IsTameType ℓ r (N * r) K := by
  -- A root of `y ^ (ℓ ^ a - 1) = 1` is a Teichmüller lift in the unramified ring of degree `a ≤ r`,
  -- so its minimal polynomial over `ℤ_[ℓ]` is monic of degree at most `r`; take their product.
  have h_minpoly (y : PadicAlgCl ℓ) (hy : y ∈ M) :
      (minpoly ℤ_[ℓ] y).Monic ∧ (minpoly ℤ_[ℓ] y).natDegree ≤ r := by
    obtain ⟨a, ⟨ha_pos, ha_le⟩, hya⟩ := h_root y hy
    obtain ⟨x, hx⟩ : ∃ x : flatFq (a.toPNat ha_pos),
        wittToQpBar (WittVector.teichmuller ℓ x) = y :=
      exists_flatFq_teichmuller_eq (f := a.toPNat ha_pos) wittToQpBar.toRingHom y fun _ ↦ hya
    rw [← hx, minpoly.algHom_eq _ wittToQpBar_injective]
    refine ⟨minpoly.monic (.of_finite ℤ_[ℓ] _), ?_⟩
    calc
      _ ≤ Module.finrank ℤ_[ℓ] (WittFq (a.toPNat ha_pos)) := minpoly.natDegree_le _
      _ ≤ a := KummerChart.JumpLattice.finrank_wittFq.le
      _ ≤ r := ha_le
  let q : ℤ_[ℓ][X] := (M.map (minpoly ℤ_[ℓ])).prod
  have hq_monic : q.Monic := monic_multiset_prod_of_monic _ _ fun y hy ↦ (h_minpoly y hy).1
  have hq_natDegree : q.natDegree ≤ N * r :=
    calc
      q.natDegree ≤ ((M.map (minpoly ℤ_[ℓ])).map natDegree).sum := natDegree_multiset_prod_le _
      _ ≤ card M * r := by
        simpa using sum_map_le_sum_map _ (fun _ ↦ r) fun y hy ↦ (h_minpoly y hy).2
      _ ≤ N * r := by gcongr
  refine ⟨hK _ fun y hy ↦ ?_, q, hq_monic, hq_natDegree, hK _ fun y hy ↦ ?_⟩
  · obtain ⟨a, ha, hya⟩ := h_root y hy
    obtain ⟨c, hc⟩ : ℓ ^ a - 1 ∣ (Finset.Icc 1 r).lcm fun i : ℕ ↦ ℓ ^ i - 1 :=
      Finset.dvd_lcm (by simpa)
    simp [hc, pow_mul, hya]
  · simpa [q, map_multiset_prod] using ⟨y, hy, minpoly.aeval ℤ_[ℓ] y⟩

/-- The lattice of `ρ` restricted to the decomposition group at the place `v` above `ℓ`. -/
noncomputable abbrev localLattice {m : Type} [Fintype m] [DecidableEq m]
    (ρ : AbsGal D →* Matrix m m O) (v : placesDividing D.E ℓ) :
    Lift.GalLattice O (decompGroup (AbsGal D) (placeOver v.val)) :=
  matrixLattice (ρ.comp (decompGroup (AbsGal D) (placeOver v.val)).subtype)

/-- Let u be a lattice in R, that is, conjugate to R over ℚ̄_ℓ. Then there is an injective map F
from Oⁿ to ℚ̄_ℓⁿ that is semilinear for the inclusion `O.val.val` of O, sends the standard basis to
a basis, and carries the action of u to that of R. -/
lemma IsLatticeIn.exists_equivariant_embedding {u : AbsGal D →* Matrix n n O} {R : GalRep ℓ D.E n}
    (hu : IsLatticeIn R u) :
    ∃ (F : (n → ↑O) →ₗ[ℤ_[ℓ]] (n → PadicAlgCl ℓ))
      (b : Module.Basis n (PadicAlgCl ℓ) (n → PadicAlgCl ℓ)),
      (∀ x : n → ↑O, F x = 0 → x = 0) ∧
      (∀ (a : ↑O) (x : n → ↑O), F (a • x) = O.val.val a • F x) ∧
      (∀ i : n, F (basisFun O n i) = b i) ∧
      ∀ (g : AbsGal D) (x : n → ↑O), F ((u g).mulVec x) = matrixRep R g (F x) := by
  -- `F` is the inclusion `O ^ n → ℚ̄_ℓ ^ n` followed by the change of basis `B`.
  obtain ⟨B, hB⟩ := hu
  let L : (n → PadicAlgCl ℓ) ≃ₗ[PadicAlgCl ℓ] (n → PadicAlgCl ℓ) := B.toLin.toLinearEquiv
  let F : (n → ↑O) →ₗ[ℤ_[ℓ]] (n → PadicAlgCl ℓ) :=
    L.toLinearMap.restrictScalars ℤ_[ℓ] ∘ₗ O.val.val.toLinearMap.compLeft n
  refine ⟨F, (basisFun (PadicAlgCl ℓ) n).map L, by simp [F, funext_iff],
    fun a x ↦ L.map_smul (O.val.val a) (O.val.val ∘ x), fun i ↦ ?_, fun g x ↦ ?_⟩
  · simp [F, funext_iff, single_apply, apply_ite]
  · calc
      F ((u g).mulVec x) = L (((u g).map O.val.val).mulVec (O.val.val ∘ x)) :=
        congrArg L (funext (O.val.val.toRingHom.map_mulVec (u g) x))
      _ = matrixRep R g (L (O.val.val ∘ x)) := by
        -- `-Subalgebra.coe_val` keeps `O.val.val` in the form in which `hB` states it
        simp [← hB, L, matrixRep, mul_assoc, -Subalgebra.coe_val]

/-- Let u be a lattice in R over O, w a place of E above ℓ, and 𝓕 a filter on the decomposition
group at w that is coarser than `nearOne`, the filter of neighbourhoods of 1 pulled back from
Gal(ℚ̄_ℓ/ℚ_ℓ). A representation on T is admissible along 𝓕 if the elements of B_max ⊗ T fixed by
𝓕-almost all group elements span it over B_max. If R at w is admissible along 𝓕, then so is u at
w. -/
lemma IsLatticeIn.isAdmissible_localLattice {u : AbsGal D →* Matrix n n O} {R : GalRep ℓ D.E n}
    (hu : IsLatticeIn R u) {w : placesDividing D.E ℓ}
    {𝓕 : Filter (decompGroup (AbsGal D) (placeOver w.val))}
    (h_le : nearOne (decompGroup (AbsGal D) (placeOver w.val)) ≤ 𝓕)
    (h_adm : Period.IsAdmissible (decompRep R (placeOver w.val)) 𝓕) :
    Period.IsAdmissible (localLattice u w).ρ 𝓕 := by
  obtain ⟨F, -, F_inj, -, -, F_mulVec⟩ := hu.exists_equivariant_embedding
  -- the family of jointly injective maps consists of the single map `F`
  exact .of_jointly_injective h_le (fun _ : Unit ↦ h_adm) (fun _ ↦ F)
    (fun _ ↦ .of_forall fun s ↦ F_mulVec s) fun x hx ↦ F_inj x (hx ())

/-- Let u be a lattice in R over O and w a place of E above ℓ. Let (s, m) be a Weil pair: s, in the
decomposition group at w, acts on the residue field of ℚ̄_ℓ as x ↦ x^(1/ℓ^m). A polynomial kills (s,
m) on a representation ρ on T (`IsKilledBy`) if ρ is potentially crystalline and the polynomial
vanishes at the B_max-linear operator on B_max ⊗ T that extends φ^m s ⊗ ρ(s), with φ the Frobenius,
from the elements fixed by all g near 1. If the polynomial Q over O, read in ℚ̄_ℓ, kills (s, m) on R
at w, then Q kills (s, m) on u at w. -/
lemma IsLatticeIn.isKilledBy_localLattice {u : AbsGal D →* Matrix n n O} {R : GalRep ℓ D.E n}
    (hu : IsLatticeIn R u) {w : placesDividing D.E ℓ}
    {s : decompGroup (AbsGal D) (placeOver w.val)} {m : ℕ} {Q : O[X]}
    (hs : IsWeilPair (OverGp.toGp s : Gp ℓ) m)
    (h_kills : IsKilledBy (decompRep R (placeOver w.val)) s m (Q.map O.val.val)) :
    IsKilledBy (localLattice u w).ρ s m Q := by
  obtain ⟨F, -, F_inj, F_smul, -, F_mulVec⟩ := hu.exists_equivariant_embedding
  -- the family of jointly injective maps consists of the single map `F`, equivariant for all `g`
  exact .of_jointly_injective hs (fun _ ↦ F) (fun _ ↦ .of_forall fun g ↦ F_mulVec g)
    (fun x hx ↦ F_inj x (hx ())) le_top (fun _ : Unit ↦ h_kills) rfl fun _ ↦ F_smul

variable [PadicIso ℓ]

/-- Fix an isomorphism ℂ ≅ ℚ̄_ℓ (`PadicIso ℓ`), let p₀, p₁ be the primes of the data D and M = p₀p₁,
so that `placesAboveM D` is the set of places of E above p₀ or p₁. Let R be a conjugate self-dual
representation of level S: R is conjugate self-dual up to a twist given by t, and local conditions
hold at the places outside S or dividing ℓM, among them the jumps τ, read through this isomorphism.
Then R is trivial on every inertia group above a place of E that is outside S and does not divide
ℓM. -/
lemma IsConjSelfDualOfLevel.eq_one_of_mem_inertiaAbove {τ : (D.E →+* ℂ) → Multiset ℤ} {t : ℕ}
    {S : Set (FinPlace D.E)} {R : GalRep ℓ D.E n} (h_selfDual : IsConjSelfDualOfLevel D t τ S R) :
    ∀ g ∈ inertiaAbove (placesDividing D.E ℓ ∪ placesAboveM D ∪ S)ᶜ, R g = 1 := by
  -- at such a place `GaloisRep.IsGoodAt R A` holds and `ℓ` is a unit, so `R` is trivial on inertia
  rintro g ⟨v, hv, A, hA, hg⟩
  simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hv
  obtain ⟨⟨hvℓ, hvM⟩, hvS⟩ := hv
  obtain ⟨-, -, h_good⟩ := h_selfDual.local_conditions v (by simp [hvS]) hA
  have h_unit : A.valuation (ℓ : Ω) = 1 := by
    simpa [hA.valuation_natCast_eq_one_iff, placesDividing] using hvℓ
  obtain ⟨h_unramified, -⟩ := h_good hvM
  exact h_unramified h_unit g hg

/-- The complex embedding ι⁻¹ ∘ g⁻¹ ∘ e of E, where e : E → ℚ̄_ℓ is the embedding attached to the
place w above ℓ, g is in Gal(ℚ̄_ℓ/ℚ_ℓ), and ι is the isomorphism ℂ ≅ ℚ̄_ℓ of `PadicIso ℓ`. -/
noncomputable abbrev complexEmbeddingAt (w : placesDividing D.E ℓ) (g : Gp ℓ) : D.E →+* ℂ :=
  complexEmbeddingOf ((localChart ℓ D.E w).e.comp (algebraMap D.E Ω)) g

/-- The filter `⊥` if the place w above ℓ lies above p₀ or p₁, and `⊤` otherwise. A conjugate
self-dual representation of given level is admissible at w along its supremum with the filter near
1: potentially crystalline in the first case, crystalline in the second. -/
noncomputable def crystallinityFilter (w : placesDividing D.E ℓ) :
    Filter (decompGroup (AbsGal D) (placeOver w.val)) :=
  ⨅ _ : w.val ∈ placesAboveM D, ⊥

/-- The place w lies above one of the primes p₀, p₁ of the data, and the polynomial Q over O kills
the pair (s, 0) on every representation in the class 𝓡, restricted to the decomposition group at w
(`New.Period.IsKilledBy`). -/
def KillsAboveM (𝓡 : GalRep ℓ D.E n → Prop) (w : placesDividing D.E ℓ)
    (s : decompGroup (AbsGal D) (placeOver w.val)) (Q : O[X]) : Prop :=
  w.val ∈ placesAboveM D ∧
    ∀ R : GalRep ℓ D.E n, 𝓡 R → IsKilledBy (decompRep R (placeOver w.val)) s 0 (Q.map O.val.val)

/-- The set of members of τ at `complexEmbeddingAt w g`, for a chosen g in Gal(ℚ̄_ℓ/ℚ_ℓ) that
induces the embedding γ of O. -/
noncomputable def jumpSetAt (τ : (D.E →+* ℂ) → Multiset ℤ) (w : placesDividing D.E ℓ)
    (γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) : Finset ℤ :=
  (τ (complexEmbeddingAt w (surjInv coefficientEmbedding_surjective γ))).toFinset

/-- Fix an isomorphism ι : ℂ ≅ ℚ̄_ℓ (`PadicIso ℓ`). Let R be a conjugate self-dual representation of
given level with jumps τ, u a lattice in R over O, w a place of E above ℓ with its chosen embedding
e : E → ℚ̄_ℓ, and g in Gal(ℚ̄_ℓ/ℚ_ℓ). Then the Hodge–Tate jumps of u at w, at the embedding x ↦ g(x)
of O in ℂ_ℓ and with multiplicity, are the value of τ at the complex embedding ι⁻¹ ∘ g⁻¹ ∘ e of E
(`complexEmbeddingAt w g`). -/
lemma IsConjSelfDualOfLevel.hasJumps_localLattice {τ : (D.E →+* ℂ) → Multiset ℤ}
    {u : AbsGal D →* Matrix n n O} {R : GalRep ℓ D.E n} {t : ℕ} {S : Set (FinPlace D.E)}
    (h_selfDual : IsConjSelfDualOfLevel D t τ S R) (hu : IsLatticeIn R u)
    (w : placesDividing D.E ℓ) (g : Gp ℓ) :
    HasJumps (localLattice u w).ρ (coefficientEmbedding O g) (τ (complexEmbeddingAt w g)) := by
  -- Jumps are unchanged by extension of scalars from `O` to `ℚ̄_ℓ`.
  obtain ⟨-, h_jump, -⟩ := h_selfDual.local_conditions w.val (by simp) w.val.isPlaceOver_placeOver
  obtain ⟨F, b, -, F_smul, F_basis, F_mulVec⟩ := hu.exists_equivariant_embedding
  have F_equivariant (s : decompGroup (AbsGal D) (placeOver w.val)) (x : n → ↑O) :
      F ((localLattice u w).ρ s x) = decompRep R (placeOver w.val) s (F x) := F_mulVec s x
  intro i
  -- `coefficientEmbedding O g` is the restriction to `O` of the map that reads `ℚ̄_ℓ` in `ℂ_ℓ`
  -- through `g`
  rw [coefficientEmbedding, ← jump_baseChange ⟨F.toAddHom, F_smul⟩ (basisFun O n) b F_basis
    (.of_forall F_equivariant)]
  exact (h_jump (g := g) (fun _ ↦ rfl) i).symm

/-- Fix an isomorphism ℂ ≅ ℚ̄_ℓ (`PadicIso ℓ`), and let p₀, p₁ be the primes of the data D. Let R be
a conjugate self-dual representation of level S with jumps τ that belongs to a class 𝓡 of
representations, u a lattice in R over O, and w a place of E above ℓ. Then u at w satisfies the
three conditions of `New.Lift.InClass`.
* It is potentially crystalline, and crystalline unless w lies above p₀ or p₁.
* At each embedding γ of O in ℂ_ℓ, its Hodge–Tate jumps lie in `jumpSetAt τ w γ`: the set of members
  of the multiset τ at the complex embedding `complexEmbeddingAt w g`, for a chosen g in
  Gal(ℚ̄_ℓ/ℚ_ℓ) that induces γ.
* Suppose w lies above p₀ or p₁ and s is in the inertia group at w. Let Q be a polynomial over O
  such that every member of 𝓡 is potentially crystalline at w and Q vanishes at its operator of s,
  the B_max-linear map on B_max ⊗ T that extends the action of s on the elements fixed by some open
  subgroup of the Galois group (`KillsAboveM 𝓡 w s Q`; T is the space of the representation, B_max
  the period ring `Bmax`). Then Q vanishes at the operator of s for u. -/
lemma IsConjSelfDualOfLevel.inClass_localLattice {τ : (D.E →+* ℂ) → Multiset ℤ}
    {u : AbsGal D →* Matrix n n O} {R : GalRep ℓ D.E n} {t : ℕ} {S : Set (FinPlace D.E)}
    {𝓡 : GalRep ℓ D.E n → Prop} (h_selfDual : IsConjSelfDualOfLevel D t τ S R) (hR : 𝓡 R)
    (hu : IsLatticeIn R u) (w : placesDividing D.E ℓ) :
    InClass (crystallinityFilter w) (KillsAboveM 𝓡 w) (jumpSetAt τ w) (localLattice u w) := by
  refine ⟨?_, fun γ i hi ↦ ?_, fun s Q ⟨_, h_kills⟩ hs ↦ ?_⟩
  · -- `R` is potentially crystalline at `w`, and crystalline if `w` is not in `placesAboveM D`
    obtain ⟨⟨-, h_potCrys⟩, -, h_good⟩ :=
      h_selfDual.local_conditions w.val (by simp) w.val.isPlaceOver_placeOver
    refine hu.isAdmissible_localLattice le_sup_left ?_
    by_cases hw : w.val ∈ placesAboveM D
    · simp [crystallinityFilter, hw, h_potCrys]
    · obtain ⟨-, h_crys⟩ := h_good hw
      simp [crystallinityFilter, hw, h_crys]
  · -- a jump of nonzero multiplicity at `γ` is a member of `τ` at any `g` that induces `γ`
    let g : Gp ℓ := surjInv coefficientEmbedding_surjective γ
    have hg : coefficientEmbedding O g = γ := surjInv_eq coefficientEmbedding_surjective γ
    have h_count : jump (localLattice u w).ρ γ i = count i (τ (complexEmbeddingAt w g)) := by
      simpa only [hg] using h_selfDual.hasJumps_localLattice hu w g i
    rwa [jumpSetAt, mem_toFinset, ← count_ne_zero, ← h_count]
  · -- `Q` kills `s` on every member of `𝓡`, in particular on `R`
    exact hu.isKilledBy_localLattice hs (h_kills R hR)

/-- Let R be a conjugate self-dual representation of level S with jumps τ that belongs to a class 𝓡
of representations, u a lattice in R over O and w a place of E above ℓ. Then for each g in
Gal(ℚ̄_ℓ/ℚ_ℓ) the Hodge–Tate jumps of u at w, at the embedding x ↦ g(x) of O, are the value of τ at
`complexEmbeddingAt w g`. Also u at w satisfies `New.Lift.InClass`: it is potentially crystalline,
and crystalline unless w lies above one of the primes p₀, p₁ of the data; its jumps lie in the sets
`jumpSetAt τ w` of members of τ; and if w lies above p₀ or p₁, a polynomial over O that kills an
inertia element on every member of 𝓡 kills it on u. -/
lemma hasJumps_and_inClass_localLattice {τ : (D.E →+* ℂ) → Multiset ℤ}
    {u : AbsGal D →* Matrix n n O}
    {R : GalRep ℓ D.E n} {t : ℕ} {S : Set (FinPlace D.E)} (w : placesDividing D.E ℓ)
    {𝓡 : GalRep ℓ D.E n → Prop} (h_selfDual : IsConjSelfDualOfLevel D t τ S R) (hR : 𝓡 R)
    (hu : IsLatticeIn R u) :
    (∀ g : Gp ℓ, HasJumps (localLattice u w).ρ (coefficientEmbedding O g)
      (τ (complexEmbeddingAt w g))) ∧
      InClass (crystallinityFilter w) (KillsAboveM 𝓡 w) (jumpSetAt τ w) (localLattice u w) :=
  ⟨h_selfDual.hasJumps_localLattice hu w, h_selfDual.inClass_localLattice hR hu w⟩

end New.Selmer
