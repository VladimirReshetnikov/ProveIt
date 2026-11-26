import Lib.PadicHodge.BlochKato
import New.Congruences.FirstOrder.EvenClasses
import New.Congruences.FirstOrder.FittingBlock

/-!
# Cocycles of Tate twists: the even part and the triangle cost

This file studies cocycles of `Gal(Ω/E)` with values in a twist `(O/ℓ^ν)(-e)`
(`New.Selmer.tateTwist`). It shows that the even part of a cocycle lies in the even classes.
It shows that a cocycle that obeys the crystalline relations above `ℓ` vanishes on
`New.Selmer.shaLocalSet`. It also shows that a triangle of primes gives a triangle cost.

## Main definitions and results

* `New.Selmer.add_conjGal_mem_evenClasses`: let `e ≠ 0`, and let a cocycle with values in
  `(O/ℓ^ν)(-e)` be unramified off ℓ, S and S̄ and zero on `New.Selmer.shaLocalSet`. Then its even
  part `c + c ∘ New.conjGal` lies in `New.Selmer.evenClasses`.
* `New.Selmer.hasTriangleCost_tateTwist`: let the tame generator family `w j`, with elements `τ j`,
  `φ j` and exponents `ty j`, form a triangle for `g₀` that holds up to `ℓ ^ h`
  (`New.Selmer.IsPrimeTriangle`), and let `e < t`. Let `Z` be a module of cocycles with values in
  `(O/ℓ^ν)(-e)`, unramified off `ℓ`, the `w j` and their conjugates, and let
  `cyclotomicInv g₀ ^ e - 1` kill the value at `g₀` of each member unramified off `ℓ`. Then the
  triangle cost of `Z` (`New.Selmer.HasTriangleCost`) is bounded by its length relative to the
  cocycles obeying the crystalline relations plus the length of the odd classes.

Notions from other files:
* `New.Selmer.tateTwist`: the rank-one representation `O(-e)`, given by the power `e` of the inverse
  `New.Selmer.cyclotomicInv` of the cyclotomic character. `New.conjGal`: the map g ↦ g^c = cgc,
  with c the chosen complex conjugation.
* `New.Selmer.shaLocalSet`: the union of the inertia groups above `ℓ` if `e = 0`; otherwise the
  elements of the decomposition groups above `ℓ` with trivial cyclotomic character.
* `New.Selmer.evenClasses`, `New.Selmer.shaOdd`: cocycles in `(O/ℓ^ν)(-e)` with local conditions
  above `ℓ`. Even classes are invariant under `New.conjGal`; odd classes are unramified off `ℓ` and,
  if `e ≠ 0`, change sign under it.
* `New.Selmer.IsPrimeTriangle`: a linearly ordered tame generator family `w j` with monotone
  exponents `ty j`. An even class of exponent `ty j` that kills the earlier `τ i`, and the earlier
  `φ i` of the same exponent, has its value at `τ j` killed by `ℓ ^ h`. Finitely many test points
  and `g₀` detect the cocycles unramified off `ℓ`, and `g₀` separates the characters up to `ℓ ^ h`.
* `New.Selmer.HasTriangleCost Z τ τ' φ φ' I C b`: for the members `Z₀` of `Z` that vanish on some
  set, agreement at the earlier pairs `τ i`, `τ' i` and, for `i ∈ I`, `φ i`, `φ' i` gives agreement
  at `τ j`, `τ' j` up to `C` for `j ∈ I`. The length of `Z / Z₀`, plus the length modulo `C`-torsion
  of any submodule of `Z₀` that is zero at all `τ j`, `τ' j` and agrees at the `φ j`, `φ' j` with
  `j ∈ I`, is at most `b`.

## Relation to the literature

See `New.Congruences.FirstOrder.RibetElement` for related work.
-/

namespace New.Selmer

section TateTwistSteps

open LinearMap Module Finset

variable {ℓ : ℕ} [ThePrime ℓ] {E J : Type} [Field E] [CMFieldWithRoot5040 E] {O : CoeffRing ℓ}

/-- Let `e ≠ 0`, and let `c` be a continuous cocycle with values in `(O/ℓ^ν)(-e)` that is unramified
outside `ℓ` and `S ∪ S̄` and vanishes on `shaLocalSet ℓ E e`. Then the even part `c + c ∘ conjGal`,
with `conjGal` conjugation by complex conjugation, is an even class (`evenClasses`): a cocycle with
the same properties that is invariant under `conjGal`. -/
lemma add_conjGal_mem_evenClasses {e ν : ℕ} {S : Set (FinPlace E)}
    {c : Gal(Ω/E) → Unit → QuotSpan (ℓ ^ ν : ↑O)} (he : e ≠ 0)
    (hc_sel : c ∈ selmerModule (tateTwist ℓ E O e) (placesDividing E ℓ ∪ S.conjClosure) ∅
      (QuotSpan (ℓ ^ ν : ↑O)))
    (hc_local : ∀ g ∈ shaLocalSet ℓ E e, c g = 0) : c + c ∘ conjGal ∈ evenClasses O S ν e := by
  -- Conjugation fixes `cyclotomicChar` and permutes the places above `ℓ` and those of
  -- `S.conjClosure`; so `c ∘ conjGal` has the properties assumed of `c`, and the sum is invariant
  -- under `conjGal`.
  obtain ⟨h_cocycle, h_unram, -, h_locConst⟩ := mem_selmerModule_iff.1 hc_sel
  -- for `e ≠ 0` the set `shaLocalSet ℓ E e` does not depend on `e`
  have h_loc : ∀ g ∈ shaLocalSet ℓ E 1, c g = 0 := by simpa [shaLocalSet, he] using hc_local
  refine ⟨mem_selmerModule_iff.2 ⟨fun g g' ↦ ?_, fun g hg ↦ ?_, by simp [mem_obeying],
    h_locConst.add (h_locConst.comp_continuous continuous_conjGal)⟩,
    fun g ↦ by simp [add_comm], fun g hg ↦ ?_⟩
  · -- the cocycle identity: `g` and `conjGal g` act alike on the twist
    simp [h_cocycle, add_add_add_comm, tateTwist, cyclotomicInv]
  · -- `conjGal g` lies in the inertia group of the conjugate place, which is again outside
    have ⟨v, hv, A, hA, hgA⟩ := hg
    have hv_star : star v ∉ placesDividing E ℓ ∪ S.conjClosure := by
      simpa [star_mem_placesDividing, and_comm] using hv
    have h_conj : c (conjGal g) = 0 :=
      h_unram _ ⟨star v, hv_star, conjPlace A, hA.conjPlace_star, hgA.conjPlace_conjGal⟩
    simp [h_unram g hg, h_conj]
  · -- `conjGal g` lies in the kernel of `cyclotomicChar` and in the decomposition group of the
    -- conjugate place
    have ⟨A, hA, hgA, h_cyc⟩ := hg
    have h_conj_mem : conjGal g ∈ shaLocalSet ℓ E 1 := ⟨conjPlace A, comap_apply_lt_one_iff.2
      (by simpa using hA), decompGroup.map cmConj_conjGal_smul hgA, by simpa using h_cyc⟩
    simp [h_loc g hg, h_loc _ h_conj_mem]

open Matrix.Module in
/-- Let `τ j` be tame generators at places `w j` off `ℓ`, and let the `φ j` fix the `ℓ ^ ν`-th roots
of unity (`IsTameGeneratorFamily`), so that all of them act trivially on `(O/ℓ^ν)(-e)`. Let `z` be a
cocycle with values there. Then the value of `z` at `(conjGal (τ j))⁻¹`, which is
`withConjInv τ (j, false)`, is `-z (conjGal (τ j))`, and likewise for `φ j`. -/
lemma apply_withConjInv_false_eq_neg {e ν : ℕ} {w : J → FinPlace E} {τ φ : J → Gal(Ω/E)}
    (hw : IsTameGeneratorFamily ν w τ φ) {z : Gal(Ω/E) → Unit → QuotSpan (ℓ ^ ν : ↑O)}
    (h_coc : ∀ g g' : Gal(Ω/E), z (g * g') = z g + tateTwist ℓ E O e g • z g') (j : J) :
    z (withConjInv τ (j, false)) = -z (conjGal (τ j)) ∧
      z (withConjInv φ (j, false)) = -z (conjGal (φ j)) := by
  -- The cyclotomic character is `1` at `τ j`, and `1` modulo `ℓ ^ ν` at `φ j`. Where the action is
  -- trivial, `z g⁻¹ = -z g`.
  obtain ⟨h_eq_one, h_dvd⟩ : cyclotomicInv ℓ E O (withConjInv τ (j, false)) = 1 ∧
      ∀ i : ℕ, (ℓ ^ ν : ↑O) ∣ cyclotomicInv ℓ E O (withConjInv φ (j, false)) ^ i - 1 :=
    hw.cyclotomicInv_withConjInv_eq_one_and_dvd O (j, false)
  have h_τ : cyclotomicChar Ω ℓ (τ j) = 1 := by simpa [cyclotomicInv, idOrConjInv] using h_eq_one
  have h_φ (x : QuotSpan (ℓ ^ ν : ↑O)) :
      algebraMap ℤ_[ℓ] O (cyclotomicChar Ω ℓ (φ j)) ^ e • x = x := by
    simpa [cyclotomicInv, idOrConjInv, sub_smul, sub_eq_zero] using
      smul_quot_eq_zero_of_dvd (h_dvd e) x
  constructor
  · simp [cocycle_apply_inv h_coc, h_τ, idOrConjInv, tateTwist, cyclotomicInv]
  · simp [cocycle_apply_inv h_coc, h_φ, idOrConjInv, tateTwist, cyclotomicInv, funext_iff]

open Matrix.Module in
/-- Let `z` be a cocycle of `Gal(Ω/E)` with values in `(O/ℓ^ν)(-e)`, the Tate twist `O(-e)` modulo
`ℓ^ν`, that obeys the linear relations `crysRelations` of the crystalline cocycles at each place
above `ℓ`. Then `z` vanishes on `shaLocalSet ℓ E e`: on the inertia groups above `ℓ` if `e = 0`, and
otherwise on the elements of the decomposition groups above `ℓ` with trivial cyclotomic
character. -/
lemma apply_eq_zero_of_mem_obeying_crysRelations {e ν : ℕ}
    {z : Gal(Ω/E) → Unit → QuotSpan (ℓ ^ ν : ↑O)}
    (h_coc : ∀ g g' : Gal(Ω/E), z (g * g') = z g + tateTwist ℓ E O e g • z g')
    (h_crys : z ∈ obeying (crysRelations (tateTwist ℓ E O e)) (QuotSpan (ℓ ^ ν : ↑O)))
    {g : Gal(Ω/E)} (hg : g ∈ shaLocalSet ℓ E e) : z g = 0 := by
  -- Conjugate `g` by some `s` into the decomposition group of the chosen place `placeOver v`.
  -- Crystalline cocycles vanish at `s * g * s⁻¹`, so this element alone is a local relation.
  obtain ⟨A, hA, hg⟩ := hg
  obtain ⟨v, hv⟩ := exists_isPlaceOver_of_val_ne_one E NeZero.out hA.ne
  obtain ⟨s, hs⟩ := hv.exists_smul Gal(Ω/E) v.isPlaceOver_placeOver
  obtain ⟨h_dec, h_one, h_ine⟩ : g ∈ decompGroup Gal(Ω/E) A ∧ tateTwist ℓ E O e g = 1 ∧
      (e = 0 → g ∈ inertiaGroup Gal(Ω/E) A) := by
    split_ifs at hg with he
    · exact ⟨hg.1, by simp [*, tateTwist, cyclotomicInv]⟩
    · exact ⟨hg.1, by simp [*, tateTwist, cyclotomicInv]⟩
  have h_dec' : s * g * s⁻¹ ∈ decompGroup Gal(Ω/E) (placeOver v) := by
    simpa only [hs] using conj_mem_decompGroup_smul (g := s) h_dec
  have h_one' : tateTwist ℓ E O e (s * g * s⁻¹) = 1 := (MonoidHom.normal_ker _).1 g h_one s
  have h_ine' (he : e = 0) : s * g * s⁻¹ ∈ inertiaGroup Gal(Ω/E) (placeOver v) := by
    rw [← hs]
    exact IsFrob.conj (h_ine he) s
  let vℓ : placesDividing E ℓ := ⟨v, hv.valuation_natCast_lt_one_iff.1 hA⟩
  have h_zero y (hy : y ∈ crysCocyclesAt vℓ (tateTwist ℓ E O e)) : y ⟨s * g * s⁻¹, h_dec'⟩ = 0 :=
    Period.crysCocycles.apply_eq_zero_of_cyclotomicGp (𝒥 := _) (tateTwist_smul e) hy
      (LinearMap.ext (by simp [h_one']))
      fun he ↦ (localChart ..).isWeilPair_zero_iff.2 (h_ine' he)
  have h_conj : z (s * g * s⁻¹) = 0 := by
    let rel : decompGroup Gal(Ω/E) (placeOver v) →₀ Matrix Unit Unit O :=
      .single ⟨s * g * s⁻¹, h_dec'⟩ 1
    simpa [rel] using mem_obeying.1 h_crys _
      ⟨_, ⟨vℓ, rfl⟩, rel, fun y hy ↦ by simp [rel, h_zero y hy], rfl⟩
  -- Compute `z (s⁻¹ * (s * g * s⁻¹)) = z (g * s⁻¹)` in two ways.
  simpa [← mul_assoc, h_coc g, h_one, h_conj] using h_coc s⁻¹ (s * g * s⁻¹)

/-- Let the places `w j` off `ℓ`, with tame generators `τ j`, elements `φ j` and exponents
`0 < ty j < t`, form a triangle of primes for `g₀` (`IsPrimeTriangle`). The following is used:
`4 (cyclotomicInv g₀ ^ e - 1) ^ 2` divides `ℓ ^ h`; there are finitely many test points in the
Galois group such that a cocycle unramified off `ℓ` that vanishes at them and at `g₀` is zero; and
at each test point twice the value of an even class of exponent `e` unramified off `ℓ`
(`evenClasses`) is its value at some `φ j` with `ty j = e`. Let `0 < e < t`, and let `S` be a module
of cocycles for `O(-e)` modulo `ℓ^ν`, unramified off `ℓ` and zero on `shaLocalSet ℓ E e`, whose
values at `g₀` are killed by `cyclotomicInv g₀ ^ e - 1` and whose even parts vanish at the `φ j`
with `ty j = e`. Then the length of `S` modulo its `ℓ^h`-torsion (`relLength`) is at most that of
`shaOdd`, the cocycles with the same local conditions that change sign under `conjGal`. -/
lemma relLength_torsionBy_le_length_shaOdd [Fintype J] [LinearOrder J] {ν : ℕ}
    {w : J → FinPlace E} {τ φ : J → Gal(Ω/E)} {t : ℕ} {g₀ : Gal(Ω/E)} {h c : ℕ} {e : Fin t}
    {ty : J →o {k : Fin t // 0 < k.val}} (h_tri : IsPrimeTriangle ν w τ φ g₀ t ty h c)
    (he : e.val ≠ 0) {S : Submodule O (Gal(Ω/E) → Unit → QuotSpan (ℓ ^ ν : ↑O))}
    (hS_g₀ : ∀ z ∈ S, (cyclotomicInv ℓ E O g₀ ^ e.val - 1) • z g₀ = 0)
    (hS_unr : ∀ z ∈ S, z ∈ selmerModule (tateTwist ℓ E O e) (placesDividing E ℓ) ∅
      (QuotSpan (ℓ ^ ν : ↑O)))
    (hS_loc : ∀ z ∈ S, ∀ g ∈ shaLocalSet ℓ E e, z g = 0)
    (hS_φ : ∀ z ∈ S, ∀ j : J, (ty j).val = e → (z + z ∘ conjGal) (φ j) = 0) :
    relLength S (Submodule.torsionBy O (Gal(Ω/E) → Unit → QuotSpan (ℓ ^ ν : ↑O)) (ℓ ^ h)) ≤
      length O (shaOdd ℓ E O e ν) := by
  -- `z ↦ z ∘ conjGal - z` maps `S` to the odd classes, as it equals `(z + z ∘ conjGal) - z - z`.
  -- Its kernel is killed by `ℓ ^ h`, as the `φ j` read the even classes at the test points.
  have h_even z (hz : z ∈ S) : z + z ∘ conjGal ∈ evenClasses O ∅ ν e := add_conjGal_mem_evenClasses
    he (mem_selmerModule_of_subset (hS_unr z hz) .rfl Set.subset_union_left) (hS_loc z hz)
  let oddPart := funLeft O (Unit → QuotSpan (ℓ ^ ν : ↑O)) (conjGal : Gal(Ω/E) → Gal(Ω/E)) - 1
  rw [← relLength_bot]
  refine relLength_le_of_mapsTo oddPart (fun z hz ↦ ?_) fun z hz h_ker ↦ funext fun g ↦ ?_
  · obtain ⟨h_sel, -, h_van⟩ := h_even z hz
    have h_sum : z + z ∘ conjGal ∈ selmerModule (tateTwist ℓ E O e) (placesDividing E ℓ) ∅
        (QuotSpan (ℓ ^ ν : ↑O)) :=
      mem_selmerModule_of_subset h_sel .rfl (by simp)
    have h_eq : oddPart z = z + z ∘ conjGal - z - z := funext fun g ↦ by simp [oddPart]
    refine mem_shaOdd.2 ⟨fun g hg ↦ ?_, fun _ g ↦ by simp [oddPart], ?_⟩
    · simpa [oddPart, hS_loc z hz g hg] using h_van g (by simpa [shaLocalSet, he] using hg)
    · rw [h_eq]
      exact sub_mem (sub_mem h_sum (hS_unr z hz)) (hS_unr z hz)
  · -- An even `z`: at a test point `i` we have `4 z(i) = 2 z(φ j) = 0` for some `j` of type `e`.
    have h_conj : z ∘ conjGal = z := sub_eq_zero.1 h_ker
    let e' : {k : Fin t // 0 < k.val} := ⟨e, Nat.pos_of_ne_zero he⟩
    obtain ⟨s, -, -, hs, hs_even⟩ := h_tri.exists_test_points
    have h_points (i : Gal(Ω/E)) (hi : i ∈ s) : ((4 : ↑O) • z) i = 0 := by
      obtain ⟨j, hj, h_read⟩ := hs_even e' i hi
      calc ((4 : ↑O) • z) i = 2 • (z + z ∘ conjGal) i := by
            rw [h_conj, Pi.smul_apply, Pi.add_apply]
            module
        _ = (z + z ∘ conjGal) (φ j) := (h_read O _ (h_even z hz)).symm
        _ = 0 := hS_φ z hz j (by simp [hj, e'])
    -- With `d = cyclotomicInv g₀ ^ e - 1`, the cocycle `4 d z` vanishes at `g₀` and at the test
    -- points, so it is zero, and `4 d` divides `ℓ ^ h`.
    let d : ↑O := cyclotomicInv ℓ E O g₀ ^ e.val - 1
    have h_kill : d • (4 : ↑O) • z = 0 := by
      refine hs O e _ (hS_unr _ (S.smul_mem d (S.smul_mem 4 hz))) ?_ fun i hi ↦ ?_
      · rw [smul_smul, mul_comm, mul_smul, Pi.smul_apply, Pi.smul_apply, hS_g₀ z hz, smul_zero]
      · rw [Pi.smul_apply, h_points i hi, smul_zero]
    obtain ⟨a, ha⟩ : 4 * d ^ 2 ∣ (ℓ ^ h : ↑O) := h_tri.four_mul_sq_dvd O e'
    calc (ℓ ^ h : ↑O) • z g = ((a * d) • d • (4 : ↑O) • z) g := by
          simp only [ha, Pi.smul_apply]
          module
      _ = 0 := by rw [h_kill, smul_zero, Pi.zero_apply]

/-- Let the places `w j` off `ℓ`, with tame generators `τ j`, elements `φ j` and monotone exponents
`ty j`, form a triangle of primes for `g₀` up to `ℓ ^ h` (`IsPrimeTriangle`): among other clauses,
`ℓ ^ h` kills the value at `τ j` of an even class of exponent `ty j` that vanishes at the earlier
`τ i` and at the earlier `φ i` of that exponent; `c` bounds `h` times the number of places and test
points. Let `e < t`, and let `Z` be a module of cocycles with values in `(O/ℓ^ν)(-e)`, unramified
off `ℓ`, the `w j` and their conjugates; let `cyclotomicInv g₀ ^ e - 1` kill the value at `g₀` of
each member that is unramified off `ℓ`. Let `b` bound the length of `Z / (Z ⊓ Zf)` (`relLength`),
where `Zf` consists of the functions that obey the linear relations `crysRelations` of the
crystalline cocycles above `ℓ`, plus the length of the odd classes `shaOdd`. Write `τ' j`, `φ' j`
for the inverses of the conjugates of `τ j`, `φ j`, and `I` for the `j` with `ty j = e`. Then
`HasTriangleCost` holds: for the members `Z₀` of `Z` that vanish on some set, (a) if `z ∈ Z₀` agrees
at `τ i`, `τ' i` for `i < j` and at `φ i`, `φ' i` for `i < j` in `I`, then `ℓ ^ h • z` agrees at
`τ j`, `τ' j` for `j ∈ I`; (b) the length of `Z / Z₀`, plus the length modulo `ℓ ^ h`-torsion of any
submodule of `Z₀` that vanishes at all `τ j`, `τ' j` and agrees at `φ j`, `φ' j` for `j ∈ I`, is at
most `b`. -/
lemma hasTriangleCost_tateTwist [Fintype J] [LinearOrder J] {ν : ℕ} {w : J → FinPlace E}
    {τ φ : J → Gal(Ω/E)} {t : ℕ} {g₀ : Gal(Ω/E)} {h c : ℕ} {e : Fin t}
    {ty : J →o {k : Fin t // 0 < k.val}} (h_tri : IsPrimeTriangle ν w τ φ g₀ t ty h c)
    {Z : Submodule O (Gal(Ω/E) → Unit → QuotSpan (ℓ ^ ν : ↑O))}
    (hZ_sel : Z ≤ selmerModule (tateTwist ℓ E O e)
      (placesDividing E ℓ ∪ Set.conjClosure (Set.range w)) ∅ (QuotSpan (ℓ ^ ν : ↑O)))
    (hZ_g₀ : ∀ z ∈ Z,
      z ∈ selmerModule (tateTwist ℓ E O e) (placesDividing E ℓ) ∅ (QuotSpan (ℓ ^ ν : ↑O)) →
      (cyclotomicInv ℓ E O g₀ ^ e.val - 1) • z g₀ = 0)
    {b : ℕ∞}
    (h_loss_add_shaOdd :
      relLength Z (obeying (crysRelations (tateTwist ℓ E O e)) (QuotSpan (ℓ ^ ν : ↑O))) +
        length O (shaOdd ℓ E O e ν) ≤ b) :
    HasTriangleCost Z τ (fun j : J ↦ (conjGal (τ j))⁻¹) φ (fun j : J ↦ (conjGal (φ j))⁻¹)
      {j : J | (ty j).val = e} (ℓ ^ h) b := by
  -- Take `L = shaLocalSet ℓ E e`. The triangle is `IsPrimeTriangle.pow_smul_eq_zero` for the even
  -- part `z + z ∘ conjGal`. Modulo the cocycles vanishing on `L` the cost is at most the local
  -- loss, and the rest costs at most the length of `shaOdd`.
  open Matrix.Module in
  have h_coc {z : Gal(Ω/E) → Unit → QuotSpan (ℓ ^ ν : ↑O)} (hz : z ∈ Z) :
      ∀ g g' : Gal(Ω/E), z (g * g') = z g + tateTwist ℓ E O e g • z g' :=
    (mem_selmerModule_iff.1 (hZ_sel hz)).1
  have h_inv {z : Gal(Ω/E) → Unit → QuotSpan (ℓ ^ ν : ↑O)} (hz : z ∈ Z) (j : J) :
      z (conjGal (τ j))⁻¹ = -z (conjGal (τ j)) ∧ z (conjGal (φ j))⁻¹ = -z (conjGal (φ j)) :=
    apply_withConjInv_false_eq_neg h_tri.isTameGeneratorFamily (h_coc hz) j
  refine ⟨shaLocalSet ℓ E e, fun j hj z ⟨hz, hzL⟩ h_prev ↦ ?_,
    fun S hS h_van ↦ h_loss_add_shaOdd.trans' (add_le_add ?_ ?_)⟩
  · -- The triangle: by `h_inv`, the values of `z` at `τ i` and `(conjGal (τ i))⁻¹` agree exactly
    -- when `z + z ∘ conjGal` kills `τ i`, and likewise for `φ i`.
    obtain rfl : (ty j).val = e := (mem_filter.1 hj).2
    have h_even : z + z ∘ conjGal ∈ evenClasses O (Set.range w) ν (ty j).val :=
      add_conjGal_mem_evenClasses (ty j).2.ne' (hZ_sel hz) hzL
    simp only [h_inv hz] at h_prev ⊢
    have h_prev' : ∀ i < j, (z + z ∘ conjGal) (τ i) = 0 ∧
        (ty i = ty j → (z + z ∘ conjGal) (φ i) = 0) := by
      simpa [eq_neg_iff_add_eq_zero, Subtype.ext_iff] using h_prev
    have h_step : ℓ ^ h • (z + z ∘ conjGal) (τ j) = 0 := h_tri.pow_smul_eq_zero O j _ h_even h_prev'
    simpa [← Nat.cast_smul_eq_nsmul O, eq_neg_iff_add_eq_zero] using h_step
  · -- The loss: a cocycle that obeys the local crystalline relations vanishes on `L`.
    exact relLength_le_of_mapsTo 1 (by simp) fun z hz h_loc g hg ↦
      apply_eq_zero_of_mem_obeying_crysRelations (h_coc hz) h_loc hg
  · -- The cocycles in `S` kill the tame generators, so they are unramified off `ℓ`.
    have hS_tame z (hz : z ∈ S) : ∀ k : J × Bool, z (withConjInv τ k) = 0 := by
      rintro ⟨j, copy⟩
      obtain ⟨h_τ, h_τ'⟩ : z (τ j) = 0 ∧ z (conjGal (τ j))⁻¹ = 0 := (h_van z hz).1 j
      cases copy
      exacts [h_τ', h_τ]
    have hS_unr z (hz : z ∈ S) : z ∈ selmerModule (tateTwist ℓ E O e) (placesDividing E ℓ) ∅
        (QuotSpan (ℓ ^ ν : ↑O)) :=
      h_tri.isTameGeneratorFamily.mem_selmerModule_of_tame_eq_zero (hZ_sel (hS hz).1) (hS_tame z hz)
        .rfl
        fun _ _ ↦ tateTwist_eq_one_of_cyclotomicChar_eq_one
    have hS_loc z (hz : z ∈ S) g (hg : g ∈ shaLocalSet ℓ E e) : z g = 0 := (hS hz).2 g hg
    by_cases he : e.val = 0
    · -- For `e = 0` there is no sign condition, and `S ≤ shaOdd`.
      rw [← relLength_bot]
      exact relLength_mono
        (fun z hz ↦ mem_shaOdd.2 ⟨hS_loc z hz, fun he' ↦ absurd he he', hS_unr z hz⟩) bot_le
    refine relLength_torsionBy_le_length_shaOdd h_tri he
      (fun z hz ↦ hZ_g₀ z (hS hz).1 (hS_unr z hz)) hS_unr hS_loc fun z hz j hj ↦ ?_
    obtain ⟨-, h_φ⟩ := h_van z hz
    have h_pair : z (φ j) = z (conjGal (φ j))⁻¹ := h_φ j (by simp [hj])
    rw [(h_inv (hS hz).1 j).2] at h_pair
    simpa [eq_neg_iff_add_eq_zero] using h_pair

end TateTwistSteps

end New.Selmer
