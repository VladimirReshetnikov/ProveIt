import Lib.GaloisRep.Main.DivisibleSelmerModules
import New.Congruences.Selmer.Mirror
import New.Congruences.Selmer.OneSystem

/-!
# The descent

Primes are added as long as this makes the tied Selmer groups modulo `ϖ ^ k`, `1 ≤ k ≤ e`, shorter.
When no prime does, reciprocity bounds the dual Selmer group at the level given by the exponent of
the tied group, and the comparison of the lengths of the two groups gives the bound for the tied
group. All data are treated at once: a prime that is added for one datum has slope `0` for the
others, which means that their classes stay unramified there. Lengths count composition factors, so
that each step lowers the sum of the lengths by at least `1`.

* `New.Selmer.tilting`: off few residues of `a`, the kernel of `a • evγ - evφ` is short.
* `New.Selmer.exists_slope_totalTiedLength_lt`: one step of the descent.
* `New.Selmer.SelmerDatum.length_tiedSelmer_pow_le`: the bound when no step is possible.
* `New.Selmer.exists_isTiedPrimes_card_le_and_length_le`: boundedly many new primes with slopes make
  the tied Selmer groups of finitely many data short.

Throughout, `E` is a number field with a chosen embedding into the algebraic closure `Ω` of `ℚ`
(`New.EmbeddedNumberField`). From the first prime on, `E` is a CM field, `ℓ` is a prime
(`New.ThePrime`) and `S₀` is a finite set of finite places of `E`; for the Selmer data, `O` is the
integer ring of a finite extension of `ℚ_ℓ` (`New.PadicIntegerRing`).

Notions from other files:
* `New.selmerModule ρ S K B`: locally constant cocycles for `ρ` with values in `Bⁿ`, unramified
  outside `S` and obeying the linear relations `K`; `New.QuotSpan a` is the ring `O / a`.
* `New.Selmer.SelmerDatum ℓ S₀ g₀ O n`: a Galois lattice `T = Oⁿ` with local conditions, unramified
  outside a set `T.places ⊆ S₀`, on which `det(g - 1) ≠ 0` for `g = g₀, g₀^{-c}`.
  `T.tiedSelmer R J x i a` is its Selmer group modulo `a`, unramified outside `T.places ∪ R ∪ R̄`,
  with the ties `z(γ) = s • z(φ)` at the primes of `J` and their conjugates, `s` the slope of datum
  `i`. It is `Sel(J)` for `R = J` and `Sel^𝔮(J)` for `R = J ∪ {𝔮}`. The global term `T.globalTerm`
  is the supremum over `a ≠ 0` of the lengths of `Hom_G(T / a, (T / a)^{*c})`, and `T.placesTerm` is
  the sum `lt_S(T)` of the local terms at the places of `T.places` prime to `ℓ`.
* `New.Selmer.IsTiedPrimes ℓ S₀ V W N P₀ J x`: a set `J` of primes outside `S₀ ∪ S̄₀` with places,
  Frobenius elements `φ`, tame generators `γ`, characters to `ℤ / ℓ ^ N` and slopes, all recorded in
  `x`. The first prime `P₀ ∈ J` has slope `0` and its Frobenius element in the set `W`, and `V i`
  holds at `φ` and `φ^{-c}` where the slope for datum `i` is not zero.
* `New.Selmer.IsNewAuxiliaryPrime ℓ V S₀ J P₀ x i P l`: the prime `P` with data `l` may be added to
  `J` with any slope for datum `i`. In particular `P` and `P̄` lie outside `S₀ ∪ J`, and `V i` holds
  at `φ = l.frob` and `φ^{-c}`.
* `New.Selmer.evalConjPair g`: the evaluation `ev_g` of a function at `g` and at `g^{-c}`, the
  inverse of the complex conjugate of `g`.

## Relation to the literature

Lowering Selmer groups mod ℓ^n by new local conditions at Chebotarev primes with trivial Frobenius
is known in the literature. Related work: Fakhruddin–Khare–Patrikis, Relative deformation theory,
relative Selmer groups, and lifting irreducible Galois representations, 2021; Mazur–Rubin,
Diophantine stability, 2018; Darmon–Diamond–Taylor, Fermat's Last Theorem, 1995.
-/

noncomputable section

namespace New.Selmer

open Module IsLocalRing LinearMap

/-! ### Tilting -/

open Fintype Polynomial Submodule in
/-- Tilting. Let `evγ, evφ` be linear maps to `(O / I) ^ m`, of finite length, and let `C` be a
submodule of their source. For `a` outside at most `card m` residue classes, the kernel of
`a • evγ - evφ` on `C` is no longer than the part of the kernel of `evγ` on `C` that `evφ` maps into
`evγ C`. -/
lemma tilting {O m B : Type*} [CommRing O] [DVR O] [Fintype m] [AddCommGroup B]
    [Module O B] {I : Ideal O} [IsArtinian O (O ⧸ I)] (evγ evφ : B →ₗ[O] m → O ⧸ I)
    (C : Submodule O B) :
    ∃ bad : List (ResidueField O),
      bad.length ≤ card m ∧
      ∀ a : O, residue O a ∉ bad →
        length O ↥(C ⊓ (a • evγ - evφ).ker) ≤ length O ↥(C ⊓ evγ.ker ⊓ (C.map evγ).comap evφ) := by
  -- Let `C'` be the sum of all the kernels in `C`; then `evφ C' ≤ evγ C'`. Write `evγ C'` as the
  -- image of a map `π` on a free module `Λ`, and choose `σ : Λ → C'` with `evγ ∘ σ = π` and an
  -- endomorphism `U` of `Λ` with `π ∘ U = evφ ∘ σ`. When `a` is no eigenvalue of `U` modulo the
  -- maximal ideal, `a • evγ - evφ` has no smaller image on `C'` than `evγ`, hence no longer kernel.
  let C' : Submodule O B := ⨆ a : O, C ⊓ (a • evγ - evφ).ker
  have hC' : C' ≤ C := by simp [C']
  have h_image : C' ≤ (C'.map evγ).comap evφ := by
    refine iSup_le fun a z ⟨hzC, hz_ker⟩ ↦ ?_
    have h_val : evγ (a • z) = evφ z := by simpa [sub_eq_zero] using hz_ker
    exact ⟨a • z, C'.smul_mem a (mem_iSup_of_mem a ⟨hzC, hz_ker⟩), h_val⟩
  -- The preimage `Λ` of `evγ C'` in `O ^ m` is free of rank at most `card m`.
  let Λ : Submodule O (m → O) := (C'.map evγ).comap (I.mkQ.compLeft m)
  let π : Λ →ₗ[O] C'.map evγ := (I.mkQ.compLeft m).submoduleComap (C'.map evγ)
  have hπ : Function.Surjective π :=
    submoduleComap_surjective_of_surjective _ _ I.mkQ_surjective.comp_left
  obtain ⟨σ, hσ⟩ : ∃ σ : Λ →ₗ[O] C', evγ.submoduleMap C' ∘ₗ σ = π :=
    projective_lifting_property _ _ (evγ.submoduleMap_surjective C')
  obtain ⟨U, hU⟩ : ∃ U : Λ →ₗ[O] Λ, π ∘ₗ U = evφ.restrict h_image ∘ₗ σ :=
    projective_lifting_property _ _ hπ
  have hσ_apply (u : Λ) : evγ (σ u) = π u := congrArg Subtype.val (LinearMap.congr_fun hσ u)
  have hU_apply (u : Λ) : π (U u) = evφ (σ u) := congrArg Subtype.val (LinearMap.congr_fun hU u)
  refine ⟨(U.charpoly.aroots (ResidueField O)).toList, ?_, fun a ha ↦ ?_⟩
  · grw [Multiset.length_toList, card_roots_map_le_natDegree, charpoly_natDegree, finrank_le,
      finrank_pi]
  -- Off the residual roots of the characteristic polynomial, `det (a - U)` is a unit.
  have h_bij : Function.Bijective (algebraMap O (Λ →ₗ[O] Λ) a - U) := by
    have h_unit : IsUnit (U.charpoly.eval a) := by
      simpa [map_monic_ne_zero, charpoly_monic] using ha
    rwa [eval_charpoly, ← isUnit_iff_isUnit_det, End.isUnit_iff] at h_unit
  -- The map `(a • evγ - evφ) ∘ σ = π ∘ (a - U)` is onto `evγ C'`.
  have h_map : C'.map evγ ≤ C'.map (a • evγ - evφ) := by
    intro x hx
    obtain ⟨u, hu⟩ := hπ.comp h_bij.surjective ⟨x, hx⟩
    refine ⟨σ u, (σ u).property, ?_⟩
    simpa [hσ_apply, hU_apply] using congrArg Subtype.val hu
  have h_ker : C' ⊓ evγ.ker ≤ C ⊓ evγ.ker ⊓ (C.map evγ).comap evφ :=
    le_inf (inf_le_inf_right _ hC')
      (inf_le_left.trans (h_image.trans (comap_mono (map_mono hC'))))
  -- Every map splits the length of `C'` into the lengths of image and kernel.
  have h_split (Φ : B →ₗ[O] m → O ⧸ I) :
      length O (C'.map Φ) + length O ↥(C' ⊓ Φ.ker) = length O C' := by
    rw [← relLength_ker C' Φ, relLength_add_length_inf]
  have h_le : C ⊓ (a • evγ - evφ).ker ≤ C' ⊓ (a • evγ - evφ).ker :=
    le_inf (le_iSup (fun t : O ↦ C ⊓ (t • evγ - evφ).ker) a) inf_le_right
  -- The image has finite length, so it cancels.
  refine (ENat.add_le_add_iff_left (k := length O (C'.map (a • evγ - evφ))) length_ne_top).1 ?_
  calc length O (C'.map (a • evγ - evφ)) + length O ↥(C ⊓ (a • evγ - evφ).ker)
    _ ≤ length O (C'.map (a • evγ - evφ)) + length O ↥(C' ⊓ (a • evγ - evφ).ker) :=
      add_le_add_right (length_mono h_le) _
    _ = length O (C'.map evγ) + length O ↥(C' ⊓ evγ.ker) := by rw [h_split, h_split]
    _ ≤ length O (C'.map (a • evγ - evφ)) + length O ↥(C ⊓ evγ.ker ⊓ (C.map evγ).comap evφ) :=
      add_le_add (length_mono h_map) (length_mono h_ker)

/-! ### Levels and the exponent of a Selmer group -/

section Levels

open Submodule Ideal

variable {O : Type} [CommRing O] [DVR O]

/-- Let `b = a c` with `a, c ≠ 0`. Multiplication by `c` identifies `O / a` with the `a`-torsion of
`O / b`. -/
lemma exists_injective_quotSpan_onto_torsion {a b c : O} (ha : a ≠ 0) (hc : c ≠ 0)
    (hb : b = a * c) : ∃ f : QuotSpan a →ₗ[O] QuotSpan b,
      Function.Injective f ∧ ∀ y : QuotSpan b, a • y = 0 → ∃ x : QuotSpan a, f x = y := by
  subst hb
  have h_ker : Ideal.span {a} = ker ((Ideal.span {a * c}).mkQ ∘ₗ (c • 1 : O →ₗ[O] O)) :=
    Ideal.ext (by simp [ker_comp, Ideal.mem_span_singleton, mul_comm c, mul_dvd_mul_iff_right hc])
  refine ⟨(Ideal.span {a}).liftQ _ h_ker.le,
    ker_eq_bot.1 ((Ideal.span {a}).ker_liftQ_eq_bot' _ h_ker), fun y hy ↦ ?_⟩
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h_dvd : a * c ∣ a * s := (Ideal.Quotient.eq_zero_iff_dvd _ _).1 hy
  obtain ⟨t, rfl⟩ : c ∣ s := (mul_dvd_mul_iff_left ha).1 h_dvd
  exact ⟨Ideal.Quotient.mk _ t, rfl⟩

/-- Let `ϖ` be a uniformizer of `O`. An element of `O / ϖ ^ (i + 1)` that `ϖ ^ i` does not kill is a
unit. -/
lemma isUnit_of_pow_smul_ne_zero {ϖ : O} (hϖ : Irreducible ϖ) {i : ℕ}
    {y : QuotSpan (ϖ ^ (i + 1))} (hy : ϖ ^ i • y ≠ 0) : IsUnit y := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  by_contra h_nonunit
  have h_mem : s ∈ maximalIdeal O := fun h ↦ h_nonunit (h.map _)
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at h_mem
  have h_dvd : ϖ ^ (i + 1) ∣ ϖ ^ i * s := by simpa [pow_succ] using mul_dvd_mul_left (ϖ ^ i) h_mem
  exact hy ((Ideal.Quotient.eq_zero_iff_dvd _ _).2 h_dvd)

end Levels

open Finset Function

/-- Passage to the exponent. Let `E` be a number field embedded in the algebraic closure `Ω` of `ℚ`,
and let `ϖ` be a uniformizer of `O`. The Selmer module modulo `ϖ ^ k` consists of the locally
constant cocycles `z` for `ρ` with values in `(O / ϖ ^ k) ^ n` that are unramified outside `S` and
obey the relations `K`: for each finite family of matrices `f ∈ K` indexed by `Gal(Ω/E)`, the sum
`∑ g, f g • z g` is zero. For some `i ≤ k` this module is no longer than the module modulo `ϖ ^ i`,
and if `i ≠ 0` the latter has a member with a value with a unit coordinate, that is, a member of
order `ϖ ^ i`. -/
lemma exists_length_selmerModule_pow_le {E O n : Type} [Field E] [EmbeddedNumberField E]
    [CommRing O] [DVR O] [Fintype n] [DecidableEq n] (ρ : Gal(Ω/E) → Matrix n n O) {ϖ : O}
    (hϖ : Irreducible ϖ) (S : Set (FinPlace E)) (K : Set (Gal(Ω/E) →₀ Matrix n n O)) (k : ℕ) :
    ∃ i ≤ k,
      length O (selmerModule ρ S K (QuotSpan (ϖ ^ k))) ≤
        length O (selmerModule ρ S K (QuotSpan (ϖ ^ i))) ∧
      (i ≠ 0 → ∃ z ∈ selmerModule ρ S K (QuotSpan (ϖ ^ i)),
        ∃ (g : Gal(Ω/E)) (j : n), IsUnit (z g j)) := by
  classical
  -- Let `ϖ ^ i` be the exponent of the module modulo `ϖ ^ k`.
  let Sel : Submodule O (Gal(Ω/E) → n → QuotSpan (ϖ ^ k)) := selmerModule ρ S K (QuotSpan (ϖ ^ k))
  have hk (z : Sel) : ϖ ^ k • z = 0 :=
    Subtype.ext (funext₂ fun _ _ ↦ smul_quot_eq_zero_of_dvd dvd_rfl _)
  obtain ⟨i, hik, hi, h_min⟩ : ∃ i ≤ k, (∀ z : Sel, ϖ ^ i • z = 0) ∧
      ∀ m < i, ¬∀ z : Sel, ϖ ^ m • z = 0 :=
    have h_ex : ∃ i : ℕ, ∀ z : Sel, ϖ ^ i • z = 0 := ⟨k, hk⟩
    ⟨Nat.find h_ex, Nat.find_min' h_ex hk, Nat.find_spec h_ex, fun _ ↦ Nat.find_min h_ex⟩
  have h_top : Submodule.torsionBy O Sel (ϖ ^ i) = ⊤ := Submodule.eq_top_iff'.2 hi
  -- The module modulo `ϖ ^ i` is the `ϖ ^ i`-torsion of the module modulo `ϖ ^ k`, so all of it.
  obtain ⟨f, hf, h_onto⟩ : ∃ f : QuotSpan (ϖ ^ i) →ₗ[O] QuotSpan (ϖ ^ k), Injective f ∧
      ∀ y : QuotSpan (ϖ ^ k), ϖ ^ i • y = 0 → ∃ x : QuotSpan (ϖ ^ i), f x = y :=
    exists_injective_quotSpan_onto_torsion (pow_ne_zero i hϖ.ne_zero)
      (pow_ne_zero (k - i) hϖ.ne_zero) (pow_mul_pow_sub ϖ hik).symm
  refine ⟨i, hik, ?_, fun hi₀ ↦ ?_⟩
  · rw [← length_torsionBy_selmerModule ρ S K hf h_onto, h_top, length_top]
  -- A member that `ϖ ^ (i - 1)` does not kill has a value with a unit coordinate.
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hi₀
  obtain ⟨z, hz⟩ : ∃ z : Sel, ϖ ^ m • z ≠ 0 := not_forall.1 (h_min m m.lt_succ_self)
  obtain ⟨z', rfl⟩ : z ∈ (selmerModuleMapOfInjective ρ S K hf).range :=
    Submodule.eq_top_iff'.1 ((range_selmerModuleMapOfInjective ρ S K hf h_onto).trans h_top) z
  have hz' : ϖ ^ m • z' ≠ 0 := fun h ↦ hz (by rw [← map_smul, h, map_zero])
  obtain ⟨g, j, h_val⟩ : ∃ (g : Gal(Ω/E)) (j : n), ϖ ^ m • z'.val g j ≠ 0 := by
    by_contra! h_zero
    exact hz' (Subtype.ext (funext₂ h_zero))
  exact ⟨z', z'.property, g, j, isUnit_of_pow_smul_ne_zero hϖ h_val⟩

/-! ### Room for slopes -/

/-- In a local ring whose residue field has `q` elements, a set of fewer than `q - 1` residues
misses the residue of some unit. -/
lemma exists_unit_residue_notMem {O : Type} [CommRing O] [IsLocalRing O]
    {bad : Finset (ResidueField O)} (h_room : #bad + 1 < Nat.card (ResidueField O)) :
    ∃ s : Oˣ, residue O s ∉ bad := by
  classical
  have : Finite (ResidueField O) := Nat.finite_of_card_ne_zero (by lia)
  have := Fintype.ofFinite (ResidueField O)
  obtain ⟨r, -, hr⟩ := exists_mem_notMem_of_card_lt_card (t := (univ : Finset (ResidueField O)))
    ((card_insert_le 0 bad).trans_lt (by simpa using h_room))
  obtain ⟨s, rfl⟩ := residue_surjective r
  obtain ⟨hs_unit, hs_bad⟩ : IsUnit s ∧ residue O s ∉ bad := by simpa using hr
  exact ⟨hs_unit.unit, hs_bad⟩

/-- Strict monotonicity of finite sums in `ℕ∞`: if `f ≤ g` on `s`, the terms of `g` are finite and
`f b < g b` for some `b ∈ s`, then the sum of `f` is smaller than the sum of `g`. -/
lemma sum_lt_sum_of_ne_top {α : Type} {s : Finset α} {f g : α → ℕ∞} (h_le : ∀ a ∈ s, f a ≤ g a)
    (h_fin : ∀ a ∈ s, g a ≠ ⊤) {b : α} (hb : b ∈ s) (h_lt : f b < g b) :
    ∑ a ∈ s, f a < ∑ a ∈ s, g a := by
  classical
  have h_rest : ∑ a ∈ s.erase b, f a ≤ ∑ a ∈ s.erase b, g a :=
    sum_le_sum fun a ha ↦ h_le a (mem_of_mem_erase ha)
  rw [← add_sum_erase s f hb, ← add_sum_erase s g hb]
  refine WithTop.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ?_ h_rest) h_lt h_rest
  exact ENat.sum_ne_top.2 fun a ha ↦ h_fin a (mem_of_mem_erase ha)

variable {ℓ : ℕ} [ThePrime ℓ] {E : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
  {S₀ : Finset (FinPlace E)} {g₀ : Gal(Ω/E)}

/-! ### The first prime -/

/-- Let `g₀` be inertial at a place of `S₀` prime to `ℓ`, and let `W` be a neighbourhood of `g₀`.
Then there is a prime `P₀` with data `l`, whose norm no prime of `S₀` divides, such that `{P₀}`,
with all slopes `0`, satisfies `IsTiedPrimes`. That is, `P₀` has prime norm, differs from its
complex conjugate `P̄₀`, both lie outside `S₀`, and the conditions on later primes are empty. The
condition on the norm lets the Greenberg–Wiles count keep its extra primes away from `P₀` and
`P̄₀`. -/
lemma exists_isTiedPrimes_singleton {O ι : Type} [CommRing O] {W : Set Gal(Ω/E)}
    (hg₀ : g₀ ∈ inertiaAbove (S₀ \ placesDividing E ℓ)) (hW : W ∈ nhds g₀)
    (V : ι → Gal(Ω/E) → Prop) (N : ℕ) :
    ∃ (P₀ : FinPlace E) (l : AuxPrimeData E (ℓ ^ N)),
      IsTiedPrimes ℓ S₀ V W N P₀ {P₀} fun _ : FinPlace E ↦ (l, (0 : ι → O)) := by
  -- Avoid the primes that divide the norm of a prime of `S₀`; these include `S₀`.
  let R : Set (FinPlace E) := ⋃ v ∈ S₀, placesDividing E v.q
  have hR : R.Finite := S₀.finite_toSet.biUnion fun v _ ↦
    have : NeZero v.q := ⟨v.one_lt_q.ne_bot⟩
    finite_natCast_mem v.q
  have hS₀ (v : FinPlace E) (hv : v ∈ S₀) : v ∈ R := Set.mem_biUnion hv v.1.absNorm_mem
  have hg₀R : g₀ ∈ inertiaAbove (R \ (.conjClosure (∅ : Finset (FinPlace E)) ∪
      placesDividing E ℓ)) := by
    obtain ⟨v, ⟨hvS, hvℓ⟩, hv⟩ := hg₀
    exact ⟨v, ⟨hS₀ v hvS, by simpa using hvℓ⟩, hv⟩
  obtain ⟨P₀, hP₀, h_prime, l, hl_near, -, hl_anti⟩ :=
    exists_isAuxPrimeDataAt N ∅ hR (Subgroup.subset_normalClosure hg₀R) hW
  obtain ⟨hP₀R, hP₀R'⟩ : P₀ ∉ R ∧ star P₀ ∉ R := not_or.1 hP₀
  -- If `v ∈ S₀` divided the prime number `P₀.q`, then `P₀.q ∣ v.q` and `P₀` would divide `v.q`.
  have h_norm (v : FinPlace E) (hv : v ∈ S₀) : v ∉ placesDividing E P₀.q := fun hvP ↦ by
    obtain h_coprime | h_dvd := Nat.coprime_or_dvd_of_prime h_prime v.q
    · exact natCast_notMem_of_coprime h_coprime hvP v.1.absNorm_mem
    · exact hP₀R (Set.mem_biUnion hv (P₀.1.mem_of_dvd (Nat.cast_dvd_cast h_dvd) P₀.1.absNorm_mem))
  have h_split : star P₀ ≠ P₀ := (hl_anti _ Set.subset_union_right).star_ne
  have h_notMem : P₀ ∉ S₀ ∧ star P₀ ∉ S₀ := ⟨mt (hS₀ P₀) hP₀R, mt (hS₀ (star P₀)) hP₀R'⟩
  have h_aux : IsAuxiliary S₀ {P₀} := by simpa [IsAuxiliary, h_prime, h_split] using h_notMem
  exact ⟨P₀, l,
    { auxiliary := h_aux
      first_mem := mem_singleton_self P₀
      isAuxPrimeDataAt := by simpa using hl_anti _ Set.subset_union_right
      char_frob_eq_ite := by simp +contextual
      first_frob_mem := hl_near
      first_slope := rfl
      notMem_placesDividing := by simpa using h_norm
      frob_of_slope_ne_zero := by simp }⟩

variable {O ι : Type} [CommRing O] [PadicIntegerRing O ℓ]

namespace SelmerDatum

variable {M N : ℕ} {a : O} {n : Type} [Fintype n] [DecidableEq n] (T : SelmerDatum ℓ S₀ g₀ O n)

/-! ### Adding a prime -/

/-- Let `T` be a Selmer datum over `O`, the integer ring of a finite extension of `ℚ_ℓ`. A tied
Selmer group of `T` modulo a divisor `a` of `ℓ ^ M` is finite. -/
lemma finite_tiedSelmer (ha : a ∣ ℓ ^ M) (R J : Finset (FinPlace E))
    (x : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)) (i : ι) :
    Finite (T.tiedSelmer R J x i a) :=
  have : NeZero a := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne _) ha⟩
  finite_selmerModule ha (T.isLocallyConstant M) (Finset.finite_toSet _) _

variable {V : ι → Gal(Ω/E) → Prop} {W : Set Gal(Ω/E)} {P₀ : FinPlace E} {J : Finset (FinPlace E)}
  {x : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)} {i j : ι}

open scoped Classical in
/-- Let `J` satisfy `IsTiedPrimes ℓ S₀ V W N P₀ J x`: its primes lie outside `S₀ ∪ S̄₀` and come
with a place, a Frobenius element, the tame generator `γ_v = (x v).1.tameGenerator`, a character to
`ℤ / ℓ ^ N` and slopes. Let `a ∣ ℓ ^ M`, let `R` be any finite set of places and `K` any set of
linear relations between the values of a function on `Gal(Ω/E)`. If a locally constant cocycle with
values in `(O / a) ^ n` satisfies the relations `K`, is unramified outside `T.places ∪ J ∪ J̄` and
vanishes at `γ_v` and `γ_v^{-c} = (conjGal γ_v)⁻¹` for all `v ∈ J \ R`, then it is unramified
outside `T.places ∪ R ∪ R̄`. -/
lemma selmerModule_inf_ker_le (hp : IsTiedPrimes ℓ S₀ V W N P₀ J x) (ha : a ∣ ℓ ^ M)
    (R : Finset (FinPlace E)) (K : Set (Gal(Ω/E) →₀ Matrix n n O)) :
    selmerModule T.ρ (unionWithConj T.places J) K (QuotSpan a) ⊓
        ker (pi fun v : ↥(J \ R) ↦ evalConjPair (x v).1.tameGenerator) ≤
      selmerModule T.ρ (unionWithConj T.places R) K (QuotSpan a) := by
  rintro c ⟨hc, hc_zero⟩
  refine mem_selmerModule_of_eq_zero_on_inertiaAbove hc .rfl fun v hv ↦ ?_
  obtain ⟨hvS, w, hw, hvw⟩ : v ∉ T.places ∧ ∃ w ∈ J \ R, v = w ∨ v = star w := by
    grind only [unionWithConj, = mem_union, = mem_image, = mem_sdiff, = Set.mem_sdiff, = mem_coe]
  have h_anti := hp.isAuxPrimeDataAt w (sdiff_subset hw)
  obtain ⟨-, -, hγ : h_anti.isPlaceOver.tameGenerator = (x w).1.tameGenerator⟩ := h_anti.tame_gen
  have h_unr : ∀ g ∈ inertiaAbove {v}, T.ρ g = 1 := by
    rintro g ⟨u, rfl, hu⟩
    exact T.unramified g ⟨u, hvS, hu⟩
  have h_zero (b : Bool) : c (idOrConjInv b (x w).1.tameGenerator) = 0 :=
    funext fun k ↦ congrFun₂ hc_zero ⟨w, hw⟩ (b, k)
  -- A cocycle that vanishes at the tame generator on the side of `v` is unramified at `v`.
  obtain ⟨b, _, -, h_side⟩ := exists_conj_side_detects (nsmul_quot_eq_zero ha)
    h_anti.isPlaceOver h_anti.notMem h_unr hvw
  rw [hγ] at h_side
  obtain ⟨h_inertia, -⟩ := h_side c hc (h_zero b)
  exact h_inertia

/-- Slope `0` means unramified. Let `T` be a Selmer datum: a lattice `O ^ n` with Galois action
`T.ρ`, unramified outside `T.places`. The relations `T.classRelations` are its local conditions
above `ℓ` and vanishing at `T.γ`, a fixed inertia element acting by a scalar, which picks one
cocycle in each class. Let `IsTiedPrimes ℓ S₀ V W N P₀ J x` hold: `J` is a set of auxiliary primes
outside `S₀` with first prime `P₀`. For each `v ∈ J`, `x v` gives a tame generator `γ_v`, a
Frobenius element `φ_v`, a character to `ℤ / ℓ ^ N` and slopes `(x v).2 i`. Let `a ∣ ℓ ^ M`. The
group `T.tiedSelmer J J x i a` consists of the cocycles `z` modulo `a` that obey `T.classRelations`,
are unramified outside `T.places ∪ J ∪ J̄` (first `J`) and satisfy the ties
`z(γ_v) = slope • z(φ_v)` at the primes `v ∈ J` and their conjugates (second `J`). If the slopes
`(x v).2 i` of datum `i` are all `0`, so that the ties read `z(γ_v) = 0`, then these cocycles are
unramified outside `T.places`: they lie in `selmerModule T.ρ T.places T.classRelations (QuotSpan
a)`, the Selmer group without auxiliary primes. -/
lemma tiedSelmer_le_of_slope_eq_zero (hp : IsTiedPrimes ℓ S₀ V W N P₀ J x) (ha : a ∣ ℓ ^ M)
    (h_slope : ∀ v ∈ J, (x v).2 i = 0) :
    T.tiedSelmer J J x i a ≤ selmerModule T.ρ T.places T.classRelations (QuotSpan a) := by
  classical
  intro c hc
  obtain ⟨-, -, h_ties : c ∈ obeying (tieRelations J x i) (QuotSpan a), -⟩ :=
    mem_selmerModule_iff.1 (mem_selmerModule_of_subset hc Set.subset_union_right .rfl)
  -- The ties at `v` and at its conjugate have slope `0`.
  have h_zero (v : FinPlace E) (hv : v ∈ J) (b : Bool) :
      c (idOrConjInv b (x v).1.tameGenerator) = 0 := by
    rw [mem_obeying_tieRelations_iff.1 h_ties v hv b, h_slope v hv, zero_smul]
  have h_ker : c ∈ ker (pi fun v : ↥(J \ ∅) ↦ evalConjPair (O := O) (x v).1.tameGenerator) := by
    ext ⟨v, hv⟩ ⟨b, k⟩
    exact congrFun (h_zero v (sdiff_subset hv) b) k
  exact mem_selmerModule_of_subset (T.selmerModule_inf_ker_le hp ha ∅ _ ⟨hc, h_ker⟩)
    Set.subset_union_left (by simp [unionWithConj])

open scoped Classical in
/-- Let `IsTiedPrimes ℓ S₀ V W N P₀ J x` hold: `J` is a set of primes outside `S₀` with data and
slopes `x` to level `ℓ ^ N`, first prime `P₀` of slope `0` with Frobenius element in `W`, and `V j`
true at Frobenius elements where the slope for `j` is not zero. Let `P` with data `l` be a new
auxiliary prime for a datum `i`: it may be added to `J` with any slope for `i`. Let `a ∣ ℓ ^ M` and
`γ = l.tameGenerator`. Consider a cocycle modulo `a` with the local conditions of `T` and the ties
`z(γ_v) = slope • z(φ_v)` of datum `j` at `v ∈ J` and `v̄`, unramified outside
`T.places ∪ J ∪ J̄ ∪ {P, P̄}`. If it vanishes at `γ` and at `γ^{-c} = (conjGal γ)⁻¹`, then it is
unramified at `P` and `P̄`, hence lies in the tied Selmer group of `J`. -/
lemma tiedSelmer_insert_inf_ker_le (hp : IsTiedPrimes ℓ S₀ V W N P₀ J x) {P : FinPlace E}
    {l : AuxPrimeData E (ℓ ^ N)} (hl : IsNewAuxiliaryPrime ℓ V S₀ J P₀ x i P l) (ha : a ∣ ℓ ^ M) :
    T.tiedSelmer (insert P J) J x j a ⊓ ker (evalConjPair l.tameGenerator) ≤
      T.tiedSelmer J J x j a := by
  -- Add `P` with slope `0` to the set of tied primes; it is the only member of `insert P J \ J`.
  have h_ker : ker (pi fun v : ↥(insert P J \ J) ↦
        evalConjPair (update x P (l, Pi.single i 0) v).1.tameGenerator) =
      (ker (evalConjPair l.tameGenerator) : Submodule O (Gal(Ω/E) → n → QuotSpan a)) := by
    simp [hl.notMem, ker_pi, iInf_subtype]
  rw [tiedSelmer, tiedSelmer, ← h_ker]
  exact T.selmerModule_inf_ker_le (hp.insert_of_isNewAuxiliaryPrime hl 0) ha J
    (T.classRelations ∪ tieRelations J x j)

open scoped Classical in
/-- Add a prime `𝔮 = P` outside `J`, with Frobenius element `l.frob`, tame generator
`l.tameGenerator` and slopes `s`. The tied Selmer group `Sel(J)` of the Selmer datum `T` modulo
`a` for the index `j` consists of the cocycles with the local conditions of `T`, unramified outside
`T.places ∪ J ∪ J̄`, with `z(γ_v) = slope • z(φ_v)` at `v ∈ J` and `v̄`. A member `z` of the new
group `Sel(J ∪ {𝔮})` lies in `Sel^𝔮(J)` (ties only at `J`, ramification allowed also at `𝔮` and
`𝔮̄`) and satisfies the tie `ev_γ z = s j • ev_φ z`, where `ev_g = evalConjPair g` evaluates at `g`
and at `g^{-c} = (conjGal g)⁻¹`, the inverse of its complex conjugate. -/
lemma tiedSelmer_update_le {P : FinPlace E} {l : AuxPrimeData E (ℓ ^ N)} (hP : P ∉ J) (s : ι → O) :
    T.tiedSelmer (insert P J) (insert P J) (update x P (l, s)) j a ≤
      T.tiedSelmer (insert P J) J x j a ⊓
        ker (evalConjPair l.tameGenerator - s j • evalConjPair l.frob) := by
  intro c hc
  have h_old : tieRelations (n := n) J x j ⊆ tieRelations (insert P J) (update x P (l, s)) j := by
    rintro r ⟨⟨⟨v, hv⟩, b⟩, rfl⟩
    exact ⟨(⟨v, mem_insert_of_mem hv⟩, b), by simp [ne_of_mem_of_not_mem hv hP]⟩
  have h_new (b : Bool) : c (idOrConjInv b l.tameGenerator) = s j • c (idOrConjInv b l.frob) := by
    have h_rel : Finsupp.single (idOrConjInv b l.tameGenerator) 1 -
        Finsupp.single (idOrConjInv b l.frob) (s j • 1) ∈
          tieRelations (n := n) (insert P J) (update x P (l, s)) j :=
      ⟨(⟨P, mem_insert_self P J⟩, b), by simp⟩
    obtain ⟨-, -, h_obey, -⟩ := mem_selmerModule_iff.1 hc
    simpa [sub_eq_zero, funext_iff, Matrix.one_apply] using mem_obeying.1 h_obey _ (.inr h_rel)
  refine ⟨mem_selmerModule_of_subset hc (Set.union_subset_union_right _ h_old) .rfl, ?_⟩
  ext ⟨b, k⟩
  simp [evalConjPair_apply, h_new b]

open scoped Classical in
/-- Let `IsTiedPrimes ℓ S₀ V W N P₀ J x` hold. Let `𝔮 = P` with data `l` be a new auxiliary prime
for datum `i`: it can be added to `J` with any slope for `i`. Let `φ = l.frob`,
`γ = l.tameGenerator`, `g^{-c}` the inverse of the complex conjugate of `g`, and `a ∣ ℓ ^ M`. For
units `u` outside at most `2 · rank T` (`= 2 · card n`) residue classes, adding `𝔮` with slope `u⁻¹`
gives a tied Selmer group no longer than the part of the old group `Sel(J)` in `T.frobInTameImage`:
the `z` whose values at `φ, φ^{-c}` are the values at `γ, γ^{-c}` of a class with the ties of `J`
that may ramify also at `𝔮` and `𝔮̄`. -/
lemma exists_length_tiedSelmer_insert_le [DecidableEq ι] (hp : IsTiedPrimes ℓ S₀ V W N P₀ J x)
    {P : FinPlace E} {l : AuxPrimeData E (ℓ ^ N)}
    (hl : IsNewAuxiliaryPrime ℓ V S₀ J P₀ x i P l) (ha : a ∣ ℓ ^ M) :
    ∃ bad : Finset (ResidueField O), #bad ≤ 2 * Fintype.card n ∧
      ∀ u : Oˣ, residue O u ∉ bad →
        length O (T.tiedSelmer (insert P J) (insert P J) (update x P (l, Pi.single i ↑u⁻¹)) i a) ≤
          length O ↥(T.tiedSelmer J J x i a ⊓ T.frobInTameImage J x i a P l) := by
  have : NeZero a := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne _) ha⟩
  let C : Submodule O (Gal(Ω/E) → n → QuotSpan a) := T.tiedSelmer (insert P J) J x i a
  obtain ⟨bad, h_card, h_bad⟩ := tilting (m := Bool × n) (I := Ideal.span {a})
    (evalConjPair l.tameGenerator) (evalConjPair l.frob) C
  refine ⟨bad.toFinset, bad.toFinset_card_le.trans (by simpa using h_card), fun u hu ↦ ?_⟩
  -- The tie with slope `u⁻¹` says that `u • ev_γ = ev_φ`.
  calc
    _ ≤ length O ↥(C ⊓ ker ((u : O) • evalConjPair l.tameGenerator - evalConjPair l.frob)) := by
      refine length_mono ((T.tiedSelmer_update_le hl.notMem _).trans (inf_le_inf_left C ?_))
      simp +contextual [smul_smul, IsConcreteLE.le_iff, sub_eq_zero]
    _ ≤ length O ↥(C ⊓ ker (evalConjPair l.tameGenerator) ⊓ T.frobInTameImage J x i a P l) :=
      h_bad u (mt List.mem_toFinset.2 hu)
    _ ≤ length O ↥(T.tiedSelmer J J x i a ⊓ T.frobInTameImage J x i a P l) :=
      length_mono (inf_le_inf_right _ (T.tiedSelmer_insert_inf_ker_le hp hl ha))

/-! ### The end of the descent -/

/-- Let `IsTiedPrimes ℓ S₀ V W N P₀ J x` hold: primes outside `S₀` with data and slopes to level
`ℓ ^ N`, the first one `P₀` with slope `0` and Frobenius element in `W`, and `V i` at Frobenius
elements with nonzero slope for `i`; here `V i g` says that `g` acts trivially on `T / ℓ ^ M`. Let
`M < N` and `a ∣ ℓ ^ M`. The tied Selmer group `Sel(J)` consists of the cocycles modulo `a` with the
local conditions of `T`, unramified outside `T.places ∪ J ∪ J̄`, with the ties
`z(γ_v) = slope • z(φ_v)` at `v ∈ J` and `v̄`. Suppose that some member has a value with a unit
coordinate, and that for every new auxiliary prime `P` (one that can be added to `J` with any slope
for `i`), with Frobenius element `φ` and tame generator `γ`, each member lies in
`T.frobInTameImage`: its values at `φ, φ^{-c}` are the values at `γ, γ^{-c}` of a class with the
ties of `J` that may ramify also at `P` and `P̄`. Then `Sel(J)` has length at most `T.globalTerm`
plus `T.placesTerm`. -/
lemma length_tiedSelmer_le_of_isUnit (hJ : IsTiedPrimes ℓ S₀ V W N P₀ J x)
    (hV : ∀ g : Gal(Ω/E), V i g ↔ reduceModPow ℓ M T.ρ g = 1) (hN : M < N) (ha : a ∣ ℓ ^ M)
    (h_unit : ∃ z ∈ T.tiedSelmer J J x i a, ∃ (g : Gal(Ω/E)) (k : n), IsUnit (z g k))
    (h_le_frobInTameImage : ∀ (P : FinPlace E) (l : AuxPrimeData E (ℓ ^ N)),
      IsNewAuxiliaryPrime ℓ V S₀ J P₀ x i P l →
      T.tiedSelmer J J x i a ≤ T.frobInTameImage J x i a P l) :
    length O (T.tiedSelmer J J x i a) ≤ T.globalTerm + T.placesTerm := by
  obtain ⟨z, hz, hz_unit⟩ := h_unit
  -- Counting compares `Sel(J)` with its dual, and reciprocity bounds the dual.
  obtain ⟨A, R, h_count⟩ := T.exists_length_tiedSelmer_le hJ hV hN ha
  calc length O (T.tiedSelmer J J x i a)
    _ ≤ length O (T.dualSelmer hJ hV hN ha A R) + T.placesTerm := h_count
    _ ≤ T.globalTerm + T.placesTerm := add_le_add_left
      (T.length_dualSelmer_le hJ hV hN ha A R hz hz_unit
        fun P l hl ↦ h_le_frobInTameImage P l hl hz) _

/-- Let `IsTiedPrimes ℓ S₀ V W N P₀ J x` hold: primes outside `S₀` with data and slopes to level
`ℓ ^ N`, the first one `P₀` with slope `0` and Frobenius element in `W`, and `V i` at Frobenius
elements with nonzero slope for `i`; here `V i g` says that `g` acts trivially on `T / ℓ ^ M`. Let
`M < N` and let `ϖ` be a uniformizer with `ϖ ^ e ∣ ℓ ^ M`. The tied Selmer group `Sel(J)` consists
of the cocycles with the local conditions of `T`, unramified outside `T.places ∪ J ∪ J̄`, with the
ties `z(γ_v) = slope • z(φ_v)` at `v ∈ J` and `v̄`. Suppose that modulo `ϖ ^ k`, for all `1 ≤ k ≤ e`
and all new auxiliary primes `P` (those that can be added to `J` with any slope for `i`), each
member lies in `T.frobInTameImage`: its values at the Frobenius element `φ` and at `φ^{-c}` are the
values at the tame generator `γ` and at `γ^{-c}` of a class with the ties of `J` that may ramify
also at `P` and `P̄`. Then `Sel(J)` modulo `ϖ ^ e` has length at most `T.globalTerm` plus
`T.placesTerm`. -/
lemma length_tiedSelmer_pow_le {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ}
    (hJ : IsTiedPrimes ℓ S₀ V W N P₀ J x) (hV : ∀ g : Gal(Ω/E), V i g ↔ reduceModPow ℓ M T.ρ g = 1)
    (hN : M < N) (he : ϖ ^ e ∣ ℓ ^ M)
    (h_le_frobInTameImage : ∀ k ∈ Icc 1 e, ∀ (P : FinPlace E) (l : AuxPrimeData E (ℓ ^ N)),
      IsNewAuxiliaryPrime ℓ V S₀ J P₀ x i P l →
        T.tiedSelmer J J x i (ϖ ^ k) ≤ T.frobInTameImage J x i (ϖ ^ k) P l) :
    length O (T.tiedSelmer J J x i (ϖ ^ e)) ≤ T.globalTerm + T.placesTerm := by
  -- Pass to a level `ϖ ^ k` where the group is no shorter and, unless `k = 0`, has a unit value.
  obtain ⟨k, hk, h_le, h_unit⟩ := exists_length_selmerModule_pow_le T.ρ hϖ
    (unionWithConj T.places J) (T.classRelations ∪ tieRelations J x i) e
  refine h_le.trans ?_
  obtain rfl | hk₀ := eq_or_ne k 0
  · have : Subsingleton (QuotSpan (ϖ ^ 0)) := Ideal.Quotient.subsingleton_iff.2 (by simp)
    exact length_eq_zero.trans_le zero_le
  · exact T.length_tiedSelmer_le_of_isUnit hJ hV hN ((pow_dvd_pow ϖ hk).trans he) (h_unit hk₀)
      (h_le_frobInTameImage k (mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 hk₀, hk⟩))

end SelmerDatum

variable {n : ι → Type} [∀ i : ι, Fintype (n i)] [∀ i : ι, DecidableEq (n i)]
  (T : ∀ i : ι, SelmerDatum ℓ S₀ g₀ O (n i))

/-! ### The loop over all data and levels -/

/-- The sum of the lengths of the tied Selmer groups `Sel(J)` of `T i` modulo `ϖ ^ k`, over all data
`i` and all levels `1 ≤ k ≤ i₀`. -/
def totalTiedLength [Fintype ι] (ϖ : O) (i₀ : ℕ) (J : Finset (FinPlace E)) {N : ℕ}
    (x : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)) : ℕ∞ :=
  ∑ p ∈ univ ×ˢ Icc 1 i₀, length O ((T p.1).tiedSelmer J J x p.1 (ϖ ^ p.2))

section Steps

variable {M N : ℕ} {V : ι → Gal(Ω/E) → Prop} {W : Set Gal(Ω/E)} {P₀ : FinPlace E}
  {J : Finset (FinPlace E)} {x : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)}

open scoped Classical in
/-- Let `IsTiedPrimes ℓ S₀ V W N P₀ J x` hold: primes outside `S₀`, the first one `P₀` with
Frobenius element in `W`, with slopes and with data in `AuxPrimeData E (ℓ ^ N)`. Let `P` with data
`l` be a new auxiliary prime for `i`: one that can be added to `J` with any slope for `i`, so
`P, P̄ ∉ S₀ ∪ J` and `V i` holds at `l.frob`. Let `ϖ ^ e ∣ ℓ ^ M` and let the residue field be
finite with more than `2 · card (n i) · e + 1` elements. Suppose that, for some `1 ≤ k ≤ e`, some
member of the tied Selmer group of `T i` modulo `ϖ ^ k` does not lie in `frobInTameImage`: its
values at `φ, φ^{-c}` (`φ = l.frob`) are not the values at `γ, γ^{-c}` (`γ = l.tameGenerator`) of a
class with the ties of `J` that may ramify also at `P` and `P̄`. Then `P` can be added, with a unit
slope for datum `i` and slope `0` for the others, so that `totalTiedLength`, the sum over all data
and all levels `ϖ ^ m`, `1 ≤ m ≤ e`, of the lengths of the tied Selmer groups, drops. -/
lemma exists_slope_totalTiedLength_lt [Fintype ι] [DecidableEq ι] {ϖ : O} {e k : ℕ} {i : ι}
    (h_room : 2 * Fintype.card (n i) * e + 1 < Nat.card (ResidueField O))
    (hJ : IsTiedPrimes ℓ S₀ V W N P₀ J x) {P : FinPlace E} {l : AuxPrimeData E (ℓ ^ N)}
    (hl : IsNewAuxiliaryPrime ℓ V S₀ J P₀ x i P l) (he : ϖ ^ e ∣ ℓ ^ M) (hk : k ∈ Icc 1 e)
    (h_fail : ¬(T i).tiedSelmer J J x i (ϖ ^ k) ≤ (T i).frobInTameImage J x i (ϖ ^ k) P l) :
    ∃ s : Oˣ, totalTiedLength T ϖ e (insert P J) (update x P (l, Pi.single i ↑s)) <
      totalTiedLength T ϖ e J x := by
  have h_dvd (m : ℕ) (hm : m ∈ Icc 1 e) : ϖ ^ m ∣ ℓ ^ M :=
    (pow_dvd_pow ϖ (mem_Icc.1 hm).2).trans he
  let x' (u : Oˣ) : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O) :=
    update x P (l, Pi.single i ↑u⁻¹)
  -- At each level `m`, at most `2 · card (n i)` residues in `bad m` are to be avoided, so some unit
  -- `u` is good for all levels.
  choose! bad h_card h_bad using fun (m : ℕ) (hm : m ∈ Icc 1 e) ↦
    (T i).exists_length_tiedSelmer_insert_le hJ hl (h_dvd m hm)
  have h_all : #((Icc 1 e).biUnion bad) ≤ 2 * Fintype.card (n i) * e := by
    simpa [mul_comm] using card_biUnion_le_card_mul (Icc 1 e) bad _ h_card
  obtain ⟨u, hu⟩ := exists_unit_residue_notMem ((Nat.add_le_add_right h_all 1).trans_lt h_room)
  have h_row (m : ℕ) (hm : m ∈ Icc 1 e) :
      length O ((T i).tiedSelmer (insert P J) (insert P J) (x' u) i (ϖ ^ m)) ≤
        length O ↥((T i).tiedSelmer J J x i (ϖ ^ m) ⊓ (T i).frobInTameImage J x i (ϖ ^ m) P l) :=
    h_bad m hm u fun h ↦ hu (mem_biUnion.2 ⟨m, hm, h⟩)
  -- No group grows: for the other data the slope is `0`, so the new group lies in the old one.
  have h_le (j : ι) (m : ℕ) (hm : m ∈ Icc 1 e) :
      length O ((T j).tiedSelmer (insert P J) (insert P J) (x' u) j (ϖ ^ m)) ≤
        length O ((T j).tiedSelmer J J x j (ϖ ^ m)) := by
    obtain rfl | hj := eq_or_ne j i
    · exact (h_row m hm).trans (length_mono inf_le_left)
    · refine length_mono (((T j).tiedSelmer_update_le hl.notMem _).trans ?_)
      simpa [hj] using (T j).tiedSelmer_insert_inf_ker_le hJ hl (h_dvd m hm)
  have h_fin (j : ι) (m : ℕ) (hm : m ∈ Icc 1 e) :
      length O ((T j).tiedSelmer J J x j (ϖ ^ m)) ≠ ⊤ :=
    have := (T j).finite_tiedSelmer (h_dvd m hm) J J x j
    length_ne_top
  -- Where the inclusion fails, the group gets shorter.
  have h_lt : length O ((T i).tiedSelmer (insert P J) (insert P J) (x' u) i (ϖ ^ k)) <
      length O ((T i).tiedSelmer J J x i (ϖ ^ k)) := by
    refine (h_row k hk).trans_lt ?_
    rw [← relLength_add_length_inf ((T i).tiedSelmer J J x i (ϖ ^ k))
      ((T i).frobInTameImage J x i (ϖ ^ k) P l)]
    exact ENat.lt_add_left (ne_top_of_le_ne_top (h_fin i k hk) (length_mono inf_le_left))
      (pos_iff_ne_zero.2 (mt relLength_eq_zero.1 h_fail))
  exact ⟨u⁻¹, sum_lt_sum_of_ne_top (fun (j, m) h_mem ↦ h_le j m (mem_product.1 h_mem).2)
    (fun (j, m) h_mem ↦ h_fin j m (mem_product.1 h_mem).2) (mk_mem_product (mem_univ i) hk) h_lt⟩

/-- Let `IsTiedPrimes ℓ S₀ V W N P₀ J x` hold: primes outside `S₀` with data and slopes to level
`ℓ ^ N`, the first one `P₀` with slope `0` and Frobenius element in `W`, and `V i` at Frobenius
elements with nonzero slope for `i`; here `V i g` says that `g` acts trivially on `T i / ℓ ^ M`. Let
`M < N`, let `ϖ` be a uniformizer with `ϖ ^ e ∣ ℓ ^ M`, and let the residue field be finite with
more than `2 · card (n i) · e + 1` elements for all `i`. Then there are tied primes `J'` with data
`x'` and the same `P₀` whose number is at most `#J + totalTiedLength`, the latter summing the
lengths of the tied Selmer groups for `J` over all data and all levels `ϖ ^ k`, `1 ≤ k ≤ e`, and
whose tied Selmer groups modulo `ϖ ^ e` have length at most `globalTerm` plus `placesTerm`. -/
lemma exists_isTiedPrimes_length_tiedSelmer_le [Fintype ι] {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ}
    (h_room : ∀ i : ι, 2 * Fintype.card (n i) * e + 1 < Nat.card (ResidueField O))
    (hV : ∀ (i : ι) (g : Gal(Ω/E)), V i g ↔ reduceModPow ℓ M (T i).ρ g = 1) (hN : M < N)
    (he : ϖ ^ e ∣ ℓ ^ M) (hJ : IsTiedPrimes ℓ S₀ V W N P₀ J x) :
    ∃ (J' : Finset (FinPlace E)) (x' : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)),
      IsTiedPrimes ℓ S₀ V W N P₀ J' x' ∧
      (#J' : ℕ∞) ≤ #J + totalTiedLength T ϖ e J x ∧
      ∀ i : ι,
        length O ((T i).tiedSelmer J' J' x' i (ϖ ^ e)) ≤ (T i).globalTerm + (T i).placesTerm := by
  classical
  -- Among the sets of tied primes whose size plus sum of lengths is at most that of `(J, x)`, take
  -- one with the least sum of lengths.
  let Good : Set (Finset (FinPlace E) × (FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O))) :=
    {p | IsTiedPrimes ℓ S₀ V W N P₀ p.1 p.2 ∧
      #p.1 + totalTiedLength T ϖ e p.1 p.2 ≤ #J + totalTiedLength T ϖ e J x}
  obtain ⟨⟨J', x'⟩, ⟨hJ', h_total⟩, h_min⟩ :=
    (InvImage.wf (fun p ↦ totalTiedLength T ϖ e p.1 p.2) wellFounded_lt).has_min Good
      ⟨(J, x), hJ, le_rfl⟩
  refine ⟨J', x', hJ', le_of_add_le_left h_total, fun i ↦
    (T i).length_tiedSelmer_pow_le hϖ hJ' (hV i) hN he fun k hk P l hl ↦ ?_⟩
  -- If an inclusion failed, a further step would be possible.
  by_contra h_fail
  obtain ⟨s, h_lt⟩ := exists_slope_totalTiedLength_lt T (h_room i) hJ' hl he hk h_fail
  let x'' : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O) := update x' P (l, Pi.single i ↑s)
  -- One more prime is paid for by the drop of the sum.
  have h_total' : #(insert P J') + totalTiedLength T ϖ e (insert P J') x'' ≤
      #J' + totalTiedLength T ϖ e J' x' := by
    rw [card_insert_of_notMem hl.notMem, Nat.cast_succ, add_assoc, add_comm 1]
    exact add_le_add_right (Order.add_one_le_of_lt h_lt) _
  exact h_min (insert P J', x'') ⟨hJ'.insert_of_isNewAuxiliaryPrime hl s, h_total'.trans h_total⟩
    h_lt

end Steps

/-- Let `ϖ ^ e ∣ ℓ ^ M`, and fix any `V` and `W`. `IsTiedPrimes ℓ S₀ V W N P₀ J x` says that the
primes of `J` lie outside `S₀` and carry slopes `(x v).2` and data in `AuxPrimeData E (ℓ ^ N)`
(place, Frobenius element `φ_v`, tame generator `γ_v`, character to `ℤ / ℓ ^ N`), with `φ_v ∈ W`
for `v = P₀` and `V i` at `φ_v` where the slope for `i` is not zero. A tied Selmer group consists of
the cocycles with the local conditions of its datum, unramified outside its places, `J` and `J̄`,
with `z(γ_v) = slope • z(φ_v)` at `v ∈ J` and `v̄`. If all slopes are `0`, the sum
`totalTiedLength` of the lengths of these groups for all data `T i` modulo `ϖ ^ k`, `1 ≤ k ≤ e`,
has a finite bound `b` that depends neither on `N` nor on `P₀`, `J` and `x`. The proof takes the
sum of the lengths of the groups `Sel(∅)` without auxiliary primes. -/
lemma exists_totalTiedLength_le [Fintype ι] (V : ι → Gal(Ω/E) → Prop) (W : Set Gal(Ω/E)) {ϖ : O}
    {e M : ℕ} (he : ϖ ^ e ∣ ℓ ^ M) :
    ∃ b : ℕ, ∀ {N : ℕ} {P₀ : FinPlace E} {J : Finset (FinPlace E)}
      {x : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)},
      IsTiedPrimes ℓ S₀ V W N P₀ J x → (∀ v ∈ J, (x v).2 = 0) → totalTiedLength T ϖ e J x ≤ b := by
  have h_dvd (k : ℕ) (hk : k ∈ Icc 1 e) : ϖ ^ k ∣ ℓ ^ M :=
    (pow_dvd_pow ϖ (mem_Icc.1 hk).2).trans he
  -- The groups `Sel(∅)` are finite.
  have h_fin (i : ι) (k : ℕ) (hk : k ∈ Icc 1 e) :
      length O (selmerModule (T i).ρ (T i).places (T i).classRelations (QuotSpan (ϖ ^ k))) ≠ ⊤ :=
    have : NeZero (ϖ ^ k) := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne _) (h_dvd k hk)⟩
    have := finite_selmerModule (h_dvd k hk) ((T i).isLocallyConstant M) (T i).places.finite_toSet
      (T i).classRelations
    length_ne_top
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = ∑ p ∈ (univ : Finset ι) ×ˢ Icc 1 e,
      length O (selmerModule (T p.1).ρ (T p.1).places (T p.1).classRelations
        (QuotSpan (ϖ ^ p.2))) :=
    ENat.ne_top_iff_exists.1
      (ENat.sum_ne_top.2 fun (i, k) h_mem ↦ h_fin i k (mem_product.1 h_mem).2)
  refine ⟨b, fun hJ h_slope ↦ ?_⟩
  rw [totalTiedLength, hb]
  exact sum_le_sum fun (i, k) h_mem ↦ length_mono <| (T i).tiedSelmer_le_of_slope_eq_zero hJ
    (h_dvd k (mem_product.1 h_mem).2) fun v hv ↦ congrFun (h_slope v hv) i

open IsDiscreteValuationRing in
/-- Descent. Let `E` be a CM field, `Gal(Ω/E)` the Galois group of the algebraic closure `Ω` of
`ℚ` over it, `ℓ` a prime, `O` the integer ring of a finite extension of `ℚ_ℓ`, and `T i` finitely
many Selmer data: Galois lattices `O ^ (n i)` of rank `card (n i)` with local conditions, unramified
outside the finite set `S₀` of places, on which `det(g - 1) ≠ 0` for `g = g₀, g₀^{-c}`, where
`g^{-c}` is the inverse of the complex conjugate of `g`. Let `g₀` be inertial at a place of `S₀`
prime to `ℓ`, let `W` be a neighbourhood of `g₀`, and let the residue field have more than
`2 · card (n i) · v(ℓ ^ M) + 1` elements for all `i`. There is an integer `s` such that for every
`N > M` there is a set `J` of at most `s` primes that satisfies `IsTiedPrimes` and whose tied
Selmer groups modulo `ℓ ^ M` have length at most `globalTerm + placesTerm`.

`IsTiedPrimes` says that the primes `v ∈ J` have prime norm, that they and their conjugates are
distinct and outside `S₀`, and that each carries slopes `(x v).2` and data `(x v).1` (place,
Frobenius element `φ_v`, tame generator `γ_v`, character to `ℤ / ℓ ^ N`); the first prime `P₀` has
slope `0` and `φ_v ∈ W`, no other prime of `J` or `S₀` divides its norm, the characters take
prescribed values at the Frobenius elements of the later primes, and `φ_v` and `φ_v^{-c}` act
trivially on `T i / ℓ ^ M` where the slope for `i` is not zero.

The tied Selmer group `(T i).tiedSelmer J J x i (ℓ ^ M)` consists of the classes `z` modulo `ℓ ^ M`
that satisfy the local conditions, are unramified outside `(T i).places ∪ J ∪ J̄`, and satisfy the
ties `z(γ_v) = (x v).2 i • z(φ_v)` between tame generator and Frobenius element at the primes
`v ∈ J` and their conjugates. For a datum `T`, `T.globalTerm` is the supremum over `a ≠ 0` of the
lengths of `Hom_G(T / a, (T / a)^{*c})`, with `*c` the dual twisted by complex conjugation, and
`T.placesTerm` is the sum, over the places of `T.places` prime to `ℓ`, of the supremum over
`a ≠ 0` of the excess length of the local cocycles over `T / a`. -/
theorem exists_isTiedPrimes_card_le_and_length_le [Finite ι]
    (hg₀ : g₀ ∈ inertiaAbove (S₀ \ placesDividing E ℓ)) (M : ℕ)
    (h_room : ∀ i : ι,
      2 * Fintype.card (n i) * addVal O (ℓ ^ M) + 1 < Nat.card (ResidueField O))
    {W : Set Gal(Ω/E)} (hW : W ∈ nhds g₀) :
    ∃ s : ℕ, ∀ N > M, ∃ (P₀ : FinPlace E) (J : Finset (FinPlace E))
      (x : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)),
      IsTiedPrimes ℓ S₀ (fun (i : ι) (g : Gal(Ω/E)) ↦ reduceModPow ℓ M (T i).ρ g = 1) W N P₀ J x ∧
      #J ≤ s ∧
      ∀ i : ι,
        length O ((T i).tiedSelmer J J x i (ℓ ^ M)) ≤ (T i).globalTerm + (T i).placesTerm := by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible O
  obtain ⟨e, he⟩ : ∃ e : ℕ, Associated ((ℓ : O) ^ M) (ϖ ^ e) :=
    associated_pow_irreducible (NeZero.ne _) hϖ
  rw [(addVal_eq_iff_associated _ _).2 he, hϖ.addVal_pow] at h_room
  let V (i : ι) (g : Gal(Ω/E)) : Prop := reduceModPow ℓ M (T i).ρ g = 1
  obtain ⟨b, hb⟩ := exists_totalTiedLength_le T V W he.symm.dvd
  refine ⟨1 + b, fun N hN ↦ ?_⟩
  -- Start from the first prime alone, with slopes `0`, and descend.
  obtain ⟨P₀, l, hJ⟩ := exists_isTiedPrimes_singleton (O := O) hg₀ hW V N
  obtain ⟨J, x, hJ', h_card, h_short⟩ := exists_isTiedPrimes_length_tiedSelmer_le T hϖ
    (fun i ↦ mod_cast h_room i) (fun _ _ ↦ Iff.rfl) hN he.symm.dvd hJ
  refine ⟨P₀, J, x, hJ', ?_, fun i ↦ ?_⟩
  · exact_mod_cast h_card.trans (add_le_add_right (hb hJ fun _ _ ↦ rfl) _)
  · -- The ideals `(ℓ ^ M)` and `(ϖ ^ e)` are equal.
    refine le_of_eq_of_le ?_ (h_short i)
    unfold SelmerDatum.tiedSelmer QuotSpan
    rw [Ideal.span_singleton_eq_span_singleton.2 he]

end New.Selmer

end
