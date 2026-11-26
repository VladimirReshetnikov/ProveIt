import Lib.ClassField.GaloisCohomology.TameSelmerCocycles
import Lib.Cyclotomic.Kolyvagin.ReciprocityComponentBounds

/-!
# Detecting unramified cocycles and a uniform bound for a model of the odd part of Ш

Let E be a number field inside ℚ(μ_N) and let l be a prime. Polynomially many elements of the
absolute Galois group of E detect the locally constant cocycles of a Tate twist that take values in
O / lⁿ and are unramified outside l. For a CM field E inside ℚ(μ_N), this gives one integer X of
explicit size whose valuation bounds the length of a module of odd cocycles at every prime l.

## Overview of this theory

For a CM field `E` inside `ℚ(μ_N)`, and `O` the integers of a finite extension of `ℚ_ℓ` with enough
roots of unity for the characters mod `N`, `New.Selmer.shaOdd` is a module of cocycles of `Gal(Ω/E)`
with values in `O/ℓⁿ(-e)`, modelled on the odd part of `Ш¹(E, O/ℓⁿ(-e))`; no comparison with `Ш¹` is
proved. For `e = 0` it consists of the everywhere unramified homomorphisms. Here `ℓ` is a prime and
`e, n ≥ 0`.

* `New.exists_length_shaOdd_le`: for each `t ≥ 0` there is an integer `X`, depending on `E`, `N` and
  `t`, with `0 < X ≤ 2^(4T²⁷) h_E`. Here `T = N + t + 3` and `h_E` is the class number of `E`. The
  length of `New.Selmer.shaOdd` over `O` is at most `v_O(X)` for all `ℓ`, `O`, `n` and all `e < t`.

No equality of characteristic ideals (the main conjecture of Mazur and Wiles) is proved.

Proof outline: 1. `Voronoi`: `New.OddPart.exists_isStickelbergerBound` gives, for `e ≥ 1`, an
integer `0 < X ≤ 2^((N+e+3)⁶)` satisfying `New.OddPart.IsStickelbergerBound N e X`. This is a
bounded divisibility of twisted Stickelberger sums.

2. `Stickelberger`: `New.OddPart.exists_isJacobiFamily` fixes a prime `p`, a place `B` above `p` and
   any `c ∈ ℕ`. It builds a map `J` from `ℚ/ℤ` to units, a variant of Jacobi sums. For `p ≡ 1 mod M`
   and `Mx = 0`, `J(x)` is a unit at places not above `p`. It has absolute value one in every
   complex embedding. Its order at `B` is `New.OddPart.floorDiff c x`. It also satisfies Galois and
   product relations.
3. `Kolyvagin.DerivativeCocycles`: `New.OddPart.exists_isKolyvaginSystem` builds
   `cyc^(e+1)ψ`-cocycles `κ_S : G_ℚ → O/ℓⁿ`. Here `cyc` is the `ℓ`-adic cyclotomic character and `ψ`
   a Dirichlet character mod `N`. The sets `S` range over subsets of a finite set `P` of primes
   `≡ 1 mod cNℓⁿ`, and `p ≡ 1 mod Nℓⁿ∏P`. For `q ∈ P ∖ S` and a place `A` above `q`, the value of
   `κ_S` at a Frobenius at `A` is a value of `κ_{S∪{q}}` on inertia at `A`.
4. `Kolyvagin.ReciprocityComponentBounds`: take `e ≥ 1` and `cycᵉψ` odd. Then `4X²` kills
   `New.OddPart.component`, a set of cocycles `G_ℚ → O/ℓ^ν` attached to `cycᵉψ`
   (`New.OddPart.nsmul_component_eq_zero`, an analogue of Stickelberger's theorem). If moreover
   `ℓ > N + e + 3`, there are `v_ℓ(X) + 1` elements of `G_ℚ` with the following property: a cocycle
   in the component vanishing at all of them is zero
   (`New.OddPart.exists_detecting_points_component`).
5. `OddSha`: for `e > 0`, the group is split by characters `ψ`, and step 4 gives an integer killing
   `New.Selmer.shaOdd`. A bounded number of suitable elements of `G_E` suffice to test whether a
   cocycle is zero. For small `ℓ` this uses ray classes, and for large `ℓ` it uses step 4. Together
   these bound the length. For `e = 0`, the class number `h_E` serves.

## Main definitions and results

* `New.OddPart.exists_detecting_points_cocycles`: the detecting set and the bound on its size.
* `New.OddPart.nsmul_shaOdd_eq_zero_of_isStickelbergerBound`: an integer that kills
  `New.Selmer.shaOdd` for e ≠ 0, at every prime l.
* `New.OddPart.length_shaOdd_le_of_le_sq`, `New.OddPart.length_shaOdd_le_of_sq_lt`: the bounds on
  the length for small and for large primes l.

Notions from other files:
* `Ω`: the fixed algebraic closure of ℚ; `Gal(Ω/E)` is its group of automorphisms
  over `E`, the absolute Galois group of `E`.
* `New.Selmer.tateTwist`: the rank-one representation O(−e), the character cyc^{−e} with values in
  O, as 1 × 1 matrices.
* `New.conjGal`: the endomorphism g ↦ c g c of Gal(Ω / E), where c is `New.cmConj`, the complex
  conjugation fixed in Gal(Ω / ℚ); a cocycle z is odd if z (c g c) = -z g.

## Relation to the literature

For large `l` a bound of this kind follows from the Iwasawa main conjecture of Mazur and Wiles; only
an upper bound for the length at finite level, by an integer of explicit size, is proved here. One
non-zero integer serves at all primes, 2 included; small primes are handled by a crude count of
generators of the ray class group. Source: B. Mazur, A. Wiles, Class fields of abelian extensions of
Q, Invent. Math. 76 (1984); C. Greither, Ann. Inst. Fourier 42 (1992), Thm 3.2.
-/

/-! ## Few Galois elements detecting unramified cocycles -/

section DetectingPoints

open New NumberField IsCyclotomicExtension.Rat Selmer Ideal NeZero Nat Function
  IsDedekindDomain.HeightOneSpectrum

/-- A number field `K` has at most `[K : ℚ]` places above a prime `l`. -/
lemma New.ncard_placesDividing_le_finrank (K : Type) [Field K] [EmbeddedNumberField K] (l : ℕ)
    [ThePrime l] : (placesDividing K l).ncard ≤ Module.finrank ℚ K := by
  have hl : span {(l : ℤ)} ≠ ⊥ := by simp [NeZero.ne l]
  grw [← ncard_primesOver_le_finrank (span {(l : ℤ)})]
  refine (Set.ncard_congr' (.trans (.subtypeEquivRight fun P ↦ ?_) (equivPrimesOver _ hl))).le
  simp [placesDividing, map_span]

/-- For `K = ℚ(μ_M)`, the class number times the index of the ideles that are `M`-th powers above
the prime `l` is at most `2 ^ (M³ + 5 M² + M)`. -/
lemma New.OddPart.classNumber_mul_index_idelesPowAt_le (M l : ℕ) [NeZero M] [ThePrime l] :
    classNumber (cycloField M) * (idelesPowAt (placesDividing (cycloField M) l) M).index ≤
      2 ^ (M ^ 3 + 5 * M ^ 2 + M) := by
  -- With `d = [K : ℚ] ≤ M`, `|disc K| ≤ M ^ d` and `M ≤ 2 ^ M`, the bounds `classNumber_le` and
  -- `index_idelesPowAt_ne_zero_and_le` become powers of `2`.
  set K : IntermediateField ℚ Ω := cycloField M
  have hM_le : M ≤ 2 ^ M := M.lt_two_pow_self.le
  have h_one : 1 ≤ 2 ^ M := Nat.one_le_two_pow
  have h_deg : Module.finrank ℚ K ≤ M := by grw [finrank M, totient_le]
  have h_discr : (discr K).natAbs ≤ (2 ^ M) ^ M := by
    grw [natAbs_discr M, Nat.div_le_self, ← finrank M K]
    exact (Nat.pow_le_pow_left hM_le _).trans (Nat.pow_le_pow_right h_one h_deg)
  have h_class : classNumber K ≤ (2 ^ M * (2 ^ M) ^ M) ^ (M + 1) := by
    grw [classNumber_le K, h_discr, pow_le_pow_right₀ one_le_two h_deg]
    exact Nat.pow_le_pow_right (by positivity) (Nat.succ_le_succ h_deg)
  have h_index : (idelesPowAt (placesDividing K l) M).index ≤ (2 ^ M) ^ (2 * M + M) := by
    refine (index_idelesPowAt_ne_zero_and_le M (placesDividing K l)).right.trans
      ((Nat.pow_le_pow_left hM_le _).trans (Nat.pow_le_pow_right h_one ?_))
    linarith [ncard_placesDividing_le_finrank K l, h_deg]
  calc classNumber K * (idelesPowAt (placesDividing K l) M).index
      ≤ (2 ^ M * (2 ^ M) ^ M) ^ (M + 1) * (2 ^ M) ^ (2 * M + M) := Nat.mul_le_mul h_class h_index
    _ = 2 ^ (M ^ 3 + 5 * M ^ 2 + M) := by ring

/-- The count of detecting points: let `M = N l²` with `2 < M`, `N ≤ y` and `l ≤ y ^ 2`. If
`c ≤ M ^ 3 + 5 M ^ 2 + M`, then `φ(M) + c ≤ y ^ 20`. -/
private lemma totient_add_le_pow_twenty {N l y c : ℕ} (hNy : N ≤ y) (hly : l ≤ y ^ 2)
    (hM_gt : 2 < N * l ^ 2) (hc : c ≤ (N * l ^ 2) ^ 3 + 5 * (N * l ^ 2) ^ 2 + N * l ^ 2) :
    φ (N * l ^ 2) + c ≤ y ^ 20 := by
  set M : ℕ := N * l ^ 2 with hM
  have hMy : M ≤ y ^ 5 := by grw [hM, hNy, hly, ← pow_mul, ← _root_.pow_succ']
  calc φ M + c ≤ M + (M ^ 3 + 5 * M ^ 2 + M) := Nat.add_le_add (totient_le M) hc
    -- `M³ + 5 M² + 2 M ≤ M⁴` for `M ≥ 3`
    _ ≤ M ^ 4 := by nlinarith [(M ^ 3).zero_le, (M ^ 2).zero_le]
    _ ≤ (y ^ 5) ^ 4 := Nat.pow_le_pow_left hMy 4
    _ = y ^ 20 := by ring

/-- Let `K = ℚ(μ_M)` and `l` a prime. A finite family of integers `m i ≥ 2` whose product divides
the class number of `K` times the index of the ideles that are `M`-th powers above `l` has at
most `M ^ 3 + 5 M ^ 2 + M` members, since `2 ^ card ι ≤ ∏ m i`. -/
private lemma card_le_of_prod_dvd_classNumber_mul_index {M l : ℕ} [NeZero M] [ThePrime l]
    {ι : Type} [Fintype ι] {m : ι → ℕ} (hm : ∀ i : ι, 2 ≤ m i)
    (h_dvd : ∏ i : ι, m i ∣
      classNumber (cycloField M) * (idelesPowAt (placesDividing (cycloField M) l) M).index) :
    Fintype.card ι ≤ M ^ 3 + 5 * M ^ 2 + M := by
  refine (Nat.pow_le_pow_iff_right one_lt_two).mp ?_
  calc 2 ^ Fintype.card ι ≤ ∏ i, m i := Finset.pow_card_le_prod Finset.univ m 2 fun i _ ↦ hm i
    _ ≤ classNumber (cycloField M) * (idelesPowAt (placesDividing (cycloField M) l) M).index :=
      Nat.le_of_dvd (Nat.mul_pos (classNumber_pos _)
        (index_idelesPowAt_ne_zero_and_le M _).left.bot_lt) h_dvd
    _ ≤ 2 ^ (M ^ 3 + 5 * M ^ 2 + M) := OddPart.classNumber_mul_index_idelesPowAt_le M l

open Matrix.Module in
/-- An element of `Gal(Ω/E)` with the same `l`-adic cyclotomic character as some `x` fixing `μ_M`
acts trivially, in the twist `tateTwist l E O e`, on the vectors over `O / lⁿ` killed by `M`. -/
private lemma tateTwist_smul_eq_self_of_nsmul_eq_zero {E : Type} [Field E]
    [EmbeddedNumberField E] {l M : ℕ} [NeZero M] [ThePrime l] {O : Type} [CommRing O]
    [PadicIntegerRing O l] {n e : ℕ} {h : Gal(Ω/E)} (x : cycloGalGroup M)
    (h_char : cyclotomicChar Ω l h = cyclotomicChar Ω l (x : Gal(Ω/ℚ)))
    {a : Unit → QuotSpan (l ^ n : O)} (ha : M • a = 0) :
    tateTwist l E O e h • a = a := by
  have h_fix : (cyclotomicPowDirichlet l e (1 : DirichletCharacter O 1)
      ((x⁻¹ : cycloGalGroup M) : Gal(Ω/ℚ))).val • a = a :=
    (OddPart.cyclotomicPowDirichlet_smul_eq_self (O := O) (ψ := 1)
      (cyclotomicCharMod_eq_one_of_dvd (one_mul M).dvd x⁻¹.prop) ha).left
  -- The twist at `h` is the value of `cyc ^ e` at `x⁻¹`.
  -- Without `-map_inv` the factor of the trivial character is left as an inverse.
  simpa [cyclotomicPowDirichlet, tateTwist, cyclotomicInv, h_char,
    map_inv (cyclotomicChar Ω l), -map_inv] using h_fix

/-- If a place `v` of an intermediate field `K` of `Ω/ℚ` is prime to `l`, then so is some place of
`E` lying under the chosen valuation subring `placeOver v` of `Ω`. -/
private lemma exists_notMem_placesDividing_isPlaceOver (E : Type) [Field E]
    [EmbeddedNumberField E] {l : ℕ} [ThePrime l] {K : IntermediateField ℚ Ω} [NumberField K]
    {v : FinPlace K} (hv : v ∉ placesDividing K l) :
    ∃ w : FinPlace E, w ∉ placesDividing E l ∧ IsPlaceOver (placeOver v) w := by
  have hv_over : IsPlaceOver (placeOver v) v := v.isPlaceOver_placeOver
  obtain ⟨w, hw, -⟩ := (hv_over.isPlaceOver_below (K := ℚ)).exists_above (L := E)
  exact ⟨w, fun h_mem ↦ hv
    (hv_over.valuation_natCast_lt_one_iff.mp (hw.valuation_natCast_lt_one_iff.mpr h_mem)), hw⟩

/-- Few points detect unramified cocycles. Let `E` be a number field whose image in the algebraic
closure `Ω` lies in `ℚ(μ_N)` (`h_sub`), and `l` a prime. There is a finite set `s` in `Gal(Ω/E)`
with (a) `#s ≤ y ^ 20` whenever `N ≤ y` and `l ≤ y ^ 2`; (b) for all `O` (the integers of a finite
extension of `ℚ_l`), `n`, `e`, a cocycle `z` in `selmerModule (tateTwist l E O e) (placesDividing E
l) ∅ (O / lⁿ)` (locally constant, for the character `cyc⁻ᵉ`, unramified off `l`) that vanishes on
`s` is zero.

This is a cocycle analogue, with the crude bound `y ^ 20`, of the class field theory bound on the
number of generators of the Galois group of the maximal pro-`l` extension unramified outside `l`. -/
lemma New.OddPart.exists_detecting_points_cocycles {N : ℕ} {E : Type} [NeZero N] [Field E]
    [EmbeddedNumberField E] (h_sub : ∀ x : E, algebraMap E Ω x ∈ cycloField N) (l : ℕ)
    [ThePrime l] :
    ∃ s : Finset Gal(Ω/E),
      -- (a)
      (∀ y : ℕ, N ≤ y → l ≤ y ^ 2 → s.card ≤ y ^ 20) ∧
      -- (b)
      ∀ {O : Type} [CommRing O] [PadicIntegerRing O l] {n e : ℕ},
        ∀ z ∈ selmerModule (tateTwist l E O e) (placesDividing E l) ∅ (QuotSpan (l ^ n : O)),
          (∀ g ∈ s, z g = 0) → z = 0 := by
  classical
  -- Put `M = N l²`, `K = ℚ(μ_M)`. The points are representatives of the cosets of `G_K` in `G_E`
  -- and the points of `exists_detecting_points_hom` for `K`. If `M • z = 0`, then `G_K` acts
  -- trivially on the values of `z`, so `z` is a homomorphism on `G_K` and
  -- `exists_detecting_points_hom` applies. That `M • z = 0` comes from an induction on the power
  -- of `l` that kills `z`, as `l ∣ M`.
  set M : ℕ := N * l ^ 2 with hM
  -- the inclusion `r : G_K → G_E` (`E ⊆ ℚ(μ_N) ⊆ K`)
  have h_fix (g : cycloGalGroup M) : cyclotomicCharMod Ω N (g : Gal(Ω/ℚ)) = 1 :=
    cyclotomicCharMod_eq_one_of_dvd ⟨l ^ 2, hM⟩ g.prop
  let r (g : cycloGalGroup M) : Gal(Ω/E) :=
    { (g : Gal(Ω/ℚ)) with commutes' := fun x ↦ h_sub x ⟨g, h_fix g⟩ }
  let K : IntermediateField ℚ Ω := cycloField M
  have hM_gt : 2 < M := by nlinarith [pos N, (Fact.out : 1 < l)]
  have hK_complex : IsTotallyComplex K := isTotallyComplex K hM_gt

  obtain ⟨ι, _, b, m, hm, h_dvd, h_detect⟩ := exists_detecting_points_hom (cycloGalGroup M)
    (placesDividing K l) M (index_idelesPowAt_ne_zero_and_le M (placesDividing K l)).left
  -- `G_K` is the kernel of `cyclotomicCharMod` on `G_E`, so a section of it gives coset
  -- representatives
  let f : Gal(Ω/E) →* (ZMod M)ˣ := cyclotomicCharMod Ω M
  refine ⟨.image (Sum.elim (invFun f) (r ∘ b)) .univ,
    fun y hNy hly ↦ Finset.card_image_le.trans ?_, ?_⟩
  · -- There are at most `φ(M)` cosets, and few points of `exists_detecting_points_hom`.
    have h_card : Fintype.card ι ≤ M ^ 3 + 5 * M ^ 2 + M :=
      card_le_of_prod_dvd_classNumber_mul_index hm h_dvd
    calc (Finset.univ : Finset ((ZMod M)ˣ ⊕ ι)).card = φ M + Fintype.card ι := by simp
      _ ≤ y ^ 20 := totient_add_le_pow_twenty hNy hly hM_gt h_card
  intro O _ _ n e z hz h_zero
  obtain ⟨k, hk⟩ : ∃ k : ℕ, l ^ k • z = 0 :=
    ⟨n, funext₂ fun g i ↦ nsmul_quot_eq_zero dvd_rfl (z g i)⟩
  induction k generalizing z with
  | zero => simpa using hk
  | succ k ih =>
    -- `M • z` is killed by `l ^ k` and vanishes at the points, so it is `0`
    have h_eq : l ^ k * M = N * l * l ^ (k + 1) := by ring
    have h_kill : l ^ k • M • z = 0 := by rw [smul_smul, h_eq, mul_smul, hk, smul_zero]
    have hMz : M • z = 0 := ih _ (nsmul_mem hz M) (fun g hg ↦ by simp [h_zero g hg]) h_kill
    obtain ⟨h_coc, h_unr, -, h_lc⟩ := mem_selmerModule_iff.mp hz
    -- on `G_K` the twist acts trivially on elements killed by `M`
    have h_add (x : cycloGalGroup M) (g : Gal(Ω/E)) : z (r x * g) = z (r x) + z g := by
      rw [h_coc, tateTwist_smul_eq_self_of_nsmul_eq_zero (h := r x) x rfl (congrFun hMz g)]
    -- an inertia group of `K` away from `l` lies in an inertia group of `E` away from `l`
    have h_unr' (v : FinPlace K) (hv : v ∉ placesDividing K l) (g : cycloGalGroup M)
        (hg : g ∈ inertiaGroup (cycloGalGroup M) (placeOver v)) : z (r g) = 0 := by
      obtain ⟨w, hw_notMem, hw⟩ := exists_notMem_placesDividing_isPlaceOver E hv
      exact h_unr _ ⟨w, hw_notMem, _, hw, hg⟩
    -- so `z` vanishes on `G_K`, by `exists_detecting_points_hom`
    have h_hom : IsUnramifiedTorsionHom (placesDividing K l) M (z ∘ r) :=
      { isLocallyConstant := h_lc.comp_continuous (continuous_of_equivariant_emb 1 fun _ _ ↦ rfl)
        map_mul := fun x g ↦ h_add x (r g)
        nsmul_eq_zero := fun g ↦ congrFun hMz (r g)
        unramified := h_unr' }
    have h_res : z ∘ r = 0 := (h_detect h_hom).right fun i ↦ h_zero _ (by simp)
    -- write `g = x * c` with `c` the representative of its coset and `x ∈ G_K`
    ext1 g
    let c : Gal(Ω/E) := invFun f (f g)
    have h_fc : f g = f c := by simp [c, invFun_eq]
    let x : cycloGalGroup M := ⟨(g / c).restrictScalars ℚ, f.div_mem_ker_iff.mpr h_fc⟩
    have hz_x : z (r x) = 0 := congrFun h_res x
    have hz_c : z c = 0 := h_zero c (by simp [c])
    calc z g = z (r x * c) := congrArg z (div_mul_cancel g c).symm
      _ = z (r x) + z c := h_add x c
      _ = 0 := by rw [hz_x, hz_c, add_zero]

open Matrix.Module in
/-- Few points in the kernel of the cyclotomic character detect. Let `E ⊆ ℚ(μ_N)` be a number
field, `l` a prime, and let `g₀` generate the absolute Galois group of `E` modulo the kernel of the
`l`-adic cyclotomic character. There is a finite set `s` of points such that (a) they lie in that
kernel; (b) their number is at most `y ^ 20` whenever `N ≤ y` and `l ≤ y ^ 2`; (c) a locally
constant cocycle with values in `O/l ^ n` twisted by `tateTwist l E O e`, unramified off `l`, that
vanishes at `g₀` and on `s` is zero. The same points serve for all `O`, `n` and `e`. -/
lemma New.OddPart.exists_detecting_points_mem_ker {N : ℕ} {E : Type} [NeZero N] [Field E]
    [EmbeddedNumberField E] (hE : ∀ x : E, algebraMap E Ω x ∈ cycloField N) (l : ℕ) [ThePrime l]
    {g₀ : Gal(Ω/E)} (hg₀ : (cyclotomicChar Ω l).IsGeneratorModKer g₀) :
    ∃ s : Finset Gal(Ω/E),
      (∀ g ∈ s, cyclotomicChar Ω l g = 1) ∧
      (∀ y : ℕ, N ≤ y → l ≤ y ^ 2 → s.card ≤ y ^ 20) ∧
      ∀ {O : Type} [CommRing O] [PadicIntegerRing O l] {n e : ℕ},
        ∀ z ∈ selmerModule (tateTwist l E O e) (placesDividing E l) ∅ (QuotSpan (l ^ n : O)),
          z g₀ = 0 → (∀ g ∈ s, z g = 0) → z = 0 := by
  classical
  -- Write each point `p` of `exists_detecting_points_cocycles` as `h p * q p`, with `h p` in the
  -- kernel and `q p` in the closure of the powers of `g₀`, and keep the `h p`.
  obtain ⟨s, h_card, h_detect⟩ := exists_detecting_points_cocycles hE l
  choose h hh q hq hp using hg₀.exists_mul_eq
    (isClosed_singleton.preimage (continuous_cyclotomicChar l))
  refine ⟨s.image h, by simpa using fun p _ ↦ hh p,
    fun y hNy hly ↦ Finset.card_image_le.trans (h_card y hNy hly), ?_⟩
  intro O _ _ n e z hz hz₀ h_zero
  obtain ⟨h_coc, -, -, h_lc⟩ := mem_selmerModule_iff.1 hz
  -- The zeros of `z` form a closed subgroup that contains `g₀`, hence the `q p`, and the `h p`.
  let Z : Subgroup Gal(Ω/E) := cocycleKer (tateTwist l E O e) h_coc
  have h_le : (Subgroup.zpowers g₀).topologicalClosure ≤ Z :=
    Subgroup.topologicalClosure_minimal _ (Subgroup.zpowers_le.2 hz₀) (h_lc.isClosed_fiber 0)
  refine h_detect z hz fun p hp_mem ↦ ?_
  rw [← hp p]
  exact Z.mul_mem (h_zero _ (Finset.mem_image_of_mem h hp_mem)) (h_le (hq p))

end DetectingPoints

/-!
## A uniform explicit bound on a model of the odd part of Ш for CM subfields of ℚ(μ_N)

For e = 0 the class number serves. For e > 0 a cocycle is split into components over ℚ by characters
mod N. The odd components are killed by an integer of Stickelberger type, and few points detect the
cocycle.

Conventions: `New.Selmer.shaOdd` is the module of locally constant cocycles that are unramified
outside l, vanish on `New.Selmer.shaLocalSet` above l and, for e ≠ 0, are odd.
`New.cyclotomicPowDirichlet l e ψ` is the character cyc ^ e · ψ of Gal(Ω / ℚ).
`New.OddPart.component` is the module of cocycles for its inverse with the matching local
conditions.
-/

section OddShaBound

open Module IsDiscreteValuationRing New OddPart Selmer Fintype Finset DirichletCharacter NeZero Nat
  MulAut NumberField Pointwise Function

/-- The case `e = 0`. Let `E` be a CM number field, `l` a prime, `O` a ring with
`PadicIntegerRing O l` (the integer ring of a finite extension of `ℚ_l`) and `n : ℕ`. The module
`shaOdd l E O 0 n` consists of the continuous homomorphisms `Gal(Ω/E) → O / lⁿ` that are unramified
at every place. Its length over `O` is at most `addVal O (classNumber E)`, the valuation in `O` of
the class number of `E`. -/
lemma New.length_shaOdd_zero_le_addVal_classNumber (E : Type) [Field E] [NumberField E]
    [IsCMField E]
    [Algebra E Ω] (l : ℕ) [ThePrime l] (O : Type) [CommRing O] [PadicIntegerRing O l] (n : ℕ) :
    length O (shaOdd l E O 0 n) ≤ addVal O (classNumber E) := by
  -- `exists_detecting_points_hom` with `S = ∅` gives points `p i` and integers `m i` whose product
  -- divides the class number, such that every unramified homomorphism `z` has `m i • z (p i) = 0`
  -- and is zero if it vanishes at all `p i`.
  obtain ⟨ι, _, p, m, -, h_dvd, h_detect⟩ :=
    exists_detecting_points_hom Gal(Ω/E) (∅ : Set (FinPlace E)) 0 (by simp [iInf_of_isEmpty])
  have h_pts (z : Gal(Ω/E) → Unit → QuotSpan (l ^ n : O)) (hz : z ∈ shaOdd l E O 0 n) :
      (∀ i, m i • z (p i) = 0) ∧ ((∀ i, z (p i) = 0) → z = 0) := by
    obtain ⟨h_above, -, h_selmer⟩ := mem_shaOdd.mp hz
    obtain ⟨h_cocycle, h_unram, -, h_loc⟩ := mem_selmerModule_iff.mp h_selmer
    refine h_detect
      { isLocallyConstant := h_loc
        map_mul := by simpa [tateTwist] using h_cocycle
        nsmul_eq_zero := fun g ↦ zero_smul ℕ (z g)
        unramified := fun v _ g hg ↦ ?_ }
    -- `z` kills inertia above `l` by the local condition, and elsewhere as it is unramified.
    by_cases hl : v ∈ placesDividing E l
    · exact h_above g ⟨_, v.isPlaceOver_placeOver.valuation_natCast_lt_one_iff.mpr hl, hg⟩
    · exact h_unram g ⟨v, hl, _, v.isPlaceOver_placeOver, hg⟩
  calc length O (shaOdd l E O 0 n) ≤ addVal O (∏ i, m i : ℕ) :=
      length_le_of_detecting_points (LinearEquiv.funUnique Unit O _)
        (fun z hz ↦ (h_pts z hz).left) fun z hz ↦ (h_pts z hz).right
    _ ≤ addVal O (classNumber E) :=
      addVal_le_iff_dvd.mpr (Nat.cast_dvd_cast (by simpa [iInf_of_isEmpty] using h_dvd))

/-- The last step of splitting by characters. Let `x` be odd: `x (conjGal g) = -x g`, where
`conjGal g = c g c` for the complex conjugation `c`. Let finitely many maps `z ψ` satisfy
`∑ ψ, z ψ (ι h) = φ(N) x (conjGal h) - φ(N) x h` for all `h`, `z ψ (ι (conjGal g)) = z ψ (ι g)`, and
`conjGal (conjGal g) = g`. Then `4 φ(N)` kills `x`. -/
private lemma four_mul_totient_smul_eq_zero_of_sum_eq {E : Type} [Field E] [NumberField E]
    [IsCMField E] [Algebra E Ω] {N l n : ℕ} {O : Type} [CommRing O]
    {x : Gal(Ω/E) → Unit → QuotSpan (l ^ n : O)} (hx_odd : ∀ g : Gal(Ω/E), x (conjGal g) = -x g)
    {ι : Gal(Ω/E) → Gal(Ω/ℚ)} {Ψ : Type} [Fintype Ψ] {z : Ψ → Gal(Ω/ℚ) → QuotSpan (l ^ n : O)}
    (h_sum : ∀ h : Gal(Ω/E), ∑ ψ : Ψ, z ψ (ι h) =
      ((φ N : ℕ) : QuotSpan (l ^ n : O)) * x (conjGal h) () -
        ((φ N : ℕ) : QuotSpan (l ^ n : O)) * x h ())
    (h_even : ∀ (ψ : Ψ) (g : Gal(Ω/E)), z ψ (ι (conjGal g)) = z ψ (ι g))
    (h_conj_conj : ∀ g : Gal(Ω/E), conjGal (conjGal g) = g) :
    (4 * φ N) • x = 0 := by
  ext g u
  -- Compare `g` with `c = conjGal g`: `φ(N) (x c - x g) = φ(N) (x g - x c)`, and `x c = -x g`.
  have hx_sum : x g () + x (conjGal g) () = 0 := by rw [hx_odd g, Pi.neg_apply, add_neg_cancel]
  have h_even_sum : ∑ ψ : Ψ, z ψ (ι (conjGal g)) = ∑ ψ : Ψ, z ψ (ι g) :=
    Fintype.sum_congr _ _ fun ψ ↦ h_even ψ g
  rw [h_sum, h_sum, h_conj_conj] at h_even_sum
  change (4 * φ N) • x g () = 0
  simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  linear_combination h_even_sum + 2 * ((φ N : ℕ) : QuotSpan (l ^ n : O)) * hx_sum

/-- Let `x` on `Gal(Ω/E)` vanish on the inertia groups at places of `E` prime to `l` and on
`shaLocalSet l E e`, where `e ≠ 0`. Let `g` lie in an inertia group at a place prime to `l`, or in
`shaLocalSet l ℚ 1` (a decomposition group above `l`, with trivial cyclotomic character). Then `x`
vanishes at each `w` whose image in `Gal(Ω/ℚ)` is the conjugate `u g u⁻¹`. -/
private lemma apply_eq_zero_of_toAlgAut_eq_conj {E : Type} [Field E] [NumberField E] [IsCMField E]
    [Algebra E Ω] {l e : ℕ} [ThePrime l] (he : e ≠ 0) {V : Type} [Zero V] {x : Gal(Ω/E) → V}
    (h_above : ∀ g ∈ shaLocalSet l E e, x g = 0)
    (h_unram : ∀ g ∈ inertiaAbove (placesDividing E l)ᶜ, x g = 0) {g : Gal(Ω/ℚ)}
    (h_local : g ∈ inertiaAbove (placesDividing ℚ l)ᶜ ∪ shaLocalSet l ℚ 1) (u : Gal(Ω/ℚ))
    {w : Gal(Ω/E)} (hw : MulSemiringAction.toAlgAut Gal(Ω/E) ℚ Ω w = conj u g) :
    x w = 0 := by
  obtain ⟨v₀, hv₀, A, hA, h_ine⟩ | ⟨A, h_val, h_dec, h_one⟩ := h_local
  -- Inertia away from `l`: `x` is unramified at the place `v` of `E` under `u • A`.
  · obtain ⟨v, hv, h_under⟩ : ∃ v : FinPlace E, IsPlaceOver (u • A) v ∧ v.below ℚ = v₀ :=
      (hA.smul u).exists_above
    have hv_compl : v ∈ (placesDividing E l)ᶜ := by simpa [← h_under, placesDividing] using hv₀
    -- The image `conj u g` of `w` lies in the inertia group at `u • A`.
    have h_mem : MulSemiringAction.toAlgAut Gal(Ω/E) ℚ Ω w ∈ inertiaGroup Gal(Ω/ℚ) (u • A) := by
      rw [hw]
      exact h_ine.conj u
    exact h_unram _ ⟨v, hv_compl, _, hv, h_mem⟩
  -- Decomposition group above `l` with trivial cyclotomic character: `w` lies in `shaLocalSet`.
  · have h_cyc_one : cyclotomicChar Ω l w = 1 := by
      change cyclotomicChar Ω l (MulSemiringAction.toAlgAut Gal(Ω/E) ℚ Ω w) = 1
      simp [hw, h_one]
    have h_val_lt : (u • A).valuation l < 1 := by
      simpa using (smul_apply_smul_lt_one_iff u).mpr h_val
    have h_mem : MulSemiringAction.toAlgAut Gal(Ω/E) ℚ Ω w ∈ decompGroup Gal(Ω/ℚ) (u • A) := by
      rw [hw]
      exact conj_mem_decompGroup_smul h_dec
    refine h_above w ⟨u • A, h_val_lt, ?_⟩
    rw [ite_eq_right he]
    exact ⟨h_mem, h_cyc_one⟩

attribute [local simp] mul_assoc tateTwist in
/-- Splitting by characters. Let `E ⊆ ℚ(μ_N)` be a CM field, `l` a prime, `e ≠ 0`, and `O` with
enough roots of unity for the characters mod `N`. `shaOdd l E O e n` is the module of odd locally
constant cocycles `Gal(Ω/E) → O/lⁿ(-e)` that are unramified outside `l` and vanish on
`shaLocalSet l E e`. `component l e ψ n` consists of cocycles on `Gal(Ω/ℚ)` for `(cyc^e ψ)⁻¹` with
local conditions: locally constant, and vanishing at `cmConj` and at elements fixing `μ_N` that lie
in inertia off `l` or in `shaLocalSet l ℚ 1`. There are `σ : (ZMod N)ˣ → Gal(Ω/ℚ)` and
`b : Gal(Ω/ℚ) → Gal(Ω/ℚ) → Gal(Ω/E)`, independent of the cocycle, with the following property. For
`x ∈ shaOdd l E O e n`, each `z ψ g = ∑ t, (cyc^e ψ)(σ t) • x (b (σ t) g)` lies in
`component l e ψ n`, and `4 * φ N` kills `x` once the odd `z ψ`
(`cyclotomicPowDirichlet l e ψ cmConj = -1`) vanish. -/
lemma New.exists_character_components {N : ℕ} [NeZero N] {E : Type} [Field E] [NumberField E]
    [IsCMField E] [Algebra E Ω] (h_sub : ∀ x : E, algebraMap E Ω x ∈ cycloField N)
    (l : ℕ) [ThePrime l] (O : Type) [CommRing O] [PadicIntegerRing O l]
    [HasEnoughRootsOfUnity O (Monoid.exponent (ZMod N)ˣ)] {e : ℕ} (he : e ≠ 0) (n : ℕ) :
    ∃ (σ : (ZMod N)ˣ → Gal(Ω/ℚ)) (b : Gal(Ω/ℚ) → Gal(Ω/ℚ) → Gal(Ω/E)),
      ∀ x ∈ shaOdd l E O e n,
        let z (ψ : DirichletCharacter O N) : Gal(Ω/ℚ) → QuotSpan (l ^ n : O) :=
          ∑ t : (ZMod N)ˣ, fun g : Gal(Ω/ℚ) ↦
            (cyclotomicPowDirichlet l e ψ (σ t)).val • x (b (σ t) g) ()
        (∀ ψ : DirichletCharacter O N, z ψ ∈ component l e ψ n) ∧
        ((∀ ψ : DirichletCharacter O N, cyclotomicPowDirichlet l e ψ cmConj = -1 → z ψ = 0) →
          (4 * φ N) • x = 0) := by
  let ι : Gal(Ω/E) →* Gal(Ω/ℚ) := MulSemiringAction.toAlgAut Gal(Ω/E) ℚ Ω
  have hι : Topology.IsClosedEmbedding ι :=
    (isClosedEmbedding_galois_restrict (K := ℚ) (L := E) ι fun _ _ ↦ rfl).1
  have h_lift : ∀ g ∈ cycloGalGroup N, ∃ w : Gal(Ω/E), ι w = g :=
    fun g hg ↦ ⟨⟨g, g.map_mul', g.map_add', fun x ↦ h_sub x ⟨g, hg⟩⟩, rfl⟩
  have h_conj (g : Gal(Ω/E)) : ι (conjGal g) = cmConj * ι g * cmConj := rfl
  have h_cyc : cyclotomicChar Ω l = (cyclotomicChar Ω l).comp ι := rfl
  -- Lifts `σ t` of `t` with `σ 1 = 1`, and lifts `b u g` to `Gal(Ω/E)` of the commutator
  -- `cmConj * g * cmConj⁻¹ * g⁻¹` conjugated by `u`.
  have h_surj : ∀ t : (ZMod N)ˣ, ∃ g : Gal(Ω/ℚ), cyclotomicCharMod Ω N g = t :=
    cyclotomicCharMod_surjective N
  choose S hS using h_surj
  let σ (t : (ZMod N)ˣ) : Gal(Ω/ℚ) := S t / S 1
  have h_lift_comm (u g : Gal(Ω/ℚ)) : ∃ w : Gal(Ω/E), ι w = conj u (conj cmConj g * g⁻¹) := by
    have h_mem : conj u (conj cmConj g * g⁻¹) ∈ cycloGalGroup N := by
      simp [mul_left_comm, mul_assoc]
    exact h_lift _ h_mem
  choose b hb using h_lift_comm
  refine ⟨σ, b, fun x hx ↦ ?_⟩
  obtain ⟨h_above, h_minus, h_selmer⟩ := mem_shaOdd.mp hx
  obtain ⟨h_cocycle, h_unram, -, h_loc⟩ := mem_selmerModule_iff.mp h_selmer
  -- The cyclotomic character is trivial at `b u g`, so the cocycle `x` is additive there: if
  -- `b u g * k = w` (checked in `Gal(Ω/ℚ)`, by default by `simp`), then `x (b u g) = x w - x k`.
  have h_add (u g : Gal(Ω/ℚ)) (k w : Gal(Ω/E)) (hw : ι (b u g * k) = ι w := by simp [*]) :
      x (b u g) = x w - x k := by
    simp [h_cocycle, h_cyc, hb, ← hι.injective hw, tateTwist, cyclotomicInv]
  let T (ψ : DirichletCharacter O N) (u g : Gal(Ω/ℚ)) : QuotSpan ((l : O) ^ n) :=
    (cyclotomicPowDirichlet l e ψ u).val • x (b u g) ()
  let z (ψ : DirichletCharacter O N) : Gal(Ω/ℚ) → QuotSpan (l ^ n : O) := ∑ t, T ψ (σ t)
  have hz (ψ : DirichletCharacter O N) : z ψ ∈ component l e ψ n := by
    refine ⟨sum_mem fun _ _ ↦ .comp (h_loc.comp_continuous ?_) fun y ↦ _ • y (),
      fun g k ↦ ?_, ?_⟩
    · simp only [hι.continuous_iff, comp_def, hb, conj_apply, mul_assoc]
      fun_prop
    -- The cocycle rule: `T ψ u k` depends only on the coset of `u` modulo `cycloGalGroup N`, and
    -- right multiplication by `g` permutes the cosets.
    · have h_coset {v : Gal(Ω/ℚ)} (w : Gal(Ω/ℚ))
          (hw : w / v ∈ cycloGalGroup N) : T ψ w k = T ψ v k := by
        obtain ⟨u, rfl⟩ : ∃ a : Gal(Ω/E), ι a * v = w := (h_lift _ hw).imp fun _ ↦ mul_eq_of_eq_div
        -- With `T` unfolded; `h_add` relates `x (b (ι u * v) k)` to `x (b v k)`.
        show (cyclotomicPowDirichlet l e ψ (ι u * v)).val • x (b (ι u * v) k) () =
          (cyclotomicPowDirichlet l e ψ v).val • x (b v k) ()
        simp_all [cyclotomicPowDirichlet, h_add v k u⁻¹ (u⁻¹ * b (ι u * v) k), mul_assoc, tateTwist,
          cyclotomicInv, smul_smul, mul_pow, mul_comm, mul_left_comm]
      -- Right multiplication by `g` permutes the cosets of the `σ t`.
      have h_shift : ∑ t, T ψ (σ t * g) k = ∑ t, T ψ (σ t) k := by
        refine sum_equiv (.mulRight (cyclotomicCharMod Ω N g)) _ _ fun t ↦ h_coset (σ t * g) ?_
        simp [σ, hS]
      simp [z, T, mul_left_comm, ← h_shift, fun u ↦ h_add u g (b (u * g) k) (b u (g * k)),
        smul_sub, smul_sum, smul_smul]
    rintro g (rfl | ⟨hg, h_local⟩)
    -- For `g = cmConj` the commutator is trivial.
    · simp [z, T, h_add _ cmConj 1 1]
    -- Otherwise `x` vanishes at the lift `w u` of every conjugate of `g`.
    have h_lift_conj (u : Gal(Ω/ℚ)) : ∃ w : Gal(Ω/E), ι w = conj u g := h_lift _ (by simpa)
    choose w hw using h_lift_conj
    have h_zero (u : Gal(Ω/ℚ)) : x (w u) = 0 :=
      apply_eq_zero_of_toAlgAut_eq_conj he h_above h_unram h_local u (hw u)
    -- `b u g * w u = w (u * cmConj)`, so `x (b u g) = 0` for all `u`.
    simp [z, T, h_zero, fun t ↦ h_add t g (w t) (w (t * cmConj))]
  refine ⟨hz, fun h_odd : ∀ ψ, cyclotomicPowDirichlet l e ψ cmConj = -1 → z ψ = 0 ↦ ?_⟩
  have hc_inv : cmConj⁻¹ = cmConj := inv_eq_of_mul_eq_one_left isComplexConj_cmConj.mul_self
  -- The odd components vanish and the even ones are invariant under conjugation by `cmConj`.
  have h_even (ψ : DirichletCharacter O N) (g : Gal(Ω/E)) : z ψ (ι (conjGal g)) = z ψ (ι g) := by
    obtain ⟨-, h_mul, h_vanish⟩ := hz ψ
    -- `cmConj` is an involution, so the value of the character there is a sign.
    have h_sign : cyclotomicPowDirichlet l e ψ cmConj = 1 ∨
        cyclotomicPowDirichlet l e ψ cmConj = -1 :=
      (Units.inv_eq_self_iff _).mp (by grind)
    rcases h_sign with h_even_sign | h_odd_sign
    · simp [h_conj, h_mul, h_vanish, h_even_sign]
    · simp [h_odd ψ h_odd_sign]
  -- By orthogonality of characters only `t = 1` survives in `∑ ψ, z ψ (ι h)`.
  have h_sum (h : Gal(Ω/E)) : ∑ ψ : DirichletCharacter O N, z ψ (ι h) =
      ((φ N : ℕ) : QuotSpan (l ^ n : O)) * x (conjGal h) () -
        ((φ N : ℕ) : QuotSpan (l ^ n : O)) * x h () := by
    simp [sum_characters_eq, cast_smul_eq_nsmul, z, T, σ, hS, cyclotomicPowDirichlet, ← sum_smul,
      ← mul_sum, sum_comm, fun g ↦ h_add 1 (ι g) g (conjGal g), smul_sub]
  have h_conj_conj (g : Gal(Ω/E)) : conjGal (conjGal g) = g := hι.injective (by simp)
  exact four_mul_totient_smul_eq_zero_of_sum_eq (h_minus he) h_sum h_even h_conj_conj

/-- The size of the integer in `New.exists_length_shaOdd_le`. Let `y = N + t + 3` and let
`X e ≤ 2 ^ (N + e + 3) ^ 6` for `e ≠ 0`. Then the product over `0 < e < t` of `4 φ(N) · 4 (X e)²`,
raised to the power `y ^ 20`, is at most `2 ^ (4 y ^ 27)`: each factor is at most `2 ^ (4 y ^ 6)`,
and there are at most `y` factors. -/
private lemma prod_Ioo_pow_le_two_pow_of_le_two_pow {N t y : ℕ} {X : ℕ → ℕ} (hy : N + t + 3 = y)
    (hX_le : ∀ e : ℕ, e ≠ 0 → X e ≤ 2 ^ (N + e + 3) ^ 6) :
    (∏ e ∈ Ioo 0 t, 4 * φ N * (4 * X e * X e)) ^ y ^ 20 ≤ 2 ^ (4 * y ^ 27) := by
  have hY (e : ℕ) (he : e ∈ Ioo 0 t) : 4 * φ N * (4 * X e * X e) ≤ 2 ^ (4 * y ^ 6) := by
    obtain ⟨he_pos, he_lt⟩ : 0 < e ∧ e < t := mem_Ioo.mp he
    have hXe : X e ≤ 2 ^ y ^ 6 := (hX_le e he_pos.ne').trans
      (Nat.pow_le_pow_right two_pos (Nat.pow_le_pow_left (by lia) 6))
    have h16 : 4 * φ N * 4 ≤ 2 ^ (2 * y ^ 6) := by grind [Nat.lt_two_pow_self, Nat.totient_le]
    calc 4 * φ N * (4 * X e * X e) = 4 * φ N * 4 * X e * X e := by ring
      _ ≤ 2 ^ (2 * y ^ 6) * 2 ^ y ^ 6 * 2 ^ y ^ 6 := by gcongr
      _ = 2 ^ (4 * y ^ 6) := by ring
  calc
    (∏ e ∈ Ioo 0 t, 4 * φ N * (4 * X e * X e)) ^ y ^ 20 ≤ ((2 ^ (4 * y ^ 6)) ^ y) ^ y ^ 20 := by
      grw [prod_le_pow_card (Ioo 0 t) _ (2 ^ (4 * y ^ 6)) hY,
        pow_le_pow_right₀ Nat.one_le_two_pow ((Nat.card_Ioo 0 t).trans_le (by lia : t - 0 - 1 ≤ y))]
    _ = 2 ^ (4 * y ^ 27) := by ring

/-- A Stickelberger bound kills `shaOdd`. Let `E ⊆ ℚ(μ_N)` be a CM field, `l` a prime, `O` with
`PadicIntegerRing O l` having enough roots of unity for the characters mod `N`, and `e ≠ 0`. Let `X`
satisfy `IsStickelbergerBound N e X`, a divisibility for each prime together with a congruence for
the Stickelberger sums. Then `4 φ(N) · 4 X²` kills every `z ∈ shaOdd l E O e n`, that is, every
continuous cocycle `Gal(Ω/E) → O / lⁿ(-e)` unramified outside `l`, vanishing on `shaLocalSet l E e`
and odd under `conjGal`: `4 X²` kills the odd character components of a cocycle, and `4 φ(N)` kills
a cocycle whose odd components vanish. -/
lemma New.OddPart.nsmul_shaOdd_eq_zero_of_isStickelbergerBound {N : ℕ} [NeZero N] {E : Type}
    [Field E] [NumberField E] [IsCMField E] [Algebra E Ω]
    (h_sub : ∀ x : E, algebraMap E Ω x ∈ cycloField N) (l : ℕ) [ThePrime l] (O : Type)
    [CommRing O] [PadicIntegerRing O l] [HasEnoughRootsOfUnity O (Monoid.exponent (ZMod N)ˣ)]
    {e : ℕ} (he : e ≠ 0) (n : ℕ) {X : ℕ} (h_stick : IsStickelbergerBound N e X) :
    ∀ z ∈ shaOdd l E O e n, (4 * φ N * (4 * X * X)) • z = 0 := by
  obtain ⟨σ, b, h_split⟩ := exists_character_components h_sub l O he n
  intro z hz
  obtain ⟨hz_comp, -⟩ := h_split z hz
  -- `(4 φ(N) · 4 X²) • z = 4 φ(N) • (4 X² • z)`, and the odd components of `4 X² • z` vanish.
  obtain ⟨-, h_kill_of_odd⟩ := h_split _ (nsmul_mem hz (4 * X * X))
  refine (mul_smul (4 * φ N) (4 * X * X) z).trans (h_kill_of_odd fun ψ hψ ↦ ?_)
  -- The component of `4 X² • z` is `4 X²` times the component of `z`, killed by Stickelberger.
  simpa [funext_iff, smul_sum] using nsmul_component_eq_zero h_stick hψ he (hz_comp ψ)

/-- An annihilator and detecting points bound the length. Let `E` be a CM field and `l` a prime. If
a natural number `m` kills `New.Selmer.shaOdd` with values in `O / lⁿ(-e)`, and only `0` vanishes
at all of the at most `k` points `p i`, then the length is at most the valuation of `m ^ k`:
evaluation at the points embeds the module in copies of the `m`-torsion of `O / lⁿ`. -/
lemma New.OddPart.length_shaOdd_le_addVal_pow {E : Type} [Field E] [NumberField E] [IsCMField E]
    [Algebra E Ω] {l : ℕ} [ThePrime l] {O : Type} [CommRing O] [PadicIntegerRing O l]
    {e n m k : ℕ} (h_kill : ∀ z ∈ shaOdd l E O e n, m • z = 0) {ι : Type} [Fintype ι]
    (p : ι → Gal(Ω/E)) (h_card : Fintype.card ι ≤ k)
    (h_detect : ∀ z ∈ shaOdd l E O e n, (∀ i : ι, z (p i) = 0) → z = 0) :
    length O (shaOdd l E O e n) ≤ addVal O (m ^ k : ℕ) := by
  calc
    length O (shaOdd l E O e n) ≤ addVal O (∏ _i : ι, m : ℕ) :=
      length_le_of_detecting_points (LinearEquiv.funUnique Unit O (QuotSpan (l ^ n : O)))
        (fun z hz i ↦ congrFun (h_kill z hz) (p i)) h_detect
    _ ≤ addVal O (m ^ k : ℕ) :=
      addVal_le_iff_dvd.mpr (cast_dvd_cast (by simpa using pow_dvd_pow m h_card))

/-- Small primes. Let `E ⊆ ℚ(μ_N)` be a CM field, `N ≤ y`, and `l` a prime with `l ≤ y ^ 2`. If a
natural number `m` kills `New.Selmer.shaOdd` with values in `O / lⁿ(-e)`, then its length is at
most the valuation of `m ^ y ^ 20`, as `y ^ 20` or fewer points detect the cocycles that are
unramified outside `l`. -/
lemma New.OddPart.length_shaOdd_le_of_le_sq {N : ℕ} [NeZero N] {E : Type} [Field E]
    [NumberField E] [IsCMField E] [Algebra E Ω] (h_sub : ∀ x : E, algebraMap E Ω x ∈ cycloField N)
    (l : ℕ) [ThePrime l] (O : Type) [CommRing O] [PadicIntegerRing O l] (e n : ℕ) {y : ℕ}
    (hN_le : N ≤ y) (hl_le : l ≤ y ^ 2) {m : ℕ}
    (h_kill : ∀ z ∈ shaOdd l E O e n, m • z = 0) :
    length O (shaOdd l E O e n) ≤ addVal O (m ^ y ^ 20 : ℕ) := by
  obtain ⟨s, h_card, h_detect⟩ := exists_detecting_points_cocycles h_sub l
  have h_card_le : Fintype.card s ≤ y ^ 20 := by simpa using h_card y hN_le hl_le
  refine length_shaOdd_le_addVal_pow h_kill (fun g : s ↦ (g : Gal(Ω/E))) h_card_le
    fun z hz h_van ↦ ?_
  obtain ⟨-, -, h_selmer⟩ := mem_shaOdd.mp hz
  exact h_detect z h_selmer fun g hg ↦ h_van ⟨g, hg⟩

/-- Let `E ⊆ ℚ(μ_N)` be a CM field, `e ≠ 0`, `N + e + 3 ≤ y`, and `l` a prime with `y ^ 2 < l`; let
`O`, the integers of a finite extension of `ℚ_l`, have enough roots of unity for the characters mod
`N`. If `0 < X ≤ 2 ^ y ^ 6` satisfies `New.OddPart.IsStickelbergerBound N e X` (a divisibility at
each prime and a congruence for Stickelberger sums), then the length of `New.Selmer.shaOdd` (odd
continuous cocycles `Gal(Ω/E) → O / lⁿ(-e)` unramified outside `l`, vanishing on
`shaLocalSet l E e`) is at most the valuation of `(4 φ(N) · 4 X²) ^ y ^ 20`.

An upper bound of this kind is usually drawn from the main conjecture of Mazur and Wiles. Here it
comes from the points that Kolyvagin's derivative cocycles give for each odd character. -/
lemma New.OddPart.length_shaOdd_le_of_sq_lt {N : ℕ} [NeZero N] {E : Type} [Field E]
    [NumberField E] [IsCMField E] [Algebra E Ω] (h_sub : ∀ x : E, algebraMap E Ω x ∈ cycloField N)
    (l : ℕ) [hl_prime : ThePrime l] (O : Type) [CommRing O] [PadicIntegerRing O l]
    [HasEnoughRootsOfUnity O (Monoid.exponent (ZMod N)ˣ)] {e : ℕ} (he : e ≠ 0) (n : ℕ) {y : ℕ}
    (h_le_y : N + e + 3 ≤ y) (hl_gt : y ^ 2 < l) {X : ℕ} (hX_ne : X ≠ 0) (hX_le : X ≤ 2 ^ y ^ 6)
    (h_stick : IsStickelbergerBound N e X) :
    length O (shaOdd l E O e n) ≤ addVal O ((4 * φ N * (4 * X * X)) ^ y ^ 20 : ℕ) := by
  -- For each odd `ψ`, points `γ ψ i` with `i ≤ v_l(X)` detect the cocycles in
  -- `component l e ψ n`. The values of `z` at the points `b (σ u) (γ ψ i)` then detect `z`.
  have h_tot : φ N ≤ N := N.totient_le
  have hl_big : N + e + 3 < l := by nlinarith
  obtain ⟨σ, b, h_split⟩ := exists_character_components h_sub l O he n
  have h_detect_pts : ∀ ψ : DirichletCharacter O N, cyclotomicPowDirichlet l e ψ cmConj = -1 →
      ∃ γ : Fin (X.factorization l + 1) → Gal(Ω/ℚ),
        ∀ x ∈ component l e ψ n, (∀ i : Fin (X.factorization l + 1), x (γ i) = 0) → x = 0 :=
    fun ψ hψ ↦ exists_detecting_points_component h_stick hψ he hX_ne hl_big
  choose! γ hγ using h_detect_pts
  refine length_shaOdd_le_addVal_pow
    (nsmul_shaOdd_eq_zero_of_isStickelbergerBound h_sub l O he n h_stick)
    (fun (u, ψ, i) ↦ b (σ u) (γ ψ i)) ?_ fun z hz h_van ↦ ?_
  · -- At most `y` values of `u`, `y` characters and `y ^ 6 + 1 ≤ y ^ 18` values of `i`.
    have h_val : X.factorization l ≤ y ^ 6 :=
      factorization_le_of_le_pow (hX_le.trans (Nat.pow_le_pow_left hl_prime.out.two_le _))
    have h_pow : y ^ 6 < y ^ 18 := Nat.pow_lt_pow_right (by lia) (by norm_num)
    have h_tot_le : φ N ≤ y := by lia
    simp only [Fintype.card_prod, ZMod.card_units_eq_totient, Fintype.card_fin]
    grw [card_eq_nat_card, card_eq_totient_of_hasEnoughRootsOfUnity, h_tot_le, h_val,
      add_one_le_of_lt h_pow]
    nlinarith
  · -- The odd components of `z` vanish, so `z` is killed by `4 * φ N`, which is prime to `l`.
    obtain ⟨hz_comp, h_kill_of_odd⟩ := h_split z hz
    have h_van' (u : (ZMod N)ˣ) (ψ : DirichletCharacter O N) (i : Fin (X.factorization l + 1)) :
        z (b (σ u) (γ ψ i)) = 0 := h_van (u, ψ, i)
    have h_four : (4 * φ N) • z = 0 :=
      h_kill_of_odd fun ψ hψ ↦ hγ ψ hψ _ (hz_comp ψ) fun i ↦ by simp [h_van']
    have h_pow : l ^ n • z = 0 := funext₂ fun g i ↦ nsmul_quot_eq_zero dvd_rfl (z g i)
    have h_lt : 4 * φ N < l := by nlinarith
    have h_coprime : (l ^ n).Coprime (4 * φ N) :=
      .pow_left n (coprime_of_lt_prime out h_lt hl_prime.out)
    exact (nsmul_eq_zero_iff_of_coprime h_coprime).mp ⟨h_pow, h_four⟩

/-- For a CM field `E` inside `ℚ(μ_N)` (`h_sub`) and `t : ℕ` there is an integer `X ≠ 0`, at most
`2 ^ (4 (N + t + 3) ^ 27) · h_E` (`h_E` the class number), such that the following holds for each
prime `l`, each `O` with `PadicIntegerRing O l` (a discrete valuation ring finite and free over
`ℤ_l`, with valuation `addVal O`) and enough roots of unity for the characters mod `N`, and each
`e < t` and `n`. The length over `O` of `shaOdd l E O e n` is at most `addVal O X`. For `e ≠ 0` this
is the module of continuous cocycles `Gal(Ω/E) → O / lⁿ(-e)`, not taken modulo coboundaries, that
are unramified off `l`, vanish on `shaLocalSet l E e` and are odd; for `e = 0` it is the everywhere
unramified continuous homomorphisms.

For large `l` a bound of this kind follows from the Iwasawa main conjecture of Mazur and Wiles; only
an upper bound for the length at finite level, by an integer of explicit size, is proved. -/
lemma New.exists_length_shaOdd_le (N t : ℕ) [NeZero N] (E : Type) [Field E] [NumberField E]
    [IsCMField E] [Algebra E Ω] (h_sub : ∀ x : E, algebraMap E Ω x ∈ cycloField N) :
    ∃ X : ℕ, X ≠ 0 ∧
      X ≤ 2 ^ (4 * (N + t + 3) ^ 27) * classNumber E ∧
      ∀ (l : ℕ) [ThePrime l] (O : Type) [CommRing O] [PadicIntegerRing O l],
        HasEnoughRootsOfUnity O (Monoid.exponent (ZMod N)ˣ) →
        ∀ e : ℕ, e < t → ∀ n : ℕ, length O (shaOdd l E O e n) ≤ addVal O X := by
  -- Put `y = N + t + 3`. For `e ≠ 0` a nonzero Stickelberger bound `X e ≤ 2 ^ (N + e + 3) ^ 6`
  -- gives an integer `Y e` that kills the module, and for small and for large `l` the length is
  -- at most the valuation of `Y e ^ y ^ 20`. For `e = 0` the class number serves.
  have h_bound : ∀ e : ℕ, e ≠ 0 →
      ∃ X ≠ (0 : ℕ), X ≤ 2 ^ (N + e + 3) ^ 6 ∧ IsStickelbergerBound N e X :=
    fun e he ↦ exists_isStickelbergerBound N e he
  choose! X hX_ne hX_le h_stick using h_bound
  generalize hy : N + t + 3 = y
  let Y (e : ℕ) : ℕ := 4 * φ N * (4 * X e * X e)
  have hY_ne : (Ioo 0 t).prod Y ≠ 0 := prod_ne_zero_iff.mpr fun e he ↦ by
    simp [NeZero.ne N, hX_ne e (mem_Ioo.mp he).left.ne']
  refine ⟨(Ioo 0 t).prod Y ^ y ^ 20 * classNumber E, by simp [hY_ne, classNumber_ne_zero],
    Nat.mul_le_mul_right (classNumber E) (prod_Ioo_pow_le_two_pow_of_le_two_pow hy hX_le), ?_⟩
  intro l _ O _ _ hO e het n
  obtain rfl | he := eq_or_ne e 0
  · exact (length_shaOdd_zero_le_addVal_classNumber E l O n).trans (addVal_le_iff_dvd.mpr (by simp))
  have h_mem : e ∈ Ioo 0 t := mem_Ioo.mpr ⟨Nat.pos_of_ne_zero he, het⟩
  have h_dvd : Y e ^ y ^ 20 ∣ (Ioo 0 t).prod Y ^ y ^ 20 * classNumber E :=
    (pow_dvd_pow_of_dvd (dvd_prod_of_mem Y h_mem) (y ^ 20)).mul_right (classNumber E)
  suffices h_length : length O (shaOdd l E O e n) ≤ addVal O (Y e ^ y ^ 20 : ℕ) from
    h_length.trans (addVal_le_iff_dvd.mpr (cast_dvd_cast h_dvd))
  have h_le_y : N + e + 3 ≤ y := by lia
  obtain hl_le | hl_gt := le_or_gt l (y ^ 2)
  · exact length_shaOdd_le_of_le_sq h_sub l O e n (by lia) hl_le
      (nsmul_shaOdd_eq_zero_of_isStickelbergerBound h_sub l O he n (h_stick e he))
  · have hXe_le : X e ≤ 2 ^ y ^ 6 :=
      (hX_le e he).trans (Nat.pow_le_pow_right two_pos (Nat.pow_le_pow_left h_le_y 6))
    exact length_shaOdd_le_of_sq_lt h_sub l O he n h_le_y hl_gt (hX_ne e he) hXe_le (h_stick e he)

end OddShaBound
