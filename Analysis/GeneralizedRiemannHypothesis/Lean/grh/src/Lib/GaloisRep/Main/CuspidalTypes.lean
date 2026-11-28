import Lib.GaloisRep.Pseudocharacter.Pseudorepresentations
import Lib.PadicHodge.Characters
import Lib.PadicHodge.Limit.TraceLimit
import Lib.Shimura.HeckeTower.HeckeData

/-!
# Cuspidal types, multiplicity-free sums and the Hodge–Tate cocharacter

The file proves four results on unitary groups and Galois representations. Here `O_w` is the ring of
integers at a place `w` of `E` with uniformiser `ϖ`, and `χ` is the cyclotomic character.

## Main definitions and results

* `New.Variety.exists_isCuspidalType`: a character of `1 + ϖ M_N(O_w)`, trivial on
  `1 + ϖ² M_N(O_w)`, that is nontrivial on every unipotent radical. It is
  `k ↦ exp (2πi u (tr (b (k - 1))))` for an integral matrix `b` with irreducible characteristic
  polynomial modulo `w` and an additive character `u : E_w / ϖ² → ℚ/ℤ` with `u ϖ ≠ 0`.
* `New.Variety.exists_levelGU_invTransposeGL_le`: an open subgroup that contains the integral points
  trivial at a finite set `S` of places contains a principal level `𝔑` (up to inverse transpose).
  The primes of `𝔑` are those of a given `N` and of a set `B` meeting each pair `w, w̄` of `S`.
* `New.GaloisRep.exists_rep_span_diagonal`: Galois representations `ρ τ`, one for each embedding `τ`
  of `E` in `ℂ`, combine into one representation `r`. This `r` is multiplicity free (the span of its
  image contains the diagonal matrices) and has the prescribed integers among its Hodge–Tate jumps
  at every `τ`. It is built from the semisimplification of the sum of the `ρ τ`, keeping each
  irreducible constituent once.
* `New.Period.aeval_cocharacter_eq_zero`: let `x i ∈ ℂ_p` and integers `κ i` be given. A polynomial
  over `ℂ_p` that vanishes at `(χ(g) ^ (-κ i) g(x i))_i` for all `g ∈ G_p` near `1` also vanishes at
  `(T ^ (κ i) x i)_i`, with `T` the variable of the Laurent polynomials over `ℂ_p`.

Notions from other files:
* `New.localCongruence n w m`: the subgroup of `GL_n(E_w)` of integral matrices congruent to `1`
  modulo `ϖ ^ (m + 1)`; so `m = 0` gives `1 + ϖ M_n(O_w)` and `m = 1` gives `1 + ϖ² M_n(O_w)`.
* `New.stdLevel E n`: the integral points of the finite adelic unitary group, the stabiliser of
  `Ô ^ n`.
* `New.Variety.IsCuspidalType`: for every idempotent matrix ε ≠ 0, 1, the character is nontrivial on
  the elements of its group that lie in 1 + εM_n(1 − ε).
* `New.Variety.levelGU`: the principal level K(𝔑), the similitudes in `GL_n(Ô E)` that are congruent
  to `1` modulo `𝔑`.
* `New.Gf`: The finite adelic unitary group G_f: matrices g in GL_n(𝔸_f) with gᴴg = 1;
  `New.Gf.trivialOn n S` is the subgroup of elements with component 1 at every place of `S`.
* `New.Period.hodgeTateMaps`: The γ-semilinear maps f : T → ℂ_ℓ with f(gx) = χ(g)^(−u)·g f(x) for g
  near 1; their dimension is the multiplicity `New.Period.jump` of the jump u at γ.

## Relation to the literature

Known result: The Hodge-Tate cocharacter lies in the algebraic monodromy group. It is stated on
coordinates in C_p as the fact that a polynomial that vanishes at the cyclotomically twisted Galois
translates of a point, near the identity, vanishes along the one-parameter torus. No algebraic
groups or Tannakian categories are used. Source: Serre, Groupes algébriques associés aux modules de
Hodge-Tate, Astérisque 65 (1979), §1; Sen, Ann. of Math. 97 (1973).

See also `Lib.GaloisRep.WeightCongruence`, `Lib.Adelic.Unitary.CongruenceLevels` and
`Lib.GaloisRep.Main.OddRank`.
-/

/-! ## Existence of a cuspidal type and of a principal level -/

namespace New.Variety

open Matrix IsLocalRing Valued Gf FiniteField IsDedekindDomain.HeightOneSpectrum QuotientAddGroup QZ
  Polynomial Ideal Fintype IsPrime NumberField

variable {E n : Type} [Field E] [NumberField E] [Fintype n] [DecidableEq n] (w : FinPlace E)

/-- Some `N × N` matrix over `LocInt w` (the integers `O_w` of the completion `LocField w = E_w`)
has irreducible characteristic polynomial modulo `w`: lift the matrix of multiplication by a
generator of the extension of degree `N` of the residue field. -/
lemma exists_irreducible_charpoly_residue (N : ℕ) [NeZero N] :
    ∃ b : Matrix (Fin N) (Fin N) (LocInt w), Irreducible (b.map (residue (LocInt w))).charpoly := by
  have h_char_prime : Fact (ringChar (ResField w)).Prime := ⟨CharP.prime_ringChar (ResField w)⟩
  let basis : PowerBasis (ResField w) (Extension (ResField w) (ringChar (ResField w)) N) :=
    Field.powerBasisOfFiniteOfSeparable (ResField w)
      (Extension (ResField w) (ringChar (ResField w)) N)
  rw [← show basis.dim = N from basis.finrank.symm.trans (finrank_extension ..)]
  -- Lift the matrix of multiplication by the generator entry by entry.
  obtain ⟨b, hb⟩ : ∃ b : Matrix (Fin basis.dim) (Fin basis.dim) (LocInt w),
      b.map (residue (LocInt w)) = Algebra.leftMulMatrix basis.basis basis.gen :=
    residue_surjective.comp_left.comp_left _
  refine ⟨b, ?_⟩
  rw [hb, charpoly_leftMulMatrix basis]
  exact minpoly.irreducible basis.isIntegral_gen

/-- A matrix with irreducible characteristic polynomial is not block triangular: if `p` holds for
some indices but not for all, some entry in a row with `p` and a column without `p` is nonzero. -/
lemma exists_ne_zero_of_irreducible_charpoly {F : Type*} [Field F] {A : Matrix n n F}
    (hA : Irreducible A.charpoly) {p : n → Prop} (h₁ : ∃ j : n, p j) (h₂ : ∃ i : n, ¬p i) :
    ∃ j i : n, p j ∧ ¬p i ∧ A j i ≠ 0 := by
  classical
  let := Prop.linearOrder
  by_contra! h_zero
  have h_block : A.BlockTriangular p := by
    -- On `Prop`, `p i' < p j'` says that `p j'` holds and `p i'` does not.
    intro j' i' (h_lt : p i' < p j')
    obtain ⟨hj', hi'⟩ : p j' ∧ ¬p i' := Classical.not_imp.mp h_lt.not_ge
    exact h_zero j' i' hj' hi'
  -- The characteristic polynomial factors along the two blocks, and neither block is empty.
  -- `h_factor`: `det (charmatrix A)` is the product of the determinants of its blocks on and off
  -- `p`. Untyped: a written type gets other decidability instances than `det_fintype`.
  have h_factor := h_block.charmatrix.det_fintype.trans (Fintype.prod_Prop _)
  -- A block with at least one row has a characteristic polynomial of positive degree, not a unit.
  rcases hA.isUnit_or_isUnit h_factor with h_unit | h_unit <;>
    simp_all [← charmatrix_toSquareBlock, ← charpoly.eq_1, card_subtype, isUnit_iff_degree_eq_zero]

/-- Let `b` be an integral `N × N` matrix whose characteristic polynomial modulo `w` is
irreducible, and let `u` be an additive map from `E_w / ϖ² O_w` to `QZ = ℚ/ℤ` with `u a ≠ 0` for
some `a` whose valuation `v a` is `exp (-1)`. Then for every idempotent matrix `ε ≠ 0, 1` over
`E_w`, some `k` in `1 + ϖ M_N(O_w)` has the form `1 + ε Y (1 - ε)` and satisfies
`u (tr (b (k - 1))) ≠ 0`. -/
lemma exists_eq_one_add_mul_mul_and_map_trace_ne_zero (N : ℕ) {a : LocField w}
    (ha : v a = .exp (-1)) {b : Matrix (Fin N) (Fin N) (LocInt w)}
    (hb : Irreducible (b.map (residue (LocInt w))).charpoly)
    {u : LocField w ⧸ v.leAddSubgroup (.exp (-2)) →+ QZ} (hu : u a ≠ 0)
    {ε : Matrix (Fin N) (Fin N) (LocField w)} (h_idem : IsIdempotentElem ε) (hε₀ : ε ≠ 0)
    (hε₁ : ε ≠ 1) :
    ∃ (k : localCongruence (Fin N) w 0) (Y : Matrix (Fin N) (Fin N) (LocField w)),
      1 + ε * Y * (1 - ε) = (k : GL (Fin N) (LocField w)).val ∧
      u (b.map Subtype.val * ((k : GL (Fin N) (LocField w)).val - 1)).trace ≠ 0 := by
  -- Smith normal form `ε = K * diagonal d * q`, with `K` the image of an integral `k`.
  obtain ⟨K, ⟨k, hk⟩, q, -, d, rfl⟩ : ∃ K ∈ intGL (Fin N) (LocInt w).toSubring,
      ∃ q ∈ intGL (Fin N) (LocInt w).toSubring, ∃ d : Fin N → LocField w,
        ε = K.val * diagonal d * q.val :=
    (isValuationPair_valuationSubring (LocInt w)).smith_normal_form ε
  rw [charpoly_map, ← charpoly_units_conj' k, ← charpoly_map] at hb
  -- As `ε ≠ 0, 1`, some but not all `d i` vanish (an idempotent unit is `1`), so `k⁻¹ b k` has a
  -- unit entry across the blocks.
  have h_some : ∃ j : Fin N, d j = 0 := by
    by_contra! h_ne
    simp_all [Pi.isUnit_iff, IsIdempotentElem.iff_eq_one_of_isUnit]
  obtain ⟨j, i, hj, hi, h_entry_ne⟩ := exists_ne_zero_of_irreducible_charpoly hb h_some <| by
    by_contra! h_eq
    simp_all [funext h_eq]
  have h_unit_val : v ((k⁻¹ * b * k) j i : LocField w) = 1 := by
    simpa [adicCompletionIntegers.isUnit_iff_valued_eq_one] using h_entry_ne
  -- Write `a = (k⁻¹ b k) j i * d i * t` in the field `LocField w`; then `d i * t` has the
  -- valuation of `a`. The test element is `K (1 + single i j (d i * t)) K⁻¹`, where the
  -- trace is `a`.
  have h_entry_val_ne : ((k⁻¹ * b * k) j i : LocField w) ≠ 0 :=
    v.ne_zero_iff.mp (ne_of_eq_of_ne h_unit_val one_ne_zero)
  obtain ⟨t, rfl⟩ : ∃ t : LocField w, a = (k⁻¹ * b * k) j i * d i * t :=
    ⟨_, (mul_inv_cancel_left₀ (mul_ne_zero h_entry_val_ne hi) a).symm⟩
  have h_ne : i ≠ j := ne_of_apply_ne d fun h ↦ hi (h.trans hj)
  have h_dt_val : v (d i * t) = .exp (-1) := by
    rwa [mul_assoc, map_mul, h_unit_val, one_mul] at ha
  have h_dt_int : d i * t ∈ v.integer := by simp +decide [v.mem_integer_iff, h_dt_val]
  have h_transv_mem : transvectionGL h_ne (d i * t) ∈ localCongruence (Fin N) w 0 := by
    refine ⟨transvectionGL_mem_intGL h_ne h_dt_int, fun i' j' ↦ ?_⟩
    aesop (add simp [transvection, single_apply])
  obtain ⟨h_int', h_red⟩ := mem_localCongruence_zero.mp h_transv_mem
  have h_conj : K * transvectionGL h_ne (d i * t) * K⁻¹ ∈ localCongruence (Fin N) w 0 :=
    mem_localCongruence_zero.mpr ⟨_, reduceGL.normal_ker.conj_mem _ h_red ⟨K, k, hk⟩⟩
  let s : Matrix (Fin N) (Fin N) (LocField w) := Matrix.single i j t
  have hs_mul_diag : s * diagonal d = 0 := by aesop (add simp single_apply)
  have hs_single : Matrix.single i j (d i * t) = diagonal d * s := by aesop (add simp single_apply)
  -- With `Y = q⁻¹ * s * K⁻¹` one has `ε * Y * (1 - ε) = K * (diagonal d * s) * K⁻¹`, as
  -- `s * diagonal d = 0`.
  refine ⟨⟨_, h_conj⟩, q⁻¹ * s * K⁻¹, ?_, ?_⟩
  · simp [mul_add, add_mul, mul_sub, mul_assoc, ← s.mul_assoc, -coe_units_inv, hs_mul_diag,
      hs_single, transvection]
  · -- At the test element `k - 1 = K * (diagonal d * s) * K⁻¹`, and the trace against `b` is `a`.
    suffices h_ne_zero : u (b.map Subtype.val * (K.val * (diagonal d * (s * K⁻¹.val)))).trace ≠ 0 by
      simpa [mul_add, add_mul, mul_assoc, -coe_units_inv, hs_mul_diag, hs_single, transvection]
        using h_ne_zero
    have h_trace : (b.map Subtype.val * (K.val * (diagonal d * (s * K⁻¹.val)))).trace =
        (k⁻¹ * b * k) j i * d i * t := by
      simp [s, ← hk, ← mul_assoc, trace_mul_cycle _ s, trace_mul_single, mul_apply, ← map_inv,
        diagonal]
    rwa [h_trace]

/-- For N ≥ 1 and a finite place w, some character of 1 + ϖM_N(O_w) is nontrivial on every
unipotent radical (`New.Variety.IsCuspidalType`) and trivial on 1 + ϖ²M_N(O_w). -/
lemma exists_isCuspidalType (N : ℕ) [NeZero N] :
    ∃ θ : localCongruence (Fin N) w 0 →* ℂ,
      IsCuspidalType (localCongruence (Fin N) w 0) θ ∧
      ∀ k : localCongruence (Fin N) w 0, k.val ∈ localCongruence (Fin N) w 1 → θ k = 1 := by
  -- Put `θ k = expUnit (u (tr (b (k - 1))))`, where `b` is integral with irreducible characteristic
  -- polynomial modulo `w`, and `u` is an additive character of `E_w / ϖ²` nontrivial at `a = ϖ`.
  obtain ⟨a, ha⟩ : ∃ a : LocField w, v a = .exp (-1) := ⟨_, v_uniformizer w⟩
  obtain ⟨b, hb⟩ := exists_irreducible_charpoly_residue w N
  -- `a` is not in `ϖ² O_w`, so some additive character of `E_w / ϖ²` does not vanish at `a`.
  obtain ⟨u, hu⟩ : ∃ u : LocField w ⧸ v.leAddSubgroup (.exp (-2)) →+ QZ, u a ≠ 0 := by
    have h_a_ne : (a : LocField w ⧸ v.leAddSubgroup (.exp (-2))) ≠ 0 := by simp -dsimp +decide [ha]
    by_contra! h_zero
    exact h_a_ne (eq_zero_of_forall_hom_eq_zero h_zero)
  -- `u` kills the trace of `b * Z` when every entry of `Z` lies in `ϖ² O_w`.
  have h_small {Z : Matrix (Fin N) (Fin N) (LocField w)}
      (hZ : ∀ i j : Fin N, v (Z i j) ≤ .exp (-2)) : u (b.map Subtype.val * Z).trace = 0 := by
    have h_mem : (b.map Subtype.val * Z).trace ∈ v.leAddSubgroup (.exp (-2)) :=
      sum_mem fun i _ ↦ (v_matrix_mul_le (fun i j ↦ (b i j).prop) hZ i i).trans_eq (one_mul _)
    rw [(eq_zero_iff _).2 h_mem, map_zero]
  -- `mat k` is the matrix of `k`.
  let mat (k : localCongruence (Fin N) w 0) : Matrix (Fin N) (Fin N) (LocField w) :=
    (k : GL (Fin N) (LocField w))
  refine ⟨(Units.coeHom ℂ).comp (expUnit.comp
      (.mk' (fun k ↦ .ofAdd (u (b.map Subtype.val * (mat k - 1)).trace)) fun x y ↦ ?_)),
    fun ε h_idem hε₀ hε₁ ↦ ?_, fun k hk ↦ ?_⟩
  · -- Multiplicativity: `xy - 1 = (x - 1) + (y - 1) + (x - 1)(y - 1)`, the last term being `O(ϖ²)`.
    have hx : ∀ i j : Fin N, v ((mat x - 1) i j) ≤ .exp (-1) := x.prop.right
    have hy : ∀ i j : Fin N, v ((mat y - 1) i j) ≤ .exp (-1) := y.prop.right
    have h_xy : mat (x * y) - 1 = (mat x - 1) + (mat y - 1) + (mat x - 1) * (mat y - 1) := by
      simp only [mat, Subgroup.coe_mul, Units.val_mul]
      noncomm_ring
    have h_cross : u (b.map Subtype.val * ((mat x - 1) * (mat y - 1))).trace = 0 :=
      h_small (v_matrix_mul_le hx hy)
    simp only [h_xy, mul_add, trace_add, mk_add, map_add, h_cross, add_zero, ofAdd_add]
  · -- Cuspidality: the test element for `ε` has `θ ≠ 1`.
    obtain ⟨k, Y, hY, h_trace_ne⟩ :=
      exists_eq_one_add_mul_mul_and_map_trace_ne_zero w N ha hb hu h_idem hε₀ hε₁
    exact ⟨k, Y, hY, by simpa [expUnit_eq_one_iff] using h_trace_ne⟩
  · -- On `1 + ϖ² M_N(O_w)` the entries of `k - 1` lie in `ϖ² O_w`, so the trace term vanishes.
    have hk_entries : ∀ i j : Fin N, v ((mat k - 1) i j) ≤ .exp (-2) := hk.right
    simpa [expUnit_eq_one_iff] using h_small hk_entries

/-- Let `H` be an open subgroup of the finite adelic unitary group `Gf E n` that contains every
element of `stdLevel E n` (the stabiliser of the standard lattice) that is trivial at each place of
`S`, and suppose each `w ∈ S` has `w` or its conjugate in `B`. Then for every `N : 𝓞 E` there is a
multiple `𝔑` of `N` that (a) lies in exactly the primes that contain `N` or belong to `B`, and (b)
satisfies `u ∈ H` whenever the inverse transpose of `u` lies in `levelGU n 𝔑`, the group of
similitudes in `GL_n(Ô E)` congruent to `1` modulo `𝔑`. -/
lemma exists_levelGU_invTransposeGL_le [IsCMField E] {H : Subgroup (Gf E n)} (hH : H.IsOpen)
    {S B : Finset (FinPlace E)} (hS : stdLevel E n ⊓ trivialOn n S ≤ H)
    (hB : ∀ w ∈ S, w ∈ B ∨ star w ∈ B) (N : 𝓞 E) :
    ∃ 𝔑 : 𝓞 E,
      N ∣ 𝔑 ∧
      (∀ w : FinPlace E, 𝔑 ∈ w.asIdeal ↔ N ∈ w.asIdeal ∨ w ∈ B) ∧
      ∀ u : Gf E n, invTransposeGL u.val ∈ levelGU n 𝔑 → u ∈ H := by
  -- By compactness there are exponents `k w` such that an integral point lying in
  -- `localCongruence n w (k w)` at every `w ∈ B` belongs to `H`: the compact image of
  -- `stdLevel ∖ H` in the components at `B` misses `1`, hence misses a box of neighbourhoods of
  -- `1`.
  obtain ⟨k, hk⟩ :
      ∃ k : B → ℕ, ∀ g ∈ stdLevel E n,
        (∀ w : B, g.atPlace w.val ∈ localCongruence n w.val (k w)) → g ∈ H := by
    let comp (g : Gf E n) (w : B) : GL n (LocField w.val) := g.atPlace w
    have h_closed : IsClosed (comp '' (stdLevel E n \ H)) :=
      ((isCompact_stdLevel.diff hH).image
        (continuous_pi fun w : B ↦ continuous_atPlace w.val)).isClosed
    -- An integral point that is `1` at every place of `B` is `1` at every place of `S`, since `w`
    -- or `star w` lies in `B`; so it lies in `stdLevel E n ⊓ trivialOn n S ≤ H`.
    have h_one : 1 ∉ comp '' (stdLevel E n \ H) := by
      rintro ⟨g, ⟨hg_int, hg_not⟩, hg_one⟩
      have hg_B (w : FinPlace E) (hw : w ∈ B) : g.atPlace w = 1 := congrFun hg_one ⟨w, hw⟩
      refine hg_not (hS ⟨hg_int, ?_⟩)
      suffices hg_S : ∀ w ∈ S, g.atPlace w = 1 by simpa [trivialOn] using hg_S
      intro w hw
      rcases hB w hw with hw_B | hw_star
      · exact hg_B w hw_B
      · grind [atPlace_star_eq_one_iff]
    obtain ⟨t, ht, h_box⟩ : ∃ t : (w : B) → Set (GL n (LocField w.val)),
        (∀ w : B, IsOpen (t w) ∧ (1 : (w : B) → GL n (LocField w.val)) w ∈ t w) ∧
        Set.univ.pi t ⊆ (comp '' (stdLevel E n \ H))ᶜ :=
      isOpen_pi_iff'.mp h_closed.isOpen_compl 1 h_one
    have h_exists_k (w : B) :
        ∃ m : ℕ, (localCongruence n w.val m : Set (GL n (LocField w.val))) ⊆ t w :=
      (eventually_localCongruence_subset ((ht w).1.mem_nhds (ht w).2)).exists
    choose k hk using h_exists_k
    refine ⟨k, fun g hg h_near ↦ ?_⟩
    by_contra hg_not
    exact h_box (fun w _ ↦ hk w (h_near w)) ⟨g, ⟨hg, hg_not⟩, rfl⟩
  -- A positive power of `∏ w ^ (k w + 1)` is principal, generated by `y`; take `𝔑 = N * y`.
  obtain ⟨m, hm, y, hy⟩ :
      ∃ m ≠ 0, ∃ y : 𝓞 E, (∏ w : B, w.val.asIdeal ^ (k w + 1)) ^ m = span {y} :=
    exists_ideal_pow_eq_span_singleton _
  have hy_mem (w : FinPlace E) : y ∈ w.asIdeal ↔ w ∈ B := by
    simp [← span_singleton_le_iff_mem, ← hy, prod_le, pow_le_iff, hm,
      IsMaximal.out.le_iff_eq ne_top', asIdeal_injective.eq_iff]
  have hy_val (w : B) : v (algebraMap E (LocField w.val) y) ≤ .exp (-(k w).succ) := by
    rw [v_algebraMap_eq_intValuation, intValuation_le_pow_iff_dvd, ← hy]
    exact (Finset.dvd_prod_of_mem (fun w' : B ↦ w'.val.asIdeal ^ (k w' + 1))
      (Finset.mem_univ w)).pow hm
  refine ⟨N * y, dvd_mul_right N y, fun w ↦ ?_, ?_⟩
  · -- The primes of `N * y` are those of `N` and those of `y`.
    simp [mul_mem_iff_mem_or_mem, hy_mem]
  · -- `invTransposeGL u` is the transpose of `u⁻¹`, so we show `u⁻¹ ∈ H`.
    intro u hu
    obtain ⟨-, hu_int, hu_cong⟩ : invTransposeGL u.val ∈ GU E n ∧ u.val ∈ intGL n (Ô E) ∧
        ∀ (i j : n) (w : FinPlace E),
          v ((invTransposeGL u.val).val i j w - (if i = j then (1 : 𝔸f E) else 0) w) ≤
            v (algebraMap (𝓞 E) (𝔸f E) N w) * v (algebraMap (𝓞 E) (𝔸f E) y w) := by
      simpa [levelGU, congruenceGL, Subgroup.ofDiv, Matrix.one_apply, exists_eq_mul_iff_v_le]
        using hu
    have h_int : u⁻¹ ∈ stdLevel E n := inv_mem (show u ∈ stdLevel E n from hu_int)
    refine inv_mem_iff.mp (hk _ h_int fun w ↦ ⟨mem_stdLevel_iff.mp h_int w, fun i j ↦ ?_⟩)
    calc v (((u⁻¹.atPlace w).val - 1) i j)
      _ ≤ v (algebraMap E (LocField w.val) N) * v (algebraMap E (LocField w.val) y) := by
        -- the entry of `u⁻¹` at `w` is that of `(u at w)⁻¹` only after unfolding `atPlace`
        simpa [← evalAt_apply, eq_comm, -coe_units_inv] using! hu_cong j i w
      _ ≤ .exp (-(k w).succ) := mul_le_of_le_one_of_le (coe_algebraMap_mem ..) (hy_val w)

end New.Variety

/-!
## Multiplicity-free sums of irreducible constituents with all jumps

`New.GaloisRep.IsSphericalAbove r R J w P` says three things at every place over `w`. The
representation `r` is unramified (crystalline above `ℓ`). `R` relates the multiplicity of each
integer in `J τ` to its multiplicity as a jump at `τ`. `P` kills geometric Frobenius. With
`R = OccursIn` the middle condition reads: every element of `J τ` occurs as a jump.
-/

section MultiplicityFreeSum

open Matrix New Period Metric Filter Submodule Polynomial

/-- Let `f` and `f'` be algebra maps from a product of matrix algebras `∏ M_{d i}(k)` to matrix
algebras, with `k` algebraically closed of characteristic `0`. If `f` kills no block unit
`piMatrixUnit i` (the matrix unit `E₀₀` in factor `i`, zero in the other factors) and every
`f' (piMatrixUnit i)` has trace `1`, then `f'` is a retract of `f`: some `B` with a left inverse `C`
satisfies `f z * B = B * f' z` for all `z`. -/
lemma New.exists_retract_of_trace_map_piMatrixUnit_eq_one {k N n : Type} [Field k] [CharZero k]
    [IsAlgClosed k] [Fintype N] [DecidableEq N] [Fintype n] [DecidableEq n] {b : ℕ}
    {d : Fin b → ℕ} [∀ i : Fin b, NeZero (d i)] (f : PiMatrix k d →ₐ[k] Matrix N N k)
    (f' : PiMatrix k d →ₐ[k] Matrix n n k) (f_ne : ∀ i : Fin b, f (piMatrixUnit i) ≠ 0)
    (f'_trace : ∀ i : Fin b, (f' (piMatrixUnit i)).trace = 1) :
    ∃ (B : Matrix N n k) (C : Matrix n N k), C * B = 1 ∧ ∀ z : PiMatrix k d,
      f z * B = B * f' z := by
  -- The rank of an idempotent is its trace, so each block has rank `1` under `f'` and positive
  -- rank under `f`.
  refine exists_piMatrix_retract f f' fun i ↦ ?_
  -- `trace_of_idempotent`: the trace of an idempotent is its rank, and is `0` only for `0`.
  obtain ⟨h_trace', -⟩ := trace_of_idempotent (isIdempotentElem_map_piMatrixUnit f' i)
  obtain ⟨h_trace, h_zero_iff⟩ := trace_of_idempotent (isIdempotentElem_map_piMatrixUnit f i)
  have rank_one : (f' (piMatrixUnit i)).rank = 1 := mod_cast h_trace'.symm.trans (f'_trace i)
  have rank_ne_zero : (f (piMatrixUnit i)).rank ≠ 0 := fun h_rank ↦
    f_ne i (by rw [h_zero_iff, h_trace, h_rank, Nat.cast_zero])
  omega

/-- If the image of `s` spans the product of matrix algebras `∏ M_{d i}(k)`, then every diagonal
matrix lies in the span of the image of `s` under the block diagonal embedding, whose rows
`Σ i, Fin (d i)` are renumbered as `Fin (∑ i, d i)`. -/
lemma New.diagonal_mem_span_range_blockDiagonal {k G : Type} [Field k] [Monoid G] {b : ℕ}
    {d : Fin b → ℕ} (s : G →* PiMatrix k d) (s_span : span k (Set.range s) = ⊤)
    (v : Fin (∑ i, d i) → k) :
    diagonal v ∈ span k (Set.range fun g : G ↦
      (reindexAlgEquiv k k (finSigmaFinEquiv (n := d))).toAlgHom.comp blockDiagonalAlgHom
        (s g)) := by
  let f' : PiMatrix k d →ₐ[k] Matrix (Fin (∑ i, d i)) (Fin (∑ i, d i)) k :=
    (reindexAlgEquiv k k (finSigmaFinEquiv (n := d))).toAlgHom.comp blockDiagonalAlgHom
  -- A diagonal matrix is block diagonal, so it is the image under `f'` of an element of the span.
  have h_block : f' (fun i ↦ diagonal fun x ↦ v (finSigmaFinEquiv ⟨i, x⟩)) = diagonal v := by
    simp [f']
  rw [show (Set.range fun g : G ↦ f' (s g)) = f'.toLinearMap '' Set.range s from
    Set.range_comp f'.toLinearMap s, span_image, s_span, ← h_block]
  exact mem_map_of_mem mem_top

/-- Let `ρ τ` be continuous representations of `Gal(Ω/E)` by matrices over `ℚ̄_ℓ = PadicAlgCl ℓ`
(`(ρ τ).rep`, rows indexed by `(ρ τ).Index`), one for each index `τ` of a finite type. Some
continuous representation `σ` with non-degenerate trace form has as trace the sum of the traces of
the `ρ τ`; it acts on the rows `Σ τ, (ρ τ).Index` of their block diagonal sum. -/
lemma New.GaloisRep.exists_continuous_isTraceNondeg_trace_eq_sum {ℓ : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] {E ι : Type} [Field E] [EmbeddedNumberField E] [Fintype ι] [DecidableEq ι]
    (ρ : ι → PadicRep Gal(Ω/E) ℓ) (ρ_cont : ∀ τ : ι, Continuous (ρ τ).rep) :
    ∃ σ : GalRep ℓ E (Σ τ : ι, (ρ τ).Index),
      Continuous σ ∧
      IsTraceNondeg σ ∧
      ∀ g : Gal(Ω/E), (σ g).val.trace = ∑ τ : ι, ((ρ τ).rep g).val.trace := by
  -- `ρ_sum g` is the block diagonal matrix with the blocks `ρ τ g`. Its trace satisfies all trace
  -- identities, so it is the trace of a semisimple `σ`.
  let ρ_sum : GalRep ℓ E (Σ τ : ι, (ρ τ).Index) := .toHomUnits
    (.comp blockDiagonalAlgHom.toRingHom.toMonoidHom (.pi fun τ ↦ (Units.coeHom _).comp (ρ τ).rep))
  obtain ⟨σ, σ_ss, σ_trace⟩ : ∃ σ : GalRep ℓ E (Σ τ : ι, (ρ τ).Index),
      IsTraceNondeg σ ∧ ∀ g : Gal(Ω/E), (σ g).val.trace = (ρ_sum g).val.trace :=
    exists_rep_of_trace_identities fun _ h_vanish ↦ h_vanish ρ_sum
  replace σ_trace (g : Gal(Ω/E)) : (σ g).val.trace = ∑ τ, ((ρ τ).rep g).val.trace := by
    simp [σ_trace, ρ_sum, trace_blockDiagonal']
  refine ⟨σ, σ_ss.continuous_of_trace ?_, σ_ss, σ_trace⟩
  simp only [σ_trace]
  fun_prop

/-- Let `s` be a homomorphism from `Gal(Ω/E)` to a product `∏ᵢ M_{d i}(ℚ̄_ℓ)` of matrix algebras,
and let `f` and `f'` be `ℚ̄_ℓ`-algebra maps out of this product with `σ = f ∘ s`, where `f'` lands
in square matrices of size `∑ i, d i`. Suppose each `f' (piMatrixUnit i)` has trace `1`, where
`piMatrixUnit i` is the matrix unit `E₀₀` in factor `i` and zero elsewhere. If `u` is not a
Hodge–Tate jump at `γ` of the representation `f' ∘ s` restricted to the decomposition group of `A`,
then it is not a jump at `γ` of `σ` restricted to that group. -/
lemma New.GaloisRep.jump_eq_zero_of_jump_eq_zero_of_trace_eq_one {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ]
    {E m : Type} [Field E] [EmbeddedNumberField E] [Fintype m] [DecidableEq m] {b : ℕ}
    {d : Fin b → ℕ} [∀ i : Fin b, NeZero (d i)] {σ : GalRep ℓ E m}
    {s : Gal(Ω/E) →* PiMatrix (PadicAlgCl ℓ) d}
    (f : PiMatrix (PadicAlgCl ℓ) d →ₐ[PadicAlgCl ℓ] Matrix m m (PadicAlgCl ℓ))
    (f' : PiMatrix (PadicAlgCl ℓ) d →ₐ[PadicAlgCl ℓ]
      Matrix (Fin (∑ i, d i)) (Fin (∑ i, d i)) (PadicAlgCl ℓ))
    (hf : ∀ g : Gal(Ω/E), f (s g) = (σ g).val)
    (f'_trace : ∀ i : Fin b, (f' (piMatrixUnit i)).trace = 1) {A : ClosurePlace}
    [PadicPlaceEmbedding E A ℓ] {γ : PadicAlgCl ℓ →ₐ[ℤ_[ℓ]] ℂ_[ℓ]} {u : ℤ}
    (h_jump : jump (decompRep (.toHomUnits (.comp f' s) : GalRep ℓ E (Fin (∑ i, d i))) A) γ u = 0) :
    jump (decompRep σ A) γ u = 0 := by
  -- Let `r = f' ∘ s`. As `r` has no jump `u`, a period map `ψ` of `σ` vanishes on the images of all
  -- intertwiners from `r` to `σ`, and these images span.
  let r : GalRep ℓ E (Fin (∑ i, d i)) := .toHomUnits (.comp f' s)
  rw [jump_eq_zero_iff] at h_jump ⊢
  intro ψ hψ
  refine ψ.ext fun v ↦ ?_
  let I (i : Fin b) (c : Fin (d i)) (x : Fin (∑ i, d i)) :
      Matrix _ (Fin (∑ i, d i)) (PadicAlgCl ℓ) :=
    intertwiner f f' fun _ ↦ vecMulVec (f (piMatrixUnit i 0 c) *ᵥ v) (Pi.single x 1)
  have I_equiv (i : Fin b) (c : Fin (d i)) (x : Fin (∑ i, d i)) :
      ∀ᶠ g in nearOne (decompGroup Gal(Ω/E) A), ∀ y : Fin (∑ i, d i) → PadicAlgCl ℓ,
        (I i c x).toLin' (decompRep r A g y) = decompRep σ A g ((I i c x).toLin' y) := by
    simp [I, r, ← hf, ← mul_intertwiner]
  -- `ψ` after an intertwiner `I i c x` from `r` to `σ` is a period map of `r`, hence `0`.
  have ψ_I (i : Fin b) (c : Fin (d i)) (x : Fin (∑ i, d i)) (y : Fin (∑ i, d i) → PadicAlgCl ℓ) :
      ψ (I i c x *ᵥ y) = 0 :=
    LinearMap.congr_fun
      (h_jump _ (hodgeTateMaps.pull (I i c x).toLin' (I_equiv i c x) ⟨ψ, hψ⟩).prop) y
  have v_eq : ∑ i, ∑ c, ∑ x, I i c x *ᵥ f' (piMatrixUnit i c) *ᵥ Pi.single x 1 = v := by
    -- Each term is `f' (piMatrixUnit i) x x • f (piMatrixUnit i c c) *ᵥ v`. The sum over `x` is the
    -- trace `1`, and the units `piMatrixUnit i c c` add up to `1`.
    have term_eq (i : Fin b) (c : Fin (d i)) (x : Fin (∑ i, d i)) :
        I i c x *ᵥ f' (piMatrixUnit i c) *ᵥ Pi.single x 1 =
          f' (piMatrixUnit i) x x • f (piMatrixUnit i c c) *ᵥ v := by
      simp [I, -mulVec_single, intertwiner_mul_piMatrixUnit, mul_vecMulVec, vecMulVec_mul,
        vecMulVec_mulVec, ← map_mul, ← Pi.single_mul]
    simp [-mulVec_single, term_eq, ← Finset.sum_smul,
      fun i ↦ show ∑ x, f' (piMatrixUnit i) x x = 1 from f'_trace i, ← sum_mulVec, ← map_sum,
      sum_piMatrixUnit]
  simp only [← v_eq, map_sum, ψ_I, Finset.sum_const_zero, LinearMap.zero_apply]

/-- Suppose that for each embedding `τ` there is a continuous `ρ` which, at `F`-almost all places
`w`, is unramified or crystalline, has every member of `J τ` among its jumps at `τ`, and has
geometric Frobenius killed by `P w`. (`Set.indicator {τ} J` is `J τ` at `τ` and the empty multiset,
no condition, elsewhere.) Then there is one continuous `r` such that (a) every diagonal matrix is
in the span of its image, and (b) the same conditions hold at `F`-almost all `w`, with the jumps
`J τ` at all `τ` at once. -/
lemma New.GaloisRep.exists_rep_span_diagonal {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {E : Type} [Field E]
    [EmbeddedNumberField E] (F : Filter (FinPlace E)) (J : (E →+* ℂ) → Multiset ℤ)
    (P : FinPlace E → (PadicAlgCl ℓ)[X])
    (h_each : ∀ τ : E →+* ℂ, ∃ ρ : PadicRep Gal(Ω/E) ℓ,
      Continuous ρ.rep ∧
      ∀ᶠ w in F, IsSphericalAbove ρ.rep OccursIn (Set.indicator {τ} J) w (P w)) :
    ∃ (b : ℕ) (r : GalRep ℓ E (Fin b)),
      Continuous r ∧
      -- (a)
      (∀ v : Fin b → PadicAlgCl ℓ,
        diagonal v ∈ span (PadicAlgCl ℓ) (Set.range fun g : Gal(Ω/E) ↦ (r g).val)) ∧
      -- (b)
      ∀ᶠ w in F, IsSphericalAbove r OccursIn J w (P w) := by
  classical
  -- Let `σ` be semisimple with the trace of the sum of the `ρ τ`; the clauses pass to `σ` by
  -- `local_clauses_of_trace_limit`. Take for `r` the sum of the distinct irreducible constituents
  -- of `σ`, each once: a retract of `σ`, in which all the jumps of `σ` still occur.
  choose ρ ρ_cont hρ using h_each
  obtain ⟨σ, σ_cont, σ_ss, σ_trace⟩ := exists_continuous_isTraceNondeg_trace_eq_sum ρ ρ_cont
  -- By Wedderburn, `σ = f ∘ s`, where the image of `s` spans a product of matrix algebras and `f`
  -- kills no block unit `piMatrixUnit i`.
  obtain ⟨b, d, d_ne_zero, s, f, f_ne, s_span, hf : ∀ g : Gal(Ω/E), f (s g) = (σ g).val⟩ :=
    exists_wedderburn _ (MonoidHom.id Gal(Ω/E)) σ_ss.hasSemiprimeSpan ⟨by simp⟩
  -- `f'` is the block diagonal embedding of the product.
  let f' : PiMatrix (PadicAlgCl ℓ) d →ₐ[PadicAlgCl ℓ]
      Matrix (Fin (∑ i, d i)) (Fin (∑ i, d i)) (PadicAlgCl ℓ) :=
    (reindexAlgEquiv _ (PadicAlgCl ℓ) (finSigmaFinEquiv (n := d))).toAlgHom.comp blockDiagonalAlgHom
  have f'_trace (i : Fin b) : trace (f' (piMatrixUnit i)) = 1 := by
    simp +contextual [f', -coe_reindexAlgEquiv, Fintype.sum_eq_single i, trace_blockDiagonal']
  -- Each factor occurs in `f` and occurs once in `f'`, so `f'` is a retract of `f`.
  obtain ⟨incl, proj, h_proj_incl, h_incl⟩ :=
    exists_retract_of_trace_map_piMatrixUnit_eq_one f f' f_ne f'_trace
  let r : GalRep ℓ E (Fin (∑ i, d i)) := .toHomUnits (.comp f' s)
  have intertwine (g : Gal(Ω/E)) : (σ g).val * incl = incl * (r g).val :=
    (congrArg (· * incl) (hf g).symm).trans (h_incl (s g))
  refine ⟨_, r, .of_coeHom_comp ?_, diagonal_mem_span_range_blockDiagonal s s_span, ?_⟩
  · -- `r g = proj * σ g * incl`
    refine .congr (f := fun g ↦ proj * ((σ g).val * incl)) (by fun_prop) fun g ↦ ?_
    simp [intertwine, ← proj.mul_assoc, h_proj_incl]
  -- Fix `w` where the clauses hold for every `ρ τ`, and a place `A` over `w`.
  filter_upwards [eventually_all.mpr hρ] with w h_spherical A hA
  -- The clauses for each `ρ τ` at `A`.
  have hρ_at (τ : E →+* ℂ) :
      IsGoodAt (ρ τ).rep A ∧
      JumpsRelAt (ρ τ).rep A OccursIn (Set.indicator {τ} J) ∧
      ∀ s : Gal(Ω/E), IsFrob A w.q s⁻¹ → PolyKillsAt (ρ τ).rep A s (P w) :=
    h_spherical τ hA
  choose hρ_good hρ_jumps hρ_poly using hρ_at
  -- The clauses for `σ`, by `local_clauses_of_trace_limit` for a family with one member: an element
  -- of `J τ` is a jump of `ρ τ`, so the sum of the multiplicities is not `0`.
  have σ_limit : IsTraceLimit σ A (pure ()) 1 fun _ ↦ ρ :=
    { continuous_limit := σ_cont
      isTraceNondeg := σ_ss
      continuous_approx := fun _ ↦ ρ_cont
      isGoodAt_approx := fun _ τ ↦ hρ_good τ
      finite_or_hasJumpsAt := .inl inferInstance
      tendstoUniformly_trace := by simp [σ_trace, tendstoUniformly_iff] }
  obtain ⟨σ_good, (σ_jump : JumpsRelAt σ A OccursIn J), σ_poly⟩ :=
    local_clauses_of_trace_limit σ_limit (R := OccursIn) (J := J) (fun _ τ ↦ hρ_jumps τ)
    fun τ u x n h_occ h_tendsto hu_count hn_zero ↦ by
      have h_count_ne : (Set.indicator {τ} J τ).count u ≠ 0 := by simpa using hu_count
      -- the limit `n = 0` is the sum of the natural numbers `x () τ'`, so each of them is `0`
      have hx_zero : x () τ = 0 := by simp_all [Tendsto, ← Nat.cast_sum]
      exact h_occ () τ h_count_ne hx_zero
  -- Finite type and killing polynomials pass to the retract `r`.
  obtain ⟨(r_finite : IsFiniteTypeAt σ A → IsFiniteTypeAt r A), -, r_poly⟩ :=
    local_clauses_of_retract (A := A) (c := 1) (i := 1) (φ := .id _) (hi := by simp) (hφ := by simp)
      (hφ_open := .id) (hS := univ_mem) (h_comm := fun g _ ↦ intertwine g) (hP := h_proj_incl)
  replace r_poly (s : Gal(Ω/E)) (Q : (PadicAlgCl ℓ)[X]) :
      PolyKillsAt σ A s Q → PolyKillsAt r A s Q :=
    r_poly s ⟨⟩
  refine ⟨?_, ?_, fun s hs ↦ ?_⟩
  · obtain ⟨σ_finite, σ_inertia⟩ := (isGoodAt_iff ..).mp σ_good
    exact (isGoodAt_iff ..).mpr ⟨r_finite σ_finite, fun s hs ↦ r_poly s _ (σ_inertia s hs)⟩
  · -- A jump of `σ` is a jump of its retract `r`.
    intro L γ g hg u hu
    exact mt (jump_eq_zero_of_jump_eq_zero_of_trace_eq_one f f' hf f'_trace) (σ_jump hg u hu)
  · refine r_poly s _ (σ_poly .refl (fun _ τ ↦ ⟨.refl, hρ_poly τ s hs⟩) ?_)
    simp [σ_trace, Finset.mul_sum, tendstoUniformly_iff]

end MultiplicityFreeSum

/-! ## The Hodge–Tate cocharacter and the Zariski closure of the image -/

section HodgeTateCocharacter

open Finset Matrix LaurentPolynomial

/-- Let `p` be a prime, `x i ∈ ℂ_p` and `κ i` integers. The absolute Galois group `G_p = Gp p` of
`ℚ_p` (that is, Gal(Q̄_p/Q_p)) acts on `ℂ_p` by `g • ·`, and `χ = cyclotomicGp` is its p-adic
cyclotomic character. If a polynomial `F` over `ℂ_p` vanishes at `(χ(g) ^ (-κ i) g(x i))_i` for all
`g ∈ G_p` near `1`, then `F` vanishes at `(T ^ (κ i) x i)_i` in the Laurent polynomials over
`ℂ_p`. -/
lemma New.Period.aeval_cocharacter_eq_zero {p : ℕ} [ThePrime p] {n : Type _} [Fintype n] (κ : n → ℤ)
    (x : n → ℂ_[p]) (F : MvPolynomial n ℂ_[p])
    (h : ∀ᶠ g : Gp p in nhds 1, F.aeval (fun i : n ↦ (cyclotomicGp g ^ (-κ i)).val • g • x i) = 0) :
    F.aeval (fun i : n ↦ T (κ i) * C (x i)) = 0 := by
  -- View `F` as the vector of its coefficients, indexed by its monomials `ν`. The vectors that
  -- vanish at the twisted translates form a space `W` stable under the twisted Galois action, so
  -- by `le_of_hodgeTate_stable` it suffices to treat vectors of pure weight.
  suffices h_sum : ∑ ν : F.support, F.coeff ν • ∏ i, (T (κ i) * C (x i)) ^ ν.1 i = 0 by
    simpa only [F.aeval_def, F.eval₂_eq', ← F.support.sum_coe_sort, ← Algebra.smul_def] using h_sum
  obtain ⟨V, hV⟩ : ∃ V : OpenSubgroup (Gp p), (V : Set (Gp p)) ⊆ {g : Gp p | ∑ ν : F.support,
      F.coeff ν • ∏ i, ((cyclotomicGp g ^ (-κ i)).val • g • x i) ^ ν.1 i = 0} :=
    NonarchimedeanGroup.is_nonarchimedean _ <| show ∀ᶠ g in nhds 1, _ by
      simpa only [F.aeval_def, F.eval₂_eq', ← F.support.sum_coe_sort, ← Algebra.smul_def] using h
  -- `u ν` is the weight of the monomial `ν`; `W` consists of the vectors that vanish at the
  -- translates by all `g` in the open subgroup `V`, and `W'` of those that vanish at `T ^ κ * x`.
  let u (ν : F.support) : ℤ := ∑ i, ν.1 i * κ i
  let W : Submodule ℂ_[p] (F.support → ℂ_[p]) := (of fun (ν : F.support) (g : V) ↦
    ∏ i, ((cyclotomicGp g ^ (-κ i)).val • (g : Gp p) • x i) ^ ν.1 i).vecMulLinear.ker
  let W' : Submodule ℂ_[p] (F.support → ℂ_[p]) := (Fintype.linearCombination ℂ_[p]
    fun ν : F.support ↦ ∏ i, (T (κ i) * C (x i)) ^ ν.1 i).ker
  have hF : (fun ν : F.support ↦ F.coeff ν) ∈ W := funext fun g ↦ hV g.prop
  refine le_of_hodgeTate_stable le_rfl u W W'
    (fun a ha ↦ ?_) (fun v ν hv _hv_int h_supp _hv_one _hv_fix ↦ ?_) hF
  · -- Stability: for `k ∈ V`, apply `k` to the equation of `W` at `k⁻¹ * g`.
    filter_upwards [V.mem_nhds_one] with k hk
    refine LinearMap.mem_ker.mpr (funext fun g ↦ ?_)
    have zpow_sum (f : n → ℤ) : cyclotomicGp k ^ ∑ i, f i = ∏ i, cyclotomicGp k ^ f i := by
      simpa [-map_prod] using map_prod (zpowersHom _ (cyclotomicGp k)) (.ofAdd ∘ f) univ
    -- `h_at`: the equation of `W` for `a` at `k⁻¹ * g`, with `k` applied to both sides.
    have h_at := congrArg (k • ·) (congrFun (LinearMap.mem_ker.mp ha) (⟨k, hk⟩⁻¹ * g))
    simpa [u, mul_pow, smul_smul, smul_prod', dotProduct, _root_.zpow_mul', vecMul, smul_sum,
      zpow_sum, mul_zpow, smul_pow, prod_smul, smul_comm k, prod_mul_distrib] using h_at
  · -- For `v` of pure weight `u ν`, the equation of `W'` is that of `W` at `1`, times `T (u ν)`.
    have h_one : ∑ l, (v l : ℂ_[p]) * ∏ i, x i ^ (l : n →₀ ℕ) i = 0 := by
      simpa [vecMul, dotProduct] using congrFun (LinearMap.mem_ker.mp hv) 1
    calc ∑ l, (v l : ℂ_[p]) • ∏ i, (T (κ i) * C (x i)) ^ (l : n →₀ ℕ) i
        = ∑ l, ((v l : ℂ_[p]) * ∏ i, x i ^ (l : n →₀ ℕ) i) • T (u ν) := by
          refine sum_congr rfl fun l _ ↦ ?_
          rcases h_supp l with hl | hl
          · simp [← hl, u, T, C, -single_eq_C_mul_T]
          · simp [hl]
      _ = 0 := by rw [← sum_smul, h_one, zero_smul]

end HodgeTateCocharacter
