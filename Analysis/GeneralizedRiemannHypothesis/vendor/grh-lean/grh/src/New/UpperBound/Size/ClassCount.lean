import New.Spanning.RemainingTerms.Box
import New.UpperBound.Size.ShortColumns

/-!
# Explicit bound for the number of classes in the genus

This file gives a crude explicit bound `New.Space.card_stdClasses_le` for the number of classes
`New.StdClasses (New.stdLevel E n)` in the genus of the standard lattice. A class is determined
by the Gram matrix `G` of a short basis of its lattice and a rational approximation `X` of the
change of basis. Both `G` and `G X` have integral entries of bounded size, and such matrices are
counted.

## Main definitions and results

* `New.Space.card_stdClasses_le`: an explicit bound for the number of classes
  `New.StdClasses (New.stdLevel E n)`, for a CM field `E` with `f` infinite places and a natural
  number `N ≠ 0` in the different of `E`.
* `New.Space.stdClasses_eq_of_gram_eq`: two classes `g`, `g'` in `Γ \ G_f / K₀` are equal if
  there are `Y`, `Y'` in `GL n E` with the same Gram matrix such that `A' A⁻¹` has entries in
  `Ô E`, where `A = g.out⁻¹ Y` and `A' = g'.out⁻¹ Y'`.

Notions from other files:
* `New.StdClasses K`: the double cosets `Γ \ G_f / K` of the finite adelic unitary group `G_f` of
  the form `∑ x_i \bar x_i` by its rational points `Γ` and a subgroup `K`.
* `New.stdLevel`: the subgroup `K₀ = G_f ∩ GL_n(Ô)`, the stabiliser of the standard lattice `Ô^n`.

## Relation to the literature

See `New.UpperBound.Size.Estimates` for related work.
-/

noncomputable section

section ClassCountBound

open NumberField Matrix Fintype DoubleCoset Units

/-- If the entries of `M` and `M'` have absolute values at most `a` and `b` under a complex
embedding `φ`, then those of `M M'` have absolute value at most `#n · a b`. -/
lemma New.Space.norm_map_mul_apply_le {E n : Type} [Field E] [Fintype n] (φ : E →+* ℂ)
    {M M' : Matrix n n E} {a b : ℝ}
    (hM : ∀ i j : n, ‖φ (M i j)‖ ≤ a) (hM' : ∀ i j : n, ‖φ (M' i j)‖ ≤ b) (i j : n) :
    ‖φ ((M * M') i j)‖ ≤ card n * (a * b) := calc
  ‖φ ((M * M') i j)‖ ≤ ∑ k, ‖φ (M i k)‖ * ‖φ (M' k j)‖ := by
    simpa [mul_apply] using norm_sum_le _ fun k ↦ φ (M i k) * φ (M' k j)
  _ ≤ ∑ _k : n, a * b := Finset.sum_le_sum fun k _ ↦
    mul_le_mul (hM i k) (hM' k j) (norm_nonneg _) ((norm_nonneg _).trans (hM i k))
  _ = card n * (a * b) := by simp

/-- Let `c = shortBasisConst E n N = 6 N (f #n)²`, with `f` the number of infinite places of `E`.
If at the infinite place `w` (with embedding `Φ w`) the entries of `Y` have size at most `c` and
those of `X` at most `(2 f)² N`, then the entries of `Yᴴ Y` and `Yᴴ Y X` have size at most `c³`. -/
lemma New.Space.norm_gram_apply_le_cube {E n : Type} [Field E] [CMType E] [Fintype n] {N : ℕ}
    [NeZero N] {Y X : Matrix n n E} {w : InfinitePlace E}
    (hY : ∀ i j : n, ‖Φ w (Y i j)‖ ≤ shortBasisConst E n N)
    (hX : ∀ i j : n, ‖Φ w (X i j)‖ ≤ (2 * Core.numInfPlaces E) ^ 2 * N) (i j : n) :
    ‖Φ w ((Yᴴ * Y) i j)‖ ≤ shortBasisConst E n N ^ 3 ∧
      ‖Φ w ((Yᴴ * Y * X) i j)‖ ≤ shortBasisConst E n N ^ 3 := by
  set c : ℕ := shortBasisConst E n N with hc
  have h_gram (i j : n) : ‖Φ w ((Yᴴ * Y) i j)‖ ≤ card n * (c * c) :=
    norm_map_mul_apply_le (Φ w) (fun i j ↦ by simpa using hY j i) hY i j
  have h_card : card n ≤ c := calc
    card n ≤ (Core.numInfPlaces E * card n) ^ 2 :=
      (Nat.le_mul_of_pos_left _ NeZero.one_le).trans (Nat.le_self_pow two_ne_zero _)
    _ ≤ c := Nat.le_mul_of_pos_left _ (by simp [NeZero.pos])
  constructor
  · calc ‖Φ w ((Yᴴ * Y) i j)‖
      _ ≤ c * (c * c) := (h_gram i j).trans (by gcongr)
      _ = c ^ 3 := by ring
  · calc ‖Φ w ((Yᴴ * Y * X) i j)‖
      _ ≤ card n * (card n * (c * c) * ((2 * Core.numInfPlaces E) ^ 2 * N)) :=
        norm_map_mul_apply_le (Φ w) h_gram hX i j
      -- Here `card n ^ 2 * (2 f) ^ 2 * N = 4 N (f * card n) ^ 2`, which is at most `c`.
      _ = (4 * N * (Core.numInfPlaces E * card n) ^ 2 : ℕ) * (c * c) := by
        push_cast
        ring
      _ ≤ c * (c * c) := by
        rw [hc, shortBasisConst]
        gcongr
        norm_num
      _ = c ^ 3 := by ring

/-- Let `g` be a finite adelic unitary matrix and `Y`, `Z` matrices over `E` such that `g Y` and
`g Z` have entries in the integral finite adeles `Ô E`. Then the entries of `Yᴴ Z` are algebraic
integers. -/
lemma New.Space.isIntegral_conjTranspose_mul_apply {E n : Type} [Field E] [CMType E] [Fintype n]
    [DecidableEq n] (g : Gf E n) {Y Z : Matrix n n E}
    (hY : IsIntMatrix (Ô E) ((g : Matrix n n (𝔸f E)) * Y.map (algebraMap E (𝔸f E))))
    (hZ : IsIntMatrix (Ô E) ((g : Matrix n n (𝔸f E)) * Z.map (algebraMap E (𝔸f E)))) (i j : n) :
    IsIntegral ℤ ((Yᴴ * Z) i j) := by
  -- As `g` is unitary for the form `1`, we have `Yᴴ Z = (g Y)ᴴ (g Z)`.
  have h_int : IsIntMatrix (Ô E) ((Y.map (algebraMap E (𝔸f E)))ᴴ * (1 : Matrix n n (𝔸f E)) *
      Z.map (algebraMap E (𝔸f E))) := by
    rw [← U.gram_invariant g]
    exact (hY.conjTranspose.mul .one).mul hZ
  rw [← algebraMap_mem_Ô]
  simpa [mul_apply] using h_int i j

/-- Let `g`, `g'` be double cosets in `StdClasses K₀ = Γ \ G_f / K₀`, with representatives `g.out`,
`g'.out`, and let `Y`, `Y'` in `GL n E` have the same Gram matrix. Put `A = g.out⁻¹ Y` and
`A' = g'.out⁻¹ Y'`. If `A' A⁻¹` has entries in `Ô`, then `g' = g`. -/
lemma New.Space.stdClasses_eq_of_gram_eq {E n : Type} [Field E] [CMType E] [Fintype n]
    [DecidableEq n] {g g' : StdClasses (stdLevel E n)} {Y Y' : GL n E} {A A' : GL n (𝔸f E)}
    (hA : A = (g.out⁻¹ : Gf E n) * Y.map (algebraMap E (𝔸f E)))
    (hA' : A' = (g'.out⁻¹ : Gf E n) * Y'.map (algebraMap E (𝔸f E)))
    (h_gram : (Y' : Matrix n n E)ᴴ * Y' = (Y : Matrix n n E)ᴴ * Y)
    (h_int : IsIntMatrix (Ô E) (A' * A⁻¹).val) : g' = g := by
  -- `γ = Y Y'⁻¹` is a rational isometry, since the Gram matrices agree.
  have h_isom : Y * Y'⁻¹ ∈ U (stdSpace E n).J :=
    gram_mul_of_gram_eq rfl (gram_inv_of_gram_eq (by simpa using h_gram))
  let γ : Gf E n := (stdSpace E n).embFin ⟨Y * Y'⁻¹, h_isom⟩
  have hγ_mem : γ ∈ (stdSpace E n).Γf := ⟨_, rfl⟩
  -- We have `g.out = γ g'.out k` with `k = A' A⁻¹`.
  let k : Gf E n := (γ * g'.out)⁻¹ * g.out
  have hk_eq : (k : GL n (𝔸f E)) = A' * A⁻¹ := by simp [k, γ, hA, hA', mul_assoc]
  have hk_mem : k ∈ stdLevel E n := by rwa [mem_stdLevel, hk_eq]
  exact Quotient.out_equiv_out.1 (rel_iff.2 ⟨γ, hγ_mem, k, hk_mem, by simp [k, mul_assoc]⟩)

/-- Let `E` be a CM field with `f` infinite places, `N ≠ 0` a natural number in the different of
`E`, and `r = #n`. Then the set `StdClasses K₀` of double cosets `Γ \ G_f / K₀` has at most
`(1 + 2 c³) ^ (4 f r²)` elements, where `c = shortBasisConst E n N = 6 N (f r)²`. -/
lemma New.Space.card_stdClasses_le {E : Type} [Field E] [CMType E] {N : ℕ} [NeZero N]
    (hN_different : (N : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E)) {n : Type} [Fintype n] [DecidableEq n] :
    Nat.card (StdClasses (stdLevel E n)) ≤
      (1 + 2 * shortBasisConst E n N ^ 3) ^ (4 * Core.numInfPlaces E * card n ^ 2) := by
  -- To a class `g` attach a short basis `Y` of its lattice, the Gram matrix `G = Yᴴ Y` and a
  -- bounded rational matrix `X ≡ (g⁻¹ Y)⁻¹` modulo `Ô`. The pair `(G, G X)` has integral entries
  -- with conjugates of size at most `c ^ 3`, and it determines the class.
  let ι : E →+* 𝔸f E := algebraMap E (𝔸f E)
  have h_basis (g : StdClasses (stdLevel E n)) : ∃ Y : GL n E,
      IsIntMatrix (Ô E) (((g.out⁻¹ : Gf E n) : Matrix n n (𝔸f E)) * Y.val.map ι) ∧
        ∀ (φ : E →+* ℂ) (i j : n), ‖φ (Y i j)‖ ≤ shortBasisConst E n N :=
    exists_short_basis_stdSpace hN_different g.out
  choose Y hY_int hY_le using h_basis
  have h_near (y : 𝔸f E) : ∃ a : E, y - ι a ∈ Ô E ∧
      ∀ w : InfinitePlace E, ‖Φ w a‖ ≤ (2 * Core.numInfPlaces E) ^ 2 * N := by
    simpa using exists_principal_near_of_mem_differentIdeal NeZero.out hN_different 0 y
  choose approx h_approx_int h_approx_le using h_near
  let A (g : StdClasses (stdLevel E n)) : GL n (𝔸f E) := (g.out⁻¹ : Gf E n) * (Y g).map ι
  let G (g : StdClasses (stdLevel E n)) : GL n E := star (Y g) * Y g
  let X (g : StdClasses (stdLevel E n)) : Matrix n n E := (A g)⁻¹.val.map approx
  -- Both `A g'` and `(A g)⁻¹ - X g` are integral.
  have hA_diff_int (g g' : StdClasses (stdLevel E n)) :
      IsIntMatrix (Ô E) ((A g' * (A g)⁻¹).val - (A g').val * (X g).map ι) := by
    rw [val_mul, ← mul_sub]
    exact (hY_int g').mul fun i j ↦ h_approx_int _
  have hAX (g : StdClasses (stdLevel E n)) : IsIntMatrix (Ô E) ((A g).val * (X g).map ι) := by
    simpa using IsIntMatrix.one.sub (hA_diff_int g g)
  have hYX (g : StdClasses (stdLevel E n)) : IsIntMatrix (Ô E)
      (((g.out⁻¹ : Gf E n) : Matrix n n (𝔸f E)) * (Y g * X g).map ι) := by
    simpa [Matrix.map_mul, ← mul_assoc, A] using hAX g
  -- The invariant of the class `g`: the entries of `G` (for `false`) and of `G X` (for `true`).
  let invariant (g : StdClasses (stdLevel E n)) : Bool × n × n → E :=
    fun (k, i, j) ↦ (bif k then G g * X g else G g : Matrix n n E) i j
  have h_invariant_int (g : StdClasses (stdLevel E n)) (k : Bool) (i j : n) :
      IsIntegral ℤ (invariant g (k, i, j)) := by
    cases k
    · exact isIntegral_conjTranspose_mul_apply _ (hY_int g) (hY_int g) i j
    · simpa [invariant, G, mul_assoc, star_eq_conjTranspose] using
        isIntegral_conjTranspose_mul_apply _ (hY_int g) (hYX g) i j
  have h_invariant_le (g : StdClasses (stdLevel E n)) (k : Bool) (i j : n) (w : InfinitePlace E) :
      ‖Φ w (invariant g (k, i, j))‖ ≤ shortBasisConst E n N ^ 3 := by
    obtain ⟨hG_le, hGX_le⟩ : ‖Φ w (G g i j)‖ ≤ shortBasisConst E n N ^ 3 ∧
        ‖Φ w ((G g * X g) i j)‖ ≤ shortBasisConst E n N ^ 3 :=
      norm_gram_apply_le_cube (hY_le g (Φ w)) (fun i j ↦ h_approx_le _ w) i j
    cases k
    exacts [hG_le, hGX_le]
  have h_invariant_inj : Function.Injective invariant := by
    intro g' g h_eq
    have hG : (G g').val = G g := Matrix.ext fun i j ↦ congrFun h_eq (false, i, j)
    have hGX : G g' * X g' = G g * X g := Matrix.ext fun i j ↦ congrFun h_eq (true, i, j)
    have hX : X g' = X g := (G g).mul_right_inj.1 (by rw [← hGX, hG])
    -- `A g' (A g)⁻¹` is the sum of the integral `A g' (A g)⁻¹ - A g' X g` and `A g' X g'`.
    have h_int : IsIntMatrix (Ô E) (A g' * (A g)⁻¹).val := by
      simpa only [hX, sub_add_cancel] using (hA_diff_int g g').add (hAX g')
    exact stdClasses_eq_of_gram_eq rfl rfl hG h_int
  -- Count the integral vectors with `2 (card n)²` entries whose conjugates are at most `c ^ 3`.
  have h_card : (Set.univ : Set (StdClasses (stdLevel E n))).encard ≤
      ENNReal.ofReal ((1 + 2 * shortBasisConst E n N ^ 3) ^
        (card (Bool × n × n) * Core.numInfPlaces E * 2)) :=
    Filling.encard_le_of_isIntegral_norm_le invariant (by positivity)
      (fun g _ ⟨k, i, j⟩ ↦ ⟨h_invariant_int g k i j, h_invariant_le g k i j⟩)
      h_invariant_inj.injOn
  rw [← Set.ncard_univ, show 4 * Core.numInfPlaces E * card n ^ 2 =
    card (Bool × n × n) * Core.numInfPlaces E * 2 by simp [sq, mul_comm, mul_left_comm]]
  exact ENat.toNat_le_of_le_natCast (mod_cast h_card)

end ClassCountBound

end
