import Lib.DiscreteSeries.Character.MultiplicityOrbitalIntegral
import Lib.DiscreteSeries.Character.OpenOrbitIntegral

/-!
# Harish-Chandra's formula for formal degrees and stable orbital integrals

`New.Orbital.formalDegree_eq_weylDimensionPoly` is Harish-Chandra's formula for the formal degree of
a discrete series of `G = U(diag ε)`, and `New.Orbital.neg_one_pow_mul_sum_integral_dsKernel` gives
the stable sum of the orbital integrals of `New.HCParam.dsKernel` over the compact torus, both for a
parameter `l = 2λ` of gap `500 n³ + 10 n⁵`; `New.Orbital.harish_chandra_degree_and_orbital` states
the two together. By `New.Orbital.exists_laurent_orbital_integral` the orbital integral times a
product of roots is a Laurent polynomial; it is identified by comparing monomials of low level
(`New.Orbital.orbital_eq_char_sub_offOrbitIntegral`, `New.Orbital.coeff_eq_zero_of_low_level`).
The formal degree, with its constant, is read off from one coefficient in this comparison. The
orbital integrals converge absolutely by `New.Orbital.integrable_dsCoeff_conj`.

Conventions: `New.HCParam.rootProd l r` is the product of `x_a - x_b` over the pairs with
`r (ε a) (ε b)` and `l b < l a`, and `New.HCParam.lowerCount l r a` counts these `b`;
`New.Orbital.alternant ε κ` is the alternant over the permutations that preserve the signs `ε`;
`New.Orbital.torusEval x` evaluates a Laurent polynomial at a point `x` of the torus.

Notions from other files:
* `New.Orbital.oppositePairs`: The finite set of pairs of indices (a,b) with ε_a = +1 and ε_b = −1.
* `New.weylDimensionPoly`: The product of `λ i - λ j` over the pairs with `λ j < λ i`, divided by
  `∏_{i < card n} i!`, for `l = 2λ`.
* `New.HCParam.formalDegree`: For signs ε and l=2λ, the reciprocal of the integral over U(diag ε) of
  the squared modulus of the matrix coefficient `l.dsCoeff`, for the compact dual measure.
* `New.HCParam.kTypeChar`: `l.compactForm.lowestKType.kTypeChar` is the character of U(n) of
  highest weight λ − ρ.
* `New.HCParam.HasGap`, `New.HCParam.HasLargeGap`: l=2λ has distinct entries ≡ n−1 mod 2, and
  |λ_i−λ_j| ≥ h whenever ε_i ≠ ε_j; `HasLargeGap A` is the gap h = 500n³+A.

## Relation to the literature

Known result: Discrete series character on the compact Cartan via orbital integrals, and formal
degree. This is done only for U(p,q), for parameters of gap 500n³+10n⁵ and for the explicit
coefficient of the lowest K-type. It gives the formal degree, and the stable sum of elliptic orbital
integrals as a multiple of the conjugate of Weyl's character of the compact form, both exact in the
compact dual measure. Source:
Harish-Chandra, Discrete series for semisimple Lie groups II: explicit determination of the
characters, Acta Math. 116 (1966), Thm 16 (with part I, Acta Math. 113 (1965), Thm 3); Knapp,
Representation Theory of Semisimple Groups (1986), Thm 12.7.
-/

namespace New.Orbital

open Finset AddMonoidAlgebra Equiv Fintype Matrix HCParam

variable {n : Type _} [Fintype n] [DecidableEq n]

/-- Rearrangement with a gain: if `o` strictly reverses the order of `b`, then permuting `b` by `w`
raises `o ⬝ᵥ b` by at least `|b i - b (w i)|`, for every `i`. -/
theorem dotProduct_add_gain_le_comp_perm (o b : n → ℤ) (ho : ∀ i j : n, b j < b i → o i < o j)
    (w : Perm n) (i : n) : o ⬝ᵥ b + |b i - b (w i)| ≤ o ⬝ᵥ b ∘ w := by
  -- Moving `o i` by `± 1` keeps `o` antivarying with `b`, so the rearrangement inequality applies
  -- to the moved vector; the extra terms give `± (b i - b (w i))`.
  have rearr (c : ℤ) (hc : c = 1 ∨ c = -1) :
      (o + Pi.single i c) ⬝ᵥ b ≤ (o + Pi.single i c) ⬝ᵥ b ∘ w :=
    Antivary.sum_mul_le_sum_mul_comp_perm fun x y hxy ↦ by grind [ho y x hxy, Pi.add_apply]
  have up : o ⬝ᵥ b + b i ≤ o ⬝ᵥ b ∘ w + b (w i) := by simpa using rearr 1 (.inl rfl)
  have down : o ⬝ᵥ b + -b i ≤ o ⬝ᵥ b ∘ w + -b (w i) := by simpa using rearr (-1) (.inr rfl)
  grind

/-- Antisymmetrising the alternant over the Weyl group of `K` (the permutations that fix the signs
`ε`) gives the alternant over all permutations, as many times as that group has elements. -/
lemma sum_sign_mul_eval_alternant (ε : n → ℤˣ) (κ : n → ℤ) (x : n → Circle) :
    ∑ τ : Perm n, τ.sign * torusEval (x ∘ τ) (alternant ε κ) =
      #{σ : Perm n | ε ∘ σ = ε} * torusEval x (alternant 1 κ) := by
  -- Each `w` contributes `w.sign` times the determinant of `(x a ^ κ (w b))`, which is the
  -- determinant of `(x a ^ κ b)`.
  have det_eq (w : Perm n) :
      ∑ τ : Perm n, (w.sign : ℂ) * (τ.sign * ∏ a, (x (τ a) : ℂ) ^ κ (w a)) =
        torusEval x (alternant 1 κ) := by
    simpa [alternant, torusEval, det_apply', mul_sum] using
      (det_permute' w⁻¹ (of fun a b : n ↦ (x a : ℂ) ^ κ (w b))).symm.trans (det_transpose _).symm
  calc ∑ τ : Perm n, τ.sign * torusEval (x ∘ τ) (alternant ε κ)
      = ∑ w ∈ {w : Perm n | ε ∘ w = ε},
          ∑ τ : Perm n, (w.sign : ℂ) * (τ.sign * ∏ a, (x (τ a) : ℂ) ^ κ (w a)) := by
        rw [sum_comm]
        simp [alternant, torusEval, mul_sum, ← sum_filter, mul_left_comm]
    _ = _ := by simp [det_eq]

/-- Here the level of an exponent is its dot product with `o = (-l).compactForm.lowerCount Eq`, the
vector that counts the larger entries of `l`. `l.rootProd r` is the Laurent polynomial ∏ (x_a − x_b)
over the pairs with `r (ε a) (ε b)` and `l b < l a`, and `(-l).lowerCount r a` counts the `b` with
`r (ε a) (ε b)` and `l a < l b`; `compactForm` is `l` with all signs set to 1, so there the
condition is `r 1 1`. For `N = 4 n²` and an exponent `γ` of
`l.compactForm.rootProd r * l.rootProd Ne ^ N`, the level of `(-l).compactForm.lowerCount r + N •
(-l).lowerCount Ne` is less than that of `γ` plus `500 n³ + 10 n⁵`. -/
lemma lowerCount_dotProduct_lt_of_coeff_ne_zero [Nonempty n] {ε : n → ℤˣ} (l : HCParam ε)
    (r : ℤˣ → ℤˣ → Prop) [DecidableRel r] {γ : n → ℤ}
    (hγ : (l.compactForm.rootProd r * l.rootProd Ne ^ (4 * card n ^ 2)).coeff γ ≠ 0) :
    (-l).compactForm.lowerCount Eq ⬝ᵥ
        ((-l).compactForm.lowerCount r + (4 * card n ^ 2) • (-l).lowerCount Ne) <
      (-l).compactForm.lowerCount Eq ⬝ᵥ γ + (500 * card n ^ 3 + 10 * card n ^ 5 : ℕ) := by
  set N : ℕ := 4 * card n ^ 2 with hN
  set o : n → ℤ := (-l).compactForm.lowerCount Eq
  -- The product is a polynomial, so its exponent `γ` is nonnegative.
  have h_mem : (Multiplicative.ofAdd (l.compactForm.lowerCount r + N • l.lowerCount Ne),
      l.compactForm.rootProd r * l.rootProd Ne ^ N) ∈ leadingMonomials l := by
    rw [ofAdd_add, ofAdd_nsmul, ← Prod.mk_mul_mk, ← Prod.pow_mk]
    exact mul_mem (rootProd_mem_leadingMonomials l.compactForm r l fun _ _ h_lt ↦ h_lt)
      (pow_mem (rootProd_mem_leadingMonomials l Ne l fun _ _ h_lt ↦ h_lt) N)
  have γ_nonneg : 0 ≤ γ := (((mem_leadingMonomials_iff l).1 h_mem).2 γ hγ).left
  have h_right : 0 ≤ o ⬝ᵥ γ := dotProduct_nonneg_of_nonneg (lowerCount_nonneg _ Eq) γ_nonneg
  -- On the left every count is at most `n`, so the level is at most `n³ (1 + N)`.
  set c : ℤ := (card n : ℤ)
  have c_pos : 0 < c := Nat.cast_pos.2 Fintype.card_pos
  have h_entry (a : n) :
      o a * ((-l).compactForm.lowerCount r a + N * (-l).lowerCount Ne a) ≤ c * (c + N * c) := by
    have compact_nonneg : 0 ≤ (-l).compactForm.lowerCount r a := lowerCount_nonneg _ r a
    have noncompact_nonneg : 0 ≤ (-l).lowerCount Ne a := lowerCount_nonneg _ Ne a
    gcongr <;> apply lowerCount_le_card
  calc o ⬝ᵥ ((-l).compactForm.lowerCount r + N • (-l).lowerCount Ne)
      ≤ ∑ _a : n, c * (c + N * c) := sum_le_sum fun a _ ↦ by simpa using h_entry a
    _ = c ^ 3 + 4 * c ^ 5 := by simp [c, hN]; ring
    _ < o ⬝ᵥ γ + (500 * card n ^ 3 + 10 * card n ^ 5 : ℕ) := by
      push_cast
      linarith [pow_pos c_pos 3, pow_pos c_pos 5]

/-- Let `o` strictly reverse and `b` strictly keep the order of the injective parameter `l`. Let
`P = D ^ k · t` with `D = (-l).rootProd Ne`, where `t` is a formal series with `t a = 1` and each
exponent of `t` occurs in `alternant ε μ` for some `μ` with `μ - a` in the positive root cone of `l`
(`IsConeSeriesMultiple`). Let `δ = (-l).lowerCount Ne` be the exponent of the highest-level term of
`D` and suppose `a + k • δ = b`; then `P` has coefficient `1` at `b`, and for every exponent `γ` of
`P` some permutation `w` with `ε ∘ w = ε` gives `o ⬝ᵥ γ ∘ w ≤ o ⬝ᵥ b`. -/
lemma coeff_top_of_isConeSeriesMultiple {ε : n → ℤˣ} {l : HCParam ε} {o a b : n → ℤ} {k : ℕ}
    {P : ℂ[n → ℤ]} (hl : l.Injective) (ho : ∀ i j : n, l j < l i → o i < o j)
    (hb : ∀ i j : n, l j < l i → b j < b i) (hP : IsConeSeriesMultiple l a ((-l).rootProd Ne ^ k) P)
    (hab : a + k • (-l).lowerCount Ne = b) :
    P.coeff b = 1 ∧ ∀ γ : n → ℤ, P.coeff γ ≠ 0 → ∃ w : Perm n, ε ∘ w = ε ∧ o ⬝ᵥ γ ∘ w ≤ o ⬝ᵥ b := by
  obtain ⟨t, coeff_P, t_a, ht⟩ := hP
  set D : ℂ[n → ℤ] := (-l).rootProd Ne
  set δ : n → ℤ := (-l).lowerCount Ne
  simp_rw [coeff_P]
  have h_mem : (Multiplicative.ofAdd (k • δ), D ^ k) ∈ leadingMonomials o :=
    pow_mem (rootProd_mem_leadingMonomials (-l) Ne o fun i j h_lt ↦ ho j i (by simpa using h_lt)) k
  obtain ⟨coeff_top, level_lt⟩ := (mem_leadingMonomials_iff o).1 h_mem
  -- A non-zero term has `(-β + γ) ∘ w ∈ a + l.rootCone`, and `β ∘ w` is again an exponent of
  -- `D ^ k`.
  have exists_perm_level_le (γ β : n → ℤ) (hc : (D ^ k).coeff β * t (-β + γ) ≠ 0) :
      ∃ w : Perm n, ε ∘ w = ε ∧ o ⬝ᵥ γ ∘ w + (if β ∘ w = k • δ then 0 else 1) ≤ o ⬝ᵥ b := by
    obtain ⟨μ, μ_alt, μ_cone⟩ := ht (-β + γ) (right_ne_zero_of_mul hc)
    obtain ⟨w, hw, rfl⟩ : ∃ w : Perm n, ε = ε ∘ w ∧ μ = (-β + γ) ∘ w := by
      -- The alternant of `μ` has a term at `-β + γ`; invert its permutation.
      rw [alternant_apply] at μ_alt
      obtain ⟨v, -, hv⟩ := exists_ne_zero_of_sum_ne_zero μ_alt
      obtain ⟨v_fixes, v_eq⟩ : ε ∘ v = ε ∧ μ ∘ v = -β + γ := by simp_all
      exact ⟨v.symm, (v.eq_comp_symm _ _).2 v_fixes, (v.eq_comp_symm _ _).2 v_eq⟩
    have cone_le : o ⬝ᵥ γ ∘ w ≤ o ⬝ᵥ β ∘ w + o ⬝ᵥ a := by
      simpa [Pi.add_comp, Pi.neg_comp] using μ_cone o ho
    have invariant : (D ^ k).coeff (β ∘ w) = 1 * (D ^ k).coeff β := by
      refine (torusEval_comp_eq_mul_iff w).mp ?_ β
      simp [D, torusEval_rootProd_noncompact_comp (l := -l) (neg_injective.comp hl) hw.symm]
    have top_or_lt : β ∘ w = k • δ ∨ o ⬝ᵥ β ∘ w < o ⬝ᵥ k • δ :=
      (level_lt _ (by simpa [invariant] using left_ne_zero_of_mul hc)).2
    -- Add `cone_le` to the level bound for `β ∘ w`, which is strict unless `β ∘ w = k • δ`.
    exact ⟨w, hw.symm, by grind [dotProduct_add]⟩
  refine ⟨?_, fun γ hγ ↦ ?_⟩
  · -- At `γ = b` only `β = k • δ` contributes: `o ⬝ᵥ b ∘ w ≤ o ⬝ᵥ b` forces `w = 1`.
    have only_top (β : n → ℤ) (hβ : β ≠ k • δ) : (D ^ k).coeff β * t (-β + b) = 0 := by
      by_contra hc
      obtain ⟨w, -, le⟩ := exists_perm_level_le b β hc
      -- As `l` is injective, `b` has exactly the order of `l`.
      have lt_iff (i j : n) : b j < b i ↔ l j < l i := by
        have : l i < l j → b i < b j := hb j i
        grind [hl.eq_iff (a := i) (b := j)]
      have b_inj : b.Injective := fun i j h_eq ↦ hl (by grind [lt_iff i j, lt_iff j i])
      have o_anti (i j : n) (h_lt : b j < b i) : o i < o j := ho i j ((lt_iff i j).1 h_lt)
      obtain rfl : w = 1 := Perm.ext fun i ↦ b_inj <| by
        grind [dotProduct_add_gain_le_comp_perm o b o_anti w i, Perm.one_apply]
      rw [Perm.coe_one, Function.comp_id, Function.comp_id, ite_eq_right hβ] at le
      lia
    calc ((D ^ k).coeff.sum fun β d ↦ d * t (-β + b))
        = (D ^ k).coeff (k • δ) * t (-(k • δ) + b) :=
          sum_eq_single (k • δ) (fun β _ hβ ↦ only_top β hβ) (by simp +contextual)
      _ = 1 := by rw [coeff_top, one_mul, ← hab, add_comm a, neg_add_cancel_left, t_a]
  · obtain ⟨β, -, hβ⟩ := exists_ne_zero_of_sum_ne_zero hγ
    exact (exists_perm_level_le γ β hβ).imp fun w hw ↦ by grind

/-- The product of the compact roots that are positive for `l` times that of the noncompact ones is
the product of all positive roots, which is the Weyl denominator of the compact form. -/
lemma prod_compact_mul_prod_noncompact {ε : n → ℤˣ} (l : HCParam ε) :
    l.rootProd Eq * l.rootProd Ne = l.compactForm.rootProd Eq := by
  simp only [rootProd, prod_filter, ← prod_mul_distrib, Pi.one_apply]
  -- Each pair is either compact or noncompact.
  congr! 2 with a - b
  grind

/-- If `l` has a gap (so that its entries are distinct), then reversing the order of `l` multiplies
the product of the noncompact positive roots by `-1` to the power `#(oppositePairs ε)`, which is
their number. -/
lemma prod_noncompact_neg {ε : n → ℤˣ} {h : ℕ} {l : HCParam ε} (hgap : l.HasGap h) :
    (-l).rootProd Ne = ((-1) ^ #(oppositePairs ε) : ℂ) • l.rootProd Ne := by
  refine eq_of_torusEval_eq fun x ↦ ?_
  have sign_eq : (∏ p ∈ oppositePairs ε, if (-l) p.2 < (-l) p.1 then (1 : ℂ) else -1) =
      (-1) ^ #(oppositePairs ε) * ∏ p ∈ oppositePairs ε, if l p.2 < l p.1 then (1 : ℂ) else -1 := by
    rw [← prod_neg]
    exact prod_congr rfl fun p hp ↦ by
      grind [oppositePairs, Pi.neg_apply, hgap.injective.eq_iff (a := p.1) (b := p.2)]
  rw [map_smul, smul_eq_mul, torusEval_rootProd_noncompact hgap.neg.injective,
    torusEval_rootProd_noncompact hgap.injective, sign_eq, mul_assoc]

omit [DecidableEq n] in
/-- The exponent `lowestKType + lowerCount Eq` in Weyl's formula for the lowest `K`-type, for any
signs `ε'` (`toHCParam ε' l` is `l` regarded for these signs), is
`paramAddRho l + (toHCParam 1 (-l)).lowerCount Eq`, a vector independent of the signs
(`paramAddRho l` is `λ + ρ`), minus the count of the negative noncompact roots. -/
lemma lowestKType_add_lowerCount_eq (ε' : n → ℤˣ) (l : n → ℤ) :
    (toHCParam ε' l).lowestKType + (toHCParam ε' l).lowerCount Eq =
      paramAddRho l + (toHCParam 1 (-l)).lowerCount Eq - (-toHCParam ε' l).lowerCount Ne := by
  funext a
  have split : #{b : n | l a < l b} =
      #{b : n | ε' a = ε' b ∧ l a < l b} + #{b : n | ε' a ≠ ε' b ∧ l a < l b} := by
    simpa only [filter_filter, and_comm] using
      (card_filter_add_card_filter_not (s := {b : n | l a < l b}) (fun b ↦ ε' a = ε' b)).symm
  simp only [Pi.add_apply, Pi.sub_apply, lowestKType, twoRho, lowerCount, Pi.one_apply, true_and,
    Pi.neg_apply, neg_lt_neg_iff, split]
  grind

omit [DecidableEq n] in
/-- Let `l` have gap `500 n³ + 10 n⁵`, let `2 κ = l + n - 1` and let `N = 4 n²`. Then
`κ + N • (-l).lowerCount Ne` keeps the order of `l`. -/
lemma add_smul_lowerCount_lt [Nonempty n] {ε : n → ℤˣ} {l : HCParam ε} {κ : n → ℤ}
    (hgap : l.HasGap (500 * card n ^ 3 + 10 * card n ^ 5 : ℕ))
    (two_κ : ∀ a : n, l a + card n - 1 = 2 * κ a) (i j : n) (lt : l j < l i) :
    (κ + (4 * card n ^ 2) • (-l).lowerCount Ne) j <
      (κ + (4 * card n ^ 2) • (-l).lowerCount Ne) i := by
  have gap (i j : n) (ne : ε i ≠ ε j) :
      2 * (500 * card n ^ 3 + 10 * card n ^ 5 : ℕ) ≤ |l i - l j| := hgap.gap i j ne
  set N : ℕ := 4 * card n ^ 2
  simp only [lowerCount, Pi.add_apply, Pi.neg_apply, neg_lt_neg_iff, nsmul_eq_mul,
    Pi.mul_apply, Pi.natCast_apply]
  -- Either `κ` drops by more than `N n`, which bounds the change of the second term, or by the gap
  -- all indices from `j` to `i` have the same sign, so the count at `j` is at most that at `i`.
  by_cases h_drop : N * card n < κ i - κ j
  · grw [card_le_univ]
    lia
  · have same_sign (a : n) (ha : l j ≤ l a) (ha' : l a ≤ l i) : ε a = ε i := by
      grind [gap a i, gap a j, two_κ i, two_κ j]
    refine add_lt_add_of_lt_of_le (by grind [two_κ i, two_κ j]) ?_
    gcongr 3
    grind

/-- Let `o` strictly reverse the order of `κ`, let entries of `κ` at indices of different sign `ε`
be at least `h` apart, and let `m < o ⬝ᵥ κ + o ⬝ᵥ β + h` for every exponent `β` of `Q`. Then the
products of `Q` with the alternants of `κ` over all permutations and over those that fix the signs
`ε` have the same coefficients up to level `m`. -/
lemma coeff_mul_alternant_of_level_le {ε : n → ℤˣ} {o κ : n → ℤ} {h m : ℤ} {Q : ℂ[n → ℤ]}
    (ho : ∀ i j : n, κ j < κ i → o i < o j) (gap : ∀ i j : n, ε i ≠ ε j → h ≤ |κ i - κ j|)
    (level : ∀ β : n → ℤ, Q.coeff β ≠ 0 → m < o ⬝ᵥ κ + o ⬝ᵥ β + h) (γ : n → ℤ) (hγ : o ⬝ᵥ γ ≤ m) :
    (Q * alternant 1 κ).coeff γ = (Q * alternant ε κ).coeff γ := by
  -- A permutation `v` that moves a sign raises the level of `κ` by at least `h`, which `level`
  -- excludes.
  have fixes (β : n → ℤ) (hβ : Q.coeff β ≠ 0) (v : Perm n) (hv : κ ∘ v = -β + γ) :
      ε ∘ v = ε := by
    funext i
    by_contra ne
    have gain : o ⬝ᵥ κ + |κ i - κ (v i)| ≤ o ⬝ᵥ κ ∘ v :=
      dotProduct_add_gain_le_comp_perm o κ ho v i
    rw [hv, dotProduct_add, dotProduct_neg] at gain
    linarith [level β hβ, gap i (v i) (Ne.symm ne)]
  simp only [coeff_mul_apply_left, alternant_apply, Finsupp.sum]
  refine sum_congr rfl fun β hβ ↦ congrArg _ (sum_congr rfl fun v _ ↦ if_congr ?_ rfl rfl)
  simpa using fixes β (Finsupp.mem_support_iff.1 hβ) v

lemma coeff_alternant_self (ε : n → ℤˣ) {κ : n → ℤ} (hκ : κ.Injective) :
    (alternant ε κ).coeff κ = 1 := by
  rw [alternant_apply, Fintype.sum_eq_single 1 fun w hw ↦
    ite_eq_right fun ⟨_, h_eq⟩ ↦ hw (Perm.ext fun a ↦ hκ (congrFun h_eq a))]
  simp

/-- Let `P` and `Q` be antisymmetric under the Weyl group of `K`, and let each of their exponents
have a Weyl conjugate of level at most `m`. If `P` and `c • Q` agree up to level `m`, they are
equal. -/
lemma eq_smul_of_coeff_eq_of_level_le {ε : n → ℤˣ} {o : n → ℤ} {m : ℤ} {c : ℂ} {P Q : ℂ[n → ℤ]}
    (P_anti : IsWeylAntisymm ε P.coeff) (Q_anti : IsWeylAntisymm ε Q.coeff)
    (P_low : ∀ γ : n → ℤ, P.coeff γ ≠ 0 → ∃ w : Perm n, ε ∘ w = ε ∧ o ⬝ᵥ γ ∘ w ≤ m)
    (Q_low : ∀ γ : n → ℤ, Q.coeff γ ≠ 0 → ∃ w : Perm n, ε ∘ w = ε ∧ o ⬝ᵥ γ ∘ w ≤ m)
    (h_low : ∀ γ : n → ℤ, o ⬝ᵥ γ ≤ m → P.coeff γ = c * Q.coeff γ) : P = c • Q := by
  ext γ
  by_contra ne
  obtain ⟨w, hw, low_w⟩ : ∃ w : Perm n, ε ∘ w = ε ∧ o ⬝ᵥ γ ∘ w ≤ m :=
    if P_γ : P.coeff γ = 0 then Q_low γ fun Q_γ ↦ ne (by simp [P_γ, Q_γ]) else P_low γ P_γ
  have conj_eq : w.sign * P.coeff γ = c * (w.sign * Q.coeff γ) := by
    rw [← P_anti w hw γ, ← Q_anti w hw γ, h_low _ low_w]
  exact ne (by simpa [mul_left_comm c] using conj_eq)

omit [DecidableEq n] in
/-- The number of entries of `l` above `l i` strictly reverses the order of `l`. -/
lemma lowerCount_neg_compactForm_lt {ε : n → ℤˣ} (l : HCParam ε) {i j : n} (h_lt : l j < l i) :
    (-l).compactForm.lowerCount Eq i < (-l).compactForm.lowerCount Eq j := by
  have h_ssubset : ({a : n | l i < l a} : Finset n) ⊂ ({a : n | l j < l a} : Finset n) :=
    (ssubset_iff_of_subset (by grind)).2 ⟨i, by simpa using h_lt, by simp⟩
  simpa [lowerCount] using card_lt_card h_ssubset

/-- The exponent `κ` of the numerator in Weyl's character formula for the compact form of `l`. It
is `paramAddRho l` plus the vector that counts, at `i`, the entries of `l` above `l i`. -/
def numeratorExponent {ε : n → ℤˣ} (l : HCParam ε) : n → ℤ :=
  paramAddRho l + (-l).compactForm.lowerCount Eq

omit [DecidableEq n] in
/-- The exponent of Weyl's numerator is `(l + n - 1) / 2`. -/
lemma two_mul_numeratorExponent {ε : n → ℤˣ} {h : ℕ} {l : HCParam ε} (hgap : l.HasGap h) (a : n) :
    l a + card n - 1 = 2 * numeratorExponent l a := by
  have count : (#{b : n | l b < l a} : ℤ) + #{b : n | l a < l b} + 1 = card n :=
    mod_cast card_lt_add_card_gt_add_one hgap.injective a
  have h_two := two_mul_paramAddRho hgap a
  simp [numeratorExponent, lowerCount, twoRho] at h_two ⊢
  lia

/-- Weyl's character formula for the compact form of `l`: the Weyl denominator times the character
of the lowest `K`-type is the full alternant of `numeratorExponent l`. -/
lemma torusEval_rootProd_mul_kTypeChar {ε : n → ℤˣ} {h : ℕ} {l : HCParam ε} (hgap : l.HasGap h)
    (x : n → Circle) :
    torusEval x (l.compactForm.rootProd Eq) * l.compactForm.lowestKType.kTypeChar (diagTorusK x) =
      torusEval x (alternant 1 (numeratorExponent l)) := by
  -- The compact form has no noncompact roots.
  have exponent : l.compactForm.lowestKType + l.compactForm.lowerCount Eq = numeratorExponent l :=
    (lowestKType_add_lowerCount_eq 1 l).trans (by simp [numeratorExponent, lowerCount, funext_iff])
  simpa only [exponent] using
    (weyl_character_kTypeChar hgap.signs_one.injective hgap.signs_one.isKDominant_lowestKType).2 x

/-- The bound of `lowerCount_dotProduct_lt_of_coeff_ne_zero` for the product `(-l).rootProd Ne` of
the negative noncompact roots in place of `l.rootProd Ne`, with both sides shifted by the level of
`a`. -/
lemma level_add_lt_of_coeff_ne_zero [Nonempty n] {ε : n → ℤˣ} {h : ℕ} {l : HCParam ε}
    (hgap : l.HasGap h) (r : ℤˣ → ℤˣ → Prop) [DecidableRel r] (a : n → ℤ) {γ : n → ℤ}
    (hγ : (l.compactForm.rootProd r * (-l).rootProd Ne ^ (4 * card n ^ 2)).coeff γ ≠ 0) :
    (-l).compactForm.lowerCount Eq ⬝ᵥ
        (a + (-l).compactForm.lowerCount r + (4 * card n ^ 2) • (-l).lowerCount Ne) <
      (-l).compactForm.lowerCount Eq ⬝ᵥ a + (-l).compactForm.lowerCount Eq ⬝ᵥ γ +
        (500 * card n ^ 3 + 10 * card n ^ 5 : ℕ) := by
  rw [add_assoc, dotProduct_add, add_assoc, add_lt_add_iff_left]
  exact lowerCount_dotProduct_lt_of_coeff_ne_zero l r
    (by simpa [prod_noncompact_neg hgap, smul_pow] using hγ)

/-- Let `l` have gap `500 n³ + 10 n⁵`, let `D = (-l).rootProd Ne`, `N = 4 n²` and
`κ = numeratorExponent l`, and let the level of `γ` be `(-l).compactForm.lowerCount Eq ⬝ᵥ γ`. At
exponents of level at most that of `κ + N • (-l).lowerCount Ne`, the products of `D ^ N` with the
alternants of `κ` over all permutations and over the Weyl group of `K` have equal coefficients. -/
lemma coeff_pow_mul_alternant_one_of_level_le [Nonempty n] {ε : n → ℤˣ} {l : HCParam ε}
    (hgap : l.HasGap (500 * card n ^ 3 + 10 * card n ^ 5 : ℕ)) (γ : n → ℤ)
    (hγ : (-l).compactForm.lowerCount Eq ⬝ᵥ γ ≤ (-l).compactForm.lowerCount Eq ⬝ᵥ
      (numeratorExponent l + (4 * card n ^ 2) • (-l).lowerCount Ne)) :
    ((-l).rootProd Ne ^ (4 * card n ^ 2) * alternant 1 (numeratorExponent l)).coeff γ =
      ((-l).rootProd Ne ^ (4 * card n ^ 2) * alternant ε (numeratorExponent l)).coeff γ := by
  set h : ℕ := 500 * card n ^ 3 + 10 * card n ^ 5 with hh
  set κ : n → ℤ := numeratorExponent l
  have two_κ (a : n) : l a + card n - 1 = 2 * κ a := two_mul_numeratorExponent hgap a
  have gap_κ (i j : n) (ne : ε i ≠ ε j) : h ≤ |κ i - κ j| := by
    have double : |l i - l j| = 2 * |κ i - κ j| := by grind [two_κ i, two_κ j]
    linarith [hgap.gap i j ne]
  have level_anti (i j : n) (lt : κ j < κ i) :
      (-l).compactForm.lowerCount Eq i < (-l).compactForm.lowerCount Eq j :=
    lowerCount_neg_compactForm_lt l (by linarith [two_κ i, two_κ j])
  refine coeff_mul_alternant_of_level_le level_anti gap_κ (fun β hβ ↦ ?_) γ hγ
  -- The compact form has no noncompact roots, so the case `r = Ne` of
  -- `level_add_lt_of_coeff_ne_zero` bounds the exponents of `D ^ N`.
  simpa [rootProd, lowerCount.eq_unfold, hh] using
    level_add_lt_of_coeff_ne_zero hgap Ne κ (γ := β) (by simpa [rootProd] using hβ)

/-- For injective `l`, a power of the product of the negative noncompact roots times the alternant
of `κ` is antisymmetric under the permutations that fix the signs `ε`. -/
lemma isWeylAntisymm_pow_mul_alternant {ε : n → ℤˣ} {l : HCParam ε} (hl : l.Injective)
    (κ : n → ℤ) (N : ℕ) :
    IsWeylAntisymm ε ((-l).rootProd Ne ^ N * alternant ε κ).coeff := fun w hw ↦ by
  refine (torusEval_comp_eq_mul_iff w).1 fun x ↦ ?_
  have D_invariant : torusEval (x ∘ w) ((-l).rootProd Ne) = torusEval x ((-l).rootProd Ne) :=
    torusEval_rootProd_noncompact_comp (neg_injective.comp hl) hw x
  have alt_anti : torusEval (x ∘ w) (alternant ε κ) = w.sign * torusEval x (alternant ε κ) :=
    (torusEval_comp_eq_mul_iff w).2 (isWeylAntisymm_alternant w hw) x
  simp only [map_mul, map_pow, D_invariant, alt_anti, mul_left_comm]

/-- For injective `κ`, a power of the product of the negative noncompact roots times the alternant
of `κ` is that power times a series `t` with `t κ = 1` whose exponents each occur in some
`alternant ε μ` with `μ - κ` in the positive root cone of `l` (`IsConeSeriesMultiple`): the series
is the alternant. -/
lemma isConeSeriesMultiple_pow_mul_alternant {ε : n → ℤˣ} (l : HCParam ε) {κ : n → ℤ}
    (hκ : κ.Injective) (N : ℕ) :
    IsConeSeriesMultiple l κ ((-l).rootProd Ne ^ N) ((-l).rootProd Ne ^ N * alternant ε κ) :=
  ⟨(alternant ε κ).coeff, coeff_mul_apply_left _ _, coeff_alternant_self ε hκ,
    fun γ hγ ↦ ⟨κ, hγ, by simp [rootCone]⟩⟩

/-- Let the Harish-Chandra parameter `l` for the signs `ε` have gap `500 n³ + 10 n⁵`
(`HasLargeGap (10 * n ^ 5)`), let `D = (-l).rootProd Ne` be the product of the negative noncompact
roots, and let `N = 4 n²`. Then `l.formalDegree` times the squared norm `kTypeNormSq` of the lowest
`K`-type of the compact form equals `1`. Moreover `Vc · D ^ (N + 1) · Θ = D ^ N · alternant ε
(numeratorExponent l)` (`IsOrbitalLaurent`), where `Θ x` is `l.formalDegree` times
`∫ g : USign ε, l.dsCoeff (g⁻¹ * diagTorus ε x * g)`, the normalised orbital integral of `l.dsCoeff`
on the diagonal torus, `Vc` is the Weyl denominator of `K`, the alternant is summed over the Weyl
group of `K`, and `numeratorExponent l` is the numerator exponent in Weyl's character formula for
the compact form.

The second part is Harish-Chandra's character formula on the compact torus, for the normalised
orbital integral of `l.dsCoeff`, with denominators cleared and only for parameters of this gap. -/
lemma formalDegree_mul_kTypeNormSq_and_isOrbitalLaurent [Nonempty n] {ε : n → ℤˣ} {l : HCParam ε}
    (hg : l.HasLargeGap (10 * card n ^ 5)) :
    l.formalDegree * l.compactForm.lowestKType.kTypeNormSq = 1 ∧
    IsOrbitalLaurent l ((-l).rootProd Ne ^ (4 * card n ^ 2 + 1))
      ((-l).rootProd Ne ^ (4 * card n ^ 2) * alternant ε (numeratorExponent l)) := by
  -- Let `Θ x` be `l.formalDegree` times the orbital integral of `l.dsCoeff` at `x`. By
  -- `exists_laurent_orbital_integral`, `P = l.rootProd Eq * D ^ (N + 1) * Θ` is a Laurent
  -- polynomial. It equals `scalar • numerator ε` for `numerator ε = D ^ N * alternant ε κ`: by
  -- `orbital_eq_char_sub_offOrbitIntegral` and `coeff_eq_zero_of_low_level` the difference has no
  -- exponent of low level, but each of its exponents has a Weyl conjugate of low level. The
  -- coefficients at `top = κ + N • δ` give `scalar = 1`.
  have hgap : l.HasGap (500 * card n ^ 3 + 10 * card n ^ 5 : ℕ) := hg
  -- The level of `γ` is `o ⬝ᵥ γ`, where `o i` is the number of entries of `l` above `l i`.
  let o : n → ℤ := (-l).compactForm.lowerCount Eq
  let κ : n → ℤ := numeratorExponent l
  have two_κ (a : n) : l a + card n - 1 = 2 * κ a := two_mul_numeratorExponent hgap a
  let N : ℕ := 4 * card n ^ 2
  let D : ℂ[n → ℤ] := (-l).rootProd Ne
  obtain ⟨P, hP⟩ : ∃ P, IsOrbitalLaurent l (D ^ (N + 1)) P := exists_laurent_orbital_integral l hg
  let Λ : HCParam (1 : n → ℤˣ) := l.compactForm.lowestKType
  obtain ⟨σ, norm_σ, orbital⟩ : ∃ σ : ℂ, ‖σ‖ = 1 ∧ ∀ x : n → Circle,
      (signMatrix ε * diagTorus ε x).IsAccretive →
        σ * ∫ g : USign ε, l.dsCoeff (g⁻¹ * diagTorus ε x * g :) = Λ.kTypeNormSq *
          Λ.kTypeChar (diagTorusK x) - offOrbitIntegral l (signMatrix ε * diagTorus ε x) :=
    orbital_eq_char_sub_offOrbitIntegral hgap
  have σ_ne : σ ≠ 0 := norm_ne_zero_iff.mp (norm_σ.trans_ne one_ne_zero)
  let δ : n → ℤ := (-l).lowerCount Ne
  let noncompactSign : ℂ := (-1) ^ #(oppositePairs ε)
  have D_eq : D = noncompactSign • l.rootProd Ne := prod_noncompact_neg hgap
  let scalar : ℂ := l.formalDegree * Λ.kTypeNormSq * noncompactSign / σ
  let numerator (ε' : n → ℤˣ) : ℂ[n → ℤ] := D ^ N * alternant ε' κ
  let top : n → ℤ := κ + N • δ
  have o_anti (i j : n) (lt : l j < l i) : o i < o j := lowerCount_neg_compactForm_lt l lt
  have top_mono (i j : n) (lt : l j < l i) : top j < top i :=
    add_smul_lowerCount_lt hgap two_κ i j lt
  have top_eq : l.lowestKType + l.lowerCount Eq + (N + 1) • δ = top := by
    rw [show l.lowestKType + l.lowerCount Eq = κ - δ from lowestKType_add_lowerCount_eq ε l,
      succ_nsmul',
      ← add_assoc, sub_add_cancel]
  obtain ⟨P_top, P_low⟩ : P.coeff top = 1 ∧
      ∀ γ : n → ℤ, P.coeff γ ≠ 0 → ∃ w : Perm n, ε ∘ w = ε ∧ o ⬝ᵥ γ ∘ w ≤ o ⬝ᵥ top :=
    coeff_top_of_isConeSeriesMultiple hgap.injective o_anti top_mono hP.isConeSeriesMultiple top_eq
  have κ_inj : κ.Injective := fun i j h_eq ↦ hgap.injective (by grind [two_κ i, two_κ j])
  obtain ⟨numerator_top, numerator_low⟩ : (numerator ε).coeff top = 1 ∧
      ∀ γ : n → ℤ, (numerator ε).coeff γ ≠ 0 → ∃ w : Perm n, ε ∘ w = ε ∧ o ⬝ᵥ γ ∘ w ≤ o ⬝ᵥ top :=
    coeff_top_of_isConeSeriesMultiple hgap.injective o_anti top_mono
      (isConeSeriesMultiple_pow_mul_alternant l κ_inj N) rfl
  -- By `orbital` and Weyl's formula for `U(n)`, on the accretive part of the torus
  -- `P - scalar • numerator 1` is a multiple of `offOrbitIntegral`; with the bound
  -- `level_add_lt_of_coeff_ne_zero` this excludes exponents of level at most that of `top`.
  have off_orbit (x : n → Circle) (hx : (signMatrix ε * diagTorus ε x).IsAccretive) :
      torusEval x (P - scalar • numerator 1) =
        torusEval x (-(l.formalDegree * noncompactSign / σ) • (l.compactForm.rootProd Eq * D ^ N)) *
          offOrbitIntegral l (signMatrix ε * diagTorus ε x) := by
    have integral_eq : ∫ g : USign ε, l.dsCoeff (g⁻¹ * diagTorus ε x * g :) =
        (Λ.kTypeNormSq * Λ.kTypeChar (diagTorusK x) -
          offOrbitIntegral l (signMatrix ε * diagTorus ε x)) / σ :=
      eq_div_of_mul_eq σ_ne ((mul_comm _ _).trans (orbital x hx))
    simp only [numerator, scalar, κ, Λ, map_sub, map_smul, map_mul, map_pow, hP.torusEval_eq,
      integral_eq, ← torusEval_rootProd_mul_kTypeChar hgap, ← prod_compact_mul_prod_noncompact l,
      pow_succ, D_eq, smul_eq_mul]
    ring
  have vanish (γ : n → ℤ) (hγ : o ⬝ᵥ γ ≤ o ⬝ᵥ top) : (P - scalar • numerator 1).coeff γ = 0 :=
    coeff_eq_zero_of_low_level hgap off_orbit o_anti γ fun β hβ ↦
      hγ.trans_lt (level_add_lt_of_coeff_ne_zero hgap Eq (paramAddRho l) (right_ne_zero_of_mul hβ))
  have P_eq : P = scalar • numerator ε := by
    refine eq_smul_of_coeff_eq_of_level_le hP.antisymm
      (isWeylAntisymm_pow_mul_alternant hgap.injective κ N) P_low numerator_low fun γ hγ ↦ ?_
    have numerator_one : (numerator 1).coeff γ = (numerator ε).coeff γ :=
      coeff_pow_mul_alternant_one_of_level_le hgap γ hγ
    simpa [numerator_one, sub_eq_zero] using vanish γ hγ
  have scalar_eq : scalar = 1 := by simpa [P_eq, numerator_top] using P_top
  have norm_eq : ‖scalar‖ = l.formalDegree * Λ.kTypeNormSq := by
    simp [scalar, noncompactSign, abs_of_pos, formalDegree_pos hg, norm_σ]
  exact ⟨by rw [← norm_eq, scalar_eq, norm_one], by rwa [P_eq, scalar_eq, one_smul] at hP⟩

/-- **Harish-Chandra's formal degree formula**, for a parameter `l` of gap `500 n³ + 10 n⁵`: the
formal degree of the discrete series, for the compact dual measure, is the value
`weylDimensionPoly l` of Weyl's dimension polynomial. -/
theorem formalDegree_eq_weylDimensionPoly [Nonempty n] {ε : n → ℤˣ} {l : HCParam ε}
    (hg : l.HasLargeGap (10 * card n ^ 5)) : l.formalDegree = weylDimensionPoly l := by
  rw [eq_inv_of_mul_eq_one_left (formalDegree_mul_kTypeNormSq_and_isOrbitalLaurent hg).1]
  exact weyl_dimension_formula (HasGap.signs_one hg)

/-- Absolute convergence of the orbital integrals: for a parameter `l` of gap `500 n³ + 10 n⁵` and a
regular point `x` of the compact torus, `g ↦ l.dsCoeff (g⁻¹ x g)` is integrable on `U(diag ε)`.

This is Harish-Chandra's convergence theorem for regular orbital integrals of Schwartz functions,
restricted to one discrete series coefficient (a Schwartz function by Harish-Chandra) of
`U(diag ε)`, the compact torus and parameters of large gap. -/
theorem integrable_dsCoeff_conj [Nonempty n] {ε : n → ℤˣ} {l : HCParam ε}
    (hg : l.HasLargeGap (10 * card n ^ 5)) {x : n → Circle} (x_inj : x.Injective) :
    MeasureTheory.Integrable fun g : USign ε ↦ l.dsCoeff (g⁻¹ * diagTorus ε x * g :) := by
  -- The integrand times a power `D` of the noncompact roots is integrable, and `D(x) ≠ 0`.
  let D : ℂ[n → ℤ] := (-l).rootProd Ne ^ (4 * card n ^ 2 + 1)
  let ψ : C(USign ε, C(maxCompactU ε, ℂ)) :=
    (ContinuousMap.mk fun p : USign ε × maxCompactU ε ↦
      l.dsCoeffSmooth.val (p.1⁻¹ * p.2 * p.1)).curry
  have hψ (g : USign ε) (k : maxCompactU ε) : ψ g k = l.dsCoeff (g⁻¹ * k * g :) := rfl
  choose s ν hν apply_eq using exists_sign_isKDominant hg.injective
  have hs : IsStraightening l s ν := ⟨hν, apply_eq⟩
  obtain ⟨Y, hXY⟩ := hs.exists_isWeylFamily hg.injective
  obtain ⟨d, hd⟩ : ∃ d : C(maxCompactU ε, ℂ),
      ∀ (y : maxCompactU ε) (t : n → Circle), d (y * diagTorusK t * y⁻¹) = torusEval t D :=
    hXY.exists_apply_conj_eq hg.injective fun w hw t ↦ by
      simp [D, torusEval_rootProd_noncompact_comp hg.neg.injective hw]
  have d_ne : d (diagTorusK x) ≠ 0 := by
    rw [show d (diagTorusK x) = torusEval x D by simpa using hd 1 x, map_pow]
    exact pow_ne_zero _ (torusEval_rootProd_ne_zero (-l) Ne x_inj)
  have h_mul : MeasureTheory.Integrable fun g : USign ε ↦ d (diagTorusK x) * ψ g (diagTorusK x) :=
    (ContinuousMap.evalCLM ℂ (diagTorusK x)).integrable_comp
      (integrable_mul_dsCoeff_conj l hg hd hψ)
  exact (MeasureTheory.integrable_const_mul_iff d_ne.isUnit _).1 h_mul

/-- Let the Harish-Chandra parameter `l = 2λ` have gap `500 n³ + 10 n⁵`, and let `l.dsKernel g` be
`l.formalDegree` (`deg_λ`) times the conjugate of the discrete series coefficient `l.dsCoeff g`
(`c_λ(g)`). At a regular point `x` of the compact torus, the stable sum of the orbital integrals of
`l.dsKernel` is, up to the sign `(-1) ^ #(oppositePairs ε)`, the order of the Weyl group of `K`
times the conjugate of Weyl's character of `U(n)` of highest weight `l.compactForm.lowestKType`.
Here `oppositePairs ε` is the set of pairs `(a, b)` with `ε a = 1` and `ε b = -1`.

This is a consequence of Harish-Chandra's elliptic orbital integral formula for discrete series
coefficients. It gives only the sum over all permutations, and the integrals converge absolutely by
`integrable_dsCoeff_conj`. -/
theorem neg_one_pow_mul_sum_integral_dsKernel [Nonempty n] {ε : n → ℤˣ} {l : HCParam ε}
    (hg : l.HasLargeGap (10 * card n ^ 5)) {x : n → Circle} (x_inj : x.Injective) :
    (-1) ^ #(oppositePairs ε) *
        ∑ σ : Perm n, ∫ g : USign ε, l.dsKernel (g⁻¹ * diagTorus ε (x ∘ σ) * g) =
      #{σ : Perm n | ε ∘ σ = ε} * star (l.compactForm.lowestKType.kTypeChar (diagTorusK x)) := by
  -- Divide the Laurent polynomial `D ^ N * alternant ε κ` of the orbital integral by `D ^ N` and
  -- antisymmetrise over all permutations; Weyl's character formula identifies the result.
  let κ : n → ℤ := numeratorExponent l
  let N : ℕ := 4 * card n ^ 2
  let D : ℂ[n → ℤ] := (-l).rootProd Ne
  let s : ℂ := (-1) ^ #(oppositePairs ε)
  let V : ℂ[n → ℤ] := l.compactForm.rootProd Eq
  have hP : IsOrbitalLaurent l (D ^ (N + 1)) (D ^ N * alternant ε κ) :=
    (formalDegree_mul_kTypeNormSq_and_isOrbitalLaurent hg).2
  have V_anti (w : Perm n) : torusEval (x ∘ w) V = w.sign * torusEval x V := by
    simp only [V, weyl_denominator (HasGap.signs_one hg).injective]
    exact (torusEval_comp_eq_mul_iff w).2 (isWeylAntisymm_alternant w rfl) x
  have D_eq : D = s • l.rootProd Ne := prod_noncompact_neg hg
  have V_eq : V = l.rootProd Eq * l.rootProd Ne := (prod_compact_mul_prod_noncompact l).symm
  have denom : l.rootProd Eq * D ^ (N + 1) = D ^ N * (s • V) := by
    rw [V_eq, ← mul_smul_comm, ← D_eq, pow_succ, mul_left_comm]
  -- Evaluate at `x ∘ τ` and cancel `D ^ N`.
  have integral_eq (τ : Perm n) : torusEval x V * s * l.formalDegree *
      ∫ g : USign ε, l.dsCoeff (g⁻¹ * diagTorus ε (x ∘ τ) * g :) =
        τ.sign * torusEval (x ∘ τ) (alternant ε κ) := by
    set I : ℂ := ∫ g : USign ε, l.dsCoeff (g⁻¹ * diagTorus ε (x ∘ τ) * g :)
    have eval_P : torusEval (x ∘ τ) (D ^ N * alternant ε κ) =
        torusEval (x ∘ τ) (l.rootProd Eq * D ^ (N + 1)) * (l.formalDegree * I) :=
      hP.torusEval_eq (x ∘ τ)
    have sign_sq : (τ.sign : ℂ) * τ.sign = 1 := by simp [← Int.cast_mul]
    have D_ne : torusEval (x ∘ τ) D ≠ 0 :=
      torusEval_rootProd_ne_zero (-l) Ne (x_inj.comp τ.injective)
    simp only [denom, map_mul, map_pow, map_smul, smul_eq_mul, V_anti τ, mul_assoc] at eval_P
    rw [mul_left_cancel₀ (pow_ne_zero N D_ne) eval_P]
    linear_combination -(torusEval x V * s * l.formalDegree * I) * sign_sq
  -- Conjugate, multiply by the Weyl denominator, sum over `τ` and compare with Weyl's formula.
  have kernel (τ : Perm n) : star (∫ g : USign ε, l.dsKernel (g⁻¹ * diagTorus ε (x ∘ τ) * g)) =
      l.formalDegree * ∫ g : USign ε, l.dsCoeff (g⁻¹ * diagTorus ε (x ∘ τ) * g :) := by
    simp [dsKernel, integral_conj, MeasureTheory.integral_const_mul]
  refine star_injective (mul_left_cancel₀ (torusEval_rootProd_ne_zero l.compactForm Eq x_inj) ?_)
  calc torusEval x V *
        star (s * ∑ τ : Perm n, ∫ g : USign ε, l.dsKernel (g⁻¹ * diagTorus ε (x ∘ τ) * g))
      = ∑ τ : Perm n, τ.sign * torusEval (x ∘ τ) (alternant ε κ) := by
        simp only [star_mul', show star s = s by simp [s], star_sum, kernel, mul_sum, ← mul_assoc,
          integral_eq]
    _ = #{σ : Perm n | ε ∘ σ = ε} * torusEval x (alternant 1 κ) :=
        sum_sign_mul_eval_alternant ε κ x
    _ = _ := by simp [κ, ← torusEval_rootProd_mul_kTypeChar hg, mul_left_comm]

/-- Let `l = 2λ` be a Harish-Chandra parameter for the signs `ε`, with `n` nonempty and gap
`500 n³ + 10 n⁵`. Then (a) the formal degree, the reciprocal of `∫ |c_λ|²` over `USign ε`, equals
`weylDimensionPoly l`; (b) at every regular point `x` of the compact torus (`x` injective), the sum
over all permutations `σ` of the orbital integrals `∫ l.dsKernel (g⁻¹ diag(x ∘ σ) g) dg`, which
converge absolutely by `integrable_dsCoeff_conj`, times `(-1)` to the number of pairs `(a, b)` with
`ε a = 1` and `ε b = -1`, equals `#{σ | ε ∘ σ = ε}` (the order of the Weyl group of `K`) times the
conjugate of Weyl's character `l.compactForm.lowestKType.kTypeChar` of the compact form at
`diag(x)`. Here `c_λ` is `l.dsCoeff`, `deg_λ` is `l.formalDegree`, and `l.dsKernel` is `deg_λ` times
the complex conjugate of `c_λ`.

These are Harish-Chandra's formal degree formula and the stable form, summed over all permutations,
of his formula for elliptic orbital integrals of discrete series coefficients, for U(p, q),
parameters with large gap and one coefficient. -/
theorem harish_chandra_degree_and_orbital {ε : n → ℤˣ} {l : HCParam ε} [Nonempty n]
    (hg : l.HasLargeGap (10 * card n ^ 5)) :
    l.formalDegree = weylDimensionPoly l ∧
    ∀ x : n → Circle, x.Injective →
      (-1) ^ #(oppositePairs ε) *
          ∑ σ : Perm n, ∫ g : USign ε, l.dsKernel (g⁻¹ * diagTorus ε (x ∘ σ) * g) =
        #{σ : Perm n | ε ∘ σ = ε} * star (l.compactForm.lowestKType.kTypeChar (diagTorusK x)) :=
  ⟨formalDegree_eq_weylDimensionPoly hg, fun _ ↦ neg_one_pow_mul_sum_integral_dsKernel hg⟩

end New.Orbital
