import Lib.General.NumberTheory.PadicLimitsValuation

/-!
# Coefficient rings with a large residue field

Adjoining the roots of unity of order `ℓ ^ k - 1` to a finite extension of `ℚ_ℓ` multiplies the
degree by at most `k` and gives a residue field with at least `ℓ ^ k - 1` elements. The extension is
unramified, but this is not needed: the ramification index is at most the degree, which grows
linearly in `k`, while `ℓ ^ k` grows faster.

* `New.Selmer.frequently_lt_card_residueField`: beyond every coefficient ring there is one whose
  residue field is large compared with the ramification index.

Notions from other files:
* `New.CoeffRing ℓ`: rings of integers of finite Galois extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, ordered
  by inclusion;
* `New.ThePrime ℓ`: the class saying that `ℓ` is prime.
-/

namespace New.Selmer

open IsDiscreteValuationRing IsLocalRing IntermediateField Module Polynomial

variable {ℓ : ℕ} [ThePrime ℓ]

/-- An element `x` of `ℚ̄_ℓ` of norm less than `1` and of degree `d` over `ℚ_ℓ` satisfies
`‖x‖ ^ d ≤ ‖ℓ‖`. -/
lemma norm_pow_natDegree_minpoly_le {x : PadicAlgCl ℓ} (hx : ‖x‖ < 1) :
    ‖x‖ ^ (minpoly ℚ_[ℓ] x).natDegree ≤ ‖(ℓ : PadicAlgCl ℓ)‖ := by
  -- `‖x‖ ^ d` is the norm of the constant coefficient, an element of `ℚ_ℓ` of norm less than `1`.
  have h_pos : (minpoly ℚ_[ℓ] x).natDegree ≠ 0 :=
    (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)).ne'
  have h_coeff : ‖x‖ ^ (minpoly ℚ_[ℓ] x).natDegree = ‖(minpoly ℚ_[ℓ] x).coeff 0‖ := by
    rw [← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, one_div,
      Real.rpow_inv_natCast_pow (norm_nonneg _) h_pos]
  have h_lt : ‖(minpoly ℚ_[ℓ] x).coeff 0‖ < (ℓ : ℝ) ^ (0 : ℤ) := by
    simpa [← h_coeff] using pow_lt_one₀ (norm_nonneg x) hx h_pos
  rw [h_coeff, ← map_natCast (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)), PadicAlgCl.norm_extends]
  simpa using (Padic.norm_lt_pow_iff_norm_le_pow_sub_one _ 0).1 h_lt

/-- If a coefficient ring `O`, the ring of integers of a finite Galois extension of `ℚ_ℓ`, is
contained in a finite extension `K` of `ℚ_ℓ`, then its ramification index, the valuation of `ℓ`
in `O`, is at most the degree of `K`. -/
lemma addVal_ell_le_finrank (O : CoeffRing ℓ) (K : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] K] (hK : ∀ x ∈ (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ)), x ∈ K) :
    addVal O (ℓ : ↑O) ≤ finrank ℚ_[ℓ] K := by
  -- For a uniformiser `ϖ` of degree `d`, `ℓ` divides `ϖ ^ d`.
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible O
  let d : ℕ := (minpoly ℚ_[ℓ] ϖ.1).natDegree
  have h_norm : ‖(ϖ : PadicAlgCl ℓ)‖ < 1 :=
    (O.norm_le_one ϖ).lt_of_ne (mt (O.isUnit_iff_norm_eq_one ϖ).2 hϖ.not_isUnit)
  have h_dvd : (ℓ : ↑O) ∣ ϖ ^ d := by
    simpa [O.dvd_iff_norm_le] using norm_pow_natDegree_minpoly_le h_norm
  have h_deg : d ≤ finrank ℚ_[ℓ] K := by
    simpa only [d, K.minpoly_eq] using minpoly.natDegree_le (A := ℚ_[ℓ]) (⟨ϖ.1, hK _ ϖ.2⟩ : K)
  calc addVal O (ℓ : ↑O) ≤ addVal O (ϖ ^ d) := addVal_le_iff_dvd.2 h_dvd
    _ = d := hϖ.addVal_pow _
    _ ≤ finrank ℚ_[ℓ] K := Nat.cast_le.2 h_deg

/-- An element `ζ` of `ℚ̄_ℓ` with `ζ ^ (ℓ ^ k - 1) = 1`, where `k ≠ 0`, has degree at most `k` over
`ℚ_ℓ`. -/
lemma natDegree_minpoly_le_of_pow_eq_one {k : ℕ} [NeZero k] {ζ : PadicAlgCl ℓ}
    (hζ : ζ ^ (ℓ ^ k - 1) = 1) : (minpoly ℚ_[ℓ] ζ).natDegree ≤ k := by
  -- The conjugates of `ζ` are among the `ζ ^ ℓ ^ j`, which depend only on `j` modulo `k`.
  have h_frob : ζ ^ ℓ ^ k = ζ := by
    rw [← Nat.sub_add_cancel (Nat.one_le_pow k ℓ (NeZero.pos ℓ)), pow_succ, hζ, one_mul]
  have h_iter (q : ℕ) : ζ ^ (ℓ ^ k) ^ q = ζ := by
    induction q with
    | zero => simp
    | succ q ih => rw [pow_succ, pow_mul, ih, h_frob]
  have h_roots : (minpoly ℚ_[ℓ] ζ).rootSet (PadicAlgCl ℓ) ⊆
      Set.range fun j : Fin k ↦ ζ ^ ℓ ^ j.1 := by
    intro y hy
    obtain ⟨σ, rfl⟩ : ∃ σ : Gp ℓ, σ ζ = y := minpoly.exists_algEquiv_of_root'
      (Algebra.IsAlgebraic.isAlgebraic ζ) (aeval_eq_zero_of_mem_rootSet hy)
    obtain ⟨j, hj⟩ : ∃ j : ℕ, σ ζ = ζ ^ ℓ ^ j := exists_apply_eq_pow not_dvd_pow_sub_one hζ σ
    refine ⟨⟨j % k, Nat.mod_lt j (NeZero.pos k)⟩, ?_⟩
    calc ζ ^ ℓ ^ (j % k) = (ζ ^ (ℓ ^ k) ^ (j / k)) ^ ℓ ^ (j % k) := by rw [h_iter]
      _ = ζ ^ ℓ ^ j := by rw [← pow_mul ℓ, ← pow_mul, ← pow_add, Nat.div_add_mod]
      _ = σ ζ := hj.symm
  calc (minpoly ℚ_[ℓ] ζ).natDegree = ((minpoly ℚ_[ℓ] ζ).rootSet (PadicAlgCl ℓ)).ncard := by
        rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
          card_rootSet_eq_natDegree (Algebra.IsSeparable.isSeparable _ ζ) (IsAlgClosed.splits _)]
    _ ≤ (Set.range fun j : Fin k ↦ ζ ^ ℓ ^ j.1).ncard := Set.ncard_le_ncard h_roots
    _ ≤ k := by simpa [Nat.card_coe_set_eq] using Finite.card_range_le fun j : Fin k ↦ ζ ^ ℓ ^ j.1

/-- If a coefficient ring `O`, the ring of integers of a finite Galois extension of `ℚ_ℓ`, holds a
primitive `m`-th root of unity `ζ` of `ℚ̄_ℓ` and `m` is prime to `ℓ`, then the residue field of
`O` has at least `m` elements. -/
lemma le_card_residueField_of_isPrimitiveRoot {O : CoeffRing ℓ} {m : ℕ} (hm : ¬ℓ ∣ m) {ζ : ↑O}
    (hζ : IsPrimitiveRoot (ζ : PadicAlgCl ℓ) m) : m ≤ Nat.card (ResidueField O) := by
  -- The residue of `ζ` has order `m`: if `ζ ^ j ≠ 1`, then `ζ ^ j - 1` divides the unit `m`.
  have : Finite (ResidueField O) := Ring.HasFiniteQuotients.finiteQuotient (not_a_field O)
  have h_norm_m : ‖((m : ↑O) : PadicAlgCl ℓ)‖ = 1 := by
    push_cast
    rw [← map_natCast (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)), PadicAlgCl.norm_extends]
    exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm)
  have hζ_pow : ζ ^ m = 1 := Subtype.ext hζ.pow_eq_one
  have h_prim : IsPrimitiveRoot (residue O ζ) m := by
    refine ⟨by rw [← map_pow, hζ_pow, map_one], fun j hj ↦ hζ.dvd_of_pow_eq_one j ?_⟩
    by_contra h_ne
    have h_dvd : ζ ^ j - 1 ∣ (m : ↑O) :=
      sub_one_dvd_natCast_of_pow_eq_one (by rw [pow_right_comm, hζ_pow, one_pow])
        fun h ↦ h_ne (congrArg Subtype.val h)
    have h_isUnit : IsUnit (ζ ^ j - 1) :=
      isUnit_of_dvd_unit h_dvd ((O.isUnit_iff_norm_eq_one _).2 h_norm_m)
    exact (h_isUnit.map (residue O)).ne_zero (by simp [hj])
  exact h_prim.eq_orderOf.le.trans orderOf_le_card

variable (ℓ) in
/-- For every natural number `a` there is a positive `k` with `a k + 1 < ℓ ^ k - 1`. -/
lemma exists_mul_add_one_lt_pow_sub_one (a : ℕ) : ∃ k : ℕ, 0 < k ∧ a * k + 1 < ℓ ^ k - 1 := by
  let j : ℕ := 2 * a + 1
  -- The exponent `2 j` works, as `(j + 1) ^ 2 ≤ ℓ ^ (2 j)`.
  refine ⟨j * 2, by positivity, Nat.lt_sub_of_add_lt ?_⟩
  calc a * (j * 2) + 1 + 1 < (j + 1) ^ 2 := by grind
    _ ≤ (ℓ ^ j) ^ 2 := Nat.pow_le_pow_left (Nat.lt_pow_self (Fact.out : ℓ.Prime).one_lt) 2
    _ = ℓ ^ (j * 2) := (pow_mul ℓ j 2).symm

variable (ℓ) in
/-- For every natural number `c` and every coefficient ring, that is, the ring of integers of a
finite Galois extension of `ℚ_ℓ`, there is a coefficient ring containing it whose residue field has
more than `c · e + 1` elements, where `e`, the valuation of `ℓ`, is the ramification index of the
containing ring. -/
lemma frequently_lt_card_residueField (c : ℕ) :
    ∃ᶠ O : CoeffRing ℓ in Filter.atTop,
      c * addVal O (ℓ : ↑O) + 1 < Nat.card (ResidueField O) := by
  -- Adjoin to the field `K₀`, of degree `d`, a primitive root of unity of order `ℓ ^ k - 1`, where
  -- `c d k + 2 < ℓ ^ k`.
  refine Filter.frequently_atTop.2 ?_
  rintro ⟨_, K₀, rfl⟩
  let d : ℕ := finrank ℚ_[ℓ] K₀
  obtain ⟨k, hk_pos, hk⟩ : ∃ k : ℕ, 0 < k ∧ c * (d * k) + 1 < ℓ ^ k - 1 := by
    simpa only [← mul_assoc] using exists_mul_add_one_lt_pow_sub_one ℓ (c * d)
  have : NeZero k := ⟨hk_pos.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (PadicAlgCl ℓ) (ℓ ^ k - 1)
  have hζ_int : IsIntegral ℚ_[ℓ] ζ := Algebra.IsIntegral.isIntegral ζ
  have : IsCyclotomicExtension {ℓ ^ k - 1} ℚ_[ℓ] ℚ_[ℓ]⟮ζ⟯ :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ_[ℓ]

  have : FiniteDimensional ℚ_[ℓ] ℚ_[ℓ]⟮ζ⟯ := adjoin.finiteDimensional hζ_int
  have : IsGalois ℚ_[ℓ] ℚ_[ℓ]⟮ζ⟯ := IsCyclotomicExtension.isGalois {ℓ ^ k - 1} _ _
  let K : FiniteGaloisIntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) := ⟨K₀.1 ⊔ ℚ_[ℓ]⟮ζ⟯⟩
  obtain ⟨O, hO⟩ : ∃ O : CoeffRing ℓ, ∀ x : PadicAlgCl ℓ,
      x ∈ (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ)) ↔ ‖x‖ ≤ 1 ∧ x ∈ K.1 :=
    ⟨⟨_, K, rfl⟩, fun x ↦ Iff.rfl⟩
  have hζ_mem : ζ ∈ (O : Subalgebra ℤ_[ℓ] (PadicAlgCl ℓ)) := (hO ζ).2
    ⟨(hζ.isOfFinOrder (NeZero.ne _)).norm_eq_one.le,
      (le_sup_right : ℚ_[ℓ]⟮ζ⟯ ≤ K.1) (mem_adjoin_simple_self _ ζ)⟩
  have h_deg : finrank ℚ_[ℓ] K ≤ d * k :=
    (finrank_sup_le _ _).trans <| Nat.mul_le_mul_left d <|
      (adjoin.finrank hζ_int).trans_le (natDegree_minpoly_le_of_pow_eq_one hζ.pow_eq_one)
  refine ⟨O, ?_, ?_⟩
  · rintro x ⟨hx_norm, hx_mem⟩
    exact (hO x).2 ⟨hx_norm, (le_sup_left : K₀.1 ≤ K.1) hx_mem⟩
  have h_addVal : addVal O (ℓ : ↑O) ≤ (d * k : ℕ) :=
    (addVal_ell_le_finrank O K.1 fun x hx ↦ ((hO x).1 hx).2).trans (Nat.cast_le.2 h_deg)
  calc c * addVal O (ℓ : ↑O) + 1 ≤ c * (d * k : ℕ) + 1 := by gcongr
    _ < (ℓ ^ k - 1 : ℕ) := by exact_mod_cast hk
    _ ≤ Nat.card (ResidueField O) := Nat.cast_le.2 <|
      le_card_residueField_of_isPrimitiveRoot not_dvd_pow_sub_one (ζ := ⟨ζ, hζ_mem⟩) hζ

end New.Selmer
