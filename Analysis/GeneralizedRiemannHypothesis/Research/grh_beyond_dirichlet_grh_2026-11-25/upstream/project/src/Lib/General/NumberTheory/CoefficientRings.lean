import Lib.General.Algebra.AdicCompletion
import Lib.General.Algebra.FittingIdealsAndLengths

/-!
# Coefficient rings of ℓ-adic lattices, and length versus cardinality of modules

The coefficient rings over which ℓ-adic lattices are taken, and, for modules over an ℓ-adic
integer ring, a comparison of length with cardinality.

* `New.card_eq_pow_length`: over an ℓ-adic integer ring R with residue field k, a module of finite
  length has #k ^ length elements.
* `New.length_le_of_card_le`, `New.length_le_of_card_dvd`: an inequality of cardinalities (the
  smaller module being finite) or a divisibility of cardinalities gives an inequality of lengths.
* `New.CoeffRing ℓ`: the rings of integers O of finite Galois extensions of ℚ_ℓ inside ℚ̄_ℓ. Each is
  a finite ℤ_ℓ-module, compact, and a discrete valuation ring with divisibility read from the norm
  (`New.CoeffRing.dvd_iff_norm_le`).
* `New.CoeffRing.eventually_mem`: an element of norm at most 1 lies in all sufficiently large
  coefficient rings. That the rings are directed by inclusion is an instance.

Three imported notions occur in the statements:

* `New.ThePrime ℓ`: the class saying that ℓ is prime, which fixes the prime ℓ in scope;
* `New.DVR O`: O is an integral domain and a discrete valuation ring;
* `New.PadicIntegerRing R ℓ`: R is a discrete valuation ring of characteristic 0, finite and free
  over ℤ_ℓ, with finite quotients by nonzero ideals.
-/

-- These instances on subalgebras get priority 10, so that other instances are tried first.
open Subalgebra in
attribute [instance 10] instSMulSubtypeMem instMulActionSubtypeMem moduleLeft
  instDistribMulActionSubtypeMem instSMulWithZeroSubtypeMem instMulActionWithZeroSubtypeMem

namespace New

open PadicInt IsDiscreteValuationRing NeZero IsLocalRing Module IntermediateField minpoly Finite Nat

variable {R : Type*} (ℓ : ℕ) [ThePrime ℓ] {X Y : Type} [CommRing R]

/-- Let R be an ℓ-adic integer ring (`New.PadicIntegerRing R ℓ`: a discrete valuation ring of
characteristic 0, finite and free over ℤ_ℓ, with finite quotients by nonzero ideals) with residue
field k. An R-module X of finite length has #k ^ length X elements. -/
lemma card_eq_pow_length [PadicIntegerRing R ℓ] [AddCommGroup X] [Module R X]
    (hX : length R X < ⊤) :
    Nat.card X = Nat.card (ResidueField R) ^ (length R X).lift hX := by
  -- induction on a composition series: each simple quotient is a copy of the residue field
  induction length_ne_top_iff.1 hX.ne with
  | of_subsingleton => simp [card_unique]
  | @of_simple_quotient M _ _ N h_simple hN ih =>
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 h_simple
    obtain rfl : I = IsLocalRing.maximalIdeal R := eq_maximalIdeal hI
    have h_card : Nat.card (M ⧸ N) = Nat.card (ResidueField R) := card_congr e.toEquiv
    have h_length : length R M = length R N + 1 := by
      rw [length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), length_eq_one R (M ⧸ N)]
    -- #M = #(M ⧸ N) * #N, and the induction hypothesis gives #N
    rw [N.card_eq_card_quotient_mul_card, h_card, ih (length_ne_top_iff.2 hN).lt_top]
    simp [h_length, pow_succ, mul_comm]

/-- The residue field of an ℓ-adic integer ring R is finite: it is the quotient of R by a nonzero
ideal. -/
lemma PadicIntegerRing.finite_residueField [PadicIntegerRing R ℓ] : Finite (ResidueField R) :=
  Ring.HasFiniteQuotients.finiteQuotient (not_a_field R)

/-- Over an ℓ-adic integer ring R (`New.PadicIntegerRing R ℓ`), an infinite module Y has infinite
length. -/
lemma length_eq_top_of_infinite [PadicIntegerRing R ℓ] [AddCommGroup Y] [Module R Y]
    [Infinite Y] : length R Y = ⊤ := by
  have : Finite (ResidueField R) := PadicIntegerRing.finite_residueField ℓ
  by_contra h_length
  -- the cardinality of `Y` would be a power of the size of the residue field, hence not `0`
  have h_card : Nat.card Y ≠ 0 := by
    rw [card_eq_pow_length ℓ (lt_top_iff_ne_top.2 h_length)]
    exact pow_ne_zero _ Nat.card_pos.ne'
  exact h_card Nat.card_eq_zero_of_infinite

/-- Let R be an ℓ-adic integer ring, and let X and Y be R-modules. If X is finite and #X ≤ #Y, then
length X ≤ length Y. The inequality forces Y to be finite too, since `Nat.card X` is positive and
`Nat.card` is 0 for an infinite type. -/
lemma length_le_of_card_le [PadicIntegerRing R ℓ] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [Finite X] (h_card : Nat.card X ≤ Nat.card Y) :
    length R X ≤ length R Y := by
  have : Finite (ResidueField R) := PadicIntegerRing.finite_residueField ℓ
  have : Finite Y := Nat.finite_of_card_ne_zero (Nat.card_pos.trans_le h_card).ne'
  have hX : length R X < ⊤ := length_ne_top.lt_top
  have hY : length R Y < ⊤ := length_ne_top.lt_top
  -- both cardinalities are powers of the size of the residue field: compare the exponents
  have h_exponent : (length R X).lift hX ≤ (length R Y).lift hY := by
    rwa [card_eq_pow_length ℓ hX, card_eq_pow_length ℓ hY,
      pow_le_pow_iff_right₀ Finite.one_lt_card] at h_card
  simpa using h_exponent

/-- Let R be an ℓ-adic integer ring, and let X and Y be R-modules. If `Nat.card X` divides
`Nat.card Y`, then length X ≤ length Y. Since `Nat.card` is 0 for an infinite type, the hypothesis
says that either Y is infinite, or both modules are finite and #X divides #Y. -/
lemma length_le_of_card_dvd [PadicIntegerRing R ℓ] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (h_card : Nat.card X ∣ Nat.card Y) : length R X ≤ length R Y := by
  cases finite_or_infinite Y
  · have : Finite X := Nat.finite_of_card_ne_zero (ne_zero_of_dvd_ne_zero Nat.card_pos.ne' h_card)
    exact length_le_of_card_le ℓ (Nat.le_of_dvd Nat.card_pos h_card)
  · simp [length_eq_top_of_infinite ℓ (Y := Y)]

/-- Let R be an ℓ-adic integer ring (`New.PadicIntegerRing R ℓ`), and let X and Y be R-modules. If
#X divides #Y, or if #X ≤ #Y and X is finite, then length X ≤ length Y. Here `Nat.card` is 0 for an
infinite type, so finiteness of X is needed in the second case only. -/
lemma length_le_of_card_dvd_or_le [PadicIntegerRing R ℓ] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y]
    (h_card : Nat.card X ∣ Nat.card Y ∨ (Nat.card X ≤ Nat.card Y ∧ Finite X)) :
    length R X ≤ length R Y :=
  h_card.elim (length_le_of_card_dvd ℓ) fun ⟨h_le, _⟩ ↦ length_le_of_card_le ℓ h_le

/-- The coefficient rings at ℓ: the ℤ_ℓ-subalgebras of ℚ̄_ℓ that are the ring of integers of some
finite Galois extension K of ℚ_ℓ inside ℚ̄_ℓ, that is, the elements of K of norm at most 1. -/
abbrev CoeffRing : Type :=
  Set.range fun K : FiniteGaloisIntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) ↦
    ⟨NormedField.valuation.integer.toSubsemiring, fun r : ℤ_[ℓ] ↦
        (norm_algebraMap' (PadicAlgCl ℓ) (r : ℚ_[ℓ])).trans_le r.2⟩ ⊓
      K.toSubalgebra.restrictScalars ℤ_[ℓ]

variable {ℓ : ℕ} [ThePrime ℓ] {O : CoeffRing ℓ}

instance : FaithfulSMul ℤ_[ℓ] (PadicAlgCl ℓ) := .trans ℤ_[ℓ] ℚ_[ℓ] (PadicAlgCl ℓ)

/-- A coefficient ring O is cut out by some finite Galois extension K of ℚ_ℓ: its elements are
those of K of norm at most 1. -/
lemma CoeffRing.exists_mem_iff (O : CoeffRing ℓ) :
    ∃ K : FiniteGaloisIntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      ∀ x : PadicAlgCl ℓ, x ∈ O.val ↔ ‖x‖ ≤ 1 ∧ x ∈ K.toIntermediateField := by
  obtain ⟨_, K, rfl⟩ := O
  exact ⟨K, fun x ↦ Iff.rfl⟩

/-- The elements of a coefficient ring have norm at most 1. -/
@[simp]
lemma CoeffRing.norm_le_one (x : ↑O) : ‖x.val‖ ≤ 1 :=
  (CoeffRing.exists_mem_iff O).elim fun _ hK ↦ ((hK x.val).mp x.prop).1

/-- An element of ℚ̄_ℓ of norm at most 1 is integral over ℤ_ℓ. -/
lemma isIntegral_padicInt_of_norm_le_one {x : PadicAlgCl ℓ} (hx : ‖x‖ ≤ 1) :
    IsIntegral ℤ_[ℓ] x := by
  -- the norm of `x` is the spectral value of its minimal polynomial, so all coefficients have norm
  -- at most `1` and the polynomial lifts to a monic one over `ℤ_[ℓ]`, the unit ball of `ℚ_[ℓ]`
  have h_monic : (minpoly ℚ_[ℓ] x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have h_coeff : ∀ n : ℕ, ‖(minpoly ℚ_[ℓ] x).coeff n‖ ≤ 1 :=
    (spectralValue_le_one_iff h_monic).mp hx
  -- `ℤ_[ℓ]` is by definition the subring `subring ℓ` of `ℚ_[ℓ]`
  let p : Polynomial ℤ_[ℓ] := Polynomial.int (subring ℓ) (minpoly ℚ_[ℓ] x) h_coeff
  have hp_root : p.eval₂ (algebraMap ℤ_[ℓ] (PadicAlgCl ℓ)) x = 0 :=
    (Polynomial.int_eval₂_eq (subring ℓ) _ h_coeff x).trans (minpoly.aeval ℚ_[ℓ] x)
  exact ⟨p, (Polynomial.int_monic_iff _ _ h_coeff).mpr h_monic, hp_root⟩

/-- A coefficient ring O, the ring of integers of a finite Galois extension of ℚ_ℓ inside ℚ̄_ℓ, is
a finite ℤ_ℓ-module. -/
instance : Module.Finite ℤ_[ℓ] O := by
  -- `O` lies in the image of the integral closure of `ℤ_[ℓ]` in `K`, which is a finite module
  obtain ⟨K, hK⟩ := CoeffRing.exists_mem_iff O
  have h_fin : Module.Finite ℤ_[ℓ] (integralClosure ℤ_[ℓ] K.toIntermediateField) :=
    IsIntegralClosure.finite ℤ_[ℓ] ℚ_[ℓ] K (integralClosure ℤ_[ℓ] K)
  let incl : integralClosure ℤ_[ℓ] K.toIntermediateField →ₐ[ℤ_[ℓ]] PadicAlgCl ℓ :=
    (K.val.restrictScalars ℤ_[ℓ]).comp (integralClosure ℤ_[ℓ] K).val
  refine .of_fg ((h_fin.fg_top.map incl.toLinearMap).of_le (S := O.val.toSubmodule) fun x hx ↦ ?_)
  obtain ⟨h_norm, h_mem⟩ := (hK x).mp hx
  exact ⟨⟨⟨x, h_mem⟩, coe_isIntegral_iff.mp (isIntegral_padicInt_of_norm_le_one h_norm)⟩,
    trivial, rfl⟩

/-- In a coefficient ring, x divides y exactly when the norm of y is at most the norm of x. -/
lemma CoeffRing.dvd_iff_norm_le (x y : ↑O) : x ∣ y ↔ ‖y.val‖ ≤ ‖x.val‖ := by
  obtain ⟨K, hK⟩ := CoeffRing.exists_mem_iff O
  refine ⟨?_, fun h_le ↦ ?_⟩
  · rintro ⟨c, rfl⟩
    simp [mul_le_of_le_one_right, norm_le_one]
  · -- the quotient `y / x` has norm at most `1` and lies in the field `K`
    have h_mem (z : ↑O) : z.val ∈ K.toIntermediateField := ((hK z).mp z.prop).2
    have h_norm : ‖y.val / x.val‖ ≤ 1 := by simpa using div_le_one_of_le₀ h_le (norm_nonneg _)
    have h_quot : y.val / x.val ∈ O.val := (hK _).mpr ⟨h_norm, div_mem (h_mem y) (h_mem x)⟩
    have h_zero (hx : x.val = 0) : y.val = 0 := by simpa [hx] using h_le
    exact ⟨⟨y.val / x.val, h_quot⟩, Subtype.ext (mul_div_cancel_of_imp' h_zero).symm⟩

/-- A coefficient ring O is a discrete valuation ring (`New.DVR O`: a domain and a DVR): it is a
Noetherian valuation ring, and it is not a field. -/
instance : DVR O :=
  have : IsNoetherianRing O := .of_finite ℤ_[ℓ] O
  have h_total (x y : ↑O) : x ∣ y ∨ y ∣ x := by simp [CoeffRing.dvd_iff_norm_le, le_total]
  have : ValuationRing O := ValuationRing.iff_dvd_total.2 ⟨h_total⟩
  -- the maximal ideal of `O` lies over that of `ℤ_[ℓ]`, which is not zero
  { not_a_field' := Ideal.ne_bot_of_liesOver_of_ne_bot (not_a_field ℤ_[ℓ]) _ }

/-- For a finite set s in ℚ̄_ℓ, some coefficient ring (the ring of integers of a finite Galois
extension of ℚ_ℓ inside ℚ̄_ℓ) contains all elements of ℚ_ℓ(s) of norm at most 1. -/
lemma CoeffRing.exists_mem_of_mem_adjoin (s : Finset (PadicAlgCl ℓ)) :
    ∃ O : CoeffRing ℓ, ∀ x ∈ adjoin ℚ_[ℓ] s, ‖x‖ ≤ 1 → x ∈ O.val :=
  -- the integers of the Galois closure of `ℚ_[ℓ](s)`, which contains that field
  ⟨⟨_, .adjoin ℚ_[ℓ] s, rfl⟩, fun _ hx h_norm ↦ ⟨h_norm, le_normalClosure _ hx⟩⟩

/-- The action of ℤ_ℓ on ℚ̄_ℓ is continuous, ℤ_ℓ being the unit ball `PadicInt.subring ℓ` of ℚ_ℓ. -/
instance : ContinuousSMul ℤ_[ℓ] (PadicAlgCl ℓ) := (subring ℓ).continuousSMul (PadicAlgCl ℓ)

/-- A coefficient ring O is compact, being finite over the compact ring ℤ_ℓ. -/
instance : CompactSpace O := compactSpace ℤ_[ℓ] O

/-- The coefficient rings are directed by inclusion. -/
instance : IsDirectedOrder (CoeffRing ℓ) :=
  -- `CoeffRing ℓ` is the range of a monotone map on the lattice of finite Galois extensions
  have h_mono : Monotone fun K : FiniteGaloisIntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) ↦
      K.toSubalgebra.restrictScalars ℤ_[ℓ] := fun _ _ h_le ↦ h_le
  (monotone_const.inf h_mono).directed_le.directedOn_range.isDirectedOrder

/-- An element of ℚ̄_ℓ of norm at most 1 lies in all sufficiently large coefficient rings: the
rings of integers of finite Galois extensions of ℚ_ℓ inside ℚ̄_ℓ, ordered by inclusion. -/
lemma CoeffRing.eventually_mem {x : PadicAlgCl ℓ} (hx : ‖x‖ ≤ 1) :
    ∀ᶠ O : CoeffRing ℓ in Filter.atTop, x ∈ O.val := by
  obtain ⟨O, hO⟩ := exists_mem_of_mem_adjoin {x}
  exact (Filter.eventually_ge_atTop O).mono fun O' h_le ↦
    h_le (hO x (subset_adjoin _ _ (by simp)) hx)

end New
