import Surreal.Foundations.OmnificOrdinaryArithmetic
import Mathlib.Algebra.CharP.Lemmas

/-!
# Ideals with ordinary moduli and finite quotients

The full `odg:cor:charideals`: classification and uniqueness of proper
ideals containing a nonzero ordinary integer, their primality criterion,
and factorization of all homomorphisms to finite rings through the actual
integer constant-term map. Finite targets may lie in any universe.
-/

universe u v
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Every ideal containing a nonzero integer contains the purely infinite ideal. -/
theorem omnific_purelyInfinite_le_of_int_mem (I : Ideal OmnificInteger.{u})
    (m : ℤ) (hm : m ≠ 0) (hmem : omnificIntCast m ∈ I) : omnificPurelyInfiniteIdeal ≤ I := by
  intro x hx
  obtain ⟨y, rfl⟩ := omnific_int_dvd_of_purelyInfinite m hm x hx
  exact I.mul_mem_right y hmem

/-- Once the purely infinite ideal is contained, ideal membership depends only on the constant. -/
theorem omnific_mem_ideal_iff_constant (I : Ideal OmnificInteger.{u})
    (hI : omnificPurelyInfiniteIdeal ≤ I) (x : OmnificInteger.{u}) :
    x ∈ I ↔ omnificIntCast (omnificConstantCoeff x) ∈ I := by
  obtain ⟨j, hj, hx⟩ := omnific_constant_decomposition x
  have hjI := hI hj
  rw [hx, map_add, omnificConstantCoeff_intCast]
  change omnificConstantCoeff j = 0 at hj
  rw [hj, _root_.add_zero]
  exact I.add_mem_iff_left hjI

/-- Different nonnegative ordinary moduli generate different omnific ideals. -/
theorem omnific_nat_span_injective : Function.Injective
    (fun n : ℕ => (Ideal.span {omnificIntCast (n : ℤ)} : Ideal OmnificInteger.{u})) := by
  intro m n h
  have he := congrArg (Ideal.map omnificConstantCoeff) h
  simp only [Ideal.map_span, Set.image_singleton, omnificConstantCoeff_intCast] at he
  have hc := congrArg (fun J : Ideal ℤ => Nat.card (ℤ ⧸ J)) he
  simpa only [Int.card_ideal_quot] using hc

/-- Every proper ideal containing a nonzero ordinary integer has a unique ordinary modulus at least two. -/
theorem omnific_ideal_existsUnique_modulus (I : Ideal OmnificInteger.{u}) (hproper : I ≠ ⊤)
    (hordinary : ∃ m : ℤ, m ≠ 0 ∧ omnificIntCast m ∈ I) :
    ∃! n : ℕ, 2 ≤ n ∧ I = Ideal.span {omnificIntCast (n : ℤ)} := by
  obtain ⟨m, hm, hmem⟩ := hordinary
  have hPi := omnific_purelyInfinite_le_of_int_mem I m hm hmem
  let J : Ideal ℤ := I.comap omnificIntCast
  let n : ℕ := Ideal.absNorm J
  have hJ : Ideal.span ({(n : ℤ)} : Set ℤ) = J := Int.ideal_span_absNorm_eq_self J
  have hn : n ≠ 0 := by
    intro hz
    have hmJ : m ∈ J := hmem
    rw [← hJ, Ideal.mem_span_singleton, hz, Int.natCast_zero, zero_dvd_iff] at hmJ
    exact hm hmJ
  have hnmem : omnificIntCast (n : ℤ) ∈ I := by
    change (n : ℤ) ∈ J
    rw [← hJ]
    exact Ideal.mem_span_singleton_self _
  have hn1 : n ≠ 1 := by
    intro h
    have h1 : (1 : OmnificInteger.{u}) ∈ I := by simpa only [h, Int.natCast_one, map_one] using hnmem
    exact hproper ((Ideal.eq_top_iff_one I).mpr h1)
  have hEq : I = Ideal.span {omnificIntCast (n : ℤ)} := by
    ext x
    rw [omnific_mem_ideal_iff_constant I hPi x, Ideal.mem_span_singleton,
      omnific_int_dvd_iff _ (by exact_mod_cast hn)]
    change omnificConstantCoeff x ∈ J ↔ _
    rw [← hJ, Ideal.mem_span_singleton]
  refine ⟨n, ⟨by omega, hEq⟩, ?_⟩
  intro k hk
  exact omnific_nat_span_injective (hk.2.symm.trans hEq)

/-- The principal ideal of a nonzero ordinary natural modulus is prime exactly for prime moduli. -/
theorem omnific_nat_span_isPrime_iff (n : ℕ) (hn : n ≠ 0) :
    (Ideal.span {omnificIntCast (n : ℤ)} : Ideal OmnificInteger.{u}).IsPrime ↔ n.Prime := by
  constructor
  · intro hp
    letI := hp
    have hJ : (Ideal.span {omnificIntCast (n : ℤ)} : Ideal OmnificInteger.{u}).comap
        omnificIntCast = Ideal.span ({(n : ℤ)} : Set ℤ) := by
      ext z
      change omnificIntCast z ∈ Ideal.span {omnificIntCast (n : ℤ)} ↔ _
      rw [Ideal.mem_span_singleton, omnific_int_dvd_iff _ (by exact_mod_cast hn),
        omnificConstantCoeff_intCast, Ideal.mem_span_singleton]
    have hprime : (Ideal.span ({(n : ℤ)} : Set ℤ)).IsPrime := hJ ▸ inferInstance
    exact Nat.prime_iff_prime_int.mpr
      ((Ideal.span_singleton_prime (by exact_mod_cast hn)).mp hprime)
  · intro hp
    letI : Fact n.Prime := ⟨hp⟩
    exact (omnific_prime_span_isMaximal n).isPrime

/-- Every unital homomorphism sends ordinary omnific constants to the target's integer casts. -/
@[simp] theorem omnific_hom_intCast {R : Type v} [Ring R]
    (f : OmnificInteger.{u} →+* R) (n : ℤ) : f (omnificIntCast n) = (n : R) := by
  have h : f.comp omnificIntCast = Int.castRingHom R := Subsingleton.elim _ _
  exact RingHom.congr_fun h n

/-- Any homomorphism to a finite ring kills the purely infinite ideal, including trivial targets. -/
theorem omnific_finite_hom_kills_purelyInfinite {R : Type v} [Ring R] [Finite R]
    (f : OmnificInteger.{u} →+* R) (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) : f x = 0 := by
  have hn : (ringChar R : ℤ) ≠ 0 := by exact_mod_cast CharP.ringChar_ne_zero_of_finite R
  obtain ⟨y, rfl⟩ := omnific_int_dvd_of_purelyInfinite (ringChar R) hn x hx
  rw [map_mul, omnific_hom_intCast, Int.cast_natCast, CharP.cast_eq_zero R (ringChar R), zero_mul]

/-- Every finite-target homomorphism is exactly constant extraction followed by integer casting. -/
theorem omnific_finite_hom_eq_constant {R : Type v} [Ring R] [Finite R]
    (f : OmnificInteger.{u} →+* R) : f = (Int.castRingHom R).comp omnificConstantCoeff := by
  apply RingHom.ext
  intro x
  obtain ⟨j, hj, hx⟩ := omnific_constant_decomposition x
  change f x = (omnificConstantCoeff x : R)
  calc
    f x = f (omnificIntCast (omnificConstantCoeff x) + j) := congrArg f hx
    _ = (omnificConstantCoeff x : R) := by
      rw [map_add, omnific_hom_intCast, omnific_finite_hom_kills_purelyInfinite f j hj,
        _root_.add_zero]

/-- In particular the factorization through the constant term is unique. -/
theorem omnific_finite_hom_factors {R : Type v} [Ring R] [Finite R]
    (f : OmnificInteger.{u} →+* R) :
    ∃! g : ℤ →+* R, f = g.comp omnificConstantCoeff :=
  ⟨Int.castRingHom R, omnific_finite_hom_eq_constant f, fun _ _ => Subsingleton.elim _ _⟩

/-- Every nonzero finite quotient of the actual omnific ring is an ordinary residue ring. -/
theorem omnific_finite_quotient_classification (I : Ideal OmnificInteger.{u})
    [Finite (OmnificInteger.{u} ⧸ I)] [Nontrivial (OmnificInteger.{u} ⧸ I)] :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((OmnificInteger.{u} ⧸ I) ≃+* ZMod n) := by
  have hproper : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  have hm : (ringChar (OmnificInteger.{u} ⧸ I) : ℤ) ≠ 0 := by
    exact_mod_cast CharP.ringChar_ne_zero_of_finite (OmnificInteger.{u} ⧸ I)
  have hmem : omnificIntCast (ringChar (OmnificInteger.{u} ⧸ I) : ℤ) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, omnific_hom_intCast, Int.cast_natCast,
      CharP.cast_eq_zero (OmnificInteger.{u} ⧸ I) (ringChar (OmnificInteger.{u} ⧸ I))]
  obtain ⟨n, ⟨hn, hI⟩, _⟩ := omnific_ideal_existsUnique_modulus I hproper ⟨_, hm, hmem⟩
  refine ⟨n, hn, ⟨(Ideal.quotEquivOfEq hI).trans ?_⟩⟩
  exact (omnificQuotientIntEquiv (n : ℤ) (by exact_mod_cast (show n ≠ 0 by omega))).trans
    (Int.quotientSpanNatEquivZMod n)

end
end Surreal.Foundations.SignSequence
