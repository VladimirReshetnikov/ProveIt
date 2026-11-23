import FermatIPRA.Program

/-!
# Exact remaining mathematical obligations and conditional assembly

STATUS: Uncompiled Lean outline. `ArithmeticContracts` is an explicit argument
to each assembly theorem, not an asserted global instance. No implementation of
these contracts is supplied. In particular the final theorem is conditional; it
is NOT a completed Lean proof of Fermat's theorem or an object-level iPRA proof.

The human-readable report proves the mathematical contracts and explains their
compilation to quantifier-free iPRA derivations. `README.md` identifies the
remaining formalization work and the relevant pinned ProveIt interfaces.
-/

namespace FermatIPRA

structure ArithmeticContracts : Prop where
  /-- Finite inverse pairing and half-factorial splitting. -/
  wilsonRoot : ∀ p, Prime p → p % 4 = 1 →
    (root p * root p + 1) % p = 0

  /-- Ordinary square-root bounds, with strictness because a prime is nonsquare. -/
  squareBounds : ∀ p, Prime p → SquareBounds p

  /-- Bounded finite pigeonhole plus correctness of the explicit pair search. -/
  collisionFound : ∀ p t, 2 ≤ p →
    Collision p t (collisionIndices p t).1 (collisionIndices p t).2

  /-- Distinct grid points give a positive norm smaller than `2*p`. -/
  differenceBounds : ∀ p t i j,
    SquareBounds p → Collision p t i j →
    0 < differenceNorm p i j ∧ differenceNorm p i j < 2 * p

  /-- Equal labels and `t^2 = -1 (mod p)` make the norm divisible by `p`. -/
  differenceDivisible : ∀ p t i j,
    0 < p → (t * t + 1) % p = 0 → Collision p t i j →
    differenceNorm p i j % p = 0

  /-- A positive multiple of `p` lying below `2*p` is exactly `p`. -/
  shortMultiple : ∀ p n,
    0 < p → 0 < n → n < 2 * p → n % p = 0 → n = p

  /-- Modulo-four square calculation and the special even prime. -/
  converse : ∀ p a b,
    Prime p → Represents p a b → p = 2 ∨ p % 4 = 1

theorem prime_ge_two {p : Nat} (hp : Prime p) : 2 ≤ p := by
  by_cases h : 2 ≤ p
  · exact h
  · simp [Prime, primeB, h] at hp

theorem gridWitness_correct_from_contracts
    (C : ArithmeticContracts) {p : Nat}
    (hp : Prime p) (hmod : p % 4 = 1) :
    Represents p (gridWitness p).1 (gridWitness p).2 := by
  let t := root p
  let ij := collisionIndices p t
  have hp2 : 2 ≤ p := prime_ge_two hp
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide : 0 < 2) hp2
  have hc : Collision p t ij.1 ij.2 := C.collisionFound p t hp2
  have hb := C.differenceBounds p t ij.1 ij.2 (C.squareBounds p hp) hc
  have hd := C.differenceDivisible p t ij.1 ij.2 hp0
    (C.wilsonRoot p hp hmod) hc
  have hn := C.shortMultiple p (differenceNorm p ij.1 ij.2) hp0 hb.1 hb.2 hd
  exact hn

theorem witness_correct_from_contracts
    (C : ArithmeticContracts) {p : Nat}
    (hp : Prime p) (hform : p = 2 ∨ p % 4 = 1) :
    Represents p (witness p).1 (witness p).2 := by
  by_cases hp2 : p = 2
  · subst p
    decide
  · have hm : p % 4 = 1 := hform.resolve_left hp2
    simpa [witness, hp2] using gridWitness_correct_from_contracts C hp hm

theorem fermat_from_contracts
    (C : ArithmeticContracts) {p : Nat} (hp : Prime p) :
    (∃ a b : Nat, Represents p a b) ↔ (p = 2 ∨ p % 4 = 1) := by
  constructor
  · intro h
    rcases h with ⟨a, b, hab⟩
    exact C.converse p a b hp hab
  · intro hform
    exact ⟨(witness p).1, (witness p).2,
      witness_correct_from_contracts C hp hform⟩

end FermatIPRA
