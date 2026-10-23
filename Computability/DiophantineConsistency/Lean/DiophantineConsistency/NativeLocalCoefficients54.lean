import DiophantineConsistency.NativeModesData54

/-!
# Compact54 local coefficient recipes implement the checked clause

These are the actual positive selector, receiver and copied-label recipes.
The later current/spatial convolution and clean-band arguments are separate.
-/

namespace DiophantineConsistency.NativeLocalCoefficients54

open NativeClause54 NativeClauseModes54 NativeModesData54

def selectorCoefficient (kind : Kind) (t : Label) : ℕ :=
  1 + 255 * 2 ^ 9 * (1 - rightFlag kind) + 255 * 2 ^ 18 * (1 - leftFlag kind) +
    2 ^ 27 * (1 - rightFlag kind - leftFlag kind) + 2 ^ 29 * (1 + encode t)

def auxiliaryWord (QR QL u : ℕ) : ℕ :=
  2 ^ 9 * QR + 2 ^ 18 * QL + 2 ^ 27 * u + 2 ^ 29 * auxiliary QR QL u

def copiedWord (Z y A1 A2 : ℕ) : ℕ := 2 ^ 29 * (Z + labelBase * (y + A1 + A2))

/-- Exact recipe identity for an arbitrary number of identical selected
modes. It requires no Boolean or carry-free premise. -/
theorem coefficient_word_eq (kind : Kind) (t : Label) (n QR QL u Z y A1 A2 : ℕ) :
    n * selectorCoefficient kind t + auxiliaryWord QR QL u + copiedWord Z y A1 A2 =
      localClause kind t n QR QL u Z y A1 A2 := by
  cases kind <;>
    simp only [selectorCoefficient,auxiliaryWord,copiedWord,localClause,
      rightFlag,leftFlag,rightGate,leftGate,commonGate,pack,payload,
      Nat.sub_zero,Nat.sub_self,Nat.mul_zero,Nat.mul_one,Nat.zero_mul,Nat.one_mul,
      Nat.add_zero,Nat.zero_add] <;>
    ring

/-- Instantiation at every one of the actual457 compact selector modes.
The finite table supplies all ordinary-label ranges and both receiver bases. -/
theorem literal_mode_clause_iff (i : Fin 457) {n QR QL u Z y A1 A2 : ℕ}
    (hn : n < 512) (hQR : QR < 256) (hQL : QL < 256) (hu : u ≤ 1)
    (hZ : Z < labelBase) (hZbit : Z % 2 = y) (hy : y ≤ 1) (hA1 : A1 ≤ 1) (hA2 : A2 ≤ 1) :
    (n * selectorCoefficient (mode i).2 (mode i).1 + auxiliaryWord QR QL u + copiedWord Z y A1 A2)
      &&& clauseMask = 0 ↔
      (n = 0 ∧ QR = 0 ∧ QL = 0 ∧ u = 0 ∧ Z = 0 ∧ y = 0 ∧ A1 = 0 ∧ A2 = 0) ∨
      (n = 1 ∧ Allowed (mode i).2 QR QL u ∧ y = 1 ∧ A1 = 1 ∧ A2 = 1 ∧
        encode (expanded (mode i).1 QR QL u) + Z = labelBase - 1) := by
  rw [coefficient_word_eq]
  exact local_clause_iff (mode_valid i) hn hQR hQL hu hZ hZbit hy hA1 hA2

end DiophantineConsistency.NativeLocalCoefficients54
