import IPRADerivations.Core.IntCertificates

/-!
# The eigenvectors of the Petersen graph in the Kneser model

Packet: `combinatorics/graph-ipra`, `tex/spectral.tex`, Theorem `spec:petersen`: "Index coordinates by the ten
two-subsets of `[5]` ... Let `C` be the `10`-by-`5` membership matrix, and `J` the all-ones matrix ... Counting
shared labels gives `A = J + I − C Cᵀ`, while counting pairs through one or two labels gives `Cᵀ C = 3I + J`.
The constant vector `1` has eigenvalue `3`. For `b` with `∑ b_i = 0`, the vector `C b` ... satisfies
`A (C b) = −2 C b`", and the vectors of sum zero in the kernel of `Cᵀ` have eigenvalue `1`.

The tables `mem` (membership) and `kadj` (disjointness of two pairs) are tables of numerals, and the vectors
have integer-term entries. As iPRA derivations:

* `kneser_gram`: `C Cᵀ + A = J + I`; `kneser_cogram`: `Cᵀ C = J + 3I`; `kneser_column`: every label is in four
  pairs; `kneser_degree`: `A 1 = 3 · 1`;
* `eigen_neg_two`, `petersen_neg_two`: `A (C b) = −2 C b` for every `b` with `∑ b_i = 0`;
* `eigen_one`, `petersen_one`: `A x = x` for every `x` with `∑ x_v = 0` and `Cᵀ x = 0`.

Not derived: the dimensions `4` and `5` of these two eigenspaces (the multiplicities), and the tree count.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.PetersenSpectrum

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The ten two-subsets of `{0, …, 4}`. -/
def pr (u : Fin 10) : ℕ × ℕ :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)].getD u.val (0, 0)

/-- The membership table `C`. -/
def mem (u : Fin 10) (i : Fin 5) : ℕ := if (pr u).1 = i.val ∨ (pr u).2 = i.val then 1 else 0

/-- The adjacency of the Kneser model: two pairs are adjacent when they are disjoint. -/
def kadj (u v : Fin 10) : ℕ :=
  if (pr u).1 ≠ (pr v).1 ∧ (pr u).1 ≠ (pr v).2 ∧ (pr u).2 ≠ (pr v).1 ∧ (pr u).2 ≠ (pr v).2 then 1 else 0

theorem gram_nat : ∀ u v : Fin 10, (∑ j, mem u j * mem v j) + kadj u v = 1 + (if u = v then 1 else 0) := by
  decide

theorem cogram_nat : ∀ i j : Fin 5, ∑ v, mem v i * mem v j = 1 + (if i = j then 3 else 0) := by decide

theorem column_nat : ∀ i : Fin 5, ∑ v, mem v i = 4 := by decide

theorem degree_nat : ∀ u : Fin 10, ∑ v, kadj u v = 3 := by decide

/-! ## The two eigenvalue computations, in any commutative ring -/

section Ring

variable {R : Type*} [CommRing R] {p q : ℕ}

/-- `A (C b) = −2 C b` when `A = J + I − C Cᵀ`, `Cᵀ C = J + 3I`, the columns of `C` sum to `4` and
`∑ b = 0`. -/
theorem eigen_neg_two (m : Fin p → Fin q → R) (a : Fin p → Fin p → R) (b : Fin q → R)
    (h1 : ∀ u v, a u v = 1 + (if u = v then 1 else 0) - ∑ j, m u j * m v j)
    (h2 : ∀ i j, ∑ v, m v i * m v j = 1 + (if i = j then 3 else 0))
    (h3 : ∀ i, ∑ v, m v i = 4) (hb : ∑ i, b i = 0) (u : Fin p) :
    ∑ v, a u v * ∑ i, m v i * b i = -2 * ∑ i, m u i * b i := by
  have hA : ∑ v, ∑ i, m v i * b i = 0 := by
    rw [Finset.sum_comm]
    have t : ∀ i, ∑ v, m v i * b i = 4 * b i := fun i => by rw [← Finset.sum_mul, h3]
    rw [Finset.sum_congr rfl fun i _ => t i, ← Finset.mul_sum, hb, MulZeroClass.mul_zero]
  have hB : ∀ j, ∑ v, m v j * ∑ i, m v i * b i = 3 * b j := fun j => by
    have e1 : ∀ v, m v j * ∑ i, m v i * b i = ∑ i, m v j * m v i * b i := fun v => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [Finset.sum_congr rfl fun v _ => e1 v, Finset.sum_comm]
    have e2 : ∀ i, ∑ v, m v j * m v i * b i = b i + (if j = i then 3 * b i else 0) := fun i => by
      rw [← Finset.sum_mul, h2]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun i _ => e2 i, Finset.sum_add_distrib, hb, Finset.sum_ite_eq,
      if_pos (Finset.mem_univ j), _root_.zero_add]
  have e4 : ∀ v, a u v * ∑ i, m v i * b i =
      (∑ i, m v i * b i) + (if u = v then ∑ i, m v i * b i else 0) -
        ∑ j, m u j * (m v j * ∑ i, m v i * b i) := fun v => by
    rw [h1 u v, sub_mul, Finset.sum_mul]
    congr 1
    · split_ifs <;> ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun v _ => e4 v, Finset.sum_sub_distrib, Finset.sum_add_distrib, hA,
    Finset.sum_ite_eq, if_pos (Finset.mem_univ u), Finset.sum_comm]
  have e5 : ∀ j, ∑ v, m u j * (m v j * ∑ i, m v i * b i) = 3 * (m u j * b j) := fun j => by
    rw [← Finset.mul_sum, hB j]
    ring
  rw [Finset.sum_congr rfl fun j _ => e5 j, ← Finset.mul_sum]
  ring

/-- `A x = x` when `A = J + I − C Cᵀ`, `∑ x = 0` and `Cᵀ x = 0`. -/
theorem eigen_one (m : Fin p → Fin q → R) (a : Fin p → Fin p → R) (x : Fin p → R)
    (h1 : ∀ u v, a u v = 1 + (if u = v then 1 else 0) - ∑ j, m u j * m v j)
    (hx : ∑ v, x v = 0) (hC : ∀ j, ∑ v, m v j * x v = 0) (u : Fin p) :
    ∑ v, a u v * x v = x u := by
  have e4 : ∀ v, a u v * x v = x v + (if u = v then x v else 0) - ∑ j, m u j * (m v j * x v) := fun v => by
    rw [h1 u v, sub_mul, Finset.sum_mul]
    congr 1
    · split_ifs <;> ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun v _ => e4 v, Finset.sum_sub_distrib, Finset.sum_add_distrib, hx,
    Finset.sum_ite_eq, if_pos (Finset.mem_univ u), Finset.sum_comm]
  have e5 : ∀ j, ∑ v, m u j * (m v j * x v) = 0 := fun j => by
    rw [← Finset.mul_sum, hC j, MulZeroClass.mul_zero]
  rw [Finset.sum_congr rfl fun j _ => e5 j, Finset.sum_const_zero]
  ring

end Ring

/-! ## The tables in `Groth (Q Γ)` -/

theorem gram_cast (u v : Fin 10) :
    ((kadj u v : ℕ) : Groth (Q Γ)) =
      1 + (if u = v then 1 else 0) - ∑ j, ((mem u j : ℕ) : Groth (Q Γ)) * ((mem v j : ℕ) : Groth (Q Γ)) := by
  have h := congrArg (Nat.cast : ℕ → Groth (Q Γ)) (gram_nat u v)
  push_cast at h
  linear_combination h

theorem cogram_cast (i j : Fin 5) :
    ∑ v, ((mem v i : ℕ) : Groth (Q Γ)) * ((mem v j : ℕ) : Groth (Q Γ)) = 1 + (if i = j then 3 else 0) := by
  have h := congrArg (Nat.cast : ℕ → Groth (Q Γ)) (cogram_nat i j)
  push_cast at h
  exact h

theorem column_cast (i : Fin 5) : ∑ v, ((mem v i : ℕ) : Groth (Q Γ)) = 4 := by
  have h := congrArg (Nat.cast : ℕ → Groth (Q Γ)) (column_nat i)
  push_cast at h
  exact h

/-! ## The derivations -/

/-- `C Cᵀ + A = J + I`. -/
theorem kneser_gram (u v : Fin 10) :
    Γ ⊢[PRAAx] ZT.eq
      ((ZT.sumFin fun j => (ZT.natLit (mem u j) : ZT n) * ZT.natLit (mem v j)) + ZT.natLit (kadj u v))
      (ZT.natLit 1 + ZT.natLit (if u = v then 1 else 0)) := by
  apply ZT.derive
  simp only [ZT.toZ_sumFin, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_one]
  have h := gram_cast (Γ := Γ) u v
  push_cast
  linear_combination h

/-- `Cᵀ C = J + 3I`. -/
theorem kneser_cogram (i j : Fin 5) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun v => (ZT.natLit (mem v i) : ZT n) * ZT.natLit (mem v j))
      (ZT.natLit 1 + ZT.natLit (if i = j then 3 else 0)) := by
  apply ZT.derive
  simp only [ZT.toZ_sumFin, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_one]
  have h := cogram_cast (Γ := Γ) i j
  push_cast
  exact h

/-- Every label is in four pairs. -/
theorem kneser_column (i : Fin 5) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun v => (ZT.natLit (mem v i) : ZT n)) (ZT.natLit 4) := by
  apply ZT.derive
  simp only [ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_ofNat]
  exact column_cast i

/-- `A 1 = 3 · 1`: the constant vector has eigenvalue `3`. -/
theorem kneser_degree (u : Fin 10) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun v => (ZT.natLit (kadj u v) : ZT n)) (ZT.natLit 3) := by
  apply ZT.derive
  simp only [ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_ofNat]
  have h := congrArg (Nat.cast : ℕ → Groth (Q Γ)) (degree_nat u)
  push_cast at h
  exact h

/-- `A (C b) = −2 C b` for `∑ b_i = 0`. -/
theorem petersen_neg_two (b : Fin 5 → ZT n) (hb : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin b) (ZT.natLit 0))
    (u : Fin 10) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.sumFin fun v => ZT.natLit (kadj u v) * ZT.sumFin fun i => ZT.natLit (mem v i) * b i)
      (-(ZT.natLit 2) * ZT.sumFin fun i => ZT.natLit (mem u i) * b i) := by
  have eb := ZT.toZ_eq hb
  simp only [ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_zero] at eb
  apply ZT.derive
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit, Nat.cast_ofNat]
  exact eigen_neg_two (fun v i => ((mem v i : ℕ) : Groth (Q Γ))) (fun u v => ((kadj u v : ℕ) : Groth (Q Γ)))
    (fun i => ZT.toZ Γ (b i)) gram_cast cogram_cast column_cast eb u

/-- `A x = x` for `∑ x_v = 0` and `Cᵀ x = 0`. -/
theorem petersen_one (x : Fin 10 → ZT n) (hx : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin x) (ZT.natLit 0))
    (hC : ∀ j, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun v => ZT.natLit (mem v j) * x v) (ZT.natLit 0)) (u : Fin 10) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun v => ZT.natLit (kadj u v) * x v) (x u) := by
  have ex := ZT.toZ_eq hx
  simp only [ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_zero] at ex
  have eC : ∀ j, ∑ v, ((mem v j : ℕ) : Groth (Q Γ)) * ZT.toZ Γ (x v) = 0 := fun j => by
    have e := ZT.toZ_eq (hC j)
    simpa only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_zero] using e
  apply ZT.derive
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit]
  exact eigen_one (fun v i => ((mem v i : ℕ) : Groth (Q Γ))) (fun u v => ((kadj u v : ℕ) : Groth (Q Γ)))
    (fun v => ZT.toZ Γ (x v)) gram_cast ex eC u

end LeanProofs.IPRA.Combinatorics.PetersenSpectrum
