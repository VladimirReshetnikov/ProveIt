import GowersSzemeredi.Proofs05MinimumPolynomialPartition
import GowersSzemeredi.Proofs05ModularApproximation

/-! Transfer the minimum-length real polynomial partition to the centered
modular norm and to the catalogue's `PolynomialOn` encoding.

For degree k and d simultaneous phases, the interval threshold retains
H^(p*(d+1)^(2*k)). Every index-progression cell has length at least H;
the centered distance between any two phase values in a cell is at most
(2*k/H)*N. The modulus need only be nonzero, and may be composite.

This theorem partitions the integer index interval. A proper modular
progression partition and the higher-dimensional box construction require
further transport. It is not a proof of the remaining Section 16 bounds.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open OAI.Erdos3 Polynomial
universe u

theorem centered_integer_difference_of_approximation {N : Nat} [NeZero N]
    (a b ma mb : Int) (z e : Real)
    (ha : |(a : Real) / N - ma - z| ≤ e)
    (hb : |(b : Real) / N - mb - z| ≤ e) :
    (centeredAbs ((a : ZMod N) - (b : ZMod N)) : Real) ≤ (2 * e) * N := by
  let E : Int := a - b - (ma - mb) * N
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcast : (E : ZMod N) = (a : ZMod N) - (b : ZMod N) := by simp [E]
  have hE : (E : Real) = N * (((a : Real) / N - ma - z) - ((b : Real) / N - mb - z)) := by
    dsimp [E]
    push_cast
    field_simp
    ring
  have hcenter : (centeredAbs (E : ZMod N) : Real) ≤ (E.natAbs : Real) := by
    exact_mod_cast recurrence_centeredAbs_intCast_le (N := N) E
  rw [hcast] at hcenter
  calc
    _ ≤ (E.natAbs : Real) := hcenter
    _ = |(E : Real)| := by simp
    _ = N * |((a : Real) / N - ma - z) - ((b : Real) / N - mb - z)| := by
      rw [hE, abs_mul, abs_of_pos hN]
    _ ≤ N * (|(a : Real) / N - ma - z| + |(b : Real) / N - mb - z|) :=
      mul_le_mul_of_nonneg_left (by simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le ((a : Real) / N - ma - z) 0 ((b : Real) / N - mb - z)) hN.le
    _ ≤ N * (e + e) := mul_le_mul_of_nonneg_left (add_le_add ha hb) hN.le
    _ = _ := by ring

theorem exists_minimum_modular_polynomial_partition (k : Nat) :
    ∃ (K : Real) (p : Nat), 2 ≤ K ∧ 0 < p ∧
      ∀ (N : Nat) [NeZero N] (ι : Type u) [Fintype ι]
        (P : ι → Polynomial Int), (∀ i, (P i).natDegree ≤ k) →
        ∀ (L H : Nat), 0 < H → K * ((Fintype.card ι : Real) + 1) ≤ H →
          H ^ (p * (Fintype.card ι + 1) ^ (2 * k)) ≤ L →
          ∃ Q : FiniteProgressionPartition L, (∀ i, H ≤ Q.length i) ∧
            ∀ i a b, a < Q.length i → b < Q.length i → ∀ j,
              (centeredAbs ((((P j).eval (Q.start i + Q.step i * a : Nat) : Int) : ZMod N) -
                (((P j).eval (Q.start i + Q.step i * b : Nat) : Int) : ZMod N)) : Real) ≤
                (2 * k / H) * N := by
  obtain ⟨K, p, hK, hp, hpartition⟩ := exists_minimum_polynomial_partition_bound.{u} k
  refine ⟨K, p, hK, hp, ?_⟩
  intro N _ ι _ P hP L H hH hscale hsize
  let R : ι → Polynomial Real := fun i => C ((N : Real)⁻¹) * (P i).map (Int.castRingHom Real)
  have hR (i : ι) : (R i).natDegree ≤ k :=
    (natDegree_C_mul_le _ _).trans ((natDegree_map_le).trans (hP i))
  have heval (i : ι) (n : Nat) : (R i).eval (n : Real) = (((P i).eval (n : Int) : Int) : Real) / N := by
    dsimp [R]
    rw [eval_mul, eval_C]
    have h := eval_map_apply (p := P i) (Int.castRingHom Real) (n : Int)
    change ((P i).map (Int.castRingHom Real)).eval ((n : Int) : Real) =
      (((P i).eval (n : Int) : Int) : Real) at h
    simpa only [Int.cast_natCast, div_eq_mul_inv, mul_comm] using
      congrArg (fun x : Real => (N : Real)⁻¹ * x) h
  obtain ⟨Q, z, m, hlength, herror⟩ := hpartition ι R hR L H hH hscale hsize
  refine ⟨Q, hlength, ?_⟩
  intro i a b ha hb j
  have ha' := herror i a ha j
  have hb' := herror i b hb j
  rw [heval] at ha' hb'
  have h := centered_integer_difference_of_approximation
    ((P j).eval (Q.start i + Q.step i * a : Nat))
    ((P j).eval (Q.start i + Q.step i * b : Nat))
    (m i a j) (m i b j) (z i j) ((k : Real) / H) ha' hb'
  convert h using 1
  ring

/-- Lift the catalogue's polynomial encoding to an integer polynomial,
without assuming the modulus prime. -/
theorem polynomialOn_integer_lift {N k : Nat} [NeZero N]
    (phi : ZMod N → ZMod N) (hphi : PolynomialOn k Finset.univ phi) :
    ∃ P : Polynomial Int, P.natDegree ≤ k ∧ ∀ n : Nat,
      ((P.eval (n : Int) : Int) : ZMod N) = phi (n : ZMod N) := by
  classical
  obtain ⟨c, hc⟩ := hphi
  let P := Polynomial.ofFn (k + 1) (fun j => (c j).valMinAbs)
  have hP : P.natDegree < k + 1 := Polynomial.ofFn_natDegree_lt (by omega) _
  refine ⟨P, by omega, ?_⟩
  intro n
  rw [hc _ (Finset.mem_univ _), Polynomial.eval_eq_sum_range' hP,
    ← Fin.sum_univ_eq_sum_range]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [show P.coeff (i : Nat) = (c i).valMinAbs from
    Polynomial.ofFn_coeff_eq_val_of_lt _ i.isLt]
  simp only [ZMod.coe_valMinAbs]

/-- Minimum-length simultaneous partitions for the modular polynomial
functions appearing in the Gowers catalogue. -/
theorem exists_minimum_polynomialOn_partition (k : Nat) :
    ∃ (K : Real) (p : Nat), 2 ≤ K ∧ 0 < p ∧
      ∀ (N : Nat) [NeZero N] (ι : Type u) [Fintype ι]
        (phi : ι → ZMod N → ZMod N), (∀ i, PolynomialOn k Finset.univ (phi i)) →
        ∀ (L H : Nat), 0 < H → K * ((Fintype.card ι : Real) + 1) ≤ H →
          H ^ (p * (Fintype.card ι + 1) ^ (2 * k)) ≤ L →
          ∃ Q : FiniteProgressionPartition L, (∀ i, H ≤ Q.length i) ∧
            ∀ i a b, a < Q.length i → b < Q.length i → ∀ j,
              (centeredAbs (phi j (Q.start i + Q.step i * a : Nat) -
                phi j (Q.start i + Q.step i * b : Nat)) : Real) ≤ (2 * k / H) * N := by
  obtain ⟨K, p, hK, hp, hpartition⟩ := exists_minimum_modular_polynomial_partition.{u} k
  refine ⟨K, p, hK, hp, ?_⟩
  intro N _ ι _ phi hphi L H hH hscale hsize
  choose P hP heval using (fun i => polynomialOn_integer_lift (phi i) (hphi i))
  obtain ⟨Q, hlength, hdiam⟩ := hpartition N ι P hP L H hH hscale hsize
  refine ⟨Q, hlength, ?_⟩
  intro i a b ha hb j
  simpa only [heval] using hdiam i a b ha hb j

end LeanProofs.GowersSzemeredi
