import Diophantine.Paper1982.ShortQuadraticShift
import Diophantine.Paper1982.Index

/-!
# Normalization of the explicit quartic at admissible indices

The first term of the index polynomial gives `(2z)^5 ≤ u` when `ν ≥ 1`.
Thus the shifted (D9) residual cannot vanish at the zero witness tuple.
This establishes normalization of the explicit quartic without adding a
witness; its solvability correspondence with (D1)–(D37) remains separate.
-/

namespace Jones1982

/-- The index polynomial is strictly larger than its base. -/
theorem Index.two_mul_lt_u {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y : ℕ}
    (hI : Index ν P z u y) (hν : 1 ≤ ν) : 2 * z < u := by
  have hz := hI.two_le
  have hleZ : (2 * z : ℤ) ^ ((4 + 1) ^ (1 : ℕ)) ≤ (u : ℤ) := by
    rw [hI.hu, eval_lpoly]
    exact Finset.single_le_sum (f := fun i => (2 * z : ℤ) ^ ((4 + 1) ^ i))
      (fun _ _ => by positivity) (Finset.mem_Icc.2 ⟨le_rfl, hν⟩)
  have hle : (2 * z) ^ 5 ≤ u := by exact_mod_cast hleZ
  have hlt : 2 * z < (2 * z) ^ 2 := by nlinarith
  have hpow : (2 * z) ^ 2 ≤ (2 * z) ^ 5 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  exact hlt.trans_le (hpow.trans hle)

/-- At an admissible index, the shifted quartic is nonzero when all 58
witnesses are zero, for every integer input. -/
theorem ShortQuadratic.index_normalized {ν : ℕ}
    {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y : ℕ}
    (hI : Index ν P z u y) (hν : 1 ≤ ν) (x : ℤ) :
    MvPolynomial.eval (ShortQuadratic.zeroWitnessAssignment x)
      (ShortQuadratic.shiftedSumSquares z u y (L4 ν)) ≠ 0 :=
  ShortQuadratic.shiftedSumSquares_nonzero_at_zeroWitnesses z u y (L4 ν)
    (hI.two_mul_lt_u hν) x

end Jones1982
