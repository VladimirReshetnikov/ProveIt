import GRHArticle.SingularModuli.HeckeChunkedPrefixCertificate

/-!
# Reducing packed intermediate values modulo the prefix modulus

The final check only needs one residue. Reducing after every operation
keeps high-degree terms from increasing the intermediate sizes.
-/

namespace GRHArticle.SingularModuli
namespace IntegerPolynomialExpression

private def powMod (a m : ℤ) (k : ℕ) : ℤ :=
  if h : k = 0 then 1 % m else
    let b := powMod a m (k/2)
    let c := (b*b) % m
    if k % 2 = 0 then c else (c*a) % m
termination_by k
decreasing_by omega

private theorem mul_emod_left (a b m : ℤ) : (a % m * b) % m = (a*b) % m := by
  rw [Int.mul_emod (a % m) b, Int.emod_emod, ← Int.mul_emod]

private theorem pow_emod_left (a m : ℤ) (k : ℕ) : (a % m)^k % m = a^k % m := by
  induction k with
  | zero => simp only [pow_zero]
  | succ k ih =>
    rw [pow_succ, pow_succ, Int.mul_emod ((a%m)^k) (a%m), ih, Int.emod_emod, ← Int.mul_emod]

private theorem powMod_eq (a m : ℤ) (k : ℕ) : powMod a m k = a^k % m := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [powMod]
    split_ifs with hk he
    · subst k
      simp only [pow_zero]
    · dsimp only
      rw [ih _ (by omega), ← Int.mul_emod]
      rw [← pow_add, show k/2+k/2 = k by omega]
    · dsimp only
      rw [ih _ (by omega), ← Int.mul_emod, mul_emod_left,
        ← pow_add, ← pow_succ, show k/2+k/2+1 = k by omega]

/-- Evaluate packed digits with every arithmetic result reduced modulo `m`. -/
def packedEvalModular (w : ℕ) (m : ℤ) : IntegerPolynomialExpression → ℤ
  | .coefficients cs => (.coefficients cs : IntegerPolynomialExpression).packedEvalChunked w % m
  | .add a b => (a.packedEvalModular w m + b.packedEvalModular w m) % m
  | .sub a b => (a.packedEvalModular w m - b.packedEvalModular w m) % m
  | .mul a b => (a.packedEvalModular w m * b.packedEvalModular w m) % m
  | .pow a k => powMod (a.packedEvalModular w m) m k

theorem packedEvalModular_eq (w : ℕ) (m : ℤ) (e : IntegerPolynomialExpression) :
    e.packedEvalModular w m = e.packedEval w % m := by
  induction e with
  | coefficients cs => rw [packedEvalModular, packedEvalChunked_eq]
  | add a b ha hb => rw [packedEvalModular, ha, hb, ← Int.add_emod, packedEval]
  | sub a b ha hb => rw [packedEvalModular, ha, hb, ← Int.sub_emod, packedEval]
  | mul a b ha hb => rw [packedEvalModular, ha, hb, ← Int.mul_emod, packedEval]
  | pow a k ha =>
    rw [packedEvalModular, ha, powMod_eq, pow_emod_left, packedEval]

/-- Check a prefix while retaining only the residue needed by the certificate. -/
def checkZeroPrefixModular (e : IntegerPolynomialExpression) (n : ℕ) : Prop :=
  let w := e.magnitudeBound.log2+1
  e.packedEvalModular w ((1 <<< (w*n) : ℕ) : ℤ) = 0

instance (e : IntegerPolynomialExpression) (n : ℕ) : Decidable (e.checkZeroPrefixModular n) := by
  unfold checkZeroPrefixModular
  infer_instance

theorem checkZeroPrefixModular_iff (e : IntegerPolynomialExpression) (n : ℕ) :
    e.checkZeroPrefixModular n ↔ e.checkZeroPrefix n := by
  unfold checkZeroPrefixModular checkZeroPrefix
  dsimp only
  rw [packedEvalModular_eq]

end IntegerPolynomialExpression
end GRHArticle.SingularModuli
