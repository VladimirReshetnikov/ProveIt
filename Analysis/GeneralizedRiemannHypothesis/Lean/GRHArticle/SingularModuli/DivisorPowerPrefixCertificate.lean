import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Certified prefixes of divisor-power sums

Each nonzero index is supplied as a product of pairwise coprime prime powers.
Checking the factorization once gives the divisor sums for every exponent.
-/

namespace GRHArticle.SingularModuli

open scoped BigOperators

namespace DivisorPowerPrefixCertificate

/-- The integer represented by a list of base-exponent pairs. -/
def witnessProduct : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p, e) :: ws => p^e * witnessProduct ws

/-- All bases are prime, and each power is coprime to the remaining product. -/
def WitnessValid : List (ℕ × ℕ) → Prop
  | [] => True
  | (p, e) :: ws => p.Prime ∧ (p^e).Coprime (witnessProduct ws) ∧ WitnessValid ws

instance (ws : List (ℕ × ℕ)) : Decidable (WitnessValid ws) :=
  match ws with
  | [] => isTrue trivial
  | (p, e) :: ws => by
    letI := instDecidableWitnessValid ws
    unfold WitnessValid
    infer_instance

/-- Compute the product of the geometric sums over the individual prime powers. -/
def witnessSigma (k : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p, e) :: ws =>
    (∑ i ∈ Finset.range (e+1), p^(i*k)) * witnessSigma k ws

theorem sigma_witnessProduct (k : ℕ) {ws : List (ℕ × ℕ)} (h : WitnessValid ws) :
    ArithmeticFunction.sigma k (witnessProduct ws) = witnessSigma k ws := by
  induction ws with
  | nil => exact ArithmeticFunction.sigma_one k
  | cons w ws ih =>
    rcases w with ⟨p,e⟩
    obtain ⟨hp, hc, hrest⟩ := h
    rw [witnessProduct, witnessSigma,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc,
      ArithmeticFunction.sigma_apply_prime_pow hp, ih hrest]

/-- A row at a positive index must give that index and valid factors.
Index zero is handled separately, since its divisor sum is zero. -/
def RowValid (i : ℕ) (ws : List (ℕ × ℕ)) : Prop :=
  i = 0 ∨ witnessProduct ws = i ∧ WitnessValid ws

instance (i : ℕ) (ws : List (ℕ × ℕ)) : Decidable (RowValid i ws) := by
  unfold RowValid
  infer_instance

/-- Check all rows by a linear pass through the table. -/
def check (rows : List (List (ℕ × ℕ))) : Bool :=
  rows.zipIdx.all fun x ↦ decide (RowValid x.2 x.1)

/-- The divisor-power coefficients generated from a checked table. -/
def coefficients (k : ℕ) (rows : List (List (ℕ × ℕ))) : List ℕ :=
  rows.mapIdx fun i ws ↦ if i = 0 then 0 else witnessSigma k ws

@[simp] theorem length_coefficients (k : ℕ) (rows : List (List (ℕ × ℕ))) :
    (coefficients k rows).length = rows.length := by
  simp [coefficients]

/-- The generated table gives the actual divisor sum at each stored index. -/
theorem getD_coefficients (k : ℕ) {rows : List (List (ℕ × ℕ))} (h : check rows = true)
    (i : ℕ) (hi : i < rows.length) :
    (coefficients k rows).getD i 0 = ArithmeticFunction.sigma k i := by
  have hj : i < rows.zipIdx.length := by simpa using hi
  have hm : rows.zipIdx[i] ∈ rows.zipIdx := List.getElem_mem hj
  have hrow := of_decide_eq_true (List.all_eq_true.mp h _ hm)
  rw [List.getElem_zipIdx] at hrow
  simp only [Nat.zero_add] at hrow
  rw [coefficients, List.getD_eq_getElem?_getD, List.getElem?_mapIdx,
    List.getElem?_eq_getElem hi]
  change (if i = 0 then 0 else witnessSigma k rows[i]) = _
  by_cases hiz : i = 0
  · simp [hiz]
  · obtain ⟨hri,hvalid⟩ := hrow.resolve_left hiz
    rw [if_neg hiz, ← sigma_witnessProduct k hvalid, hri]

end DivisorPowerPrefixCertificate

end GRHArticle.SingularModuli
