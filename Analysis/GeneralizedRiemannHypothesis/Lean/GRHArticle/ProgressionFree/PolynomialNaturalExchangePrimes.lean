import GRHArticle.ProgressionFree.PolynomialNaturalExchangeNumerics
import GRHArticle.ProgressionFree.PolynomialIrreducibleDegrees
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# The explicit monic primes for the natural-density exchange

The binary and ternary cases use the displayed quadratic and cubic
polynomials. Their irreducibility follows by exhausting the roots in
fields of the stated cardinalities. Larger fields use all monic linears.
-/

namespace GRHArticle.ProgressionFree

open Polynomial
open scoped Classical

variable {F : Type*} [Field F]

private theorem natDegree_X_add_one : (X+1 : F[X]).natDegree = 1 := by
  simpa only [map_one] using natDegree_X_add_C (1:F)

private theorem monic_X_add_one : (X+1 : F[X]).Monic := by
  simpa only [map_one] using monic_X_add_C (1:F)

private theorem irreducible_X_add_one : Irreducible (X+1 : F[X]) := by
  simpa only [map_neg, map_one, sub_neg_eq_add] using irreducible_X_sub_C (-1:F)

private theorem natDegree_X_pow_add_X_add_one (n : ℕ) (h : 1 < n) :
    (X^n+(X+1) : F[X]).natDegree = n := by
  rw [natDegree_add_eq_left_of_natDegree_lt (by rwa [natDegree_X_add_one, natDegree_X_pow]),
    natDegree_X_pow]

private theorem monic_X_pow_add_X_add_one (n : ℕ) (h : 1 < n) :
    (X^n+(X+1) : F[X]).Monic := by
  apply monic_X_pow_add
  refine degree_le_natDegree.trans_lt ?_
  rw [natDegree_X_add_one, Nat.cast_lt]
  exact h

private theorem natDegree_X_sq_add_one : (X^2+1 : F[X]).natDegree = 2 := by
  simpa only [map_one] using (natDegree_X_pow_add_C (n := 2) (r := (1:F)))

private theorem monic_X_sq_add_one : (X^2+1 : F[X]).Monic := by
  simpa only [map_one] using monic_X_pow_add_C (1:F) (n := 2) (by decide)

variable [Fintype F]

private theorem binaryField_eq_zero_or_one (hq : Fintype.card F = 2) (x : F) :
    x = 0 ∨ x = 1 := by
  have h : ({0,1} : Finset F) = Finset.univ :=
    (Finset.card_eq_iff_eq_univ _).mp (by simp [hq, zero_ne_one])
  have hx : x ∈ ({0,1} : Finset F) := h ▸ Finset.mem_univ x
  simpa using hx

private theorem irreducible_binary_X_pow_add_X_add_one (hq : Fintype.card F = 2)
    (n : ℕ) (hl : 1 < n) (hr : n ≤ 3) : Irreducible (X^n+(X+1) : F[X]) := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : CharP F 2 := charP_of_card_eq_prime hq
  have h₂ : (1:F)+1 = 0 := by simpa only [Nat.cast_two, one_add_one_eq_two] using CharP.cast_eq_zero F 2
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_X_pow_add_X_add_one n hl]
    exact Finset.mem_Icc.mpr ⟨hl.le, hr⟩
  · intro x hx
    rcases binaryField_eq_zero_or_one hq x with rfl | rfl
    · simp [IsRoot, zero_pow (by omega : n ≠ 0)] at hx
    · simp [IsRoot, h₂] at hx

private theorem ternaryField_two_ne_zero (hq : Fintype.card F = 3) : (2:F) ≠ 0 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : CharP F 3 := charP_of_card_eq_prime hq
  intro he
  exact (by decide : ¬(3:ℕ) ∣ 2) ((CharP.cast_eq_zero_iff F 3 2).mp (by simpa using he))

private theorem ternaryField_eq_zero_or_one_or_neg_one (hq : Fintype.card F = 3) (x : F) :
    x = 0 ∨ x = 1 ∨ x = -1 := by
  have hn : (1:F) ≠ -1 := by
    intro he
    apply ternaryField_two_ne_zero hq
    calc
      (2:F) = 1+1 := by norm_num
      _ = (-1:F)+1 := congrArg (· + (1:F)) he
      _ = 0 := neg_add_cancel _
  have h0 : (0:F) ≠ -1 := by simp
  have h : ({0,1,-1} : Finset F) = Finset.univ :=
    (Finset.card_eq_iff_eq_univ _).mp (by simp [hq, zero_ne_one, hn, h0])
  have hx : x ∈ ({0,1,-1} : Finset F) := h ▸ Finset.mem_univ x
  simpa using hx

private theorem irreducible_ternary_X_sq_add_one (hq : Fintype.card F = 3) :
    Irreducible (X^2+1 : F[X]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_X_sq_add_one]
    decide
  · intro x hx
    have h₂ := ternaryField_two_ne_zero hq
    rcases ternaryField_eq_zero_or_one_or_neg_one hq x with rfl | rfl | rfl
    · norm_num [IsRoot] at hx
    · exact h₂ (by simpa [IsRoot, one_add_one_eq_two] using hx)
    · exact h₂ (by simpa [IsRoot, one_add_one_eq_two] using hx)

private noncomputable def binaryExchangePrimeList : List F[X] :=
  [X, X+1, X^2+(X+1), X^3+(X+1)]

omit [Fintype F] in
private theorem binaryExchangePrimeList_nodup : (binaryExchangePrimeList (F := F)).Nodup := by
  have hq : (X^2+(X+1) : F[X]).natDegree = 2 := natDegree_X_pow_add_X_add_one 2 (by decide)
  have hc : (X^3+(X+1) : F[X]).natDegree = 3 := natDegree_X_pow_add_X_add_one 3 (by decide)
  have hne {p r : F[X]} (h : p.natDegree ≠ r.natDegree) : p ≠ r :=
    fun he ↦ h (congrArg natDegree he)
  have hXq : (X : F[X]) ≠ X^2+(X+1) := hne (by simp [hq])
  have hXc : (X : F[X]) ≠ X^3+(X+1) := hne (by simp [hc])
  have hLq : (X+1 : F[X]) ≠ X^2+(X+1) := hne (by simp [hq,natDegree_X_add_one])
  have hLc : (X+1 : F[X]) ≠ X^3+(X+1) := hne (by simp [hc,natDegree_X_add_one])
  have hqc : (X^2+(X+1) : F[X]) ≠ X^3+(X+1) := hne (by simp [hq,hc])
  simp [binaryExchangePrimeList, hXq,hXc,hLq,hLc,hqc]

/-- The finite set of primes prescribed in the article. -/
noncomputable def naturalExchangeSelectedPrimes (F : Type*) [Field F] [Fintype F] : Finset F[X] :=
  if Fintype.card F = 2 then (binaryExchangePrimeList (F := F)).toFinset
  else if Fintype.card F = 3 then insert (X^2+1) (polynomialSmoothPrimes F 1)
  else polynomialSmoothPrimes F 1

theorem naturalExchangeSelectedPrimes_eq_binary (hq : Fintype.card F = 2) :
    naturalExchangeSelectedPrimes F = {X, X+1, X^2+X+1, X^3+X+1} := by
  simp [naturalExchangeSelectedPrimes, hq, binaryExchangePrimeList, add_assoc]

theorem naturalExchangeSelectedPrimes_eq_ternary (hq : Fintype.card F = 3) :
    naturalExchangeSelectedPrimes F = insert (X^2+1) (polynomialSmoothPrimes F 1) := by
  simp [naturalExchangeSelectedPrimes, hq]

theorem naturalExchangeSelectedPrimes_eq_linears (hq : 4 ≤ Fintype.card F) :
    naturalExchangeSelectedPrimes F = polynomialSmoothPrimes F 1 := by
  simp [naturalExchangeSelectedPrimes, show Fintype.card F ≠ 2 by omega,
    show Fintype.card F ≠ 3 by omega]

theorem natDegree_eq_one_of_mem_monicLinears {p : F[X]} (hp : p ∈ polynomialSmoothPrimes F 1) :
    p.natDegree = 1 := by
  have hp' := mem_polynomialSmoothPrimes.mp hp
  exact le_antisymm hp'.2.2 hp'.2.1.natDegree_pos

theorem mem_monicLinears_iff {p : F[X]} :
    p ∈ polynomialSmoothPrimes F 1 ↔ p.Monic ∧ p.natDegree = 1 := by
  constructor
  · intro hp
    exact ⟨(mem_polynomialSmoothPrimes.mp hp).1, natDegree_eq_one_of_mem_monicLinears hp⟩
  · rintro ⟨hm, hd⟩
    have hd' : p.degree = 1 := by rw [degree_eq_natDegree hm.ne_zero, hd]; rfl
    exact mem_polynomialSmoothPrimes.mpr ⟨hm, (Monic.prime_of_degree_eq_one hd' hm).irreducible, hd.le⟩

theorem card_monicLinears (F : Type*) [Field F] [Fintype F] :
    (polynomialSmoothPrimes F 1).card = Fintype.card F := by
  have h := sum_divisors_mul_polynomialIrreducibleCount (F := F) 1 (by decide)
  have he : (polynomialSmoothPrimes F 1).filter (fun p ↦ p.natDegree = 1) =
      polynomialSmoothPrimes F 1 :=
    Finset.filter_eq_self.mpr fun _ hp ↦ natDegree_eq_one_of_mem_monicLinears hp
  simpa [polynomialIrreducibleCount, he, Nat.divisors_one] using h

private theorem quadratic_notMem_monicLinears : (X^2+1 : F[X]) ∉ polynomialSmoothPrimes F 1 := by
  intro h
  have he := natDegree_eq_one_of_mem_monicLinears h
  rw [natDegree_X_sq_add_one] at he
  omega

/-- Every prescribed polynomial is a monic irreducible over the actual field. -/
theorem mem_naturalExchangeSelectedPrimes {p : F[X]} (hp : p ∈ naturalExchangeSelectedPrimes F) :
    p.Monic ∧ Irreducible p := by
  unfold naturalExchangeSelectedPrimes at hp
  split at hp
  · rename_i hq
    have hmem := List.mem_toFinset.mp hp
    simp only [binaryExchangePrimeList, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact ⟨monic_X,irreducible_X⟩
    · exact ⟨monic_X_add_one,irreducible_X_add_one⟩
    · exact ⟨monic_X_pow_add_X_add_one 2 (by decide),
        irreducible_binary_X_pow_add_X_add_one hq 2 (by decide) (by decide)⟩
    · exact ⟨monic_X_pow_add_X_add_one 3 (by decide),
        irreducible_binary_X_pow_add_X_add_one hq 3 (by decide) (by decide)⟩
  · split at hp
    · rename_i hq
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact ⟨monic_X_sq_add_one, irreducible_ternary_X_sq_add_one hq⟩
      · have h := mem_polynomialSmoothPrimes.mp hp
        exact ⟨h.1,h.2.1⟩
    · have h := mem_polynomialSmoothPrimes.mp hp
      exact ⟨h.1,h.2.1⟩

/-- The exact cardinality of the prescribed family. -/
theorem card_naturalExchangeSelectedPrimes :
    (naturalExchangeSelectedPrimes F).card = max (Fintype.card F) 4 := by
  unfold naturalExchangeSelectedPrimes
  split
  · rename_i hq
    rw [List.toFinset_card_of_nodup (binaryExchangePrimeList_nodup (F := F)), hq]
    rfl
  · rename_i h₂
    split
    · rename_i hq
      rw [Finset.card_insert_of_notMem quadratic_notMem_monicLinears, card_monicLinears, hq]
      decide
    · rename_i h₃
      rw [card_monicLinears, max_eq_left]
      have hq : 1 < Fintype.card F := Fintype.one_lt_card
      omega

private theorem monicLinears_degreeList :
    (polynomialSmoothPrimes F 1).toList.map natDegree = List.replicate (Fintype.card F) 1 := by
  have h : (polynomialSmoothPrimes F 1).toList.map natDegree =
      List.replicate ((polynomialSmoothPrimes F 1).toList.map natDegree).length 1 := by
    apply List.eq_replicate_length.mpr
    intro d hd
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hd
    exact natDegree_eq_one_of_mem_monicLinears (Finset.mem_toList.mp hp)
  simpa [Finset.length_toList, card_monicLinears] using h

/-- The binary degree multiset is exactly `[1,1,2,3]`. -/
theorem naturalExchangeSelectedPrimes_degrees_binary (hq : Fintype.card F = 2) :
    ((naturalExchangeSelectedPrimes F).toList.map natDegree).Perm [1,1,2,3] := by
  simp only [naturalExchangeSelectedPrimes, if_pos hq]
  have h := (List.toFinset_toList (binaryExchangePrimeList_nodup (F := F))).map natDegree
  simpa [binaryExchangePrimeList, natDegree_X_add_one, natDegree_X_pow_add_X_add_one] using h

/-- The ternary degree multiset is exactly `[1,1,1,2]`. -/
theorem naturalExchangeSelectedPrimes_degrees_ternary (hq : Fintype.card F = 3) :
    ((naturalExchangeSelectedPrimes F).toList.map natDegree).Perm [1,1,1,2] := by
  have h₂ : Fintype.card F ≠ 2 := by omega
  simp only [naturalExchangeSelectedPrimes, if_neg h₂, if_pos hq]
  have h := (Finset.toList_insert (quadratic_notMem_monicLinears (F := F))).map natDegree
  have h' : ((insert (X^2+1 : F[X]) (polynomialSmoothPrimes F 1)).toList.map natDegree).Perm
      [2,1,1,1] := by simpa [natDegree_X_sq_add_one, monicLinears_degreeList, hq] using h
  exact h'.trans (by decide +kernel)

/-- At size at least four the prescribed list contains exactly `q` linears. -/
theorem naturalExchangeSelectedPrimes_degrees_linear (hq : 4 ≤ Fintype.card F) :
    (naturalExchangeSelectedPrimes F).toList.map natDegree = List.replicate (Fintype.card F) 1 := by
  rw [naturalExchangeSelectedPrimes_eq_linears hq]
  exact monicLinears_degreeList

/-- The weight list of the prescribed prime set, in its arbitrary finset order. -/
noncomputable def naturalExchangeSelectedWeights (F : Type*) [Field F] [Fintype F] : List ℝ :=
  (naturalExchangeSelectedPrimes F).toList.map (fun p ↦ (Fintype.card F : ℝ)⁻¹^p.natDegree)

theorem naturalExchangeSelectedWeights_mem_Ioo {w : ℝ} (hw : w ∈ naturalExchangeSelectedWeights F) :
    w ∈ Set.Ioo 0 1 := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hw
  have hp' := (mem_naturalExchangeSelectedPrimes (Finset.mem_toList.mp hp)).2.natDegree_pos
  have hq : 1 < (Fintype.card F : ℝ) := by exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F)
  have hz : 0 < (Fintype.card F : ℝ)⁻¹ := inv_pos.mpr (zero_lt_one.trans hq)
  exact ⟨pow_pos hz _, pow_lt_one₀ hz.le (inv_lt_one_of_one_lt₀ hq) hp'.ne'⟩

theorem naturalExchangeSelectedWeights_binary (hq : Fintype.card F = 2) :
    (naturalExchangeSelectedWeights F).Perm [1/2,1/2,1/4,1/8] := by
  have h := (naturalExchangeSelectedPrimes_degrees_binary hq).map
    (fun d ↦ (Fintype.card F : ℝ)⁻¹^d)
  norm_num [naturalExchangeSelectedWeights, List.map_map, Function.comp_def, hq] at h ⊢
  exact h

theorem naturalExchangeSelectedWeights_ternary (hq : Fintype.card F = 3) :
    (naturalExchangeSelectedWeights F).Perm [1/3,1/3,1/3,1/9] := by
  have h := (naturalExchangeSelectedPrimes_degrees_ternary hq).map
    (fun d ↦ (Fintype.card F : ℝ)⁻¹^d)
  norm_num [naturalExchangeSelectedWeights, List.map_map, Function.comp_def, hq] at h ⊢
  exact h

theorem naturalExchangeSelectedWeights_linear (hq : 4 ≤ Fintype.card F) :
    naturalExchangeSelectedWeights F = List.replicate (Fintype.card F) (1/(Fintype.card F:ℝ)) := by
  have h := congrArg (List.map (fun d ↦ (Fintype.card F : ℝ)⁻¹^d))
    (naturalExchangeSelectedPrimes_degrees_linear hq)
  simpa [naturalExchangeSelectedWeights, List.map_map, Function.comp_def, one_div] using h

theorem naturalExchangeSelectedWeights_four (hq : Fintype.card F = 4) :
    naturalExchangeSelectedWeights F = [1/4,1/4,1/4,1/4] := by
  rw [naturalExchangeSelectedWeights_linear (by omega), hq]
  rfl

theorem naturalExchangeBracket_perm {u v : List ℝ} (h : u.Perm v) :
    naturalExchangeBracket u = naturalExchangeBracket v := by
  unfold naturalExchangeBracket
  rw [(h.map _).prod_eq, (h.map _).prod_eq]

theorem naturalExchangeGainLower_perm (z : ℝ) {u v : List ℝ} (h : u.Perm v) :
    naturalExchangeGainLower z u = naturalExchangeGainLower z v := by
  unfold naturalExchangeGainLower
  rw [(h.map _).prod_eq, naturalExchangeBracket_perm h]

/-- The certified bracket is positive for every finite coefficient field. -/
theorem naturalExchangeBracket_selected_pos : 0 < naturalExchangeBracket (naturalExchangeSelectedWeights F) := by
  by_cases h₂ : Fintype.card F = 2
  · rw [naturalExchangeBracket_perm (naturalExchangeSelectedWeights_binary h₂)]
    exact (by norm_num : (0:ℝ) < 6622/100000).trans naturalExchangeBracket_small.1
  by_cases h₃ : Fintype.card F = 3
  · rw [naturalExchangeBracket_perm (naturalExchangeSelectedWeights_ternary h₃)]
    exact (by norm_num : (0:ℝ) < 9852/100000).trans naturalExchangeBracket_small.2.1
  by_cases h₄ : Fintype.card F = 4
  · rw [naturalExchangeSelectedWeights_four h₄]
    exact (by norm_num : (0:ℝ) < 9023/100000).trans naturalExchangeBracket_small.2.2
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hq₅ : 5 ≤ Fintype.card F := by omega
  rw [naturalExchangeSelectedWeights_linear (by omega)]
  exact (by norm_num : (0:ℝ) < 1/15).trans_le (naturalExchangeBracket_linear_lower _ hq₅)

/-- The three certified numerical gains apply to the actual prime choices. -/
theorem naturalExchangeGainLower_selected_small :
    (Fintype.card F = 2 → (4244:ℝ)/100000000 <
      naturalExchangeGainLower (Fintype.card F : ℝ)⁻¹ (naturalExchangeSelectedWeights F)) ∧
    (Fintype.card F = 3 → (7119:ℝ)/100000000 <
      naturalExchangeGainLower (Fintype.card F : ℝ)⁻¹ (naturalExchangeSelectedWeights F)) ∧
    (Fintype.card F = 4 → (8364:ℝ)/100000000 <
      naturalExchangeGainLower (Fintype.card F : ℝ)⁻¹ (naturalExchangeSelectedWeights F)) := by
  refine ⟨fun hq ↦ ?_, fun hq ↦ ?_, fun hq ↦ ?_⟩
  · rw [naturalExchangeGainLower_perm _ (naturalExchangeSelectedWeights_binary hq), hq]
    simpa only [Nat.cast_ofNat, inv_eq_one_div] using naturalExchangeGainLower_small.1
  · rw [naturalExchangeGainLower_perm _ (naturalExchangeSelectedWeights_ternary hq), hq]
    simpa only [Nat.cast_ofNat, inv_eq_one_div] using naturalExchangeGainLower_small.2.1
  · rw [naturalExchangeSelectedWeights_four hq, hq]
    simpa only [Nat.cast_ofNat, inv_eq_one_div] using naturalExchangeGainLower_small.2.2

end GRHArticle.ProgressionFree
