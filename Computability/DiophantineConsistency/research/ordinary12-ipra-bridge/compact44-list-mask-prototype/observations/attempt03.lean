import DiophantineConsistency.ArithmeticMaskConstants
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
noncomputable section
namespace CompactListMask
open Finset
open scoped BigOperators

def digit (B special : ℕ) (S : Finset ℕ) (j : ℕ) : ℕ :=
  if j=special then B-4 else if j∈S then B-2 else B-1

def defect (special : ℕ) (S : Finset ℕ) (j : ℕ) : ℕ :=
  if j=special then 3 else if j∈S then 1 else 0

def digits (B len special : ℕ) (S : Finset ℕ) : List ℕ :=
  (List.range len).map (digit B special S)

theorem ofDigits_map_range (B : ℕ) (f : ℕ → ℕ) :
    ∀ n : ℕ, Nat.ofDigits B ((List.range n).map f) = ∑ j ∈ range n, f j * B^j
  | 0 => by simp
  | n+1 => by
    rw [List.range_succ, List.map_append, Nat.ofDigits_append, ofDigits_map_range B f n,
      Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil, List.length_map, List.length_range,
      Nat.ofDigits_singleton]
    ring

theorem geom_identity (B : ℕ) (hB : 1 ≤ B) :
    ∀ n : ℕ, (∑ j ∈ range n, B^j) * (B-1) + 1 = B^n
  | 0 => by simp
  | n+1 => by
    rw [Finset.sum_range_succ, Nat.add_mul]
    calc
      ((∑ j ∈ range n, B^j) * (B-1) + B^n*(B-1)) + 1 =
          ((∑ j ∈ range n, B^j) * (B-1) + 1) + B^n*(B-1) := by omega
      _ = B^n + B^n*(B-1) := by rw [geom_identity B hB n]
      _ = B^n * ((B-1)+1) := by ring
      _ = B^n * B := by rw [Nat.sub_add_cancel hB]
      _ = B^(n+1) := by rw [pow_succ]

/-- Exact finite symbolic recipe, with no expansion of the large numeral. -/
theorem digits_add_defect (B len special : ℕ) (S : Finset ℕ) (hB : 4 ≤ B) :
    Nat.ofDigits B (digits B len special S) +
      (∑ j ∈ range len, defect special S j * B^j) + 1 = B^len := by
  have hgeom := geom_identity B (by omega : 1 ≤ B) len
  have hsum : Nat.ofDigits B (digits B len special S) +
      (∑ j ∈ range len, defect special S j * B^j) =
      (∑ j ∈ range len, B^j) * (B-1) := by
    unfold digits
    rw [ofDigits_map_range, ← Finset.sum_add_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hs : j = special
    · simp only [digit, defect, if_pos hs]
      have he : B-4+3=B-1 := by omega
      calc
        (B-4)*B^j+3*B^j = (B-4+3)*B^j := by ring
        _ = B^j*(B-1) := by rw [he]; ring
    · by_cases hS : j ∈ S
      · simp only [digit, defect, if_neg hs, if_pos hS, one_mul]
        have he : B-2+1=B-1 := by omega
        calc
          (B-2)*B^j+B^j = (B-2+1)*B^j := by ring
          _ = B^j*(B-1) := by rw [he]; ring
      · simp only [digit, defect, if_neg hs, if_neg hS, zero_mul, add_zero]
        ring
  omega
theorem digits_length (B len special : ℕ) (S : Finset ℕ) :
    (digits B len special S).length = len := by simp [digits]

theorem digits_getD (B len special : ℕ) (S : Finset ℕ) {j : ℕ} (hj : j < len) :
    (digits B len special S).getD j 0 = digit B special S j := by
  unfold digits
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem digits_lt (B len special : ℕ) (S : Finset ℕ) (hB : 4 ≤ B) :
    ∀ x ∈ digits B len special S, x < B := by
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  unfold digit
  split_ifs <;> omega

section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
open DiophantineConsistency.ArithmeticMaskConstants
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem model_mask_class (len special : ℕ) (S : Finset ℕ) (j : V) (hj : j < (len:V)) :
    let M : V := (Nat.ofDigits (2^67) (digits (2^67) len special S) : ℕ)
    dig 67 M j = Exp.exp 67-1 ∨ dig 67 M j = Exp.exp 67-2 ∨
      dig 67 M j = Exp.exp 67-4 := by
  obtain ⟨j₀,rfl⟩ := eq_nat_of_lt_nat (n := len) hj
  have hj₀ : j₀ < len := by exact_mod_cast hj
  have hd := dig_ofDigits (V:=V) 67 (digits (2^67) len special S)
    (digits_lt _ _ _ _ (by norm_num)) j₀
  rw [digits_getD _ _ _ _ hj₀] at hd
  have hsub (r : ℕ) (hr : r ≤ 2^67) :
      ((2^67-r : ℕ):V) = Exp.exp (67:V)-(r:V) := by
    rw [Nat.cast_sub hr, ←cast_exp]
    simp
  unfold digit at hd
  split_ifs at hd <;> simp only [hsub _ (by norm_num), Nat.cast_ofNat] at hd
  · exact Or.inr (Or.inr hd)
  · exact Or.inr (Or.inl hd)
  · exact Or.inl hd
end Model
end CompactListMask
#print axioms CompactListMask.model_mask_class
#print axioms CompactListMask.digits_add_defect
