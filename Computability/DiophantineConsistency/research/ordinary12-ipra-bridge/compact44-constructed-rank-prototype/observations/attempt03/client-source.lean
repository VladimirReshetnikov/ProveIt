import DiophantineConsistency.ArithmeticRankForcing
import DiophantineConsistency.ArithmeticMaskPopulation
import DiophantineConsistency.CompactLowExact
import DiophantineConsistency.CompactLowEven
import DiophantineConsistency.CompactHighResidue
import DiophantineConsistency.ArithmeticPacking

/-! Rank forcing for the exact symbolic compact masks. The two mod-four
assumptions are retained until the origin and mask residues are connected. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactConstructedRank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticRepunit ArithmeticRankForcing ArithmeticPacking
attribute [local irreducible] CompactHighPopulation.highDigits CompactConcreteIncrement.mask
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

abbrev low : V := CompactConcreteIncrement.mask
abbrev high : V := ((Nat.ofDigits (2^67) CompactHighPopulation.highDigits : ℕ) : V)

def rank (K N s : V) (X : V → V) [𝚺₁-Function₁ X] : V :=
  let q := Exp.exp (590069*N)
  let β := Exp.exp (590069:V)-1
  let J := rep 590069 N
  ((q-1)*(q-Fw 590069 K N s X)+alpha 590069 K N s X)*(q^2-1) +
    (low+q*(high+β))*J

theorem rank_properties {K N s : V} {X : V → V} [𝚺₁-Function₁ X]
    (h : PackingInput 590069 K low high N s X)
    (hA4 : (Cw 590069 N X-1)%4=0)
    (hL4 : (low:V)%4=2) :
    population (rank K N s X) = 3*(590069*N)+2 ∧
      rank K N s X % 4 = 3 ∧ 2*(590069*N) < rank K N s X := by
  let d : V := 590069
  let J := rep d N
  let q := Exp.exp (d*N)
  let β := Exp.exp d-1
  let C := Cw d N X
  let F := Fw d K N s X
  let A := alpha d K N s X
  have hN : 0<N := N_pos h
  have hq : β*J+1=q := repunit_identity d N
  obtain ⟨j,hj⟩ := ArithmeticMaskPopulation.rep_eight d N (by dsimp [d]; norm_num) hN
  have hJ1 : 1≤J := by rw [show J=rep d N from rfl, hj]; exact le_add_of_nonneg_left (by simp)
  have hsum : C+F+A=q := (packing_alpha h).2
  have hC : 0<C := C_pos h
  have hA : 0<A := (packing_alpha h).1
  have hsumA : (C-1)+1+F+A=q := by rw [tsub_add_cancel_of_le (pos_iff_one_le.mp hC)]; exact hsum
  have hβ : low+1≤β := by
    apply le_tsub_of_add_le_left
    simpa only [d, add_comm] using (lt_iff_succ_le.mp h.MC_lt)
  have hM : low*J+1<q := by
    rw [←hq]
    calc
      low*J+1 ≤ low*J+J := add_le_add le_rfl hJ1
      _ = (low+1)*J := by ring
      _ ≤ β*J := mul_le_mul_of_nonneg_right hβ (by simp)
      _ < β*J+1 := lt_add_one _
  have hHβ : high≤β := by
    apply le_tsub_of_add_le_left
    simpa only [d, add_comm] using (lt_iff_succ_le.mp h.HP_lt)
  have hH : high*J-1<q := by
    rw [←hq]
    exact lt_of_le_of_lt (le_trans tsub_le_self (mul_le_mul_of_nonneg_right hHβ (by simp))) (lt_add_one _)
  have hHJ : high*J-1+1=high*J := tsub_add_cancel_of_le (one_le_mul h.HP_pos hJ1)
  have hEq : rank K N s X = fourBlocks (d*N) (C-1) (low*J+1) F (high*J-1) A := by
    dsimp only [rank, d, J, q, β, C, F, A] at *
    exact rank_eq_fourBlocks _ _ _ _ _ _ _ _ _ _ hq rfl hsumA hHJ
  have hmasks : population (low*J+1)+population (high*J-1)=d*N+2 := by
    apply ArithmeticMaskPopulation.repeated_mask_population d N low high (by dsimp [d]; norm_num) hN
    · exact lt_of_le_of_lt (le_add_of_nonneg_right (by simp)) h.MC_lt
    · exact h.HP_lt
    · exact CompactLowEven.low_even
    · exact CompactHighResidue.model_mod_eight
    · have hl := CompactLowExact.model_population (V:=V)
      have hh := CompactHighPopulation.model_population (V:=V)
      change population (low:V)=589083 at hl
      change population (high:V)=986 at hh
      rw [hl,hh]
      dsimp [d]
      norm_num
  have hM4 : (low*J+1)%4=3 := by
    have hJ4 : J%4=1 := by
      rw [show J=rep d N from rfl,hj,show (8:V)*j+1=1+4*(2*j) by ring,
        mod_add_mul' _ _ (by norm_num),mod_eq_self_of_lt (by norm_num : (1:V)<4)]
    rw [mod_add (by norm_num : (0:V)<4),mod_mul (by norm_num : (0:V)<4),hL4,hJ4]
    norm_num
  have hu : 2≤d*N := le_trans (by dsimp [d]; norm_num)
    (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hN))
  refine ⟨?_,?_,?_⟩
  · rw [hEq, fourBlocks_population _ _ _ _ _ _ (by simpa [q] using hsumA)
      (by simpa [q] using hM) (by simpa [q] using hH) (packing_low_mask h) (packing_high_mask h), hmasks]
    dsimp [d]; ring
  · rw [hEq]; exact fourBlocks_mod_four _ _ _ _ _ _ hu hA4 hM4
  · rw [hEq]; exact fourBlocks_gt _ _ _ _ _ _ hA

#print axioms CompactConstructedRank.rank_properties
end CompactConstructedRank
