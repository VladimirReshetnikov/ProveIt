import DiophantineConsistency.ArithmeticRankForcing
import DiophantineConsistency.ArithmeticMaskPopulation
import DiophantineConsistency.ArithmeticPacking
import DiophantineConsistency.Source34.Source34PulseBit

/-! # Rank forcing for the exact source34 masks

`Mixed121ConstructedRank` at the source34 tuple: the abbreviations `low`,
`high` now denote `Source34Ports.lowNat`, `Source34Ports.highNat`, so `rank`
and both theorems are re-declared; the proof bodies are unchanged. The source34
masks have the same residues and populations (`MC ≡ 2 (mod 4)`,
`MF_native ≡ 4 (mod 8)`, populations `1063932` and `989`). For a packing input
at block width `d = 121·8801`:

* `packing_origin_mod_four`: the low packing condition forces
  `C − 1 ≡ 0 (mod 4)`, because `MC·J + 1 ≡ 3 (mod 4)` (`MC ≡ 2`, `J ≡ 1`);
* `rank_properties`: the packed rank `R` has `popcount(R) = 3dN + 2`,
  `R ≡ 3 (mod 4)` and `R > 2dN`. The population balance is
  `popcount(MC) + popcount(MF) = 1063932 + 989 = d`, recipe §5. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Source34ConstructedRank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticRepunit ArithmeticRankForcing ArithmeticPacking
open ArithmeticWindowDigits ArithmeticMaskPopulation
attribute [local irreducible] Source34Ports.lowNat Source34Ports.highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

abbrev low : V := ((Source34Ports.lowNat : ℕ) : V)
abbrev high : V := ((Source34Ports.highNat : ℕ) : V)

theorem packing_origin_mod_four {K hi N s : V} {X : V → V} [𝚺₁-Function₁ X]
    (h : PackingInput 1064921 K (low : V) hi N s X) :
    (Cw 1064921 N X-1)%4=0 := by
  let L : V := low
  let J : V := rep 1064921 N
  obtain ⟨j,hj⟩ := rep_eight (1064921:V) N (by norm_num) (N_pos h)
  have hJ4 : J%4=1 := by
    rw [show J=rep 1064921 N from rfl,hj,show (8:V)*j+1=1+4*(2*j) by ring,
      mod_add_mul' _ _ (by norm_num),mod_eq_self_of_lt (by norm_num : (1:V)<4)]
  have hmask : (L*J+1)%4=3 := by
    rw [mod_add (by norm_num : (0:V)<4), mod_mul (by norm_num : (0:V)<4),
      show L%4=2 from Source34PulseBit.low_mod_four, hJ4]
    norm_num
  have he2 : Exp.exp (2:V)=4 := by
    rw [show (2:V)=1+1 by norm_num,exp_succ,exp_one]
    norm_num
  have hnc := noCarry_dig (2:V) (Cw 1064921 N X-1) (L*J+1) 0 (packing_low_mask h)
  rw [dig_zero_index, dig_zero_index, he2, hmask] at hnc
  have hthree : (4:V)-1=3 := by
    rw [show (4:V)=3+1 by norm_num, add_tsub_cancel_right]
  have hz := noCarry_ones (2:V) ((Cw 1064921 N X-1)%4)
    (by rw [he2]; exact mod_lt _ (by norm_num))
    (by simpa only [he2, hthree] using hnc)
  exact hz

def rank (K N s : V) (X : V → V) [𝚺₁-Function₁ X] : V :=
  let q := Exp.exp (1064921*N)
  let β := Exp.exp (1064921:V)-1
  let J := rep 1064921 N
  ((q-1)*(q-Fw 1064921 K N s X)+alpha 1064921 K N s X)*(q^2-1) +
    (low+q*(high+β))*J

theorem rank_properties {K N s : V} {X : V → V} [𝚺₁-Function₁ X]
    (h : PackingInput 1064921 K low high N s X)
    (hA4 : (Cw 1064921 N X-1)%4=0)
    (hL4 : (low:V)%4=2) :
    population (rank K N s X) = 3*(1064921*N)+2 ∧
      rank K N s X % 4 = 3 ∧ 2*(1064921*N) < rank K N s X := by
  let d : V := 1064921
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
    · exact Source34Masks.model_low_even
    · exact Source34Masks.model_high_mod_eight
    · have hl : population (low:V)=1063932 := Source34Masks.model_low_population
      have hh : population (high:V)=989 := Source34Masks.model_high_population
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

#print axioms Source34ConstructedRank.packing_origin_mod_four
#print axioms Source34ConstructedRank.rank_properties
end Source34ConstructedRank
