import DiophantineConsistency.ArithmeticRankForcing
import DiophantineConsistency.ArithmeticMaskPopulation
import DiophantineConsistency.Adm942.Adm942MaskConstants
import DiophantineConsistency.Adm942.Adm942CarrierRadix

/-! # Construction stage R for the actual admissible942 carrier

The counterpart of `ArithmeticRankForcing2011` (`PROOF.md` §10). With
`J = v0 = rep W N` (`W = width = 189269`, `u = W*N`), `C > 0`, `F = v1`,
`α = v2 > 0`, `C+F+α = 2^u`, `C-1 ≡ 0 (mod 4)` and the two AND-disjointness
facts (`NoCarry`) of `C-1` against `MC*J+1` and of `F` against `MF_native*J-1`,
the rank is the four-block number and has

  `σ(rank v) = 3u+2`,  `rank v % 4 = 3`,  `2u < rank v`,  `q v = 2^u`.

The mask populations come from the port-generic
`ArithmeticMaskPopulation.repeated_mask_population` with the admissible942
standard-constant facts of `Adm942MaskConstants`. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace Adm942RankForcing
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticRepunit ArithmeticRankForcing
  Adm942CarrierRadix
attribute [local irreducible] Adm942Kernel.K Adm942MaskData.radix Adm942MaskData.beta
  Adm942MaskData.lowPort Adm942MaskData.highPort

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `MC ≡ 2 (mod 4)`: its radix-`2^47` digit 0 is `2^47-2`. -/
theorem lowPort_four_nat : Adm942MaskData.lowPort % 4 = 2 := by
  obtain ⟨l, hl⟩ : ∃ l, Adm942MaskData.lowDigits = (Adm942MaskData.radix - 2) :: l :=
    ⟨_, rfl⟩
  rw [Adm942MaskData.lowPort_ofDigits, hl, Nat.ofDigits_cons]
  generalize Nat.ofDigits Adm942MaskData.radix l = X
  rw [Adm942MaskData.radix_eq]
  norm_num
  omega

theorem lowPort_mod_four : (Adm942MaskData.lowPort:V)%4=2 := by
  simpa only [lowPort_four_nat, Nat.cast_ofNat] using
    (ArithmeticMaskConstants.cast_mod (V:=V) Adm942MaskData.lowPort 4).symm

/-- `MF_native ≡ 4 (mod 8)`, in ℕ: its radix-`2^47` digit 0 is `4`. -/
theorem highPort_eight_nat : Adm942MaskData.highPort % 8 = 4 := by
  obtain ⟨l, hl⟩ : ∃ l, Adm942MaskData.highDigits = 4 :: l := ⟨_, rfl⟩
  rw [Adm942MaskData.highPort_ofDigits, hl, Nat.ofDigits_cons]
  generalize Nat.ofDigits (2^47) l = X
  rw [show (2:ℕ)^47 * X = 8 * (2^44 * X) by ring, Nat.add_mul_mod_self_left]

/-- **Rank forcing at the actual admissible942 carrier.** -/
theorem current_rank_forcing (v : Fin 14 → V) (N C : V) (hN : 0<N)
    (hJ : v 0=rep (Adm942MaskData.width:V) N) (hC : 0<C) (halpha : 0<v 2)
    (hsum : C+v 1+v 2=Exp.exp ((Adm942MaskData.width:V)*N))
    (hA4 : (C-1)%4=0)
    (hlow : NoCarry (C-1) ((Adm942MaskData.lowPort:V)*v 0+1))
    (hhigh : NoCarry (v 1) ((Adm942MaskData.highPort:V)*v 0-1)) :
    q v=Exp.exp ((Adm942MaskData.width:V)*N) ∧
    rank v=fourBlocks ((Adm942MaskData.width:V)*N) (C-1)
      ((Adm942MaskData.lowPort:V)*v 0+1) (v 1) ((Adm942MaskData.highPort:V)*v 0-1) (v 2) ∧
    population (rank v)=3*((Adm942MaskData.width:V)*N)+2 ∧ rank v%4=3 ∧
    2*((Adm942MaskData.width:V)*N)<rank v := by
  obtain ⟨_,hl,hh⟩ := Adm942Ports.current_bounds (V:=V)
  have hW : (Adm942MaskData.width:V)=189269 := (current_width (V:=V)).1
  have hW47 : (47:V)*4027=189269 := by norm_num
  have hW3 : (3:V)≤(Adm942MaskData.width:V) := by rw [hW]; norm_num
  obtain ⟨j,hj⟩ := ArithmeticMaskPopulation.rep_eight (Adm942MaskData.width:V) N hW3 hN
  have hJ1 : 1≤v 0 := by rw [hJ,hj]; exact le_add_of_nonneg_left (by simp)
  -- q = 2^u
  have hq : q v=Exp.exp ((Adm942MaskData.width:V)*N) := by
    simpa only [q, hJ, current_beta_exp (V:=V)] using
      repunit_identity (Adm942MaskData.width:V) N
  -- block bounds
  have hhp_lt : (Adm942MaskData.highPort:V)<(Adm942MaskData.beta:V) := by
    exact lt_of_add_lt_add_right (by simpa only [Nat.cast_add, two_mul] using hh)
  have hM : (Adm942MaskData.lowPort:V)*v 0+1<q v := by
    unfold q
    have h1 : (Adm942MaskData.lowPort:V)+1≤(Adm942MaskData.beta:V) := lt_iff_succ_le.mp hl
    calc
      (Adm942MaskData.lowPort:V)*v 0+1≤(Adm942MaskData.lowPort:V)*v 0+v 0 :=
        add_le_add le_rfl hJ1
      _=((Adm942MaskData.lowPort:V)+1)*v 0 := by ring
      _≤(Adm942MaskData.beta:V)*v 0 := mul_le_mul_of_nonneg_right h1 (by simp)
      _<(Adm942MaskData.beta:V)*v 0+1 := lt_add_one _
  have hHle : (Adm942MaskData.highPort:V)*v 0≤(Adm942MaskData.beta:V)*v 0 :=
    mul_le_mul_of_nonneg_right hhp_lt.le (by simp)
  have hH : (Adm942MaskData.highPort:V)*v 0-1<q v := by
    unfold q
    exact lt_of_le_of_lt (le_trans tsub_le_self hHle) (lt_add_one _)
  have hpos : (0:V)<(Adm942MaskData.highPort:V) := Adm942MaskConstants.highPort_pos
  have hHJ : (Adm942MaskData.highPort:V)*v 0-1+1=(Adm942MaskData.highPort:V)*v 0 :=
    tsub_add_cancel_of_le (one_le_mul (pos_iff_one_le.mp hpos) hJ1)
  have hsumA : (C-1)+1+v 1+v 2=q v := by
    rw [tsub_add_cancel_of_le (pos_iff_one_le.mp hC),hq]; exact hsum
  -- the rank identity
  have hrank : rank v=fourBlocks ((Adm942MaskData.width:V)*N) (C-1)
      ((Adm942MaskData.lowPort:V)*v 0+1) (v 1) ((Adm942MaskData.highPort:V)*v 0-1) (v 2) := by
    unfold rank
    rw [Nat.cast_add]
    exact rank_eq_fourBlocks _ (q v) (Adm942MaskData.beta:V) (v 0) (Adm942MaskData.lowPort:V)
      (Adm942MaskData.highPort:V) (C-1) (v 1) (v 2) _ rfl hq hsumA hHJ
  rw [hq] at hsumA hM hH
  -- populations
  have hpop := fourBlocks_population _ (C-1) _ (v 1) _ (v 2) hsumA hM hH hlow hhigh
  have hmask := ArithmeticMaskPopulation.repeated_mask_population (Adm942MaskData.width:V) N
    (Adm942MaskData.lowPort:V) (Adm942MaskData.highPort:V) hW3 hN
    (by rw [hW,←hW47]; exact Adm942MaskConstants.lowPort_lt_exp)
    (by rw [hW,←hW47]; exact Adm942MaskConstants.highPort_lt_exp)
    Adm942MaskConstants.lowPort_even Adm942MaskConstants.highPort_mod_eight
    (by rw [hW]; exact Adm942MaskConstants.ports_population)
  rw [←hJ] at hmask
  -- residue of the low summand
  have hM4 : ((Adm942MaskData.lowPort:V)*v 0+1)%4=3 := by
    have hJ4 : v 0 % 4 = 1 := by
      rw [hJ, hj, show (8:V)*j+1 = 1+4*(2*j) by ring,
        mod_add_mul' _ _ (by norm_num), mod_eq_self_of_lt (by norm_num : (1:V)<4)]
    rw [mod_add (by norm_num : (0:V)<4), mod_mul (by norm_num : (0:V)<4), lowPort_mod_four, hJ4]
    norm_num
  have hu2 : 2≤(Adm942MaskData.width:V)*N := le_trans (le_trans (by norm_num) hW3)
    (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hN))
  refine ⟨hq,hrank,?_,?_,?_⟩
  · rw [hrank,hpop,hmask]; ring
  · rw [hrank]; exact fourBlocks_mod_four _ _ _ _ _ _ hu2 hA4 hM4
  · rw [hrank]; exact fourBlocks_gt _ _ _ _ _ _ halpha

end Adm942RankForcing

#print axioms Adm942RankForcing.lowPort_four_nat
#print axioms Adm942RankForcing.lowPort_mod_four
#print axioms Adm942RankForcing.highPort_eight_nat
#print axioms Adm942RankForcing.current_rank_forcing
