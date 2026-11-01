import DiophantineConsistency.ArithmeticRankForcing
import DiophantineConsistency.ArithmeticMaskPopulation
import DiophantineConsistency.ArithmeticMaskConstants
import DiophantineConsistency.ArithmeticCarrierRadix2011

/-! Construction stage R (spec §6, plan K4) for the actual current carrier.

The rank `ArithmeticCarrierRadix2011.rank v` is *constructed* from the packing
blocks: with `J = v0 = rep W N` (`W = width = 94517`, `u = W*N`), `C > 0`,
`F = v1`, `α = v2 > 0`, `C+F+α = 2^u`, `C-1 ≡ 0 (mod 4)` and the two
AND-disjointness facts (`NoCarry`) of `C-1` against the low mask summand
`lowPort*J+1` and of `F` against the high mask summand `highPort*J-1`, it is the
four-block number and has

  `σ(rank v) = 3u+2`,  `rank v % 4 = 3`,  `2u < rank v`,  `q v = 2^u`.

The mask populations come from `ArithmeticMaskPopulation.repeated_mask_population`
with the standard-constant facts of `ArithmeticMaskConstants`. -/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace DiophantineConsistency.ArithmeticRankForcing2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticRepunit ArithmeticRankForcing
  ArithmeticCarrierRadix2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `lowPort ≡ 2 (mod 4)`, Matrix-free: its radix-`2^47` digit 0 is `2^47-2`
(`CurrentMasks2011.lowPort_four` is not importable next to Foundation). -/
theorem lowPort_four_nat : CurrentMasks2011.lowPort % 4 = 2 := by
  obtain ⟨l, hl⟩ : ∃ l, ArithmeticMaskData.lowDigits = (CurrentMasks2011.radix - 2) :: l :=
    ⟨_, rfl⟩
  rw [ArithmeticMaskData.lowPort_ofDigits, hl, Nat.ofDigits_cons]
  generalize Nat.ofDigits CurrentMasks2011.radix l = X
  rw [ArithmeticMaskData.radix_eq]
  norm_num
  omega

theorem lowPort_mod_four : (CurrentMasks2011.lowPort:V)%4=2 := by
  simpa only [lowPort_four_nat, Nat.cast_ofNat] using
    (ArithmeticMaskConstants.cast_mod (V:=V) CurrentMasks2011.lowPort 4).symm

/-- **Rank forcing at the actual carrier.** -/
theorem current_rank_forcing (v : Fin 14 → V) (N C : V) (hN : 0<N)
    (hJ : v 0=rep (CurrentMasks2011.width:V) N) (hC : 0<C) (halpha : 0<v 2)
    (hsum : C+v 1+v 2=Exp.exp ((CurrentMasks2011.width:V)*N))
    (hA4 : (C-1)%4=0)
    (hlow : NoCarry (C-1) ((CurrentMasks2011.lowPort:V)*v 0+1))
    (hhigh : NoCarry (v 1) ((CurrentMasks2011.highPort:V)*v 0-1)) :
    q v=Exp.exp ((CurrentMasks2011.width:V)*N) ∧
    rank v=fourBlocks ((CurrentMasks2011.width:V)*N) (C-1)
      ((CurrentMasks2011.lowPort:V)*v 0+1) (v 1) ((CurrentMasks2011.highPort:V)*v 0-1) (v 2) ∧
    population (rank v)=3*((CurrentMasks2011.width:V)*N)+2 ∧ rank v%4=3 ∧
    2*((CurrentMasks2011.width:V)*N)<rank v := by
  obtain ⟨_,hl,hh⟩ := ArithmeticCarrierSoundness2011.current_bounds (V:=V)
  have hW : (CurrentMasks2011.width:V)=94517 := (current_width (V:=V)).1
  have hW47 : (47:V)*2011=94517 := by norm_num
  have hW3 : (3:V)≤(CurrentMasks2011.width:V) := by rw [hW]; norm_num
  obtain ⟨j,hj⟩ := ArithmeticMaskPopulation.rep_eight (CurrentMasks2011.width:V) N hW3 hN
  have hJ1 : 1≤v 0 := by rw [hJ,hj]; exact le_add_of_nonneg_left (by simp)
  -- q = 2^u
  have hq : q v=Exp.exp ((CurrentMasks2011.width:V)*N) := by
    simpa only [q, hJ, current_beta_exp (V:=V)] using
      repunit_identity (CurrentMasks2011.width:V) N
  -- block bounds
  have hhp_lt : (CurrentMasks2011.highPort:V)<(CurrentMasks2011.beta:V) := by
    exact lt_of_add_lt_add_right (by simpa only [Nat.cast_add, two_mul] using hh)
  have hM : (CurrentMasks2011.lowPort:V)*v 0+1<q v := by
    unfold q
    have h1 : (CurrentMasks2011.lowPort:V)+1≤(CurrentMasks2011.beta:V) := lt_iff_succ_le.mp hl
    calc
      (CurrentMasks2011.lowPort:V)*v 0+1≤(CurrentMasks2011.lowPort:V)*v 0+v 0 :=
        add_le_add le_rfl hJ1
      _=((CurrentMasks2011.lowPort:V)+1)*v 0 := by ring
      _≤(CurrentMasks2011.beta:V)*v 0 := mul_le_mul_of_nonneg_right h1 (by simp)
      _<(CurrentMasks2011.beta:V)*v 0+1 := lt_add_one _
  have hHle : (CurrentMasks2011.highPort:V)*v 0≤(CurrentMasks2011.beta:V)*v 0 :=
    mul_le_mul_of_nonneg_right hhp_lt.le (by simp)
  have hH : (CurrentMasks2011.highPort:V)*v 0-1<q v := by
    unfold q
    exact lt_of_le_of_lt (le_trans tsub_le_self hHle) (lt_add_one _)
  have hpos : (0:V)<(CurrentMasks2011.highPort:V) := ArithmeticMaskConstants.highPort_pos
  have hHJ : (CurrentMasks2011.highPort:V)*v 0-1+1=(CurrentMasks2011.highPort:V)*v 0 :=
    tsub_add_cancel_of_le (one_le_mul (pos_iff_one_le.mp hpos) hJ1)
  have hsumA : (C-1)+1+v 1+v 2=q v := by
    rw [tsub_add_cancel_of_le (pos_iff_one_le.mp hC),hq]; exact hsum
  -- the rank identity
  have hrank : rank v=fourBlocks ((CurrentMasks2011.width:V)*N) (C-1)
      ((CurrentMasks2011.lowPort:V)*v 0+1) (v 1) ((CurrentMasks2011.highPort:V)*v 0-1) (v 2) := by
    unfold rank
    rw [Nat.cast_add]
    exact rank_eq_fourBlocks _ (q v) (CurrentMasks2011.beta:V) (v 0) (CurrentMasks2011.lowPort:V)
      (CurrentMasks2011.highPort:V) (C-1) (v 1) (v 2) _ rfl hq hsumA hHJ
  rw [hq] at hsumA hM hH
  -- populations
  have hpop := fourBlocks_population _ (C-1) _ (v 1) _ (v 2) hsumA hM hH hlow hhigh
  have hmask := ArithmeticMaskPopulation.repeated_mask_population (CurrentMasks2011.width:V) N
    (CurrentMasks2011.lowPort:V) (CurrentMasks2011.highPort:V) hW3 hN
    (by rw [hW,←hW47]; exact ArithmeticMaskConstants.lowPort_lt_exp)
    (by rw [hW,←hW47]; exact ArithmeticMaskConstants.highPort_lt_exp)
    ArithmeticMaskConstants.lowPort_even ArithmeticMaskConstants.highPort_mod_eight
    (by rw [hW]; exact ArithmeticMaskConstants.ports_population)
  rw [←hJ] at hmask
  -- residue of the low summand
  have hM4 : ((CurrentMasks2011.lowPort:V)*v 0+1)%4=3 := by
    have hJ4 : v 0 % 4 = 1 := by
      rw [hJ, hj, show (8:V)*j+1 = 1+4*(2*j) by ring,
        mod_add_mul' _ _ (by norm_num), mod_eq_self_of_lt (by norm_num : (1:V)<4)]
    rw [mod_add (by norm_num : (0:V)<4), mod_mul (by norm_num : (0:V)<4), lowPort_mod_four, hJ4]
    norm_num
  have hu2 : 2≤(CurrentMasks2011.width:V)*N := le_trans (le_trans (by norm_num) hW3)
    (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hN))
  refine ⟨hq,hrank,?_,?_,?_⟩
  · rw [hrank,hpop,hmask]; ring
  · rw [hrank]; exact fourBlocks_mod_four _ _ _ _ _ _ hu2 hA4 hM4
  · rw [hrank]; exact fourBlocks_gt _ _ _ _ _ _ halpha

end DiophantineConsistency.ArithmeticRankForcing2011
