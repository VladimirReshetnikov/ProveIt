import DiophantineConsistency.ArithmeticWindowZero
import DiophantineConsistency.ArithmeticRankForcing2011
import Model69Phase

/-! Draft extraction of the current 2011 parent rank phase from an actual
positive zero. This has not yet been compiled against a coherent closure. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Model69CurrentPhase
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011
open ArithmeticWindowDigits ArithmeticWindowInterface ArithmeticWindowZero
open ArithmeticRankForcing ArithmeticRankForcing2011 ArithmeticRepunit
open ObjectCurrentEquation2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Draft: the actual 2011 positive parent zero has rank phase three. -/
theorem current_rank_phase (v : Fin 14 → V) (hv : ∀ j,0<v j)
    (hz : expression.splitNatural.1.evalSemiring v=expression.splitNatural.2.evalSemiring v) :
    (rank v)%4=3 := by
  obtain ⟨N,hq,hw⟩ := window_of_positive_zero v ⟨hv,hz⟩
  have hN : 0<N := hw.N_pos
  have hwidth : (CurrentMasks2011.width:V)=94517 := (current_width (V:=V)).1
  have hwidth3 : (3:V)≤(CurrentMasks2011.width:V) := by rw [hwidth]; norm_num
  have hwidth0 : (0:V)<(CurrentMasks2011.width:V) := lt_of_lt_of_le (by norm_num : (0:V)<3) hwidth3
  have hqexp : q v=Exp.exp ((CurrentMasks2011.width:V)*N) := by rw [hwidth]; exact hq
  let C:=q v-v 1-v 2
  have hC : 0<C := by
    obtain ⟨hb,hl,hh⟩ := current_bounds (V:=V)
    have hb0 : (0:V)<(CurrentMasks2011.beta:V) := lt_of_lt_of_le (by simp) hb
    have ht := (current_equations v hv hz).1
    exact (ArithmeticPellFirstIndex.scalar_window (q v) (CurrentMasks2011.beta:V)
      (CurrentKernel2011.K:V) (CurrentMasks2011.lowPort:V)
      ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)
      (v 0) (v 1) (v 2) (v 3) (v 8) (v 7) hb0 (hv 0) (hv 1) (hv 2)
      (hv 3) (hv 8) (hv 7) hl hh rfl ht).1
  have hsumlt : v 1+v 2<q v := tsub_pos_iff_lt.mp (by simpa only [C,tsub_tsub] using hC)
  have hsum : v 1+v 2+C=q v := by
    dsimp [C];rw [tsub_tsub];exact add_tsub_cancel_of_le (le_of_lt hsumlt)
  have hC1 : 1≤C := pos_iff_one_le.mp hC
  have hA : (C-1)+1+v 1+v 2=q v := by
    rw [tsub_add_cancel_of_le hC1,←hsum];ring
  have horigin : C % Exp.exp (47:V)=1 := by
    simpa only [C,dig_zero_index] using hw.origin
  have hexp2 : Exp.exp (2:V)=4 := by
    rw [show (2:V)=1+1 by ring,exp_add,exp_one];ring
  have hmod : Exp.exp (47:V)=4*Exp.exp (45:V) := by
    rw [show (47:V)=2+45 by norm_num,exp_add,hexp2]
  have hA4 : (C-1)%4=0 :=
    Model69Phase.pred_mod_four C (Exp.exp (47:V)) (Exp.exp (45:V)) hmod horigin
  have hJ : v 0=rep (CurrentMasks2011.width:V) N := by
    apply eq_rep_of_identity hwidth0
    rw [←current_beta_exp (V:=V)]
    exact hqexp
  obtain ⟨j,hj⟩ := ArithmeticMaskPopulation.rep_eight (CurrentMasks2011.width:V) N hwidth3 hN
  have hJ4 : v 0%4=1 := by
    rw [hJ,hj,show (8:V)*j+1=1+4*(2*j) by ring,
      mod_add_mul' _ _ (by norm_num),mod_eq_self_of_lt (by norm_num : (1:V)<4)]
  have hM4 : ((CurrentMasks2011.lowPort:V)*v 0+1)%4=3 := by
    rw [mod_add (by norm_num : (0:V)<4),mod_mul (by norm_num : (0:V)<4),lowPort_mod_four,hJ4]
    norm_num
  have hHP : (0:V)<(CurrentMasks2011.highPort:V) := ArithmeticMaskConstants.highPort_pos
  have hH : (CurrentMasks2011.highPort:V)*v 0-1+1=(CurrentMasks2011.highPort:V)*v 0 :=
    tsub_add_cancel_of_le (one_le_mul (pos_iff_one_le.mp hHP) (pos_iff_one_le.mp (hv 0)))
  have hrank : rank v=fourBlocks ((CurrentMasks2011.width:V)*N) (C-1)
      ((CurrentMasks2011.lowPort:V)*v 0+1) (v 1)
      ((CurrentMasks2011.highPort:V)*v 0-1) (v 2) := by
    unfold rank
    rw [Nat.cast_add]
    exact rank_eq_fourBlocks _ (q v) (CurrentMasks2011.beta:V) (v 0)
      (CurrentMasks2011.lowPort:V) (CurrentMasks2011.highPort:V) (C-1) (v 1)
      (v 2) ((CurrentMasks2011.highPort:V)*v 0-1) rfl hqexp hA hH
  have hu2 : (2:V)≤(CurrentMasks2011.width:V)*N :=
    le_trans (le_trans (by norm_num) hwidth3)
      (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hN))
  rw [hrank]
  exact fourBlocks_mod_four _ _ _ _ _ _ hu2 hA4 hM4
end Model69CurrentPhase
#print axioms Model69CurrentPhase.current_rank_phase
