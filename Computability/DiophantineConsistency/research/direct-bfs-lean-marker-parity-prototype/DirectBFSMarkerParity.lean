import DirectBFSRawParity
import DirectBFSCarryRoom
import DiophantineConsistency.FieldMarkerColumns
import DiophantineConsistency.BooleanEvenSum
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectBFSMarkerParity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticBinaryCarry ArithmeticRepunit CompactHeterogeneousCarry CompactBitRotation CompactSymbolicPorts
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
open FieldWindowGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem pos_of_phase (k : V) (t : ℕ) (ht : 0<t) (hp : k%8807=(t:V)) : 0<k := by
  by_contra hn
  have hk : k=0 := nonpos_iff_eq_zero.mp (not_lt.mp hn)
  rw [hk,zero_mod] at hp
  have ht0 : t=0 := by exact_mod_cast hp.symm
  omega

theorem vertical (N C E F k : V) (hN : 0<N) (hk : k<8807*N)
    (hC : C<Exp.exp (67*(8807*N))) (haligned : E%67=0)
    (hcell : ((E/67)%(8807*N))%8807=0) (hp : k%8807=(1022:V))
    (hslots : ∀ x<8807*N, 0<x → NoCarry (dig 67 C x) (dig 67 (lowNat:V) (x%8807)))
    (hbool : ∀ x<8807*N, x%8807≠1063 → dig 67 C x≤1)
    (hhigh : NoCarry F ((highNat:V)*rep (67*8807) N-1))
    (hcarry : CarryInput 67 (8807*N) F 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41)))
      (GenericBandCarryFamily.coefficient (fun j => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V)))
      (GenericBandCarryFamily.word (8807*N) C (bandOffsets CompactSymbolicKernel.position) (temporalWord (8807*N) E C))) :
    dig 67 C (cyc (8807*N) k 30)=dig 67 C (cyc (8807*N) k ((E/67)%(8807*N))) := by
  let n : V := 8807*N
  let D : V := (E/67)%n
  let T := temporalWord n E C
  have hn : 0<n := mul_pos (by norm_num) hN
  have hk0 : 0<k := pos_of_phase k 1022 (by norm_num) hp
  have heven := FieldMarkerHigh.even N F k hN hk hk0 (Or.inl hp) hhigh
  have hreset := (FieldWindowReset.reset N C E F k 1022
    (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V))
    (bandOffsets CompactSymbolicKernel.position) hN hk hC haligned hcell (by norm_num) (by norm_num) (by norm_num)
    hp hbool hcarry DirectBFSCarryRoom.aligned_room).2
  have hraw := (CarryParity.raw_plus_incoming_even n F _ _ _ hcarry k hk heven).2
  have hpar := DirectBFSRawParity.expand CompactSymbolicKernel.position n C T k _ hn hk hC hraw
  obtain ⟨hs1,hs2,hbare⟩ := FieldMarkerColumns.vertical N C k hN hk hC hp hslots
  rw [hs1,hs2,hbare,hreset] at hpar
  simp only [zero_add,add_zero] at hpar
  rw [dig_rot 67 n C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn,
    AlignedTemporalAnchor.digit C n E k hn hk hC haligned] at hpar
  have hleftphase : (cyc n k 30)%8807=((992:ℕ):V) := by
    have hh := FieldExactZero.cyclic_phase N k 1022 30 hN hp
    have hp' : phase 1022 30=992 := by decide
    simpa only [hp',Nat.cast_ofNat] using hh
  have hrightphase : (cyc n k D)%8807=(1022:V) := by
    rw [WholeBlockPhase.shift_phase N k D hN hcell,hp]
  have hleft : dig 67 C (cyc n k 30)≤1 := by
    apply hbool _ (cyc_lt hn _ _)
    rw [hleftphase]
    norm_num
  have hright : dig 67 C (cyc n k D)≤1 := by
    apply hbool _ (cyc_lt hn _ _)
    rw [hrightphase]
    norm_num
  exact BooleanEvenSum.eq_of_even _ _ hleft hright hpar

theorem horizontal (N C E F k : V) (hN : 0<N) (hk : k<8807*N)
    (hC : C<Exp.exp (67*(8807*N))) (haligned : E%67=0)
    (hcell : ((E/67)%(8807*N))%8807=0) (hp : k%8807=(1073:V))
    (hslots : ∀ x<8807*N, 0<x → NoCarry (dig 67 C x) (dig 67 (lowNat:V) (x%8807)))
    (hbool : ∀ x<8807*N, x%8807≠1063 → dig 67 C x≤1)
    (hhigh : NoCarry F ((highNat:V)*rep (67*8807) N-1))
    (hcarry : CarryInput 67 (8807*N) F 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41)))
      (GenericBandCarryFamily.coefficient (fun j => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V)))
      (GenericBandCarryFamily.word (8807*N) C (bandOffsets CompactSymbolicKernel.position) (temporalWord (8807*N) E C))) :
    dig 67 C (cyc (8807*N) k 62)=dig 67 C (cyc (8807*N) k 8849) := by
  let n : V := 8807*N
  let D : V := (E/67)%n
  let T := temporalWord n E C
  have hn : 0<n := mul_pos (by norm_num) hN
  have hk0 : 0<k := pos_of_phase k 1073 (by norm_num) hp
  have heven := FieldMarkerHigh.even N F k hN hk hk0 (Or.inr hp) hhigh
  have hreset := (FieldWindowReset.reset N C E F k 1073
    (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V))
    (bandOffsets CompactSymbolicKernel.position) hN hk hC haligned hcell (by norm_num) (by norm_num) (by norm_num)
    hp hbool hcarry DirectBFSCarryRoom.aligned_room).2
  have htemp : dig 67 T k=0 := by
    rw [AlignedTemporalAnchor.digit C n E k hn hk hC haligned]
    apply FieldExactZero.source_zero N C _ 1073 (cyc_lt hn _ _) (by norm_num) _
      HorizontalMarkerGeometry.temporal_absent hslots
    rw [WholeBlockPhase.shift_phase N k D hN hcell,hp]
    norm_num
  have hraw := (CarryParity.raw_plus_incoming_even n F _ _ _ hcarry k hk heven).2
  have hpar := DirectBFSRawParity.expand CompactSymbolicKernel.position n C T k _ hn hk hC hraw
  obtain ⟨hs1,hs2,hbare⟩ := FieldMarkerColumns.horizontal N C k hN hk hC hp hslots
  rw [hs1,hs2,hbare,hreset,htemp] at hpar
  simp only [zero_add,add_zero] at hpar
  rw [dig_rot 67 n C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn,
    dig_rot 67 n C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn] at hpar
  have hleftphase : (cyc n k 62)%8807=((1011:ℕ):V) := by
    have hh := FieldExactZero.cyclic_phase N k 1073 62 hN hp
    have hp' : phase 1073 62=1011 := by decide
    simpa only [hp',Nat.cast_ofNat] using hh
  have hrightphase : (cyc n k 8849)%8807=((1031:ℕ):V) := by
    have hh := FieldExactZero.cyclic_phase N k 1073 8849 hN hp
    have hp' : phase 1073 8849=1031 := by decide
    simpa only [hp',Nat.cast_ofNat] using hh
  have hleft : dig 67 C (cyc n k 62)≤1 := by
    apply hbool _ (cyc_lt hn _ _)
    rw [hleftphase]
    norm_num
  have hright : dig 67 C (cyc n k 8849)≤1 := by
    apply hbool _ (cyc_lt hn _ _)
    rw [hrightphase]
    norm_num
  exact BooleanEvenSum.eq_of_even _ _ hleft hright hpar
#print axioms DirectBFSMarkerParity.vertical
#print axioms DirectBFSMarkerParity.horizontal
end DirectBFSMarkerParity
