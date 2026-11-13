import DiophantineConsistency.BFS943.DirectBFSRawParity
import DiophantineConsistency.BFS943.DirectBFSCarryRoom
import DiophantineConsistency.Compact44.FieldWindowParity
import DiophantineConsistency.Compact44.FieldWindowColumns
import DiophantineConsistency.Compact44.BooleanEvenSum

/-! Field-window parity for the direct-BFS aligned family.

Reconstructed in the tree (the research source was never committed): a port of
`FieldWindowParity.vertical/horizontal` to `DirectBFSModelMass.selectors/copies`,
`DirectBFSRawParity.expand` and `DirectBFSCarryRoom.aligned_room`, made exactly
as `DirectBFSMarkerParity` ports `FieldMarkerParity`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectBFSFieldParity
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

theorem vertical (N C E F k : V) (u : ℕ) (hu : u<9) (hN : 0<N) (hk : k<8807*N)
    (hC : C<Exp.exp (67*(8807*N))) (haligned : E%67=0)
    (hcell : ((E/67)%(8807*N))%8807=0) (hp : k%8807=((1013+u:ℕ):V))
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
  have hk0 : 0<k := pos_of_phase k (1013+u) (by omega) hp
  have heven := FieldHighModel.vertical_even N F k u hu hN hk hk0 hp hhigh
  have hreset := (FieldWindowReset.reset N C E F k (1013+u)
    (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V))
    (bandOffsets CompactSymbolicKernel.position) hN hk hC haligned hcell (by omega) (by omega) (by omega)
    hp hbool hcarry DirectBFSCarryRoom.aligned_room).2
  have hraw := (CarryParity.raw_plus_incoming_even n F _ _ _ hcarry k hk heven).2
  have hpar := DirectBFSRawParity.expand CompactSymbolicKernel.position n C T k _ hn hk hC hraw
  obtain ⟨hs1,hs2,hbare⟩ := FieldWindowColumns.vertical N C k u hu hN hk hC hp hslots
  rw [hs1,hs2,hbare,hreset] at hpar
  simp only [zero_add,add_zero] at hpar
  rw [dig_rot 67 n C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn,
    AlignedTemporalAnchor.digit C n E k hn hk hC haligned] at hpar
  have hleftphase : (cyc n k 30)%8807=((983+u:ℕ):V) := by
    have hh := FieldExactZero.cyclic_phase N k (1013+u) 30 hN hp
    have hp' : phase (1013+u) 30=983+u := by unfold phase; omega
    simpa only [hp',Nat.cast_ofNat] using hh
  have hrightphase : (cyc n k D)%8807=((1013+u:ℕ):V) := by
    rw [WholeBlockPhase.shift_phase N k D hN hcell,hp]
  have hleft : dig 67 C (cyc n k 30)≤1 := by
    apply hbool _ (cyc_lt hn _ _)
    rw [hleftphase]
    intro he
    have hh : 983+u=1063 := by exact_mod_cast he
    omega
  have hright : dig 67 C (cyc n k D)≤1 := by
    apply hbool _ (cyc_lt hn _ _)
    rw [hrightphase]
    intro he
    have hh : 1013+u=1063 := by exact_mod_cast he
    omega
  exact BooleanEvenSum.eq_of_even _ _ hleft hright hpar

theorem horizontal (N C E F k : V) (u : ℕ) (hu : u<8) (hN : 0<N) (hk : k<8807*N)
    (hC : C<Exp.exp (67*(8807*N))) (haligned : E%67=0)
    (hcell : ((E/67)%(8807*N))%8807=0) (hp : k%8807=((1065+u:ℕ):V))
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
  have hk0 : 0<k := pos_of_phase k (1065+u) (by omega) hp
  have heven := FieldHighModel.horizontal_even N F k u hu hN hk hk0 hp hhigh
  have hreset := (FieldWindowReset.reset N C E F k (1065+u)
    (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V))
    (bandOffsets CompactSymbolicKernel.position) hN hk hC haligned hcell (by omega) (by omega) (by omega)
    hp hbool hcarry DirectBFSCarryRoom.aligned_room).2
  have htemp : dig 67 T k=0 := by
    rw [AlignedTemporalAnchor.digit C n E k hn hk hC haligned]
    apply FieldExactZero.source_zero N C _ (1065+u) (cyc_lt hn _ _) (by omega) _
      (FieldWindowGeometry.horizontal_temporal u hu) hslots
    rw [WholeBlockPhase.shift_phase N k D hN hcell,hp]
  have hraw := (CarryParity.raw_plus_incoming_even n F _ _ _ hcarry k hk heven).2
  have hpar := DirectBFSRawParity.expand CompactSymbolicKernel.position n C T k _ hn hk hC hraw
  obtain ⟨hs1,hs2,hbare⟩ := FieldWindowColumns.horizontal N C k u hu hN hk hC hp hslots
  rw [hs1,hs2,hbare,hreset,htemp] at hpar
  simp only [zero_add,add_zero] at hpar
  rw [dig_rot 67 n C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn,
    dig_rot 67 n C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn] at hpar
  have hleftphase : (cyc n k 62)%8807=((1003+u:ℕ):V) := by
    have hh := FieldExactZero.cyclic_phase N k (1065+u) 62 hN hp
    have hp' : phase (1065+u) 62=1003+u := by unfold phase; omega
    simpa only [hp',Nat.cast_ofNat] using hh
  have hrightphase : (cyc n k 8849)%8807=((1023+u:ℕ):V) := by
    have hh := FieldExactZero.cyclic_phase N k (1065+u) 8849 hN hp
    have hp' : phase (1065+u) 8849=1023+u := by unfold phase; omega
    simpa only [hp',Nat.cast_ofNat] using hh
  have hleft : dig 67 C (cyc n k 62)≤1 := by
    apply hbool _ (cyc_lt hn _ _)
    rw [hleftphase]
    intro he
    have hh : 1003+u=1063 := by exact_mod_cast he
    omega
  have hright : dig 67 C (cyc n k 8849)≤1 := by
    apply hbool _ (cyc_lt hn _ _)
    rw [hrightphase]
    intro he
    have hh : 1023+u=1063 := by exact_mod_cast he
    omega
  exact BooleanEvenSum.eq_of_even _ _ hleft hright hpar
#print axioms DirectBFSFieldParity.vertical
#print axioms DirectBFSFieldParity.horizontal
end DirectBFSFieldParity
