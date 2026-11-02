import DiophantineConsistency.FieldWindowParity
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphFieldBits
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_field_bits (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    let a := GenericBandCarryFamily.coefficient (fun j : Aligned (Fin 943) (Fin 41) => (alignedCoeff selectors copies j:V))
    ∃ N w s : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ v 0=rep (67*8807) N ∧
      (67*8807)*N≤R ∧ w=Exp.exp (R-(67*8807)*N) ∧ v 5=q*w ∧
      let E := R-67*(8807*N)
      let T := temporalWord (8807*N) E C
      let X := GenericBandCarryFamily.word (8807*N) C (bandOffsets position) T
      CarryInput 67 (8807*N) (v 1) 1 (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41))) a X ∧
      E%67=0 ∧ s<N ∧ (E/67)%(8807*N)=8807*s ∧
      (∀ u : ℕ, u<9 → ∀ k<8807*N, k%8807=((1013+u:ℕ):V) →
        dig 67 C (cyc (8807*N) k 30)=dig 67 C (cyc (8807*N) k ((E/67)%(8807*N)))) ∧
      (∀ u : ℕ, u<8 → ∀ k<8807*N, k%8807=((1065+u:ℕ):V) →
        dig 67 C (cyc (8807*N) k 62)=dig 67 C (cyc (8807*N) k 8849)) := by
  obtain ⟨N,w,s,hN,hq,hJ,hle,hw,hv5,hcarry,haligned,hs,hshift,hreset⟩ :=
    FixedGraphUniformReset.graph_uniform_reset v hv hz
  obtain ⟨N',w',hN',hq',hJ',hle',hw',hv5',hcarry',h0',hzero,hbool⟩ :=
    FixedGraphSupportCarry.graph_support_carry v hv hz
  obtain ⟨N'',w'',hN'',hq'',hJ'',hv5'',hcongr'',h0'',hslots,hhigh⟩ :=
    CompactPositionCarry.fixed_position_noCarry (paramKernel rho) v hv hz
  dsimp only at *
  have hNN1 : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hNN2 : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N''
  let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let C : V := q-v 1-v 2
  let n : V := 8807*N
  let E : V := R-67*n
  have hqexp : q=Exp.exp (67*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (67*n) := by
    dsimp [C]
    exact BandCarryInputs.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  have hhigh' : NoCarry (v 1) ((highNat:V)*rep (67*8807) N-1) := by rw [←hJ]; exact hhigh
  have hcell : ((E/67)%n)%8807=0 := by rw [hshift,mod_mul_self_right]
  refine ⟨N,w,s,hN,hq,hJ,hle,hw,hv5,hcarry,haligned,hs,hshift,?_,?_⟩
  · intro u hu k hk hp
    exact FieldWindowParity.vertical N C E (v 1) k u hu hN hk hC haligned hcell hp hslots hbool hhigh' hcarry
  · intro u hu k hk hp
    exact FieldWindowParity.horizontal N C E (v 1) k u hu hN hk hC haligned hcell hp hslots hbool hhigh' hcarry
#print axioms FixedGraphFieldBits.graph_field_bits
end FixedGraphFieldBits
