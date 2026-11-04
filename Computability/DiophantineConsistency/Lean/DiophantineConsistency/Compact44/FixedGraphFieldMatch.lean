import DiophantineConsistency.Compact44.HorizontalFieldBits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FixedGraphFieldMatch
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactPartialBand
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry ArithmeticPackingBlocks
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_field_match (v : Fin 12 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N W s : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ s<N ∧
      ((R-67*(8807*N))/67)%(8807*N)=8807*s ∧
      Blocks 10 (OrbitRowWord.row C N 1) N W ∧
      (∀ h<N, OrbitRowWord.row C N 1 h<943 ∧ OrbitRowWord.row C N 1 h≠1) ∧
      ∀ h<N, ∃ i j l : Fin 943,
        OrbitRowWord.row C N 1 h=(i.val:V) ∧
        OrbitRowWord.row C N 1 (cyc N h s)=(j.val:V) ∧
        OrbitRowWord.row C N 1 (cyc N h 1)=(l.val:V) ∧
        BinarySliceEqual.slice (Compact943Decoder.tileValue (V:=V) i) 25 9 =
          BinarySliceEqual.slice (Compact943Decoder.tileValue (V:=V) j) 8 9 ∧
        BinarySliceEqual.slice (Compact943Decoder.tileValue (V:=V) i) 17 8 =
          BinarySliceEqual.slice (Compact943Decoder.tileValue (V:=V) l) 0 8 := by
  obtain ⟨N,W,hN,hq,hW,hrows,hbound⟩ := FixedGraphAllBlockWord.graph_all_block_word v hv hz
  obtain ⟨N',w',s',hN',hq',hJ',hle',hw',hv5',hcarry',haligned',hs',hshift',hvert,hhoriz⟩ :=
    FixedGraphFieldMarkers.graph_field_markers v hv hz
  obtain ⟨N'',w'',s'',hN'',hq'',hJ'',hle'',hw'',hv5'',hcarry'',haligned'',hs'',hshift'',hdec,hdec2⟩ :=
    FixedGraphUniformDecoder.graph_uniform_decoder v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hNN : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N''
  let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
  let q : V := 1+v 0*(p 0:V)
  let C : V := q-v 1-v 2
  have hdecoder : ∀ h<N, UniformBandInputs.Inputs (8807*N) C (8807*h+4393) 4393 := by
    intro h hh
    have hi := BlockCyclicIndex.index N h 4393 hh (by norm_num)
    exact (hdec _ hi.1 hi.2).2.1
  refine ⟨N,W,s',hN,hq,hs',hshift',hW,hbound,?_⟩
  intro h hh
  have hj : cyc N h s'<N := cyc_lt hN _ _
  have hl : cyc N h 1<N := cyc_lt hN _ _
  obtain ⟨i,hi,hsi,hwi⟩ := hrows h hh
  obtain ⟨j,hj',hsj,hwj⟩ := hrows _ hj
  obtain ⟨l,hl',hsl,hwl⟩ := hrows _ hl
  have hver : ∀ u : ℕ, u<9 → ∀ k<8807*N, k%8807=((1013+u:ℕ):V) →
      dig 67 C (cyc (8807*N) k 30)=dig 67 C (cyc (8807*N) k (8807*s')) := by
    intro u hu k hk hp
    have he := hvert u (by omega) k hk hp
    rw [hshift'] at he
    exact he
  have hhor : ∀ u : ℕ, u<8 → ∀ k<8807*N, k%8807=((1065+u:ℕ):V) →
      dig 67 C (cyc (8807*N) k 62)=dig 67 C (cyc (8807*N) k 8849) := by
    intro u hu k hk hp
    exact hhoriz u (by omega) k hk hp
  exact ⟨i,j,l,hi,hj',hl',
    VerticalFieldBits.fields N C s' h i j hN hh hs' hver (hdecoder h hh) hwi (hdecoder _ hj) hwj,
    HorizontalFieldBits.fields N C h i l hN hh hhor (hdecoder h hh) hwi (hdecoder _ hl) hwl⟩
#print axioms FixedGraphFieldMatch.graph_field_match
end FixedGraphFieldMatch
