import DiophantineConsistency.CompactFieldCastBridge
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactLocalWord
open DiophantineConsistency CompactBitRotation CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactPartialBand
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry ArithmeticPackingBlocks
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
abbrev Quad := ℕ × ℕ × ℕ × ℕ

/-- Same recursion as the later Wang-table lookup, under a distinct namespace. -/
noncomputable def tabValue : List ℕ → ℕ → V → V
  | [], _, _ => 0
  | v :: vs, k, i =>
    if i = ORingStructure.numeral k then ORingStructure.numeral v else tabValue vs (k + 1) i

theorem tab_cast_aux (l : List ℕ) (k m : ℕ) :
    tabValue l k (((k + m : ℕ)) : V) = (l.getD m 0 : V) := by
  induction l generalizing k m with
  | nil => simp [tabValue]
  | cons v vs ih =>
    simp only [tabValue, numeral_eq_natCast_app, Nat.cast_inj]
    cases m with
    | zero => simp
    | succ m =>
      rw [if_neg (by omega)]
      have he : k + (m + 1) = (k + 1) + m := by omega
      rw [he, ih (k + 1) m]
      simp

theorem tab_cast (l : List ℕ) (m : ℕ) : tabValue l 0 (m : V) = (l.getD m 0 : V) := by
  simpa using tab_cast_aux (V := V) l 0 m

def field (f : Quad → ℕ) (i : V) : V := tabValue (Compact943Data.rows.map f) 0 i

theorem field_cast (f : Quad → ℕ) (hf : f (0,0,0,0)=0) (m : ℕ) :
    field f (m:V)=((f (Compact943Data.rows.toArray[m]?.getD (0,0,0,0))):V) := by
  dsimp only [field]
  rw [tab_cast, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : Compact943Data.rows[m]? <;> simp [h, hf]

structure Word (b : V → V) (N s : V) : Prop where
  pos : 0<N
  tile_lt : ∀ j<N, b j<943
  tile_ne : ∀ j<N, b j≠1
  marker : b 0=0
  east : ∀ j<N, ∀ j'<N, (j'+1)%N=j → field (fun t => t.2.2.1) (b j)=field (fun t => t.1) (b j')
  south : ∀ j<N, ∀ j'<N, (j'+s)%N=j → field (fun t => t.2.2.2) (b j)=field (fun t => t.2.1) (b j')

theorem graph_local_word (v : Fin 12 → V) (hv : ∀ j,0<v j)
    (hz : InternalZero (literal (fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ))) v) :
    let p := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N W s : V, 0<N ∧ q=Exp.exp ((67*8807)*N) ∧ s<N ∧
      ((R-67*(8807*N))/67)%(8807*N)=8807*s ∧
      Blocks 10 (OrbitRowWord.row C N 1) N W ∧ Word (OrbitRowWord.row C N 1) N s := by
  obtain ⟨N,W,s,hN,hq,hs,hshift,hW,hzero,hbound,hfields⟩ := FixedGraphAnchoredMatch.graph_anchored_match v hv hz
  have hm := CompactFieldCastBridge.lookup_matches field (fun f hf m => field_cast f hf m)
    (OrbitRowWord.row _ N 1) N s hN hfields
  refine ⟨N,W,s,hN,hq,hs,hshift,hW,?_⟩
  exact ⟨hN,fun j hj => (hbound j hj).1,fun j hj => (hbound j hj).2,hzero,hm.1,hm.2⟩
#print axioms CompactLocalWord.field_cast
#print axioms CompactLocalWord.graph_local_word
end CompactLocalWord
