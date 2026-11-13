import P64QCube77Unit

/-! Draft: the four non-first residuals of an actual 78 zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCube77OldFacts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open P64QCubeMap
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem residuals (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀i,0<v i)
    (hz : InternalZero (P64QCube78.graph (fun j => (p j:ℤ))).output v) :
    let g := P64QCube78.graph (fun j => (p j:ℤ))
    let z : Fin 14 → DiffRing V := fun i => ι (v i)
    g.A0.evalRing z=1 ∧ g.M.evalRing z=0 ∧ g.W.evalRing z=0 ∧
      g.Na.evalRing z=1 ∧ g.Lt.evalRing z=0 := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let w : Fin 14 → V := lift p v
  let first : DiffRing V := (P64QCube78.graph pp).A0.evalRing z
  have hf : first=1 := P64QCube78GraphSplit.first_eq_one p v hv hz
  have hs : first*first+(P64QCube78.graph pp).M.evalRing z*(P64QCube78.graph pp).M.evalRing z+
      (P64QCube78.graph pp).W.evalRing z*(P64QCube78.graph pp).W.evalRing z+
      (P64QCube78.graph pp).Na.evalRing z*(P64QCube78.graph pp).Na.evalRing z+
      (P64QCube78.graph pp).Lt.evalRing z*(P64QCube78.graph pp).Lt.evalRing z=2 := by
    have hh := hz
    rw [internalZero_iff,P64QCube78GraphSplit.output_shape] at hh
    simp only [Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_sub,Expr.evalRing_ofNat] at hh
    exact sub_eq_zero.mp hh
  have hs1 : (0:DiffRing V)*0+(P64QCube78.graph pp).M.evalRing z*(P64QCube78.graph pp).M.evalRing z+
      (P64QCube78.graph pp).W.evalRing z*(P64QCube78.graph pp).W.evalRing z+
      (P64QCube78.graph pp).Na.evalRing z*(P64QCube78.graph pp).Na.evalRing z+
      (P64QCube78.graph pp).Lt.evalRing z*(P64QCube78.graph pp).Lt.evalRing z=1 := by
    rw [hf] at hs
    linarith
  rw [P64QCube78GraphSplit.main_same pp,P64QCube78GraphSplit.strong_same pp,
    P64QCube78GraphSplit.auxiliary_same pp,P64QCube78GraphSplit.transport_same pp,
    ←P64QCubeBinding.main pp z,←P64QCubeBinding.strong pp z,
    ←P64QCubeBinding.auxiliary pp z,←P64QCubeBinding.transport pp z,←P64QCubeMap.lift_cast p v] at hs1
  obtain ⟨_,hm,hw,hn,hl⟩ := P64NormFirstReplacement.residuals p w (P64QCubeMap.lift_pos p v hv) 0 hs1
  rw [internalZero_iff,P64QCubeMap.lift_cast p v,P64QCubeBinding.main pp z,
    ←P64QCube78GraphSplit.main_same pp] at hm
  rw [internalZero_iff,P64QCubeMap.lift_cast p v,P64QCubeBinding.strong pp z,
    ←P64QCube78GraphSplit.strong_same pp] at hw
  rw [P64QCubeMap.lift_cast p v,P64QCubeBinding.auxiliary pp z,
    ←P64QCube78GraphSplit.auxiliary_same pp] at hn
  rw [internalZero_iff,P64QCubeMap.lift_cast p v,P64QCubeBinding.transport pp z,
    ←P64QCube78GraphSplit.transport_same pp] at hl
  exact ⟨hf,hm,hw,hn,hl⟩

#print axioms P64QCube77OldFacts.residuals
end P64QCube77OldFacts
