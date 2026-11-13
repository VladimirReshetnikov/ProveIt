import P64QCubeBinding
import P64NormFirstReplacement

/-! Draft: positive-zero equivalence for the P64 q³ quotient graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCubeExistence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open P64QCubeMap P64QCubeBinding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem candidate_zero_iff (p : Fin 4 → ℤ) (v : Fin 14 → V) :
    InternalZero (P64QCube81.graph p).output v ↔
      let z : Fin 14 → DiffRing V := fun j => ι (v j)
      (P64QCube81.graph p).A0.evalRing z*(P64QCube81.graph p).A0.evalRing z+
      (P64QCube81.graph p).M.evalRing z*(P64QCube81.graph p).M.evalRing z+
      (P64QCube81.graph p).W.evalRing z*(P64QCube81.graph p).W.evalRing z+
      (P64QCube81.graph p).Na.evalRing z*(P64QCube81.graph p).Na.evalRing z+
      (P64QCube81.graph p).Lt.evalRing z*(P64QCube81.graph p).Lt.evalRing z=1 := by
  rw [output_shape,internalZero_iff]
  simp only [Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_sub,Expr.evalRing_ofNat,Nat.cast_one]
  exact sub_eq_zero

theorem exists_old_of_new (p : Fin 4 → ℕ)
    (h : ∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube81.graph (fun j => (p j:ℤ))).output v) :
    ∃w : Fin 14 → V, (∀i,0<w i) ∧
      InternalZero (P64Graph.graph (fun j => (p j:ℤ))).output w := by
  obtain ⟨v,hv,hz⟩ := h
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun j => ι (v j)
  let w : Fin 14 → V := lift p v
  let first : DiffRing V := (P64QCube81.graph pp).A0.evalRing z
  have hs := (candidate_zero_iff pp v).mp hz
  change first*first+(P64QCube81.graph pp).M.evalRing z*(P64QCube81.graph pp).M.evalRing z+
      (P64QCube81.graph pp).W.evalRing z*(P64QCube81.graph pp).W.evalRing z+
      (P64QCube81.graph pp).Na.evalRing z*(P64QCube81.graph pp).Na.evalRing z+
      (P64QCube81.graph pp).Lt.evalRing z*(P64QCube81.graph pp).Lt.evalRing z=1 at hs
  rw [←main pp z,←strong pp z,←auxiliary pp z,←transport pp z,←lift_cast p v] at hs
  obtain ⟨hf,hm,hw,hn,hl⟩ := P64NormFirstReplacement.residuals p w (lift_pos p v hv) first hs
  have ha : InternalZero (P64Graph.graph pp).A0 w := by
    rw [internalZero_iff,lift_cast p v,P64QCubeBinding.first pp z]
    change (((pp 0:ℤ):DiffRing V)*z 0+1)*(((pp 0:ℤ):DiffRing V)*z 0+1)*
      (((pp 0:ℤ):DiffRing V)*z 0+1)*
      ((((pp 0:ℤ):DiffRing V)*z 0+1)*(((pp 0:ℤ):DiffRing V)*z 0+1)*
        (((pp 0:ℤ):DiffRing V)*z 0+1))*first=0
    rw [hf]
    ring
  refine ⟨w,lift_pos p v hv,?_⟩
  apply (P64Graph.zero_iff pp w).mpr
  rw [internalZero_iff] at ha hm hw hl
  change (P64Graph.graph pp).M.evalRing (fun j => ι (w j))=0 at hm
  change (P64Graph.graph pp).W.evalRing (fun j => ι (w j))=0 at hw
  change (P64Graph.graph pp).Na.evalRing (fun j => ι (w j))=1 at hn
  change (P64Graph.graph pp).Lt.evalRing (fun j => ι (w j))=0 at hl
  dsimp only
  rw [ha,hm,hw,hn,hl]
  norm_num

theorem exists_new_of_old (p : Fin 4 → ℕ)
    (h : ∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64Graph.graph (fun j => (p j:ℤ))).output v) :
    ∃w : Fin 14 → V, (∀i,0<w i) ∧
      InternalZero (P64QCube81.graph (fun j => (p j:ℤ))).output w := by
  obtain ⟨v,hv,hz⟩ := h
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  obtain ⟨ha,hm,hw,hn,hl⟩ := P64Norm.residuals p v hv hz
  obtain ⟨s,hs,hlift⟩ := quotient_of_first_zero p v hv ha
  let w : Fin 14 → V := Function.update v 7 s
  let z : Fin 14 → DiffRing V := fun j => ι (w j)
  have hwpos : ∀i,0<w i := by
    intro i
    by_cases hi : i=7
    · subst i; simpa [w] using hs
    · simpa [w,hi] using hv i
  have heval : (P64Graph.graph pp).A0.evalRing (liftRing pp z)=0 := by
    rw [←lift_cast p w,hlift]
    exact (internalZero_iff _ _).mp ha
  rw [first pp z] at heval
  let q : V := (p 0:V)*w 0+1
  have hq : 0<q := by dsimp [q]; simp
  have hq' : (0:DiffRing V)<ι q := by rw [←map_zero ι,ι_lt_ι]; exact hq
  have hq3 : (0:DiffRing V)<ι q*ι q*ι q := mul_pos (mul_pos hq' hq') hq'
  have hq6 : (ι q : DiffRing V)*ι q*ι q*(ι q*ι q*ι q)≠0 := ne_of_gt (mul_pos hq3 hq3)
  have hanew : (P64QCube81.graph pp).A0.evalRing z=0 := by
    have hc : (ι q : DiffRing V)*ι q*ι q*(ι q*ι q*ι q)*
        (P64QCube81.graph pp).A0.evalRing z=0 := by
      simpa only [q,z,pp,P64Root.cast_nat,map_add,map_mul,map_one] using heval
    exact (mul_eq_zero.mp hc).resolve_left hq6
  have hm' := (internalZero_iff _ _).mp hm
  have hw' := (internalZero_iff _ _).mp hw
  have hl' := (internalZero_iff _ _).mp hl
  rw [←hlift,lift_cast p w,main pp z] at hm'
  rw [←hlift,lift_cast p w,strong pp z] at hw'
  rw [←hlift,lift_cast p w,auxiliary pp z] at hn
  rw [←hlift,lift_cast p w,transport pp z] at hl'
  refine ⟨w,hwpos,?_⟩
  apply (candidate_zero_iff pp w).mpr
  change (P64QCube81.graph pp).A0.evalRing z*(P64QCube81.graph pp).A0.evalRing z+
      (P64QCube81.graph pp).M.evalRing z*(P64QCube81.graph pp).M.evalRing z+
      (P64QCube81.graph pp).W.evalRing z*(P64QCube81.graph pp).W.evalRing z+
      (P64QCube81.graph pp).Na.evalRing z*(P64QCube81.graph pp).Na.evalRing z+
      (P64QCube81.graph pp).Lt.evalRing z*(P64QCube81.graph pp).Lt.evalRing z=1
  rw [hanew,hm',hw',hn,hl']
  norm_num

theorem positive_zero_iff (p : Fin 4 → ℕ) :
    (∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube81.graph (fun j => (p j:ℤ))).output v) ↔
    (∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64Graph.graph (fun j => (p j:ℤ))).output v) :=
  ⟨exists_old_of_new p,exists_new_of_old p⟩

#print axioms P64QCubeExistence.candidate_zero_iff
#print axioms P64QCubeExistence.exists_old_of_new
#print axioms P64QCubeExistence.exists_new_of_old
#print axioms P64QCubeExistence.positive_zero_iff
end P64QCubeExistence
