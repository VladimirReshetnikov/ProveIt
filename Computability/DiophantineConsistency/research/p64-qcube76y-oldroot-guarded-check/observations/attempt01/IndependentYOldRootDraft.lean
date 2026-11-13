import P64QCube77Existence
import P64QCube76YBinding

/-! Unchecked draft: nonzero old signed auxiliary root at an actual 77 zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace IndependentYOldRootDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open P64QCubeMap P64Graph
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Generic discrete-ring argument: if `A≥2`, the auxiliary norm excludes y=0. -/
theorem nonzero_of_aux_norm (A v y : DiffRing V)
    (hA : 2≤A) (haux : A*(v*v-y*y)+y*y=1) : y≠0 := by
  intro hy
  rw [hy] at haux
  simp only [mul_zero,sub_zero,add_zero] at haux
  have hunit := DiscreteOrderedRingFacts.eq_one_or_neg_one_of_mul_eq_one
    ModelArithmetic.model_discrete haux
  rcases hunit with h | h <;> linarith

/-- Intended actual-graph specialization; all imports and tactics are unchecked. -/
theorem old_root_ne_zero (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀j,0<v j)
    (hz : InternalZero (P64QCube77.graph (fun j => (p j:ℤ))).output v) :
    P64QCube76YBinding.oldV (fun j => (p j:ℤ)) (fun j => ι (v j)) + ι (v 12) ≠ 0 := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun j => ι (v j)
  let w : Fin 14 → V := lift p v
  let zw : Fin 14 → DiffRing V := fun j => ι (w j)
  have hwpos : ∀j,0<w j := lift_pos p v hv
  have hz78 := (P64QCube77Existence.same_zero_iff p v hv).mp hz
  obtain ⟨_,_,hw,hn,_⟩ := P64QCube77OldFacts.residuals p v hv hz78
  change (P64QCube78.graph pp).W.evalRing z=0 at hw
  change (P64QCube78.graph pp).Na.evalRing z=1 at hn
  rw [P64QCube78GraphSplit.strong_same pp,←P64QCubeBinding.strong pp z,
    ←P64QCubeMap.lift_cast p v] at hw
  rw [P64QCube78GraphSplit.auxiliary_same pp,←P64QCubeBinding.auxiliary pp z,
    ←P64QCubeMap.lift_cast p v] at hn
  change (P64Graph.graph pp).W.evalRing zw=0 at hw
  change (P64Graph.graph pp).Na.evalRing zw=1 at hn
  rw [P64Graph.W_eval] at hw
  rw [P64Graph.Na_eval] at hn
  have hc3 : (3:V) ≤ (w 10+w 11)*w 7+w 10 := by
    have hk : (2:V)≤w 10+w 11 := by
      simpa [one_add_one_eq_two] using add_le_add
        (pos_iff_one_le.mp (hwpos 10)) (pos_iff_one_le.mp (hwpos 11))
    calc
      (3:V)=2*1+1 := by norm_num
      _≤(w 10+w 11)*w 7+w 10 := add_le_add
        (mul_le_mul hk (pos_iff_one_le.mp (hwpos 7)) (by norm_num) (Arithmetic.zero_le _))
        (pos_iff_one_le.mp (hwpos 10))
  have hc : (3:DiffRing V)≤(P64Graph.vals pp zw).c := by
    rw [P64Root.c_c]
    have h := (ι_le_ι (V:=V)).mpr hc3
    rwa [map_ofNat] at h
  have hi : (1:DiffRing V)≤zw 5 := ModelArithmetic.model_discrete _ (ModelArithmetic.ι_pos (hwpos 5))
  have hcc : (2:DiffRing V)≤(P64Graph.vals pp zw).c*(P64Graph.vals pp zw).c := by nlinarith only [hc]
  have hI : (2:DiffRing V)≤zw 5*((P64Graph.vals pp zw).c*(P64Graph.vals pp zw).c) := by
    have h := mul_le_mul hi hcc (by norm_num) (by linarith)
    simpa using h
  have hA : (2:DiffRing V)≤(P64Graph.vals pp zw).Aaux := by
    have hAeq : (P64Graph.vals pp zw).Aaux =
        (zw 5*((P64Graph.vals pp zw).c*(P64Graph.vals pp zw).c))*
        (zw 5*((P64Graph.vals pp zw).c*(P64Graph.vals pp zw).c)) := (sub_eq_zero.mp hw).symm
    rw [hAeq]
    nlinarith only [hI]
  have hy : (P64Graph.vals pp zw).y = P64QCube76YBinding.oldV pp z + ι (v 12) := by
    rw [P64Root.c_y]
    have hV : (P64Graph.vals pp zw).V = P64QCube76YBinding.oldV pp z := by
      rw [P64QCubeMap.lift_cast p v]
      simp [P64Graph.vals,P64QCubeMap.liftRing,P64QCube76YBinding.oldV]
    rw [hV]
    simp [zw,w,lift]
  change P64QCube76YBinding.oldV pp z + ι (v 12) ≠ 0
  rw [←hy]
  exact nonzero_of_aux_norm _ _ _ hA hn

#print axioms IndependentYOldRootDraft.nonzero_of_aux_norm
#print axioms IndependentYOldRootDraft.old_root_ne_zero
end IndependentYOldRootDraft
