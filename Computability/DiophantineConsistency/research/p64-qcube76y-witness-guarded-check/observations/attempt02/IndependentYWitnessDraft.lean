import IndependentYGraphDraft
import P64QCube76YBinding

/-! Unchecked draft: conditional model witness maps using the ring binding. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace IndependentYWitnessDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_magnitude (r : DiffRing V) (hr : r≠0) :
    ∃y : V, 0<y ∧ (ι y:DiffRing V)*ι y=r*r := by
  rcases ModelDifferenceRing.nonneg_or_nonpos r with ⟨y,hy⟩ | ⟨y,hy⟩
  · have hn : y≠0 := by
      intro h
      apply hr
      rw [hy,h,map_zero]
    have hp : 0<y := by
      by_contra h
      exact hn (le_antisymm (le_of_not_gt h) (Arithmetic.zero_le _))
    exact ⟨y,hp,by rw [hy]⟩
  · have hn : y≠0 := by
      intro h
      apply hr
      rw [hy,h,map_zero,neg_zero]
    have hp : 0<y := by
      by_contra h
      exact hn (le_antisymm (le_of_not_gt h) (Arithmetic.zero_le _))
    exact ⟨y,hp,by rw [hy,neg_mul_neg]⟩

theorem positive_difference (r : DiffRing V) (y : V) (h : r<ι y) :
    ∃e : V, 0<e ∧ r+ι e=ι y := by
  have hp : (0:DiffRing V)<ι y-r := sub_pos.mpr h
  obtain ⟨e,he⟩ := nonneg_iff.mp (le_of_lt hp)
  have hepos : 0<e := by
    apply ι_lt_ι.mp
    rw [map_zero,←he]
    exact hp
  refine ⟨e,hepos,?_⟩
  rw [←he]
  ring

theorem old_to_new_conditional (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀i,0<v i)
    (hz : InternalZero (P64QCube77.graph (fun j => (p j:ℤ))).output v)
    (hne : P64QCube76YBinding.oldV (fun j => (p j:ℤ)) (fun i => ι (v i)) + ι (v 12) ≠ 0) :
    ∃w : Fin 14 → V, (∀i,0<w i) ∧
      InternalZero (P64QCube76Y.graph (fun j => (p j:ℤ))).output w := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let signed : DiffRing V := P64QCube76YBinding.oldV pp z+ι (v 12)
  obtain ⟨y,hy,hysq⟩ := positive_magnitude signed hne
  let w : Fin 14 → V := Function.update v 12 y
  have hw : ∀i,0<w i := by
    intro i
    by_cases hi : i=12
    · subst i; simpa [w] using hy
    · simpa [w,hi] using hv i
  have hcast : (fun i => (ι (w i):DiffRing V)) =
      Function.update (P64QCube76YBinding.liftRing pp z) 12 (ι y) := by
    funext i
    by_cases hi : i=12
    · subst i; simp [w,P64QCube76YBinding.liftRing]
    · simp [w,P64QCube76YBinding.liftRing,hi,z]
  have hs : (ι y:DiffRing V)*ι y =
      P64QCube76YBinding.liftRing pp z 12*P64QCube76YBinding.liftRing pp z 12 := by
    simpa [P64QCube76YBinding.liftRing,signed,z] using hysq
  refine ⟨w,hw,?_⟩
  rw [internalZero_iff] at hz ⊢
  change (P64QCube77.graph pp).output.evalRing z=0 at hz
  rw [hcast,P64QCube76YBinding.output_same_square pp _ (ι y) hs,
    P64QCube76YBinding.output pp z]
  exact hz

theorem new_to_old_conditional (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀i,0<v i)
    (hz : InternalZero (P64QCube76Y.graph (fun j => (p j:ℤ))).output v)
    (hlt : P64QCube76YBinding.oldV (fun j => (p j:ℤ)) (fun i => ι (v i)) < ι (v 12)) :
    ∃w : Fin 14 → V, (∀i,0<w i) ∧
      InternalZero (P64QCube77.graph (fun j => (p j:ℤ))).output w := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  obtain ⟨e,he,heq⟩ := positive_difference (P64QCube76YBinding.oldV pp z) (v 12) hlt
  let w : Fin 14 → V := Function.update v 12 e
  have hw : ∀i,0<w i := by
    intro i
    by_cases hi : i=12
    · subst i; simpa [w] using he
    · simpa [w,hi] using hv i
  let zw : Fin 14 → DiffRing V := fun i => ι (w i)
  have hV : P64QCube76YBinding.oldV pp zw = P64QCube76YBinding.oldV pp z := by
    simp [P64QCube76YBinding.oldV,zw,w,z]
  have hcast : P64QCube76YBinding.liftRing pp zw=z := by
    funext i
    by_cases hi : i=12
    · subst i; simp [P64QCube76YBinding.liftRing,hV,zw,w,z,heq]
    · simp [P64QCube76YBinding.liftRing,zw,w,z,hi]
  refine ⟨w,hw,?_⟩
  rw [internalZero_iff] at hz ⊢
  change (P64QCube76Y.graph pp).output.evalRing z=0 at hz
  change (P64QCube77.graph pp).output.evalRing zw=0
  rw [←P64QCube76YBinding.output pp zw,hcast]
  exact hz

#print axioms IndependentYWitnessDraft.positive_magnitude
#print axioms IndependentYWitnessDraft.positive_difference
#print axioms IndependentYWitnessDraft.old_to_new_conditional
#print axioms IndependentYWitnessDraft.new_to_old_conditional
end IndependentYWitnessDraft
