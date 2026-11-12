import DiophantineConsistency.Compact44.P72Root
import DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011
import DiophantineConsistency.ArithmeticGcdNormalization

/-! Source-only signed first-root quotient fact. No graph, provider,
Lean elaboration or endpoint result is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.QCubeQuotientFactsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticSignedPairs ArithmeticAdaptiveQuotients2011
open ArithmeticAdaptiveFirstDivisibility2011 ArithmeticGcdNormalization
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A squared 86-style signed first root forces a positive q³ quotient of Y
and gives a positive natural root of D, without choosing the root sign. -/
theorem quotient_and_root (b Y P r D : V) (hb : 0<b) (hY : 0<Y) (hD : 0<D)
    (hfield : let q := 1+b; let Q := q*(q*q); let M := Q*b
      (ι (M*P+b*Y)-ι (M*r))*(ι (M*P+b*Y)-ι (M*r))=(ι M*ι M)*ι D) :
    let q := 1+b
    let Q := q*(q*q)
    ∃ s tau : V, 0<s ∧ Y=Q*s ∧ 0<tau ∧ tau*tau=D := by
  let q : V := 1+b
  let Q : V := q*(q*q)
  let M : V := Q*b
  let z := (M*P+b*Y,M*r)
  have hq : 0<q := by dsimp [q]; simp
  have hQ : 0<Q := by dsimp [Q]; exact mul_pos hq (mul_pos hq hq)
  have hM : 0<M := mul_pos hQ hb
  have hsq : magnitude z*magnitude z=M*M*D := by
    apply ι_injective
    simp only [map_mul,P72Root.ι_magnitude_sq]
    exact hfield
  obtain ⟨tau,ht,hn⟩ := scaled_quotient M (magnitude z) D hM hsq
  have htpos : 0<tau := pos_of_mul_pos_left (by rw [hn]; exact hD) (Arithmetic.zero_le tau)
  have hQdiv : Q∣magnitude z := by
    refine ⟨b*tau,?_⟩
    rw [ht]
    dsimp [M]
    ring
  have hmod := magnitude_mod z Q hQ hQdiv
  change (M*P+b*Y)%Q=(M*r)%Q at hmod
  have hleft : M*P+b*Y=b*Y+Q*(b*P) := by dsimp [M]; ring
  have hright : M*r=Q*(b*r) := by dsimp [M]; ring
  have hzero : (Q*(b*r))%Q=0 := by rw [mul_comm]; exact mod_mul_self_left _ _
  rw [hleft,hright,mod_add_mul' _ _ hQ,hzero] at hmod
  have hby : Q∣b*Y := mod_eq_zero_iff_dvd.mp hmod
  have hunit : Bez b Q 1 := by
    refine ⟨q*q+q+1,0,0,1,?_⟩
    dsimp [q,Q]
    ring
  obtain ⟨s,hs⟩ := unit_certificate_cancel hunit hby
  have hspos : 0<s := by
    apply pos_iff_ne_zero.mpr
    intro hs0
    have : Y=0 := by rw [hs,hs0,mul_zero]
    exact (ne_of_gt hY) this
  exact ⟨s,tau,hspos,hs,htpos,hn⟩

end DiophantineConsistency.QCubeQuotientFactsDraft

#print axioms DiophantineConsistency.QCubeQuotientFactsDraft.quotient_and_root
