import Model69Growth
import Model69Transport
import DiophantineConsistency.ArithmeticPellFirstIndex

/-! Conditional model-level extraction of positive and divisible transport
from the scalar parent equation and supplied power/population estimates.
Deriving these estimates from the actual fixed-port zero is still separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Model69Outer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPellFirstIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem outer_of_scalar_data (beta K MC MF J F alpha z w s u count : V)
    (hbeta : 0<beta) (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha)
    (hz : 0<z) (hw : 0<w) (hs : 0<s) (hMC : MC<beta) (hMF : MF<2*beta) :
    let q:=beta*J+1
    let R:=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
    let C:=q-F-alpha
    (K+w)*q+q=(K+w)*(F+alpha)+F+z*(q-1)+1 →
    q=Exp.exp u → w*q=Exp.exp R → count≤R → 3*u+2≤count →
    ∃ G : V, 0<C ∧ 0<G ∧ beta*J∣G ∧ (K+w)*C=F+G := by
  dsimp only
  intro ht hq hX hcount hpop
  let q:=beta*J+1
  let R:=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
  let C:=q-F-alpha
  have hgap : 0<C := (scalar_window q beta K MC MF J F alpha z w s
    hbeta hJ hF halpha hz hw hs hMC hMF rfl ht).1
  have hsumlt : F+alpha<q := tsub_pos_iff_lt.mp (by simpa only [C,tsub_tsub] using hgap)
  have hsum : F+alpha+C=q := by
    dsimp [C]
    rw [tsub_tsub]
    exact add_tsub_cancel_of_le (le_of_lt hsumlt)
  have hFq : F<q := lt_of_le_of_lt (by simp) hsumlt
  have hqw : q≤w := Model69Growth.radix_le_multiplier_of_population u R count q w hq hX hcount hpop
  obtain ⟨hG,hdiv,heq⟩ := Model69Transport.positive_divisible_transport (beta*J) q K w F alpha C z
    rfl hz hgap hsum hFq hqw ht
  exact ⟨beta*J*(z-1),hgap,hG,hdiv,heq⟩
end Model69Outer
#print axioms Model69Outer.outer_of_scalar_data
