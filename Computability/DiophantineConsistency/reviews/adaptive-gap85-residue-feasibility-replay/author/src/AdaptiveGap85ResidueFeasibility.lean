import DiophantineConsistency.AdaptiveGap85ActualJoint
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ResidueFeasibility
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveGap85Literal AdaptiveGap85ActualJoint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Exact feasibility of the zero joint-residue constraint, without asserting
that these coordinates extend to a zero or are reachable by any shifts. -/
theorem residue_gap_iff (b A : V) (hb : 0<b) :
    (∃ F C : V, 0<F ∧ 0<C ∧ F+C<1+b ∧ F%b=(C*A)%b) ↔ ¬b∣A := by
  constructor
  · rintro ⟨F,C,hF,hC,hgap,hmod⟩ hA
    have hCA : b∣C*A := dvd_mul_of_dvd_right hA C
    have hFdiv : b∣F := mod_eq_zero_iff_dvd.mp (hmod.trans (mod_eq_zero_iff_dvd.mpr hCA))
    have hbF : b≤F := Arithmetic.le_of_dvd hF hFdiv
    have hC1 : 1≤C := pos_iff_one_le.mp hC
    have hle : 1+b≤F+C := by
      calc
        1+b=b+1 := by ring
        _≤F+C := add_le_add hbF hC1
    exact (not_le_of_gt hgap) hle
  · intro hA
    have hrne : A%b≠0 := by
      intro he
      exact hA (mod_eq_zero_iff_dvd.mp he)
    have hrpos : 0<A%b := pos_iff_ne_zero.mpr hrne
    have hrlt : A%b<b := mod_lt A hb
    refine ⟨A%b,1,hrpos,by simp,?_,?_⟩
    · have hh := add_lt_add_of_lt_of_le hrlt (le_refl (1:V))
      simpa only [add_comm] using hh
    · rw [one_mul,mod_eq_self_of_lt hrlt]

/-- Any positive actual zero which itself meets the reverse gap necessarily
has a first transport coefficient nondivisible by b. -/
theorem normalized_actual_zero_coefficient (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v)
    (hgap : v 1+v 2<1+v 0*(p 0:V)) :
    ¬ v 0*(p 0:V) ∣ v 6+(p 1:V) := by
  have hmod := actual_zero_transport_mod p v hb hv hz
  exact (residue_gap_iff _ _ (mul_pos (hv 0) hb)).mp
    ⟨v 1,v 2,hv 1,hv 2,hgap,hmod⟩
end DiophantineConsistency.AdaptiveGap85ResidueFeasibility
