import Absorb88Gap
import Absorb88ModelReflection
import Absorb88Inverse

/-! Select a positive 88 zero with enough room for the inverse map. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Absorb88Select
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb88 Absorb88First
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem select (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v)
    (hbound : (v 1+v 2)*((p 1:V)+v 5)+v 1 < (1+v 0*(p 0:V))*((p 1:V)+v 5)) :
    ∃w : Fin 12 → V, (∀j,0<w j) ∧ Absorb88Inverse.threshold p w<w 7 ∧
      InternalZero (graph (integerPorts p)).output w := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let k : V := v 8+v 9
  let Q : V := (X*Y)*Y
  let ell : V := (X*Y)*(Y*k)
  let A : V := (p 1:V)+v 5
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1
  let Bt : V := q*(Bp-Bn)
  obtain ⟨first,hfirst,hBtpos,hnorm,hbranch⟩ := Absorb88Signs.first_branches p v hb hv hz hbound
  have hn : first*first=1+ell*(ell+k) := by
    calc
      first*first=1+Q*(Q+1)*k*k := hnorm
      _=1+ell*(ell+k) := by dsimp [Q,ell]; ring
  rcases hbranch with hp | hm
  · exact ⟨v,hv,Absorb88Gap.positive_gap p v first hb hv hz hbound hn hBtpos hp,hz⟩
  · let w := Absorb88ModelReflection.reflected v first
    have hwz : InternalZero (graph (integerPorts p)).output w :=
      Absorb88ModelReflection.negative_branch_preserves p v first hbound hm hz
    have hwv : ∀j,0<w j := by
      intro j
      by_cases hj : j=7
      · subst j
        simpa [w,Absorb88ModelReflection.reflected] using add_pos (hv 7) (mul_pos (by norm_num : (0:V)<2) hfirst)
      · simpa [w,Absorb88ModelReflection.reflected,hj] using hv j
    have hp' : b*(v 7+2*first)=(1+k*b)*Bt+b*first := by
      calc
        _=(b*(v 7)+b*first)+b*first := by ring
        _=(1+k*b)*Bt+b*first := by rw [hm]
    have hboundw : (w 1+w 2)*((p 1:V)+w 5)+w 1 < (1+w 0*(p 0:V))*((p 1:V)+w 5) := by
      simpa [w,Absorb88ModelReflection.reflected] using hbound
    have hgap : Absorb88Inverse.threshold p w<w 7 := by
      apply Absorb88Gap.positive_gap p w first hb hwv hwz hboundw
      · simpa [w,Absorb88ModelReflection.reflected] using hn
      · simpa [w,Absorb88ModelReflection.reflected] using hBtpos
      · simpa [w,Absorb88ModelReflection.reflected] using hp'
    exact ⟨w,hwv,hgap,hwz⟩

#print axioms Absorb88Select.select
end Absorb88Select
