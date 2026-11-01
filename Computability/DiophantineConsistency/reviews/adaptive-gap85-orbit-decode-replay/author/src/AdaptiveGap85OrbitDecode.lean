import DiophantineConsistency.AdaptiveGap85WeightedOrbit
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85OrbitDecode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveGap85JointResidue AdaptiveGap85WeightedOrbit
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A normalized endpoint has exactly the quotient and remainder of the
initial weighted code. No endpoint or shift path is constructed here. -/
theorem orbit_gap_decode (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hv : ∀j,0<v j) (h : Relation.ReflTransGen (LiteralStep p) v w)
    (hg : w 1+w 2<1+w 0*(p 0:V)) :
    let q := 1+v 0*(p 0:V)
    let N := (v 9+v 7*(v 9+v 10))*(v 7*(q*q))
    let R := (q*v 1+v 2)%N
    w 1=R/q ∧ w 2=R%q := by
  let q : V := 1+v 0*(p 0:V)
  let N : V := (v 9+v 7*(v 9+v 10))*(v 7*(q*q))
  let R : V := (q*v 1+v 2)%N
  have hq : 0<q := by dsimp [q]; simp
  have h0 := (literal_orbit_weight p v w h).1
  have hg' : w 1+w 2<q := by simpa only [h0] using hg
  have hc : w 2<q := lt_of_le_of_lt (by simp : w 2≤w 1+w 2) hg'
  have he : q*w 1+w 2=R := orbit_gap_code p v w hv h hg
  have hm := congrArg (fun z : V => z%q) he
  have ht : q*w 1+w 2=w 2+q*w 1 := by ring
  rw [ht,mod_add_mul' _ _ hq,mod_eq_self_of_lt hc] at hm
  have hdiv : q*w 1=q*(R/q) := by
    apply add_right_cancel (b:=R%q)
    calc
      q*w 1+R%q=q*w 1+w 2 := by rw [hm]
      _=R := he
      _=q*(R/q)+R%q := (div_add_mod R q).symm
  exact ⟨mul_left_cancel₀ (ne_of_gt hq) hdiv,hm⟩
/-- A positive normalizing endpoint can exist only when the explicitly
decoded candidate itself is positive and satisfies the reverse gap. -/
theorem orbit_positive_gap_candidate (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hv : ∀j,0<v j) (h : Relation.ReflTransGen (LiteralStep p) v w)
    (hwF : 0<w 1) (hwC : 0<w 2)
    (hg : w 1+w 2<1+w 0*(p 0:V)) :
    let q := 1+v 0*(p 0:V)
    let N := (v 9+v 7*(v 9+v 10))*(v 7*(q*q))
    let R := (q*v 1+v 2)%N
    0<R/q ∧ 0<R%q ∧ R/q+R%q<q := by
  have h0 := (literal_orbit_weight p v w h).1
  have hdecode := orbit_gap_decode p v w hv h hg
  dsimp only at hdecode ⊢
  obtain ⟨hF,hC⟩ := hdecode
  refine ⟨by rw [←hF]; exact hwF,by rw [←hC]; exact hwC,?_⟩
  rw [←hF,←hC,←h0]
  exact hg
end DiophantineConsistency.AdaptiveGap85OrbitDecode
