import DiophantineConsistency.AdaptiveGap85JointResidue
set_option autoImplicit false
noncomputable section
/-! Conditional joint-residue orbit obstruction; no actual zero is asserted. -/
namespace DiophantineConsistency.AdaptiveGap85JointMinusOne
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveGap85JointResidue
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem joint_sum_mod (b A : V) (p r : V × V) (hb : 0<b)
    (hA : b∣A+1) (h : Joint b A p r) : (r.1+r.2)%b=(p.1+p.2)%b := by
  obtain ⟨k,hk⟩ := hA
  obtain ⟨u,v,huv⟩ := h
  have he : (r.1+r.2)+b*(k*p.2+u)=(p.1+p.2)+b*(k*r.2+v) := by
    calc
      (r.1+r.2)+b*(k*p.2+u) = (r.1+r.2)+(b*k)*p.2+b*u := by ring
      _ = (r.1+A*p.2+b*u)+(p.2+r.2) := by rw [←hk]; ring
      _ = (p.1+A*r.2+b*v)+(p.2+r.2) := by rw [huv]
      _ = (p.1+p.2)+(b*k)*r.2+b*v := by rw [←hk]; ring
      _ = (p.1+p.2)+b*(k*r.2+v) := by ring
  have hm := congrArg (fun x : V => x%b) he
  simpa only [mod_add_mul' _ _ hb] using hm

theorem orbit_blocks_minus_one (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hb : 1<v 0*(p 0:V))
    (h : Relation.ReflTransGen (LiteralStep p) v w)
    (hA : v 0*(p 0:V)∣(v 6+(p 1:V)*(1+v 0*(p 0:V)))+1)
    (hscore : (v 1+v 2)%(v 0*(p 0:V))=1)
    (hF : 0<w 1) (hC : 0<w 2) : ¬ w 1+w 2<1+w 0*(p 0:V) := by
  let b : V := v 0*(p 0:V)
  let A : V := v 6+(p 1:V)*(1+b)
  change 1<b at hb
  change b∣A+1 at hA
  change (v 1+v 2)%b=1 at hscore
  have hb0 : 0<b := lt_trans (by norm_num) hb
  have ho := literal_orbit_joint p v w h
  have hm : (w 1+w 2)%b=(v 1+v 2)%b := joint_sum_mod b A (v 1,v 2) (w 1,w 2) hb0 hA ho.2.2
  rw [hscore] at hm
  intro hgap
  rw [ho.1] at hgap
  change w 1+w 2<1+b at hgap
  have hle : w 1+w 2≤b := lt_succ_iff_le.mp (by simpa [add_comm] using hgap)
  have htwo : (1:V)+1≤w 1+w 2 := by
    have hf : 1≤w 1 := pos_iff_one_le.mp hF
    have hc : 1≤w 2 := pos_iff_one_le.mp hC
    exact add_le_add hf hc
  rcases lt_or_eq_of_le hle with hl | he
  · rw [mod_eq_self_of_lt hl] at hm
    rw [hm] at htwo
    exact (by norm_num : ¬(1:V)+1≤1) htwo
  · rw [he,mod_self] at hm
    exact (by norm_num : (0:V)≠1) hm
end DiophantineConsistency.AdaptiveGap85JointMinusOne
