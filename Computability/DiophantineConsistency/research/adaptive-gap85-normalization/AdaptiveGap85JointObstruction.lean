import DiophantineConsistency.AdaptiveGap85JointResidue
/-! Conditional three-shift orbit obstruction; no actual zero is asserted. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85JointObstruction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveGap85JointResidue
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem literal_orbit_divisible_F (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hb : 0<v 0*(p 0:V))
    (h : Relation.ReflTransGen (LiteralStep p) v w)
    (hA : v 0*(p 0:V)∣v 6+(p 1:V)*(1+v 0*(p 0:V)))
    (hF : v 0*(p 0:V)∣v 1) : v 0*(p 0:V)∣w 1 := by
  let b : V := v 0*(p 0:V)
  let A : V := v 6+(p 1:V)*(1+b)
  change 0<b at hb
  change b∣A at hA
  change b∣v 1 at hF
  change b∣w 1
  have hm : (w 1+A*v 2)%b=(v 1+A*w 2)%b := literal_orbit_congruence p v w hb h
  obtain ⟨k,hk⟩ := hA
  rw [hk] at hm
  rw [mul_assoc,mod_add_mul' _ _ hb,mul_assoc,mod_add_mul' _ _ hb] at hm
  apply mod_eq_zero_iff_dvd.mp
  rw [hm]
  exact mod_eq_zero_iff_dvd.mpr hF

theorem literal_orbit_blocks_of_divisible_A_F (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hb : 0<v 0*(p 0:V))
    (h : Relation.ReflTransGen (LiteralStep p) v w)
    (hA : v 0*(p 0:V)∣v 6+(p 1:V)*(1+v 0*(p 0:V)))
    (hF : v 0*(p 0:V)∣v 1) (hwF : 0<w 1) (hwC : 0<w 2) :
    ¬ w 1+w 2<1+w 0*(p 0:V) := by
  have hz : w 0=v 0 := (literal_orbit_joint p v w h).1
  have hdiv := literal_orbit_divisible_F p v w hb h hA hF
  have hle : v 0*(p 0:V)≤w 1 := Arithmetic.le_of_dvd hwF hdiv
  have hc1 : 1≤w 2 := pos_iff_one_le.mp hwC
  apply not_lt_of_ge
  rw [hz]
  calc
    1+v 0*(p 0:V)=v 0*(p 0:V)+1 := by ac_rfl
    _ ≤ w 1+w 2 := add_le_add hle hc1
end DiophantineConsistency.AdaptiveGap85JointObstruction
