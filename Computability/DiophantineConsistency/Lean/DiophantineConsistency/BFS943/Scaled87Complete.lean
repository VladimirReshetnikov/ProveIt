import DiophantineConsistency.BFS943.Scaled87Regs
import DiophantineConsistency.BFS943.Trace87Transport

/-! # Positive root-scale-two zeros from positive 87 zeros

Package 194 §6 (`n_new = n_parent + (r - 1) g y + Ω` at `r = 2`), read here
without fixing the sign of the 87 root. At a positive 87 zero the carrier is
`Z₈₇ = M z` with `z = ±τ f y` (`Trace87Transport.graph_zero_data`). Keep every
coordinate except `n` and, for a natural shift `W` (any value not reading `n`),
put

  `n' = n + W + τ f y`   if `z = τ f y`,     `n' = n + W + 3 τ f y`   if `z = -τ f y`.

Then `Z₈₇(n') - M W = 2 Z₈₇(n)` resp. `-2 Z₈₇(n)` (`TenPositiveScaled87.Z_update`),
so the root-scale-two norm there is `4 value87 = 0`
(`TenPositiveScaled87.scaledNorm_two`). `n' > 0` because `W ≥ 0`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Scaled87Complete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace87 TenPositiveTrace76
open Trace87Factors
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cast_update (v : Fin 10 → V) (x : V) :
    (fun j => (ι (Function.update v 7 x j) : DiffRing V)) =
      Function.update (fun j => (ι (v j) : DiffRing V)) 7 (ι x) := by
  funext j
  fin_cases j <;> simp

set_option maxHeartbeats 1000000 in
/-- A positive 87 zero gives a positive zero of the root-scale-two norm at the
carrier `Z₈₇(n') - M W`, for every natural shift `W`. -/
theorem scaled_zero (p : Fin 4 → ℕ) (v : Fin 10 → V) (W : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j) (hz : value87 (ports p) (fun j => ι (v j)) = 0) :
    ∃ n' : V, 0<n' ∧ TenPositiveScaled87.scaledNorm (regs (ports p) (fun j => ι (v j)))
      ((regs (ports p) (fun j => ι (Function.update v 7 n' j))).Z-
        (regs (ports p) (fun j => ι (v j))).M*ι W) = 0 := by
  obtain ⟨z,tau,f,y,_,_,_,_,hzpm,hZ,_⟩ := Trace87Transport.graph_zero_data p v hb hv hz
  have hshift : ∀ x : V, (regs (ports p) (fun j => ι (Function.update v 7 x j))).Z =
      (regs (ports p) (fun j => ι (v j))).Z+
        (regs (ports p) (fun j => ι (v j))).M*(ι x-ι (v 7)) := by
    intro x
    rw [cast_update,TenPositiveScaled87.Z_update]
  have hnorm : normValue (regs (ports p) (fun j => ι (v j)))
      (regs (ports p) (fun j => ι (v j))).Z = 0 := hz
  set rr := regs (ports p) (fun j => ι (v j)) with hrr
  rcases hzpm with hp|hm
  · refine ⟨v 7+(W+tau*f*y),add_pos_of_pos_of_nonneg (hv 7) (by simp),?_⟩
    rw [hshift]
    have hc : rr.Z+rr.M*(ι (v 7+(W+tau*f*y))-ι (v 7))-rr.M*ι W=2*rr.Z := by
      rw [hZ,hp]
      simp only [map_add]
      ring
    rw [hc,TenPositiveScaled87.scaledNorm_two,hnorm,mul_zero]
  · refine ⟨v 7+(W+3*(tau*f*y)),add_pos_of_pos_of_nonneg (hv 7) (by simp),?_⟩
    rw [hshift]
    have hc : rr.Z+rr.M*(ι (v 7+(W+3*(tau*f*y)))-ι (v 7))-rr.M*ι W=2*(-rr.Z) := by
      rw [hZ,hm]
      simp only [map_add,map_mul,map_ofNat]
      ring
    rw [hc,TenPositiveScaled87.scaledNorm_two,TenPositiveScaled87.normValue_neg,hnorm,mul_zero]

#print axioms Scaled87Complete.scaled_zero
end Scaled87Complete
