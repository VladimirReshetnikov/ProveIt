import DiophantineConsistency.Compact44.BlockSelectionBridge
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace InternalOrbit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits
open OrbitDefinability
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem orbit_next (N s t : V) (hN : 0<N) :
    orbit N s (t+1)=(orbit N s t+s)%N := by
  unfold orbit
  rw [add_mul,one_mul]
  symm
  rw [mod_add hN,mod_eq_self_of_lt (mod_lt (t*s) hN), ←mod_add hN]

theorem all (C N s : V) (hN : 0<N)
    (hdec : ∀ h<N, UniformBandDecoder.Conclusion (8807*N) C (8807*h+4393) 4393)
    (hbase : FixedGraphOccupiedOrbit.SelectedBlock N C 0)
    (hstep : ∀ h<N, FixedGraphOccupiedOrbit.SelectedBlock N C h → FixedGraphOccupiedOrbit.SelectedBlock N C ((h+s)%N)) :
    ∀ t : V, Occupied C N s t := by
  intro t
  induction t using ISigma1.sigma1_succ_induction
  · unfold Occupied orbit; definability
  case zero =>
    have h0 := (BlockSelectionBridge.selected_iff_digit N C 0 hN (hdec 0 hN)).1 hbase
    simpa [Occupied,orbit] using h0
  case succ t ih =>
    let h := orbit N s t
    have hh : h<N := mod_lt _ hN
    have hs : FixedGraphOccupiedOrbit.SelectedBlock N C h :=
      (BlockSelectionBridge.selected_iff_digit N C h hh (hdec h hh)).2 ih
    have hn := hstep h hh hs
    have hnext : orbit N s (t+1)=(h+s)%N := orbit_next N s t hN
    have hnextlt : (h+s)%N<N := mod_lt _ hN
    have hdigit := (BlockSelectionBridge.selected_iff_digit N C ((h+s)%N) hnextlt (hdec _ hnextlt)).1 hn
    unfold Occupied
    rw [hnext]
    exact hdigit
#print axioms InternalOrbit.orbit_next
#print axioms InternalOrbit.all
end InternalOrbit
