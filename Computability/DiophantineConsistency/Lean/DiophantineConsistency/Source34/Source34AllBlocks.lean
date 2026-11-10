import DiophantineConsistency.Source34.Source34Successor
import DiophantineConsistency.Mixed121.Mixed121AllBlocks

/-! # Every block of the native word selects a tile, at source34

`Mixed121AllBlocks` at the source34 tuple. The orbit `t·s mod N`, the
`𝚺₁` occupancy predicate `Mixed121AllBlocks.Occupied` and its definability,
`selector_index` and `orbit_next` read only selector cells and are shared.
Re-declared over `Source34Uniform.DecodedAt` and the source34 successor step:
`selected_iff_digit`, `all` and the chain link `graph_all_blocks`
(`ISigma1.sigma1_succ_induction` carries block `0` and the successor step to
every block). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34AllBlocks
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticRepunit
open Mixed121AllBlocks (orbit Occupied selector_index orbit_next)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem selected_iff_digit (N C h : V) (hh : h<N)
    (hdec : Source34Uniform.DecodedAt (8801*N) C (8801*h+4393) 4393) :
    Mixed121Orbit.SelectedBlock N C h ↔ ∃ j<943, dig 121 C (8801*h+j)=1 := by
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨(i.val:V),by exact_mod_cast i.isLt,?_⟩
    have hbit := hi.1
    unfold Mixed121Band.selDigit at hbit
    rw [selector_index N h i hh] at hbit
    exact hbit
  · rintro ⟨j,hj,hbit⟩
    obtain ⟨m,hm,hmj⟩ := CleanGeometry.bounded_standard 943 j hj
    let i : Fin 943 := ⟨m,hm⟩
    have hi : Mixed121Band.selDigit (8801*N) C (8801*h+4393) 4393 i=1 := by
      unfold Mixed121Band.selDigit
      rw [selector_index N h i hh]
      simpa only [hmj] using hbit
    rcases hdec with ⟨hzero, _⟩ | ⟨i', hsel, _⟩
    · have h := hzero i
      rw [hi] at h
      exact False.elim (_root_.one_ne_zero h)
    · exact ⟨i', hsel⟩

theorem all (C N s : V) (hN : 0<N)
    (hdec : ∀ h<N, Source34Uniform.DecodedAt (8801*N) C (8801*h+4393) 4393)
    (hbase : Mixed121Orbit.SelectedBlock N C 0)
    (hstep : ∀ h<N, Mixed121Orbit.SelectedBlock N C h →
      Mixed121Orbit.SelectedBlock N C ((h+s)%N)) :
    ∀ t : V, Occupied C N s t := by
  intro t
  induction t using ISigma1.sigma1_succ_induction
  · unfold Occupied orbit; definability
  case zero =>
    have h0 := (selected_iff_digit N C 0 hN (hdec 0 hN)).1 hbase
    simpa [Occupied,orbit] using h0
  case succ t ih =>
    let h := orbit N s t
    have hh : h<N := mod_lt _ hN
    have hs : Mixed121Orbit.SelectedBlock N C h := (selected_iff_digit N C h hh (hdec h hh)).2 ih
    have hn := hstep h hh hs
    have hnext : orbit N s (t+1)=(h+s)%N := orbit_next N s t hN
    have hnextlt : (h+s)%N<N := mod_lt _ hN
    have hdigit := (selected_iff_digit N C ((h+s)%N) hnextlt (hdec _ hnextlt)).1 hn
    unfold Occupied
    rw [hnext]
    exact hdigit

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho

theorem graph_all_blocks (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (∀ h<N, Source34Uniform.DecodedAt (8801*N) C (8801*h+4393) 4393) ∧
      ∀ h<N, Mixed121Orbit.SelectedBlock N C h := by
  obtain ⟨N,hN,hq,hJ,hzero,hstep⟩ := Source34Successor.graph_spatial_successor v hv hz
  obtain ⟨N',s',hN',hq',hJ',haligned',hs',hshift',hdec,_⟩ :=
    Source34Uniform.graph_uniform_decoder v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hdecoder : ∀ h<N, Source34Uniform.DecodedAt (8801*N)
      (1+v 0*(Source34Ports.ports 0:V)-v 1-v 2) (8801*h+4393) 4393 := by
    intro h hh
    have hi := Mixed121Copy.index N h 4393 hh (by norm_num)
    exact hdec _ hi.1 hi.2
  have hall := all _ N 1 hN hdecoder hzero hstep
  refine ⟨N,hN,hq,hJ,hdecoder,?_⟩
  intro h hh
  have hd := hall h
  have hd' : ∃ j<943, dig 121 (1+v 0*(Source34Ports.ports 0:V)-v 1-v 2) (8801*h+j)=1 := by
    simpa only [Occupied,orbit,mul_one,mod_eq_self_of_lt hh] using hd
  exact (selected_iff_digit N _ h hh (hdecoder h hh)).2 hd'
end Source34AllBlocks
#print axioms Source34AllBlocks.selected_iff_digit
#print axioms Source34AllBlocks.all
#print axioms Source34AllBlocks.graph_all_blocks
