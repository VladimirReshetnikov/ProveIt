import DiophantineConsistency.Mixed121.Mixed121Successor

/-! # Every block of the native word selects a tile, at 121x8801

This is the 121x8801 counterpart of Compact44's `OrbitDefinability`,
`BlockSelectionBridge`, `InternalOrbit` and `graph_all_blocks_facts`.

"Every block `h < N` is selected" needs induction inside the model of `𝗜𝚺₁`.
Two facts make it available:

* a decoded block is selected exactly when some cell `8801h + j`, `j < 943`,
  holds `1` (`selected_iff_digit`), because selector `i` reads cell
  `8801h + i`;
* that condition is a `𝚺₁` predicate of the step count `t` along the orbit
  `t·s mod N` (`occupied_definable`).

`ISigma1.sigma1_succ_induction` then carries the base block and the
successor step of `Mixed121Successor` to every block
(`graph_all_blocks`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mixed121AllBlocks
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticRepunit
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def orbit (N s t : V) : V := (t*s)%N
instance orbit_definable (N s : V) : 𝚺₁-Function₁ (orbit N s) := by
  unfold orbit
  definability

/-- Some selector cell of the block at orbit step `t` holds `1`. -/
def Occupied (C N s t : V) : Prop := ∃ j<943, dig 121 C (8801*orbit N s t+j)=1
instance occupied_definable (C N s : V) : 𝚺₁-Predicate (Occupied C N s) := by
  unfold Occupied orbit
  definability

theorem selector_index (N h : V) (i : Fin 943) (hh : h<N) :
    cyc (8801*N) (8801*h+4393) (((4393-i.val):ℕ):V) = 8801*h+(i.val:V) := by
  have hiT : i.val≤4393 := by have := i.isLt; omega
  have hd : (((4393-i.val):ℕ):V)≤(4393:V) := by exact_mod_cast (Nat.sub_le 4393 i.val)
  have he := Mixed121Copy.reflected N h (4393:V) (((4393-i.val):ℕ):V) hh (by norm_num) hd
  have hsum : (i.val:V)+(((4393-i.val):ℕ):V)=(4393:V) := by exact_mod_cast (Nat.add_sub_of_le hiT)
  rw [(eq_tsub_of_add_eq hsum).symm] at he
  exact he

theorem selected_iff_digit (N C h : V) (hh : h<N)
    (hdec : Mixed121Uniform.DecodedAt (8801*N) C (8801*h+4393) 4393) :
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

theorem orbit_next (N s t : V) (hN : 0<N) :
    orbit N s (t+1)=(orbit N s t+s)%N := by
  unfold orbit
  rw [add_mul,one_mul]
  symm
  rw [mod_add hN,mod_eq_self_of_lt (mod_lt (t*s) hN), ←mod_add hN]

theorem all (C N s : V) (hN : 0<N)
    (hdec : ∀ h<N, Mixed121Uniform.DecodedAt (8801*N) C (8801*h+4393) 4393)
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
attribute [local irreducible] Mixed121Ports.betaNat Mixed121Ports.lowNat Mixed121Ports.highNat
  Mixed121Kernel.paramKernel Mixed121Kernel.rho

theorem graph_all_blocks (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (∀ h<N, Mixed121Uniform.DecodedAt (8801*N) C (8801*h+4393) 4393) ∧
      ∀ h<N, Mixed121Orbit.SelectedBlock N C h := by
  obtain ⟨N,hN,hq,hJ,hzero,hstep⟩ := Mixed121Successor.graph_spatial_successor v hv hz
  obtain ⟨N',s',hN',hq',hJ',haligned',hs',hshift',hdec,_⟩ :=
    Mixed121Uniform.graph_uniform_decoder v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hdecoder : ∀ h<N, Mixed121Uniform.DecodedAt (8801*N)
      (1+v 0*(Mixed121Ports.ports 0:V)-v 1-v 2) (8801*h+4393) 4393 := by
    intro h hh
    have hi := Mixed121Copy.index N h 4393 hh (by norm_num)
    exact hdec _ hi.1 hi.2
  have hall := all _ N 1 hN hdecoder hzero hstep
  refine ⟨N,hN,hq,hJ,hdecoder,?_⟩
  intro h hh
  have hd := hall h
  have hd' : ∃ j<943, dig 121 (1+v 0*(Mixed121Ports.ports 0:V)-v 1-v 2) (8801*h+j)=1 := by
    simpa only [Occupied,orbit,mul_one,mod_eq_self_of_lt hh] using hd
  exact (selected_iff_digit N _ h hh (hdecoder h hh)).2 hd'
end Mixed121AllBlocks
#print axioms Mixed121AllBlocks.selected_iff_digit
#print axioms Mixed121AllBlocks.all
#print axioms Mixed121AllBlocks.graph_all_blocks
