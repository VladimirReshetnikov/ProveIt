import DiophantineConsistency.Source34.Source34Orbit
import DiophantineConsistency.Mixed121.Mixed121Successor
import DiophantineConsistency.Mixed121.W121.TemporalSafeCyclic

/-! # The spatial successor of a selected block, at the source34 ports

`Mixed121Successor` at the source34 tuple. `Mixed121Successor.bit_nine` (the
radix-four digit `9` of every clause coefficient is `1`) is generic and used
directly. Copy index `9` is now the last west cell `1020 + 18 = 1038`, and
copy index `29` the last east cell `980 + 18 = 998` (121x8801: `1032`,
`1012`).

If block `h` selects a tile, `C(8801h + 1038) = 1`. The horizontal transport of
`Source34Field` at phase `1021 + 18 = 1039` reads
`C(8801g + 998) = C(8801(g − 1) + 1038)`: the DC shift `41` lands on `998`, and
the DR shift `8802 = 8801 + 1` on `1038` of the previous block (`previous`,
`marker`). So block `(h + 1) mod N`'s band has copy digit `29` equal to `1`,
hence is selected (`graph_spatial_successor`). Re-declared: `copy_nine`,
`previous`, `marker`, `graph_spatial_successor`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34Successor
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
open Mixed121Orbit (SelectedBlock)
open Source34Orbit
open Mixed121Successor (bit_nine)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- In a decoded band that selects a tile, copy digit `9` is `1`. -/
theorem copy_nine (n C k : V) (T : ℕ) (hdec : Source34Uniform.DecodedAt n C k T)
    (hsel : ∃ i, CompactSelectorSum.Selected (Mixed121Band.selDigit n C k T) i) :
    Source34Band.copyDigit n C k T 9=1 := by
  obtain ⟨i, hi⟩ := hsel
  rcases hdec with ⟨hz, _⟩ | ⟨i', _, hcopy⟩
  · have := hz i
    rw [hi.1] at this
    exact absurd this _root_.one_ne_zero
  · rw [hcopy 9 (by norm_num), bit_nine, Nat.cast_one]

theorem previous (N g : V) (hN : 0<N) (hg : g<N) :
    cyc (8801*N) (8801*g+1039) 8802 = 8801*(cyc N g 1)+1038 := by
  have hn : 0<8801*N := mul_pos (by norm_num) hN
  have hs : 1%N<N := mod_lt _ hN
  have hmod : (8801:V)%(8801*N)=8801*(1%N) := by
    simpa only [mul_one] using (ArithmeticModularCancellation.mul_mod_mul (k:=(8801:V)) (a:=(1:V))
      (b:=N) (by norm_num) hN)
  calc
    _ = cyc (8801*N) (cyc (8801*N) (8801*g+1039) 1) 8801 := by
      rw [W121.TemporalSafeCyclic.cyc_nested _ _ _ _ hn]
      norm_num
    _ = cyc (8801*N) (8801*g+1038) 8801 := by
      rw [Mixed121Copy.reflected N g 1039 1 hg (by norm_num) (by norm_num)]
      rw [show (1039:V)-1=1038 from (eq_tsub_of_add_eq (by norm_num : (1038:V)+1=1039)).symm]
    _ = cyc (8801*N) (8801*g+1038) (8801*(1%N)) := by
      rw [←hmod,cyc_mod _ _ _ hn]
    _ = 8801*(cyc N g (1%N))+1038 := Mixed121Copy.shift N g (1%N) 1038 hg hs (by norm_num)
    _ = 8801*(cyc N g 1)+1038 := by rw [cyc_mod _ _ _ hN]

theorem marker (N C g : V) (hN : 0<N) (hg : g<N)
    (heq : ∀ k<8801*N, k%8801=((1021+2*9:ℕ):V) →
      dig 121 C (cyc (8801*N) k 41)=dig 121 C (cyc (8801*N) k 8802)) :
    dig 121 C (8801*g+998)=dig 121 C (8801*(cyc N g 1)+1038) := by
  have hi := Mixed121Copy.index N g 1039 hg (by norm_num)
  have he := heq _ hi.1 (by rw [hi.2]; norm_num)
  rw [Mixed121Copy.reflected N g 1039 41 hg (by norm_num) (by norm_num),previous N g hN hg] at he
  rw [show (1039:V)-41=998 from (eq_tsub_of_add_eq (by norm_num : (998:V)+41=1039)).symm] at he
  exact he

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho

theorem graph_spatial_successor (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      SelectedBlock N C 0 ∧ ∀ h<N, SelectedBlock N C h → SelectedBlock N C ((h+1)%N) := by
  obtain ⟨N,s,hN,hq,hJ,hs,hzero,_⟩ := graph_occupied_orbit v hv hz
  obtain ⟨N',s',hN',hq',hJ',haligned',hs',hshift',hdec,_⟩ :=
    Source34Uniform.graph_uniform_decoder v hv hz
  obtain ⟨N'',s'',hN'',hq'',hJ'',haligned'',hs'',hshift'',_,horiz⟩ :=
    Source34Field.graph_field_markers v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  have hNN' : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N' N''
  let C : V := 1+v 0*(Source34Ports.ports 0:V)-v 1-v 2
  let n : V := 8801*N
  have hmarker : ∀ k<n, k%8801=((1021+2*9:ℕ):V) →
      dig 121 C (cyc n k 41)=dig 121 C (cyc n k 8802) :=
    fun k hk hp => horiz 9 (by norm_num) k hk hp
  refine ⟨N,hN,hq,hJ,hzero,?_⟩
  intro h hh hsel
  let g : V := (h+1)%N
  have hg : g<N := mod_lt _ hN
  have hidx := Mixed121Copy.index N h 4393 hh (by norm_num)
  have hdech := hdec (8801*h+4393) hidx.1 hidx.2
  have h1038 : dig 121 C (8801*h+1038) = 1 := by
    have hc := copy_nine n C (8801*h+4393) 4393 hdech hsel
    rw [show (8801*h+4393 : V) = 8801*h+((4393:ℕ):V) by simp,
      copy_cell N h 4393 1038 9 hh (by norm_num) (by norm_num) rfl C] at hc
    simpa using hc
  have he := marker N C g hN hg hmarker
  rw [show cyc N g 1=h from BlockOrbit.forward_back N h 1 hN hh, h1038] at he
  have hidxg := Mixed121Copy.index N g 4393 hg (by norm_num)
  have hdecg := hdec (8801*g+4393) hidxg.1 hidxg.2
  have hbit : Source34Band.copyDigit n C (8801*g+4393) 4393 29 = 1 := by
    rw [show (8801*g+4393 : V) = 8801*g+((4393:ℕ):V) by simp,
      copy_cell N g 4393 998 29 hg (by norm_num) (by norm_num) rfl C]
    simpa using he
  exact selected_of_copy_one n C _ 4393 29 (by norm_num) hbit hdecg
end Source34Successor
#print axioms Source34Successor.copy_nine
#print axioms Source34Successor.previous
#print axioms Source34Successor.marker
#print axioms Source34Successor.graph_spatial_successor
