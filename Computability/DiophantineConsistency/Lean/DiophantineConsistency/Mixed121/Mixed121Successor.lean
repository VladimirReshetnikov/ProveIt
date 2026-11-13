import DiophantineConsistency.Mixed121.Mixed121Orbit
import DiophantineConsistency.Mixed121.W121.TemporalSafeCyclic

/-! # The spatial successor of a selected block, at the 121x8801 ports

This is the 121x8801 counterpart of Compact44's `MarkerBlockIndex`,
`MarkerSuccessor` and `graph_spatial_successor_facts`.

Every tile label is below `512`, so bit `9` of `x + 512` is `1`. The
radix-four digit `9` of every clause coefficient is therefore `1`. This is
copy index `9`, at position `1032` (`bit_nine`). If block `h` selects a tile,
then `C(8801h + 1032) = 1`. The horizontal transport of `Mixed121Field` at
phase `1065 + 9 = 1074` reads `C(8801g + 1012) = C(8801(g − 1) + 1032)`, and
position `1012` is copy index `29` of block `g`. So block `(h + 1) mod N`'s band
is not empty, hence selected (`graph_spatial_successor`). Compact44 uses its
copy bits `34` and `36` at positions `1031` and `1011`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mixed121Successor
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
open Mixed121Orbit

/-- Bit `9` of `x + 512` is `1` for every tile label `x < 512`: the radix-four
digit `9` of every clause coefficient. -/
theorem bit_nine (i : Fin 943) : Mixed121Digits.digit (Compact943Data.row i) 9 = 1 := by
  have hm : Compact943Data.row i ∈ Compact943Data.rows := List.get_mem Compact943Data.rows _
  have h := of_decide_eq_true ((List.all_eq_true.mp Mixed121Kernel.labels_below) _ hm)
  unfold Mixed121Digits.digit Mixed121Digits.bit
  rw [if_pos (by norm_num)]
  have hx := h.1
  generalize (Compact943Data.row i).1 = x at hx ⊢
  norm_num
  omega

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- In a decoded band that selects a tile, copy digit `9` is `1`. -/
theorem copy_nine (n C k : V) (T : ℕ) (hdec : Mixed121Uniform.DecodedAt n C k T)
    (hsel : ∃ i, CompactSelectorSum.Selected (Mixed121Band.selDigit n C k T) i) :
    Mixed121Band.copyDigit n C k T 9=1 := by
  obtain ⟨i, hi⟩ := hsel
  rcases hdec with ⟨hz, _⟩ | ⟨i', _, hcopy⟩
  · have := hz i
    rw [hi.1] at this
    exact absurd this _root_.one_ne_zero
  · rw [hcopy 9 (by norm_num), bit_nine, Nat.cast_one]

theorem previous (N g : V) (hN : 0<N) (hg : g<N) :
    cyc (8801*N) (8801*g+1074) 8843 = 8801*(cyc N g 1)+1032 := by
  have hn : 0<8801*N := mul_pos (by norm_num) hN
  have hs : 1%N<N := mod_lt _ hN
  have hmod : (8801:V)%(8801*N)=8801*(1%N) := by
    simpa only [mul_one] using (ArithmeticModularCancellation.mul_mod_mul (k:=(8801:V)) (a:=(1:V))
      (b:=N) (by norm_num) hN)
  calc
    _ = cyc (8801*N) (cyc (8801*N) (8801*g+1074) 42) 8801 := by
      rw [W121.TemporalSafeCyclic.cyc_nested _ _ _ _ hn]
      norm_num
    _ = cyc (8801*N) (8801*g+1032) 8801 := by
      rw [Mixed121Copy.reflected N g 1074 42 hg (by norm_num) (by norm_num)]
      rw [show (1074:V)-42=1032 from (eq_tsub_of_add_eq (by norm_num : (1032:V)+42=1074)).symm]
    _ = cyc (8801*N) (8801*g+1032) (8801*(1%N)) := by
      rw [←hmod,cyc_mod _ _ _ hn]
    _ = 8801*(cyc N g (1%N))+1032 := Mixed121Copy.shift N g (1%N) 1032 hg hs (by norm_num)
    _ = 8801*(cyc N g 1)+1032 := by rw [cyc_mod _ _ _ hN]

theorem marker (N C g : V) (hN : 0<N) (hg : g<N)
    (heq : ∀ k<8801*N, k%8801=((1065+9:ℕ):V) →
      dig 121 C (cyc (8801*N) k 62)=dig 121 C (cyc (8801*N) k 8843)) :
    dig 121 C (8801*g+1012)=dig 121 C (8801*(cyc N g 1)+1032) := by
  have hi := Mixed121Copy.index N g 1074 hg (by norm_num)
  have he := heq _ hi.1 (by rw [hi.2]; norm_num)
  rw [Mixed121Copy.reflected N g 1074 62 hg (by norm_num) (by norm_num),previous N g hN hg] at he
  rw [show (1074:V)-62=1012 from (eq_tsub_of_add_eq (by norm_num : (1012:V)+62=1074)).symm] at he
  exact he

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Mixed121Ports.betaNat Mixed121Ports.lowNat Mixed121Ports.highNat
  Mixed121Kernel.paramKernel Mixed121Kernel.rho

theorem graph_spatial_successor (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      SelectedBlock N C 0 ∧ ∀ h<N, SelectedBlock N C h → SelectedBlock N C ((h+1)%N) := by
  obtain ⟨N,s,hN,hq,hJ,hs,hzero,_⟩ := graph_occupied_orbit v hv hz
  obtain ⟨N',s',hN',hq',hJ',haligned',hs',hshift',hdec,_⟩ :=
    Mixed121Uniform.graph_uniform_decoder v hv hz
  obtain ⟨N'',s'',hN'',hq'',hJ'',haligned'',hs'',hshift'',_,horiz⟩ :=
    Mixed121Field.graph_field_markers v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  have hNN' : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N' N''
  let C : V := 1+v 0*(Mixed121Ports.ports 0:V)-v 1-v 2
  let n : V := 8801*N
  have hmarker : ∀ k<n, k%8801=((1065+9:ℕ):V) →
      dig 121 C (cyc n k 62)=dig 121 C (cyc n k 8843) :=
    fun k hk hp => horiz 9 (by norm_num) k hk hp
  refine ⟨N,hN,hq,hJ,hzero,?_⟩
  intro h hh hsel
  let g : V := (h+1)%N
  have hg : g<N := mod_lt _ hN
  have hidx := Mixed121Copy.index N h 4393 hh (by norm_num)
  have hdech := hdec (8801*h+4393) hidx.1 hidx.2
  have h1032 : dig 121 C (8801*h+1032) = 1 := by
    have hc := copy_nine n C (8801*h+4393) 4393 hdech hsel
    rw [show (8801*h+4393 : V) = 8801*h+((4393:ℕ):V) by simp,
      copy_cell N h 4393 1032 9 hh (by norm_num) (by norm_num) rfl C] at hc
    simpa using hc
  have he := marker N C g hN hg hmarker
  rw [show cyc N g 1=h from BlockOrbit.forward_back N h 1 hN hh, h1032] at he
  have hidxg := Mixed121Copy.index N g 4393 hg (by norm_num)
  have hdecg := hdec (8801*g+4393) hidxg.1 hidxg.2
  have hbit : Mixed121Band.copyDigit n C (8801*g+4393) 4393 29 = 1 := by
    rw [show (8801*g+4393 : V) = 8801*g+((4393:ℕ):V) by simp,
      copy_cell N g 4393 1012 29 hg (by norm_num) (by norm_num) rfl C]
    simpa using he
  exact selected_of_copy_one n C _ 4393 29 (by norm_num) hbit hdecg
end Mixed121Successor
#print axioms Mixed121Successor.bit_nine
#print axioms Mixed121Successor.copy_nine
#print axioms Mixed121Successor.previous
#print axioms Mixed121Successor.marker
#print axioms Mixed121Successor.graph_spatial_successor
