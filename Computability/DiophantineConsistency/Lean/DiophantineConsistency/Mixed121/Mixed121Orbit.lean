import DiophantineConsistency.Mixed121.Mixed121Copy
import DiophantineConsistency.Compact44.BlockOrbit

/-! # Every temporal block on the shift orbit carries a tile, at 121x8801

This is the 121x8801 counterpart of Compact44's `BlockSelectedMarker` and of
`graph_occupied_orbit_facts`.

`SelectedBlock N C h` says that the clause band at cell `8801h + 4393`
selects a tile.

* Block `0` is selected. Selector `0` of its band reads cell `0`, and
  `C_0 = 1`.
* If block `h` is selected, every tile's anchor digits are `1`, so
  `C(8801h + 2195) = 1`. The anchor copy of `Mixed121Copy` puts that `1` into
  anchor `1095` of block `(h + s) mod N`. A band with a nonzero copy digit is
  not empty, so it is selected (`graph_occupied_orbit`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mixed121Orbit
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The band at cell `8801h + 4393` selects a tile. -/
def SelectedBlock (N C h : V) : Prop :=
  ∃ i, CompactSelectorSum.Selected
    (Mixed121Band.selDigit (8801*N) C (8801*h+4393) 4393) i

/-- A decoded band with a nonzero copy digit selects a tile. -/
theorem selected_of_copy_one (n C k : V) (T : ℕ) (j : ℕ) (hj : j<44)
    (hbit : Mixed121Band.copyDigit n C k T j=1) (hdec : Mixed121Uniform.DecodedAt n C k T) :
    ∃ i, CompactSelectorSum.Selected (Mixed121Band.selDigit n C k T) i := by
  rcases hdec with ⟨_, hz⟩ | ⟨i, hi, _⟩
  · have := hz j hj
    rw [hbit] at this
    exact absurd this _root_.one_ne_zero
  · exact ⟨i, hi⟩

/-- In a decoded band that selects a tile, every anchor copy digit is `1`. -/
theorem anchor_copy_one (n C k : V) (T : ℕ) (hdec : Mixed121Uniform.DecodedAt n C k T)
    (hsel : ∃ i, CompactSelectorSum.Selected (Mixed121Band.selDigit n C k T) i)
    (j : ℕ) (hj : j<44) (hj40 : 40≤j) :
    Mixed121Band.copyDigit n C k T j=1 := by
  obtain ⟨i, hi⟩ := hsel
  rcases hdec with ⟨hz, _⟩ | ⟨i', _, hcopy⟩
  · have := hz i
    rw [hi.1] at this
    exact absurd this _root_.one_ne_zero
  · rw [hcopy j hj]
    have hd : Mixed121Digits.digit (Compact943Data.row i') j = 1 := by
      unfold Mixed121Digits.digit
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [hd, Nat.cast_one]

/-- A copy digit of the band at `8801h + T` reads cell `8801h + e`. -/
theorem copy_cell (N h : V) (T e : ℕ) (j : ℕ) (hh : h<N) (hT : T<8801) (he : e≤T)
    (hpos : Mixed121Band.extraPosN j = e) (C : V) :
    Mixed121Band.copyDigit (8801*N) C (8801*h+(T:V)) T j = dig 121 C (8801*h+(e:V)) := by
  unfold Mixed121Band.copyDigit
  rw [hpos, Mixed121Copy.reflected N h (T:V) (((T-e:ℕ)):V) hh (by exact_mod_cast hT)
    (by exact_mod_cast Nat.sub_le T e)]
  congr 2
  have hev : (e:V) ≤ (T:V) := by exact_mod_cast he
  rw [show (((T-e:ℕ)):V) = (T:V) - (e:V) from by
    apply eq_tsub_of_add_eq; exact_mod_cast Nat.sub_add_cancel he]
  exact tsub_tsub_cancel_of_le hev

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Mixed121Ports.betaNat Mixed121Ports.lowNat Mixed121Ports.highNat
  Mixed121Kernel.paramKernel Mixed121Kernel.rho

theorem graph_occupied_orbit (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N s : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧ s<N ∧
      SelectedBlock N C 0 ∧ ∀ h<N, SelectedBlock N C h → SelectedBlock N C ((h+s)%N) := by
  obtain ⟨N,s,hN,hq,hJ,haligned,hs,hshift,hdecode,hdecode'⟩ :=
    Mixed121Uniform.graph_uniform_decoder v hv hz
  obtain ⟨N'',w'',hN'',hq'',hJ'',hle'',hw'',hv5'',hcarry'',h0,hzero,hbool⟩ :=
    Mixed121Clean.graph_support_carry v hv hz
  obtain ⟨N''',s'',hN''',hq''',hJ''',haligned'',hs'',hshift'',hpar1,_⟩ :=
    Mixed121Copy.graph_parity_copy v hv hz
  dsimp only at *
  have hNN2 : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  have hNN3 : N'''=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'''.symm.trans hq)
  subst N'' N'''
  -- The copy shift of `graph_parity_copy` is the decoder's block shift.
  have hss : s''=s := by
    apply mul_left_cancel₀ (by norm_num : (8801:V)≠0)
    exact hshift''.symm.trans hshift
  subst s''
  let C : V := 1+v 0*(Mixed121Ports.ports 0:V)-v 1-v 2
  let n : V := 8801*N
  have hnge : (8801:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8801)
    simpa only [n,mul_one] using h
  have ht : (4393:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have hp0 : (4393:V)%8801=4393 := mod_eq_self_of_lt (by norm_num)
  have hdec0 := hdecode 4393 ht hp0
  have hone : Mixed121Band.selDigit n C 4393 4393 Mixed121Occupied.origin=1 := by
    unfold Mixed121Band.selDigit
    have hs0 : cyc n (4393:V) (((4393 - Mixed121Occupied.origin.val : ℕ)) : V)=0 := by
      have hh := Mixed121Selected.source_cell n 4393 0 (by simpa using ht) (by norm_num)
      simpa [Mixed121Occupied.origin] using hh
    rw [hs0]
    exact h0
  have hsel0 : SelectedBlock N C 0 := by
    rcases hdec0 with ⟨hz0, _⟩ | ⟨i, hi, _⟩
    · have hh := hz0 Mixed121Occupied.origin
      rw [hone] at hh
      exact False.elim (_root_.one_ne_zero hh)
    · exact ⟨i, by simpa only [SelectedBlock, mul_zero, zero_add] using hi⟩
  refine ⟨N,s,hN,hq,hJ,hs,hsel0,?_⟩
  intro h hh hsel
  let g : V := (h+s)%N
  have hg : g<N := mod_lt _ hN
  have hidx := Mixed121Copy.index N h 4393 hh (by norm_num)
  have hdech := hdecode (8801*h+4393) hidx.1 hidx.2
  have h2195 : dig 121 C (8801*h+2195) = 1 := by
    have hc := anchor_copy_one n C (8801*h+4393) 4393 hdech hsel 42 (by norm_num) (by norm_num)
    rw [show (8801*h+4393 : V) = 8801*h+((4393:ℕ):V) by simp,
      copy_cell N h 4393 2195 42 hh (by norm_num) (by norm_num) rfl C] at hc
    simpa using hc
  have hidxg2 := Mixed121Copy.index N g 2195 hg (by norm_num)
  have heq := hpar1 (8801*g+2195) hidxg2.1 hidxg2.2
  have href : cyc n (8801*g+2195) 1100 = 8801*g+1095 := by
    rw [Mixed121Copy.reflected N g 2195 1100 hg (by norm_num) (by norm_num),
      show (2195:V)-1100 = 1095 from (eq_tsub_of_add_eq (show (1095:V)+1100=2195 by norm_num)).symm]
  rw [href, hshift, Mixed121Copy.shift N g s 2195 hg hs (by norm_num),
    BlockOrbit.forward_back N h s hN hh] at heq
  have hg1095 : dig 121 C (8801*g+1095) = 1 := heq.trans h2195
  have hidxg := Mixed121Copy.index N g 4393 hg (by norm_num)
  have hdecg := hdecode (8801*g+4393) hidxg.1 hidxg.2
  have hbit : Mixed121Band.copyDigit n C (8801*g+4393) 4393 40 = 1 := by
    rw [show (8801*g+4393 : V) = 8801*g+((4393:ℕ):V) by simp,
      copy_cell N g 4393 1095 40 hg (by norm_num) (by norm_num) rfl C]
    simpa using hg1095
  exact selected_of_copy_one n C _ 4393 40 (by norm_num) hbit hdecg
end Mixed121Orbit
#print axioms Mixed121Orbit.selected_of_copy_one
#print axioms Mixed121Orbit.anchor_copy_one
#print axioms Mixed121Orbit.copy_cell
#print axioms Mixed121Orbit.graph_occupied_orbit
