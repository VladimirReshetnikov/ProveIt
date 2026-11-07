import DiophantineConsistency.Mixed121.Mixed121BlockWord

/-! # Neighbouring tiles agree on their shared fields, at 121x8801

This is the 121x8801 counterpart of Compact44's `VerticalFieldBits`,
`HorizontalFieldBits` and `graph_field_match_facts`. Here it is stated
directly on the radix-four clause digits.

Let `i` be block `h`'s tile, `j` the tile of its temporal predecessor
`h − s`, and `l` the tile of its spatial neighbour `h − 1`. Then for
`u < 10`:

* `digit_i(30 + u) = digit_j(10 + u)`. This is the vertical transport of
  `Mixed121Field` at cell `1013 + u`, read through the copy positions `983 + u`
  (copy index `30 + u`) and `1013 + u` (copy index `10 + u`). Field `3` of
  `i` is field `1` of `j`.
* `digit_i(20 + u) = digit_l(u)`. This is the horizontal transport at
  `1065 + u`, read through `1003 + u` (index `20 + u`) and `1023 + u`
  (index `u`). Field `2` of `i` is field `0` of `l`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mixed121FieldMatch
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticRepunit ArithmeticPackingBlocks
open Mixed121BlockWord

theorem pos_south : ∀ u < 10, Mixed121Band.extraPosN (30+u) = 983+u := by decide
theorem pos_north : ∀ u < 10, Mixed121Band.extraPosN (10+u) = 1013+u := by decide
theorem pos_east : ∀ u < 10, Mixed121Band.extraPosN (20+u) = 1003+u := by decide
theorem pos_west : ∀ u < 10, Mixed121Band.extraPosN u = 1023+u := by decide

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Mixed121Ports.betaNat Mixed121Ports.lowNat Mixed121Ports.highNat
  Mixed121Kernel.paramKernel Mixed121Kernel.rho

/-- A block's copy cell at position `e` is its tile's digit there. -/
theorem cell_digit (N C h : V) (hh : h<N) (i : Fin 943) (j e : ℕ) (hj : j<44)
    (he : e≤4393) (hpos : Mixed121Band.extraPosN j = e)
    (hcopy : ∀ j < 44, Mixed121Band.copyDigit (8801*N) C (8801*h+4393) 4393 j =
      (Mixed121Digits.digit (Compact943Data.row i) j : V)) :
    dig 121 C (8801*h+(e:V)) = (Mixed121Digits.digit (Compact943Data.row i) j : V) := by
  have h1 := hcopy j hj
  rw [show (8801*h+4393 : V) = 8801*h+((4393:ℕ):V) by simp,
    Mixed121Orbit.copy_cell N h 4393 e j hh (by norm_num) he hpos C] at h1
  exact h1

theorem graph_field_match (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N W s : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ s<N ∧
      Blocks 10 (row C N 1) N W ∧
      (∀ h<N, row C N 1 h<943 ∧ row C N 1 h≠1) ∧
      ∀ h<N, ∃ i j l : Fin 943,
        row C N 1 h=(i.val:V) ∧ row C N 1 (cyc N h s)=(j.val:V) ∧
        row C N 1 (cyc N h 1)=(l.val:V) ∧
        (∀ u < 10, Mixed121Digits.digit (Compact943Data.row i) (30+u) =
          Mixed121Digits.digit (Compact943Data.row j) (10+u)) ∧
        (∀ u < 10, Mixed121Digits.digit (Compact943Data.row i) (20+u) =
          Mixed121Digits.digit (Compact943Data.row l) u) := by
  obtain ⟨N,W,hN,hq,hJ,hW,hrows,hbound⟩ := graph_all_block_word v hv hz
  obtain ⟨N',s',hN',hq',hJ',haligned',hs',hshift',hvert,hhoriz⟩ :=
    Mixed121Field.graph_field_markers v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  let C : V := 1+v 0*(Mixed121Ports.ports 0:V)-v 1-v 2
  refine ⟨N,W,s',hN,hq,hs',hW,hbound,?_⟩
  intro h hh
  have hjb : cyc N h s'<N := cyc_lt hN _ _
  have hlb : cyc N h 1<N := cyc_lt hN _ _
  obtain ⟨i,hi,_,hci⟩ := hrows h hh
  obtain ⟨j,hj,_,hcj⟩ := hrows _ hjb
  obtain ⟨l,hl,_,hcl⟩ := hrows _ hlb
  refine ⟨i,j,l,hi,hj,hl,?_,?_⟩
  · intro u hu
    have hidx := Mixed121Copy.index N h (((1013+u:ℕ)):V) hh (by exact_mod_cast (show 1013+u<8801 by omega))
    have he := hvert u hu _ hidx.1 hidx.2
    rw [hshift', Mixed121Copy.reflected N h _ 30 hh (by exact_mod_cast (show 1013+u<8801 by omega))
      (by exact_mod_cast (show 30≤1013+u by omega)),
      Mixed121Copy.shift N h s' _ hh hs' (by exact_mod_cast (show 1013+u<8801 by omega))] at he
    have hsub : (((1013+u:ℕ)):V) - 30 = (((983+u:ℕ)):V) := by
      apply (eq_tsub_of_add_eq ?_).symm
      exact_mod_cast (show 983+u+30 = 1013+u by omega)
    rw [hsub] at he
    rw [cell_digit N C h hh i (30+u) (983+u) (by omega) (by omega) (pos_south u hu) hci,
      cell_digit N C _ hjb j (10+u) (1013+u) (by omega) (by omega) (pos_north u hu) hcj] at he
    exact_mod_cast he
  · intro u hu
    have hidx := Mixed121Copy.index N h (((1065+u:ℕ)):V) hh (by exact_mod_cast (show 1065+u<8801 by omega))
    have he := hhoriz u hu _ hidx.1 hidx.2
    have hprev : cyc (8801*N) (8801*h+(((1065+u:ℕ)):V)) 8843 = 8801*(cyc N h 1)+(((1023+u:ℕ)):V) := by
      have hn : 0<8801*N := mul_pos (by norm_num) hN
      have hs1 : 1%N<N := mod_lt _ hN
      have hmod : (8801:V)%(8801*N)=8801*(1%N) := by
        simpa only [mul_one] using (ArithmeticModularCancellation.mul_mod_mul (k:=(8801:V)) (a:=(1:V))
          (b:=N) (by norm_num) hN)
      have hsub : (((1065+u:ℕ)):V) - 42 = (((1023+u:ℕ)):V) := by
        apply (eq_tsub_of_add_eq ?_).symm
        exact_mod_cast (show 1023+u+42 = 1065+u by omega)
      calc
        _ = cyc (8801*N) (cyc (8801*N) (8801*h+(((1065+u:ℕ)):V)) 42) 8801 := by
          rw [W121.TemporalSafeCyclic.cyc_nested _ _ _ _ hn]
          norm_num
        _ = cyc (8801*N) (8801*h+(((1023+u:ℕ)):V)) 8801 := by
          rw [Mixed121Copy.reflected N h _ 42 hh (by exact_mod_cast (show 1065+u<8801 by omega))
            (by exact_mod_cast (show 42≤1065+u by omega)), hsub]
        _ = cyc (8801*N) (8801*h+(((1023+u:ℕ)):V)) (8801*(1%N)) := by
          rw [←hmod,cyc_mod _ _ _ hn]
        _ = 8801*(cyc N h (1%N))+(((1023+u:ℕ)):V) :=
          Mixed121Copy.shift N h (1%N) _ hh hs1 (by exact_mod_cast (show 1023+u<8801 by omega))
        _ = _ := by rw [cyc_mod _ _ _ hN]
    rw [Mixed121Copy.reflected N h _ 62 hh (by exact_mod_cast (show 1065+u<8801 by omega))
      (by exact_mod_cast (show 62≤1065+u by omega)), hprev] at he
    have hsub : (((1065+u:ℕ)):V) - 62 = (((1003+u:ℕ)):V) := by
      apply (eq_tsub_of_add_eq ?_).symm
      exact_mod_cast (show 1003+u+62 = 1065+u by omega)
    rw [hsub] at he
    rw [cell_digit N C h hh i (20+u) (1003+u) (by omega) (by omega) (pos_east u hu) hci,
      cell_digit N C _ hlb l u (1023+u) (by omega) (by omega) (pos_west u hu) hcl] at he
    exact_mod_cast he
end Mixed121FieldMatch
#print axioms Mixed121FieldMatch.pos_south
#print axioms Mixed121FieldMatch.cell_digit
#print axioms Mixed121FieldMatch.graph_field_match
