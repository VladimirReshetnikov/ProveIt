import DiophantineConsistency.Source34.Source34Target
import DiophantineConsistency.Mixed121.Mixed121High
import DiophantineConsistency.Source34.Source34HighPhase

/-! # The constructed word avoids the whole high mask, at the source34 ports

`Mixed121High` at the source34 tuple.

* Padding. The lower kernel mass is at most `2^110·ρ^5495` and a (pulsed)
  cell is below `2^(121·3296+1)`, so every transport block is below
  `4·2^(121·8791+111) ≤ 2^(121·8792)`: its padding digits `8792..8799` vanish.
  The high part is now only `2^121·x` (top term `ρ^8802`), far below that.
* Assembly. With the padding, phase `0` (`Source34Block`), the stride-two field
  windows `1000 + 2u`, `1021 + 2u` and the anchor phases
  (`Source34FieldParity`) and the two clause targets (`Source34Target`),
  `Source34HighPhase.noCarry_of_active` gives that every block of the
  constructed word is carry-free against `MF_native`.

`Mixed121High.digits_clear` is generic and used directly. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Source34High
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticStandardCasts ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPacking
  ArithmeticBinaryCarry
open Mixed121Kernel (rho)
open Mixed121Block (rho_pow_cast)
open Mixed121Column (perturb)
open Mixed121High (digits_clear)
open CompactMarkedTransport Source34Kernel Source34KernelSplit Source34Cell Source34Word
  Source34Block Source34Column Source34FieldParity Source34Target
attribute [local irreducible] paramKernel rho lowerKernelAt Source34Ports.lowNat Source34Ports.highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem lower_mass_model :
    ((lowerKernelAt rho : ℕ) : V) ≤ Exp.exp (121*5495+110 : V) := by
  have hr : 1 ≤ rho := by unfold rho; norm_num
  have hn := lower_le rho hr
  have hv : ((lowerKernelAt rho : ℕ) : V) ≤ ((2^110 * rho^5495 : ℕ) : V) := by
    exact_mod_cast hn
  calc
    _ ≤ ((2^110 * rho^5495 : ℕ) : V) := hv
    _ = Exp.exp (110:V) * Exp.exp (121*5495 : V) := by
      rw [Nat.cast_mul, ← cast_exp 110, rho_pow_cast]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
    _ = Exp.exp (121*5495+110 : V) := by
      rw [← exp_add]
      apply congrArg Exp.exp
      ring

theorem sharp_cell (a d : V) (ha : a ≠ 1) (hd : d ≤ 1) :
    packedCell a d < Exp.exp (121*3296+1 : V) := by
  rw [exp_succ]
  exact packedCell_lt_twice_top a d ha hd

theorem low_product_sharp (x : V) (hx : x < Exp.exp (121*3296+1 : V)) :
    ((lowerKernelAt rho : ℕ) : V) * x < Exp.exp (121*8791+111 : V) := by
  calc
    ((lowerKernelAt rho : ℕ) : V) * x ≤ Exp.exp (121*5495+110 : V) * x :=
      mul_le_mul_of_nonneg_right lower_mass_model (Arithmetic.zero_le x)
    _ < Exp.exp (121*5495+110 : V) * Exp.exp (121*3296+1 : V) :=
      mul_lt_mul_of_pos_left hx (exp_pos _)
    _ = Exp.exp ((121*5495+110)+(121*3296+1) : V) := (exp_add _ _).symm
    _ = Exp.exp (121*8791+111 : V) := by apply congrArg Exp.exp; norm_num

theorem block_lt_padding {N s : V} {X : V → V} (hN : 0 < N)
    (hsmall : ∀ j < N, X j < Exp.exp (121*3296+1 : V)) :
    ∀ j < N, blk 1064921 (paramKernel rho : V) N s X j < Exp.exp (121*8792 : V) := by
  intro j hj
  have h0 := hsmall j hj
  have h1 := hsmall (cyc N j 1) (cyc_lt hN j 1)
  have hs := hsmall (cyc N j s) (cyc_lt hN j s)
  have h0' : X j < Exp.exp (121*3297+1 : V) :=
    lt_of_lt_of_le h0 (exp_monotone_le.mpr (by norm_num))
  have h1' : X (cyc N j 1) < Exp.exp (121*3297+1 : V) :=
    lt_of_lt_of_le h1 (exp_monotone_le.mpr (by norm_num))
  let E : V := Exp.exp (121*8791+111)
  have hl : lo 1064921 (paramKernel rho : V) X j < E := by
    unfold lo E
    rw [low_product_remainder (X j) h0']
    exact low_product_sharp (X j) h0
  have hh : hi 1064921 (paramKernel rho : V) X (cyc N j 1) < E := by
    unfold hi E
    exact lt_of_lt_of_le (high_product_lt _ h1') (exp_monotone_le.mpr (by norm_num))
  have ht : X (cyc N j s) < E :=
    lt_of_lt_of_le hs (exp_monotone_le.mpr (by norm_num))
  have hsum : blk 1064921 (paramKernel rho : V) N s X j < E+E+E := by
    unfold blk
    exact add_lt_add (add_lt_add hl hh) ht
  have hless : E+E+E ≤ E+E+E+E := le_add_of_nonneg_right (Arithmetic.zero_le E)
  have hfour : E+E+E+E = Exp.exp (121*8791+113 : V) := by
    have he : Exp.exp ((121*8791+111)+1+1 : V) =
        2*(2*Exp.exp (121*8791+111 : V)) := by rw [exp_succ, exp_succ]
    calc
      E+E+E+E = 2*(2*Exp.exp (121*8791+111 : V)) := by unfold E; ring
      _ = Exp.exp ((121*8791+111)+1+1 : V) := he.symm
      _ = Exp.exp (121*8791+113 : V) := by apply congrArg Exp.exp; ring
  exact lt_of_lt_of_le hsum (le_trans hless (by
    rw [hfour]
    exact exp_monotone_le.mpr (by norm_num)))

/-- All padding digits vanish for both the base and the perturbed word. -/
theorem marked_padding {N s : V} (row δ : V → V)
    (hw : CompactWord row N s) (hbool : ∀ j < N, δ j ≤ 1) :
    let X0 : V → V := fun j => packedCell (row j) 0
    (∀ j < N, ∀ p, 8792 ≤ p →
      dig 121 (blk 1064921 (paramKernel rho : V) N s X0 j) p = 0) ∧
    (∀ j < N, ∀ p, 8792 ≤ p →
      dig 121 (blk 1064921 (paramKernel rho : V) N s (perturb X0 δ) j) p = 0) := by
  let X0 : V → V := fun j => packedCell (row j) 0
  have hbase : ∀ j < N, X0 j < Exp.exp (121*3296+1 : V) := by
    intro j hj
    exact sharp_cell (row j) 0 (hw.tile_ne j hj) (by simp)
  have hpulse : ∀ j < N, perturb X0 δ j < Exp.exp (121*3296+1 : V) := by
    intro j hj
    rcases le_one_iff_eq_zero_or_one.mp (hbool j hj) with hz | ho
    · simpa [perturb, hz] using hbase j hj
    · change packedCell (row j) 0 + Exp.exp (121*1063) * δ j < _
      rw [ho, mul_one, ← cell_one]
      exact sharp_cell (row j) 1 (hw.tile_ne j hj) (by simp)
  constructor
  · intro j hj p hp
    exact digits_clear _ _ (block_lt_padding hw.pos hbase j hj) hp
  · intro j hj p hp
    exact digits_clear _ _ (block_lt_padding hw.pos hpulse j hj) hp

/-- Actual normalized blocks avoid the complete high mask `MF_native`. -/
theorem marked_all_high (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    {N s : V} (hw : CompactWord row N s) (hN : 1<N) (hs : s<N)
    (hbool : ∀ j, dummy j ≤ 1) :
    ∀ j<N, NoCarry (blk 1064921 (paramKernel rho : V) N s (cellWord row dummy) j)
      ((Source34Ports.highNat : ℕ) : V) := by
  let X0 : V → V := fun j => packedCell (row j) 0
  have he : cellWord row dummy = perturb X0 dummy := by
    funext j
    exact cellWord_boolean_pulse row dummy j (hbool j)
  have hpads := (marked_padding row dummy hw (fun j _ => hbool j)).2
  have hsums := (marked_cell_sums row dummy hw (fun j _ => hbool j)).2
  intro j hj
  apply Source34HighPhase.noCarry_of_active
  · have hsum := hsums j hj
    rw [← he] at hsum
    have hb := lt_of_le_of_lt (le_add_of_nonneg_left (Arithmetic.zero_le (cellWord row dummy j))) hsum
    simpa only [show (121*8801 : V) = 1064921 by norm_num] using hb
  · intro p _ hp
    rw [he]
    exact hpads j hj p hp
  · intro p _ ha
    rcases ha with h0 | ⟨u, hu, hv⟩ | ⟨u, hu, hh⟩ | h1 | h2 | h3 | h4
    · rw [h0]
      exact phase_zero_noCarry (row:=row) (dummy:=dummy) (j:=j) hw
    · rw [hv]; exact vertical_fields row dummy hw hN hs hbool hj u hu
    · rw [hh]; exact horizontal_fields row dummy hw hN hs hbool hj u hu
    · rw [h1]; exact phase2195_noCarry row dummy hw hN hs hbool hj
    · rw [h2]; exact phase3296_noCarry row dummy hw hN hs hbool hj
    · rw [h3]
      simpa only [Nat.cast_ofNat] using marked_targets_noCarry row dummy hw hN hs hbool j hj 4393 (Or.inl rfl)
    · rw [h4]
      simpa only [Nat.cast_ofNat] using marked_targets_noCarry row dummy hw hN hs hbool j hj 5495 (Or.inr rfl)

#print axioms Source34High.block_lt_padding
#print axioms Source34High.marked_padding
#print axioms Source34High.marked_all_high
end Source34High
