import DiophantineConsistency.ArithmeticPacking

/-! Packing transport needs only size and source-origin conditions, not
the low- or high-mask fields of PackingInput. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactPartialPackingTransport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPackingBlocks ArithmeticPacking

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {d K N s : V} {X : V → V} [𝚺₁-Function₁ X]

/-- Exact arithmetic prerequisites for the transport residue. -/
structure TransportInput (d K N s : V) (X : V → V) : Prop where
  N_gt : 1 < N
  s_lt : s < N
  hi_lt : ∀ j < N, K * X j < Exp.exp d * Exp.exp d
  cell_sum : ∀ j < N, X j + blk d K N s X j < Exp.exp d
  origin : 1 ≤ X 0

section main
variable (h : TransportInput d K N s X)
include h

omit [𝚺₁-Function₁ X] in
theorem X_lt : ∀ j < N, X j < Exp.exp d := fun j hj =>
  lt_of_le_of_lt (le_add_of_nonneg_right (Arithmetic.zero_le _)) (h.cell_sum j hj)

omit [𝚺₁-Function₁ X] in
theorem blk_lt : ∀ j < N, blk d K N s X j < Exp.exp d := fun j hj =>
  lt_of_le_of_lt (le_add_of_nonneg_left (Arithmetic.zero_le _)) (h.cell_sum j hj)

omit [𝚺₁-Function₁ X] in
theorem N_pos : 0 < N := lt_trans (by norm_num) h.N_gt

/-- Both represented sums fit together in the ambient cyclic word. -/
theorem C_add_F_lt : Cw d N X + Fw d K N s X < Exp.exp (d*N) := by
  haveI : 𝚺₁-Function₁ (fun j => X j + blk d K N s X j) := by definability
  rw [Cw, Fw, ← bsum_add (h := fun j => X j + blk d K N s X j) h.cell_sum (fun _ _ => rfl)]
  exact bsum_lt h.cell_sum

theorem C_pos : 0 < Cw d N X := by
  change 0 < bsum d X N
  have hd := dig_bsum (X_lt h) (N_pos h)
  rw [dig_zero_index] at hd
  have hc : 0 < X 0 := lt_of_lt_of_le (by norm_num) h.origin
  exact lt_of_lt_of_le (by rwa [hd]) (mod_le _ _)

theorem F_lt_M : Fw d K N s X < Exp.exp (d*N) - 1 := by
  have hlt := C_add_F_lt h
  have hC := C_pos h
  apply lt_tsub_of_add_lt_left
  exact lt_of_le_of_lt (add_le_add (pos_iff_one_le.mp hC) le_rfl) hlt

/-- The identity behind transport, with no mask or block-positivity premise. -/
theorem transport_formula :
    Fw d K N s X + (Exp.exp (d*N)-1) *
      (bsum d (hi d K X) N / Exp.exp (d*(N-1)) + Cw d N X / Exp.exp (d*(N-s))) =
      (K + Exp.exp (d*s)) * Cw d N X := by
  have hX := X_lt h
  have hB := blk_lt h
  have hlo : ∀ j < N, lo d K X j < Exp.exp d := fun j _ => mod_lt _ (exp_pos d)
  have hhi : ∀ j < N, hi d K X j < Exp.exp d := fun j hj => div_lt_of_lt_mul (h.hi_lt j hj)
  have hsplit : ∀ j < N, K * X j = lo d K X j + Exp.exp d * hi d K X j := fun j _ => by
    rw [lo, hi, add_comm]; exact (div_add_mod _ _).symm
  have e1 := bsum_mul_split (w := d) (f := X) K (lo := lo d K X) (hi := hi d K X) hX hlo hhi hsplit
  haveI : 𝚺₁-Function₁ (fun j => hi d K X (cyc N j 1)) := by definability
  haveI : 𝚺₁-Function₁ (fun j => X (cyc N j s)) := by definability
  haveI : 𝚺₁-Function₁ (fun j => lo d K X j + hi d K X (cyc N j 1)) := by definability
  have hF1 : Fw d K N s X = bsum d (fun j => lo d K X j + hi d K X (cyc N j 1)) N +
      bsum d (fun j => X (cyc N j s)) N :=
    bsum_add (fun j hj => hB j hj) (fun _ _ => rfl)
  have hF2 : bsum d (fun j => lo d K X j + hi d K X (cyc N j 1)) N =
      bsum d (lo d K X) N + bsum d (fun j => hi d K X (cyc N j 1)) N :=
    bsum_add (fun j hj => lt_of_le_of_lt (le_add_of_nonneg_right (Arithmetic.zero_le _)) (hB j hj))
      (fun _ _ => rfl)
  have hc1 := bsum_cyc (w := d) (f := hi d K X) (e := 1) h.N_gt hhi
  have hcs := bsum_cyc (w := d) (f := X) (e := s) h.s_lt hX
  have r1 := rot_identity d N (bsum d (hi d K X) N) 1 h.N_gt.le
  have rs := rot_identity d N (bsum d X N) s h.s_lt.le
  rw [mul_one] at r1
  rw [hF1, hF2, hc1, hcs, Cw]
  calc bsum d (lo d K X) N + rot d N (bsum d (hi d K X) N) 1 + rot d N (bsum d X N) s +
        (Exp.exp (d*N)-1) * (bsum d (hi d K X) N / Exp.exp (d*(N-1)) +
          bsum d X N / Exp.exp (d*(N-s)))
      = bsum d (lo d K X) N + (rot d N (bsum d (hi d K X) N) 1 +
          (Exp.exp (d*N)-1) * (bsum d (hi d K X) N / Exp.exp (d*(N-1)))) +
        (rot d N (bsum d X N) s + (Exp.exp (d*N)-1) * (bsum d X N / Exp.exp (d*(N-s)))) := by ring
    _ = bsum d (lo d K X) N + Exp.exp d * bsum d (hi d K X) N +
        Exp.exp (d*s) * bsum d X N := by rw [r1, rs]
    _ = _ := by rw [← e1]; ring

/-- The true cyclic remainder equals the represented normalized block word. -/
theorem transport_residue :
    ((K + Exp.exp (d*s)) * Cw d N X) % (Exp.exp (d*N)-1) = Fw d K N s X := by
  have hM : 0 < Exp.exp (d*N)-1 := lt_of_le_of_lt (Arithmetic.zero_le _) (F_lt_M h)
  have hm := congrArg (fun z : V => z % (Exp.exp (d*N)-1)) (transport_formula h)
  rw [mod_add hM, mod_mul hM, mod_self, zero_mul, zero_mod, add_zero,
    mod_eq_self_of_lt (F_lt_M h)] at hm
  simpa only [mod_eq_self_of_lt (F_lt_M h)] using hm.symm

end main
#print axioms CompactPartialPackingTransport.transport_formula
#print axioms CompactPartialPackingTransport.transport_residue
end CompactPartialPackingTransport
