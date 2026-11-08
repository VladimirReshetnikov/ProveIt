import DiophantineConsistency.BFS943.DirectBFSConstructedWord
import DiophantineConsistency.BFS943.DirectBFSCoefficientDecoder
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSWordOccupied
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticStandardCasts ArithmeticWindowDigits
open CompactForwardCellInputs DirectBFSConstructedWord DirectBFSModelPayload DirectBFSModelMass
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private theorem cast_sum_generic {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    ((∑ i ∈ s, f i : ℕ):V) = ∑ i ∈ s, (f i:V) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, Nat.cast_add, ih]

theorem payload_sum (i : Fin 943) :
    (∑ j : Fin 41, (2:V)^j.val * payloadBit (DirectBFSDecoder.tileValue (V:=V) i) j) =
      DirectBFSDecoder.tileValue (V:=V) i := by
  let x := CompactCoefficientMass.value (DirectBFSSymbolicKernel.row i)
  have hv : DirectBFSDecoder.tileValue (V:=V) i = (x : V) :=
    (DirectBFSCoefficientDecoder.cast_value i).symm
  have hb (j : Fin 41) : payloadBit (x:V) j = ((x / 2^j.val % 2 : ℕ) : V) := by
    unfold payloadBit
    rw [fbit_eq_div, cast_exp, ← cast_div]
    exact (cast_mod (x / 2^j.val) 2).symm
  have hn : (∑ j : Fin 41, 2^j.val * (x / 2^j.val % 2)) = x := by
    rw [nat_low_bit_sum, Nat.mod_eq_of_lt]
    have hm : DirectBFSSymbolicKernel.row i ∈ DirectBFSSymbolicKernel.rows := List.get_mem _ _
    exact (of_decide_eq_true ((List.all_eq_true.mp DirectBFSCoefficientMass.values_in_range)
      (DirectBFSSymbolicKernel.row i) hm)).2
  rw [hv]
  simp_rw [hb]
  have hvn := congrArg (fun n : ℕ => (n : V)) hn
  simp only [cast_sum_generic, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at hvn
  exact hvn

theorem word_occupied {b : V → V} {N s : V} (hw : DirectBFSLocalWord.Word b N s)
    {j : V} (hj : j < N) :
    (∑ i, ((selectors i : ℕ) : V) * wordSelector b i j) +
      (∑ i, ((copies i : ℕ) : V) * wordPayloadBit b i j) = 1 + Exp.exp 51 := by
  obtain ⟨i,hi⟩ := standard_row (hw.tile_lt j hj)
  have hp : DirectBFSModelPayload.payload (b j) = DirectBFSDecoder.tileValue i := by rw [hi, DirectBFSModelPayload.payload_row]
  unfold wordSelector wordPayloadBit selectors copies
  rw [hp, DirectBFSCoefficientDecoder.finite_decomposition, hi, selector_count, selector_weighted,
    payload_sum, tsub_add_cancel_of_le (DirectBFSDecoder.tileValue_bounds (V := V) i).2.le]
  have hexp : Exp.exp (10 : V) * Exp.exp 41 = Exp.exp 51 := by
    rw [← exp_add]
    congr 1; norm_num
  rw [hexp]

#print axioms DirectBFSWordOccupied.payload_sum
#print axioms DirectBFSWordOccupied.word_occupied
end DirectBFSWordOccupied
