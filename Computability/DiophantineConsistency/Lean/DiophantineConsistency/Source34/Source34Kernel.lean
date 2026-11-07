import DiophantineConsistency.Mixed121.Mixed121Kernel

/-! # The source34 coefficient tuple, symbolically

The "mixed-parity-unrounded-1064921" tuple of `source34_coefficients.md`, used
by package 132's fifteen-integer 44 / 111. It shares with the 121x8801 tuple
(`Mixed121Kernel`) the radix `ρ = 2^121`, the period `L = 8801`, the 943 rows,
the clause coefficients `Mixed121Kernel.clause` and the weights
`Mixed121Kernel.W`. Its kernel is `K = D_C + B·ρ` with

  `D_C = ρ^40 + ρ^41 + ρ^1100 + ρ^2200 + Σ_{e∈E} c_e (ρ^(4393−e) + ρ^(5495−e))`.

The 44 non-tile support positions are parity-separated copy tracks
`o_t + 2j` (`o = 1020, 1000, 980, 960` for west, north, east, south, `j < 10`)
carrying `W (10t+j)`, then the four anchors `1095, 1096, 2195, 3296` carrying
`W 40 … W 43`.

`research/source34-calibration/tools/check_recipe.py` gives external evidence
for the transcription: from the same Lean rows it reproduces all six source34
payloads byte for byte. That is a finite check outside Lean. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Source34Kernel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic CompactSymbolicKernelGeneric
open Mixed121Kernel (W clause maskOf testBit_maskOf mem_of_testBit_maskOf testBit_two_pow_ne
  increasing pairwise_of_increasing)
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The 44 non-tile support positions with nonzero coefficient: four
stride-two copy tracks (offsets `1020, 1000, 980, 960`), then the anchors. -/
def extraPositions : List ℕ :=
  (List.range 10).map (1020 + 2 * ·) ++ (List.range 10).map (1000 + 2 * ·) ++
    (List.range 10).map (980 + 2 * ·) ++ (List.range 10).map (960 + 2 * ·) ++
    [1095, 1096, 2195, 3296]

theorem extraPositions_length : extraPositions.length = 44 := by decide

def extraPos (k : Fin 44) : ℕ :=
  extraPositions.get ⟨k.val, by rw [extraPositions_length]; exact k.isLt⟩

/-- The kernel `K = D_C + ρ^L·ρ`, parameterized by the radix. -/
def paramKernel (r : ℕ) : ℕ :=
  r^40+r^41+r^1100+r^2200 +
  (∑ i : Fin 943, clause (Compact943Data.row i) * (r^(4393-i.val)+r^(5495-i.val))) +
  (∑ k : Fin 44, W k.val * (r^(4393-extraPos k)+r^(5495-extraPos k))) +
  r^8801*r^1

theorem cast_paramKernel (r : ℕ) :
    ((paramKernel r:ℕ):V) =
      ((r:V)^40+(r:V)^41+(r:V)^1100+(r:V)^2200)
      + (∑ i : Fin 943,
          (clause (Compact943Data.row i):V)*((r:V)^(4393-i.val)+(r:V)^(5495-i.val)))
      + (∑ k : Fin 44, ((W k.val:ℕ):V)*((r:V)^(4393-extraPos k)+(r:V)^(5495-extraPos k)))
      + (r:V)^8801*(r:V)^1 := by
  exact cast_kernel_generic r 40 41 1100 2200 4393 5495 8801 1
    (fun i : Fin 943 => i.val) (fun i => clause (Compact943Data.row i))
    (fun k : Fin 44 => extraPos k) (fun k => W k.val)

/-! ## Support facts -/

/-- The support `E`, in increasing order: the 943 tile rows `0..942`, the even
copy positions `960, 962, …, 1038`, the dummies `1063, 1064` and the anchors
`1095, 1096, 2195, 3296`. -/
def support : List ℕ :=
  List.range 943 ++ (List.range 40).map (960 + 2 * ·) ++
    [1063, 1064, 1095, 1096, 2195, 3296]

theorem support_length : support.length = 989 := by decide
theorem support_increasing : increasing support = true := by decide +kernel
theorem support_nodup : support.Nodup :=
  (pairwise_of_increasing support_increasing).imp Nat.ne_of_lt
theorem support_below_target : support.all (· < 4393) = true := by decide +kernel

theorem extra_mask : maskOf extraPositions &&& maskOf support = maskOf extraPositions := by
  decide +kernel

/-- The 44 copy and anchor positions lie in the support. -/
theorem extra_mem {e : ℕ} (h : e ∈ extraPositions) : e ∈ support := by
  have := testBit_maskOf h
  rw [← extra_mask, Nat.testBit_and, Bool.and_eq_true] at this
  exact mem_of_testBit_maskOf this.2

theorem clause_mask : maskOf support &&& (maskOf support >>> 1102) = 0 := by decide +kernel

/-- `1102` is not a difference of two support positions. -/
theorem clause_targets_disjoint {e : ℕ} (he : e ∈ support) : e + 1102 ∉ support := by
  intro h
  have h' : (maskOf support).testBit (1102 + e) = true := by
    rw [Nat.add_comm]; exact testBit_maskOf h
  have := congrArg (fun m => m.testBit e) clause_mask
  simp [Nat.testBit_and, Nat.testBit_shiftRight, testBit_maskOf he, h'] at this

theorem anchor_mask : (maskOf support ^^^ 2^2195) &&& (maskOf support >>> 1101) = 0 := by
  decide +kernel

/-- `1101` is a difference of two support positions only as `3296 − 2195`. -/
theorem anchor_targets_meet_at_zero {e : ℕ} (he : e ∈ support) (h : e + 1101 ∈ support) :
    e = 2195 := by
  refine Decidable.byContradiction fun hne => ?_
  have h' : (maskOf support).testBit (1101 + e) = true := by
    rw [Nat.add_comm]; exact testBit_maskOf h
  have h2 := testBit_two_pow_ne (n := 2195) hne
  have := congrArg (fun m => m.testBit e) anchor_mask
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, testBit_maskOf he, h',
    h2, Nat.zero_testBit, Bool.xor_false, Bool.and_true, Bool.true_eq_false] at this

end Source34Kernel

#print axioms Source34Kernel.extraPositions_length
#print axioms Source34Kernel.cast_paramKernel
#print axioms Source34Kernel.support_length
#print axioms Source34Kernel.support_nodup
#print axioms Source34Kernel.support_below_target
#print axioms Source34Kernel.extra_mem
#print axioms Source34Kernel.clause_targets_disjoint
#print axioms Source34Kernel.anchor_targets_meet_at_zero
