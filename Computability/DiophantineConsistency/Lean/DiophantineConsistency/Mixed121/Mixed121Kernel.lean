import DiophantineConsistency.Compact44.CompactSymbolicKernelGeneric
import DiophantineConsistency.Compact44.Compact943Data

/-! # The wang943-mixed-121x8801 coefficient tuple, symbolically

The tuple of `31-sun10/coefficients/COEFFICIENT_PROOF.md` §1, used by package
55's and 59's fourteen-positive 52 / 79 and package 132's fifteen-integer
44 / 111. It has `ρ = 2^121`, period `L = 8801` and `B = ρ^L`. Its ports are
`β = B − 1`, `K = D_C + B·ρ^42`, `MC` and `MF_source = MF_native + B − 1`.

The 943 tile rows are the tree's `Compact943Data.rows`. They are the compact44
rows, in the same order. A tile `(x₀, x₁, x₂, x₃)` has the radix-four clause
coefficient `1 + Σₜ Σⱼ<10 bitⱼ(xₜ + 512)·W(10t+j) + W40 + W41 + W42 + W43`,
with `W j = 2^(10+2j)`. The 44 further support positions are the four copy
offsets `1023, 1013, 1003, 983` (ten each) and the four anchors
`1095, 1096, 2195, 3296`. They carry `W k`. The two dummies `1063, 1064` carry
zero.

`research/mixed121-calibration/tools/check_recipe.py` gives external evidence
for this transcription. It implements the same recipe from the Lean rows and
reproduces all four package payloads byte for byte. That is a finite check
outside Lean. It is not a Lean theorem about the payload files.

This module fixes only the symbolic kernel, its cast identity and the support
facts that `decide` settles. The decoding, packing and controller layers of a
calibration are separate work. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Mixed121Kernel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic CompactSymbolicKernelGeneric
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The radix `ρ = 2^121`. -/
def rho : ℕ := 2^121
/-- The period `L = 8801`. -/
def period : ℕ := 8801

/-- The field weights `W j = 2^(10+2j)`. -/
def W (j : ℕ) : ℕ := 2^(10+2*j)

/-- The ten radix-four field digits of one slot label `x` in slot `t`. -/
def field (x t : ℕ) : ℕ := ∑ j : Fin 10, ((x+512)/2^j.val % 2) * W (10*t+j.val)

/-- The clause coefficient of a tile `(west, north, east, south)`. -/
def clause (tile : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  1 + field tile.1 0 + field tile.2.1 1 + field tile.2.2.1 2 + field tile.2.2.2 3 +
    W 40 + W 41 + W 42 + W 43

/-- The 44 non-tile support positions with nonzero coefficient: four copy
blocks of ten (offsets `1023, 1013, 1003, 983`), then the four anchors. -/
def extraPositions : List ℕ :=
  (List.range 10).map (1023 + ·) ++ (List.range 10).map (1013 + ·) ++
    (List.range 10).map (1003 + ·) ++ (List.range 10).map (983 + ·) ++
    [1095, 1096, 2195, 3296]

theorem extraPositions_length : extraPositions.length = 44 := by decide

def extraPos (k : Fin 44) : ℕ :=
  extraPositions.get ⟨k.val, by rw [extraPositions_length]; exact k.isLt⟩

/-- The kernel `K = D_C + ρ^L·ρ^42`, parameterized by the radix. -/
def paramKernel (r : ℕ) : ℕ :=
  r^30+r^62+r^1100+r^2200 +
  (∑ i : Fin 943, clause (Compact943Data.row i) * (r^(4393-i.val)+r^(5495-i.val))) +
  (∑ k : Fin 44, W k.val * (r^(4393-extraPos k)+r^(5495-extraPos k))) +
  r^8801*r^42

theorem cast_paramKernel (r : ℕ) :
    ((paramKernel r:ℕ):V) =
      ((r:V)^30+(r:V)^62+(r:V)^1100+(r:V)^2200)
      + (∑ i : Fin 943,
          (clause (Compact943Data.row i):V)*((r:V)^(4393-i.val)+(r:V)^(5495-i.val)))
      + (∑ k : Fin 44, ((W k.val:ℕ):V)*((r:V)^(4393-extraPos k)+(r:V)^(5495-extraPos k)))
      + (r:V)^8801*(r:V)^42 := by
  exact cast_kernel_generic r 30 62 1100 2200 4393 5495 8801 42
    (fun i : Fin 943 => i.val) (fun i => clause (Compact943Data.row i))
    (fun k : Fin 44 => extraPos k) (fun k => W k.val)

/-! ## Support facts -/

/-- The support `E`, in increasing order: the 943 tile rows `0..942`, the copy
blocks `983..992` and `1003..1032`, the dummies `1063, 1064` and the anchors
`1095, 1096, 2195, 3296`. -/
def support : List ℕ :=
  List.range 943 ++ (List.range 10).map (983 + ·) ++ (List.range 30).map (1003 + ·) ++
    [1063, 1064, 1095, 1096, 2195, 3296]

/-! The difference facts are quadratic as list scans; the kernel did not finish
one of them in twelve minutes. They are checked instead on the bitmask
`Σ_{e ∈ l} 2^e`, whose `&&&`, `^^^` and `>>>` the kernel evaluates natively,
and transferred back to membership by `testBit_maskOf`. -/

/-- The bitmask of a list of positions. -/
def maskOf : List ℕ → ℕ
  | [] => 0
  | e :: l => 2^e ||| maskOf l

theorem testBit_maskOf {l : List ℕ} {e : ℕ} (h : e ∈ l) : (maskOf l).testBit e = true := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp [maskOf]
    · simp [maskOf, ih h]

theorem mem_of_testBit_maskOf {l : List ℕ} {e : ℕ} (h : (maskOf l).testBit e = true) :
    e ∈ l := by
  induction l with
  | nil => simp [maskOf] at h
  | cons a l ih =>
    simp only [maskOf, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow,
      decide_eq_true_eq] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem testBit_two_pow_ne {n e : ℕ} (h : e ≠ n) : (2^n).testBit e = false := by
  rw [Nat.testBit_two_pow]; exact decide_eq_false (fun h' => h h'.symm)

/-- A linear check that a list is strictly increasing. -/
def increasing : List ℕ → Bool
  | a :: b :: l => decide (a < b) && increasing (b :: l)
  | _ => true

theorem pairwise_of_increasing : ∀ {l : List ℕ}, increasing l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.Pairwise.cons (by simp) List.Pairwise.nil
  | a :: b :: l, h => by
    simp only [increasing, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_increasing h.2
    refine List.Pairwise.cons ?_ ih
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

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

/-- `1102` is not a difference of two support positions. So the two clause
targets `4393 − e` and `5495 − e'` never coincide modulo `L`, because every
position is below `4393` and the span is below `L`. -/
theorem clause_targets_disjoint {e : ℕ} (he : e ∈ support) : e + 1102 ∉ support := by
  intro h
  have h' : (maskOf support).testBit (1102 + e) = true := by
    rw [Nat.add_comm]; exact testBit_maskOf h
  have := congrArg (fun m => m.testBit e) clause_mask
  simp [Nat.testBit_and, Nat.testBit_shiftRight, testBit_maskOf he, h'] at this

theorem anchor_mask : (maskOf support ^^^ 2^2195) &&& (maskOf support >>> 1101) = 0 := by
  decide +kernel

/-- `1101` is a difference of two support positions only as `3296 − 2195`.
So the anchor targets `2195 − e` and `3296 − e'` meet modulo `L` only at
residue zero. -/
theorem anchor_targets_meet_at_zero {e : ℕ} (he : e ∈ support) (h : e + 1101 ∈ support) :
    e = 2195 := by
  refine Decidable.byContradiction fun hne => ?_
  have h' : (maskOf support).testBit (1101 + e) = true := by
    rw [Nat.add_comm]; exact testBit_maskOf h
  have h2 := testBit_two_pow_ne (n := 2195) hne
  have := congrArg (fun m => m.testBit e) anchor_mask
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, testBit_maskOf he, h',
    h2, Nat.zero_testBit, Bool.xor_false, Bool.and_true, Bool.true_eq_false] at this
/-- Every tile label is below 512, so `x + 512` has exactly ten bits. -/
theorem labels_below : Compact943Data.rows.all (fun t =>
    decide (t.1 < 512 ∧ t.2.1 < 512 ∧ t.2.2.1 < 512 ∧ t.2.2.2 < 512)) = true := by decide

end Mixed121Kernel

#print axioms Mixed121Kernel.extraPositions_length
#print axioms Mixed121Kernel.cast_paramKernel
#print axioms Mixed121Kernel.support_length
#print axioms Mixed121Kernel.support_nodup
#print axioms Mixed121Kernel.support_below_target
#print axioms Mixed121Kernel.extra_mem
#print axioms Mixed121Kernel.clause_targets_disjoint
#print axioms Mixed121Kernel.anchor_targets_meet_at_zero
#print axioms Mixed121Kernel.labels_below
