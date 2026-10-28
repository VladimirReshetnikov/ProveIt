import DiophantineConsistency.NativeSparseDigits54

/-! # Exact local contributions at the two native clause bands

Periodic sparsity removes every current-copy, spatial and opposite-band
stencil contribution at these targets. Temporal rotation is retained;
this statement does not assume or prove its phase alignment.
-/

namespace DiophantineConsistency.NativeCleanBands54

open NativeCyclicConvolution NativeStencil54 NativeSparseDigits54
  NativeSourceMask NativeBinaryScale
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- A deliberately coarse enclosure sufficient to separate the bands. -/
abbrev CoarseSupport (j : ℕ) : Prop := j ≤ 583 ∨ j = 1203 ∨ j = 1807

private theorem coarse_positions :
    OnePageTuple54.assignmentPositions.all
      (fun j => decide (CoarseSupport j)) = true := by decide

theorem entries_coarse {p : ℕ × ℕ} (hp : p ∈ entries) : CoarseSupport p.1 := by
  have hm : p.1 ∈ entries.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
  rw [← OnePageTuple54.assignmentPositions_eq] at hm
  exact of_decide_eq_true ((List.all_eq_true.mp coarse_positions) p.1 hm)

theorem support_coarse {j : ℕ} (hj : j ∈ support) : CoarseSupport j := by
  have hm : j ∈ NativeLowPort54.positions := List.mem_toFinset.mp hj
  rw [NativeLowPort54.positions, ← OnePageTuple54.assignmentPositions_eq] at hm
  exact of_decide_eq_true ((List.all_eq_true.mp coarse_positions) j (List.mem_filter.mp hm).1)

variable {N : ℕ} [NeZero (N * cellLength)]

/-- Residues of cyclic subtraction agree modulo the native cell length,
including a one-cell cyclic word and offsets beyond the whole word. -/
theorem subtraction_residue (k : ZMod (N * cellLength)) (e : ℕ) :
    ((k - (e : ZMod (N * cellLength))).val + e) % cellLength = k.val % cellLength := by
  have he : (((k - (e : ZMod (N * cellLength))).val + e : ℕ) :
      ZMod (N * cellLength)) = (k.val : ZMod (N * cellLength)) := by
    simp only [Nat.cast_add, ZMod.natCast_zmod_val, sub_add_cancel]
  have hm := (ZMod.natCast_eq_natCast_iff _ _ _).mp he
  exact hm.of_dvd ⟨N, by ring⟩

/-- Arithmetic exclusion of the source of one stencil term forces that
term's assignment digit to vanish. -/
theorem digit_zero_of_avoid (c : ZMod (N * cellLength) → ℕ)
    (hc : ∀ k, c k < 2 ^ periodicBits k) (k : ZMod (N * cellLength))
    (e t : ℕ) (hk : k.val % cellLength = t)
    (ha : ∀ j, CoarseSupport j → (j + e) % cellLength ≠ t) :
    c (k - (e : ZMod (N * cellLength))) = 0 := by
  by_cases hm : (k - (e : ZMod (N * cellLength))).val % cellLength ∈ support
  · have he := subtraction_residue k e
    rw [hk] at he
    have he' : ((k - (e : ZMod (N * cellLength))).val % cellLength + e) % cellLength = t := by
      simpa only [Nat.add_mod, Nat.mod_mod] using he
    exact False.elim (ha _ (support_coarse hm) he')
  · exact assignment_sparse c hc _ hm

private theorem bare_avoid (t e j : ℕ) (ht : t = 2409 ∨ t = 3015)
    (he : e = 33 ∨ e = 68 ∨ e = 664 ∨ e = 1268 ∨ e = cellLength + 46)
    (hj : CoarseSupport j) : (j + e) % cellLength ≠ t := by
  unfold CoarseSupport cellLength at *
  rcases ht with rfl | rfl <;>
    rcases he with rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with hj | rfl | rfl <;> omega

private theorem opposite_avoid (j p : ℕ) (hj : CoarseSupport j)
    (hp : CoarseSupport p) :
    (j + (3015 - p)) % cellLength ≠ 2409 ∧
      (j + (2409 - p)) % cellLength ≠ 3015 := by
  unfold CoarseSupport cellLength at *
  rcases hj with hj | rfl | rfl <;>
    rcases hp with hp | rfl | rfl <;> omega

omit [NeZero (N * cellLength)] in
private theorem pair_convolution (c : ZMod (N * cellLength) → ℕ)
    (k : ZMod (N * cellLength)) (l : List (ℕ × ℕ)) :
    ((l.flatMap fun p : ℕ × ℕ => [((2409 - p.1 : ℕ), p.2), ((3015 - p.1 : ℕ), p.2)]).map
      fun p => p.2 * c (k - (p.1 : ZMod (N * cellLength)))).sum =
    (l.map fun p => p.2 * (c (k - ((2409 - p.1 : ℕ) : ZMod (N * cellLength))) +
      c (k - ((3015 - p.1 : ℕ) : ZMod (N * cellLength))))).sum := by
  simp [List.flatMap, List.sum_flatten, List.map_map, Function.comp_def, mul_add]

/-- An exact stencil expansion; no collision after cyclic folding is lost. -/
theorem convolution_entries (c : ZMod (N * cellLength) → ℕ)
    (k : ZMod (N * cellLength)) :
    convolution folded c k =
      c (k - ((33 : ℕ) : ZMod (N * cellLength))) + c (k - ((68 : ℕ) : ZMod (N * cellLength))) + c (k - ((664 : ℕ) : ZMod (N * cellLength))) + c (k - ((1268 : ℕ) : ZMod (N * cellLength))) +
      (entries.map fun p => p.2 *
        (c (k - ((2409 - p.1 : ℕ) : ZMod (N * cellLength))) +
         c (k - ((3015 - p.1 : ℕ) : ZMod (N * cellLength))))).sum +
      c (k - ((cellLength + 46 : ℕ) : ZMod (N * cellLength))) := by
  rw [folded, convolution_foldStencil, ← Fin.sum_ofFn]
  change (List.ofFn (fun i : Fin terms.length =>
    terms[i.val].2 * c (k - (terms[i.val].1 : ZMod (N * cellLength))))).sum = _
  rw [List.ofFn_getElem_eq_map terms (fun p => p.2 * c (k - (p.1 : ZMod (N * cellLength))))]
  simp only [terms, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    List.map_nil, List.sum_nil, one_mul, add_zero, pair_convolution]
  ring

/-- The local coefficient sum at a target in one cell. -/
def localContribution (c : ZMod (N * cellLength) → ℕ)
    (k : ZMod (N * cellLength)) (t : ℕ) : ℕ :=
  (entries.map fun p => p.2 * c (k - (t : ZMod (N * cellLength)) + p.1)).sum

omit [NeZero (N * cellLength)] in
private theorem local_index (k : ZMod (N * cellLength)) {t p : ℕ} (hp : p ≤ t) :
    k - ((t - p : ℕ) : ZMod (N * cellLength)) = k - t + p := by
  rw [Nat.cast_sub hp]
  abel

/-- The first clause target receives exactly its own local coefficient sum. -/
theorem convolution_left (c : ZMod (N * cellLength) → ℕ)
    (hc : ∀ k, c k < 2 ^ periodicBits k) (k : ZMod (N * cellLength))
    (hk : k.val % cellLength = 2409) :
    convolution folded c k = localContribution c k 2409 := by
  have hz (e : ℕ) (he : e = 33 ∨ e = 68 ∨ e = 664 ∨ e = 1268 ∨ e = cellLength + 46) :
      c (k - (e : ZMod (N * cellLength))) = 0 :=
    digit_zero_of_avoid c hc k e 2409 hk (fun j hj => bare_avoid _ _ _ (Or.inl rfl) he hj)
  rw [convolution_entries, hz 33 (by simp), hz 68 (by simp), hz 664 (by simp),
    hz 1268 (by simp), hz (cellLength + 46) (by simp)]
  simp only [zero_add, add_zero, localContribution]
  congr 1
  apply List.map_congr_left
  intro p hp
  have hb := entries_coarse hp
  have hz' := digit_zero_of_avoid c hc k (3015 - p.1) 2409 hk
    (fun j hj => (opposite_avoid j p.1 hj hb).1)
  rw [hz', add_zero, local_index k (show p.1 ≤ 2409 by unfold CoarseSupport at hb; omega)]

/-- The second clause target receives exactly its own local coefficient sum. -/
theorem convolution_right (c : ZMod (N * cellLength) → ℕ)
    (hc : ∀ k, c k < 2 ^ periodicBits k) (k : ZMod (N * cellLength))
    (hk : k.val % cellLength = 3015) :
    convolution folded c k = localContribution c k 3015 := by
  have hz (e : ℕ) (he : e = 33 ∨ e = 68 ∨ e = 664 ∨ e = 1268 ∨ e = cellLength + 46) :
      c (k - (e : ZMod (N * cellLength))) = 0 :=
    digit_zero_of_avoid c hc k e 3015 hk (fun j hj => bare_avoid _ _ _ (Or.inr rfl) he hj)
  rw [convolution_entries, hz 33 (by simp), hz 68 (by simp), hz 664 (by simp),
    hz 1268 (by simp), hz (cellLength + 46) (by simp)]
  simp only [zero_add, add_zero, localContribution]
  congr 1
  apply List.map_congr_left
  intro p hp
  have hb := entries_coarse hp
  have hz' := digit_zero_of_avoid c hc k (2409 - p.1) 3015 hk
    (fun j hj => (opposite_avoid j p.1 hj hb).2)
  rw [hz', zero_add, local_index k (show p.1 ≤ 3015 by unfold CoarseSupport at hb; omega)]

/-- The literal source yields both local clause-band mask tests with its
reconstructed sparse assignment. The temporal contribution is displayed
and still requires alignment; it is not silently discarded. -/
theorem source_clean_bands (ports : Fin 4 → ℤ) {MF : ℕ}
    (h : Interface ports (89 * cellLength) NativeLowPort54.lowPort MF)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, SplitCertificate59.sourceRows ports (fun i => (x i : ℤ)) k = 0)
    (hq : sourceQ ports x = (2 ^ (89 * cellLength)) ^ N)
    (hK : (ports 1).toNat = rawWord radix)
    (m : ZMod (N * cellLength) → ℕ) (hm : ∀ k, m k < radix)
    (hM : word radix m = MF * x 0 - 1) :
    ∃ c : ZMod (N * cellLength) → ℕ,
      word radix c = gap ports x ∧ c 0 = 1 ∧
      (∀ k, c k < 2 ^ periodicBits k) ∧
      (∀ k, k.val % cellLength = 2409 →
        (localContribution c k 2409 + NativeWindowConvolution54.temporalDigits x c k) &&& m k = 0) ∧
      (∀ k, k.val % cellLength = 3015 →
        (localContribution c k 3015 + NativeWindowConvolution54.temporalDigits x c k) &&& m k = 0) := by
  obtain ⟨c, hC, h0, hbits, _, hmask⟩ :=
    source_sparse_convolution ports h x hx hs hq hK m hm hM
  refine ⟨c, hC, h0, hbits, ?_, ?_⟩
  · intro k hk
    simpa only [convolution_left c hbits k hk] using hmask k
  · intro k hk
    simpa only [convolution_right c hbits k hk] using hmask k

end DiophantineConsistency.NativeCleanBands54
