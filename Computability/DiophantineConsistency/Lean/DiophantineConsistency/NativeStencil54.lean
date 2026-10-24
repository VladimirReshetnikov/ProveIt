import DiophantineConsistency.NativeCyclicConvolution
import DiophantineConsistency.NativeClauseBits54

/-!
# The exact nonnegative compact54 current/spatial stencil

The recipe is the whole `K = DC + B*DR` stencil at radix `ρ = 2^89`,
including both clause bands and all four current-copy offsets.  The
coefficient-mass proof is independent of the word length and of collisions
after cyclic folding.  Equality with any materialized port remains an
explicit binding obligation.
-/

namespace DiophantineConsistency.NativeStencil54

open NativeClauseBits54 NativeLocalCoefficients54 NativeModesData54
open NativeCyclicConvolution
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def radix : ℕ := 2 ^ 89
def cellLength : ℕ := 4831

/-- Bit positions follow the west/north/east/south field order of `encode`. -/
def copyPosition (j : Fin 42) : ℕ :=
  if j.val < 11 then 539 + j.val
  else if j.val < 21 then 528 + (j.val - 11)
  else if j.val < 32 then 517 + (j.val - 21)
  else 495 + (j.val - 32)

/-- The 520 supported assignment positions, with their literal positive
local-clause coefficients. The two ignored dummy coefficients are zero. -/
def entries : List (ℕ × ℕ) :=
  (modeList.zipIdx.map fun p =>
    (p.2, selectorCoefficient p.1.2 p.1.1)) ++
  ((List.finRange 42).map fun j => (copyPosition j, copyBitCoefficient j)) ++
  ((List.finRange 8).map fun j => (567 + j.val, rightBitCoefficient j)) ++
  ((List.finRange 8).map fun j => (575 + j.val, leftBitCoefficient j)) ++
  [(583, commonBitCoefficient), (1203, anchorCoefficient), (1807, anchorCoefficient),
    (507, 0), (508, 0)]

theorem entries_length : entries.length = 520 := by decide

theorem entries_mass : (entries.map Prod.snd).sum = 21018633715859000553417 := by decide

/-- All raw stencil monomials, before folding modulo `X^n−1`. -/
def terms : List (ℕ × ℕ) :=
  [(33, 1), (68, 1), (664, 1), (1268, 1)] ++
  (entries.flatMap fun p => [(2409 - p.1, p.2), (3015 - p.1, p.2)]) ++
  [(cellLength + 46, 1)]

theorem terms_length : terms.length = 1045 := by decide

theorem terms_mass : (terms.map Prod.snd).sum = 42037267431718001106839 := by decide

def exponent (i : Fin terms.length) : ℕ := terms[i.val].1
def coefficient (i : Fin terms.length) : ℕ := terms[i.val].2

/-- A symbolic integer coefficient port, without expanding its 434054 bits. -/
def rawWord (ρ : ℕ) : ℕ := (terms.map fun p => p.2 * ρ ^ p.1).sum

private theorem pair_terms_sum (ρ : ℕ) (l : List (ℕ × ℕ)) :
    ((l.flatMap fun p => [(2409 - p.1, p.2), (3015 - p.1, p.2)]).map
      fun p => p.2 * ρ ^ p.1).sum =
    (l.map fun p => p.2 * (ρ ^ (2409 - p.1) + ρ ^ (3015 - p.1))).sum := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, List.map_nil, List.sum_nil, add_zero, ih]
    ring

theorem rawWord_eq (ρ : ℕ) :
    rawWord ρ = ρ ^ 33 + ρ ^ 68 + ρ ^ 664 + ρ ^ 1268 +
      (entries.map fun p => p.2 * (ρ ^ (2409 - p.1) + ρ ^ (3015 - p.1))).sum +
      ρ ^ (cellLength + 46) := by
  simp only [rawWord, terms, List.map_append, List.sum_append, List.map_cons,
    List.sum_cons, List.map_nil, List.sum_nil, one_mul, add_zero, pair_terms_sum]
  omega

theorem sum_coefficient : (∑ i, coefficient i) = 42037267431718001106839 := by
  rw [← Fin.sum_ofFn]
  change (List.ofFn (fun i : Fin terms.length => terms[i.val].2)).sum = _
  rw [List.ofFn_getElem_eq_map]
  exact terms_mass

theorem sum_rawWord (ρ : ℕ) : (∑ i, coefficient i * ρ ^ exponent i) = rawWord ρ := by
  rw [← Fin.sum_ofFn]
  change (List.ofFn (fun i : Fin terms.length => terms[i.val].2 * ρ ^ terms[i.val].1)).sum = _
  rw [List.ofFn_getElem_eq_map terms (fun p => p.2 * ρ ^ p.1)]
  rfl

variable {n : ℕ} [NeZero n]

def folded : ZMod n → ℕ := foldStencil exponent coefficient

theorem folded_mass : mass (folded (n := n)) = 42037267431718001106839 := by
  rw [folded, mass_foldStencil, sum_coefficient]

theorem folded_word (ρ : ℕ) (hρ : 1 ≤ ρ) :
    word ρ (folded (n := n)) ≡ rawWord ρ [MOD ρ ^ n - 1] := by
  simpa only [folded, sum_rawWord] using word_foldStencil (n := n) hρ exponent coefficient

/-- The exact coefficient mass leaves room even for three-quarter-radix
temporal digits and for a strict gap below the Mersenne modulus. -/
theorem carry_budget : 42037267431718001106839 * 3 + 3 * 2 ^ 87 + 2 ≤ radix := by decide

theorem no_carry (c r : ZMod n → ℕ) (hc : ∀ i, c i ≤ 3)
    (hr : ∀ i, r i ≤ 3 * 2 ^ 87) :
    (∀ k, convolution folded c k + r k < radix - 1) ∧
      word radix (fun k => convolution folded c k + r k) < radix ^ n - 1 := by
  apply no_carry_representative (by decide : 1 < radix) folded c r hc hr
  rw [folded_mass]
  exact carry_budget

/-- A raw-stencil transport equation and the actual word mask imply every
local convolution mask test.  No accepted-clause or one-hot premise is used. -/
theorem transport_mask_digits {F : ℕ} (c r m : ZMod n → ℕ)
    (hc : ∀ i, c i ≤ 3) (hr : ∀ i, r i ≤ 3 * 2 ^ 87)
    (hm : ∀ i, m i < radix)
    (htransport : rawWord radix * word radix c + word radix r ≡ F [MOD radix ^ n - 1])
    (hF : F < radix ^ n - 1) (hmask : F &&& word radix m = 0) :
    ∀ k, (convolution folded c k + r k) &&& m k = 0 := by
  have htransport' : word radix (folded (n := n)) * word radix c + word radix r ≡
      F [MOD radix ^ n - 1] :=
    (((folded_word radix (by decide : 1 ≤ radix)).mul_right (word radix c)).add_right
      (word radix r)).trans htransport
  apply NativeCyclicConvolution.transport_mask_digits rfl (by decide : 1 < radix)
    folded c r m hc hr hm _ htransport' hF hmask
  rw [folded_mass]
  exact carry_budget

end DiophantineConsistency.NativeStencil54
