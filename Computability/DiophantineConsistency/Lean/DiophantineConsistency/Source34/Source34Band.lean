import DiophantineConsistency.Source34.Source34Kernel
import DiophantineConsistency.Mixed121.Mixed121Band

/-! # One reflected clause band of the source34 tuple

`Mixed121Band` at the source34 tuple. The selector digits
(`Mixed121Band.selDigit`) and the decoder are shared; only the copy and anchor
sources change, because they are read at `T − extraPos j` with the source34
positions `Source34Kernel.extraPos` (the stride-two copy tracks
`1020, 1000, 980, 960` and the anchors).

`band_decomposition` rewrites the weighted band into the input of
`Mixed121Decoder.decode` at `m = 44`, and `band_decode` decodes it. Given
Boolean source digits and no carry against `μ = 1022 + Σ W_k`, either the band
is empty or exactly one tile `i` is selected, and every copy or anchor digit
equals that tile's radix-four digit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34Band
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticCyclicWord ArithmeticWindowDigits ArithmeticBinaryCarry ModelDigitTransfer
open Mixed121Band (selDigit)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The source34 extra position with index `j`, as a total function on `ℕ`. -/
def extraPosN (j : ℕ) : ℕ := if h : j < 44 then Source34Kernel.extraPos ⟨j, h⟩ else 0

theorem extraPos_eq (j : Fin 44) : Source34Kernel.extraPos j = extraPosN j.val := by
  unfold extraPosN; rw [dif_pos j.isLt]

/-- The source digit of copy or anchor index `j` at output cell `k`. -/
def copyDigit (n C k : V) (T : ℕ) (j : ℕ) : V :=
  dig 121 C (cyc n k (((T - extraPosN j : ℕ)) : V))

/-- The weighted band equals the radix-four decoder input. -/
theorem band_decomposition (T : ℕ) (n C k : V)
    (hn : 0 < n) (hk : k < n) (hC : C < Exp.exp (121*n)) :
    (∑ i : Fin 943, ((Mixed121Kernel.clause (Compact943Data.row i) : ℕ) : V) *
        dig 121 (rot 121 n C ((((T - i.val : ℕ)) : V) % n)) k) +
      (∑ j : Fin 44, ((Mixed121Kernel.W j.val : ℕ) : V) *
        dig 121 (rot 121 n C ((((T - Source34Kernel.extraPos j : ℕ)) : V) % n)) k) =
    (∑ i, selDigit n C k T i *
        (1 + Exp.exp 10 * dsum (Exp.exp 2)
          (fun d => (Mixed121Digits.digit (Compact943Data.row i) d : V)) 44)) +
      Exp.exp 10 * dsum (Exp.exp 2) (copyDigit n C k T) 44 := by
  have hi : ∀ i : Fin 943,
      dig 121 (rot 121 n C ((((T - i.val : ℕ)) : V) % n)) k = selDigit n C k T i := by
    intro i
    unfold selDigit
    rw [dig_rot 121 n C _ k (mod_lt _ hn) hk hC, cyc_mod n k _ hn]
  have hj : ∀ j : Fin 44,
      dig 121 (rot 121 n C ((((T - Source34Kernel.extraPos j : ℕ)) : V) % n)) k =
        copyDigit n C k T j.val := by
    intro j
    unfold copyDigit
    rw [dig_rot 121 n C _ k (mod_lt _ hn) hk hC, cyc_mod n k _ hn, extraPos_eq]
  have e1 : (∑ i : Fin 943, ((Mixed121Kernel.clause (Compact943Data.row i) : ℕ) : V) *
        dig 121 (rot 121 n C ((((T - i.val : ℕ)) : V) % n)) k) =
      ∑ i, selDigit n C k T i *
        (1 + Exp.exp 10 * dsum (Exp.exp 2)
          (fun d => (Mixed121Digits.digit (Compact943Data.row i) d : V)) 44) :=
    Finset.sum_congr rfl fun i _ => by rw [hi i, Mixed121Digits.clause_cast, mul_comm]
  have e2 : (∑ j : Fin 44, ((Mixed121Kernel.W j.val : ℕ) : V) *
        dig 121 (rot 121 n C ((((T - Source34Kernel.extraPos j : ℕ)) : V) % n)) k) =
      Exp.exp 10 * dsum (Exp.exp 2) (copyDigit n C k T) 44 := by
    rw [dsum, Finset.sum_range, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hj j, Mixed121Digits.W_cast]; ring
  rw [e1, e2]

/-- **Band decoding.** Boolean source digits with no carry against `μ` give
an empty band or a single selected tile whose digits the copies repeat. -/
theorem band_decode (T : ℕ) (n C k : V)
    (hn : 0 < n) (hk : k < n) (hC : C < Exp.exp (121*n))
    (hsel : ∀ i, selDigit n C k T i ≤ 1) (hcopy : ∀ j < 44, copyDigit n C k T j ≤ 1)
    (h : NoCarry
      ((∑ i : Fin 943, ((Mixed121Kernel.clause (Compact943Data.row i) : ℕ) : V) *
          dig 121 (rot 121 n C ((((T - i.val : ℕ)) : V) % n)) k) +
        (∑ j : Fin 44, ((Mixed121Kernel.W j.val : ℕ) : V) *
          dig 121 (rot 121 n C ((((T - Source34Kernel.extraPos j : ℕ)) : V) % n)) k))
      ((1022 + ∑ j ∈ Finset.range 44, Mixed121Kernel.W j : ℕ) : V)) :
    ((∀ i, selDigit n C k T i = 0) ∧ ∀ j < 44, copyDigit n C k T j = 0) ∨
      ∃ i, CompactSelectorSum.Selected (selDigit n C k T) i ∧
        ∀ j < 44, copyDigit n C k T j = (Mixed121Digits.digit (Compact943Data.row i) j : V) := by
  rw [band_decomposition T n C k hn hk hC, Mixed121Digits.mu_cast] at h
  exact Mixed121Decoder.decode (selDigit n C k T)
    (fun i d => (Mixed121Digits.digit (Compact943Data.row i) d : V)) (copyDigit n C k T) 44
    (Compact943Decoder.count_bound _ hsel)
    (fun i d _ => by exact_mod_cast Mixed121Digits.digit_le_one _ d) hcopy h
end Source34Band
#print axioms Source34Band.band_decomposition
#print axioms Source34Band.band_decode
