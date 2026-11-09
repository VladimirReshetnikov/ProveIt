import DiophantineConsistency.ModelDigitTransfer

/-! # The low code mask at an injective weight table, in every model of `𝗜𝚺₁`

For `b = 2ᵏ ≤ B = 2^v`, a standard injective weight table `w : Fin m → ℕ` with
all weights below `n`, and `g < Bⁿ`, no carry between `g` and the code mask
(`B − b` at the weights, `B − 1` elsewhere) holds iff `g = Σᵢ zᵢ B^{wᵢ}` with
every `zᵢ < b` (`noCarry_code_iff_weights`). This is
`ModelDigitTransfer.noCarry_code_iff` with the digit sum regrouped over the
weight table. Weight `0` is allowed (package 101's translated layout puts `J`
there). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Nine121.LowMask
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDigitTransfer ArithmeticBinaryCarry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The positions of a weight table. -/
def Pos {m : ℕ} (w : Fin m → ℕ) (j : ℕ) : Prop := ∃ i, w i = j

instance {m : ℕ} (w : Fin m → ℕ) : DecidablePred (Pos w) := fun j =>
  inferInstanceAs (Decidable (∃ i, w i = j))

/-- A digit sum supported on the weights is the weight-indexed sum. -/
theorem dsum_weights {m : ℕ} (B : V) (w : Fin m → ℕ) (hw : Function.Injective w) (n : ℕ)
    (hn : ∀ i, w i < n) (f : ℕ → V) (hf : ∀ j < n, ¬ Pos w j → f j = 0) :
    dsum B f n = ∑ i, f (w i) * B ^ w i := by
  unfold dsum
  have himg : Finset.univ.image w ⊆ Finset.range n := by
    intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (hn i)
  rw [← Finset.sum_subset himg]
  · rw [Finset.sum_image (fun i _ i' _ h => hw h)]
  · intro j hj hnot
    have hjn := Finset.mem_range.mp hj
    have hp : ¬ Pos w j := by
      rintro ⟨i, rfl⟩
      exact hnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    rw [hf j hjn hp, zero_mul]

/-- **The low mask.** -/
theorem noCarry_code_iff_weights {k v : V} (hkv : k ≤ v) {m : ℕ} (w : Fin m → ℕ)
    (hw : Function.Injective w) (n : ℕ) (hn : ∀ i, w i < n) (g : V)
    (hg : g < Exp.exp v ^ n) :
    NoCarry g (dsum (Exp.exp v) (codeMask (Exp.exp k) (Exp.exp v) (Pos w)) n) ↔
      ∃ z : Fin m → V, (∀ i, z i < Exp.exp k) ∧ g = ∑ i, z i * Exp.exp v ^ w i := by
  have hB : 0 < Exp.exp v := exp_pos v
  have hbB : Exp.exp k ≤ Exp.exp v := exp_monotone_le.mpr hkv
  rw [noCarry_code_iff hkv n (Pos w) g hg]
  have hgd : g = dsum (Exp.exp v) (fun j => g / Exp.exp v ^ j % Exp.exp v) n := by
    rw [← mod_pow_eq_dsum g _ hB n, mod_eq_self_of_lt hg]
  constructor
  · intro h
    refine ⟨fun i => g / Exp.exp v ^ w i % Exp.exp v, fun i => (h (w i) (hn i)).1 ⟨i, rfl⟩, ?_⟩
    conv_lhs => rw [hgd]
    exact dsum_weights _ w hw n hn _ (fun j hj hp => (h j hj).2 hp)
  · rintro ⟨z, hz, rfl⟩
    -- the digits of `Σ zᵢ B^{wᵢ}`
    let f : ℕ → V := fun j => if h : Pos w j then z (Classical.choose h) else 0
    have hfw : ∀ i, f (w i) = z i := by
      intro i
      have h : Pos w (w i) := ⟨i, rfl⟩
      simp only [f, dif_pos h]
      congr 1
      exact hw (Classical.choose_spec h)
    have hf0 : ∀ j < n, ¬ Pos w j → f j = 0 := fun j _ hp => by simp only [f, dif_neg hp]
    have hflt : ∀ j < n, f j < Exp.exp v := by
      intro j _
      by_cases hp : Pos w j
      · simp only [f, dif_pos hp]; exact lt_of_lt_of_le (hz _) hbB
      · simp only [f, dif_neg hp]; exact hB
    have hsum : ∑ i, z i * Exp.exp v ^ w i = dsum (Exp.exp v) f n := by
      rw [dsum_weights _ w hw n hn f hf0]
      exact Finset.sum_congr rfl (fun i _ => by rw [hfw])
    have hdig := dsum_digit (Exp.exp v) hB f n hflt
    intro j hj
    rw [hsum, hdig j hj]
    refine ⟨fun hp => ?_, fun hp => hf0 j hj hp⟩
    obtain ⟨i, rfl⟩ := hp
    rw [hfw]; exact hz i

end Nine121.LowMask

#print axioms Nine121.LowMask.dsum_weights
#print axioms Nine121.LowMask.noCarry_code_iff_weights
