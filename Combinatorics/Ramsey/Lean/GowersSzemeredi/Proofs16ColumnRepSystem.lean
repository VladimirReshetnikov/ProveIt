import GowersSzemeredi.Proofs16RepresentedMap
import GowersSzemeredi.Proofs16CorrelationWitnessCount
import GowersSzemeredi.Proofs16BohrLowerBound

/-! One column of Milićević's Proposition 5.1 with robust representations,
in `ℤ/N`.

Let `f` be a Freiman 8-homomorphism on `B ⊆ ℤ/N`, with `β = |B|/N`, and
let `S = commonLargeSpectrum B B (√β³/4)`. Then (`column_rep_system`):
* `|S| ≤ 16/β²`;
* the induced map `repMap B f` is Freiman-linear on `B(S; 1/(4π))`;
* every `d ∈ B(S; 1/(4π))` has at least `β⁴N³/4` representations
  `d = a + e − b − c` with `a, e, b, c ∈ B`.

The count comes from the robust self-correlation `robust_self_correlation`
and its exact interpretation `mixed_self_correlation_eq_card`, through an
injection of `fourDifferenceTriples` into four-tuples
(`fourDifferenceTriples_card_le_reps`). This is Proposition 5.1 (ii) in
robust form: every representing four-tuple is a witness, by `repMap_spec`.

`column_witness_card_ge` turns this into a dense witness set,
`|{q ∈ B⁴ : a+e−b−c ∈ B(S;1/(4π))}| ≥ β⁴N⁴/(4·13^{|S|})`, using the Bohr
lower bound `N ≤ 13^{|S|}·|B(S;1/(4π))|`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The four-tuples of `B` representing `d`. -/
def repTuples {N : Nat} [NeZero N] (B : Finset (ZMod N)) (d : ZMod N) : Finset (Fin 4 → ZMod N) :=
  Finset.univ.filter fun q => (∀ i, q i ∈ B) ∧ fourSum q = d

/-- Correlation triples inject into representing four-tuples. -/
theorem fourDifferenceTriples_card_le_reps {N : Nat} [NeZero N] (B : Finset (ZMod N))
    (d : ZMod N) : (fourDifferenceTriples B d).card ≤ (repTuples B d).card := by
  apply Finset.card_le_card_of_injOn
    (fun p : ZMod N × ZMod N × ZMod N => ![p.2.1, p.2.2 - (p.1 - d), p.2.1 - p.1, p.2.2])
  · intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := (Finset.mem_filter.mp hp).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro i
      fin_cases i <;> simpa
    · simp only [fourSum]
      simp
      ring
  · intro p _ p' _ h
    have h0 := congrFun h 0
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    simp at h0 h2 h3
    have ht : p.1 = p'.1 := by linear_combination h0 - h2
    exact Prod.ext ht (Prod.ext h0 h3)

/-- **One column with robust representations.** -/
theorem column_rep_system {N : Nat} [NeZero N] (B : Finset (ZMod N)) (f : ZMod N → ZMod N)
    (hf : FreimanHom 8 B f) (hB : B.Nonempty) :
    let β : Real := B.card / N
    let S := commonLargeSpectrum B B (Real.sqrt (β ^ 3) / 4)
    (S.card : Real) ≤ 16 / β ^ 2 ∧
      IsFreimanLinearOn (bohr S (1 / (4 * Real.pi))) (repMap B f) ∧
      ∀ d ∈ bohr S (1 / (4 * Real.pi)), β ^ 4 * (N : Real) ^ 3 / 4 ≤ (repTuples B d).card := by
  intro β S
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hβ : 0 < β := div_pos (by exact_mod_cast hB.card_pos) hNR
  have hcard : (B.card : Real) = β * N := (div_mul_cancel₀ _ hNR.ne').symm
  obtain ⟨hS, hcorr⟩ := robust_self_correlation B hβ hcard
  have hcount : ∀ d ∈ bohr S (1 / (4 * Real.pi)),
      β ^ 4 * (N : Real) ^ 3 / 4 ≤ (repTuples B d).card := by
    intro d hd
    have h := hcorr d hd
    rw [mixed_self_correlation_eq_card, Complex.norm_natCast] at h
    exact h.trans (by exact_mod_cast fourDifferenceTriples_card_le_reps B d)
  refine ⟨hS, ?_, hcount⟩
  apply repMap_freimanLinear hf
  intro d hd
  have h := hcount d hd
  have hpos : (0 : Real) < (repTuples B d).card :=
    lt_of_lt_of_le (div_pos (mul_pos (pow_pos hβ 4) (pow_pos hNR 3)) (by norm_num)) h
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (by exact_mod_cast hpos)
  simp only [repTuples, Finset.mem_filter, Finset.mem_univ, true_and] at hq
  exact ⟨q, hq.1, hq.2⟩

/-- The witnesses of a column: four-tuples of `B` landing in the Bohr set. -/
def columnWitnesses {N : Nat} [NeZero N] (B S : Finset (ZMod N)) : Finset (Fin 4 → ZMod N) :=
  Finset.univ.filter fun q => (∀ i, q i ∈ B) ∧ fourSum q ∈ bohr S (1 / (4 * Real.pi))

/-- **A dense witness set.** -/
theorem column_witness_card_ge {N : Nat} [NeZero N] (B S : Finset (ZMod N)) {κ : Real}
    (hκ : ∀ d ∈ bohr S (1 / (4 * Real.pi)), κ ≤ (repTuples B d).card) (hκ0 : 0 ≤ κ) :
    κ * N ≤ (13 : Real) ^ S.card * (columnWitnesses B S).card := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  -- the witnesses are the disjoint union of the representing tuples
  have hunion : (columnWitnesses B S).card =
      ∑ d ∈ bohr S (1 / (4 * Real.pi)), (repTuples B d).card := by
    unfold columnWitnesses repTuples
    rw [Finset.card_eq_sum_card_fiberwise (f := fourSum) (t := bohr S (1 / (4 * Real.pi)))
      (fun q hq => (Finset.mem_filter.mp hq).2.2)]
    apply Finset.sum_congr rfl
    intro d hd
    congr 1
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hd⟩, h3⟩
  have hsum : κ * (bohr S (1 / (4 * Real.pi))).card ≤ (columnWitnesses B S).card := by
    rw [hunion]; push_cast
    calc κ * ((bohr S (1 / (4 * Real.pi))).card : Real) =
          ∑ _d ∈ bohr S (1 / (4 * Real.pi)), κ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum hκ
  have hlow : (N : Real) ≤ (13 : Real) ^ S.card * (bohr S (1 / (4 * Real.pi))).card := by
    have h := bohr_card_lower S (ρ := 1 / (4 * Real.pi)) 13 (by
      have hpi := Real.pi_lt_d2
      rw [show (1 : Real) / (4 * Real.pi) * ((13 : Nat) : Real) = 13 / (4 * Real.pi) by
        push_cast; ring, le_div_iff₀ (by positivity)]
      linarith)
    exact_mod_cast h
  calc κ * N ≤ κ * ((13 : Real) ^ S.card * (bohr S (1 / (4 * Real.pi))).card) :=
        mul_le_mul_of_nonneg_left hlow hκ0
    _ = (13 : Real) ^ S.card * (κ * (bohr S (1 / (4 * Real.pi))).card) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

end LeanProofs.GowersSzemeredi
