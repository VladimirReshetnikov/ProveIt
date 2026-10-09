import GowersSzemeredi.Proofs16PatternRelationsQuasirandom
import GowersSzemeredi.Proofs16PrimeBandSplit

/-! The pattern-graph relation bridge with its annulus hypotheses
discharged in prime `ℤ/N`.

`pattern_boxSum_of_relation_splitting` assumes three annulus bounds:
the fixed block, the typical degrees, and the typical codegrees, each at
the radii enlarged by `2c`. In prime `ℤ/N` all three follow from
`mixedBohr_band_le_budget`, applied at the centre `a + c` with half-width
`c`. The fixed block has `|F|` frequencies, a degree tuple `|F ⊕ I|` and a
codegree tuple `|F ⊕ (I ⊕ I)|`, so one budget
`|F ⊕ (I ⊕ I)|·(4c+2) ≤ εN` covers all three
(`pattern_boxSum_of_relation_splitting_prime`). The remaining hypotheses
are the relation-splitting identities, the approximate density of the
lattice weight, the truncation budgets, and the numerical conversion. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The band bound at the centre `r + c`, in the shifted form used by the
pattern bridge. -/
theorem mixedBohr_shift_band_le {N : Nat} [NeZero N] [Fact N.Prime] {μ : Type*} [Fintype μ]
    (g : μ → ZMod N) (r : μ → Nat) (c m : Nat) (hcard : Fintype.card μ ≤ m) {ε : Real}
    (hbudget : (m : Real) * (4 * c + 2) ≤ ε * N) :
    ((mixedBohr g (fun q => r q + 2 * c)).card : Real) ≤ (mixedBohr g r).card + ε * N := by
  have h := mixedBohr_band_le_budget g (fun q => r q + c) c m (fun q => by omega) hcard
  have h1 : (fun q => r q + c + c) = fun q => r q + 2 * c := by funext q; ring
  have h2 : (fun q => r q + c - c) = r := by funext q; omega
  rw [h1, h2] at h
  linarith

/-- **The pattern-graph bridge in prime `ℤ/N`.** No annulus hypothesis
remains. -/
theorem pattern_boxSum_of_relation_splitting_prime {N m c R : Nat} [NeZero N] [Fact N.Prime]
    (F C : Finset (ZMod N)) (psi : Fin m → ZMod N → ZMod N)
    (J : Fin 4 → Finset (Fin m)) {eta delta epsilon zeta e chi : Real}
    (heta : 0 ≤ eta) (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1)
    (heps : 0 ≤ epsilon) (he : 0 ≤ e) :
    let I := J 0 ∪ J 2
    let gamma := patternFixedTuple F
    let L := fun t : ↥C => patternVaryingTuple psi J t
    let a : ↥F → Nat := fun _ => ⌊eta * N⌋₊
    let b : ↥I → Nat := fun _ => ⌊eta / 4 * N⌋₊
    ∀ Lambda : Set (↥I → centeredBall N R),
    (∀ i, 2 * (a i + c) < N) → (∀ j, 2 * (b j + c) < N) → 2 * c < N →
    ‖latticeWeightMixed (fun j => b j + c) c R Lambda - (delta : Complex)‖ ≤ zeta →
    (Fintype.card (↥F ⊕ (↥I ⊕ ↥I)) : Real) * (4 * c + 2) ≤ epsilon * N →
    (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ Fintype.card ↥F - 1 ≤ epsilon →
    (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ Fintype.card (↥F ⊕ ↥I) - 1 ≤ epsilon →
    (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ Fintype.card (↥F ⊕ (↥I ⊕ ↥I)) - 1 ≤
      epsilon →
    ∀ Ybad : Finset ↥C, (Ybad.card : Real) ≤ chi * C.card →
    (∀ t ∉ Ybad, ∀ (nu : ↥F → centeredBall N R) (mu : ↥I → centeredBall N R),
      (∑ i, (nu i : ZMod N) * gamma i) + (∑ j, (mu j : ZMod N) * L t j) = 0 ↔
        (∑ i, (nu i : ZMod N) * gamma i = 0 ∧ mu ∈ Lambda)) →
    ∀ Pbad : Finset (↥C × ↥C), (Pbad.card : Real) ≤ chi * (C.card : Real)^2 →
    (∀ t u, (t, u) ∉ Pbad →
      ∀ (nu : ↥F → centeredBall N R) (mu : (↥I ⊕ ↥I) → centeredBall N R),
      (∑ i, (nu i : ZMod N) * gamma i) + (∑ j, (mu j : ZMod N) * Sum.elim (L t) (L u) j) = 0 ↔
        (∑ i, (nu i : ZMod N) * gamma i = 0 ∧
          (fun j => mu (Sum.inl j)) ∈ Lambda ∧ (fun j => mu (Sum.inr j)) ∈ Lambda)) →
    (4 + 2 * zeta) * epsilon * N + zeta * (bohr F eta).card ≤ e * (bohr F eta).card →
    (4 + 2 * (zeta * (2 + zeta))) * epsilon * N +
      (zeta * (2 + zeta)) * (bohr F eta).card ≤ e * (bohr F eta).card →
    boxSum (fun (d : ↥(bohr F eta)) (t : ↥C) =>
      edgeIndicator (patternEdge psi J (eta / 4)) d t - delta) ≤
      3 * (e + chi) * ((bohr F eta).card : Real)^2 * (C.card : Real)^2 := by
  intro I gamma L a b Lambda ha hb hc hW hbudget htr1 htr2 htr3 Ybad hYbad hsplit1 Pbad hPbad
    hsplit2 hbud1 hbud2
  have hcF : Fintype.card ↥F ≤ Fintype.card (↥F ⊕ (↥I ⊕ ↥I)) := by simp [Fintype.card_sum]
  have hcFI : Fintype.card (↥F ⊕ ↥I) ≤ Fintype.card (↥F ⊕ (↥I ⊕ ↥I)) := by
    simp [Fintype.card_sum]
  -- the fixed block
  have hann0 : ((mixedBohr gamma (fun i => a i + 2 * c)).card : Real) ≤
      (bohr F eta).card + epsilon * N := by
    have h := mixedBohr_shift_band_le gamma a c _ hcF hbudget
    have hfix : mixedBohr gamma a = bohr F eta := by
      have := mixedBohr_floor_tuple gamma heta
      rw [patternFixedTuple_image] at this
      exact this
    rw [hfix] at h
    exact h
  -- typical degrees
  have hann1 : ∀ t ∉ Ybad,
      ((mixedBohr (Sum.elim gamma (L t)) (fun q => Sum.elim a b q + 2 * c)).card : Real) ≤
        (patternDegreeBohr F psi J eta t).card + epsilon * N := by
    intro t _
    exact mixedBohr_shift_band_le (Sum.elim gamma (L t)) (Sum.elim a b) c _ hcFI hbudget
  -- typical codegrees
  have hann2 : ∀ t u, (t, u) ∉ Pbad →
      ((mixedBohr (Sum.elim gamma (Sum.elim (L t) (L u)))
        (fun q => Sum.elim a (Sum.elim b b) q + 2 * c)).card : Real) ≤
          (patternCodegreeBohr F psi J eta t u).card + epsilon * N := by
    intro t u _
    exact mixedBohr_shift_band_le (Sum.elim gamma (Sum.elim (L t) (L u)))
      (Sum.elim a (Sum.elim b b)) c _ le_rfl hbudget
  exact pattern_boxSum_of_relation_splitting F C psi J heta hd0 hd1 heps he Lambda ha hb hc hW
    hann0 htr1 htr2 htr3 Ybad hYbad hsplit1 hann1 Pbad hPbad hsplit2 hann2 hbud1 hbud2

end LeanProofs.GowersSzemeredi
