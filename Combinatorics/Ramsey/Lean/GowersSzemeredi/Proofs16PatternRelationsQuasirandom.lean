import GowersSzemeredi.Proofs16PatternBohrQuasirandom
import GowersSzemeredi.Proofs16BohrDensityAtRadii

/-! The algebraic-to-graph step: typical splitting of bounded relations,
regular annuli, and an explicit Fourier cutoff imply pattern quasirandomness.
The existence of such splitting domains remains a separate theorem. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem pattern_boxSum_of_relation_splitting {N m c R : Nat} [NeZero N]
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
    ((mixedBohr gamma (fun i => a i + 2 * c)).card : Real) ≤ (bohr F eta).card + epsilon * N →
    (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ Fintype.card ↥F - 1 ≤ epsilon →
    (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ Fintype.card (↥F ⊕ ↥I) - 1 ≤ epsilon →
    (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ Fintype.card (↥F ⊕ (↥I ⊕ ↥I)) - 1 ≤ epsilon →
    ∀ Ybad : Finset ↥C, (Ybad.card : Real) ≤ chi * C.card →
    (∀ t ∉ Ybad, ∀ (nu : ↥F → centeredBall N R) (mu : ↥I → centeredBall N R),
      (∑ i, (nu i : ZMod N) * gamma i) + (∑ j, (mu j : ZMod N) * L t j) = 0 ↔
        (∑ i, (nu i : ZMod N) * gamma i = 0 ∧ mu ∈ Lambda)) →
    (∀ t ∉ Ybad,
      ((mixedBohr (Sum.elim gamma (L t)) (fun q => Sum.elim a b q + 2 * c)).card : Real) ≤
        (patternDegreeBohr F psi J eta t).card + epsilon * N) →
    ∀ Pbad : Finset (↥C × ↥C), (Pbad.card : Real) ≤ chi * (C.card : Real)^2 →
    (∀ t u, (t, u) ∉ Pbad →
      ∀ (nu : ↥F → centeredBall N R) (mu : (↥I ⊕ ↥I) → centeredBall N R),
      (∑ i, (nu i : ZMod N) * gamma i) + (∑ j, (mu j : ZMod N) * Sum.elim (L t) (L u) j) = 0 ↔
        (∑ i, (nu i : ZMod N) * gamma i = 0 ∧
          (fun j => mu (Sum.inl j)) ∈ Lambda ∧ (fun j => mu (Sum.inr j)) ∈ Lambda)) →
    (∀ t u, (t, u) ∉ Pbad →
      ((mixedBohr (Sum.elim gamma (Sum.elim (L t) (L u)))
        (fun q => Sum.elim a (Sum.elim b b) q + 2 * c)).card : Real) ≤
          (patternCodegreeBohr F psi J eta t u).card + epsilon * N) →
    (4 + 2 * zeta) * epsilon * N + zeta * (bohr F eta).card ≤ e * (bohr F eta).card →
    (4 + 2 * (zeta * (2 + zeta))) * epsilon * N +
      (zeta * (2 + zeta)) * (bohr F eta).card ≤ e * (bohr F eta).card →
    boxSum (fun (d : ↥(bohr F eta)) (t : ↥C) =>
      edgeIndicator (patternEdge psi J (eta / 4)) d t - delta) ≤
      3 * (e + chi) * ((bohr F eta).card : Real)^2 * (C.card : Real)^2 := by
  dsimp only
  intro Lambda ha hb hc hweight hband htrunc htruncD htruncP
    Ybad hYbad hsplitD hbandD Pbad hPbad hsplitP hbandP hbudgetD hbudgetP
  let gamma := patternFixedTuple F
  let a : ↥F → Nat := fun _ => ⌊eta * N⌋₊
  let b : ↥(J 0 ∪ J 2) → Nat := fun _ => ⌊eta / 4 * N⌋₊
  have hbase : mixedBohr gamma a = bohr F eta := by
    rw [mixedBohr_floor_tuple _ heta, patternFixedTuple_image]
  refine pattern_boxSum_le_of_typical_bohr F C psi J heta hd0 hd1 he Ybad hYbad ?_ Pbad hPbad ?_
  · intro t ht
    have h := bohr_card_factor_at_radii gamma (patternVaryingTuple psi J t) a b ha hb hc
      Lambda (hsplitD t ht) heps hd0 hd1 hweight (by rwa [hbase]) (hbandD t ht) htrunc htruncD
    change |(patternDegreeBohr F psi J eta t).card - delta * ((mixedBohr gamma a).card : Real)| ≤
      (4 + 2 * zeta) * epsilon * N + zeta * (mixedBohr gamma a).card at h
    rw [hbase] at h
    exact h.trans hbudgetD
  · intro t u htu
    have h := bohr_pair_card_factor_at_radii gamma (patternVaryingTuple psi J t)
      (patternVaryingTuple psi J u) a b ha hb hc Lambda (hsplitP t u htu) heps hd0 hd1 hweight
      (by rwa [hbase]) (hbandP t u htu) htrunc htruncP
    change |(patternCodegreeBohr F psi J eta t u).card - delta^2 * ((mixedBohr gamma a).card : Real)| ≤
      (4 + 2 * (zeta * (2 + zeta))) * epsilon * N +
        (zeta * (2 + zeta)) * (mixedBohr gamma a).card at h
    rw [hbase] at h
    exact h.trans hbudgetP

end LeanProofs.GowersSzemeredi
