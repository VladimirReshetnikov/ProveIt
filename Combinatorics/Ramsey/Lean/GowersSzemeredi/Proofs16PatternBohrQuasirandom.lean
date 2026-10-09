import GowersSzemeredi.Proofs16PatternBohrDegrees
import GowersSzemeredi.Proofs16OneSidedQuasirandom
import GowersSzemeredi.Proofs16RobustRowFilling

/-! Typical mixed-Bohr sizes imply the actual box-sum estimate needed by
row filling. Exceptional vertices and pairs are retained explicitly. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Turn typical degree and codegree Bohr sizes into graph quasirandomness. -/
theorem pattern_boxSum_le_of_typical_bohr {N m : Nat} [NeZero N]
    (F C : Finset (ZMod N)) (psi : Fin m → ZMod N → ZMod N)
    (J : Fin 4 → Finset (Fin m)) {eta delta e chi : Real}
    (heta : 0 ≤ eta) (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) (he : 0 ≤ e)
    (Ybad : Finset ↥C) (hYbad : (Ybad.card : Real) ≤ chi * C.card)
    (hdeg : ∀ t ∉ Ybad,
      |(patternDegreeBohr F psi J eta t).card - delta * ((bohr F eta).card : Real)| ≤
        e * (bohr F eta).card)
    (Pbad : Finset (↥C × ↥C)) (hPbad : (Pbad.card : Real) ≤ chi * (C.card : Real)^2)
    (hcodeg : ∀ t u, (t, u) ∉ Pbad →
      |(patternCodegreeBohr F psi J eta t u).card - delta^2 * ((bohr F eta).card : Real)| ≤
        e * (bohr F eta).card) :
    boxSum (fun (d : ↥(bohr F eta)) (t : ↥C) =>
      edgeIndicator (patternEdge psi J (eta / 4)) d t - delta) ≤
      3 * (e + chi) * ((bohr F eta).card : Real)^2 * (C.card : Real)^2 := by
  have h := boxSum_le_of_typical_codegrees
    (G := fun (d : ↥(bohr F eta)) (t : ↥C) => edgeIndicator (patternEdge psi J (eta / 4)) d t)
    (fun _ _ => by unfold edgeIndicator; split_ifs <;> norm_num)
    (fun _ _ => by unfold edgeIndicator; split_ifs <;> norm_num)
    hd0 hd1 he Ybad (by simpa only [Fintype.card_coe] using hYbad)
    (fun t ht => by
      simpa only [pattern_degree_eq_mixedBohr F C psi J heta, Fintype.card_coe] using hdeg t ht)
    Pbad (by simpa only [Fintype.card_coe] using hPbad)
    (fun t u htu => by
      simpa only [pattern_codegree_eq_mixedBohr F C psi J heta, Fintype.card_coe] using hcodeg t u htu)
  simpa only [Fintype.card_coe] using h

/-- The fourth-root-free interface matches the error parameter used by
common-neighborhood counting and row filling. -/
theorem pattern_boxSum_le_of_typical_bohr_budget {N m : Nat} [NeZero N]
    (F C : Finset (ZMod N)) (psi : Fin m → ZMod N → ZMod N)
    (J : Fin 4 → Finset (Fin m)) {eta delta e chi epsilon : Real}
    (heta : 0 ≤ eta) (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) (he : 0 ≤ e)
    (Ybad : Finset ↥C) (hYbad : (Ybad.card : Real) ≤ chi * C.card)
    (hdeg : ∀ t ∉ Ybad,
      |(patternDegreeBohr F psi J eta t).card - delta * ((bohr F eta).card : Real)| ≤
        e * (bohr F eta).card)
    (Pbad : Finset (↥C × ↥C)) (hPbad : (Pbad.card : Real) ≤ chi * (C.card : Real)^2)
    (hcodeg : ∀ t u, (t, u) ∉ Pbad →
      |(patternCodegreeBohr F psi J eta t u).card - delta^2 * ((bohr F eta).card : Real)| ≤
        e * (bohr F eta).card)
    (hbudget : 3 * (e + chi) ≤ epsilon^4) :
    boxSum (fun (d : ↥(bohr F eta)) (t : ↥C) =>
      edgeIndicator (patternEdge psi J (eta / 4)) d t - delta) ≤
      epsilon^4 * ((bohr F eta).card : Real)^2 * (C.card : Real)^2 := by
  exact (pattern_boxSum_le_of_typical_bohr F C psi J heta hd0 hd1 he
    Ybad hYbad hdeg Pbad hPbad hcodeg).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbudget (sq_nonneg _)) (sq_nonneg _))

end LeanProofs.GowersSzemeredi
