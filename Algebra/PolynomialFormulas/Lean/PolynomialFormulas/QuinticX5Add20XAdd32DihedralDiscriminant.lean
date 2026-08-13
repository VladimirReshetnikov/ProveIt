import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic
import PolynomialFormulas.QuinticScalarGaloisBridge
import PolynomialFormulas.QuinticX5Add20XAdd32DihedralDiscriminantAlgebra

/-!
# The square-discriminant parity bridge for rational quintics

This module isolates the generic algebra needed by the concrete polynomial
`X^5 + 20 X + 32`.  The square root of the discriminant is represented by
the determinant of the Vandermonde matrix.  The only degree-five polynomial
identity below is proved in five small derivative-evaluation stages; this
avoids expanding the full derivative product in one enormous normalization.
-/

open scoped BigOperators Polynomial
open Polynomial Equiv

namespace LeanProofs.PolynomialFormulas.QuinticX5Add20XAdd32Dihedral

open LazardQuintic

set_option autoImplicit false

/-- For the ordered roots used by the quintic Galois bridge, the square of
the Vandermonde determinant is the scalar extension of Mathlib's polynomial
discriminant. -/
theorem rootTuple_rootDetDelta_sq_eq_discr
    (p : ℚ[X]) (hp : Irreducible p) (hmonic : p.Monic)
    (hdeg : p.natDegree = 5) :
    rootDetDelta (QuinticScalarGaloisBridge.rootTuple p hp hdeg) ^ 2 =
      algebraMap ℚ p.SplittingField p.discr := by
  classical
  let L := p.SplittingField
  let r : Fin 5 → L := QuinticScalarGaloisBridge.rootTuple p hp hdeg
  let P : L[X] := p.map (algebraMap ℚ L)
  have hPmonic : P.Monic := hmonic.map (algebraMap ℚ L)
  have hPdeg : P.natDegree = 5 := by
    simpa only [P, hmonic.natDegree_map] using hdeg
  have hPsplit : P.Splits := SplittingField.splits p
  have hfactor : P = ∏ i : Fin 5, (X - C (r i)) :=
    QuinticScalarGaloisBridge.mapped_eq_prod_rootTuple p hp hmonic hdeg
  have hroots : P.roots = Finset.univ.val.map r := by
    rw [hfactor, Finset.prod]
    calc
      (Finset.univ.val.map (fun i => X - C (r i))).prod.roots =
          ((Finset.univ.val.map r).map (fun a => X - C a)).prod.roots := by
        rw [Multiset.map_map]
        rfl
      _ = Finset.univ.val.map r :=
        roots_multiset_prod_X_sub_C (Finset.univ.val.map r)
  have hderivDegree : P.derivative.natDegree ≤ 4 := by
    calc
      P.derivative.natDegree ≤ P.natDegree - 1 := natDegree_derivative_le P
      _ = 4 := by rw [hPdeg]
  have hresProd0 :=
    Polynomial.resultant_eq_prod_eval P P.derivative 4 hderivDegree hPsplit
  have hresProd :
      Polynomial.resultant P P.derivative 5 4 =
        ∏ i : Fin 5, eval (r i) P.derivative := by
    simpa only [hPdeg, hPmonic.leadingCoeff, one_pow, one_mul, hroots,
      Multiset.map_map, Finset.prod, Function.comp_apply] using hresProd0
  have hpDegreePos : 0 < p.degree := by
    rw [← natDegree_pos_iff_degree_pos, hdeg]
    norm_num
  have hresBase0 := Polynomial.resultant_deriv (f := p) hpDegreePos
  have hresBase :
      Polynomial.resultant p p.derivative 5 4 = p.discr := by
    rw [hdeg, hmonic.leadingCoeff] at hresBase0
    norm_num at hresBase0
    exact hresBase0
  have hresDisc :
      Polynomial.resultant P P.derivative 5 4 = algebraMap ℚ L p.discr := by
    change
      Polynomial.resultant (p.map (algebraMap ℚ L))
          (p.map (algebraMap ℚ L)).derivative 5 4 =
        algebraMap ℚ L p.discr
    rw [derivative_map, Polynomial.resultant_map_map, hresBase]
  calc
    rootDetDelta r ^ 2 =
        ∏ i : Fin 5,
          eval (r i) ((∏ j : Fin 5, (X - C (r j))).derivative) :=
      (prod_eval_derivative_prod_X_sub_C_eq_rootDetDelta_sq r).symm
    _ = ∏ i : Fin 5, eval (r i) P.derivative := by rw [hfactor]
    _ = Polynomial.resultant P P.derivative 5 4 := hresProd.symm
    _ = algebraMap ℚ L p.discr := hresDisc

/-- The classical square-discriminant criterion, specialized to the faithful
five-root permutation representation used in this repository. -/
theorem rootPermutationGroup_le_alternating_of_discr_eq_sq
    (p : ℚ[X]) (hp : Irreducible p) (hmonic : p.Monic)
    (hdeg : p.natDegree = 5) (q : ℚ) (hdiscr : p.discr = q ^ 2) :
    QuinticScalarGaloisBridge.rootPermutationGroup p hp hdeg ≤
      Classification.standardA5 := by
  set_option maxRecDepth 100000 in
  classical
  let r : Fin 5 → p.SplittingField :=
    QuinticScalarGaloisBridge.rootTuple p hp hdeg
  let delta : p.SplittingField := rootDetDelta r
  have hdeltaSq :
      delta ^ 2 = (algebraMap ℚ p.SplittingField q) ^ 2 := by
    change rootDetDelta r ^ 2 = (algebraMap ℚ p.SplittingField q) ^ 2
    rw [rootTuple_rootDetDelta_sq_eq_discr p hp hmonic hdeg,
      hdiscr, map_pow]
  have hfactor :
      (delta - algebraMap ℚ p.SplittingField q) *
          (delta + algebraMap ℚ p.SplittingField q) = 0 := by
    calc
      (delta - algebraMap ℚ p.SplittingField q) *
          (delta + algebraMap ℚ p.SplittingField q) =
          delta ^ 2 - (algebraMap ℚ p.SplittingField q) ^ 2 := by ring
      _ = 0 := by rw [hdeltaSq]; ring
  have hdeltaRational :
      delta = algebraMap ℚ p.SplittingField q ∨
        delta = -algebraMap ℚ p.SplittingField q := by
    rcases mul_eq_zero.mp hfactor with hminus | hplus
    · exact Or.inl (sub_eq_zero.mp hminus)
    · right
      calc
        delta = delta + algebraMap ℚ p.SplittingField q -
            algebraMap ℚ p.SplittingField q := by ring
        _ = -algebraMap ℚ p.SplittingField q := by rw [hplus]; ring
  have hdeltaNe : delta ≠ 0 := by
    change (Matrix.vandermonde r).det ≠ 0
    exact Matrix.det_vandermonde_ne_zero_iff.mpr
      (QuinticScalarGaloisBridge.rootTuple_injective p hp hdeg)
  rintro g ⟨σ, rfl⟩
  rw [Equiv.Perm.mem_alternatingGroup]
  have hfixed : σ delta = delta := by
    rcases hdeltaRational with hdelta | hdelta
    · rw [hdelta]
      simp
    · rw [hdelta]
      simp
  have hmapDelta :
      σ delta =
        rootDetDelta
          (permuteRootTuple r
            (QuinticScalarGaloisBridge.rootPermutationHom p hp hdeg σ)) := by
    calc
      σ delta = rootDetDelta (fun i => σ (r i)) := by
        change σ (rootDetDelta r) = rootDetDelta (fun i => σ (r i))
        exact map_rootDetDelta σ.toRingHom r
      _ = rootDetDelta
          (permuteRootTuple r
            (QuinticScalarGaloisBridge.rootPermutationHom p hp hdeg σ)) := by
        congr 1
        funext i
        exact QuinticScalarGaloisBridge.gal_maps_rootTuple p hp hdeg σ i
  have hsignMul :
      ((QuinticScalarGaloisBridge.rootPermutationHom p hp hdeg σ).sign :
          p.SplittingField) * delta = delta := by
    calc
      ((QuinticScalarGaloisBridge.rootPermutationHom p hp hdeg σ).sign :
          p.SplittingField) * delta =
          rootDetDelta
            (permuteRootTuple r
              (QuinticScalarGaloisBridge.rootPermutationHom p hp hdeg σ)) :=
        (rootDetDelta_permute r
          (QuinticScalarGaloisBridge.rootPermutationHom p hp hdeg σ)).symm
      _ = σ delta := hmapDelta.symm
      _ = delta := hfixed
  rcases Int.units_eq_one_or
      (QuinticScalarGaloisBridge.rootPermutationHom p hp hdeg σ).sign with
      hsign | hsign
  · exact hsign
  · exfalso
    have hnegMul : (-1 : p.SplittingField) * delta = delta := by
      simpa [hsign] using hsignMul
    have hneg : -delta = delta := by
      simpa only [neg_one_mul] using hnegMul
    have htwo : (2 : p.SplittingField) * delta = 0 := by
      calc
        (2 : p.SplittingField) * delta = delta - (-delta) := by ring
        _ = 0 := by rw [hneg, sub_self]
    exact hdeltaNe ((mul_eq_zero.mp htwo).resolve_left (by norm_num))

end LeanProofs.PolynomialFormulas.QuinticX5Add20XAdd32Dihedral
