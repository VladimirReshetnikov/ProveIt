import DiophantineConsistency.DegreeSeparatedCoding
import Mathlib.Data.Fin.VecNotation

open DiophantineConsistency DiophantineConsistency.DegreeSeparatedCoding
open DiophantineConsistency.SelectiveQuadraticCoding DiophantineConsistency.SidonPositions

private def weights : Fin 3 → ℕ := ![1, 2, 3]
private def inputs : Fin 3 → ℤ := ![2, 3, 7]
private def pair01 : PairIndex 2 := ⟨(0, 1), by decide⟩
private def s1 : Fin 1 → Finset (Fin 3) := fun _ => {2}
private def s2 : Fin 1 → Finset (PairIndex 2) := fun _ => {pair01}

-- The quadratic label w0+w1 equals the linear label w2. Keeping the
-- channels separate still extracts twice (11+4*7+5*2*3)=138.
example :
    (product weights inputs (fun _ : Fin 1 => (11 : ℤ)) s1 (fun _ _ => 4)
      s2 (fun _ _ => 5) (fun _ => 5)).coeff 5 = 138 := by
  have h := coeff_product weights (by decide : Function.Injective weights)
    inputs (fun _ : Fin 1 => (11 : ℤ)) s1 (fun _ _ => 4) s2 (fun _ _ => 5)
    (fun _ => 5) (by intro i j _; exact Subsingleton.elim i j)
    (by intro k i hi; simp only [s1, Finset.mem_singleton] at hi; subst i; decide)
    (by intro k l hkl; exact False.elim (hkl (Subsingleton.elim k l)))
    (by intro k p hp; simp only [s2, Finset.mem_singleton] at hp; subst p; decide)
    (by intro k p hp; simp only [s2, Finset.mem_singleton] at hp; subst p; unfold Isolated; decide)
    (by intro k l hkl; exact False.elim (hkl (Subsingleton.elim k l))) 0
  rw [h]
  norm_num [value, linearValue, rowValue, s1, s2, inputs, pair01]
  decide

#print axioms coeff_mul_linearCombined
#print axioms coeff_constantCombined
#print axioms coeff_product
