import GowersSzemeredi.Proofs16BohrSizeFactorization
import GowersSzemeredi.Proofs16PatternMissingRows

/-! Exact degree and codegree formulas for the pattern graph, with separate
radii on the fixed and varying frequency blocks. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem mixedBohr_sumElim_radii {N : Nat} [NeZero N] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (gamma : ι → ZMod N) (ell : κ → ZMod N) (a : ι → Nat) (b : κ → Nat) :
    mixedBohr (Sum.elim gamma ell) (Sum.elim a b) = mixedBohr gamma a ∩ mixedBohr ell b := by
  ext x
  simp only [mem_mixedBohr, Finset.mem_inter, Sum.forall, Sum.elim_inl, Sum.elim_inr]

/-- Rounding a real radius down is exact for the integer centered norm. -/
theorem mixedBohr_floor_tuple {N : Nat} [NeZero N] {ι : Type*} [Fintype ι]
    (gamma : ι → ZMod N) {rho : Real} (hrho : 0 ≤ rho) :
    mixedBohr gamma (fun _ => ⌊rho * N⌋₊) = bohr (Finset.univ.image gamma) rho := by
  rw [mixedBohr_const, bohr_floor_radius _ hrho]

/-- Counting inside a subtype agrees with intersection in the ambient set. -/
theorem sum_subtype_indicator_inter {N : Nat} [NeZero N] (B D : Finset (ZMod N)) :
    (∑ x : ↥B, if (x : ZMod N) ∈ D then (1 : Real) else 0) = ((B ∩ D).card : Real) := by
  have hcard : (Finset.univ.filter fun x : ↥B => (x : ZMod N) ∈ D).card = (B ∩ D).card := by
    apply Finset.card_bij (fun (x : ↥B) _ => (x : ZMod N))
    · intro x hx
      exact Finset.mem_inter.mpr ⟨x.property, (Finset.mem_filter.mp hx).2⟩
    · intro x hx y hy h
      exact Subtype.ext h
    · intro x hx
      refine ⟨⟨x, (Finset.mem_inter.mp hx).1⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_inter.mp hx).2⟩
  simpa using congrArg (fun n : Nat => (n : Real)) hcard

def patternFixedTuple {N : Nat} (F : Finset (ZMod N)) : ↥F → ZMod N := fun r => r.val

def patternVaryingTuple {N m : Nat} (psi : Fin m → ZMod N → ZMod N)
    (J : Fin 4 → Finset (Fin m)) (t : ZMod N) : ↥(J 0 ∪ J 2) → ZMod N :=
  fun i => psi i t

theorem patternFixedTuple_image {N : Nat} (F : Finset (ZMod N)) :
    Finset.univ.image (patternFixedTuple F) = F := by
  ext x
  simp [patternFixedTuple]

theorem patternVaryingTuple_image {N m : Nat}
    (psi : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m)) (t : ZMod N) :
    Finset.univ.image (patternVaryingTuple psi J t) = varyingPatternFrequencies psi J t := by
  ext x
  simp [patternVaryingTuple, varyingPatternFrequencies]

/-- The degree neighborhood as a single mixed-radius Bohr set. -/
def patternDegreeBohr {N m : Nat} [NeZero N] (F : Finset (ZMod N))
    (psi : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m)) (eta : Real) (t : ZMod N) :=
  mixedBohr (Sum.elim (patternFixedTuple F) (patternVaryingTuple psi J t))
    (Sum.elim (fun _ => ⌊eta * N⌋₊) (fun _ => ⌊eta / 4 * N⌋₊))

/-- The common neighborhood has two varying blocks, keeping repeated frequencies. -/
def patternCodegreeBohr {N m : Nat} [NeZero N] (F : Finset (ZMod N))
    (psi : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m))
    (eta : Real) (t u : ZMod N) :=
  mixedBohr (Sum.elim (patternFixedTuple F)
    (Sum.elim (patternVaryingTuple psi J t) (patternVaryingTuple psi J u)))
    (Sum.elim (fun _ => ⌊eta * N⌋₊)
      (Sum.elim (fun _ => ⌊eta / 4 * N⌋₊) (fun _ => ⌊eta / 4 * N⌋₊)))

theorem patternDegreeBohr_eq_inter {N m : Nat} [NeZero N] (F : Finset (ZMod N))
    (psi : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m))
    {eta : Real} (heta : 0 ≤ eta) (t : ZMod N) :
    patternDegreeBohr F psi J eta t = bohr F eta ∩ bohr (varyingPatternFrequencies psi J t) (eta / 4) := by
  unfold patternDegreeBohr
  rw [mixedBohr_sumElim_radii, mixedBohr_floor_tuple _ heta,
    mixedBohr_floor_tuple _ (by positivity), patternFixedTuple_image, patternVaryingTuple_image]

theorem patternCodegreeBohr_eq_inter {N m : Nat} [NeZero N] (F : Finset (ZMod N))
    (psi : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m))
    {eta : Real} (heta : 0 ≤ eta) (t u : ZMod N) :
    patternCodegreeBohr F psi J eta t u = bohr F eta ∩
      (bohr (varyingPatternFrequencies psi J t) (eta / 4) ∩
        bohr (varyingPatternFrequencies psi J u) (eta / 4)) := by
  unfold patternCodegreeBohr
  rw [mixedBohr_sumElim_radii, mixedBohr_sumElim_radii, mixedBohr_floor_tuple _ heta,
    mixedBohr_floor_tuple _ (by positivity), mixedBohr_floor_tuple _ (by positivity),
    patternFixedTuple_image, patternVaryingTuple_image, patternVaryingTuple_image]

/-- The pattern graph degree equals the mixed Bohr cardinality exactly. -/
theorem pattern_degree_eq_mixedBohr {N m : Nat} [NeZero N] (F C : Finset (ZMod N))
    (psi : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m))
    {eta : Real} (heta : 0 ≤ eta) (t : ↥C) :
    (∑ d : ↥(bohr F eta), edgeIndicator (patternEdge psi J (eta / 4)) d t) =
      ((patternDegreeBohr F psi J eta t).card : Real) := by
  rw [patternDegreeBohr_eq_inter F psi J heta t]
  rw [← sum_subtype_indicator_inter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases ht : (d : ZMod N) ∈ bohr (varyingPatternFrequencies psi J t) (eta / 4) <;>
    simp [edgeIndicator, patternEdge, ht]

/-- The pattern graph codegree equals the mixed Bohr cardinality exactly. -/
theorem pattern_codegree_eq_mixedBohr {N m : Nat} [NeZero N] (F C : Finset (ZMod N))
    (psi : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m))
    {eta : Real} (heta : 0 ≤ eta) (t u : ↥C) :
    (∑ d : ↥(bohr F eta), edgeIndicator (patternEdge psi J (eta / 4)) d t *
      edgeIndicator (patternEdge psi J (eta / 4)) d u) =
      ((patternCodegreeBohr F psi J eta t u).card : Real) := by
  rw [patternCodegreeBohr_eq_inter F psi J heta t u]
  rw [← sum_subtype_indicator_inter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases ht : (d : ZMod N) ∈ bohr (varyingPatternFrequencies psi J t) (eta / 4) <;>
    by_cases hu : (d : ZMod N) ∈ bohr (varyingPatternFrequencies psi J u) (eta / 4) <;>
    simp [edgeIndicator, patternEdge, ht, hu]

end LeanProofs.GowersSzemeredi
