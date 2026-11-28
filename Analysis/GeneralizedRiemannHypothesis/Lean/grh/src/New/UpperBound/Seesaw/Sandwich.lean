import Lib.Weil.DualPair.FiniteAction
import Lib.Weil.Periods.GradedLattice
import New.UpperBound.Seesaw.StandardLines

/-!
# Bounds for the lattices of points on graded spaces

Let `Λ'` be the lattice `V.lattice x` of a finite point `x` of a graded space and `Λ` the lattice
of the point `1`. The file proves lattice steps of the induction for the bounds
`Q̄ ^ k Λ⁻ ⊆ Λ'⁻ ⊆ Q ^ (-k) Λ⁻`, where `q` generates `Q`.

* `New.Grading.smul_latticeMinus_le_of_map_latticePlus`: if `sh Λ⁺` is `a` times the `Λ⁻` of the
  next space, then the upper bound on one space and an inclusion `(q̄ / a) sh Λ'⁺ ⊆ Λ''⁻`, with
  `Λ''` the lattice of a point on the next space, give the lower bound on the next space.
* `New.Grading.SpansLattice.hasLatticeBounds_or_latticeSplitsAt`: for a grading over `X ⊕ Unit`,
  duality turns the lower bound into both bounds, unless `s` is odd and `Λ'` splits along `X ⊕ Unit`
  at a place above `N`.
* `New.Grading.LatticeSplitsAt.conj_scalarFin_mem`: if `Λ'` splits along `X` at a place `w ≠ w̄`,
  then the integral scalings of `X` supported at `w` and `w̄` preserve `Λ'`.

Notions from other files:

* `Gf E ι`: the finite adelic unitary group in the variables `ι`, whose elements are the finite
  points. The lattice `V.lattice x` is spanned over `Ô E` by the columns of `V.xFin * x`, where
  `V.xFin` is the finite frame of the hermitian space `V`.
* `New.Grading V N X s`: a splitting of the basis `ι` of `V` into an orthonormal part `X` of grade
  `0` and a string of `s` vectors, where vector `i` pairs only with vector `s - 1 - i`, to `1`,
  except that the middle vector (for odd `s`) pairs with itself to `-N`.
* `Y.latticePlus x`, `Y.latticeMinus x`: the projection `Λ'⁺` of the lattice of `x` to `X^⊥` and
  its intersection `Λ'⁻` with `X^⊥`, the span of the string.
* `Y.stringMapFin Y'`: the shift `sh` from the vectors of one graded space to those of the next.

## Relation to the literature

See `New.UpperBound.Seesaw.SeesawIdentity` for related work.
-/

open Matrix Pointwise Valued

noncomputable section

namespace New

open Seesaw Gf Space

variable {E X X' ι ι' : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] [Fintype X] [DecidableEq X] [DecidableEq X']
  {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {s : ℕ} {N : E} {V : Space E ι ε} {V' : Space E ι' ε'}

namespace Grading

section Splitting

/-- Let `Y` split the basis of `V` into `X` and a string spanning `X^⊥`, and let `Λ' = V.lattice x`
be the lattice of the point `x` of the finite adelic unitary group. Then `Λ'` splits along `X` at
the place `w` if there the projection `Λ'⁺` of `Λ'` to `X^⊥` lies in the intersection `Λ'⁻` of `Λ'`
with `X^⊥`, so the two are equal. The idempotent `idem {w}` cuts out the component at `w`. -/
def LatticeSplitsAt (Y : Grading V N X s) (w : FinPlace E) (x : Gf E ι) : Prop :=
  (idem {w} : 𝔸f E) • Y.latticePlus x ≤ Y.latticeMinus x

/-- If the lattice of `x` splits along `X` at the place `w`, then it splits at the complex conjugate
place `star w` too. -/
lemma LatticeSplitsAt.conj {Y : Grading V N X s} {w : FinPlace E} {x : Gf E ι}
    (h_split : Y.LatticeSplitsAt w x) : Y.LatticeSplitsAt (star w) x := by
  have h_idem : (idem {star w} : 𝔸f E) = star (idem {w}) := by
    rw [star_idem]
    congr with u
    exact eq_star_iff_eq_star.trans eq_comm
  simpa only [LatticeSplitsAt, h_idem] using star_smul_latticePlus_le_latticeMinus h_split

/-- In rational coordinates, the finite point `Y.inclXFin (scalarFin X z)` of `U(V)`, which scales
`X` by `z`, sends a vector `y` to `y + (z - 1) (y - p y)`, where `p = Y.stringProj` is the
projection to `X^⊥`. -/
lemma inclXFin_scalarFin_mulVec {Y : Grading V N X s} (z : unitary (𝔸f E)) (y : ι → 𝔸f E) :
    V.ratCoordMatrixFin (Y.inclXFin (scalarFin X z)) *ᵥ y =
      y + (z.val - 1) • (y - Y.stringProj y) := by
  ext1 i
  obtain ⟨a | b, rfl⟩ := Y.indexEquiv.surjective i <;>
    simp [ratCoordMatrixFin_inclXFin, submatrix_mulVec_equiv, fromBlocks_mulVec,
      stringProj_apply_inl, stringProj_apply_inr, sub_mul, scalarFin]

omit [Fintype X] in
/-- Let the lattice of `x` split along `X` at the place `w`: there its projection to `X^⊥` lies in
the lattice. For every vector `y` of the lattice, the component at `w` (cut out by `idem {w}`) of
the part `y - Y.stringProj y` of `y` in `X` lies in the lattice. -/
lemma LatticeSplitsAt.idem_smul_sub_stringProj_mem {Y : Grading V N X s} {w : FinPlace E}
    {x : Gf E ι} (h_split : Y.LatticeSplitsAt w x) {y : ι → 𝔸f E} (hy : y ∈ V.lattice x) :
    (idem {w} : 𝔸f E) • (y - Y.stringProj y) ∈ V.lattice x := by
  have h_minus : (idem {w} : 𝔸f E) • Y.stringProj y ∈ Y.latticeMinus x :=
    smul_le_iff_forall.1 h_split _ (Submodule.mem_map_of_mem hy)
  rw [smul_sub]
  exact sub_mem ((V.lattice x).smul_mem ⟨_, idem_mem_Ô _⟩ hy) (mem_latticeMinus.1 h_minus).1

/-- At a place `u` where the unitary adele `z` is `1`, the finite point that scales `X` by `z`,
conjugated by the finite frame `V.xFin` into rational coordinates, has the identity matrix. -/
lemma inclXFin_scalarFin_map_evalAt {Y : Grading V N X s} {z : unitary (𝔸f E)} {u : FinPlace E}
    (hz : z.val u = 1) :
    (V.xFin * Y.inclXFin (scalarFin X z) * V.xFin⁻¹).map (evalAt u) = 1 := by
  refine Units.ext ?_
  change (V.ratCoordMatrixFin (Y.inclXFin (scalarFin X z))).map (evalAt u) = 1
  rw [ratCoordMatrixFin_inclXFin]
  ext i l
  obtain ⟨i | i, rfl⟩ := Y.indexEquiv.surjective i <;>
    obtain ⟨l | l, rfl⟩ := Y.indexEquiv.surjective l <;>
    simp [scalarFin, one_apply, diagonal_apply, apply_ite, hz]

/-- Let `x` be a point of the finite adelic unitary group `Gf E ι` whose lattice, spanned by the
columns of `V.xFin * x`, splits along `X` at a place `w ≠ w̄`: there its projection to `X^⊥` lies in
the lattice. Let `z` be an integral unitary adele that is `1` off `w` and `w̄`. Then the conjugate
by `x` of the scaling `Y.inclXFin (scalarFin X z)` of `X` by `z` lies in `maxCompactAt ι w`: it is
integral and trivial off `w` and `w̄`. -/
lemma LatticeSplitsAt.conj_scalarFin_mem {Y : Grading V N X s} {w : FinPlace E} {x : Gf E ι}
    (h_split : Y.LatticeSplitsAt w x) (hw : star w ≠ w)
    {z : unitary (𝔸f E)} (hz_int : z.val ∈ Ô E)
    (hz_off : ∀ u : FinPlace E, u ≠ w → star u ≠ w → z.val u = 1) :
    x⁻¹ * (Y.inclXFin (scalarFin X z) * x) ∈ maxCompactAt ι w := by
  refine ⟨V.conj_mem_stdLevel_iff.2 fun y hy ↦ ?_, mem_supportedOn.2 fun u hu hu' ↦ ?_⟩
  · -- The conjugate is integral, as the scaling by `z` maps the lattice of `x` into itself.
    show V.ratCoordMatrixFin (Y.inclXFin (scalarFin X z)) *ᵥ y ∈ V.lattice x
    have h_supp : z.val - 1 = (z.val - 1) * (idem {w} + idem {star w}) := by
      ext u
      by_cases hu : u = w
      · simp [hu, hw.symm]
      by_cases hu' : u = star w
      · simp [hu', hw]
      -- At a place other than `w` and `w̄` both sides are `0`.
      have h_off : z.val u = 1 := hz_off u hu fun h_eq ↦ hu' (eq_star_of_eq_star h_eq.symm)
      simp [h_off]
    rw [inclXFin_scalarFin_mulVec, h_supp, mul_smul, add_smul]
    -- The two components of the part of `y` in `X`, at `w` and at `w̄`, lie in the lattice.
    exact add_mem hy ((V.lattice x).smul_mem ⟨_, sub_mem hz_int (one_mem _)⟩ (add_mem
      (h_split.idem_smul_sub_stringProj_mem hy) (h_split.conj.idem_smul_sub_stringProj_mem hy)))
  · -- The conjugate is trivial at a place other than `w` and `w̄`, where `z` is `1`.
    have h_scaling : atPlace u (Y.inclXFin (scalarFin X z)) = 1 := by
      simpa [atPlace, mul_eq_one_iff_eq_inv] using inclXFin_scalarFin_map_evalAt (hz_off u hu hu')
    simp [h_scaling]

end Splitting

/-- Write `Λ⁺` and `Λ'⁺` for the projections to `X^⊥` of the lattices of `1` and `x`, `Λ⁻` and `Λ'⁻`
for their intersections with `X^⊥`, and `M⁻` and `M'⁻` for the intersections with `X'^⊥` of the
lattices of `1` and `x'` in `V'`. Let `sh Λ⁺ = a M⁻` and `(q̄ / a) sh Λ'⁺ ⊆ M'⁻` for finite ideles
`a`, `q`. Then the upper bound `q ^ k Λ'⁻ ⊆ Λ⁻` on `V` gives `q̄ ^ (k + 1) M⁻ ⊆ M'⁻` on `V'`. -/
lemma smul_latticeMinus_le_of_map_latticePlus {Y : Grading V N X s} {Y' : Grading V' N X' (s - 1)}
    {a q : (𝔸f E)ˣ} {k : ℕ} {x : Gf E ι} {x' : Gf E ι'}
    (h_shift_one_eq : (Y.latticePlus 1).map ((Y.stringMapFin Y').restrictScalars (Ô E)) =
      a.val • Y'.latticeMinus 1)
    (h_upper : q.val ^ k • Y.latticeMinus x ≤ Y.latticeMinus 1)
    (h_shift_le : (star q / a).val •
      (Y.latticePlus x).map ((Y.stringMapFin Y').restrictScalars (Ô E)) ≤ Y'.latticeMinus x') :
    star q.val ^ (k + 1) • Y'.latticeMinus 1 ≤ Y'.latticeMinus x' := by
  refine smul_le_iff_forall.2 fun y hy ↦ ?_
  obtain ⟨z, hz, hzy⟩ : ∃ z ∈ Y.latticePlus 1, Y.stringMapFin Y' z = a.val • y :=
    h_shift_one_eq.ge (Submodule.smul_mem_pointwise_smul y a.val _ hy)
  -- The dual `q̄ ^ k Λ⁺ ⊆ Λ'⁺` of the upper bound puts `q̄ ^ k z` into `Λ'⁺`.
  have h_mem : star (q.val ^ k) • z ∈ Y.latticePlus x :=
    smul_le_iff_forall.1 (star_smul_latticePlus_le h_upper) z hz
  have h_eq : star q.val ^ (k + 1) • y =
      (star q / a).val • Y.stringMapFin Y' (star (q.val ^ k) • z) := by
    rw [map_smul, hzy, smul_smul, smul_smul, mul_right_comm, ← Units.val_mul, div_mul_cancel,
      Units.coe_star, star_pow, pow_succ']
  rw [h_eq]
  exact smul_le_iff_forall.1 h_shift_le _ (Submodule.mem_map_of_mem h_mem)

omit [Fintype X] in
/-- Write `Λ±` and `Λ'±` for the projection to `X^⊥` (`+`) and the intersection with it (`-`) of the
lattices of `1` and `x`, and `v` for the valuation at a place. Let `q` and `q̄` be units at `w`, let
`q̄ ^ k Λ⁻ ⊆ Λ'⁻` and `q ^ k Λ'⁺ ⊆ Λ⁺`, and let `y ∈ Λ'⁻` be such that `q ^ k y` generates `Λ⁺` over
`Λ⁻` at `w`. Then the lattice of `x` splits at `w`: there `Λ'⁺ ⊆ Λ⁺ = Λ⁻ + Ô y ⊆ Λ'⁻`. -/
lemma latticeSplitsAt_of_generates {Y : Grading V N X s} {q : (𝔸f E)ˣ} {k : ℕ} {x : Gf E ι}
    {w : FinPlace E} {y : ι → 𝔸f E}
    (h_lower : star q.val ^ k • Y.latticeMinus 1 ≤ Y.latticeMinus x)
    (h_dual : q.val ^ k • Y.latticePlus x ≤ Y.latticePlus 1)
    (hy : y ∈ Y.latticeMinus x) (hq : v (q.val w) = 1) (hq_star : v (q.val (star w)) = 1)
    (h_gen : ∀ z ∈ Y.latticePlus 1,
      ∃ c ∈ Ô E, (idem {w} : 𝔸f E) • (z - c • q.val ^ k • y) ∈ Y.latticeMinus 1) :
    Y.LatticeSplitsAt w x := by
  refine smul_le_iff_forall.2 fun z hz ↦ ?_
  obtain ⟨c, hc, h_sub⟩ : ∃ c ∈ Ô E,
      (idem {w} : 𝔸f E) • (q.val ^ k • z - c • q.val ^ k • y) ∈ Y.latticeMinus 1 :=
    h_gen (q.val ^ k • z) (smul_le_iff_forall.1 h_dual z hz)
  -- The norm `n = (q̄ q) ^ k` is a unit at `w`, so its inverse is integral there.
  let n : (𝔸f E)ˣ := (star q * q) ^ k
  have hn : idem {w} * n⁻¹.val ∈ Ô E := by
    simp [idem_mul_mem_Ô, n, ← inv_pow, idele_inv_apply_and_ne_zero, hq, hq_star]
  have h_inv : n⁻¹.val * (star q.val ^ k * q.val ^ k) = 1 := by
    rw [← mul_pow]
    exact n.inv_mul
  -- Split the component of `z` at `w` into its parts from `Λ⁻` and from `y`.
  have h_eq : (idem {w} : 𝔸f E) • z = (idem {w} * n⁻¹.val) • star q.val ^ k •
      (idem {w} : 𝔸f E) • (q.val ^ k • z - c • q.val ^ k • y) + (idem {w} * c) • y := by
    linear_combination (norm := module)
      (-(idem {w} * idem {w}) * h_inv - idem_mul_self (E := E) {w}) • (z - c • y)
  have h_sub_mem : star q.val ^ k • (idem {w} : 𝔸f E) • (q.val ^ k • z - c • q.val ^ k • y) ∈
      Y.latticeMinus x :=
    smul_le_iff_forall.1 h_lower _ h_sub
  rw [h_eq]
  exact add_mem ((Y.latticeMinus x).smul_mem ⟨_, hn⟩ h_sub_mem)
    ((Y.latticeMinus x).smul_mem ⟨_, mul_mem (idem_mem_Ô _) hc⟩ hy)

/-- Let the lattice of `1` have the basis `gradedLatticeBasis` built from the ideles `a`, `π` and
the unitary adele `u`. Let `N = π π̄` with `π` a uniformiser at the places of `P`, none of which has
its conjugate in `P`, and a unit elsewhere, and let `q` be a unit at the places of `P` and their
conjugates. Write `Λ⁻` and `Λ'⁻` for the intersections of the lattices of `1` and `x` with
`(X ⊕ Unit)^⊥`, and assume the lower bound `q̄ ^ k Λ⁻ ⊆ Λ'⁻`. Then the upper bound `q ^ k Λ'⁻ ⊆ Λ⁻`
holds too, or `s` is odd and the lattice of `x` splits at some `w ∈ P`: there its projection to
`(X ⊕ Unit)^⊥` lies in `Λ'⁻`. -/
lemma SpansLattice.hasLatticeBounds_or_latticeSplitsAt {Y : Grading V N (X ⊕ Unit) s}
    {a π q : (𝔸f E)ˣ} {u : unitary (𝔸f E)} {P : Finset (FinPlace E)} {k : ℕ} {x : Gf E ι}
    (hL : Y.SpansLattice a π u) (hπ : IsSplitSquarefree P N π)
    (hq : ∀ w : FinPlace E, w ∈ P ∨ star w ∈ P → v (q.val w) = 1)
    (h_lower : star q.val ^ k • Y.latticeMinus 1 ≤ Y.latticeMinus x) :
    Y.HasLatticeBounds q.val k x ∨ Odd s ∧ ∃ w ∈ P, Y.LatticeSplitsAt w x := by
  have h_dual : q.val ^ k • Y.latticePlus x ≤ Y.latticePlus 1 := by
    simpa only [star_pow, star_star] using star_smul_latticePlus_le h_lower
  refine or_iff_not_imp_left.2 fun h_fail ↦ ?_
  obtain ⟨y, hy, hy_notMem⟩ : ∃ y ∈ Y.latticeMinus x, q.val ^ k • y ∉ Y.latticeMinus 1 := by
    by_contra! h_upper
    exact h_fail ⟨h_lower, smul_le_iff_forall.2 h_upper⟩
  -- The vector `q ^ k y` of `Λ⁺` is not in `Λ⁻`, so it generates `Λ⁺` over `Λ⁻` at some `w ∣ N`.
  have h_plus : q.val ^ k • y ∈ Y.latticePlus 1 :=
    smul_le_iff_forall.1 h_dual y (latticeMinus_le_latticePlus hy)
  obtain ⟨hs, w, hw, h_gen⟩ : Odd s ∧ ∃ w : FinPlace E, (w ∈ P ∨ star w ∈ P) ∧
      ∀ z ∈ Y.latticePlus 1,
        ∃ c ∈ Ô E, (idem {w} : 𝔸f E) • (z - c • q.val ^ k • y) ∈ Y.latticeMinus 1 :=
    hL.odd_and_exists_place_of_notMem_latticeMinus hπ h_plus hy_notMem
  have hw_star : star w ∈ P ∨ star (star w) ∈ P := by simpa [or_comm] using hw
  have h_split : Y.LatticeSplitsAt w x :=
    latticeSplitsAt_of_generates h_lower h_dual hy (hq w hw) (hq (star w) hw_star) h_gen
  rcases hw with hw | hw
  · exact ⟨hs, w, hw, h_split⟩
  · exact ⟨hs, star w, hw, h_split.conj⟩

/-- Suppose that each translate `r x` by the finite Bessel subgroup `Y.besselFin` whose lattice is
graded (closed under the projections to the grades) has the bounds `Y.HasLatticeBounds q k`. Then
the orbit of `x` is bounded: some translate has both properties, as every orbit has a graded
lattice. The field `E` is assumed to contain a primitive root of unity of order `5040`. -/
lemma HasBoundedOrbit.of_forall [HasPrimitiveRoot5040 E] {Y : Grading V N X s} {q : 𝔸f E} {k : ℕ}
    {x : Gf E ι} (h_bounds : ∀ r ∈ Y.besselFin,
      Y.IsGraded (V.lattice (r * x)) → Y.HasLatticeBounds q k (r * x)) :
    Y.HasBoundedOrbit q k x := by
  obtain ⟨u, hu, h_graded⟩ :
      ∃ u : Gf E ι, ((1, u) : G E ε) ∈ Y.unipotent ∧ Y.IsGraded (V.lattice (u * x)) :=
    Y.exists_isGraded x
  have hu_bessel : u ∈ Y.besselFin := Y.unipotent_le_besselGroup hu
  exact ⟨u, hu_bessel, h_graded, h_bounds u hu_bessel h_graded⟩

/-- Let the lattice of `1`, spanned by the finite frame `V.xFin`, have the basis
`gradedLatticeBasis` with parameters `a`, `π`, `u`. If the orbit of the finite point `x` under the
finite Bessel subgroup `Y.besselFin` has an integral point `r x ∈ stdLevel E ι`, then some point of
the orbit has a graded lattice with the bounds for `k = 0`: the lattice of `r x` is the one of
`1`. -/
lemma SpansLattice.hasBoundedOrbit_zero {Y : Grading V N (X ⊕ Unit) s} {a π : (𝔸f E)ˣ}
    {u : unitary (𝔸f E)} (hL : Y.SpansLattice a π u) (q : 𝔸f E) {r x : Gf E ι}
    (hr : r ∈ Y.besselFin) (hx : r * x ∈ stdLevel E ι) : Y.HasBoundedOrbit q 0 x := by
  have h_lattice : V.lattice (r * x) = V.lattice 1 := (lattice_eq_iff.2 (by simpa using hx)).symm
  have h_minus : Y.latticeMinus (r * x) = Y.latticeMinus 1 := by simp [latticeMinus, h_lattice]
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · simpa [h_lattice] using hL.isGraded
  · simp [h_minus]
  · simp [h_minus]

end Grading

end New

end
