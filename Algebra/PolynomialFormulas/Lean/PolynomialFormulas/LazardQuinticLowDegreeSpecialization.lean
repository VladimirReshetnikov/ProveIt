import PolynomialFormulas.Fin5Solvable
import PolynomialFormulas.Fin5DihedralCore
import PolynomialFormulas.FrobeniusDummitResolvent
import PolynomialFormulas.LazardGeneralResolventExplicit
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Low-degree cyclic invariants on the roots of `X^5 - a`

This file gives the corrected form of the low-degree specialization argument
in Section 5 of Lazard's *Solving Quintics by Radicals*.

If `omega` is a primitive fifth root of unity and

`r_i = alpha * omega^i`,

then a positive-degree homogeneous polynomial of degree below five which is
invariant under the regular five-cycle evaluates to zero at `r`.  Consequently
an arbitrary cyclic invariant of total degree below five evaluates to its
constant coefficient, rather than necessarily to zero.  In particular, the
constant invariant `1` is an explicit counterexample to the literal printed
vanishing assertion.

The standard `C5` is normal in its normalizer `F20`.  Thus every `F20`
translate of a low-degree `C5`-invariant is again `C5`-invariant and all such
translated values collide at the displayed root tuple.  This is the actual
mechanism behind the inseparability obstruction for the low-degree relative
resolvent.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuinticLowDegreeSpecialization

open MvPolynomial
open LeanProofs.PolynomialFormulas.Fin5Solvable

/- Lean 4.32 has no namespace-assignment aliases.  These local shims expose
only the declarations used in this file. -/
namespace Action
export LeanProofs.PolynomialFormulas.LazardGeneralResolventExplicit
  (InvariantUnder renameAction renameAction_mul specializedOrbitValue
    universalOrbitValue_mk)
end Action

namespace Resolvent
export LeanProofs.PolynomialFormulas.LazardGeneralResolventCriterion
  (Cosets orbitResolvent orbitResolvent_separable_iff)
end Resolvent

namespace F20
export LeanProofs.PolynomialFormulas.FrobeniusDummitResolvent
  (multiplierTwo multiplierTwo_mem_standardF20)
end F20

namespace Classification
export LeanProofs.PolynomialFormulas.Fin5DihedralCore
  (mem_standardD5_iff standardC5_le_standardD5 standardD5)
end Classification

noncomputable section

noncomputable local instance cosetsFintype (G : Subgroup S5) :
    Fintype (Resolvent.Cosets G) := Fintype.ofFinite _

/-- Evaluation of a homogeneous polynomial after multiplying every variable
by the same scalar. -/
theorem eval_mul_variables_of_isHomogeneous
    {K σ : Type*} [CommRing K] [Fintype σ]
    {p : MvPolynomial σ K} {d : ℕ}
    (hp : p.IsHomogeneous d) (z : K) (x : σ → K) :
    MvPolynomial.eval (fun i ↦ z * x i) p =
      z ^ d * MvPolynomial.eval x p := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmDegree : ∑ i, m i = d := by
    calc
      ∑ i, m i = m.degree := (Finsupp.degree_eq_sum m).symm
      _ = ∑ i ∈ m.support, m i := Finsupp.degree_apply m
      _ = d := (hp.degree_eq_sum_deg_support hm).symm
  have hzDegree : (∏ i, z ^ m i) = z ^ d := by
    calc
      (∏ i, z ^ m i) = z ^ ∑ i, m i := by
        simpa using
          (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset σ) (fun i ↦ m i) z)
      _ = z ^ d := by rw [hmDegree]
  simp only [mul_pow, Finset.prod_mul_distrib, hzDegree]
  ring

/-- The five roots `alpha * omega^i` of `X^5 - alpha^5`, in their cyclic
ordering. -/
def radicalRootTuple {K : Type*} [CommRing K] (α ω : K) : Fin 5 → K :=
  fun i ↦ α * ω ^ i.val

/-- The standard five-cycle multiplies the cyclic root tuple by `omega`. -/
theorem radicalRootTuple_fiveCycle
    {K : Type*} [CommRing K] {α ω : K}
    (hω : IsPrimitiveRoot ω 5) (i : Fin 5) :
    radicalRootTuple α ω (fiveCycle i) =
      ω * radicalRootTuple α ω i := by
  fin_cases i <;>
    simp [radicalRootTuple, fiveCycle, finRotate_apply, pow_succ]
  all_goals ring_nf
  rw [hω.pow_eq_one, one_mul]

/-- Every entry of the cyclic tuple is a root of `X^5 - alpha^5`. -/
theorem radicalRootTuple_isRoot
    {K : Type*} [Field K] {α ω : K}
    (hω : IsPrimitiveRoot ω 5) (i : Fin 5) :
    (Polynomial.X ^ 5 - Polynomial.C (α ^ 5)).IsRoot
      (radicalRootTuple α ω i) := by
  simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, radicalRootTuple, mul_pow]
  rw [show (ω ^ i.val) ^ 5 = (ω ^ 5) ^ i.val by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
  rw [hω.pow_eq_one, one_pow, mul_one, sub_self]

/-- If `alpha` is nonzero, the displayed five roots are distinct. -/
theorem radicalRootTuple_injective
    {K : Type*} [Field K] {α ω : K}
    (hα : α ≠ 0) (hω : IsPrimitiveRoot ω 5) :
    Function.Injective (radicalRootTuple α ω) := by
  intro i j hij
  have hpowers : ω ^ i.val = ω ^ j.val := by
    apply (mul_left_cancel₀ hα)
    simpa only [radicalRootTuple] using hij
  exact Fin.ext (hω.pow_inj i.isLt j.isLt hpowers)

/-- Invariance under the standard regular cyclic subgroup. -/
def CyclicInvariant {K : Type*} [CommRing K]
    (p : MvPolynomial (Fin 5) K) : Prop :=
  Action.InvariantUnder standardC5 p

/-- Homogeneous components of a cyclic invariant remain cyclic invariant. -/
theorem cyclicInvariant_homogeneousComponent
    {K : Type*} [CommRing K]
    {p : MvPolynomial (Fin 5) K}
    (hp : CyclicInvariant p) (d : ℕ) :
    CyclicInvariant (MvPolynomial.homogeneousComponent d p) := by
  intro g hg
  change MvPolynomial.rename g
      (MvPolynomial.homogeneousComponent d p) =
    MvPolynomial.homogeneousComponent d p
  have hpg := hp g hg
  change MvPolynomial.rename g p = p at hpg
  rw [MvPolynomial.rename_homogeneousComponent, hpg]

/-- Correct homogeneous form of Lazard's low-degree specialization claim.

Every positive-degree homogeneous `C5`-invariant of degree below five
vanishes on the cyclic roots of `X^5 - alpha^5`. -/
theorem eval_eq_zero_of_cyclicInvariant_isHomogeneous
    {K : Type*} [Field K] {α ω : K}
    (hω : IsPrimitiveRoot ω 5)
    {p : MvPolynomial (Fin 5) K} {d : ℕ}
    (hinvariant : CyclicInvariant p)
    (hh : p.IsHomogeneous d) (hd0 : 0 < d) (hd5 : d < 5) :
    MvPolynomial.eval (radicalRootTuple α ω) p = 0 := by
  have hcycle :
      Action.renameAction fiveCycle p = p :=
    hinvariant fiveCycle (by
      change fiveCycle ∈ Subgroup.zpowers fiveCycle
      exact Subgroup.mem_zpowers fiveCycle)
  have heval := congrArg (MvPolynomial.eval (radicalRootTuple α ω)) hcycle
  change MvPolynomial.eval (radicalRootTuple α ω)
      (MvPolynomial.rename fiveCycle p) =
    MvPolynomial.eval (radicalRootTuple α ω) p at heval
  rw [MvPolynomial.eval_rename] at heval
  have htuple :
      radicalRootTuple α ω ∘ fiveCycle =
        fun i ↦ ω * radicalRootTuple α ω i := by
    funext i
    exact radicalRootTuple_fiveCycle hω i
  rw [htuple, eval_mul_variables_of_isHomogeneous hh] at heval
  have hωd : ω ^ d ≠ 1 :=
    hω.pow_ne_one_of_pos_of_lt hd0.ne' hd5
  have hproduct :
      (ω ^ d - 1) * MvPolynomial.eval (radicalRootTuple α ω) p = 0 := by
    rw [sub_mul, heval, one_mul, sub_self]
  exact (mul_eq_zero.mp hproduct).resolve_left (sub_ne_zero.mpr hωd)

/-- Correct arbitrary-polynomial form: a cyclic invariant of total degree
below five specializes to its constant coefficient. -/
theorem eval_eq_constantCoeff_of_cyclicInvariant_totalDegree_lt_five
    {K : Type*} [Field K] {α ω : K}
    (hω : IsPrimitiveRoot ω 5)
    {p : MvPolynomial (Fin 5) K}
    (hinvariant : CyclicInvariant p) (hdegree : p.totalDegree < 5) :
    MvPolynomial.eval (radicalRootTuple α ω) p =
      MvPolynomial.constantCoeff p := by
  classical
  let r := radicalRootTuple α ω
  have hvanish : ∀ d ∈ Finset.range (p.totalDegree + 1), d ≠ 0 →
      MvPolynomial.eval r (MvPolynomial.homogeneousComponent d p) = 0 := by
    intro d hd hd0
    apply eval_eq_zero_of_cyclicInvariant_isHomogeneous hω
      (cyclicInvariant_homogeneousComponent hinvariant d)
      (MvPolynomial.homogeneousComponent_isHomogeneous d p)
    · omega
    · have hdle : d ≤ p.totalDegree := by
        have hdlt : d < p.totalDegree + 1 := Finset.mem_range.mp hd
        omega
      exact lt_of_le_of_lt hdle hdegree
  have hsum :
      (∑ d ∈ Finset.range (p.totalDegree + 1),
          MvPolynomial.eval r (MvPolynomial.homogeneousComponent d p)) =
        MvPolynomial.eval r (MvPolynomial.homogeneousComponent 0 p) := by
    apply Finset.sum_eq_single 0
    · intro d hd hd0
      exact hvanish d hd hd0
    · simp
  calc
    MvPolynomial.eval r p =
        MvPolynomial.eval r
          (∑ d ∈ Finset.range (p.totalDegree + 1),
            MvPolynomial.homogeneousComponent d p) := by
              rw [MvPolynomial.sum_homogeneousComponent]
    _ = ∑ d ∈ Finset.range (p.totalDegree + 1),
          MvPolynomial.eval r (MvPolynomial.homogeneousComponent d p) := by
            simp
    _ = MvPolynomial.eval r (MvPolynomial.homogeneousComponent 0 p) := hsum
    _ = MvPolynomial.constantCoeff p := by
      simp [MvPolynomial.constantCoeff_eq]

/-- Normality of `C5` in `F20` preserves cyclic invariance under every
`F20` translate. -/
theorem cyclicInvariant_rename_of_mem_standardF20
    {K : Type*} [CommRing K]
    {p : MvPolynomial (Fin 5) K}
    (hinvariant : CyclicInvariant p) {g : S5}
    (hg : g ∈ standardF20) :
    CyclicInvariant (Action.renameAction g p) := by
  intro c hc
  have hgNormalizer : g ∈ Subgroup.normalizer standardC5 := by
    exact hg
  have hconjugate : g⁻¹ * c * g ∈ standardC5 :=
    (Subgroup.mem_normalizer_iff''.mp hgNormalizer c).mp hc
  calc
    Action.renameAction c (Action.renameAction g p) =
        Action.renameAction (c * g) p :=
      (Action.renameAction_mul c g p).symm
    _ = Action.renameAction (g * (g⁻¹ * c * g)) p := by
      congr 1
      group
    _ = Action.renameAction g (Action.renameAction (g⁻¹ * c * g) p) :=
      Action.renameAction_mul g (g⁻¹ * c * g) p
    _ = Action.renameAction g p := by
      rw [hinvariant (g⁻¹ * c * g) hconjugate]

/-- Every relevant `F20` translate has the same specialized value, namely
the original constant coefficient. -/
theorem eval_rename_eq_constantCoeff_of_mem_standardF20
    {K : Type*} [Field K] {α ω : K}
    (hω : IsPrimitiveRoot ω 5)
    {p : MvPolynomial (Fin 5) K}
    (hinvariant : CyclicInvariant p) (hdegree : p.totalDegree < 5)
    {g : S5} (hg : g ∈ standardF20) :
    MvPolynomial.eval (radicalRootTuple α ω)
        (Action.renameAction g p) = MvPolynomial.constantCoeff p := by
  have hdegreeRename : (Action.renameAction g p).totalDegree < 5 := by
    change (MvPolynomial.rename g p).totalDegree < 5
    exact lt_of_le_of_lt (MvPolynomial.totalDegree_rename_le g p) hdegree
  rw [eval_eq_constantCoeff_of_cyclicInvariant_totalDegree_lt_five hω
    (cyclicInvariant_rename_of_mem_standardF20 hinvariant hg) hdegreeRename]
  exact MvPolynomial.constantCoeff_rename g p

/-- Hence any two `F20` conjugate values collide. -/
theorem eval_rename_eq_eval_rename_of_mem_standardF20
    {K : Type*} [Field K] {α ω : K}
    (hω : IsPrimitiveRoot ω 5)
    {p : MvPolynomial (Fin 5) K}
    (hinvariant : CyclicInvariant p) (hdegree : p.totalDegree < 5)
    {g h : S5} (hg : g ∈ standardF20) (hh : h ∈ standardF20) :
    MvPolynomial.eval (radicalRootTuple α ω)
        (Action.renameAction g p) =
      MvPolynomial.eval (radicalRootTuple α ω)
        (Action.renameAction h p) := by
  rw [eval_rename_eq_constantCoeff_of_mem_standardF20 hω
      hinvariant hdegree hg,
    eval_rename_eq_constantCoeff_of_mem_standardF20 hω
      hinvariant hdegree hh]

/-- Multiplication by two represents a genuinely different `C5` coset from
the identity.  This makes the collision below a repeated factor rather than
two names for the same formal conjugate. -/
theorem multiplierTwo_not_mem_standardC5 :
    F20.multiplierTwo ∉ standardC5 := by
  rw [← LeanProofs.PolynomialFormulas.Fin5TransitiveC5.mem_c5Elements_iff]
  decide

/-- The specialized value of every `F20` representative in the `S5/C5`
orbit is the constant coefficient. -/
theorem specializedOrbitValue_eq_constantCoeff_of_mem_standardF20
    {K : Type*} [Field K] { α ω : K }
    (hω : IsPrimitiveRoot ω 5)
    {p : MvPolynomial (Fin 5) K}
    (hinvariant : CyclicInvariant p) (hdegree : p.totalDegree < 5)
    {g : S5} (hg : g ∈ standardF20) :
    Action.specializedOrbitValue standardC5 p hinvariant
        (radicalRootTuple α ω)
        (g : Resolvent.Cosets standardC5) =
      MvPolynomial.constantCoeff p := by
  rw [Action.specializedOrbitValue, Action.universalOrbitValue_mk]
  change MvPolynomial.eval (radicalRootTuple α ω)
      (Action.renameAction g p) = MvPolynomial.constantCoeff p
  exact eval_rename_eq_constantCoeff_of_mem_standardF20
    hω hinvariant hdegree hg

/-- The identity and multiplier-by-two classes are distinct in `S5/C5`,
but every cyclic invariant of total degree below five takes the same value
on them at the cyclic binomial root tuple. -/
theorem cyclic_distinctCosetValue_collision
    {K : Type*} [Field K] {α ω : K}
    (hω : IsPrimitiveRoot ω 5)
    {p : MvPolynomial (Fin 5) K}
    (hinvariant : CyclicInvariant p) (hdegree : p.totalDegree < 5) :
    ((1 : S5) : Resolvent.Cosets standardC5) ≠
        (F20.multiplierTwo : Resolvent.Cosets standardC5) ∧
      Action.specializedOrbitValue standardC5 p hinvariant
          (radicalRootTuple α ω)
          ((1 : S5) : Resolvent.Cosets standardC5) =
        Action.specializedOrbitValue standardC5 p hinvariant
          (radicalRootTuple α ω)
          (F20.multiplierTwo : Resolvent.Cosets standardC5) := by
  constructor
  · intro hcosets
    apply multiplierTwo_not_mem_standardC5
    have := QuotientGroup.leftRel_apply.mp (Quotient.exact' hcosets)
    simpa using this
  · rw [specializedOrbitValue_eq_constantCoeff_of_mem_standardF20
        hω hinvariant hdegree (Subgroup.one_mem standardF20),
      specializedOrbitValue_eq_constantCoeff_of_mem_standardF20
        hω hinvariant hdegree F20.multiplierTwo_mem_standardF20]

/-- Paper-level consequence of the corrected low-degree specialization
argument: the relative `S5/C5` resolvent has a repeated linear factor on the
roots of `X^5 - alpha^5`, hence is not separable.

No exact-stabilizer hypothesis is needed for this negative statement.  If
`p` is a genuine `C5` resolvent invariant, the theorem applies in particular
to that stronger situation. -/
theorem lowDegree_cyclic_relativeResolvent_not_separable
    {K : Type*} [Field K] { α ω : K }
    (hω : IsPrimitiveRoot ω 5)
    {p : MvPolynomial (Fin 5) K}
    (hinvariant : CyclicInvariant p) (hdegree : p.totalDegree < 5) :
    ¬ (Resolvent.orbitResolvent standardC5
        (Action.specializedOrbitValue standardC5 p hinvariant
          (radicalRootTuple α ω))).Separable := by
  rw [Resolvent.orbitResolvent_separable_iff]
  intro hinjective
  have hvalues :
      Action.specializedOrbitValue standardC5 p hinvariant
          (radicalRootTuple α ω)
          ((1 : S5) : Resolvent.Cosets standardC5) =
        Action.specializedOrbitValue standardC5 p hinvariant
          (radicalRootTuple α ω)
          (F20.multiplierTwo : Resolvent.Cosets standardC5) := by
    rw [specializedOrbitValue_eq_constantCoeff_of_mem_standardF20
        hω hinvariant hdegree (Subgroup.one_mem standardF20),
      specializedOrbitValue_eq_constantCoeff_of_mem_standardF20
        hω hinvariant hdegree F20.multiplierTwo_mem_standardF20]
  have hcosets :
      ((1 : S5) : Resolvent.Cosets standardC5) =
        (F20.multiplierTwo : Resolvent.Cosets standardC5) :=
    hinjective hvalues
  have hmem : F20.multiplierTwo ∈ standardC5 := by
    have := QuotientGroup.leftRel_apply.mp (Quotient.exact' hcosets)
    simpa using this
  exact multiplierTwo_not_mem_standardC5 hmem

/-! ## The corresponding `D5` relative resolvent

The paper's degree-five lower bound is asserted for invariants of both `C5`
and `D5`.  A collision in `S5/C5` does not by itself prove a collision in
`S5/D5`, because two distinct `C5` cosets can become the same `D5` coset.
The multiplier-by-two element is outside `D5` as well, so the same two
specialized values give the required literal `S5/D5` repeated factor. -/

theorem multiplierTwo_not_mem_standardD5 :
    F20.multiplierTwo ∉ Classification.standardD5 := by
  rw [Classification.mem_standardD5_iff]
  decide

/-- A `D5`-invariant is, in particular, cyclic invariant. -/
theorem cyclicInvariant_of_D5Invariant
    {K : Type*} [CommRing K]
    {p : MvPolynomial (Fin 5) K}
    (hD : Action.InvariantUnder Classification.standardD5 p) :
    CyclicInvariant p := by
  intro c hc
  exact hD c (Classification.standardC5_le_standardD5 hc)

/-- Every `F20` representative in the `S5/D5` orbit again specializes to
the constant coefficient. -/
theorem specializedD5OrbitValue_eq_constantCoeff_of_mem_standardF20
    {K : Type*} [Field K] {α ω : K}
    (hω : IsPrimitiveRoot ω 5)
    {p : MvPolynomial (Fin 5) K}
    (hD : Action.InvariantUnder Classification.standardD5 p)
    (hdegree : p.totalDegree < 5)
    {g : S5} (hg : g ∈ standardF20) :
    Action.specializedOrbitValue Classification.standardD5 p hD
        (radicalRootTuple α ω)
        (g : Resolvent.Cosets Classification.standardD5) =
      MvPolynomial.constantCoeff p := by
  rw [Action.specializedOrbitValue, Action.universalOrbitValue_mk]
  exact eval_rename_eq_constantCoeff_of_mem_standardF20 hω
    (cyclicInvariant_of_D5Invariant hD) hdegree hg

/-- The corresponding collision is genuinely between distinct `S5/D5`
classes, so it does not merely reuse the finer `S5/C5` quotient. -/
theorem dihedral_distinctCosetValue_collision
    {K : Type*} [Field K] {α ω : K}
    (hω : IsPrimitiveRoot ω 5)
    {p : MvPolynomial (Fin 5) K}
    (hD : Action.InvariantUnder Classification.standardD5 p)
    (hdegree : p.totalDegree < 5) :
    ((1 : S5) : Resolvent.Cosets Classification.standardD5) ≠
        (F20.multiplierTwo : Resolvent.Cosets Classification.standardD5) ∧
      Action.specializedOrbitValue Classification.standardD5 p hD
          (radicalRootTuple α ω)
          ((1 : S5) : Resolvent.Cosets Classification.standardD5) =
        Action.specializedOrbitValue Classification.standardD5 p hD
          (radicalRootTuple α ω)
          (F20.multiplierTwo : Resolvent.Cosets Classification.standardD5) := by
  constructor
  · intro hcosets
    apply multiplierTwo_not_mem_standardD5
    have := QuotientGroup.leftRel_apply.mp (Quotient.exact' hcosets)
    simpa using this
  · rw [specializedD5OrbitValue_eq_constantCoeff_of_mem_standardF20
        hω hD hdegree (Subgroup.one_mem standardF20),
      specializedD5OrbitValue_eq_constantCoeff_of_mem_standardF20
        hω hD hdegree F20.multiplierTwo_mem_standardF20]

/-- Literal `S5/D5` counterpart of the cyclic obstruction: every
degree-below-five `D5`-invariant has a nonseparable relative orbit resolvent
on the cyclic binomial root tuple. -/
theorem lowDegree_dihedral_relativeResolvent_not_separable
    {K : Type*} [Field K] {α ω : K}
    (hω : IsPrimitiveRoot ω 5)
    {p : MvPolynomial (Fin 5) K}
    (hD : Action.InvariantUnder Classification.standardD5 p)
    (hdegree : p.totalDegree < 5) :
    ¬ (Resolvent.orbitResolvent Classification.standardD5
        (Action.specializedOrbitValue Classification.standardD5 p hD
          (radicalRootTuple α ω))).Separable := by
  rw [Resolvent.orbitResolvent_separable_iff]
  intro hinjective
  have hvalues :
      Action.specializedOrbitValue Classification.standardD5 p hD
          (radicalRootTuple α ω)
          ((1 : S5) : Resolvent.Cosets Classification.standardD5) =
        Action.specializedOrbitValue Classification.standardD5 p hD
          (radicalRootTuple α ω)
          (F20.multiplierTwo : Resolvent.Cosets Classification.standardD5) := by
    rw [specializedD5OrbitValue_eq_constantCoeff_of_mem_standardF20
        hω hD hdegree (Subgroup.one_mem standardF20),
      specializedD5OrbitValue_eq_constantCoeff_of_mem_standardF20
        hω hD hdegree F20.multiplierTwo_mem_standardF20]
  have hcosets :
      ((1 : S5) : Resolvent.Cosets Classification.standardD5) =
        (F20.multiplierTwo : Resolvent.Cosets Classification.standardD5) :=
    hinjective hvalues
  have hmem : F20.multiplierTwo ∈ Classification.standardD5 := by
    have := QuotientGroup.leftRel_apply.mp (Quotient.exact' hcosets)
    simpa using this
  exact multiplierTwo_not_mem_standardD5 hmem

/-- Explicit counterexample to the paper's literal claim that every cyclic
invariant of degree below five specializes to zero: the invariant `1` has
degree zero and evaluates to one. -/
theorem literal_low_degree_vanishing_counterexample
    {K : Type*} [Field K] (α ω : K) :
    CyclicInvariant (1 : MvPolynomial (Fin 5) K) ∧
      (1 : MvPolynomial (Fin 5) K).totalDegree < 5 ∧
      MvPolynomial.eval (radicalRootTuple α ω)
          (1 : MvPolynomial (Fin 5) K) ≠ 0 := by
  constructor
  · intro g hg
    simp [Action.renameAction]
  · simp

end

end LeanProofs.PolynomialFormulas.LazardQuinticLowDegreeSpecialization
