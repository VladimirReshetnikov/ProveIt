import Lib.General.NumberTheory.FrobeniusOrbits
import Lib.Weil.Construction.FiniteMultiplier
import Lib.Weil.Construction.WeilOperators

/-!
# The finite cocycle as a finite Gauss sum, and its triviality

This file treats the matrix action of the finite unitary group `New.Gf` on the finite Heisenberg
datum `New.stdLattice.finHeisenberg` of vectors `ι → 𝔸f E`, with vacuum `New.stdLattice.finVac` and
multiplier `New.finMultiplier`. We write `Ô` for `New.Ô E`, `ψ₀` for
`New.stdLattice.selfDualAddChar E`, `x* y` for `star x ⬝ᵥ y`, and `c₀` for `WeilData.traceOne`.
The double integral in the resulting cocycle is a finite Gauss sum, and the cocycle equals `1`.

## Main definitions and results

* `New.stdLattice.exists_gauss_sum_finProjAction`: the double integral in the cocycle is a Gauss sum
  over a finite module over `New.Ô`, the ring of integral finite adeles.
* `New.stdLattice.mem_cocycleRadical`: the cocycle is `1` at all `g` and `s`.
* `New.finAction`: the same action with cocycle `1`, as used for the adelic Weil representation.

Notions from other files:
* `New.WeilData`: Weil data on a CM field E: ȷ in E with ȷ = −ȷ̄, a finite idele α for which Ô is
  self-dual under (z, u) ↦ ψ_f(ȷαᾱzu), and a splitting character υ.
* `New.Heisenberg.IsVacuum`: a vacuum for β and μ is a continuous, integrable, even, real function e
  with e(0) = 1 and ∫ e(z)e(x−y−z)β(z,y)β(z+y,x) dμ(z) = e(y)e(x).
* `New.Heisenberg.MultiplierAction`: an action of G on W that preserves β and μ. It comes with a
  continuous multiplier Δ: G → ℂ such that Δ(1) = 1, Δ(g⁻¹) = conj Δ(g) and Δ(g)Δ(h)Δ((gh)⁻¹) ∬
  e(hx)e(ghy)β(x,y)e(x+y) = c(g,h).
* `New.stdLattice.finVac`: the function `ψ₀ (c₀ x* x / 2)` on the lattice `Ô ^ ι` and `0` off it.
* `New.finMultiplier`: for g in `New.Gf`, Δ_f(g) = χ_f(det u) with uÔ^ι = Ô^ι ∩ g⁻¹Ô^ι and
  χ_f = υ|·|^(−1/2).

## Relation to the literature

Known; see `Lib.Weil.MixedModel.ZeroTerm` for sources.
-/

noncomputable section

namespace New.stdLattice

/-!
## The finite cocycle as a finite Gauss sum

The vacuum `New.stdLattice.finVac` vanishes off the standard lattice. So the integrand of the double
integral that defines the cocycle lives on a compact module, where it is invariant under an open
submodule.
-/

section FiniteCocycle

open MeasureTheory Matrix NumberField Submodule Set Function

universe u_1 u_2

variable {E : Type u_1} {ι : Type u_2} [Field E] [CMType E]
  [WeilData E] [Fintype ι] [DecidableEq ι]

/-- The matrix action of the finite unitary group on the finite Heisenberg datum (β x y = ψ₀(y*
x / 2); vacuum `finVac` = ψ₀(c₀ x* x / 2) on Ô^ι and `0` off it; `latticeMeasure` the Haar measure
giving Ô^ι mass one), with multiplier `New.finMultiplier`, paired with its cocycle
`finProjAction.1`, for which the cocycle identity holds by definition. -/
noncomputable def finProjAction :
    Σ c : Gf E ι → Gf E ι → ℂ,
      (finHeisenberg E ι).MultiplierAction (latticeMeasure E ι) finVac (Gf E ι) c where
  fst g h :=
    finMultiplier g * finMultiplier h * finMultiplier (g * h)⁻¹ *
      ∫ x : ι → 𝔸f E, ∫ y : ι → 𝔸f E, finVac (h • x) * finVac ((g * h) • y) * (finHeisenberg E ι).β
        x y *
        finVac (x + y) ∂latticeMeasure E ι ∂latticeMeasure E ι
  snd :=
    { beta_smul := by simp [finHeisenberg, HSMul.hSMul, SMul.smul]
      -- `g` scales Haar measure by the inverse idele norm of its determinant, which is `1`.
      measurePreserving g :=
        ⟨by fun_prop, (map_mulVec_haar_finAdele ..).trans (by simp [g.finIdeleAbs_det])⟩
      Δ := finMultiplier
      continuous_delta := by
        -- `finMultiplier` is invariant under right translation by the open subgroup `stdLevel E ι`.
        refine (isLocallyConstant_of_eventually_mul
          ((isOpen_stdLevel.eventually_mem (one_mem _)).mono fun k hk g ↦ ?_)).continuous
        simpa using! glMultiplier_mul_of_mem g (one_mem _) hk
      Δ_one := finMultiplier_eq_one_of_mem (one_mem (stdLevel E ι))
      Δ_inv := finMultiplier_inv
      cocycle _ _ := rfl }

open scoped Classical in
/-- The integrand of the double integral in the cocycle at `(g, s)`, made of the vacuum `finVac`
(ψ₀(c₀ x* x / 2) on Ô^ι, `0` off it) and the bicharacter `β` of `finHeisenberg`, is
`selfDualAddChar E (c̄₀ y* x)`, with `c₀ = traceOneAdele`, if `x + y`, `s x` and `g s y` lie in the
standard lattice, and `0` otherwise. -/
lemma cocycleIntegrand_eq (g s : Gf E ι) (x y : ι → 𝔸f E) :
    finVac (s • x) * finVac ((g * s) • y) * (finHeisenberg E ι).β x y * finVac (x + y) =
      if x + y ∈ stdLattice E ι ∧ s • x ∈ stdLattice E ι ∧ (g * s) • y ∈ stdLattice E ι then
        selfDualAddChar E (star traceOneAdele * star y ⬝ᵥ x) else 0 := by
  -- The function `semichar` is invariant under unitary matrices and squares to `1` on the lattice.
  have h_smul (h : Gf E ι) (z : ι → 𝔸f E) : semichar (h • z) = semichar z := by
    simp [semichar, HSMul.hSMul, SMul.smul]
  split_ifs with h
  · obtain ⟨h_sum, hx, hy⟩ := h
    calc _ = semichar (s • x) * semichar ((g * s) • y) * (finHeisenberg E ι).β x y *
          semichar (x + y) := by simp [finVac, semichar, h_sum, hx, hy]
      _ = selfDualAddChar E (star traceOneAdele * star y ⬝ᵥ x) *
        (semichar (x + y) * semichar (x + y)) := by
        rw [h_smul, h_smul, semichar_add, mul_assoc]
      _ = selfDualAddChar E (star traceOneAdele * star y ⬝ᵥ x) := by
        rw [semichar_mul_self h_sum, mul_one]
  · simp only [finVac]
    grind

/-- Let `(x₁, x₂)` and `(y₁, y₂)` be pairs whose sums and whose images under `(s, g s)` lie in the
standard lattice, and which differ by lattice vectors. Then `selfDualAddChar E (c̄₀ x₂* x₁)` and
`selfDualAddChar E (c̄₀ y₂* y₁)` agree. -/
lemma selfDualAddChar_traceOne_dot_congr (g s : Gf E ι) {x₁ x₂ y₁ y₂ : ι → 𝔸f E}
    (hx : x₁ + x₂ ∈ stdLattice E ι) (hy : y₁ + y₂ ∈ stdLattice E ι)
    (hsx : s • x₁ ∈ stdLattice E ι) (hsy : s • y₁ ∈ stdLattice E ι)
    (hgsx : (g * s) • x₂ ∈ stdLattice E ι) (hgsy : (g * s) • y₂ ∈ stdLattice E ι)
    (hd₁ : -x₁ + y₁ ∈ stdLattice E ι) (hd₂ : -x₂ + y₂ ∈ stdLattice E ι) :
    selfDualAddChar E (star traceOneAdele * star y₂ ⬝ᵥ y₁) = selfDualAddChar E
      (star traceOneAdele * star x₂ ⬝ᵥ x₁) := by
  -- The pairing is unchanged when `s`, or `g * s`, is applied to both vectors.
  have h_fst' : star y₁ ⬝ᵥ (y₁ - x₁) ∈ Ô E := by
    rw [← star_mulVec_dotProduct_mulVec s, mulVec_sub]
    exact star_dotProduct_mem (sub_mem hsy hsx) hsy
  have h_snd' : star (y₂ - x₂) ⬝ᵥ x₂ ∈ Ô E := by
    rw [← star_mulVec_dotProduct_mulVec (g * s), mulVec_sub]
    exact star_dotProduct_mem hgsx (sub_mem hgsy hgsx)
  -- The two pairings differ by a combination of these four integral ones.
  have h_diff : star y₂ ⬝ᵥ y₁ = star x₂ ⬝ᵥ x₁ +
      ((star (y₁ + y₂) ⬝ᵥ (-x₁ + y₁) - star y₁ ⬝ᵥ (y₁ - x₁)) +
        (star (-x₂ + y₂) ⬝ᵥ (x₁ + x₂) - star (y₂ - x₂) ⬝ᵥ x₂)) := by
    simp [neg_add_eq_sub]
    ring
  refine selfDualAddChar_congr 0 (mul_mem (star_mem_Ô traceOneAdele_mem)
    (add_mem (sub_mem (star_dotProduct_mem hd₁ hy) h_fst')
      (sub_mem (star_dotProduct_mem hx hd₂) h_snd'))) ?_
  rw [h_diff, mul_add, star_zero, add_zero, add_zero]

/-- The pairs `(x, y)` of finite adelic vectors such that `x + y`, `s x` and `g s y` lie in the
lattice `Ô^ι`, as an `Ô E`-submodule. The integrand of the cocycle at `(g, s)` lives on it
(`New.stdLattice.cocycleIntegrand_eq`). -/
def cocycleSubmodule {E : Type u_1} [Field E] [NumberField E] [IsCMField E]
    (g s : Gf E ι) : Submodule (Ô E) ((ι → 𝔸f E) × (ι → 𝔸f E)) :=
  (intVectors (Ô E) ι).comap (.coprod 1 1) ⊓
    ((intVectors (Ô E) ι).comap (s.1.1 • .id)).prod ((intVectors (Ô E) ι).comap ((g * s).1 • .id))

/-- For the square of the Haar measure `latticeMeasure E ι`, which gives Ô^ι mass one, the pairs
`(x, y)` in `Ô^ι × Ô^ι` that lie in `cocycleSubmodule g s` (that is, `x + y`, `s x` and `g s y` are
again in `Ô^ι`) have volume `(‖Δ s‖ ^ 2)⁻¹ * (‖Δ (g * s)‖ ^ 2)⁻¹`, with `Δ = finMultiplier`. -/
lemma measureReal_prod_inter_cocycleSubmodule (g s : Gf E ι) :
    ((latticeMeasure E ι).prod (latticeMeasure E ι)).real
        (((intVectors (Ô E) ι).prod (intVectors (Ô E) ι)).toAddSubgroup ∩
          (cocycleSubmodule g s).toAddSubgroup) =
      (‖finMultiplier s‖ ^ 2)⁻¹ * (‖finMultiplier (g * s)‖ ^ 2)⁻¹ := by
  -- On pairs of lattice vectors the condition on the sum is automatic, so the set is a product.
  have h_set : (SetLike.coe ((intVectors (Ô E) ι).prod (intVectors (Ô E) ι)).toAddSubgroup ∩
      (cocycleSubmodule g s).toAddSubgroup) =
      {x : ι → 𝔸f E | s.val.val *ᵥ x ∈ stdLattice E ι ∧ x ∈ stdLattice E ι} ×ˢ
        {y : ι → 𝔸f E | (g * s).val.val *ᵥ y ∈ stdLattice E ι ∧ y ∈ stdLattice E ι} :=
    Set.ext fun ⟨x, y⟩ ↦ ⟨fun ⟨⟨hx, hy⟩, _, hsx, hgsy⟩ ↦ ⟨⟨hsx, hx⟩, hgsy, hy⟩,
      fun ⟨⟨hsx, hx⟩, hgsy, hy⟩ ↦ ⟨⟨hx, hy⟩, add_mem hx hy, hsx, hgsy⟩⟩
  rw [h_set, measureReal_prod_prod, latticeMeasure_inter_eq_glMultiplier,
    latticeMeasure_inter_eq_glMultiplier, finMultiplier, finMultiplier]

/-- In the product of multipliers on the left of the Gauss sum identity
`New.stdLattice.exists_gauss_sum_finProjAction`, the volume factors
`(‖Δ s‖ ^ 2)⁻¹ * (‖Δ (g * s)‖ ^ 2)⁻¹` cancel against `Δ x * Δ x⁻¹ = ‖Δ x‖ ^ 2` for `x = s` and
`x = g * s`, with `Δ = finMultiplier`: only `Δ g` and the factor `z` remain. -/
lemma finMultiplier_mul_smul_mul_eq (g s : Gf E ι) (z : ℂ) :
    finMultiplier g * finMultiplier s * finMultiplier (g * s)⁻¹ *
        (((‖finMultiplier s‖ ^ 2)⁻¹ * (‖finMultiplier (g * s)‖ ^ 2)⁻¹ : ℝ) • z) *
          finMultiplier s⁻¹ * finMultiplier (g * s) = z * finMultiplier g := by
  have h_sq (x : Gf E ι) :
      ((‖finMultiplier x‖ : ℝ) : ℂ) ^ 2 = finMultiplier x⁻¹ * finMultiplier x := by
    rw [finMultiplier_inv, Complex.conj_mul']
  push_cast [Complex.real_smul, h_sq]
  field_simp [finMultiplier_ne_zero]

/-- The cocycle as a finite Gauss sum. For `g`, `s` in the finite unitary group there are a finite
module `Q` over the ring `Ô E` of integral finite adeles, in the larger of the universes `u_1` of
`E` and `u_2` of `ι`, and a function `γ` from `Q` to the finite adeles with the following
properties. Take the cocycle `c = finProjAction.1` of the matrix action of `Gf E ι` on the finite
Heisenberg datum, the multiplier `Δ = finMultiplier` (`glMultiplier` of the underlying invertible
matrix) and the character `ψ₀ = selfDualAddChar E`, z ↦ ψ_f(ȷαᾱz). Then (a)
`c g s * Δ s⁻¹ * Δ (g * s)` is the sum of `ψ₀ (γ q)` over `Q` times `Δ g`; and for all `t` in `Ô E`
and `q` in `Q`, (b) `γ (t • q)` and `star t * t * γ q` have the same value under `ψ₀`, and (c)
`t • q = 0` if the matrix `t • s⁻¹` has entries in `Ô E`. -/
lemma exists_gauss_sum_finProjAction (g s : Gf E ι) :
    ∃ (Q : ModuleCat.{max u_1 u_2} (Ô E)) (_ : Fintype Q) (γ : Q → 𝔸f E),
      -- (a) the cocycle is a sum over the finite module `Q`, up to values of `finMultiplier`
      finProjAction.1 g s * finMultiplier s⁻¹ * finMultiplier (g * s) =
        (∑ q : Q, selfDualAddChar E (γ q)) * finMultiplier g ∧
      ∀ (t : Ô E) (q : Q),
        -- (b) `γ` is hermitian-quadratic modulo the kernel of `selfDualAddChar E`
        selfDualAddChar E (γ (t • q)) = selfDualAddChar E (star (t : 𝔸f E) * t * γ q) ∧
        -- (c) `t` kills `Q` when `t • s⁻¹` is integral
        ((t : 𝔸f E) • ((s⁻¹ : Gf E ι) : Matrix ι ι (𝔸f E)) ∈ (Ô E).matrix → t • q = 0) := by
  -- The integrand is `ψ₀ ∘ F` on the compact module `M`, where it is constant on the cosets of
  -- `M ∩ (L × L)`, so the cocycle is a sum over the finite quotient `Q = M / (M ∩ (L × L))`.
  classical
  let L : Submodule (Ô E) (ι → 𝔸f E) := intVectors (Ô E) ι
  let M : Submodule (Ô E) ((ι → 𝔸f E) × (ι → 𝔸f E)) := cocycleSubmodule g s
  let F (p : (ι → 𝔸f E) × (ι → 𝔸f E)) : 𝔸f E := star traceOneAdele * star p.2 ⬝ᵥ p.1
  have hM : IsCompact (SetLike.coe M.toAddSubgroup) :=
    ((isCompact_stdLattice.preimage_smul s.1).prod (isCompact_stdLattice.preimage_smul (g * s).1))
      |>.inter_left (isCompact_stdLattice.isClosed.preimage continuous_add)
  have hL : IsOpen (SetLike.coe (L.prod L).toAddSubgroup) :=
    isOpen_stdLattice.prod isOpen_stdLattice
  have h_fin : Fintype (M.toAddSubgroup ⧸ (L.prod L).toAddSubgroup.addSubgroupOf M.toAddSubgroup) :=
    AddSubgroup.fintypeOfIndexNeZero (hM.relIndex_ne_zero_add hL)
  have h_integrand (x y : ι → 𝔸f E) : (SetLike.coe M.toAddSubgroup).indicator
    (selfDualAddChar E ∘ F) (x, y) =
      finVac (s • x) * finVac ((g * s) • y) * (finHeisenberg E ι).β x y * finVac (x + y) := by
    rw [cocycleIntegrand_eq, indicator_apply]
    congr 1
  -- Invariance: for `x`, `y` in `M` with `y - x` in `L × L`, the difference `F y - F x` is
  -- integral.
  have h_inv (x y : M.toAddSubgroup) (h : -x.1 + y ∈ (L.prod L).toAddSubgroup) :
      (selfDualAddChar E ∘ F) y = (selfDualAddChar E ∘ F) x := by
    obtain ⟨⟨x₁, x₂⟩, hx_sum, hx₁, hx₂⟩ := x
    obtain ⟨⟨y₁, y₂⟩, hy_sum, hy₁, hy₂⟩ := y
    obtain ⟨hd₁, hd₂⟩ := h
    exact selfDualAddChar_traceOne_dot_congr g s hx_sum hy_sum hx₁ hy₁ hx₂ hy₂ hd₁ hd₂
  refine ⟨.of _ (M ⧸ submoduleOf (L.prod L) M), h_fin, fun q ↦ F q.out, ?_, fun t q ↦ ⟨?_, ?_⟩⟩
  · let ν : Measure ((ι → 𝔸f E) × (ι → 𝔸f E)) := (latticeMeasure E ι).prod (latticeMeasure E ι)
    have h_int : IntegrableOn (selfDualAddChar E ∘ F) M.toAddSubgroup ν :=
      hM.integrableOn _ (continuous_selfDualAddChar.comp (by fun_prop))
    -- The double integral is the integral of `selfDualAddChar E ∘ F` over `M`, so a volume times a
    -- sum.
    simp_rw [finProjAction, ← h_integrand]
    have h_double :
        ∫ x : ι → 𝔸f E, ∫ y : ι → 𝔸f E, (SetLike.coe M.toAddSubgroup).indicator
          (selfDualAddChar E ∘ F) (x, y)
            ∂latticeMeasure E ι ∂latticeMeasure E ι =
          ν.real ((L.prod L).toAddSubgroup ∩ M.toAddSubgroup) •
            ∑ q : M.toAddSubgroup ⧸ (L.prod L).toAddSubgroup.addSubgroupOf M.toAddSubgroup,
              selfDualAddChar E (F q.out.1) := by
      rw [← integral_prod _ (h_int.integrable_indicator hM.measurableSet),
        integral_indicator hM.measurableSet, setIntegral_eq_finsum hM hL h_inv,
        finsum_eq_sum_of_fintype]
      rfl
    rw [h_double, measureReal_prod_inter_cocycleSubmodule g s]
    -- The sum over `Q` is by definition the sum over the quotient of additive groups.
    exact finMultiplier_mul_smul_mul_eq g s _
  · -- `t • q.out` represents `t • q`, and `F` is sesquilinear.
    refine (h_inv (t • q.out) (t • q).out
      ((Submodule.Quotient.eq' (submoduleOf (L.prod L) M)).1 (by simp))).trans ?_
    have h_sesq (p : (ι → 𝔸f E) × (ι → 𝔸f E)) : F (t • p) = star t.val * t * F p := by
      simp [F, Subring.smul_def]
      ring
    exact congrArg (selfDualAddChar E) (h_sesq q.out.1)
  · -- For `(x₁, x₂)` in `M`, `t • x₁ = (t • s⁻¹) (s x₁)` and `t • (x₁ + x₂)` lie in `L`.
    refine q.inductionOn fun x ht ↦ ?_
    have h_sx : s.val.val *ᵥ x.1.1 ∈ stdLattice E ι := x.2.2.1
    have h_fst : (t • x).1.1 ∈ L := by simpa [smul_mulVec] using! IsIntMatrix.mulVec ht h_sx
    have h_sum : (t • x).1.1 + (t • x).1.2 ∈ L := (t • x).property.1
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨h_fst, (add_mem_cancel_left h_fst).1 h_sum⟩

end FiniteCocycle

/-!
## Triviality of the finite cocycle

* `New.stdLattice.finProjAction_cocycle_eq_one_of_mem`: the cocycle at `(g, s)` is `1` when `s` lies
  in the stabiliser `New.stdLevel` of the standard lattice.

The `s` at which the cocycle is `1` for all `g` form a subgroup,
`New.Heisenberg.IsVacuum.cocycleRadical`. It contains `New.stdLevel`, so only `s` supported on one
pair of conjugate places remain. The cocycle has absolute value `1`, and
`New.stdLattice.exists_gauss_sum_finProjAction` turns it into a Gauss sum. At a split place `w`,
where one may assume `s⁻¹` integral at `w`, all terms of this sum are `1`. At a place fixed by
conjugation `New.eq_one_of_apply_apply_eq_neg` fixes the sign.
-/

section FiniteCocycleTrivial

open Complex NumberField Gf ComplexOrder WeilData AddChar Weil Heisenberg IsVacuum

variable {E ι : Type*} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [WeilData E]

/-- The finite cocycle is `1` at `(g, s)` when `s` lies in the stabiliser `New.stdLevel` of the
standard lattice. -/
lemma finProjAction_cocycle_eq_one_of_mem ⦃s : Gf E ι⦄ (hs : s ∈ stdLevel E ι) (g : Gf E ι) :
    finProjAction.1 g s = 1 := by
  -- As `s⁻¹` is integral, `1` kills the module `Q` of the Gauss sum: the sum is its one term `1`.
  obtain ⟨Q, _, γ, h_sum, h_smul⟩ := exists_gauss_sum_finProjAction g s
  have h_zero (q : Q) : q = 0 := by
    simpa using (h_smul 1 q).2 (by simpa using! hs.isIntMatrix_inv)
  have h_gauss : ∑ q : Q, selfDualAddChar E (γ q) = 1 := by
    rw [Fintype.sum_eq_single 0 fun q hq ↦ absurd (h_zero q) hq]
    simpa using (h_smul 0 0).1
  have h_mul : finMultiplier (g * s) = finMultiplier g := by
    simpa [finMultiplier] using glMultiplier_mul_of_mem g.val (one_mem _) hs
  simpa [h_gauss, h_mul, finMultiplier_eq_one_of_mem (inv_mem hs), finMultiplier_ne_zero] using
    h_sum

/-- The finite cocycle has absolute value one, as the operators of the action are isometries. -/
lemma norm_cocycle_eq_one (g s : Gf E ι) : ‖finProjAction.1 g s‖ = 1 := by
  -- The product of the operators of `(g * s)⁻¹`, `g` and `s` is the scalar `finProjAction.1 g s`
  -- (`weilOp_inv_mul_weilOp_mul_weilOp`), and each preserves `modelInner`; apply it to the vacuum,
  -- a unit vector.
  let A := (finProjAction (E := E) (ι := ι)).2
  let v : Model (finHeisenberg E ι) := isVacuum_finVac.vacElem
  have h_isometry (x : Gf E ι) (f : Model (finHeisenberg E ι)) :
      modelInner (weilOp A x f) (weilOp A x f) = modelInner f f :=
    modelInner_weilOp A x f f (finProjAction_cocycle_eq_one_of_mem (one_mem _) x)
  have h_triple :
      weilOp A (g * s)⁻¹ (weilOp A g (weilOp A s v)) = finProjAction.1 g s • v :=
    DFunLike.congr_fun (weilOp_inv_mul_weilOp_mul_weilOp A g s) v
  have h_unit : modelInner v v = 1 := (modelInner_vacElem ..).trans isVacuum_finVac.apply_zero
  have h_inner : modelInner (finProjAction.1 g s • v) (finProjAction.1 g s • v) = 1 := by
    rw [← h_triple, h_isometry, h_isometry, h_isometry, h_unit]
  have h_sq : ((‖finProjAction.1 g s‖ : ℝ) : ℂ) ^ 2 = 1 := by
    simpa [h_unit, ← Complex.mul_conj', mul_comm] using h_inner
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (mod_cast h_sq)

/-- For `a`, `s` supported on a split place `w` and its conjugate, `Δ a / Δ (a * s) / Δ s⁻¹` is
nonnegative, that is real and `≥ 0` in `ComplexOrder`, with `Δ = finMultiplier`: the phase of
`Δ x` is a character of the determinant of `x` at `w`. -/
lemma finMultiplier_div_nonneg_of_isSplit {w : FinPlace E} (hw : w.IsSplit) {a s : Gf E ι}
    (ha : a ∈ supportedOn ι {w}) (hs : s ∈ supportedOn ι {w}) :
    0 ≤ finMultiplier a / finMultiplier (a * s) / finMultiplier s⁻¹ := by
  let cut (x : Gf E ι) : GL ι (𝔸f E) := cutGL (idem_mul_self {w}) x.val
  have h_eq {x : Gf E ι} (hx : x ∈ supportedOn ι {w}) :
      finMultiplier x = ‖glMultiplier (cut x)‖ ^ 2 * starRingEnd ℂ (chiFin (cut x).det) :=
    finMultiplier_eq_of_supportedOn (by simp [hw]) hx
  have h_phase : chiFin (cut (a * s)).det * chiFin (cut s⁻¹).det = chiFin (cut a).det := by
    rw [← map_mul, ← map_mul, show cut (a * s) * cut s⁻¹ = cut a by simp [cut]]
  have h_ne (x : Gf E ι) : starRingEnd ℂ (chiFin (cut x).det) ≠ 0 :=
    star_ne_zero.2 (chiFin.toHomUnits _).ne_zero
  -- By `h_phase` the characters cancel, and squares of absolute values are left.
  rw [h_eq ha, h_eq (mul_mem ha hs), h_eq (inv_mem hs), ← h_phase, map_mul]
  field_simp [h_ne]
  positivity

/-- Let `x` be an element of the finite adelic unitary group `Gf E ι` (matrices g over the finite
adeles with gᴴg = 1) supported on an inert place `w`: `w` is fixed by conjugation, and `x` has
component 1 at every other place. If the residue field of `w` has `w.q = r ^ 2` elements, then the
multiplier Δ_f(x) (`New.finMultiplier`) is a power of `-r`, as the splitting character `υ` of the
Weil data is `-1` at the uniformiser. -/
lemma exists_finMultiplier_eq_neg_pow {w : FinPlace E} (hw : star w = w) {r : ℕ}
    (hr : r ^ 2 = w.q) {x : Gf E ι} (hx : x ∈ supportedOn ι {w}) :
    ∃ n : ℕ, finMultiplier x = (-(r : ℂ)) ^ n := by
  have h_away (u : FinPlace E) (hu : u ≠ w) : x.val.map (evalAt u) = 1 :=
    mem_supportedOn.1 hx u hu fun h_star ↦ hu (star_injective (h_star.trans hw.symm))
  obtain ⟨n, h_pow⟩ : ∃ n : ℕ, glMultiplier x.val = (υ.atUniformizer w * √w.q) ^ n :=
    ⟨_, glMultiplier_eq_pow_of_local h_away ((saturatingElem x.val).property.map_evalAt w)⟩
  have h_unif : υ.atUniformizer w * √w.q = -(r : ℂ) := by simp [υ_inert, hw, ← hr]
  exact ⟨n, by rw [finMultiplier, h_pow, h_unif]⟩

/-- Let `w = star w` be an inert place with `w.q = r ^ 2` residue field elements, `r ≡ 3` modulo
`4`. Let `Q` be a finite `Ô E`-module killed by `idem (star {w})ᶜ`, the idempotent that is `1` off
`w = star w` and `0` at it. Let `γ` be hermitian-quadratic modulo the kernel of the character
`selfDualAddChar E`. If `‖c‖ = 1` and `c * (-r) ^ k` is the Gauss sum of `γ` times `(-r) ^ m`,
then `c = 1`. -/
lemma eq_one_of_gauss_sum_of_inert {w : FinPlace E} (hw : star w = w) {Q : Type*}
    [AddCommGroup Q] [Module (Ô E) Q] [Fintype Q] {γ : Q → 𝔸f E}
    (h_smul : ∀ (t : Ô E) (q : Q),
      selfDualAddChar E (γ (t • q)) = selfDualAddChar E (star (t : 𝔸f E) * t * γ q))
    (h_kill : ∀ q : Q, (⟨idem (star {w})ᶜ, idem_mem_Ô (star {w})ᶜ⟩ : Ô E) • q = 0)
    {r : ℕ} (hr_sq : r ^ 2 = w.q) (hr_mod : r % 4 = 3) {k m : ℕ} {c : ℂ} (hc : ‖c‖ = 1)
    (h_eq : c * (-(r : ℂ)) ^ k = (∑ q : Q, selfDualAddChar E (γ q)) * (-(r : ℂ)) ^ m) :
    c = 1 := by
  -- The sum is real: scaling by `normNegOne`, a unit of norm `-1`, permutes `Q` and conjugates the
  -- terms.
  have h_real : star (∑ q : Q, selfDualAddChar E (γ q)) = ∑ q : Q, selfDualAddChar E (γ q) := by
    simpa [h_smul, map_neg_eq_inv, inv_eq_conj, norm_selfDualAddChar, star_normNegOne_mul_self]
      using
      (normNegOne (E := E)).isUnit.smul_bijective.sum_comp (selfDualAddChar E ∘ γ)
  -- `Q` has no `2`-torsion: `t - 2` is `-2` at `w`, `-1` elsewhere, and `w.q = r ^ 2` is odd.
  let t : Ô E := ⟨idem (star {w})ᶜ, idem_mem_Ô _⟩
  have h_unit : IsUnit (t - 1 - 1) := by
    have h_odd : Odd w.q := hr_sq.subst (Odd.pow (Nat.odd_iff.2 (by omega)))
    have h_two : (2 : 𝓞 E) ∉ w.asIdeal :=
      w.isPrime.notMem_of_isCoprime_of_mem h_odd.coprime_two_right.cast w.asIdeal.absNorm_mem
    refine isUnit_Ô.2 fun u ↦ ?_
    obtain rfl | hu := eq_or_ne w u
    · have h_val : Valued.v (2 : LocField w) = 1 := by
        simpa [map_ofNat] using v_algebraMap_eq_one h_two
      norm_num [t, hw, h_val]
    · norm_num [t, star_injective.eq_iff' hw, hu.symm]
  have h_tors (q : Q) (hq : -q = q) : q = 0 :=
    h_unit.smul_eq_zero.1 (by simpa [t, h_kill, sub_smul, sub_eq_zero] using hq)
  -- Multiplication by `i` has square `-1` and norm `1`, so it preserves the terms of the sum. Its
  -- orbits off `0` have four points, so `eq_one_of_apply_apply_eq_neg` applies.
  obtain ⟨i, -, hi_sq, hi_star, -⟩ :=
    HasPrimitiveRoot5040.exists_mul_self_eq_neg_one_and_mul_star_eq_two (E := E)
  let rot (q : Q) : Q := algebraMap (𝓞 E) (Ô E) i • q
  have h_rot_term (q : Q) : selfDualAddChar E (γ (rot q)) = selfDualAddChar E (γ q) := by
    simp [rot, h_smul, ← map_mul, ← coe_star_ringOfIntegers, hi_sq, hi_star]
  have h_rot_sq (q : Q) : rot (rot q) = -q := by simp [rot, ← map_mul, smul_smul, hi_sq]
  have h_mod : (-r : ℤ) ≡ 1 [ZMOD 4] := by grind [Int.ModEq]
  exact eq_one_of_apply_apply_eq_neg (F := fun q : Q ↦ selfDualAddChar E (γ q)) h_tors h_rot_sq
    h_rot_term
    (fun _ ↦ isOfFinOrder_ψf _) (by simpa using h_smul 0 0) h_real h_mod hc (by simpa using h_eq)

/-- **The finite cocycle is trivial**: `finProjAction.1 g s = 1` for all `g`, `s` in the finite
unitary group. It is stated as membership of `s` in `New.Heisenberg.IsVacuum.cocycleRadical` for the
action `New.stdLattice.finProjAction`, the subgroup of the `s` with `finProjAction.1 g s = 1` for
every `g`, so that the proof may argue on generators. Forming that subgroup needs
`finProjAction.1 g 1 = 1` for all `g`. This follows from
`New.stdLattice.finProjAction_cocycle_eq_one_of_mem`, since `1` lies in `New.stdLevel`.

A special case of the splitting of the Weil representation over unitary groups (Kudla) at the finite
places, for one explicit normalisation on the finite vacuum. -/
lemma mem_cocycleRadical ⦃s : Gf E ι⦄ :
    s ∈ cocycleRadical finProjAction.2 (finProjAction_cocycle_eq_one_of_mem (by simp)) := by
  -- A subgroup that contains `stdLevel E ι` and, for every `w`, the elements supported on `w` and
  -- `star w` is the whole group. For such `s` the cocycle has absolute value `1`, and its phase
  -- is read off the Gauss sum `exists_gauss_sum_finProjAction`.
  refine s.mem_of_stdLevel_le_of_supportedOn_le finProjAction_cocycle_eq_one_of_mem fun w s hs ↦ ?_
  -- At a split place we may assume `s⁻¹` integral at `w`: with `u` and `s⁻¹ u` integral at `w` and
  -- `b = ofSplitPlace hw u⁻¹`, both `b` and `b * s` are of this kind.
  wlog! h_int : w.IsSplit → (s⁻¹.atPlace w).1 ∈ (LocInt w).matrix generalizing s with h_gen
  · obtain ⟨hw, -⟩ := h_int
    obtain ⟨u, hu, hsu, -⟩ : ∃ u : GL ι (LocField w),
        IsSaturating (LocInt w).matrix (s⁻¹.atPlace w) u :=
      ⟨_, (saturatingElem s⁻¹.val).property.map_evalAt w⟩
    have hb : ofSplitPlace hw u⁻¹ ∈ supportedOn ι {w} := ofSplitPlace_mem_supportedOn hw u⁻¹
    exact (mul_mem_cancel_left (h_gen _ hb fun _ ↦ by simpa [hw] using hu)).1
      (h_gen _ (mul_mem hb hs) fun _ ↦ by simpa [hw] using hsu)
  intro g
  obtain ⟨Q, _, γ, h_sum, h_smul⟩ := exists_gauss_sum_finProjAction g s
  -- Write `g = a * b` with `a` on `w`, `star w` and `b` off them; the factor `finMultiplier b`
  -- cancels.
  obtain ⟨a, ha, b, hb, rfl, -⟩ := g.exists_supportedOn_mul_trivialOn {w}
  have h_mul (x : Gf E ι) (hx : x ∈ supportedOn ι {w}) :
      finMultiplier (x * b) = finMultiplier x * finMultiplier b :=
    glMultiplier_mul_of_map_evalAt_eq_one (atPlace_eq_one_or hx hb)
  replace h_sum : finProjAction.1 (a * b) s * finMultiplier s⁻¹ * finMultiplier (a * s) =
      (∑ q : Q, selfDualAddChar E (γ q)) * finMultiplier a := by
    simpa [← (commute_supportedOn_trivialOn hs hb).right_comm, h_mul, ha, hs, mul_mem, field,
      finMultiplier_ne_zero] using h_sum
  -- `Q` lives at `star w`: `s⁻¹` is integral at all other places, so their idempotent kills `Q`.
  let t : Ô E := ⟨idem (star {w})ᶜ, idem_mem_Ô _⟩
  have h_kill (q : Q) : t • q = 0 := by
    refine (h_smul t q).2 fun i j ↦ idem_mul_mem_Ô.2 fun u hu ↦ ?_
    suffices h_entries : (s⁻¹.atPlace u).1 ∈ (LocInt u).matrix from h_entries i j
    obtain rfl | huw := eq_or_ne u w
    · exact h_int (by simpa using hu)
    · simp [mem_supportedOn.1 hs _ huw hu]
  by_cases! hw : w.IsSplit
  · -- Split place: `1 - t` acts as the identity and has norm `0`, so every term of the sum is `1`.
    have h_idem : (1 - star t.1) * (1 - t) = 0 := by
      ext1 u
      by_cases hu : u = w <;> simp [t, star_idem, hu, hw]
    have h_one (q : Q) : selfDualAddChar E (γ q) = 1 := by
      simpa [sub_smul, h_kill, h_idem] using (h_smul (1 - t) q).1
    -- The phases of `finMultiplier a` and of `finMultiplier s⁻¹ * finMultiplier (a * s)` cancel.
    have h_quot : finProjAction.1 (a * b) s =
        Fintype.card Q * (finMultiplier a / finMultiplier (a * s) / finMultiplier s⁻¹) := by
      simpa [h_one, field, finMultiplier_ne_zero, mul_right_comm] using h_sum
    have h_nonneg : 0 ≤ finProjAction.1 (a * b) s :=
      (mul_nonneg (Nat.cast_nonneg _) (finMultiplier_div_nonneg_of_isSplit hw ha hs)).trans_eq
        h_quot.symm
    exact (eq_coe_norm_of_nonneg h_nonneg).trans (mod_cast norm_cocycle_eq_one (a * b) s)
  -- Inert place: `w.q = r ^ 2` with `-r ≡ 1` modulo `4`, and the multipliers are powers of `-r`.
  obtain ⟨r, hr_sq, hr_mod⟩ := HasPrimitiveRoot5040.exists_sq_eq_q_of_inert (w := w) hw
  obtain ⟨k₁, hk₁⟩ := exists_finMultiplier_eq_neg_pow hw hr_sq (inv_mem hs)
  obtain ⟨k₂, hk₂⟩ := exists_finMultiplier_eq_neg_pow hw hr_sq (mul_mem ha hs)
  obtain ⟨m, hm⟩ := exists_finMultiplier_eq_neg_pow hw hr_sq ha
  rw [hk₁, hk₂, hm, mul_assoc, ← pow_add] at h_sum
  exact eq_one_of_gauss_sum_of_inert hw (fun t q ↦ (h_smul t q).1) h_kill hr_sq hr_mod
    (norm_cocycle_eq_one (a * b) s) h_sum

/-- The matrix action of the finite adelic unitary group on the finite Heisenberg datum with
multiplier `New.finMultiplier`, together with the fact that its cocycle is identically 1. -/
def _root_.New.finAction : (finHeisenberg E ι).MultiplierAction (latticeMeasure E ι) finVac
  (Gf E ι) :=
  { finProjAction.2 with cocycle g _ := mem_cocycleRadical g }

end FiniteCocycleTrivial

end New.stdLattice

end
