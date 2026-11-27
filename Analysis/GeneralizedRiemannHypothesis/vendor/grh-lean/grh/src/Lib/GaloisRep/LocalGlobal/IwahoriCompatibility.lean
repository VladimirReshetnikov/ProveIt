import Lib.GaloisRep.BaseChange.IwahoriEigenforms
import Lib.GaloisRep.Main.AllRanks
import Lib.LocalGL.Iwahori.SortedExponents
import Lib.LocalGL.Iwahori.SphericalExponents

/-!
# Local-global compatibility at split places for Iwahori eigencharacters and parahoric types

Let `r` be an `ℓ`-adic Galois representation attached to an eigenform on a definite unitary group
over a CM field `E`, and let `w` be a split place. Level information on the form at `w` gives
polynomials that kill geometric Frobenius and inertia elements under `r`, in the sense of
`New.GaloisRep.PolyKillsAt`. At pro-`p` Iwahori level, with eigencharacter `New.torusChar ξ`, the
characters `ξ i` are tamely ramified and, when sorted, give the roots of such polynomials. For `w`
not above `ℓ`, when a parahoric subgroup acts by scalars there are analogous polynomials for the
Frobenius and inertia matrices. For the stabiliser in `GL_N(𝒪_w)` of a line modulo `w`, the Hecke
operator of `diag (ϖ, 1, …, 1)` acts like Frobenius on the image of `T - 1`, for the matrix `T` of
an inertia element, in the sense of an identity between traces. Here `p` is the residue
characteristic of `w`.

## Main definitions and results

* `New.GaloisRep.Attached.local_global_of_eigencharacter`: the main result, for `ξ i` sorted by size
  at a uniformiser.
* `New.Patching.IsParahoricCompatible`: commuting matrices `F`, `T` are killed by polynomials read
  off given scalars and an exponent that is not zero on a given vector.
* `New.Patching.isParahoricCompatible_galRep`: the Frobenius and inertia matrices have this property
  for a non-zero pro-`p` Iwahori fixed form on which a parahoric subgroup acts by scalars that tell
  its blocks apart.
* `New.Patching.hecke_eq_frob_on_parahoricEigenspace`: for the stabiliser in `GL_N(𝒪_w)` of a line
  modulo `w`, acting by a scalar character that is not of order dividing `N !` at the unit, the
  Hecke operator of `diag (ϖ, 1, …, 1)` acts like Frobenius on the image of `T - 1`, with `T` the
  inertia matrix, in the sense of an identity between traces.

Notions from other files:
* `New.GaloisRep.PolyKillsAt r A s P`: `P (r s) = 0` if `ℓ` is a unit at `A`; above `ℓ`, for every
  Weil pair `(s, k)`, `r` is potentially crystalline and `P` kills `New.Period.linearFrob`.
* `New.IsFrob A q σ`: `σ` stabilises `A` and acts as `x ↦ x ^ q` on its residue field.
* `New.Patching.localFormRep V κ hw`: the representation of `GL_N(E_w)`, with `N` the cardinality
  of `n`, on the forms of weight `κ` on `V` at the split place `w`.
* `New.IsIwahoriEigen ρ ξ x`: `x ≠ 0` is fixed by the pro-`p` Iwahori subgroup, and
  `U_t x = ξ t • x` for dominant diagonal `t`.
* `New.torusChar θ`: the character `t ↦ ∏ i, θ i (t i) * |t i| ^ (N - 1 - i)` of the diagonal torus
  of `GL_N`.

## Relation to the literature

Known; see `Lib.GaloisRep.LocalGlobal.LabelCompatibility` for sources.
-/

/-!
## Compatibility for a sorted Iwahori eigencharacter

Let `f` be an eigenform on the standard definite unitary group over the CM field `E`, `r` an
`ℓ`-adic Galois representation attached to it (`New.GaloisRep.Attached`), `w` a split place and `A`
a place of `Ω` above `w`. Suppose that at `w` the form is an eigenvector at the pro-`p` Iwahori
level (`New.IsIwahoriEigen`) for the torus character `New.torusChar ξ`, that is
`t ↦ ∏ i, ξ i (t i) * |t i| ^ (N - 1 - i)` with `N` the cardinality of `n`.
-/

namespace New

open Polynomial Valued Subgroup WithZero QuotientGroup Period Patching Fintype ComplexOrder Ideal
  MonoidHom Set Finite Algebra QZChar Int

variable {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {E n : Type} [Field E] [CMType E]
  {w : FinPlace E} [Fintype n] [DecidableEq n]
  {κ : Weight E} {P : FinPlace E → ℂ[X]} {ξ : Fin (card n) → (LocField w)ˣ →* ℂˣ}
  {hw : Star.star w ≠ w} {f : (stdSpace E n).forms κ}

/-- Let `f` be a pro-`p` Iwahori eigenvector at `w` with eigencharacter `torusChar ξ`. Then the
absolute value and the characters `ξ i` are trivial on the `y` congruent to `1` modulo `w`. -/
lemma IsIwahoriEigen.apply_eq_one_of_principal_unit
    (hf_iwahori : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
    {y : (LocField w)ˣ} (hy : v (y.val - 1) < 1) :
    normAbsChar.prod (MonoidHom.pi ξ) y = 1 := by
  obtain ⟨hf_ne, hf_fixed, hU⟩ := hf_iwahori
  have hy_val : v y.val = 1 := by simpa using v.map_one_add_of_lt hy
  -- The diagonal matrix `t` with `y` at `i` is dominant and lies in the pro-`p` Iwahori subgroup,
  -- so `U_t` is the identity on `f` and its eigenvalue is `1`.
  have h_torus_one (i : Fin (card n)) : (torusChar ξ (Pi.mulSingle i y)).val = 1 := by
    have h_dom : Pi.mulSingle i y ∈ dominantTorus := by
      simp [dominantTorus, Monotone, apply_ite, hy_val, Pi.mulSingle_apply]
    have h_mem : diagGL (Pi.mulSingle i y) ∈ proIwahori :=
      diagGL_mem_proIwahori.2 fun j ↦ by rcases eq_or_ne j i with rfl | hj <;> simp [*]
    have h_smul : (torusChar ξ (Pi.mulSingle i y)).val • f = f := by
      rw [← hU _ h_dom, compactMean_apply h_mem, compactMean_eq_self _ hf_fixed]
    exact smul_left_injective ℂ hf_ne (h_smul.trans (one_smul ℂ f).symm)
  simpa [normAbsChar, hy_val, funext_iff] using h_torus_one

/-- Let `f` be a pro-`p` Iwahori eigenvector at `w` with eigencharacter `torusChar ξ`. Then the
absolute value and the characters `ξ i` kill the `(q - 1)`-th power of every local unit, where
`q = w.q` is the size of the residue field. -/
lemma IsIwahoriEigen.char_pow_q_sub_one_eq_one
    (hf_iwahori : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
    (y : (LocField w)ˣ) (hy : v y.val = 1) :
    normAbsChar.prod (MonoidHom.pi ξ) (y ^ (w.q - 1)) = 1 := by
  -- Fermat's little theorem in the residue field: `y ^ (w.q - 1)` is `1` modulo `w`,
  -- so `IsIwahoriEigen.apply_eq_one_of_principal_unit` applies to it.
  let a : (ResField w)ˣ :=
    .mk0 ⟦⟨y.val, hy.le⟩⟧ (mt residue_eq_iff_valuation_sub_lt_one.1 (by simp [hy]))
  have h_pow : (a : ResField w) ^ (w.q - 1) = 1 := by
    rw [← card_ResField]
    exact algebraMap_pow_card_pred_eq_one a
  exact hf_iwahori.apply_eq_one_of_principal_unit (residue_eq_iff_valuation_sub_lt_one.1 h_pow)

omit [PadicIso ℓ] [CMType E] in
/-- Let `s`, `φ` lie in the decomposition group of a place `A` above `w`, with `φ` a Frobenius. If
`∏ (X - a i)` kills `φ⁻¹`, with `a i ≠ 0`, and `∏ (X - α i * a i ^ m)` kills `s * φ⁻¹ ^ m` for all
`m > 0`, then `∏ (X - α i)` kills `s`. Here "kills" is `New.GaloisRep.PolyKillsAt` for `r`:
vanishing at the matrix away from `ℓ`, at the linear Frobenius above `ℓ`. -/
lemma GaloisRep.PolyKillsAt.of_mul_frob_pow [EmbeddedNumberField E] {r : GalRep ℓ E n}
    {A : ClosurePlace} {N : ℕ} {α a : Fin N → PadicAlgCl ℓ}
    {s φ : decompGroup Gal(Ω/E) A} (hA : IsPlaceOver A w) (hφ : IsFrob A w.q φ.val)
    (ha : ∀ i : Fin N, a i ≠ 0) (hφa : PolyKillsAt r A (φ⁻¹).val (∏ i : Fin N, (X - C (a i))))
    (hpow : ∀ m > (0 : ℕ),
      PolyKillsAt r A (s * φ⁻¹ ^ m).val (∏ i : Fin N, (X - C (α i * a i ^ m)))) :
    PolyKillsAt r A s.val (∏ i : Fin N, (X - C (α i))) := by
  -- Both clauses are `eval₂_prod_eq_zero_of_mul_pow`, the same statement for two elements of a
  -- ring: for the matrices `r s` and `r φ⁻¹` away from `ℓ`, and for `linearFrob` at `s` and at
  -- `φ⁻¹` above `ℓ`.
  refine ⟨fun hℓ ↦ ?_, ?_⟩
  · refine eval₂_prod_eq_zero_of_mul_pow (Algebra.commutes · (r s).val)
      (Algebra.commutes · (r φ⁻¹.val).val) (hφa.1 hℓ) ha fun m hm ↦ ?_
    change aeval ((r s).val * (r φ⁻¹.val).val ^ m) (∏ i : Fin N, (X - C (α i * a i ^ m))) = 0
    simpa using (hpow m hm).1 hℓ
  intro L _ d hs
  -- Above `ℓ` we have `w.q = ℓ ^ deg`, and `φ⁻¹` is a Weil element of degree `deg`.
  have hℓ_lt : A.valuation ℓ < 1 := by
    rw [show A = (intQpBar ℓ).comap L.e from L.inducesPlace.1.1.symm]
    exact valuation_comap_intQpBar_lt_one L.e
  obtain ⟨deg, hq, -⟩ := w.exists_q_eq_pow (hA.valuation_natCast_lt_one_iff.mp hℓ_lt)
  have hφW : IsWeilPair (L.toGp φ⁻¹) deg := by simpa [IsWeilPair, L.isFrob_iff, ← hq]
  obtain ⟨hpcr, hφ_kill⟩ := hφa.2 hφW
  refine ⟨hpcr, eval₂_prod_eq_zero_of_mul_pow (commute_coeffEnd_linearFrob hpcr hs)
    (commute_coeffEnd_linearFrob hpcr hφW) hφ_kill ha fun m hm ↦ ?_⟩
  -- `linearFrob` is multiplicative on Weil pairs.
  rw [← linearFrob_pow hpcr hφW, ← linearFrob_mul hpcr hs (hφW.pow m)]
  exact ((hpow m hm).2 (hs.mul (hφW.pow m))).2

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let the eigenform `f` for the system `P` of Hecke polynomials be a pro-`p` Iwahori eigenvector
at `w` with eigencharacter `torusChar ξ`. If the `ξ i` are unramified and `‖ξ i ϖ‖` is antitone in
`i` for a uniformiser `ϖ`, then some eigenform for the same system `P` is spherical at `w` with
Hecke roots `ξ i ϖ` (`New.HasHeckePolyAt`). -/
lemma IsIwahoriEigen.exists_hasHeckePolyAt
    (hf_iwahori : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
    [EmbeddedNumberField E] {ϖ : (LocField w)ˣ} (he : IsEigenform f.val P)
    (hϖ : v ϖ.val = WithZero.exp (-1))
    (hunr : ∀ y : (LocField w)ˣ, v y.val = 1 → ∀ i : Fin (card n), (ξ i y).val = 1)
    (hξ_antitone : Antitone fun i : Fin (card n) ↦ ‖(ξ i ϖ).val‖) :
    ∃ g : (stdSpace E n).forms κ,
      IsEigenform g.val P ∧
      HasHeckePolyAt g.val w hw (∏ i : Fin (card n), (X - C (ξ i ϖ).val)) := by
  -- `f` gives an exponent `(torusChar ξ, B u)` with `u` in the span of the translates of `f`, for
  -- an invariant scalar product `B`. The form is the mean `g` of `u` over `K = GL_N(𝒪_w)`: it is
  -- not zero by `IsExponent.eq_zero_of_eq_zero_on_spherical`, and Satake's formula
  -- `IsExponent.apply_partialHecke` gives its Hecke eigenvalues.
  let ρ : Rep.{0, 0, 0} ℂ (GL (Fin (card n)) (LocField w)) := localFormRep (stdSpace E n) κ hw
  obtain ⟨B, hB⟩ : ∃ B : ρ →ₗ⋆[ℂ] ρ →ₗ[ℂ] ℂ, IsUnitary ρ.ρ B := ⟨_, isUnitary_localFormRep⟩
  obtain ⟨u, hu_mem, hu_ne, hexp⟩ := hf_iwahori.exists_isExponent hB self_mem_cyclicSpan
  let K : Subgroup (GL (Fin (card n)) (LocField w)) := localIntGL (Fin (card n)) w
  let S : Submodule ℂ ρ := levelSpace ρ.ρ K
  let g : (stdSpace E n).forms κ := compactMean ρ.ρ K u
  have hg : g ∈ S := compactMean_mem_levelSpace u
  have B_g (y : ρ) (hy : y ∈ S) : B g y = B u y := by
    rw [hB.compactMean_adjoint, compactMean_eq_self y hy]
  have hg_ne : g ≠ 0 := fun hzero ↦ hu_ne <|
    hexp.eq_zero_of_eq_zero_on_spherical hϖ hunr hξ_antitone fun y hy ↦ by
      simp [← B_g y hy, hzero]
  -- The Hecke eigenvalues are `e_j (ξ i ϖ) / q ^ (j (j - 1) / 2)`, with `e_j` elementary symmetric.
  let roots : Multiset ℂ := List.ofFn fun i : Fin (card n) ↦ (ξ i ϖ).val
  let t (j : ℕ) : ℂ := roots.esymm j / w.q ^ j.choose 2
  refine ⟨g, he.of_mem_cyclicSpan (by simpa using compactMean_mem_cyclicSpan 1 hu_mem) hg_ne,
    hasHeckePolyAt_iff_localFormRep.mpr ⟨hg, t, ?_, fun j ↦ ?_⟩⟩
  · -- Vieta's formula
    rw [show ∏ i : Fin (card n), (X - C (ξ i ϖ).val) = (roots.map (X - C ·)).prod by
      simp [roots, List.map_ofFn, Fin.prod_ofFn, Function.comp_def],
      Multiset.prod_X_sub_X_eq_sum_esymm]
    simp [roots, t, heckePoly, mul_div_cancel₀, mul_assoc]
  -- Let `T` be the `j`-th Hecke operator and `T'` its adjoint, which commutes with `T` on spherical
  -- vectors. Satake's formula says that `B g (T y) = t j * B g y` for spherical `y`.
  let T : Module.End ℂ ρ := heckeGL ρ.ρ j
  let c : GL (Fin (card n)) (LocField w) → ℂ := (basicDoubleCoset (Fin (card n)) w j).indicator 1
  let T' : Module.End ℂ ρ := heckeFun ρ.ρ K fun a ↦ starRingEnd ℂ (c a⁻¹)
  have hbi : IsHeckeFunction K c := isHeckeFunction_basicDoubleCoset j
  have hbi' : IsHeckeFunction K _ := (hbi.heckeFun_adjoint B hg hB.2 hg).1
  have adjoint (y : ρ) (hy : y ∈ S) : B (T g) y = B g (T' y) :=
    (hbi.heckeFun_adjoint B hg hB.2 hy).2
  have satake (y : ρ) (hy : y ∈ S) : B g (T y) = t j * B g y := by
    rw [B_g (T y) (hbi.heckeFun_mem hy), B_g y hy,
      show T = partialHecke ρ.ρ 0 j from partialHecke_zero_eq_heckeGL.symm]
    exact hexp.apply_partialHecke hϖ hy bot_le j
  have normal : B (T g) (T g) = t j * B (T g) g := by
    rw [adjoint (T g) (hbi.heckeFun_mem hg), adjoint _ hg, ← satake (T' g) (hbi'.heckeFun_mem hg)]
    exact congrArg _ (hbi.heckeFun_comm hbi' hg).symm
  -- Hence `T g - t j • g` is orthogonal to `T g` and to `g`, so to itself.
  by_contra hne
  refine (hB.1 _ (sub_ne_zero.mpr hne)).ne' ?_
  change B (T g - t j • g) (T g - t j • g) = 0
  simp [normal, satake g hg]

/-- Let `f` be a pro-`p` Iwahori eigenvector at `w` with eigencharacter `torusChar ξ`. If
`‖ξ i (uniformizer w)‖` is antitone in `i`, so is `‖ξ i x‖` for `x` of order `k ≥ 0`. -/
lemma IsIwahoriEigen.antitone_norm
    (hf_iwahori : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
    [EmbeddedNumberField E]
    (hξ_antitone : Antitone fun i : Fin (card n) ↦ ‖(ξ i (uniformizer w)).val‖)
    {x : (LocField w)ˣ} {k : ℕ} (hx_val : v x.val = WithZero.exp (-k : ℤ)) :
    Antitone fun i : Fin (card n) ↦ ‖(ξ i x).val‖ := by
  intro i j hij
  -- `x / uniformizer w ^ k` is a unit, so `ξ i` kills its `(q - 1)`-th power.
  have h_unit : v (x / uniformizer w ^ k).val = 1 := by simp [hx_val]
  have h_killed : MonoidHom.pi ξ ((x / uniformizer w ^ k) ^ (w.q - 1)) = 1 :=
    congrArg Prod.snd (hf_iwahori.char_pow_q_sub_one_eq_one _ h_unit)
  have pow_eq : ∀ i : Fin (card n),
      (ξ i x).val ^ (w.q - 1) = (ξ i (uniformizer w)).val ^ (k * (w.q - 1)) := by
    simpa [div_pow, div_eq_iff, ← pow_mul, funext_iff, Units.ext_iff] using h_killed
  refine le_of_pow_le_pow_left₀ w.q_sub_one_pos.ne' (norm_nonneg _) ?_
  simpa [← norm_pow, pow_eq] using pow_le_pow_left₀ (norm_nonneg _) (hξ_antitone hij) _

/-- Let `f` be a pro-`p` Iwahori eigenvector at `w` with eigencharacter `torusChar ξ`. If `x` has
order `k > 0`, the `y` with `(|y|, ξ y)` a power of `(|x|, ξ x)` form a subgroup of finite index. -/
lemma IsIwahoriEigen.finiteIndex_comap_zpowers
    (hf_iwahori : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
    [EmbeddedNumberField E] {x : (LocField w)ˣ} {k : ℕ}
    (hx_val : v x.val = WithZero.exp (-k : ℤ)) (hk : 0 < k) :
    ((zpowers (normAbsChar.prod (MonoidHom.pi ξ) x)).comap
      (normAbsChar.prod (MonoidHom.pi ξ))).FiniteIndex := by
  -- The subgroup contains the `k * (q - 1)`-th powers, which have finite index.
  have : NeZero (k * (w.q - 1)) := ⟨(mul_pos hk w.q_sub_one_pos).ne'⟩
  have : (powMonoidHom (α := (LocField w)ˣ) (k * (w.q - 1))).range.FiniteIndex :=
    ⟨(index_pow_local_le _ w).1⟩
  refine finiteIndex_of_le (H := (powMonoidHom (k * (w.q - 1))).range)
    (range_subset_iff.mpr fun y ↦ ⟨-(v y.val).log * (w.q - 1), ?_⟩)
  -- `x ^ (v y).log * y ^ k` is a unit, so its `(q - 1)`-th power is killed.
  have hunit : v (x ^ (v y.val).log * y ^ k).val = 1 := by
    rw [← exp_log (x := v (x ^ (v y.val).log * y ^ k).val) (v.ne_zero_iff.2 (Units.ne_zero _))]
    simp [hx_val, mul_comm]
  simpa [mul_zpow, zpow_mul, ← zpow_natCast, inv_eq_iff_mul_eq_one] using
    hf_iwahori.char_pow_q_sub_one_eq_one _ hunit

/-- Let `f` be a pro-`p` Iwahori eigenvector at `w` with eigencharacter `torusChar ξ`, and let `A`
be a place above `w`. If `y / x` is a unit and `x`, `y` have the same local Artin symbol at `A`,
then the absolute value and the `ξ i` agree at `x` and `y`. -/
lemma IsIwahoriEigen.eq_of_localArtin_eq
    (hf_iwahori : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
    [EmbeddedNumberField E] {A : ClosurePlace} (hA : IsPlaceOver A w) {x y : (LocField w)ˣ}
    (hunit : v (y / x).val = 1) (hart : localArtin Gal(Ω/E) A w y = localArtin Gal(Ω/E) A w x) :
    normAbsChar.prod (MonoidHom.pi ξ) y = normAbsChar.prod (MonoidHom.pi ξ) x := by
  -- Take a uniformiser `π` in `E` and `z` with `z ^ (q - 1) = π`. The symbol of the unit `y / x` is
  -- trivial, so by the tame symbol `y / x` is congruent to `z / z = 1`.
  obtain ⟨π, hπ, -⟩ := hA.exists_uniformiser Gal(Ω/E)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω π) w.q_sub_one_pos
  have hz_ne : z ≠ 0 := ne_zero_pow w.q_sub_one_pos.ne' (by simp [hz])
  have h_symb : localArtin Gal(Ω/E) A w (y / x) = 1 := (div_mem_ker_iff _).mpr hart
  have h_one : v ((y / x).val - 1) < 1 := by
    simpa [hz_ne] using
      hA.valuation_sub_lt_one_iff_of_localArtin_eq (s := 1) (x := 1) (hA.isUniformiser_iff.mpr hπ)
        hunit h_symb hz
  exact (div_mem_ker_iff _).mp (hf_iwahori.apply_eq_one_of_principal_unit h_one)

omit [DecidableEq n] in
/-- Let `ξ i` be characters of the completion at `w` and let `x` have order `k`. If `(|y|, ξ y)` is
a power of `(|x|, ξ x)` for every `y`, then `x` is a uniformiser and the `ξ i` are unramified. -/
lemma IsIwahoriEigen.order_eq_one_and_unramified [EmbeddedNumberField E] {x : (LocField w)ˣ}
    {k : ℕ} (hx_val : v x.val = WithZero.exp (-k : ℤ))
    (hgen : ∀ y : (LocField w)ˣ,
      normAbsChar.prod (MonoidHom.pi ξ) y ∈ zpowers (normAbsChar.prod (MonoidHom.pi ξ) x)) :
    k = 1 ∧
    ∀ y : (LocField w)ˣ, v y.val = 1 → ∀ i : Fin (card n), (ξ i y).val = 1 := by
  -- Compare absolute values through the injectivity of `a ↦ q ^ a`.
  have hq_inj {a b : ℤ} : (w.q : ℂ) ^ a = w.q ^ b ↔ a = b :=
    (zpow_right_strictMono₀ (by simp : (1 : ℂ) < w.q)).injective.eq_iff
  have hpow (y : (LocField w)ˣ) :
      ∃ a : ℤ, -(k * a) = (v y.val).log ∧ ∀ i : Fin (card n), (ξ i x).val ^ a = ξ i y := by
    -- `zpow_neg` would move the sign out of the exponent that `hq_inj` compares.
    simpa [hx_val, -zpow_neg, hq_inj, mem_zpowers_iff, ← zpow_mul, Units.ext_iff,
      coe_normAbsChar_locField, norm_locField_eq_q_zpow, funext_iff] using hgen y
  obtain rfl : k = 1 := by
    obtain ⟨a, ha, -⟩ := hpow (uniformizer w)
    exact_mod_cast eq_one_of_dvd_one k.cast_nonneg ⟨a, by simpa [eq_comm] using ha⟩
  refine ⟨rfl, fun y hy i ↦ ?_⟩
  obtain ⟨a, ha, hξa⟩ := hpow y
  obtain rfl : a = 0 := by simpa [hy] using ha
  simp [← hξa]

variable [Nonempty n] [WeilData E]

/-- If a prime `p` divides the finite index of a subgroup `D` of a commutative group `G`, there is a
non-trivial character `χ` of `G` with values in `ℚ/ℤ` that is killed by `p` and trivial on `D`. -/
lemma exists_char_trivial_of_prime_dvd_index {G : Type} [CommGroup G] (D : Subgroup G)
    [D.FiniteIndex] {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ D.index) :
    ∃ (χ : G →* Multiplicative QZ) (x₀ : G),
      χ x₀ ≠ 1 ∧ (∀ y : G, χ y ^ p = 1) ∧ ∀ y ∈ D, χ y = 1 := by
  -- The dual of `G ⧸ D` has as many elements as `G ⧸ D`, so it has an element `ψ` of order `p`.
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ψ, hψ⟩ :=
    exists_prime_addOrderOf_dvd_card' (G := Additive (G ⧸ D) →+ QZ) p (by rwa [card_hom_QZ])
  obtain ⟨hψp, ⟨x₀⟩, hψ₀⟩ : (∀ a : G ⧸ D, p • ψ (Additive.ofMul a) = 0) ∧
      ∃ a : G ⧸ D, ψ (Additive.ofMul a) ≠ 0 := by
    simpa [addOrderOf_eq_prime_iff, DFunLike.ext_iff] using hψ
  refine ⟨ψ.toMultiplicativeRight.comp (mk' D), x₀, hψ₀, fun y ↦ hψp y, fun y hy ↦ ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, (eq_one_iff y).mpr hy, map_one]

/-- If a character `χ` of `G` is trivial on the subgroup `D` of finite index and on the image of
`N : G' →* G` but not at `x₀`, then the preimage of `D` under `N` has smaller index than `D`. -/
lemma index_comap_lt_of_char_ne_one {G G' M : Type*} [CommGroup G] [Group G'] [Group M]
    {D : Subgroup G} [D.FiniteIndex] {N : G' →* G} {χ : G →* M} {x₀ : G} (hχ₀ : χ x₀ ≠ 1)
    (hχD : ∀ y ∈ D, χ y = 1) (hχN : ∀ z : G', χ (N z) = 1) :
    (D.comap N).index < D.index := by
  -- The class of `x₀` modulo `D` is not in the image of `G'`.
  rw [← ker_mk' D, comap_ker, index_ker, ker_mk']
  refine card_subtype_lt (x := (x₀ : G ⧸ D)) fun ⟨z, hz⟩ ↦ hχ₀ ?_
  have h_mem : (N z)⁻¹ * x₀ ∈ D := QuotientGroup.eq.1 hz
  simpa [hχN] using hχD _ h_mem

/-- The unramified case of `New.GaloisRep.Attached.local_global_of_eigencharacter`. Let `r` be
attached to the Hecke polynomials `P` of the eigenform `f` on the standard space over the CM field
`E`, where `f` is a pro-`p` Iwahori eigenvector at the split place `w` for `torusChar ξ`, each `ξ i`
is trivial on units, and `‖ξ i ϖ‖` is antitone in `i` for a uniformiser `ϖ`. If `A` lies above `w`
and `s⁻¹` is a Frobenius at `A`, then `r` is of finite type at `A` (trivial on inertia near `1` if
`ℓ` is a unit at `A`, and potentially crystalline), its Hodge–Tate jumps at `A` are
`jumps κ (card n)`, and `∏ i, (X - ιℓ (ξ i ϖ))` kills `r(s)` at `A` in the sense of
`New.GaloisRep.PolyKillsAt`. -/
lemma GaloisRep.Attached.local_global_of_eigencharacter_of_unramified
    (hf_iwahori : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
    [EmbeddedNumberField E] {r : GalRep ℓ E n} {A : ClosurePlace} (he : IsEigenform f.val P)
    (hr : Attached P r) (hA : IsPlaceOver A w) {s : Gal(Ω/E)} (hs_frob : IsFrob A w.q s⁻¹)
    {ϖ : (LocField w)ˣ} (hϖ : v ϖ.val = WithZero.exp (-1))
    (hunr : ∀ y : (LocField w)ˣ, v y.val = 1 → ∀ i : Fin (card n), (ξ i y).val = 1)
    (hξ_antitone : Antitone fun i : Fin (card n) ↦ ‖(ξ i ϖ).val‖) :
    IsFiniteTypeAt r A ∧
    HasJumpsAt r A (jumps κ (card n)) ∧
    PolyKillsAt r A s (∏ i : Fin (card n), (X - C (ιℓ (ξ i ϖ)))) := by
  -- By `sphericalCompat_std` at a spherical form `g` for `P`, `r` is unramified or crystalline at
  -- `A`, has the jumps of `κ`, and the Hecke polynomial kills `s`.
  obtain ⟨g, hg, hgw⟩ : ∃ g : (stdSpace E n).forms κ, IsEigenform g.val P ∧
      HasHeckePolyAt g.val w hw (∏ i : Fin (card n), (X - C (ξ i ϖ).val)) :=
    hf_iwahori.exists_hasHeckePolyAt he hϖ hunr hξ_antitone
  obtain ⟨hgood, hjump, hpoly⟩ : IsCompatibleAt g.val (card n) w r A :=
    (sphericalCompat_std w g.2 hg).2 hr hgw.1 A hA
  refine ⟨(isGoodAt_iff.1 hgood).1, hjump, ?_⟩
  simpa [Polynomial.map_prod] using hpoly hw _ hgw s hs_frob

/-- The case `k > 0` of `New.GaloisRep.Attached.local_global_of_eigencharacter`, with the `ξ i`
sorted at `x`. Let `r` be attached to the eigenform `f`, a pro-`p` Iwahori eigenvector for
`torusChar ξ` at the split place `w` (`star w ≠ w`). Let `A` lie above `w`, let `s⁻¹` act as the
`q ^ k`-th power map on the residue field of `A`, and let `x`, of order `k`, have the class of `s`
as local Artin symbol. Then `r` is of finite type at `A`: it is trivial on inertia near `1` if `ℓ`
is a unit at `A`, and it is potentially crystalline along every embedding inducing `A`. It also has
the jumps of `κ`, and `∏ i, (X - ιℓ (ξ i x))` kills `s` (that is, kills `r s` if `ℓ` is a unit at
`A`). -/
lemma GaloisRep.Attached.local_global_of_eigencharacter_of_pos
    (hf_iwahori : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
    [EmbeddedNumberField E] {r : GalRep ℓ E n} {A : ClosurePlace} (he : IsEigenform f.val P)
    (hr : Attached P r) (hA : IsPlaceOver A w) (s : decompGroup Gal(Ω/E) A)
    (x : (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w)ˣ) (k : ℕ)
    (hs_frob : IsFrob A (w.q ^ k) s.val⁻¹) (hx_artin : localArtin Gal(Ω/E) A w x = s)
    (hx_val : v x.val = WithZero.exp (-k : ℤ)) (hk_pos : 0 < k)
    (hξ_antitone : Antitone fun i : Fin (card n) ↦ ‖(ξ i x).val‖) :
    IsFiniteTypeAt r A ∧
    HasJumpsAt r A (jumps κ (card n)) ∧
    PolyKillsAt r A s.val (∏ i : Fin (card n), (X - C (ιℓ (ξ i x)))) := by
  -- Induct on the index of the group `D` of the `y` with `(|y|, ξ y)` a power of `(|x|, ξ x)`.
  -- Index one forces `k = 1` and `ξ` unramified: the spherical case. Otherwise base change to a
  -- cyclic extension of prime degree in which `x` is a norm lowers the index.
  let D : Subgroup (LocField w)ˣ :=
    (zpowers (normAbsChar.prod (.pi ξ) x)).comap (normAbsChar.prod (.pi ξ))
  induction hidx : D.index using Nat.strong_induction_on generalizing E k with
  | _ idx ih => ?_
  have : D.FiniteIndex := hf_iwahori.finiteIndex_comap_zpowers hx_val hk_pos
  by_cases h_index : D.index = 1
  · obtain ⟨rfl, hunr⟩ := IsIwahoriEigen.order_eq_one_and_unramified hx_val
      ((eq_top_iff' D).1 (index_eq_one.1 h_index))
    rw [pow_one] at hs_frob
    exact hr.local_global_of_eigencharacter_of_unramified hf_iwahori he hA hs_frob hx_val hunr
      hξ_antitone
  -- Duality for the finite group `(LocField w)ˣ ⧸ D` gives `χ` of prime order that is trivial on
  -- `D`.
  obtain ⟨p, hp, hp_dvd⟩ := D.index.exists_prime_and_dvd h_index
  obtain ⟨χ, x₀, hχ₀, hχp, hχD⟩ := exists_char_trivial_of_prime_dvd_index D hp hp_dvd
  have h_tame (y : (LocField w)ˣ) (hy : v y.val = 1) : χ (y ^ (w.q - 1)) = 1 :=
    hχD _ (by simp [D, Subgroup.mem_comap, hf_iwahori.char_pow_q_sub_one_eq_one y hy, one_mem])
  -- As `χ` is tame, Grunwald's theorem gives a Galois character `μ` such that the field
  -- `stepField μ` cut out by `symmetrise μ` has degree `p` and one place `u` above `w`. Under the
  -- Artin map at `w`, `μ` is trivial (`hμw`) and `symmetrise μ` is `χ` (`hμχ`).
  obtain ⟨μ, u, ⟨_inst⟩, _hstep, -, hu, hbelow, hAu, hμw, hμχ⟩ :=
    exists_step_of_local_char hw hA hp χ hχ₀ hχp h_tame
  obtain rfl : u.below E = w := (hbelow u).2 rfl
  -- Base change `f` to `f'`, with eigencharacter `ξ i ∘ N` for the local norm `N`. What holds at
  -- `A` for its representation `r'` descends to `r`.
  let N : (LocField u)ˣ →* (LocField (u.below E))ˣ := localNorm E u
  obtain ⟨f', P', he', hsame, hf'_iwahori⟩ :=
    exists_baseChange_isIwahoriEigen hu hbelow (by simp [*]) hf_iwahori
  obtain ⟨r', hr'⟩ := (sphericalCompat_std u f'.2 he').1
  have h_down : DescendsAt μ r' r A := hsame.descendsAt hr' he' he hr A
  -- As `χ x = 1`, `x` is a norm: the residue degree `e` divides `k`, and `s` fixes the step.
  have hx_ker : abelianLift (symmetrise μ) (artinAt Gal(Ω/E) (u.below E) x) = 1 :=
    (hμχ x).trans (hχD x (mem_zpowers _))
  let e : ℕ := u.asIdeal.inertiaDeg (NumberField.RingOfIntegers E)
  have hq : (u.below E).q ^ e = u.q := absNorm_pow_inertiaDeg ..
  have v_norm (z : (LocField u)ˣ) : v (N z).val = v z.val ^ e := v_localNorm hq z
  obtain ⟨k', rfl⟩ : e ∣ k := by
    obtain ⟨z, rfl⟩ := exists_localNorm_of_abelianLift_artinAt hx_ker
    have h_val : WithZero.exp (-k : ℤ) = v z.val ^ e := hx_val.symm.trans (v_norm z)
    exact ofNat_dvd.1 (dvd_neg.1 ⟨(v z.val).log, by simpa using congrArg WithZero.log h_val⟩)
  rw [pow_mul, hq] at hs_frob
  have h_artin : artinAt Gal(Ω/E) (u.below E) x = s.val :=
    hA.artinAt_eq_of_localArtin_eq hx_artin
  have hs_sym : s.val ∈ ker (symmetrise μ) := (h_artin ▸ hx_ker :)
  have hs_μ : s.val ∈ ker μ := (h_artin ▸ hμw x :)
  let s' : Gal(Ω/stepField μ) := (stepField μ).fixingSubgroupEquiv ⟨s, fun z ↦ z.2 ⟨s, hs_sym⟩⟩
  have hs'_frob : IsFrob A (u.q ^ k') s'⁻¹ := hs_frob
  -- Take `y` in the completion at `u` of order `k'` with symbol `s'`. Then `N y` and `x` have the
  -- same symbol and the same order.
  obtain ⟨y, hy_val, hy_artin⟩ := hAu.exists_localArtin_eq hs'_frob k'
  have hart : localArtin Gal(Ω/E) A (u.below E) (N y) = s :=
    (hAu.localArtin_localNorm (Γ := Gal(Ω/stepField μ))
      (AlgEquiv.restrictScalarsHom E)).1 hy_artin
  have hNy : normAbsChar.prod (.pi ξ) (N y) = normAbsChar.prod (.pi ξ) x :=
    hf_iwahori.eq_of_localArtin_eq hA (by simp [v_norm, hx_val, hy_val]) (hart.trans hx_artin.symm)
  have hξy (i : Fin (card n)) : ξ i (N y) = ξ i x := congrFun (congrArg Prod.snd hNy) i
  simp_rw [← hξy] at hξ_antitone ⊢
  -- The group for `(f', y)` is `D.comap N`, as `N` keeps the absolute value. Its index is smaller:
  -- `χ` kills norms and `D` but not `x₀`.
  have hpull : normAbsChar.prod (.pi fun i ↦ (ξ i).comp N) = (normAbsChar.prod (.pi ξ)).comp N :=
    MonoidHom.ext fun z ↦ Prod.ext (by ext; simp [N, coe_normAbsChar_locField, norm_localNorm]) rfl
  have hχN (z : (LocField u)ˣ) : χ (N z) = 1 :=
    (hμχ _).symm.trans
      (abelianLift_artinAt_eq_one_of_mem_closure (L := stepField μ) adeleNorm_mem_closure)
  have hlt : (D.comap N).index < idx := (index_comap_lt_of_char_ne_one hχ₀ hχD hχN).trans_eq hidx
  obtain ⟨hfin, hjump, hpoly⟩ :
      IsFiniteTypeAt r' A ∧ HasJumpsAt r' A (jumps κ.baseChange (card n)) ∧
        PolyKillsAt r' A s' (∏ i : Fin (card n), (X - C (ιℓ (ξ i (N y))))) := by
    refine ih _ hlt hf'_iwahori he' hr' hAu ⟨s', _⟩ y k' hs'_frob hy_artin hy_val
      (Nat.pos_of_mul_pos_left hk_pos) hξ_antitone ?_
    rw [hpull, MonoidHom.comp_apply, hNy, ← Subgroup.comap_comap]
  exact ⟨h_down.isFiniteTypeAt hfin, h_down.hasJumpsAt _ hjump,
    h_down.polyKillsAt ⟨s, hs_sym, hs_μ⟩ _ hpoly⟩

/-- Local-global compatibility at a split place with a sorted pro-`p` Iwahori eigencharacter. Let
`r` be attached to the eigenform `f`, which at the split place `w` is a pro-`p` Iwahori eigenvector
for `New.torusChar ξ`, with `‖ξ i ϖ‖` antitone in `i` for the uniformiser `ϖ = New.uniformizer w`.
Let `A` lie above `w`, let `s⁻¹` act as the `q ^ k`-th power map on the residue field of `A`, and
let `x`, of order `k`, have the class of `s` as local Artin symbol. Then (a) `r` is of finite type
at `A` (`New.GaloisRep.IsFiniteTypeAt`: trivial on inertia near `1` away from `ℓ`, potentially
crystalline above `ℓ`), (b) it has the Hodge–Tate jumps of `κ`, and (c)
`∏ i, (X - ιℓ (ξ i x))` kills `s` (`New.GaloisRep.PolyKillsAt`). Parts (a) and (b) do not involve
`s`, `x`, `k`; they stand here because one induction proves all three. Here `q = w.q` is the size
of the residue field at `w` and `ιℓ` is the fixed isomorphism of `ℂ` with `ℚ̄_ℓ`. -/
lemma GaloisRep.Attached.local_global_of_eigencharacter
    (hf_iwahori : IsIwahoriEigen (localFormRep (stdSpace E n) κ hw) (torusChar ξ) f)
    [EmbeddedNumberField E] {r : GalRep ℓ E n} {A : ClosurePlace} (he : IsEigenform f.val P)
    (hr : Attached P r) (hξ_antitone : Antitone fun i : Fin (card n) ↦ ‖(ξ i (uniformizer w)).val‖)
    (hA : IsPlaceOver A w) (s : decompGroup Gal(Ω/E) A)
    (x : (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w)ˣ) (k : ℕ)
    (hs_frob : IsFrob A (w.q ^ k) s.val⁻¹) (hx_artin : localArtin Gal(Ω/E) A w x = s)
    (hx_val : v x.val = WithZero.exp (-k : ℤ)) :
    IsFiniteTypeAt r A ∧
    HasJumpsAt r A (jumps κ (card n)) ∧
    PolyKillsAt r A s.val (∏ i : Fin (card n), (X - C (ιℓ (ξ i x)))) := by
  obtain hk_pos | rfl : 0 < k ∨ k = 0 := k.eq_zero_or_pos.symm
  · exact hr.local_global_of_eigencharacter_of_pos hf_iwahori he hA s x k hs_frob hx_artin hx_val
      hk_pos (hf_iwahori.antitone_norm hξ_antitone hx_val)
  -- For `k = 0`, multiply `s` by positive powers of the symbol `φ⁻¹` of the uniformiser.
  obtain ⟨φ, hφ, hϖ⟩ : ∃ φ : decompGroup Gal(Ω/E) A,
      IsFrob A w.q φ.val ∧ localArtin Gal(Ω/E) A w (uniformizer w) = ↑φ⁻¹ :=
    hA.exists_isFrob_localArtin_eq_inv (Γ := Gal(Ω/E)) (v_uniformizer w)
  obtain ⟨hfin, hjump, hφ_kill⟩ : IsFiniteTypeAt r A ∧ HasJumpsAt r A (jumps κ (card n)) ∧
      PolyKillsAt r A (φ⁻¹).val (∏ i : Fin (card n), (X - C (ιℓ (ξ i (uniformizer w))))) :=
    hr.local_global_of_eigencharacter_of_pos hf_iwahori he hA φ⁻¹ (uniformizer w) 1 (by simpa) hϖ
      (by simp) one_pos hξ_antitone
  refine ⟨hfin, hjump, .of_mul_frob_pow hA hφ (by simp) hφ_kill fun m hm ↦ ?_⟩
  have h_frob : IsFrob A (w.q ^ m) (s * φ⁻¹ ^ m).val⁻¹ := by
    simpa using (hφ.pow m).mul_iff.2 hs_frob
  have h_art : localArtin Gal(Ω/E) A w (x * uniformizer w ^ m) = ↑(s * φ⁻¹ ^ m) := by
    simp [hx_artin, hϖ]
  have h_val : v (x * uniformizer w ^ m).val = WithZero.exp (-m : ℤ) := by simp [hx_val]
  obtain ⟨-, -, h_kill⟩ := hr.local_global_of_eigencharacter_of_pos hf_iwahori he hA _ _ m h_frob
    h_art h_val hm (hf_iwahori.antitone_norm hξ_antitone h_val)
  simpa using h_kill

end New

/-!
## Frobenius and inertia for parahoric types

At a finite place `w ≠ w̄` of `E` not above `ℓ`, the action of `GL_N(E_w)`, with `N` the cardinality
of `n`, on a form `y` of an isotypic space `x` (`New.Patching.localFormRep`) is compared with the
Galois representation `x.galRep` attached to `x`. A place `A` of the algebraic closure above `w` is
fixed. `New.proIwahori` is the pro-`p` Iwahori subgroup and `ιℓ : ℂ ≃+* ℚ̄_ℓ`.
-/

section TypeFrobenius

open NumberField Matrix Polynomial Finset Valued Pi Nat Algebra Fintype

namespace New.Patching

variable {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ]
  {E n : Type} [Field E] [CMType E] [Algebra E Ω] [Fintype n] [DecidableEq n] [Nonempty n]
  {V : Space E n 1} {κ : Weight E} [V.IsStd] [WeilData E]
  {w : FinPlace E} {hw : star w ≠ w} {A : ClosurePlace}
  {ϖ u : (LocField w)ˣ} {s τ : decompGroup Gal(Ω/E) A} {x : Isotypic V κ} {y : V.forms κ}

/-- `IsParahoricCompatible ρ z ϖ d F T` says that the matrices `F`, `T` behave as those of a
geometric Frobenius that comes from `ϖ` and of an inertia element, as seen by the vector `z` of `ρ`:
they commute, `T` is killed by every polynomial that vanishes at all `ιℓ (d i)`, and there are
characters `θ i`, with an exponent functional that is not zero on `z`, such that
`∏ i, (X - ιℓ (θ i ϖ * d i ^ b))` kills `F * T ^ b` for every natural number `b`. -/
structure IsParahoricCompatible {E : Type} [Field E] [NumberField E] {w : FinPlace E}
    {N : ℕ} (ρ : Rep ℂ (GL (Fin N) (LocField w))) [IsSmoothRep ρ.ρ]
    (z : ρ) (ϖ : (LocField w)ˣ) (d : Fin N → ℂ) (F T : Matrix n n (PadicAlgCl ℓ)) : Prop where
  /-- Every polynomial that vanishes at all `ιℓ (d i)` kills `T`. -/
  aeval_inertia_eq_zero :
    ∀ p : (PadicAlgCl ℓ)[X], (∀ i : Fin N, p.IsRoot (ιℓ (d i))) → aeval T p = 0
  /-- `F` and `T` commute. -/
  commute : Commute F T
  /-- There are characters `θ i` such that some exponent `l` for the torus character of `θ`
  (`New.IsExponent`) is not zero on `z`, and `∏ i, (X - ιℓ (θ i ϖ * d i ^ b))` kills `F * T ^ b`
  for all `b`. -/
  exists_characters : ∃ θ : Fin N → (LocField w)ˣ →* ℂˣ,
    (∃ l : ρ →ₗ[ℂ] ℂ, IsExponent ρ (torusChar θ) l ∧ l z ≠ 0) ∧
    ∀ b : ℕ, aeval (F * T ^ b) (∏ i : Fin N, (X - C (ιℓ (θ i ϖ * d i ^ b)))) = 0

/-- Let `A` lie above `w ∤ ℓ`. Let the local Artin map send the uniformiser `ϖ` to `s`, the inverse
of a Frobenius element, and the unit `u` to the inertia element `τ`. Let `y ≠ 0` in the isotypic
space `x` be fixed by the pro-`p` Iwahori subgroup at `w`, let the parahoric subgroup with blocks
`f` act on `y` by scalars `c`, and write `d i` for the scalar of the diagonal matrix with `u` in
slot `i` and `1` elsewhere. Assume that slots with the same `d` lie in one block. Then the matrices
`F` of `s` and `T` of `τ` commute, and `T` is killed by every polynomial that vanishes at all
`ιℓ (d i)`. Also, there are characters `θ i` and an exponent for `New.torusChar θ` (a linear
functional as in `New.IsExponent`) that is not zero on `y`, such that
`∏ i, (X - ιℓ (θ i ϖ * d i ^ b))` kills `F * T ^ b` for every natural number `b`
(`New.Patching.IsParahoricCompatible`). -/
lemma isParahoricCompatible_galRep (hA : IsPlaceOver A w) (hϖ : v ϖ.val = WithZero.exp (-1))
    (hϖ_artin : localArtin Gal(Ω/E) A w ϖ = s) (hs_frob : IsFrob A w.q s.val⁻¹)
    (hu : v u.val = 1) (hu_artin : localArtin Gal(Ω/E) A w u = τ)
    (hτ : τ.val ∈ inertiaGroup Gal(Ω/E) A) (hℓ : (ℓ : 𝓞 E) ∉ w.asIdeal) (hy : y ∈ x.val)
    (hy_ne : y ≠ 0) (f : ℕ → ℕ) {c : GL (Fin (card n)) (LocField w) → ℂ}
    (hy_type : y ∈ parahoricEigenspace (localFormRep V κ hw) f c)
    (h_blocks : ∀ i k : Fin (card n),
      c (diagGL (mulSingle i u)) = c (diagGL (mulSingle k u)) → f i = f k) :
    IsParahoricCompatible (localFormRep V κ hw) y ϖ
      (fun i : Fin (Fintype.card n) ↦ c (diagGL (mulSingle i u))) (x.galRep s).val
      (x.galRep τ).val := by
  -- `exists_sorted_isIwahoriEigen_of_diagGL_smul` gives characters `θ` with an exponent and, for a
  -- sorted rearrangement of them, an eigenvector `z` in the system `x`; local-global compatibility
  -- at `z` gives the polynomials.
  cases Space.IsStd.eq_stdSpace V
  let ρ := localFormRep (stdSpace E n) κ hw
  obtain ⟨y_fixed, h_par⟩ := hy_type
  have hℓ_unit : A.valuation ℓ = 1 := hA.valuation_natCast_eq_one_iff.2 hℓ
  -- a permutation that keeps the `d i` keeps the blocks, so its matrix is in the parahoric group
  have h_perm (σ : Equiv.Perm (Fin (card n)))
      (hσ : ∀ i, c (diagGL (mulSingle i u)) = c (diagGL (mulSingle (σ i) u))) :
      permGL σ ∈ blockParahoric (F := LocField w) f := by
    refine ⟨permGL_mem_intGL σ, fun i j hij ↦ ?_⟩
    rw [h_blocks j (σ j) (hσ j)] at hij
    simp [σ.symm_apply_eq, Fin.ext_iff, ne_of_apply_ne f hij.ne']
  obtain ⟨θ, h_exp, hθ, σ, h_anti, z, z_mem, z_eig⟩ :
      ∃ θ : Fin (card n) → (LocField w)ˣ →* ℂˣ,
        (∃ l : ρ →ₗ[ℂ] ℂ, IsExponent ρ (torusChar θ) l ∧ l y ≠ 0) ∧
        (∀ i (ε : (LocField w)ˣ), v ε.val = 1 → θ i ε = c (diagGL (mulSingle i ε))) ∧
        ∃ σ : Equiv.Perm (Fin (card n)), Antitone ((fun i ↦ ‖(θ i (uniformizer w) : ℂ)‖) ∘ σ) ∧
          ∃ z ∈ cyclicSpan ρ.ρ y, IsIwahoriEigen ρ (torusChar (θ ∘ σ)) z :=
    exists_sorted_isIwahoriEigen_of_diagGL_smul (v_uniformizer w) y_fixed
      (fun t ht ↦ h_par _ ⟨ht, fun i j hij ↦ by simp [Fin.ext_iff, ne_of_apply_ne f hij.ne']⟩)
      (fun σ hσ ↦ ⟨c (permGL σ), h_par _ (h_perm σ fun i ↦ hσ i u hu)⟩) isUnitary_localFormRep hy_ne
  have z_form : IsEigenform z.val x.heckePolyAt :=
    (x.isEigenform hy hy_ne).of_mem_cyclicSpan z_mem z_eig.1
  -- if `g⁻¹` acts as the `w.q ^ k`-th power on the residue field and `g` is the local Artin symbol
  -- of `ε`, of order `k`, then `∏ i, (X - ιℓ (θ (σ i) ε))` kills `g`
  have h_poly (g : decompGroup Gal(Ω/E) A) (ε : (LocField w)ˣ) (k : ℕ)
      (hg : IsFrob A (w.q ^ k) g.val⁻¹) (h_art : localArtin Gal(Ω/E) A w ε = g)
      (hε : v ε.val = WithZero.exp (-(k : ℤ))) : GaloisRep.IsFiniteTypeAt x.galRep A ∧
      GaloisRep.PolyKillsAt x.galRep A g.val (∏ i, (X - C (ιℓ (θ (σ i) ε)))) :=
    ((x.attached_galRep hy hy_ne).local_global_of_eigencharacter z_eig z_form h_anti hA g ε k
      hg h_art hε).imp_right And.right
  -- inertia has finite image, so an inertial `g` that comes from a unit `ε` is semisimple, with
  -- eigenvalues among the `ιℓ (θ i ε)`
  have h_inertia (g : decompGroup Gal(Ω/E) A) (ε : (LocField w)ˣ)
      (hg : g.val ∈ inertiaGroup Gal(Ω/E) A) (h_art : localArtin Gal(Ω/E) A w ε = g)
      (hε : v ε.val = 1) (p : (PadicAlgCl ℓ)[X]) (hp : ∀ i, p.IsRoot (ιℓ (θ (σ i) ε))) :
      aeval (x.galRep g).val p = 0 := by
    obtain ⟨h_fin, h_kill⟩ := h_poly g ε 0 (inv_mem hg) h_art hε
    exact h_fin.aeval_eq_zero_of_roots hℓ_unit hg h_kill p
      (by simpa [eval_prod, prod_eq_zero_iff, sub_eq_zero] using hp)
  refine ⟨fun p hp ↦ ?_, ?_, θ, h_exp, fun b ↦ ?_⟩
  · exact h_inertia τ u hτ hu_artin hu p fun i ↦ by simpa only [hθ _ u hu] using hp (σ i)
  · -- the commutator of `s` and `τ` is inertial and comes from the unit `1`
    have h_conj : IsFrob A 1 (s.val * τ.val * s.val⁻¹) := by
      convert IsFrob.conj hτ s.val
      exact s.prop.symm
    have h_comm : aeval (x.galRep (s * τ / s / τ)).val (X - 1 : (PadicAlgCl ℓ)[X]) = 0 :=
      h_inertia (s * τ / s / τ) 1 (div_mem h_conj hτ) (by simp) (by simp) (X - 1) (by simp)
    simpa [commute_iff_eq, div_eq_iff_eq_mul, Units.ext_iff, sub_eq_zero] using h_comm
  · -- `s * τ ^ b` is a geometric Frobenius that comes from `ϖ * u ^ b`
    have h_frob : IsFrob A (w.q ^ 1) (s * τ ^ b).val⁻¹ := by
      simpa using (zpow_mem hτ (-b)).mul_iff.2 hs_frob
    obtain ⟨-, h_kill, -⟩ :=
      h_poly (s * τ ^ b) (ϖ * u ^ b) 1 h_frob (by simp [hϖ_artin, hu_artin]) (by simp [hϖ, hu])
    rw [← Equiv.prod_comp σ]
    simpa [hθ _ u hu] using h_kill hℓ_unit

omit [Nonempty n] in
/-- Let `F` and `T` commute, let `T` be semisimple with eigenvalues among `d 0, 1, …, 1`, where
`d 0 ≠ 0` and `d 0 ^ N ! ≠ 1`, and let `∏ i, (X - α i * d i ^ b)` kill `F * T ^ b` for every `b`,
with all `α i ≠ 0`. Then `F * (T - 1) = α 0 • (T - 1)`: `F` is the scalar `α 0` on the image of
`T - 1`. -/
lemma mul_sub_one_eq_smul_sub_one {k : Type*} {N : ℕ} [Field k] [NeZero N] {F T : Matrix n n k}
    {α d : Fin N → k} (hd : ∀ i : Fin N, i ≠ 0 → d i = 1) (hd_ne : d 0 ≠ 0) (hζ : d 0 ^ N ! ≠ 1)
    (hα : ∀ i : Fin N, α i ≠ 0) (hFT : Commute F T)
    (hT : ∀ p : k[X], (∀ i : Fin N, p.IsRoot (d i)) → aeval T p = 0)
    (hF : ∀ b : ℕ, aeval (F * T ^ b) (∏ i : Fin N, (X - C (α i * d i ^ b))) = 0) :
    F * (T - 1) = α 0 • (T - 1) := by
  -- Put `ζ = d 0` and `q = ∏_{i ≠ 0} (X - α i)`. On the image of `T - 1` the matrix `T` acts as
  -- `ζ`, so `hF` gives `∑ i, (ζ ^ b) ^ i • (q.coeff i • F ^ i * (F - α 0) * (T - 1)) = 0`. The
  -- `ζ ^ b` are distinct, so every coefficient is zero (Vandermonde); `i = 0` is the claim.
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  let q : k[X] := ∏ i : Fin N, (X - C (α i.succ))
  have hq_zero : q.coeff 0 ≠ 0 := by simp [q, hα, coeff_zero_prod, prod_eq_zero_iff]
  -- `(T - 1) * T = ζ • (T - 1)`, because `(X - 1) * (X - ζ)` vanishes at every `d i`
  have hT_semi : SemiconjBy (T - 1) T (d 0 • 1) := by
    have h_roots (i : Fin (N + 1)) : ((X - 1) * (X - C (d 0))).IsRoot (d i) := by
      by_cases hi : i = 0 <;> simp [hi, hd]
    simpa [SemiconjBy, mul_sub (T - 1), sub_eq_zero, algebraMap_eq_smul_one] using hT _ h_roots
  have h_semi (b : ℕ) : SemiconjBy (T - 1) (F * T ^ b) (d 0 ^ b • F) := by
    simpa [_root_.smul_pow] using
      (hFT.sub_right (.one_right F)).symm.semiconjBy.mul_right (hT_semi.pow_right b)
  -- moving `T - 1` across `hF b` replaces `F * T ^ b` by `ζ ^ b • F`; the factor for `i = 0` is
  -- `ζ ^ b • (F - α 0)`, and `ζ ^ b ≠ 0` cancels
  have h_sum (b : ℕ) : ∑ i : Fin (N + 1),
      (d 0 ^ b) ^ i.val • (q.coeff i • F ^ i.val * (F - α 0 • 1) * (T - 1)) = 0 := by
    have h_prod : ∏ i, (X - C (α i * d i ^ b)) = q * (X - C (α 0 * d 0 ^ b)) := by
      simp [Fin.prod_univ_succ, hd, q, mul_comm]
    have h_move : aeval (d 0 ^ b • F) q * (d 0 ^ b • (F - α 0 • 1)) * (T - 1) = 0 := by
      rw [← mul_zero (T - 1), ← hF b, aeval_semiconj (h_semi b), h_prod, map_mul]
      simp [smul_sub, _root_.smul_pow, smul_smul, mul_comm, algebraMap_eq_smul_one]
    rw [aeval_eq_sum_range, show q.natDegree = N by simp [q], sum_range] at h_move
    simpa [hd_ne, sum_mul, _root_.smul_pow, ← smul_sum, smul_comm (q.coeff _)] using h_move
  -- `ζ ^ i = ζ ^ j` with `i < j ≤ N` gives `ζ ^ (j - i) = 1`, and `j - i` divides `(N + 1)!`
  have h_inj : Function.Injective fun b : Fin (N + 1) ↦ d 0 ^ b.val := by
    refine .of_lt_imp_ne fun i j hij (h_eq : d 0 ^ i.val = d 0 ^ j.val) ↦ hζ ?_
    have h_pow : d 0 ^ (j.val - i.val) = 1 := by simp [pow_sub₀ _ hd_ne hij.le, ← h_eq, hd_ne]
    exact orderOf_dvd_iff_pow_eq_one.1
      ((orderOf_dvd_of_pow_eq_one h_pow).trans (dvd_factorial (by lia) (by lia)))
  have h_zero : q.coeff 0 • F ^ 0 * (F - α 0 • 1) * (T - 1) = 0 := by
    ext r c
    refine congrFun (eq_zero_of_forall_index_sum_pow_mul_eq_zero h_inj (v := fun i ↦
      (q.coeff i • F ^ i.val * (F - α 0 • 1) * (T - 1)) r c) fun b ↦ ?_) 0
    simpa [Matrix.sum_apply] using congrFun₂ (h_sum b) r c
  simpa [hq_zero, sub_mul, sub_eq_zero] using h_zero

/-- Let `A` lie above `w ∤ ℓ`. Let the local Artin map send the uniformiser `ϖ` to `s`, the inverse
of a Frobenius element, and the unit `u` to the inertia element `τ`. Let `y` in the isotypic space
`x` be fixed by the pro-`p` Iwahori subgroup at `w`, and let the stabiliser in `GL_N(𝒪_w)` of the
first coordinate line modulo `w` act on `y` by `χ` of the top left entry
(`New.Patching.parahoricEigenspace`), where `χ u ≠ 0` and `χ u ^ (card n)! ≠ 1`. Let `U` be the
Hecke operator of `diag (ϖ, 1, …, 1)`, `F` the matrix of `s` and `T` that of `τ` minus `1`. Then
`tr (T M) • G(U) y = tr (G(F) T M) • y` through `ιℓ`, for every complex polynomial `G` and every
matrix `M`: `U` acts like `F` on the image of `T`. -/
lemma hecke_eq_frob_on_parahoricEigenspace (hA : IsPlaceOver A w)
    (hϖ : v ϖ.val = WithZero.exp (-1)) (hϖ_artin : localArtin Gal(Ω/E) A w ϖ = s)
    (hs_frob : IsFrob A w.q s.val⁻¹) (hu : v u.val = 1)
    (hu_artin : localArtin Gal(Ω/E) A w u = τ) (hτ : τ.val ∈ inertiaGroup Gal(Ω/E) A)
    (hℓ : (ℓ : 𝓞 E) ∉ w.asIdeal) (hy : y ∈ x.val) (χ : LocField w → ℂ) (hχ : χ u ≠ 0)
    (hζ : χ u ^ (card n)! ≠ 1) (G : ℂ[X]) {M : Matrix n n (PadicAlgCl ℓ)}
    (hy_type : y ∈ parahoricEigenspace (localFormRep V κ hw) (min 1)
      (χ ∘ fun g : GL (Fin (card n)) (LocField w) ↦ g 0 0)) :
    let U := heckeCoset (localFormRep V κ hw).ρ proIwahori (diagGL (mulSingle 0 ϖ))
    let F := (x.galRep s).val
    let T := (x.galRep τ).val - 1
    ιℓ.symm (T * M).trace • aeval U G y =
      ιℓ.symm (aeval F (G.map ιℓ.toRingHom) * T * M).trace • y := by
  intro U F T
  let ρ := localFormRep V κ hw
  let S : Submodule ℂ (V.forms κ) := x.val ⊓ parahoricEigenspace ρ (min 1) (χ ∘ fun g ↦ g 0 0)
  -- Degree one. If the difference `z` of the two sides is not zero, `isParahoricCompatible_galRep`
  -- gives it an exponent `l` with characters `θ` and `l z ≠ 0`. But both `U` (seen by `l`) and `F`
  -- (on the image of `T`) act by `θ 0 ϖ`, so `l z = 0`.
  have degree_one (B : Matrix n n (PadicAlgCl ℓ)) :
      ιℓ.symm (B * T * M).trace • U y = ιℓ.symm (B * F * T * M).trace • y := by
    let z := ιℓ.symm (B * T * M).trace • U y - ιℓ.symm (B * F * T * M).trace • y
    refine eq_of_sub_eq_zero (by_contra fun z_ne : z ≠ 0 ↦ ?_)
    have Uy_mem : U y ∈ S := ⟨x.map_mem (heckeFun_mem_localGroupAlgebra hw _) hy,
      parahoricEigenspace_mem_invtSubmodule ρ hϖ hy_type⟩
    obtain ⟨hz, z_type⟩ : z ∈ S := sub_mem (S.smul_mem _ Uy_mem) (S.smul_mem _ ⟨hy, hy_type⟩)
    have χ_one : χ 1 = 1 :=
      smul_left_injective ℂ z_ne (by simpa using (z_type.2 1 (one_mem _)).symm)
    -- the unit `u` gives `χ u ≠ 1` in slot `0` and `1` in the others: it separates the two blocks
    have χ_ne : χ u ≠ 1 := fun h ↦ hζ (by rw [h, one_pow])
    have χ_slot (i : Fin (card n)) : χ (diagGL (mulSingle i u) 0 0) = 1 ↔ i ≠ 0 := by
      by_cases hi : i = 0 <;> simp [hi, χ_ne, χ_one, eq_comm]
    have blocks (i k : Fin (card n))
        (h_eq : χ (diagGL (mulSingle i u) 0 0) = χ (diagGL (mulSingle k u) 0 0)) :
        min 1 i.val = min 1 k.val := by
      have h_iff : i ≠ 0 ↔ k ≠ 0 := by rw [← χ_slot, ← χ_slot, h_eq]
      grind [Fin.val_ne_zero_iff]
    obtain ⟨τ_roots, comm, θ, ⟨l, hl, lz_ne⟩, sτ_roots⟩ :
        IsParahoricCompatible ρ z ϖ (fun i ↦ χ (diagGL (mulSingle i u) 0 0)) F (x.galRep τ).val :=
      isParahoricCompatible_galRep hA hϖ hϖ_artin hs_frob hu hu_artin hτ hℓ hz z_ne _ z_type blocks
    have l_U : l (U y) = θ 0 ϖ * l y := by
      -- `U y` is `w.q ^ (card n - 1)` times the mean over `proIwahori` of
      -- `ρ (diag (ϖ, 1, …, 1)) y`, and this degree cancels the modulus factor in `torusChar`
      obtain ⟨dominant, U_eq⟩ : mulSingle 0 ϖ ∈ dominantTorus ∧ U y = (w.q : ℂ) ^ (card n - 1) •
          compactMean ρ.ρ proIwahori (ρ.ρ (diagGL (mulSingle 0 ϖ)) y) :=
        heckeCoset_mulSingle_zero_eq hϖ hy_type.1
      have l_diag : l (ρ.ρ (diagGL (mulSingle 0 ϖ)) y) = torusChar θ (mulSingle 0 ϖ) * l y := by
        simpa only [compactMean_eq_self (ρ := ρ.ρ) y hy_type.1] using hl dominant y
      rw [U_eq, map_smul, hl.apply_compactMean, l_diag]
      simp [coe_normAbsChar_locField, norm_locField_eq_q_zpow, hϖ, field]
    have F_mul_T : F * T = ιℓ (θ 0 ϖ) • T :=
      mul_sub_one_eq_smul_sub_one (α := fun i ↦ ιℓ (θ i ϖ))
        (fun i hi ↦ by simp only [(χ_slot i).2 hi, map_one])
        (by simpa using hχ) (by simpa using (ιℓ.injective.ne_iff' (map_one ιℓ)).2 hζ) (by simp)
        comm τ_roots (by simpa only [map_mul, map_pow] using sτ_roots)
    exact lz_ne (by simp [z, l_U, mul_assoc B F T, F_mul_T, mul_left_comm, mul_assoc])
  -- Horner induction on `G`: the step from `p` to `p * X` applies `U` and uses degree one
  induction G using recOnHorner with
  | M0 => simp
  | MC p a _ _ ih => simp [ih, add_mul, add_smul, smul_smul, mul_comm, algebraMap_eq_smul_one]
  | MX p _ ih =>
    nth_rw 1 [← X_mul]
    simpa [degree_one] using congrArg U ih

end New.Patching

end TypeFrobenius
