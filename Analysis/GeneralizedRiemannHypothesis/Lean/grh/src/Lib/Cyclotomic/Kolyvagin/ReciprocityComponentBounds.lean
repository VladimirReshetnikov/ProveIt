import Lib.ClassField.Global.Chebotarev
import Lib.Cyclotomic.Kolyvagin.DerivativeCocycles
import Lib.PadicComparison.Descent.TestCategory

/-!
# Reciprocity laws and Stickelberger and Kolyvagin bounds for odd-part cocycles

The file studies cocycles on `Gal(Ω/ℚ)`, with `Ω` an algebraic closure of ℚ. Here
`New.cyclotomicPowDirichlet l e ψ` is `cyc^e ψ` with `cyc` the `l`-adic cyclotomic character. The
module `New.OddPart.component l e ψ ν` consists of the cocycles for `(cyc^e ψ)⁻¹` with values in
`O / l^ν`, where `O` (`PadicIntegerRing O l`) is the integer ring of a finite extension of ℚ_l, that
satisfy three conditions. They are unramified off `l` over ℚ(μ_N), split at `l` over ℚ(μ_{N l^∞})
and zero at `New.cmConj`, a complex conjugation. Reciprocity laws at primes `q ≡ 1` relate the value
of one cocycle at a Frobenius element to the ramification of another. Using these laws and
Chebotarev's theorem, the file bounds these components in two ways. One bound is an annihilation
result analogous to Stickelberger's theorem. The other uses Kolyvagin's descent with the Euler
system of Gauss sums.

## Main definitions and results

* `New.OddPart.artin_reciprocity_of_mem_component`: Artin reciprocity over ℚ(μ_{N m}), where the
  prime q ≡ 1 splits completely, pairs a cocycle `x` with a number `y`; only the places above q
  contribute.
* `New.OddPart.reciprocity_mod_ell`: the same law modulo `l` for a cocycle κ for cyc^(e+1) ψ; if
  `2 (a ^ e - 1) x φ ≠ 0`, then κ vanishes on the inertia group of `B`.
* `New.OddPart.nsmul_component_eq_zero`: if `X` has the Stickelberger property
  (`New.OddPart.IsStickelbergerBound N e X`), `cyc^e ψ` is odd and `e ≠ 0`, then `4 X²` kills
  `New.OddPart.component l e ψ ν` (an analogue of Stickelberger's theorem).
* `New.OddPart.exists_detecting_points_component`: for large `l`, a cocycle in
  `New.OddPart.component l e ψ ν` is determined by its values at `v_l(X) + 1` elements (Kolyvagin's
  descent with the Euler system of Gauss sums).

Notions from other files:
* `New.cyclotomicPowDirichlet l e ψ`: the character `cyc^e ψ` of `Gal(Ω/ℚ)` with values in `Oˣ`; the
  Dirichlet character `ψ` is read through the action on the `N`-th roots of unity.
* `New.OddPart.vanishingCocycles χ M s`: the `O`-module of locally constant maps `x : Gal(Ω/ℚ) → M`
  with `x (g h) = x g + χ(g) x h` (cocycles for `χ`) that vanish on `s`.
* `New.IsFrob A q σ`: `σ` stabilises the place `A` and `σ • x ≡ x ^ q` modulo its maximal ideal for
  all `x ∈ A`.
* `New.ordRat K A`: the order `Ωˣ → ℚ` at the place `A`, normalised to be `1` on uniformisers of
  `K`. `New.cyclotomicCharMod Ω n` gives the action on the `n`-th roots of unity, in `(ℤ/n)ˣ`.

## Relation to the literature

Known result: Stickelberger annihilation and the Kolyvagin–Rubin bound for odd twisted components.
Here the value is taken at a negative integer instead of at zero, and for an integer X whose
multiples (a^(e+1) − 1) X, for a ≡ 1 mod N, are congruent modulo each m prime to a to 2w times the
Stickelberger sum at level N m, and which for each prime ℓ is divisible by (a^e − 1)(a^(e+1) − 1)
for some such a prime to ℓ, 4X² kills the odd component at every prime. For large primes ℓ, at most
v_ℓ(X)+1 Galois elements detect its classes. Source: J. Coates, W. Sinnott, An analogue of
Stickelberger's theorem for the higher K-groups, Invent. Math. 24 (1974); K. Rubin, Euler Systems,
2000, III.4, Thm 4.6.
-/

namespace New.OddPart

/-!
## Reciprocity laws for Galois cocycles and finiteness

Places are valuation subrings of `Ω`, and the group Ω^× is written additively. `New.cycloGalGroup N`
is the Galois group over ℚ(μ_N). The cocycles in `New.OddPart.component l e ψ ν` vanish at
`New.cmConj`. Over ℚ(μ_N) they also vanish on inertia at places prime to `l` and on
`New.Selmer.shaLocalSet` above `l`.
-/

section ReciprocityLaw

open DiscreteUnits Finset Subgroup QZ MonoidHom NeZero Fact Pointwise Submodule IsLocalRing
  IsPlaceOver

variable {O M : Type} [CommRing O]
  {N l m e q ν : ℕ} [NeZero N] [NeZero m] [Fact l.Prime] [Fact q.Prime] [PadicIntegerRing O l]
  {ψ : DirichletCharacter O N} {g τ φ : Gal(Ω/ℚ)}
  {B : ClosurePlace} [AddCommGroup M] [Module O M]
  {χ : Gal(Ω/ℚ) →* Oˣ} {s : Set Gal(Ω/ℚ)} {z : Gal(Ω/ℚ) → M} (hz : z ∈ vanishingCocycles χ M s)

/-- A map `z` in `vanishingCocycles χ M s` satisfies the cocycle rule
`z (g h) = z g + χ(g) z h`. -/
private lemma apply_mul_of_mem_vanishingCocycles (hz : z ∈ vanishingCocycles χ M s)
    (g h : Gal(Ω/ℚ)) : z (g * h) = z g + (χ g).val • z h :=
  hz.2.1 g h

/-- A map `z` in `vanishingCocycles χ M s` is locally constant. -/
private lemma isLocallyConstant_of_mem_vanishingCocycles (hz : z ∈ vanishingCocycles χ M s) :
    IsLocallyConstant z :=
  hz.1

/-- A map `z` in `vanishingCocycles χ M s` vanishes on `s`. -/
private lemma apply_eq_zero_of_mem_vanishingCocycles (hz : z ∈ vanishingCocycles χ M s)
    {g : Gal(Ω/ℚ)} (hg : g ∈ s) : z g = 0 :=
  hz.2.2 g hg

/-- A Frobenius element `σ` at the place `A` lies in the decomposition group of `A`. -/
private lemma mem_decompGroup_of_isFrob {A : ClosurePlace} {q : ℕ} {σ : Gal(Ω/ℚ)}
    (hσ : IsFrob A q σ) : σ ∈ decompGroup Gal(Ω/ℚ) A :=
  hσ.1

/-- The inertia group of the place `A` lies in its decomposition group. -/
private lemma mem_decompGroup_of_mem_inertiaGroup {A : ClosurePlace} {i : Gal(Ω/ℚ)}
    (hi : i ∈ inertiaGroup Gal(Ω/ℚ) A) : i ∈ decompGroup Gal(Ω/ℚ) A :=
  hi.1

/-- Let `g` fix the `N m`-th roots of unity (`g ∈ cycloGalGroup (N * m)`) and let `m • y = 0`.
Then `cyc^e ψ (g)` and its inverse fix `y`. -/
lemma cyclotomicPowDirichlet_smul_eq_self (hg : g ∈ cycloGalGroup (N * m)) {y : M}
    (hy : m • y = 0) :
    (cyclotomicPowDirichlet l e ψ g).val • y = y ∧
      (cyclotomicPowDirichlet l e ψ g)⁻¹.val • y = y := by
  have h_fix {σ : Gal(Ω/ℚ)} (hσ : σ ∈ cycloGalGroup (N * m)) :
      (cyclotomicPowDirichlet l e ψ σ).val • y = y := by
    simpa using cyclotomicPowDirichlet_smul (a := 1) (by simp [mem_ker.1 hσ]) hy
  exact ⟨h_fix hg, by simpa using h_fix (inv_mem hg)⟩

/-- The open subgroup `{g | z g = 0}` of zeros of a map `z` in `vanishingCocycles χ M s` (given by
`hz`): it is a subgroup by the cocycle rule, and open since `z` is locally constant. -/
noncomputable def openCocycleKer : OpenSubgroup Gal(Ω/ℚ) :=
  OpenSubgroup.mk (cocycleKer χ hz.2.1) (hz.1 {0})

/-- Let `z` be in `vanishingCocycles χ M s`, with `z γ = 0` and `(χ γ - 1) • z ≠ 0`. Then `z` does
not vanish on the Galois group over ℚ(μ_f), for any `f ≠ 0`. -/
lemma not_cycloGalGroup_le_openCocycleKer (γ : Gal(Ω/ℚ)) (hγ : z γ = 0)
    (h_ne : ((χ γ).val - 1) • z ≠ 0) (f : ℕ) [NeZero f] :
    ¬cycloGalGroup f ≤ openCocycleKer hz := by
  -- If `z` vanishes on `cycloGalGroup f`, it kills all commutators, so Sah's lemma gives
  -- `(χ γ - 1) • z g = (χ g - 1) • z γ`; and `z γ = 0`.
  refine fun h_le ↦ h_ne (funext fun g ↦ ?_)
  have h_comm_mem : (γ * g)⁻¹ * (g * γ) ∈ cycloGalGroup f := by simp [mul_right_comm]
  simpa [hγ] using sah (apply_mul_of_mem_vanishingCocycles hz) γ g (h_le h_comm_mem)

omit [PadicIntegerRing O l] in
/-- Let `M` be finite, let ℚ(μ_{N l^n}) trivialise the action through `χ`, and let `s` contain
the inertia over ℚ(μ_N) at all non-trivial places prime to `l`. Then there are finitely many
locally constant cocycles for `χ` that vanish on `s`. -/
lemma finite_vanishingCocycles [Finite M] {n : ℕ}
    (h_triv : ∀ g : cycloGalGroup (N * l ^ n), ∀ {y : M}, (χ g).val • y = y)
    (hs : ↑(cycloGalGroup N) ∩ inertiaAbove (placesDividing ℚ l)ᶜ ⊆ s) :
    Finite (vanishingCocycles χ M s) := by
  -- These cocycles are continuous for the discrete topology and unramified outside `N l`, and
  -- there are finitely many such (`selmerZ1.finite_unramified_cocycles`).
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := discreteTopology_bot M
  let : MulAction Gal(Ω/ℚ) M := .compHom M χ
  have cont : ContinuousSMul Gal(Ω/ℚ) M :=
    continuousSMul_iff_stabilizer_isOpen.2 fun y ↦ isOpen_mono (fun g hg ↦ h_triv ⟨g, hg⟩) out
  refine (selmerZ1.finite_unramified_cocycles (.of (charRep M χ) cont.1)
    ((finite_natCast_mem N).union (placesDividing ℚ l).toFinite)).subset
    fun z ⟨z_lc, z_cocycle, z_zero⟩ ↦
      ⟨⟨z_lc.continuous, z_cocycle⟩, Submodule.mem_pi.2 fun g hg ↦ z_zero g ?_⟩
  -- Inertia at a place prime to `N l` fixes the `N`-th roots of unity, so `g ∈ s`.
  show g ∈ s
  simp_all [inertiaAbove, Set.subset_def]
  grind [valuation_natCast_eq_one_iff, cyclotomicCharMod_eq_one_of_mem_inertiaGroup]

/-- Let `B` be a place of `Ω` above `l`, and let `a ≡ 1 mod N` be prime to `l`. Then some element
`i` of the inertia group of `B` has `cyc^e ψ (i) = a ^ e`. -/
lemma exists_inertia_cyclotomicPowDirichlet_eq {a : ℕ} (ha : l.Coprime a) (ha_one : a ≡ 1 [MOD N])
    (hB : B.valuation (l : Ω) < 1) (e : ℕ) :
    ∃ i ∈ inertiaGroup Gal(Ω/ℚ) B, (cyclotomicPowDirichlet l e ψ i).val = a ^ e := by
  -- Take `i` in inertia with `l`-adic cyclotomic character `a`.
  obtain ⟨i, hi, cyc_i⟩ := exists_inertia_cyclotomicChar_eq hB ha
  -- It fixes the roots of unity of order the `l`-part of `N`, since `a ≡ 1` modulo that number.
  have fix_l_part : i ∈ cycloGalGroup (ordProj[l] N) := Units.ext <| by
    simp [cyclotomicCharMod_prime_pow_eq, cyc_i,
      (ZMod.natCast_eq_natCast_iff a 1 _).2 (ha_one.of_dvd (N.ordProj_dvd l))]
  -- By rigidity it fixes all `N`-th roots of unity, so `ψ` contributes nothing.
  have hB_compl : B.valuation (ordCompl[l] N : ℕ) = 1 :=
    (N.coprime_ordCompl out (NeZero.ne N)).valuation_eq_one hB
  have fix_N : i ∈ cycloGalGroup N :=
    mem_cycloGalGroup_of_mem_inertiaGroup hi hB_compl (N.ordProj_mul_ordCompl_eq_self l) fix_l_part
  exact ⟨i, hi, by simp [cyclotomicPowDirichlet, cyc_i, mem_ker.1 fix_N]⟩

/-- A cocycle `x ∈ component l e ψ ν` vanishes at every `g` that fixes the `N m`-th roots of unity
and lies in the inertia group of a place `A` of `Ω` prime to `l`, above the place `t` of `ℚ`. -/
private lemma apply_eq_zero_of_mem_inertiaGroup_of_valuation_eq_one
    {x : Gal(Ω/ℚ) → QuotSpan ((l : O) ^ ν)} (hx : x ∈ component l e ψ ν) {A : ClosurePlace}
    {t : FinPlace ℚ} (hA : IsPlaceOver A t) (hA_l : A.valuation l = 1) {g : Gal(Ω/ℚ)}
    (hg : g ∈ cycloGalGroup (N * m)) (hg_inertia : g ∈ inertiaGroup Gal(Ω/ℚ) A) : x g = 0 := by
  have hg_N : g ∈ cycloGalGroup N := cyclotomicCharMod_eq_one_of_dvd ⟨_, rfl⟩ hg
  have hg_off : g ∈ inertiaAbove (placesDividing ℚ l)ᶜ :=
    ⟨t, hA.valuation_natCast_eq_one_iff.1 hA_l, A, hA, hg_inertia⟩
  exact apply_eq_zero_of_mem_vanishingCocycles hx (.inr ⟨hg_N, .inl hg_off⟩)

/-- Let `x ∈ component l e ψ ν` be killed by `m`, let `A` be a place of `Ω` above `l`, and let
`a ≡ 1 mod N` be prime to `l`. Then `(a ^ e - 1) • x g = 0` for every `g` that fixes the `N m`-th
roots of unity and lies in the decomposition group of `A`. -/
private lemma pow_sub_one_smul_apply_eq_zero_of_mem_decompGroup {a : ℕ} (ha : l.Coprime a)
    (ha_one : a ≡ 1 [MOD N]) {x : Gal(Ω/ℚ) → QuotSpan ((l : O) ^ ν)} (hx : x ∈ component l e ψ ν)
    (hx_tors : ∀ g : Gal(Ω/ℚ), m • x g = 0) {A : ClosurePlace} (hA : A.valuation l < 1)
    {g : Gal(Ω/ℚ)} (hg : g ∈ cycloGalGroup (N * m)) (hg_dec : g ∈ decompGroup Gal(Ω/ℚ) A) :
    (a ^ e - 1 : O) • x g = 0 := by
  -- Take `δ` in the inertia group of `A` with `cyc^e ψ (δ) = a ^ e`. The cocycle `x` vanishes on
  -- the commutator of `δ⁻¹` and `g`, so Sah's lemma gives `(Υ δ - 1) • x g = ((Υ g)⁻¹ - 1) • x δ⁻¹`
  -- for `Υ = cyc^e ψ`, and the right side is `0` because `g` acts trivially.
  obtain ⟨δ, hδ_inertia, hδ⟩ := exists_inertia_cyclotomicPowDirichlet_eq (ψ := ψ) ha ha_one hA e
  have hδ_dec : δ ∈ decompGroup Gal(Ω/ℚ) A := mem_decompGroup_of_mem_inertiaGroup hδ_inertia
  have h_comm_mem : (δ⁻¹ * g)⁻¹ * (g * δ⁻¹) ∈
      ↑(cycloGalGroup N) ∩ (inertiaAbove (placesDividing ℚ l)ᶜ ∪ Selmer.shaLocalSet l ℚ 1) :=
    ⟨by simp [mul_comm], .inr ⟨A, by simp_all [mul_comm, mul_mem]⟩⟩
  have h_sah : (((cyclotomicPowDirichlet l e ψ)⁻¹ δ⁻¹).val - 1) • x g =
      (((cyclotomicPowDirichlet l e ψ)⁻¹ g).val - 1) • x δ⁻¹ :=
    sah (apply_mul_of_mem_vanishingCocycles hx) δ⁻¹ g
      (apply_eq_zero_of_mem_vanishingCocycles hx (.inr h_comm_mem))
  simpa [hδ, hx_tors, sub_smul, cyclotomicPowDirichlet_smul_eq_self hg] using h_sah

/-- Let `x ∈ component l e ψ ν` be killed by `m`, let `φ` fix the `N m`-th roots of unity, and let
`σ` act on them by `u ∈ (ℤ/N m)ˣ`. Then `x (σ⁻¹ φ σ) = (u ^ e ψ(u)) • x φ`. -/
private lemma apply_conj_eq_smul_of_cyclotomicCharMod_eq {x : Gal(Ω/ℚ) → QuotSpan ((l : O) ^ ν)}
    (hx : x ∈ component l e ψ ν) (hx_tors : ∀ g : Gal(Ω/ℚ), m • x g = 0) {φ σ : Gal(Ω/ℚ)}
    (hφ : φ ∈ cycloGalGroup (N * m)) {u : (ZMod (N * m))ˣ}
    (hσ : cyclotomicCharMod Ω (N * m) σ = u) :
    x (σ⁻¹ * φ * σ⁻¹⁻¹) = (u.val.val ^ e * ψ u.val.val : O) • x φ := by
  -- The cocycle rule gives `x (σ⁻¹ φ σ) = Υ⁻¹ (σ⁻¹) • x φ = Υ σ • x φ` for `Υ = cyc^e ψ`, as `φ`
  -- acts trivially.
  have h_fix : ((cyclotomicPowDirichlet l e ψ)⁻¹ φ).val • x σ⁻¹⁻¹ = x σ⁻¹⁻¹ := by
    simp [cyclotomicPowDirichlet_smul_eq_self hφ (hx_tors _)]
  have h_cyc : (cyclotomicCharMod Ω (N * m) σ).val = (u.val.val : ℕ) := by simp [hσ]
  rw [cocycle_conj_eq_smul (apply_mul_of_mem_vanishingCocycles hx) h_fix]
  simpa using cyclotomicPowDirichlet_smul h_cyc (hx_tors φ)

/-- Let `x ∈ component l e ψ ν` be killed by `m`, and let `σ` fix the `N m`-th roots of unity and
satisfy `σ * σ = 1`. Then `2 • x σ = 0`. -/
private lemma two_smul_apply_eq_zero_of_mul_self_eq_one {x : Gal(Ω/ℚ) → QuotSpan ((l : O) ^ ν)}
    (hx : x ∈ component l e ψ ν) (hx_tors : ∀ g : Gal(Ω/ℚ), m • x g = 0) {σ : Gal(Ω/ℚ)}
    (hσ : σ ∈ cycloGalGroup (N * m)) (hσ_sq : σ * σ = 1) :
    (2 : O) • x σ = 0 := by
  -- `σ` acts trivially on `x σ`, so the cocycle rule gives `x (σ * (σ * σ)) = 3 • x σ`, while
  -- `σ * (σ * σ) = σ`.
  have h_val : x (σ * (σ * σ)) = x σ := by rw [hσ_sq, mul_one]
  simpa [apply_mul_of_mem_vanishingCocycles hx, hx_tors, two_smul,
    cyclotomicPowDirichlet_smul_eq_self hσ] using h_val

/-- Let `s u ∈ Gal(Ω/ℚ)` act on the `N m`-th roots of unity by `u ∈ (ℤ/N m)ˣ`, and let the
decomposition group of the place `B` fix them. If `w u` is a place of `ℚ(μ_{N m})` below
`(s u)⁻¹ • B` for each `u`, then the places `w u` are pairwise distinct. -/
private lemma injective_of_forall_isPlaceOver_inv_smul {s : (ZMod (N * m))ˣ → Gal(Ω/ℚ)}
    (hs : ∀ u : (ZMod (N * m))ˣ, cyclotomicCharMod Ω (N * m) (s u) = u)
    (dec_B : decompGroup Gal(Ω/ℚ) B ≤ cycloGalGroup (N * m))
    {w : (ZMod (N * m))ˣ → FinPlace (fixedFieldOf (cycloGalGroup (N * m)))}
    (hw : ∀ u : (ZMod (N * m))ˣ, IsPlaceOver ((s u)⁻¹ • B) (w u)) :
    Function.Injective w := by
  -- If `w u = w t`, some `g` over ℚ(μ_{N m}) carries `(s t)⁻¹ • B` to `(s u)⁻¹ • B`. Then
  -- `s u * g * (s t)⁻¹` fixes `B`, so it fixes the roots of unity, and `u = t`.
  intro u t hut
  obtain ⟨g, hg⟩ : ∃ g : cycloGalGroup (N * m), (g : Gal(Ω/ℚ)) • (s t)⁻¹ • B = (s u)⁻¹ • B :=
    (hw t).exists_smul (cycloGalGroup (N * m)) (by simpa only [hut] using hw u)
  have h_dec : s u * g * (s t)⁻¹ ∈ decompGroup Gal(Ω/ℚ) B :=
    MulAction.mem_stabilizer_iff.2 (by simp [mul_smul, hg])
  simpa [mem_ker.1, mul_inv_eq_one, hs] using dec_B h_dec

/-- Let `v` be a place of `ℚ` such that every place of `Ω` at which `v.q` is not a unit lies over
`v`, and let `B` be such a place. Let `s u ∈ Gal(Ω/ℚ)` act on the `N m`-th roots of unity by `u`,
and let `w u` be a place of `ℚ(μ_{N m})` below `(s u)⁻¹ • B`. Then every place `t` of `ℚ(μ_{N m})`
at which `v.q` is not a unit is one of the `w u`. -/
private lemma mem_range_of_valuation_lt_one {v : FinPlace ℚ}
    (over_v : ∀ A : ClosurePlace, A.valuation (v.q : Ω) < 1 → IsPlaceOver A v)
    (hB : B.valuation (v.q : Ω) < 1) {s : (ZMod (N * m))ˣ → Gal(Ω/ℚ)}
    (hs : ∀ u : (ZMod (N * m))ˣ, cyclotomicCharMod Ω (N * m) (s u) = u)
    {w : (ZMod (N * m))ˣ → FinPlace (fixedFieldOf (cycloGalGroup (N * m)))}
    (hw : ∀ u : (ZMod (N * m))ˣ, IsPlaceOver ((s u)⁻¹ • B) (w u))
    {t : FinPlace (fixedFieldOf (cycloGalGroup (N * m)))}
    (ht : (placeOver t).valuation (v.q : Ω) < 1) :
    t ∈ Set.range w := by
  -- Some `σ` carries a place above `t` to `B`. With `u` the action of `σ` on the roots of unity,
  -- `(s u)⁻¹ * σ` fixes them, so `(s u)⁻¹ • B` also lies above `t`, and `t = w u`.
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(Ω/ℚ), σ • placeOver t = B :=
    (over_v _ ht).exists_smul Gal(Ω/ℚ) (over_v B hB)
  let u : (ZMod (N * m))ˣ := cyclotomicCharMod Ω (N * m) σ
  let g : cycloGalGroup (N * m) := ⟨(s u)⁻¹ * σ, (eq_iff _).1 (hs u).symm⟩
  have h_over_g : IsPlaceOver (((s u)⁻¹ * σ : Gal(Ω/ℚ)) • placeOver t) t :=
    t.isPlaceOver_placeOver.smul g
  have h_over : IsPlaceOver ((s u)⁻¹ • B) t := by simpa [← hσ, smul_smul] using h_over_g
  exact ⟨u, (hw u).unique h_over⟩

/-- Artin reciprocity over `K = ℚ(μ_{N m})` at a prime `q ≡ 1 mod N m`, with `φ` a Frobenius at `B`
above `q`. The space `component l e ψ ν` consists of cocycles `Gal(Ω/ℚ) → O/l^ν` for `(cyc^e ψ)⁻¹`
under local conditions, including vanishing at `cmConj` and on inertia over `ℚ(μ_N)` away from `l`.
Let `x` in it be killed by `m`, and let `a ≡ 1 mod N` be prime to `l`. Let `y ∈ Kˣ` be, at each
place prime to `l q`, a unit times the `m`-th power of an element fixed by inertia, unless `x` kills
the decomposition group there. With `s u` acting on `μ_{N m}` by `u`, the orders `k u` of `s u • y`
at `B`, weighted by `u ^ e ψ(u)`, sum to a scalar killing `2 (a ^ e - 1) x φ`. -/
lemma artin_reciprocity_of_mem_component {a : ℕ} (ha : l.Coprime a) (ha_one : a ≡ 1 [MOD N])
    (hB : B.valuation q < 1) (hφ : IsFrob B q φ) {x : Gal(Ω/ℚ) → QuotSpan ((l : O) ^ ν)}
    (hx : x ∈ component l e ψ ν) (hq_one : q ≡ 1 [MOD N * m])
    (hx_tors : ∀ g : Gal(Ω/ℚ), m • x g = 0) {y : DiscreteUnits Ω}
    (hy : ∀ g : cycloGalGroup (N * m), galUnitsRep g y = y)
    (h_away : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) = 1 → A.valuation q = 1 →
      (∃ r : DiscreteUnits Ω,
        A.valuation (y - m • r).toMul = 1 ∧
        ∀ i ∈ inertiaGroup (cycloGalGroup (N * m)) A, galUnitsRep i r = r) ∨
        ∀ g ∈ decompGroup Gal(Ω/ℚ) A, x g = 0)
    {s : (ZMod (N * m))ˣ → Gal(Ω/ℚ)}
    (hs : ∀ u : (ZMod (N * m))ˣ, cyclotomicCharMod Ω (N * m) (s u) = u) :
    ∃ k : (ZMod (N * m))ˣ → ℤ,
      -- (a) `k u` is the order at `B` of the conjugate of `y` by `s u`
      (∀ u : (ZMod (N * m))ˣ, ordRat ℚ B (galUnitsRep (s u) y) = k u) ∧
      -- (b) the weighted sum of these orders kills `2 (a ^ e - 1) • x φ`
      (∑ u : (ZMod (N * m))ˣ, k u * (u.val.val ^ e * ψ u.val.val)) • (2 * (a ^ e - 1) : O) • x φ =
        0 := by
  -- Over `F = ℚ(μ_{N m})`, with group `G`, the map `g ↦ lam (d • x g)` is a character `χ` for each
  -- `lam` with values in `ℚ/ℤ`. Apply Artin's law `sum_ord_smul_frob_eq_zero` to `χ` and `y`: only
  -- the places above `q`, which lie below the conjugates `(s u)⁻¹ • B`, contribute.
  set d : O := 2 * (a ^ e - 1)
  let G : Subgroup Gal(Ω/ℚ) := cycloGalGroup (N * m)
  let F : IntermediateField ℚ Ω := fixedFieldOf G
  -- `v` is the place of `ℚ` at `q`; from here on `q` is `v.q`.
  obtain ⟨v, ⟨rfl, -⟩, -, over_v⟩ := exists_rat_place_of_prime (p := q) (Fact.out : q.Prime)
  -- `y` is fixed by `G`, so it comes from `Fˣ`; from here on `y` is that element of `Fˣ`.
  obtain ⟨y, rfl⟩ : ∃ y₀ : Fˣ, (ofBase G Ω (Additive.ofMul y₀) : DiscreteUnits Ω) = y :=
    ((ofBase_bijective G).surjective ⟨y, hy⟩).imp fun _ ↦ congrArg Subtype.val
  -- `q` splits completely in `F`; let `w u` be the place of `F` below `(s u)⁻¹ • B`.
  have dec_B : decompGroup Gal(Ω/ℚ) B ≤ G := decompGroup_le_cycloGalGroup hB hq_one
  have conj_over (u : (ZMod (N * m))ˣ) : IsPlaceOver ((s u)⁻¹ • B) v := (over_v B hB).smul (s u)⁻¹
  choose w hw _ using fun u ↦ (conj_over u).exists_above (L := F)
  have split (u : (ZMod (N * m))ˣ) :
      FinPlace.q (w u) = v.q ∧ ordRat F ((s u)⁻¹ • B) = ordRat ℚ ((s u)⁻¹ • B) :=
    ((conj_over u).ramification_in_tower G (hw u)).1
      (decompGroup_le_cycloGalGroup (conj_over u).valuation_q_lt_one hq_one)
  refine ⟨fun u ↦ -((w u).valuation F y).log, fun u ↦ ?_,
    eq_zero_of_forall_hom_eq_zero fun lam ↦ ?_⟩
  · show ordRat ℚ B (unitsRep (s u) (ofBase G Ω (Additive.ofMul y) : DiscreteUnits Ω)) =
      -((w u).valuation F y).log
    simpa [split, ← (conj_over u).ordRat_smul (s u)] using (hw u).ordRat_ofBase (Γ := G) y
  have h_lc : IsLocallyConstant fun g : Gal(Ω/ℚ) ↦ lam (d • x g) :=
    (isLocallyConstant_of_mem_vanishingCocycles hx).comp fun z ↦ lam (d • z)
  let χ : QZChar G := ⟨fun g ↦ lam (d • x g), h_lc.continuous.comp continuous_subtype_val,
    fun g h ↦ by simp [apply_mul_of_mem_vanishingCocycles hx,
      cyclotomicPowDirichlet_smul_eq_self g.prop, hx_tors]⟩
  have torsion : m • χ = 0 := by
    ext
    simp [χ, ← map_nsmul, smul_comm, hx_tors]
  -- `χ` kills complex conjugations `σ`, since `2 • x σ = 0` and `2 ∣ d`.
  have conj_zero (σ : G) (hσ : IsComplexConj σ) : χ.1 σ = 0 := by
    have hσ_sq : (σ : Gal(Ω/ℚ)) * σ = 1 := by simp [← Subgroup.coe_mul, hσ.mul_self]
    simp [χ, d, mul_comm (2 : O), mul_smul,
      two_smul_apply_eq_zero_of_mul_self_eq_one hx hx_tors σ.prop hσ_sq]
  -- Above `l`, `χ` kills the decomposition group, since `(a ^ e - 1) • x g = 0` there.
  have dec_zero (A : ClosurePlace) (hA : A.valuation l < 1) (g : G)
      (hg : (g : Gal(Ω/ℚ)) ∈ decompGroup Gal(Ω/ℚ) A) : χ.1 g = 0 := by
    simp [χ, d, mul_smul,
      pow_sub_one_smul_apply_eq_zero_of_mem_decompGroup ha ha_one hx hx_tors hA g.prop hg]
  -- `χ` is unramified: off `l`, `x` vanishes on inertia over `ℚ(μ_N)`.
  have unramified {A : ClosurePlace} {t : FinPlace ℚ} (hA : IsPlaceOver A t) (g : G)
      (hg : g ∈ inertiaGroup G A) : χ.1 g = 0 := by
    rcases (A.valuation_le_one l).eq_or_lt with h | h
    · simp [χ, apply_eq_zero_of_mem_inertiaGroup_of_valuation_eq_one hx hA h g.prop hg]
    · exact dec_zero A h g (mem_decompGroup_of_mem_inertiaGroup hg)
  -- The places `w u` are all the places of `F` above `q`.
  have unit_q (t : FinPlace F) (ht : t ∉ Set.range w) : (placeOver t).valuation v.q = 1 :=
    eq_of_le_of_not_lt (by simp) fun h ↦ ht (mem_range_of_valuation_lt_one over_v hB hs hw h)
  have hφ_G : φ ∈ G := dec_B (mem_decompGroup_of_isFrob hφ)
  let frob u : G := ⟨(s u)⁻¹ * φ * (s u)⁻¹⁻¹, (normal_ker _).conj_mem _ hφ_G _⟩
  -- The conjugate `frob u` of `φ` is a Frobenius element at `(s u)⁻¹ • B`, above `w u`.
  have frob_isFrob (u : (ZMod (N * m))ˣ) : IsFrob ((s u)⁻¹ • B) (w u).q (frob u) := by
    rw [(split u).left]
    exact hφ.conj (s u)⁻¹
  have reciprocity : ∑ u, -((w u).valuation F y).log • χ.1 (frob u) = 0 := by
    -- `χ` kills complex conjugations, hence the Artin symbol of `y`.
    refine sum_ord_smul_frob_eq_zero torsion
      (abelianLift_artinMap_principalIdele_eq_one χ y conj_zero)
      (injective_of_forall_isPlaceOver_inv_smul hs dec_B hw) hw frob_isFrob
      (fun u ↦ unramified (conj_over u)) fun t ht ↦ ?_
    -- At another place either `χ` kills the decomposition group, or `y` is a unit times an
    -- `m`-th power of an element fixed by inertia.
    have h_over : IsPlaceOver (placeOver t) t := t.isPlaceOver_placeOver
    rcases ((placeOver t).valuation_le_one l).eq_or_lt with h | h
    · rcases h_away _ h (unit_q t ht) with h_unit | h_dec
      · exact .inr ⟨h_unit, unramified h_over.isPlaceOver_below⟩
      · exact .inl ((h_over.artinAt_trivial_iff_decompGroup_le χ).2
          (fun g hg ↦ show χ.1 g = 0 by simp [χ, h_dec g hg]) _)
    · exact .inl ((h_over.artinAt_trivial_iff_decompGroup_le χ).2 (dec_zero _ h) _)
  -- Each `x (frob u)` is `(u ^ e * ψ u) • x φ`, so `reciprocity` is the claim.
  have frob_val (u : (ZMod (N * m))ˣ) : x (frob u) = (u.val.val ^ e * ψ u.val.val : O) • x φ :=
    apply_conj_eq_smul_of_cyclotomicCharMod_eq hx hx_tors hφ_G (hs u)
  rw [← reciprocity]
  simp [sum_smul, χ, frob_val, smul_comm d, mul_smul, ← zsmul_eq_mul]

/-- Hilbert 90 for a cocycle read through `L : M →+ Ωˣ`. Let `κ` be a cocycle for `cyc^(e+1) ψ` with
values in `M`, killed by `l`. Then on the Galois group over ℚ(μ_{N l}) the map `g ↦ L (κ g)` is a
coboundary: `L (κ g) = g • r - r` for some `r ∈ Ωˣ` (the group `Ωˣ` is written additively). -/
private lemma exists_apply_eq_galUnitsRep_sub {κ : Gal(Ω/ℚ) → M} {s : Set Gal(Ω/ℚ)}
    (hκ : κ ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) M s)
    (hκ_tors : ∀ g : Gal(Ω/ℚ), l • κ g = 0) (L : M →+ DiscreteUnits Ω) :
    ∃ r : DiscreteUnits Ω, ∀ g : cycloGalGroup (N * l), L (κ g) = galUnitsRep g r - r := by
  have h_lc : IsLocallyConstant (L ∘ κ) := (isLocallyConstant_of_mem_vanishingCocycles hκ).comp L
  refine hilbert90_unitsRep ⟨_, h_lc.continuous.comp continuous_subtype_val, fun g h ↦ ?_⟩
  -- `g` fixes the root of unity `L (κ h)` and acts trivially on `κ h`.
  show L (κ (g * h)) = L (κ g) + unitsRep (g : Gal(Ω/ℚ)) (L (κ h))
  rw [cyclotomicCharMod_eq_one_iff.1 g.2]
  · simp [hκ_tors, apply_mul_of_mem_vanishingCocycles hκ, cyclotomicPowDirichlet_smul_eq_self g.2]
  · simp [mul_smul, ← map_nsmul, hκ_tors]

/-- Let `z` be an element of `M`, let `b` be a basis of `O ∙ z` over `ZMod l`, and let `j ∈ ZMod l`.
Suppose that for every unit `u` modulo `N l` the vector with coordinates `m i u * j` in the basis
`b`, scaled by `u ^ e ψ(u)`, is `z`. Suppose also that each weighted sum `∑_u m i u u ^ e ψ(u)`
kills a nonzero `c`, and that the totient of `N l` is a unit of `O`. Then `z = 0`. -/
private lemma eq_zero_of_forall_smul_equivFun_symm_eq {z : M} [Module (ZMod l) (O ∙ z)]
    (b : Module.Basis (Fin (Module.finrank (ZMod l) (O ∙ z))) (ZMod l) (O ∙ z))
    (m : Fin (Module.finrank (ZMod l) (O ∙ z)) → (ZMod (N * l))ˣ → ℤ) (j : ZMod l)
    (h_coords : ∀ u : (ZMod (N * l))ˣ,
      (u.val.val ^ e * ψ u.val.val) • b.equivFun.symm (m · u * j) = z)
    {Y : Type} [AddCommGroup Y] [Module O Y] {c : Y} (hc : c ≠ 0)
    (h_kill : ∀ i : Fin (Module.finrank (ZMod l) (O ∙ z)),
      (∑ u : (ZMod (N * l))ˣ, m i u * (u.val.val ^ e * ψ u.val.val : O)) • c = 0)
    (h_totient : IsUnit ((N * l).totient : O)) :
    z = 0 := by
  -- The weighted sums kill `c ≠ 0`, so they lie in the maximal ideal. Summing `h_coords` over the
  -- units `u` gives `t • z = φ(N l) • z` for some `t` in the maximal ideal.
  obtain ⟨t, t_mem, ht⟩ : ∃ t ∈ maximalIdeal O,
      t • z = ∑ i, (∑ u, m i u * (u.val.val ^ e * ψ u.val.val)) • ((j • b i : O ∙ z) : M) :=
    mem_smul_span_singleton.1 <| sum_mem fun i _ ↦
      (maximalIdeal O).smul_mem_smul (fun h ↦ hc (h.smul_eq_zero.1 (h_kill i))) (j • b i).prop
  have unit : IsUnit (t - (N * l).totient) :=
    by_contra fun h ↦ (sub_mem_iff_right _ t_mem).1 h h_totient
  have sum_coords : ∑ u : (ZMod (N * l))ˣ,
      (((u.val.val ^ e * ψ u.val.val) • b.equivFun.symm (m · u * j) : O ∙ z) : M) =
        ∑ u : (ZMod (N * l))ˣ, z :=
    sum_congr rfl fun u _ ↦ h_coords u
  rw [← unit.smul_eq_zero, sub_smul, sub_eq_zero, ht]
  simpa [smul_sum, sum_smul, sum_comm (γ := _ˣ), ← zsmul_eq_mul, Nat.cast_smul_eq_nsmul,
    smul_comm (_ : O)] using sum_coords

/-- Reciprocity modulo `l`, when the totient of `N l` is a unit of `O`. The space
`component l e ψ ν` consists of cocycles `Gal(Ω/ℚ) → O/l^ν` for `(cyc^e ψ)⁻¹` under local
conditions, including vanishing at `cmConj` and on inertia over `ℚ(μ_N)` away from `l`. Let `φ` be a
Frobenius at `B` above a prime `q ≡ 1 mod N l`. Let `l` kill `x ∈ component l e ψ ν` and a cocycle
`κ` for `cyc ^ (e + 1) ψ` zero on `inertiaOff N l T`: the elements over `ℚ(μ_N)` in the inertia
group of a place above neither `l` nor a prime of `T`. Let each place prime to `q` lie above no
prime of `T`, or have its decomposition group killed by `x`. If `2 (a ^ e - 1) x φ ≠ 0` for some
`a ≡ 1 mod N` prime to `l`, then `κ` vanishes on the inertia group of `B`. -/
lemma reciprocity_mod_ell {a : ℕ} (ha : l.Coprime a) (ha_one : a ≡ 1 [MOD N])
    (hB : B.valuation q < 1) (hφ : IsFrob B q φ) {x : Gal(Ω/ℚ) → QuotSpan ((l : O) ^ ν)}
    (hx : x ∈ component l e ψ ν) [Finite M] (h_totient : IsUnit ((N * l).totient : O))
    (hq_one : q ≡ 1 [MOD N * l]) (hx_tors : l • x = 0) {κ : Gal(Ω/ℚ) → M} {T : Finset Nat.Primes}
    (hκ : κ ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) M (inertiaOff N l T))
    (hκ_tors : ∀ g : Gal(Ω/ℚ), l • κ g = 0) (hτ : τ ∈ inertiaGroup Gal(Ω/ℚ) B)
    (h_away : ∀ A : ValuationSubring Ω, A.valuation (q : Ω) = 1 →
      (∀ r ∈ T, ¬A.valuation r < 1) ∨ ∀ g ∈ decompGroup Gal(Ω/ℚ) A, x g = 0)
    (h_ne : (2 * (a ^ e - 1) : O) • x φ ≠ 0) :
    κ τ = 0 := by
  -- Kummer theory turns each coordinate of `κ` in the `𝔽_l`-space `O ∙ κ τ` into an element
  -- `l • r i` of `ℚ(μ_{N l})`; the orders `m i u` at `B` of its conjugates give the coordinates of
  -- `κ τ`. By `artin_reciprocity_of_mem_component` their weighted sums lie in the maximal ideal, so
  -- `κ τ` is killed by a unit.
  have h_zmodModule : Module (ZMod l) (O ∙ κ τ) :=
    AddCommGroup.zmodModule (by simp [mem_span_singleton, smul_comm, hκ_tors])
  have b := Module.finBasis (ZMod l) (O ∙ κ τ)
  have τ_fix : cyclotomicCharMod Ω (N * l) τ = 1 :=
    mem_ker.1 (decompGroup_le_cycloGalGroup hB hq_one (mem_decompGroup_of_mem_inertiaGroup hτ))
  obtain ⟨v, hv, -, ord_q⟩ := exists_isPlaceOver_prime hB
  choose σ hσ using cyclotomicCharMod_surjective (N * l)
  -- `μ` identifies `ℤ/l` with the `l`-th roots of unity; `τ` moves an `l`-th root `π` of `q`
  -- by `μ j`.
  set μ : ZMod l →+ DiscreteUnits Ω := (rootPowHom Ω l).val with hμ
  obtain ⟨-, μ_range⟩ := (rootPowHom Ω l).property
  obtain ⟨π, hπ⟩ := (ofNeZero (q : Ω) (NeZero.ne _)).exists_nsmul (NeZero.ne l)
  obtain ⟨j, hj⟩ : galUnitsRep τ π - π ∈ μ.range :=
    (μ_range _).2 (DiscreteUnits.ext (by simp [smul_sub, ← map_nsmul, hπ]))
  -- Extend the coordinates, read in `μ_l`, to `M`; by Hilbert 90 `L i ∘ κ` is a coboundary.
  have extend i : ∃ L : M →+ DiscreteUnits Ω, ∀ y hy, L y = μ (b.repr ⟨y, hy⟩ i) := by
    simpa [DFunLike.ext_iff] using
      exists_extend (O ∙ κ τ).subtype.toAddMonoidHom (μ.comp (b.coord i)) (by aesop_cat)
  choose L hL using extend
  have kummer i :
      ∃ r : DiscreteUnits Ω, ∀ g : cycloGalGroup (N * l), L i (κ g) = galUnitsRep g r - r :=
    exists_apply_eq_galUnitsRep_sub hκ hκ_tors (L i)
  choose r hr using kummer
  have reciprocity i : ∃ m : (ZMod (N * l))ˣ → ℤ,
      (∀ u, ordRat ℚ B (galUnitsRep (σ u) (l • r i)) = m u) ∧
      (∑ u, m u * (u.val.val ^ e * ψ u.val.val)) • (2 * (a ^ e - 1) : O) • x φ = 0 := by
    refine artin_reciprocity_of_mem_component ha ha_one hB hφ hx hq_one (congrFun hx_tors)
      (fun g ↦ ?_)
      (fun A hAl hAq ↦ ?_) hσ
    · simp [← add_eq_of_eq_sub (hr i g), ← map_nsmul, hκ_tors]
    · -- At a place off `l` and `T` the cocycle `κ` kills inertia, which therefore fixes `r i`.
      refine (h_away A hAq).imp_left fun off_T ↦ ⟨r i, by simp, fun g hg ↦ ?_⟩
      have hκ_g : κ g = 0 := apply_eq_zero_of_mem_vanishingCocycles hκ
        ⟨A, ⟨cyclotomicCharMod_eq_one_of_dvd (N.dvd_mul_right l) g.prop, hAl, hg⟩, off_T⟩
      simp [← sub_eq_zero, ← hr, hκ_g]
  choose m hm m_sum using reciprocity
  -- For each `u`, the `m i u * j` are the coordinates of `κ τ` up to the weight `u ^ e * ψ u`.
  have coords (u : (ZMod (N * l))ˣ) :
      (u.val.val ^ e * ψ u.val.val) • b.equivFun.symm (m · u * j) = κ τ := by
    have cyc_u : (cyclotomicCharMod Ω (N * l) (σ u)).val = u.val.val := by simp [hσ]
    have κ_conj :
        κ ((σ u)⁻¹ * τ * (σ u)⁻¹⁻¹) = (cyclotomicPowDirichlet l (e + 1) ψ (σ u)⁻¹).val • κ τ :=
      cocycle_conj_eq_smul (apply_mul_of_mem_vanishingCocycles hκ)
        (cyclotomicPowDirichlet_smul_eq_self τ_fix (hκ_tors _)).left
    let y : O ∙ κ τ := ⟨_, mem_span_singleton.2 ⟨_, κ_conj.symm⟩⟩
    -- `l • (m i u • π - σ u • r i)` is a unit at `B`, so `τ` moves `m i u • π - σ u • r i` by a
    -- principal unit; it moves it by the root of unity `μ (m i u * j - u * b.repr y i)`.
    have coord i : m i u * j = b.equivFun (u.val.val • y) i := by
      have unit : B.valuation (l • (m i u • π - galUnitsRep (σ u) (r i))).toMul.1 = 1 := by
        simp [↓← hv.ordRat_eq_zero_iff, smul_comm, hπ, ord_q, smul_sub, ← hm]
      refine eq_of_mem_principalUnits
        (hq_one.of_mul_left.coprime_of_modEq_one.valuation_eq_one hB) ?_
      -- `using!` matches the conjugation by `σ u` inside `galUnitsRep`.
      simpa [y, smul_smul, ← hμ, hj, τ_fix, hr _ ⟨_, _⟩, ← zsmul_eq_mul, smul_sub, ↓map_nsmul, ← hL,
        ← cyclotomicCharMod_eq_of_dvd _ cyc_u, sub_sub_sub_comm, map_cyclotomicCharMod_mul] using!
        hτ.sub_nsmul_mem_principalUnits unit
    rw [b.equivFun.symm_apply_eq.2 (funext coord)]
    calc (u.val.val ^ e * ψ u.val.val : O) • u.val.val • y.val
        = (cyclotomicPowDirichlet l (e + 1) ψ (σ u)).val • y.val := by
          rw [← Nat.cast_smul_eq_nsmul O, smul_smul, mul_right_comm, ← pow_succ,
            cyclotomicPowDirichlet_smul cyc_u (hκ_tors _)]
      _ = κ τ := by simp [y, ↓κ_conj, smul_smul]
  -- By `m_sum i` the weighted sums kill the nonzero `2 (a ^ e - 1) • x φ`; with `coords` this
  -- makes `κ τ` killed by a unit.
  exact eq_zero_of_forall_smul_equivFun_symm_eq b m j coords h_ne m_sum h_totient

end ReciprocityLaw

/-!
## Stickelberger and Kolyvagin bounds for the components

The proofs of `New.OddPart.nsmul_component_eq_zero` and
`New.OddPart.exists_detecting_points_component` use Chebotarev's theorem
(`New.OddPart.exists_isFrob_notMem`) to find a Frobenius element at which a cocycle does not vanish.
They also use the reciprocity laws.
-/

section ComponentBound

open NeZero ZMod Selmer Ideal.Quotient Function QZ Finset Nat HasEnoughRootsOfUnity

variable {O : Type} [CommRing O]
  {N l e X ν : ℕ} [NeZero N] [L : Fact l.Prime] [PadicIntegerRing O l] {ψ : DirichletCharacter O N}

/-- If neither of the open subgroups `U`, `V` contains the Galois group over `ℚ(ζ_m)`, then some
Frobenius element at a place above a prime `q ≡ 1 mod m` lies outside both. -/
lemma exists_isFrob_notMem (m : ℕ) [NeZero m] {U V : OpenSubgroup Gal(Ω/ℚ)}
    (hU : ¬cycloGalGroup m ≤ U) (hV : ¬cycloGalGroup m ≤ V) :
    ∃ q : Primes, q ≡ 1 [MOD m] ∧
      ∃ (A : ClosurePlace) (σ : Gal(Ω/ℚ)),
        A.valuation (q : Ω) < 1 ∧ IsFrob A q σ ∧ σ ∉ U ∧ σ ∉ V := by
  -- A group is not the union of two proper subgroups, so the open set below is not empty.
  have h_ne : ((cycloGalGroup m : Set Gal(Ω/ℚ)) \ (U ∪ V)).Nonempty :=
    Set.sdiff_nonempty.2 fun h_sub ↦ (SubgroupClass.subset_union.1 h_sub).elim hU hV
  -- Chebotarev: it contains a Frobenius at a prime not dividing `m`.
  obtain ⟨v, hv, h_prime, A, hA, σ, ⟨hσ, hσ_not⟩, h_frob, -⟩ :=
    chebotarev (isOpen_ker_cyclotomicCharMod.out.sdiff (U.isClosed.union V.isClosed)) h_ne
      (finite_natCast_mem m)
  exact ⟨⟨v.q, h_prime⟩,
    (h_frob.mem_ker_cyclotomicCharMod_iff (hA.valuation_natCast_eq_one_iff.2 hv)).1 hσ,
    A, σ, hA.valuation_q_lt_one, h_frob, not_or.1 hσ_not⟩

lemma exists_place_above (r : Primes) : ∃ A : ClosurePlace, A.valuation (r : Ω) < 1 :=
  have : Fact (r : ℕ).Prime := ⟨r.prop⟩
  ⟨_, valuation_comap_intQpBar_lt_one (IsAlgClosed.lift : Ω →ₐ[ℚ] PadicAlgCl r).toRingHom⟩

/-- The function `x` on the Galois group vanishes on the decomposition group of every place above
the prime `r`. -/
def IsTrivialAbove {M : Type} [Zero M] (x : Gal(Ω/ℚ) → M) (r : Primes) : Prop :=
  ∀ A : ClosurePlace, A.valuation (r : Ω) < 1 → ∀ g ∈ decompGroup Gal(Ω/ℚ) A, x g = 0

omit [PadicIntegerRing O l] in
/-- The sum `∑ ⌊a x / (N lⁿ⁺¹)⌋ x ^ e ψ(x)` over `x < N lⁿ⁺¹` splits into its part over the units
modulo `N lⁿ⁺¹` and `l ^ e ψ(l)` times the same sum at level `N lⁿ`. -/
lemma sum_range_eq_sum_units_add (a n : ℕ) :
    ∑ x ∈ range (N * l ^ (n + 1)), (a * x / (N * l ^ (n + 1)) : ℕ) * (x ^ e * ψ x : O) =
      ∑ u : (ZMod (N * l ^ (n + 1)))ˣ,
          (a * ZMod.val u.val / (N * l ^ (n + 1)) : ℕ) *
            (ZMod.val u.val ^ e * ψ (ZMod.val u.val) : O) +
        l ^ e * ψ l * ∑ x ∈ range (N * l ^ n), (a * x / (N * l ^ n) : ℕ) * (x ^ e * ψ x : O) := by
  -- A number below `N lⁿ⁺¹` at which `ψ` is not zero is a unit or a multiple of `l`.
  have h_level : N * l ^ (n + 1) = l * (N * l ^ n) := by ring
  have h_lt (y : ℕ) : l * y < N * l ^ (n + 1) ↔ y < N * l ^ n := by simp [h_level, L.out.pos]
  have h_inj : Injective
      (Sum.elim (fun u : (ZMod (N * l ^ (n + 1)))ˣ ↦ u.val.val) fun y ↦ l * y) :=
    ((ZMod.val_injective _).comp Units.val_injective).sumElim (mul_right_injective₀ (NeZero.ne l))
      fun u y h_eq ↦ L.out.ne_one
        (eq_one_of_dvd_coprimes (val_coe_unit_coprime u) ⟨y, h_eq⟩ ⟨_, h_level⟩)
  rw [← sum_of_injOn (s := univ.disjSum (range (N * l ^ n))) _ h_inj.injOn ?_
    (fun x hx h_out ↦ ?_) fun _ _ ↦ rfl]
  · -- The term at `l y` is `l ^ e ψ(l)` times the term at `y` of level `N lⁿ`.
    have h_floor (y : ℕ) : a * (l * y) / (N * l ^ (n + 1)) = a * y / (N * l ^ n) := by
      rw [h_level, mul_left_comm, Nat.mul_div_mul_left _ _ L.out.pos]
    simp only [sum_disjSum, Sum.elim_inl, Sum.elim_inr, h_floor, mul_sum, Nat.cast_mul, map_mul]
    exact congrArg _ (sum_congr rfl fun y _ ↦ by ring)
  · -- Both kinds of numbers lie below `N lⁿ⁺¹`.
    simp [Set.MapsTo, val_lt, h_lt]
  · -- At the other numbers `ψ` is zero.
    suffices h_nonunit : ¬IsUnit (x : ZMod N) by simp [ψ.map_nonunit h_nonunit]
    refine fun h_unit ↦ h_out ?_
    by_cases h_dvd : l ∣ x
    · obtain ⟨y, rfl⟩ := h_dvd
      exact ⟨.inr y, by simpa [h_lt] using hx, rfl⟩
    · have h_cop : x.Coprime (N * l ^ (n + 1)) :=
        .mul_right ((isUnit_iff_coprime x N).1 h_unit) (L.out.coprime_pow_of_not_dvd h_dvd)
      exact ⟨.inl (unitOfCoprime x h_cop), by simpa [mod_eq_iff_lt, NeZero.ne] using hx⟩

/-- Let `O` be the integer ring of a finite extension of `ℚ_l` (`PadicIntegerRing O l`), and let `X`
have the Stickelberger property `IsStickelbergerBound N e X`: for `a ≡ 1 mod N`, for some `w` that
does not depend on `m`, `(a ^ (e + 1) - 1) X` is congruent modulo every `m` prime to `a` to `2 w`
times the Stickelberger sum at level `N m`. Let `cyc ^ e ψ` be odd (`hc`: its value at the complex
conjugation `cmConj` is `-1`), let `e ≠ 0`, and let `a ≡ 1 mod N` be prime to `l`. Then in
`O / lⁿ O` the sum of `floorDiff a (u / (N lⁿ)) u ^ e ψ(u)` over the units `u` modulo `N lⁿ` divides
`(a ^ (e + 1) - 1) X`. Here `floorDiff a t = ⌊a ⟨t⟩⌋ - ⌊a ⟨-t⟩⌋`, where `⟨t⟩ ∈ [0, 1)` represents
`t ∈ ℚ/ℤ`. The multiples of `l` give the Euler factor `1 - l ^ e ψ(l)`, a unit modulo `lⁿ`. -/
lemma sum_floorDiff_dvd (h : IsStickelbergerBound N e X)
    (hc : cyclotomicPowDirichlet l e ψ cmConj = -1)
    (he_ne_zero : e ≠ 0) (n : ℕ) {a : ℕ} (ha : a ≡ 1 [MOD N]) (hla : l.Coprime a) :
    ((∑ x : (ZMod (N * l ^ n))ˣ, floorDiff a (ofZMod (N * l ^ n) x) *
        ((x : ZMod (N * l ^ n)).val ^ e * ψ (x : ZMod (N * l ^ n)).val) : O) :
      QuotSpan (l ^ n : O)) ∣ ((a ^ (e + 1) - 1) * X : O) := by
  -- `cmConj` inverts roots of unity, so `hc` says that `(-1) ^ e * ψ (-1) = -1`.
  have h_odd (y : ZMod N) : -((-1) ^ e * ψ y) = ψ (-y) := by
    have h_mul :
        ((cyclotomicPowDirichlet l e ψ cmConj : Oˣ) : O) * -ψ (-y) = ((-1 : Oˣ) : O) * -ψ (-y) := by
      rw [hc]
    simpa [cyclotomicPowDirichlet, isComplexConj_cmConj.cyclotomicChar_eq_neg_one,
      isComplexConj_cmConj.cyclotomicCharMod_eq_neg_one, mul_assoc, ← map_mul] using h_mul
  have h_nil : (l : QuotSpan (l ^ n : O)) ^ n = 0 := mk_singleton_self _
  rcases n with - | n
  · -- Modulo `l ^ 0 = 1` the ring is trivial.
    have h_subsingleton : Subsingleton (QuotSpan (l ^ 0 : O)) :=
      subsingleton_of_zero_eq_one (h_nil.symm.trans (pow_zero _))
    exact ⟨0, Subsingleton.elim _ _⟩
  -- `T m` is the sum of `IsStickelbergerBound` at level `N m`, and `U` is the part of `T lⁿ⁺¹`
  -- over the units modulo `N lⁿ⁺¹`.
  let T (m : ℕ) : O := ∑ x ∈ range (N * m), ↑(a * x / (N * m)) * (x ^ e * ψ x)
  let U : O := ∑ u : (ZMod (N * l ^ (n + 1)))ˣ,
    ↑(a * u.1.val / (N * l ^ (n + 1))) * (u.1.val ^ e * ψ u.1.val)
  have h_split : T (l ^ (n + 1)) = U + l ^ e * ψ l * T (l ^ n) := sum_range_eq_sum_units_add a n
  -- Modulo `lⁿ⁺¹` our sum is `2 U`: `floorDiff` is a difference of two integer parts, and `u ↦ -u`
  -- changes the sign of `u ^ e * ψ u`.
  have h_twice : ((∑ u : (ZMod (N * l ^ (n + 1)))ˣ, floorDiff a (ofZMod _ u.1) *
      (u.1.val ^ e * ψ u.1.val) : O) : QuotSpan (l ^ (n + 1) : O)) = 2 * U := by
    have h_char : ringChar (QuotSpan (l ^ (n + 1) : O)) ∣ N * l ^ (n + 1) :=
      ringChar.dvd (by simp [h_nil])
    simp only [floorDiff, ↓← map_neg, ofZMod_apply, QZ.fracRep_mk, mul_div, mod_eq_of_lt, val_lt,
      Int.fract_div_natCast_eq_div_natCast_mod]
    norm_cast
    simp [-natCast_val, U, two_mul, sub_mul]
    nth_rw 2 [← neg_bijective.sum_comp]
    simp [← h_odd, ← mul_assoc, ← mul_pow, h_char]
  -- Use `IsStickelbergerBound` at the levels `lⁿ⁺¹` and `lⁿ`. As `e ≠ 0`, the factor `l ^ e` turns
  -- the congruence modulo `lⁿ` into one modulo `lⁿ⁺¹`.
  have hψ_odd : ψ (-1) = -(-1) ^ e := by simp [← h_odd]
  obtain ⟨w, hw⟩ := h.exists_natCast_dvd_sub_mul_sum ha O ψ hψ_odd
  obtain ⟨x, hx⟩ : (l ^ (n + 1) : O) ∣ (a ^ (e + 1) - 1) * X - 2 * w * T (l ^ (n + 1)) := by
    simpa only [Nat.cast_pow] using hw (l ^ (n + 1)) (hla.pow_left (n + 1))
  obtain ⟨y, hy⟩ : (l ^ n : O) ∣ (a ^ (e + 1) - 1) * X - 2 * w * T (l ^ n) := by
    simpa only [Nat.cast_pow] using hw (l ^ n) (hla.pow_left n)
  have h_euler : ((1 - l ^ e * ψ l) * ((a ^ (e + 1) - 1) * X) : O) =
      2 * w * U + l ^ (n + 1) * (x - l ^ (e - 1) * ψ l * y) := by
    obtain ⟨e, rfl⟩ : ∃ k : ℕ, e = k + 1 := exists_eq_add_one_of_ne_zero he_ne_zero
    rw [add_tsub_cancel_right]
    linear_combination hx - l ^ (e + 1) * ψ l * hy + 2 * w * h_split
  -- The Euler factor is a unit modulo `lⁿ⁺¹`, because `l ^ e * ψ l` is nilpotent there.
  obtain ⟨G, hG⟩ : (1 - l ^ e * ψ l : QuotSpan (l ^ (n + 1) : O)) ∣ 1 := by
    have h_dvd : (1 - l ^ e * ψ l : QuotSpan (l ^ (n + 1) : O)) ∣ 1 - (l ^ e * ψ l) ^ (n + 1) :=
      one_sub_dvd_one_sub_pow _ (n + 1)
    rwa [mul_pow, pow_right_comm, h_nil, zero_pow he_ne_zero, zero_mul, sub_zero] at h_dvd
  have h_euler_mod :
      (((1 - l ^ e * ψ l) * ((a ^ (e + 1) - 1) * X) : O) : QuotSpan (l ^ (n + 1) : O)) =
        ((2 * w * U + l ^ (n + 1) * (x - l ^ (e - 1) * ψ l * y) : O) :
          QuotSpan (l ^ (n + 1) : O)) := by
    rw [h_euler]
  use w * G
  rw [h_twice]
  -- Push the reduction modulo `lⁿ⁺¹` through both equations; there `lⁿ⁺¹ = 0`.
  simp only [map_mul, map_sub, map_add, map_pow, map_natCast, map_one, map_ofNat, h_nil, zero_mul,
    add_zero] at h_euler_mod ⊢
  linear_combination G * h_euler_mod + (a ^ (e + 1) - 1) * X * hG

private lemma ne_zero_of_coprime {a : ℕ} (hla : l.Coprime a) : a ≠ 0 := by
  rintro rfl
  exact L.out.ne_one ((Nat.coprime_zero_right l).1 hla)

/-- An analogue of Stickelberger's theorem. Let `X` have the Stickelberger property
`IsStickelbergerBound N e X` (a divisibility for each prime and a congruence for the Stickelberger
sums), let `cyc ^ e ψ` be odd (its value at the complex conjugation `cmConj` is `-1`), and let
`e ≠ 0`. Then `4 X²` kills every cocycle `z` in `component l e ψ ν`, the locally constant cocycles
`Gal(Ω/ℚ) → O/l^ν` for `(cyc ^ e ψ)⁻¹` that vanish at `cmConj` and at the elements of
`Gal(Ω/ℚ(μ_N))` lying in an inertia group at a place prime to `l` or in `shaLocalSet l ℚ 1`. -/
lemma nsmul_component_eq_zero (h_bound : IsStickelbergerBound N e X)
    (hc : cyclotomicPowDirichlet l e ψ cmConj = -1) (he_ne_zero : e ≠ 0)
    {z : Gal(Ω/ℚ) → QuotSpan (l ^ ν : O)} (hz : z ∈ component l e ψ ν) :
    (4 * X * X) • z = 0 := by
  -- At a Frobenius `σ` above `p ≡ 1 mod N l ^ ν`, Artin's law for a Jacobi sum shows that the
  -- Stickelberger sum kills `2 (a ^ e - 1) z σ`, hence `2 X² z σ = 0`. If `4 X² z ≠ 0`, Chebotarev
  -- gives such a `σ` with `2 X² z σ ≠ 0`.
  by_contra h_ne
  -- The character of `z` is `-1` at `cmConj`, so `not_cycloGalGroup_le_openCocycleKer` asks for
  -- `-2 • 2 X² z ≠ 0`.
  have h_conj_zero : ((2 * X * X) • z) cmConj = 0 := by
    simp [apply_eq_zero_of_mem_vanishingCocycles hz (Set.mem_insert cmConj _)]
  have h_char : ((cyclotomicPowDirichlet l e ψ)⁻¹ cmConj : O) - 1 = -(2 : ℕ) := by norm_num [hc]
  have h_visible : ¬cycloGalGroup (N * l ^ ν) ≤ openCocycleKer (nsmul_mem hz (2 * X * X)) := by
    refine not_cycloGalGroup_le_openCocycleKer _ cmConj h_conj_zero ?_ _
    rwa [h_char, neg_smul, cast_smul_eq_nsmul, smul_smul, neg_ne_zero, ← mul_assoc, ← mul_assoc]
  obtain ⟨p, hp : p ≡ 1 [MOD N * l ^ ν], B, σ, hB : B.valuation (p : Ω) < 1, hσ : IsFrob B p σ,
      hzσ : ((2 * X * X) • z) σ ≠ 0, -⟩ :=
    exists_isFrob_notMem (N * l ^ ν) h_visible h_visible
  obtain ⟨a, ha, hla, h_dvd⟩ := h_bound.exists_modEq_one_coprime_dvd L.out
  obtain ⟨b, hX⟩ : ∃ b : ℕ, X = (a ^ e - 1) * (a ^ (e + 1) - 1) * b := h_dvd
  -- The Jacobi sum `J (1 / (N l ^ ν))` is a unit off `p`, and its conjugates have the orders
  -- `μ u = floorDiff a (u / (N l ^ ν))` at `B`.
  obtain ⟨J, hJ⟩ := exists_isJacobiFamily hB a
  have hJ_level : IsJacobiFamily p B a (N * l ^ ν) J := hJ (N * l ^ ν) hp
  have h_tors (u : ZMod (N * l ^ ν)) : (N * l ^ ν) • ofZMod (N * l ^ ν) u = 0 := by
    rw [← map_nsmul, nsmul_eq_mul, natCast_self, zero_mul, map_zero]
  have hz_tors (g : Gal(Ω/ℚ)) : l ^ ν • z g = 0 := nsmul_quot_eq_zero dvd_rfl (z g)
  have hJ_fix (g : cycloGalGroup (N * l ^ ν)) :
      galUnitsRep g (J (ofZMod (N * l ^ ν) 1)) = J (ofZMod (N * l ^ ν) 1) := by
    rw [hJ_level.galUnitsRep_apply (h_tors 1) g 1 (by simp [MonoidHom.mem_ker.1 g.prop]),
      one_nsmul]
  have hJ_away (A : ValuationSubring Ω) (_hA_l : A.valuation (l : Ω) = 1)
      (hA_p : A.valuation (p : Ω) = 1) :
      (∃ r : DiscreteUnits Ω, A.valuation (J (ofZMod (N * l ^ ν) 1) - l ^ ν • r).toMul = 1 ∧
        ∀ i ∈ inertiaGroup (cycloGalGroup (N * l ^ ν)) A, galUnitsRep i r = r) ∨
        ∀ g ∈ decompGroup Gal(Ω/ℚ) A, z g = 0 :=
    .inl ⟨0, by simpa using hJ_level.valuation_eq_one (h_tors 1) A hA_p, fun i _ ↦ map_zero _⟩
  -- Apply Artin's law with representatives of the units modulo `N l ^ ν` in the Galois group.
  have h_reps (u : (ZMod (N * l ^ ν))ˣ) : cyclotomicCharMod Ω (N * l ^ ν)
      (surjInv (cyclotomicCharMod_surjective _) u) = u :=
    surjInv_eq (cyclotomicCharMod_surjective _) u
  obtain ⟨μ, hμ, h_law⟩ := artin_reciprocity_of_mem_component hla ha hB hσ hz hp hz_tors hJ_fix
    hJ_away h_reps
  have h_ord (u : (ZMod (N * l ^ ν))ˣ) :
      μ u = floorDiff a (ofZMod (N * l ^ ν) (u : ZMod (N * l ^ ν))) := by
    simpa [hJ_level.galUnitsRep_apply (h_tors 1) _ _ zmod_eq_natCast_val, surjInv_eq,
      ← map_nsmul, hJ_level.ordRat_eq (h_tors _)] using (hμ u).symm
  -- In `O / l ^ ν`, the Stickelberger sum `t` divides `(a ^ (e + 1) - 1) X` with quotient `k`, and
  -- `X = (a ^ e - 1) (a ^ (e + 1) - 1) b`; so `k b` times Artin's law gives `2 X² z σ = 0`.
  set t : QuotSpan (l ^ ν : O) := ((∑ u : (ZMod (N * l ^ ν))ˣ,
      floorDiff a (ofZMod (N * l ^ ν) u) *
        ((u : ZMod (N * l ^ ν)).val ^ e * ψ (u : ZMod (N * l ^ ν)).val) : O) :
      QuotSpan (l ^ ν : O)) with ht
  obtain ⟨k, hk⟩ : t ∣ ((a : QuotSpan (l ^ ν : O)) ^ (e + 1) - 1) * X := by
    simpa [ht] using sum_floorDiff_dvd h_bound hc he_ne_zero ν ha hla
  have h_law_t : t * (2 * ((a : QuotSpan (l ^ ν : O)) ^ e - 1) * z σ) = 0 := by
    simpa [ht, h_ord, Algebra.smul_def, map_ofNat] using h_law
  have hX_q : (X : QuotSpan (l ^ ν : O)) =
      ((a : QuotSpan (l ^ ν : O)) ^ e - 1) * ((a : QuotSpan (l ^ ν : O)) ^ (e + 1) - 1) * b := by
    simp [hX, Nat.pos_of_ne_zero (ne_zero_of_coprime hla)]
  have h_zero : 2 * (X : QuotSpan (l ^ ν : O)) * X * z σ = 0 := by
    linear_combination k * b * h_law_t +
      2 * ((a : QuotSpan (l ^ ν : O)) ^ e - 1) * b * z σ * hk + 2 * X * z σ * hX_q
  exact hzσ (by simpa [nsmul_eq_mul] using h_zero)

omit [NeZero N] in
lemma isUnit_natCast_of_not_dvd {k : ℕ} (hk : ¬l ∣ k) : IsUnit (k : O) := by
  have h_unit : IsUnit (k : ℤ_[l]) :=
    .of_map PadicInt.toZMod _ (by simpa [natCast_eq_zero_iff] using hk)
  simpa using h_unit.map (algebraMap ℤ_[l] O)

/-- For `l > N` the number `φ (N l) = φ(N) (l - 1)` is a unit of `O`: both factors lie strictly
between `0` and `l`. -/
lemma isUnit_totient_mul (hl : N < l) : IsUnit (φ (N * l) : O) := by
  have hl_one : 1 < l := L.out.one_lt
  rw [totient_mul (N.coprime_of_lt_prime (NeZero.ne N) hl L.out).symm, totient_prime L.out,
    Nat.cast_mul]
  exact (isUnit_natCast_of_not_dvd
      (not_dvd_of_pos_of_lt (NeZero.pos _) (N.totient_le.trans_lt hl))).mul
    (isUnit_natCast_of_not_dvd (not_dvd_of_pos_of_lt (by lia) (by lia)))

/-- For `l > N` some `a ≡ 1 mod N` prime to `l` (a primitive root modulo `l`) makes `a ^ k - 1` a
unit of `O` for all `0 < k < l - 1`. -/
lemma exists_modEq_one_forall_isUnit_pow_sub_one (hl : N < l) :
    ∃ a : ℕ, a ≡ 1 [MOD N] ∧ l.Coprime a ∧
      ∀ k : ℕ, 0 < k → k < l - 1 → IsUnit (a ^ k - 1 : O) := by
  obtain ⟨b, hb⟩ : ∃ b : ZMod l, IsPrimitiveRoot b (l - 1) :=
    exists_isPrimitiveRoot (ZMod l) (l - 1)
  -- `a` is `b` modulo `l` and `1` modulo `N`.
  obtain ⟨a, hab, ha⟩ : {a : ℕ // a ≡ b.val [MOD l] ∧ a ≡ 1 [MOD N]} :=
    chineseRemainder (N.coprime_of_lt_prime (NeZero.ne N) hl L.out) b.val 1
  obtain rfl : (a : ZMod l) = b := by simpa [← natCast_eq_natCast_iff] using hab
  have hl_one : 1 < l := L.out.one_lt
  have hla : l.Coprime a := ((isUnit_iff_coprime a l).1 (hb.isUnit (by lia))).symm
  refine ⟨a, ha, hla, fun k hk hkl ↦ ?_⟩
  -- `a ^ k ≠ 1` modulo `l`, as `k` lies strictly between `0` and the order `l - 1` of `a`.
  have h_unit : IsUnit (a ^ k - 1 : ℤ_[l]) :=
    .of_map PadicInt.toZMod _ (by simpa [sub_eq_zero] using hb.pow_ne_one_of_pos_of_lt hk.ne' hkl)
  simpa using h_unit.map (algebraMap ℤ_[l] O)

private lemma isUnit_two_of_two_lt (hl : 2 < l) : IsUnit (2 : O) := by
  exact_mod_cast isUnit_natCast_of_not_dvd (O := O) (not_dvd_of_pos_of_lt two_pos hl)

/-- For `e ≠ 0` and `l > N + e + 3`, the numbers `a ^ e - 1` and `a ^ (e + 1) - 1` are units of `O`
for some `a ≡ 1 mod N` prime to `l`. -/
lemma exists_modEq_one_coprime_isUnit_pow_sub_one (he_ne_zero : e ≠ 0) (hl : N + e + 3 < l) :
    ∃ a : ℕ, a ≡ 1 [MOD N] ∧ l.Coprime a ∧
      IsUnit (a ^ e - 1 : O) ∧ IsUnit (a ^ (e + 1) - 1 : O) := by
  obtain ⟨a, ha, hla, h_pow⟩ :=
    exists_modEq_one_forall_isUnit_pow_sub_one (O := O) (show N < l by lia)
  exact ⟨a, ha, hla, h_pow e (by lia) (by lia), h_pow (e + 1) e.succ_pos (by lia)⟩

omit [Fact l.Prime] in
/-- Let `i` lie in the inertia group of a place `A` above a prime `r ≡ 1 mod N l`. Then `i` fixes
the `N`-th roots of unity, and `A` is not above `l`. The last clause repeats `hi`, so that the
conclusion has the form of the membership condition of `inertiaOff`. -/
lemma mem_cycloGalGroup_and_valuation_eq_one {r : Primes} {A : ClosurePlace} {i : Gal(Ω/ℚ)}
    (hr : r ≡ 1 [MOD N * l]) (hA : A.valuation (r : Ω) < 1) (hi : i ∈ inertiaGroup Gal(Ω/ℚ) A) :
    i ∈ cycloGalGroup N ∧ A.valuation (l : Ω) = 1 ∧ i ∈ inertiaGroup Gal(Ω/ℚ) A :=
  ⟨decompGroup_le_cycloGalGroup hA hr.of_mul_right (mem_decompGroup_of_mem_inertiaGroup hi),
    hr.of_mul_left.coprime_of_modEq_one.valuation_eq_one hA, hi⟩

/-- Let `O` be the integer ring of a finite extension of ℚ_l, `ψ` a Dirichlet character mod `N` with
values in `O`, and `component l e ψ ν` the locally constant cocycles for `(cyc ^ e ψ)⁻¹` on Gal(Ω/ℚ)
with values in `O / l ^ ν` that vanish at `cmConj` and at those elements of Gal(Ω/ℚ(μ_N)) lying in
an inertia group at a place prime to `l` or in `shaLocalSet l ℚ 1`. At a place `A` above a prime
`r ≡ 1 mod N l` (`A.valuation r < 1`) there is a Frobenius element `σ` with this property: every
cocycle `x` in `component l e ψ ν` that is killed by `l` and zero at `σ` is trivial above `r`
(`IsTrivialAbove x r`: it vanishes on the decomposition group of every place above `r`). -/
lemma exists_isFrob_forall_isTrivialAbove {r : Primes} {A : ClosurePlace} (hr : r ≡ 1 [MOD N * l])
    (hA : A.valuation (r : Ω) < 1) :
    ∃ σ : Gal(Ω/ℚ), IsFrob A r σ ∧
      ∀ x ∈ component l e ψ ν, l • x = 0 → x σ = 0 → IsTrivialAbove x r := by
  obtain ⟨v, ⟨hv : v.q = r, -⟩, -,
      h_over : ∀ A : ClosurePlace, A.valuation (r : Ω) < 1 → IsPlaceOver A v⟩ :=
    exists_rat_place_of_prime r.prop
  obtain ⟨σ, hσ⟩ : ∃ σ : Gal(Ω/ℚ), IsFrob A v.q σ := (h_over A hA).exists_isFrob Gal(Ω/ℚ)
  refine ⟨σ, by rwa [← hv], fun x hx h_tors hxσ B hB ↦ ?_⟩
  -- `B` is a conjugate `ρ • A`. The zeros of `x` form an open subgroup that contains inertia at
  -- `B` and the Frobenius element `ρ σ ρ⁻¹`, so it contains the decomposition group.
  have hBv : IsPlaceOver B v := h_over B hB
  obtain ⟨ρ, hρ⟩ := (h_over A hA).exists_smul Gal(Ω/ℚ) hBv
  have h_frob : IsFrob B v.q (ρ * σ * ρ⁻¹) := by
    rw [← hρ]
    exact hσ.conj ρ
  have h_inertia (i : Gal(Ω/ℚ)) (hi : i ∈ inertiaGroup Gal(Ω/ℚ) B) : x i = 0 := by
    obtain ⟨h_fix, h_val, -⟩ := mem_cycloGalGroup_and_valuation_eq_one hr hB hi
    have h_off_l : i ∈ inertiaAbove (placesDividing ℚ l)ᶜ :=
      ⟨v, hBv.valuation_natCast_eq_one_iff.1 h_val, B, hBv, hi⟩
    exact apply_eq_zero_of_mem_vanishingCocycles hx (.inr ⟨h_fix, .inl h_off_l⟩)
  -- `σ` fixes the `N l`-th roots of unity, so it fixes the values of `x`, which `l` kills.
  have h_conj : x (ρ * σ * ρ⁻¹) = 0 := by
    have h_fix : σ ∈ cycloGalGroup (N * l) :=
      decompGroup_le_cycloGalGroup hA hr (mem_decompGroup_of_isFrob hσ)
    have h_inv_fix : (cyclotomicPowDirichlet l e ψ σ)⁻¹.val • x ρ⁻¹ = x ρ⁻¹ :=
      (cyclotomicPowDirichlet_smul_eq_self h_fix (congrFun h_tors ρ⁻¹)).right
    rw [cocycle_conj_eq_smul (apply_mul_of_mem_vanishingCocycles hx) h_inv_fix, hxσ, smul_zero]
  exact hBv.decompGroup_le h_frob (openCocycleKer hx).isOpen' h_inertia h_conj

/-- Suppose no `m` points detect the cocycles in `component`: for every `γ : Fin m → Gal(Ω/ℚ)` some
non-zero `x` in `component` vanishes at all `γ i`. Then for every set `T` of at most `m` primes
`≡ 1 mod N l` some non-zero `z` in `component`, killed by `l`, is trivial above every prime of `T`
(it vanishes on the decomposition groups of the places above them). -/
lemma exists_ne_zero_forall_isTrivialAbove {m : ℕ}
    (h_blind : ∀ γ : Fin m → Gal(Ω/ℚ), ∃ x ∈ component l e ψ ν, (∀ i : Fin m, x (γ i) = 0) ∧ x ≠ 0)
    {T : Finset Primes} (hT : ∀ r ∈ T, r ≡ 1 [MOD N * l]) (h_card : #T ≤ m) :
    ∃ z ∈ component l e ψ ν, z ≠ 0 ∧ l • z = 0 ∧ ∀ r ∈ T, IsTrivialAbove z r := by
  -- Some `x ≠ 0` vanishes at the Frobenius elements `σ r`, `r ∈ T`, that detect triviality above
  -- `r`.
  choose place h_place using exists_place_above
  have h_detect : ∀ r : Primes, r ≡ 1 [MOD N * l] → ∃ σ : Gal(Ω/ℚ), IsFrob (place r) r σ ∧
      ∀ x ∈ component l e ψ ν, l • x = 0 → x σ = 0 → IsTrivialAbove x r :=
    fun r hr ↦ exists_isFrob_forall_isTrivialAbove hr (h_place r)
  choose! σ _hσ_frob hσ using h_detect
  obtain ⟨x, hx, hx_zero, hx_ne⟩ := h_blind fun i ↦ σ T.toList[i]!
  -- Replace `x` by its last non-zero multiple `l ^ k • x`.
  obtain ⟨k, hk, hk_succ⟩ : ∃ k : ℕ, l ^ k • x ≠ 0 ∧ l ^ (k + 1) • x = 0 :=
    exists_not_and_succ_of_not_zero_of_exists (p := fun k ↦ l ^ k • x = 0) (by simpa using hx_ne)
      ⟨ν, funext fun g ↦ nsmul_quot_eq_zero dvd_rfl (x g)⟩
  have h_tors : l • l ^ k • x = 0 := by rwa [← mul_nsmul]
  refine ⟨l ^ k • x, nsmul_mem hx _, hk, h_tors,
    fun r hr ↦ hσ r (hT r hr) _ (nsmul_mem hx _) h_tors ?_⟩
  have h_index : T.toList.idxOf r < m :=
    (List.idxOf_lt_length_iff.2 (mem_toList.2 hr)).trans_le (by rwa [length_toList])
  have hxσ : x (σ r) = 0 := by simpa [hr] using hx_zero ⟨_, h_index⟩
  simp [hxσ]

/-- Reciprocity modulo `l`. Let `a ≡ 1 mod N` be prime to `l`, with `2`, `φ (N l)` and `a ^ e - 1`
units of `O`. Let `z` in `component`, killed by `l`, be trivial above every prime of `T` but not
above a prime `r ≡ 1 mod N l`. Then a dual cocycle `y` for `cyc ^ (e + 1) ψ`, killed by `l`, that
vanishes on `inertiaOff N l (insert r T)`, vanishes on `inertiaOff N l T`. -/
lemma mem_vanishingCocycles_of_mem_insert {a m : ℕ} (ha : a ≡ 1 [MOD N]) (hla : l.Coprime a)
    (h_two : IsUnit (2 : O)) (h_totient : IsUnit (φ (N * l) : O)) (h_pow : IsUnit (a ^ e - 1 : O))
    {T : Finset Primes} {r : Primes} (hr : r ≡ 1 [MOD N * l])
    {z : Gal(Ω/ℚ) → QuotSpan (l ^ ν : O)} (hz : z ∈ component l e ψ ν) (hz_tors : l • z = 0)
    (hzT : ∀ t ∈ T, IsTrivialAbove z t) (hzr : ¬IsTrivialAbove z r)
    {y : Gal(Ω/ℚ) → QuotSpan (l ^ m : O)}
    (hy : y ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
      (inertiaOff N l (insert r T)))
    (hy_tors : l • y = 0) :
    y ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
      (inertiaOff N l T) := by
  -- Local constancy and the cocycle identity come from `hy`; it remains to show that `y` vanishes
  -- on the inertia groups of the places above neither `l` nor a prime of `T`.
  suffices hy_zero : ∀ τ ∈ inertiaOff N l T, y τ = 0 by
    obtain ⟨hy_const, hy_cocycle, -⟩ := hy
    exact ⟨hy_const, hy_cocycle, hy_zero⟩
  rintro τ ⟨A, ⟨h_fix, h_val, hτ⟩, hA⟩
  by_cases hAr : A.valuation (r : Ω) < 1
  · obtain ⟨σ, hσ, h_detect⟩ := exists_isFrob_forall_isTrivialAbove (e := e) (ψ := ψ) (ν := ν) hr
      hAr
    -- A place that is not above `r` lies above no prime of `insert r T`, or `z` is trivial there.
    have h_away (B : ClosurePlace) (hB : B.valuation (r : Ω) = 1) :
        (∀ t ∈ insert r T, ¬B.valuation (t : Ω) < 1) ∨
          ∀ g ∈ decompGroup Gal(Ω/ℚ) B, z g = 0 := by
      rw [or_iff_not_imp_right, forall_mem_insert]
      exact fun h_nontrivial ↦ ⟨hB.not_lt, fun t ht hBt ↦ h_nontrivial (hzT t ht B hBt)⟩
    -- `z σ ≠ 0`, since `σ` detects triviality above `r`.
    have hzσ : (2 * (a ^ e - 1) : O) • z σ ≠ 0 :=
      (h_two.mul h_pow).smul_eq_zero.ne.2 fun h_zero ↦ hzr (h_detect z hz hz_tors h_zero)
    exact reciprocity_mod_ell hla ha hAr hσ hz h_totient hr hz_tors hy (congrFun hy_tors) hτ
      h_away hzσ
  · -- `A` lies above neither `r` nor a prime of `T`, so `hy` applies.
    exact apply_eq_zero_of_mem_vanishingCocycles hy
      ⟨A, ⟨h_fix, h_val, hτ⟩, (forall_mem_insert r T _).2 ⟨hAr, hA⟩⟩

/-- Let `v_l(X) = X.factorization l`. If `l ^ (v_l(X) + 1)` divides `X ≠ 0` in `O`, then `l` is a
unit of `O`: it divides the part of `X` prime to `l`. -/
lemma isUnit_natCast_of_pow_factorization_succ_dvd (hX : X ≠ 0)
    (h_dvd : (l ^ (X.factorization l + 1) : O) ∣ X) :
    IsUnit (l : O) := by
  -- Write `X = l ^ v_l(X) * X'`; cancelling `l ^ v_l(X)` gives `l ∣ X'`, and `X'` is prime to `l`.
  nth_rw 2 [← X.ordProj_mul_ordCompl_eq_self l] at h_dvd
  have h_dvd_compl : (l : O) ∣ (ordCompl[l] X : ℕ) := by
    simpa [pow_succ, NeZero.ne, mul_dvd_mul_iff_left] using h_dvd
  exact (X.coprime_ordCompl L.out hX).cast.isUnit_of_dvd h_dvd_compl

lemma finite_component : Finite (component l e ψ ν) :=
  finite_vanishingCocycles (n := ν)
    (fun g y ↦ (cyclotomicPowDirichlet_smul_eq_self g.prop (nsmul_quot_eq_zero dvd_rfl y)).right)
    fun _ ⟨h_fix, h_inertia⟩ ↦ .inr ⟨h_fix, .inl h_inertia⟩

/-- There are finitely many cocycles for `cyc ^ e ψ` modulo `l ^ m` that are unramified off `l`
over `ℚ(ζ_N)`. -/
lemma finite_vanishingCocycles_inertiaOff_empty (m : ℕ) :
    Finite (vanishingCocycles (cyclotomicPowDirichlet l e ψ) (QuotSpan (l ^ m : O))
      (inertiaOff N l ∅)) :=
  finite_vanishingCocycles (n := m)
    (fun g y ↦ (cyclotomicPowDirichlet_smul_eq_self g.prop (nsmul_quot_eq_zero dvd_rfl y)).left)
    fun _ ⟨h_fix, _, hv, A, hA, h_inertia⟩ ↦
      ⟨A, ⟨h_fix, hA.valuation_natCast_eq_one_iff.2 hv, h_inertia⟩, nofun⟩

/-- If `cyc ^ e ψ` is odd (value `-1` at `cmConj`) and `2` is a unit of `O`, a non-zero cocycle `z`
in `component` does not vanish on the Galois group over `ℚ(ζ_f)`, that is, this group does not lie
in the open subgroup `openCocycleKer hz` of zeros of `z`. The reason: `z` is zero at `cmConj`, where
the character of `z` has the value `-1`, and `-1 - 1 = -2` is a unit. -/
lemma not_cycloGalGroup_le_openCocycleKer_of_ne_zero (hc : cyclotomicPowDirichlet l e ψ cmConj = -1)
    (h_two : IsUnit (2 : O))
    {z : Gal(Ω/ℚ) → QuotSpan (l ^ ν : O)} (hz : z ∈ component l e ψ ν) (hz_ne : z ≠ 0)
    (f : ℕ) [NeZero f] : ¬cycloGalGroup f ≤ openCocycleKer hz := by
  have h_char : ((cyclotomicPowDirichlet l e ψ)⁻¹ cmConj : O) - 1 = -2 := by norm_num [hc]
  refine not_cycloGalGroup_le_openCocycleKer hz cmConj
    (apply_eq_zero_of_mem_vanishingCocycles hz (Set.mem_insert cmConj _)) ?_ f
  rw [h_char]
  exact h_two.neg.smul_eq_zero.ne.2 hz_ne

/-- Let `cyc ^ e ψ` be odd (value `-1` at `cmConj`) and `2` a unit of `O`. There is a finite set `Q`
of primes `≡ 1 mod f` with this property. Let `y` be a cocycle for the dual character
`cyc ^ (e + 1) ψ` with values in `O / l ^ m`, unramified off `l` over `ℚ(ζ_N)` and not zero on the
Galois group over `ℚ(ζ_f)`, and let `z` be a non-zero cocycle in `component`. Then at some
Frobenius element `σ` at a place above a prime of `Q` neither `y` nor `z` vanishes. -/
lemma exists_finset_forall_exists_isFrob (hc : cyclotomicPowDirichlet l e ψ cmConj = -1)
    (h_two : IsUnit (2 : O)) (m f : ℕ) [NeZero f] :
    ∃ Q : Finset Primes, (∀ r ∈ Q, r ≡ 1 [MOD f]) ∧
      ∀ (y : vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
          (inertiaOff N l ∅)) (z : component l e ψ ν),
        ¬cycloGalGroup f ≤ openCocycleKer y.prop → z ≠ 0 →
          ∃ r ∈ Q, ∃ (A : ClosurePlace) (σ : Gal(Ω/ℚ)),
            A.valuation (r : Ω) < 1 ∧ IsFrob A r σ ∧ y.val σ ≠ 0 ∧ z.val σ ≠ 0 := by
  -- Choose a prime for each pair; there are finitely many pairs.
  have h_finite_y : Finite (vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ)
      (QuotSpan (l ^ m : O)) (inertiaOff N l ∅)) := finite_vanishingCocycles_inertiaOff_empty m
  have h_finite_z : Finite (component l e ψ ν) := finite_component
  have h_pair (y : {y : vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ)
      (QuotSpan (l ^ m : O)) (inertiaOff N l ∅) // ¬cycloGalGroup f ≤ openCocycleKer y.prop})
      (z : {z : component l e ψ ν // z ≠ 0}) :
      ∃ q : Primes, q ≡ 1 [MOD f] ∧ ∃ (A : ClosurePlace) (σ : Gal(Ω/ℚ)),
        A.valuation (q : Ω) < 1 ∧ IsFrob A q σ ∧ σ ∉ openCocycleKer y.val.prop ∧
          σ ∉ openCocycleKer z.val.prop :=
    exists_isFrob_notMem f y.prop (not_cycloGalGroup_le_openCocycleKer_of_ne_zero hc h_two
      z.val.prop (Subtype.coe_ne_coe.2 z.prop) f)
  choose q hq hq_frob using h_pair
  refine ⟨(Set.finite_range (uncurry q)).toFinset, fun r hr ↦ ?_, fun y z hy hz ↦ ?_⟩
  · obtain ⟨⟨y, z⟩, rfl⟩ : r ∈ Set.range (uncurry q) := (Set.Finite.mem_toFinset _).1 hr
    exact hq y z
  · have h_mem : q ⟨y, hy⟩ ⟨z, hz⟩ ∈ (Set.finite_range (uncurry q)).toFinset :=
      (Set.Finite.mem_toFinset _).2 ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩
    exact ⟨q ⟨y, hy⟩ ⟨z, hz⟩, h_mem, hq_frob ⟨y, hy⟩ ⟨z, hz⟩⟩

omit [Fact l.Prime] [PadicIntegerRing O l] in
/-- A cocycle unramified off `l` over `ℚ(ζ_N)` vanishes on inertia above a prime `≡ 1 mod N l`. -/
lemma apply_eq_zero_of_mem_inertiaGroup {M : Type} [AddCommGroup M] [Module O M]
    {χ : Gal(Ω/ℚ) →* Oˣ} {y : Gal(Ω/ℚ) → M} (hy : y ∈ vanishingCocycles χ M (inertiaOff N l ∅))
    {r : Primes} (hr : r ≡ 1 [MOD N * l]) {A : ClosurePlace} (hA : A.valuation (r : Ω) < 1)
    {ι : Gal(Ω/ℚ)} (hι : ι ∈ inertiaGroup Gal(Ω/ℚ) A) : y ι = 0 :=
  apply_eq_zero_of_mem_vanishingCocycles hy
    ⟨A, mem_cycloGalGroup_and_valuation_eq_one hr hA hι, nofun⟩

variable (l e ψ) in
/-- A finite set `T` of primes is tight at level `m` when its primes are `≡ 1 mod N l` and every
cocycle for the dual character `cyc ^ (e + 1) ψ` with values in `O / l ^ m` that is killed by `l`
and vanishes on `inertiaOff N l T` (unramified over `ℚ(ζ_N)` off `l` and `T`) also vanishes on
`inertiaOff N l ∅` (unramified off `l`). -/
private def IsTight (m : ℕ) (T : Finset Primes) : Prop :=
  (∀ r ∈ T, r ≡ 1 [MOD N * l]) ∧
    ∀ y ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
        (inertiaOff N l T), l • y = 0 →
        y ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
          (inertiaOff N l ∅)

private lemma IsTight.modEq_one {m : ℕ} {T : Finset Primes} (hT : IsTight l e ψ m T) :
    ∀ r ∈ T, r ≡ 1 [MOD N * l] :=
  hT.1

/-- For a tight set `T`, a dual cocycle killed by `l` and unramified off `l` and `T` is unramified
off `l`. -/
private lemma IsTight.mem_vanishingCocycles_of_nsmul_eq_zero {m : ℕ} {T : Finset Primes}
    (hT : IsTight l e ψ m T) {y : Gal(Ω/ℚ) → QuotSpan (l ^ m : O)}
    (hy : y ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
      (inertiaOff N l T))
    (hy_tors : l • y = 0) :
    y ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
      (inertiaOff N l ∅) :=
  hT.2 y hy hy_tors

/-- Reciprocity keeps a set tight. Let `a ≡ 1 mod N` be prime to `l`, with `2`, `φ (N l)` and
`a ^ e - 1` units of `O`. If `T` is tight and some `z` in `component`, killed by `l`, is trivial
above every prime of `T` but not above a prime `r ≡ 1 mod N l`, then `insert r T` is tight. -/
private lemma IsTight.insert {a m : ℕ} (ha : a ≡ 1 [MOD N]) (hla : l.Coprime a)
    (h_two : IsUnit (2 : O)) (h_totient : IsUnit (φ (N * l) : O)) (h_pow : IsUnit (a ^ e - 1 : O))
    {T : Finset Primes} (hT : IsTight l e ψ m T) {r : Primes} (hr : r ≡ 1 [MOD N * l])
    {z : Gal(Ω/ℚ) → QuotSpan (l ^ ν : O)} (hz : z ∈ component l e ψ ν) (hz_tors : l • z = 0)
    (hzT : ∀ t ∈ T, IsTrivialAbove z t) (hzr : ¬IsTrivialAbove z r) :
    IsTight l e ψ m (insert r T) := by
  refine ⟨(forall_mem_insert r T _).2 ⟨hr, hT.modEq_one⟩, fun y hy hy_tors ↦ ?_⟩
  -- By reciprocity modulo `l`, `y` is unramified off `l` and `T`.
  have hy_T : y ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
      (inertiaOff N l T) :=
    mem_vanishingCocycles_of_mem_insert ha hla h_two h_totient h_pow hr hz hz_tors hzT hzr hy
      hy_tors
  exact hT.mem_vanishingCocycles_of_nsmul_eq_zero hy_T hy_tors

/-- Kolyvagin's descent. Suppose no `m` points detect the cocycles in `component l e ψ ν`; let
`a ≡ 1 mod N` be prime to `l` with `2`, `φ (N l)`, `a ^ e - 1` units. Let `κ` be a Kolyvagin system
for `cyc ^ (e + 1) ψ` in `O / l ^ m` over the primes of `Q` (all `≡ 1 mod a N l ^ m`), with
auxiliary prime `p`, zero at `γ` (`cyc ^ (e + 1) ψ (γ) - 1` a unit), and `hQ_frob` supplying
detecting Frobenius elements. If `i ≤ m` and `S ⊆ Q` has at most `i` primes with `insert p S` tight,
`l ^ i • κ S` is unramified off `l`. -/
private lemma nsmul_mem_vanishingCocycles_of_isTight {a m : ℕ} [NeZero a] (ha : a ≡ 1 [MOD N])
    (hla : l.Coprime a) (h_two : IsUnit (2 : O)) (h_totient : IsUnit (φ (N * l) : O))
    (h_pow : IsUnit (a ^ e - 1 : O))
    (h_blind : ∀ δ : Fin m → Gal(Ω/ℚ),
      ∃ x ∈ component l e ψ ν, (∀ j : Fin m, x (δ j) = 0) ∧ x ≠ 0)
    {γ : Gal(Ω/ℚ)} (hγ_unit : IsUnit (cyclotomicPowDirichlet l (e + 1) ψ γ - 1 : O))
    {Q : Finset Primes} (hQ_mod : ∀ r ∈ Q, r ≡ 1 [MOD a * (N * l ^ m)])
    (hQ_frob : ∀ (y : vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
          (inertiaOff N l ∅)) (z : component l e ψ ν),
        ¬cycloGalGroup (a * (N * l ^ m)) ≤ openCocycleKer y.prop → z ≠ 0 →
          ∃ r ∈ Q, ∃ (A : ClosurePlace) (σ : Gal(Ω/ℚ)),
            A.valuation (r : Ω) < 1 ∧ IsFrob A r σ ∧ y.val σ ≠ 0 ∧ z.val σ ≠ 0)
    {p : Primes} {κ : Finset Primes → Gal(Ω/ℚ) → QuotSpan (l ^ m : O)}
    (hκ : IsKolyvaginSystem (cyclotomicPowDirichlet l (e + 1) ψ) γ N l p Q κ) {i : ℕ} (hi : i ≤ m) :
    ∀ S ⊆ Q, #S ≤ i → IsTight l e ψ m (insert p S) →
      l ^ i • κ S ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
        (inertiaOff N l ∅) := by
  -- Descent on `i`, from `i = m`, where `l ^ m` kills the coefficients.
  induction hi using decreasingInduction with
  | self =>
    intro S _ _ _
    simp [show l ^ m • κ S = 0 from funext fun g ↦ nsmul_quot_eq_zero dvd_rfl (κ S g)]
  | of_succ i hi ih =>
    intro S hS h_card h_tight
    suffices h_tors : l • l ^ i • κ S = 0 from
      h_tight.mem_vanishingCocycles_of_nsmul_eq_zero (nsmul_mem (hκ.mem_vanishingCocycles S hS) _)
        h_tors
    by_contra h_ne
    -- If `y = l ^ (i + 1) • κ S` is not zero, it is not zero on the Galois group over
    -- `ℚ(ζ_{a N l ^ m})`, because `y γ = 0` and `cyc ^ (e + 1) ψ (γ) - 1` is a unit.
    let y : vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
        (inertiaOff N l ∅) :=
      ⟨l ^ (i + 1) • κ S, ih S hS h_card.step h_tight⟩
    have hy_ne : l ^ (i + 1) • κ S ≠ 0 := by rwa [← mul_nsmul] at h_ne
    have hyγ : (l ^ (i + 1) • κ S) γ = 0 := by simp [hκ.apply_eq_zero S hS]
    have hy : ¬cycloGalGroup (a * (N * l ^ m)) ≤ openCocycleKer y.prop :=
      not_cycloGalGroup_le_openCocycleKer y.prop γ hyγ (hγ_unit.smul_eq_zero.ne.2 hy_ne) _
    -- Some `w ≠ 0` in `component`, killed by `l`, is trivial above `p` and the primes of `S`.
    obtain ⟨w, hw, hw_ne, hw_tors, hw_triv⟩ := exists_ne_zero_forall_isTrivialAbove h_blind
      h_tight.modEq_one ((card_insert_le p S).trans (Nat.succ_le_of_lt (h_card.trans_lt hi)))
    -- The prime `r` of the pair `(y, w)` is new (`w` is not trivial above it); the set stays tight.
    obtain ⟨r, hrQ, A, σ, hA, hσ, hyσ, hwσ⟩ := hQ_frob y ⟨w, hw⟩ hy (Subtype.coe_ne_coe.1 hw_ne)
    have h_level : N * l ∣ N * l ^ m := mul_dvd_mul_left N (dvd_pow_self l (Nat.ne_zero_of_lt hi))
    have hr : r ≡ 1 [MOD N * l] := (hQ_mod r hrQ).of_dvd (h_level.mul_left a)
    have hwr : ¬IsTrivialAbove w r := fun h_triv ↦
      hwσ (h_triv A hA σ (mem_decompGroup_of_isFrob hσ))
    have hrS : r ∉ S := fun hrS ↦ hwr (hw_triv r (mem_insert_of_mem hrS))
    have h_tight_next : IsTight l e ψ m (insert p (insert r S)) := by
      rw [insert_comm]
      exact h_tight.insert ha hla h_two h_totient h_pow hr hw hw_tors hw_triv hwr
    have h_next : l ^ (i + 1) • κ (insert r S) ∈ vanishingCocycles
        (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O)) (inertiaOff N l ∅) :=
      ih _ (insert_subset hrQ hS) ((card_insert_le r S).trans (Nat.succ_le_succ h_card))
        h_tight_next
    -- Hence `y σ = l ^ (i + 1) • κ (insert r S) ι = 0`, against the choice of `σ`.
    obtain ⟨ι, hι, h_eq⟩ := hκ.exists_mem_inertiaGroup_eq S hS r hrQ hrS A σ hσ hA
    refine hyσ ?_
    calc l ^ (i + 1) • κ S σ = (l ^ (i + 1) • κ (insert r S)) ι := by rw [← h_eq, Pi.smul_apply]
      _ = 0 := apply_eq_zero_of_mem_inertiaGroup h_next hr hA hι

/-- The Kolyvagin–Rubin bound, from the Euler system of Gauss sums. Let `X ≠ 0` satisfy
`IsStickelbergerBound N e X`, a divisibility for each prime plus a congruence for the Stickelberger
sums. Let `cyc ^ e ψ` be odd (value `-1` at `cmConj`), `e ≠ 0` and `l > N + e + 3`. Then there are
`v_l(X) + 1` elements `γ i` of the Galois group, where `v_l(X) = X.factorization l`, such that a
cocycle in `component l e ψ ν` vanishing at all of them is zero. That space consists of cocycles
`Gal(Ω/ℚ) → O/l^ν` for `(cyc^e ψ)⁻¹` under local conditions.

It is used instead of the Iwasawa main conjecture proved by Mazur and Wiles: for l > N + e + 3 it
bounds, at finite level, the number of Galois elements needed to detect the cocycles. -/
lemma exists_detecting_points_component (h_bound : IsStickelbergerBound N e X)
    (hc : cyclotomicPowDirichlet l e ψ cmConj = -1) (he_ne_zero : e ≠ 0) (hX : X ≠ 0)
    (hl : N + e + 3 < l) :
    ∃ γ : Fin (X.factorization l + 1) → Gal(Ω/ℚ),
      ∀ x ∈ component l e ψ ν, (∀ i : Fin (X.factorization l + 1), x (γ i) = 0) → x = 0 := by
  -- Suppose no `m = v_l(X) + 1` points detect the cocycles. Then for any `m` primes `≡ 1 mod N l`
  -- some non-zero cocycle killed by `l` is trivial above all of them. By reciprocity this bounds
  -- the ramification of Kolyvagin's cocycles `κ S`; by descent `κ ∅` is unramified at `p`, so that
  -- `l ^ m ∣ X` in `O`.
  by_contra! h_blind
  set m : ℕ := X.factorization l + 1
  have h_two : IsUnit (2 : O) := isUnit_two_of_two_lt (by lia)
  have h_totient : IsUnit (φ (N * l) : O) := isUnit_totient_mul (by lia)
  obtain ⟨a, ha, hla, h_pow, h_pow_succ⟩ :=
    exists_modEq_one_coprime_isUnit_pow_sub_one (O := O) he_ne_zero hl
  have ha_ne_zero : NeZero a := ⟨ne_zero_of_coprime hla⟩
  have h_level : N * l ∣ N * l ^ m := mul_dvd_mul_left N (dvd_pow_self l (NeZero.ne m))
  -- At `γ` the dual character has the value `a ^ (e + 1)`.
  obtain ⟨P, hP⟩ := exists_place_above ⟨l, L.out⟩
  obtain ⟨γ, -, hγ⟩ := exists_inertia_cyclotomicPowDirichlet_eq (ψ := ψ) hla ha hP (e + 1)
  have hγ_unit : IsUnit (cyclotomicPowDirichlet l (e + 1) ψ γ - 1 : O) := by rwa [hγ]
  obtain ⟨Q, hQ_mod, hQ_frob⟩ :=
    exists_finset_forall_exists_isFrob (ν := ν) hc h_two m (a * (N * l ^ m))
  -- Choose `z ≠ 0` killed by `l`, and a prime `p ≡ 1` modulo `N l ^ m` and all of `Q` at which `z`
  -- is not trivial.
  obtain ⟨z, hz, hz_ne, hz_tors, -⟩ :=
    exists_ne_zero_forall_isTrivialAbove h_blind (T := ∅) (by simp) bot_le
  have h_prod_ne_zero : NeZero (∏ r ∈ Q, (r : ℕ)) := NeZero.of_pos (Q.prod_pos fun r _ ↦ r.prop.pos)
  have hz_visible : ¬cycloGalGroup (N * l ^ m * ∏ r ∈ Q, (r : ℕ)) ≤ openCocycleKer hz :=
    not_cycloGalGroup_le_openCocycleKer_of_ne_zero hc h_two hz hz_ne _
  obtain ⟨p, hp : p ≡ 1 [MOD N * l ^ m * ∏ r ∈ Q, (r : ℕ)], B, τ, hB : B.valuation (p : Ω) < 1,
      hτ : IsFrob B p τ, hzτ : z τ ≠ 0, -⟩ :=
    exists_isFrob_notMem _ hz_visible hz_visible
  have hp_split : p ≡ 1 [MOD N * l] := hp.of_dvd (h_level.mul_right _)
  have h_tight_empty : IsTight l e ψ m ∅ := ⟨by simp, fun y hy _hy_tors ↦ hy⟩
  have hp_tight : IsTight l e ψ m (insert p ∅) :=
    h_tight_empty.insert ha hla h_two h_totient h_pow hp_split hz hz_tors (by simp)
      fun h_triv ↦ hzτ (h_triv B hB τ (mem_decompGroup_of_isFrob hτ))
  -- Kolyvagin's cocycles `κ S` for `S ⊆ Q`; if `κ ∅` is unramified at `B`, then
  -- `cyc ^ (e + 1) ψ (γ) - 1` kills the Stickelberger sum (`h_value`).
  obtain ⟨κ, hκ : IsKolyvaginSystem (cyclotomicPowDirichlet l (e + 1) ψ) γ N l p Q κ, h_value⟩ :=
    exists_isKolyvaginSystem (ψ := ψ) e a γ hQ_mod hp hB
  -- By descent down to `i = 0`, `κ ∅` is unramified off `l`, so it kills inertia at `B`.
  have h_κ_mem : κ ∅ ∈ vanishingCocycles (cyclotomicPowDirichlet l (e + 1) ψ) (QuotSpan (l ^ m : O))
      (inertiaOff N l ∅) := by
    simpa using nsmul_mem_vanishingCocycles_of_isTight ha hla h_two h_totient h_pow h_blind
      hγ_unit hQ_mod hQ_frob hκ (zero_le m) ∅ (empty_subset Q) le_rfl hp_tight
  have h_inertia (ι : Gal(Ω/ℚ)) (hι : ι ∈ inertiaGroup Gal(Ω/ℚ) B) : κ ∅ ι = 0 :=
    apply_eq_zero_of_mem_inertiaGroup h_κ_mem hp_split hB hι
  -- So the Stickelberger sum is `0` modulo `l ^ m`, and `l ^ m ∣ X`.
  have h_sum_zero : ((∑ u : (ZMod (N * l ^ m))ˣ, floorDiff a (ofZMod (N * l ^ m) u) *
      ((u : ZMod (N * l ^ m)).val ^ e * ψ (u : ZMod (N * l ^ m)).val) : O) :
        QuotSpan (l ^ m : O)) = 0 :=
    hγ_unit.smul_eq_zero.1 (h_value h_inertia)
  have h_dvd_mul : (l ^ m : O) ∣ (a ^ (e + 1) - 1) * X := by
    obtain ⟨c, h_eq⟩ := sum_floorDiff_dvd h_bound hc he_ne_zero m ha hla
    simpa only [h_sum_zero, zero_mul, eq_zero_iff_dvd] using h_eq
  have h_dvd : (l ^ m : O) ∣ X := h_pow_succ.dvd_mul_left.1 h_dvd_mul
  -- Then `l` is a unit of `O`, and a unit kills no `z ≠ 0`.
  have hl_unit : IsUnit (l : O) := isUnit_natCast_of_pow_factorization_succ_dvd hX h_dvd
  exact hz_ne (hl_unit.smul_eq_zero.1 (by rwa [Nat.cast_smul_eq_nsmul]))

end ComponentBound

end New.OddPart
