import Lib.PadicHodge.Crystalline.HodgeTateForms
import Lib.PadicHodge.Kisin.Charts

/-!
# Witt coefficients, the Frobenius group action and existence of Kummer charts

Let Λ = `New.Lift.WittFq f` be the ring of Witt vectors of the field with p^f elements inside O^♭,
with p implicit, and let θ be Fontaine's map from A_inf to O_C. The group ℤ × Γ acts on O^♭, A_inf
and W(C^♭), where (n, g) acts as φ^n j(g) and φ is the bijective Frobenius. A local field is given
by `Γ : GroupOverGp p`, a group with a homomorphism j = `toGp` to `Gp p` of open image; the field is
the subfield of ℚ̄_p fixed by the image. Every such field has a Kummer chart: a chart
S = Λ⟦z⟧ ⊂ A_inf with a subgroup Γ' of Γ of index prime to p, such that j(Γ') fixes Λ and θ(z) and
moves z to every [ε]^l z.

## Main definitions and results

* `New.Lift.wittToQpBar`: the restriction of θ to Λ, with values in the algebraic closure of
  `ℚ_[p]`; it is injective (`New.Lift.wittToQpBar_injective`).
* `New.Lift.FrobGroup`: the group ℤ × Γ, with Frobenius `New.Lift.FrobGroup.φ`.
* `New.Lift.KummerChart`: a Kummer chart; `New.Lift.KummerChart.IsUnramified`: it is unramified.
* `New.Lift.exists_kummerChart`: every such field has a Kummer chart, with ef the degree of the
  field.

Notions from other files:
* `New.Period.OFlat`: The ring O^♭, the inverse limit of O_C/p along x ↦ x^p, where O_C is the ring
  of integers of C_p.
* `New.Lift.Chart`: A Λ-algebra map Λ[[X]] → A_inf with image S, sending X to a non-unit Teichmüller
  lift z and a series X^e A + p, A a unit, to an element E that generates ker θ.

## Relation to the literature

Known; see `Lib.PadicHodge.Kisin.PeriodMatrixFrame` and `Lib.PadicHodge.PeriodRings.DeRhamPeriods`
for sources.
-/

noncomputable section

namespace New.Lift

/-! ## Embedding the Witt coefficients in ℚ̄_p by θ -/

section WittEmbedding

open Period WittVector

variable {p : ℕ} [ThePrime p] {𝔣 : ℕ+} {g : Gp p} {c : WittFq 𝔣}

/-- The Z_p-algebra homomorphism from Λ = W(F_{p^f}) to Q̄_p that becomes the restriction of θ
after the inclusion of Q̄_p in C_p. -/
noncomputable def wittToQpBar : WittFq 𝔣 →ₐ[ℤ_[p]] PadicAlgCl p :=
  (exists_algHom_lift (OC.toPadicIntAlgHom (theta.comp (algebraMap (WittFq 𝔣) Ainf)))).choose

lemma coe_wittToQpBar : wittToQpBar c = (theta (algebraMap (WittFq 𝔣) Ainf c)).val :=
  ((exists_algHom_lift _).choose_spec c).symm

/-- The map from Λ = W(F_{p^f}) to Q̄_p given by θ is injective. -/
lemma wittToQpBar_injective : Function.Injective (wittToQpBar (p := p) (𝔣 := 𝔣)) :=
  -- `WittFq 𝔣` is integral over `ℤ_[p]`, and the kernel lies over `⊥`, so it is `⊥`
  (injective_iff_map_eq_zero _).mpr (Ideal.eq_bot_of_liesOver_bot ℤ_[p]
    ((⊥ : Ideal _).comap (wittToQpBar (p := p) (𝔣 := 𝔣)))).le

/-- An element g of G_p fixes the image in A_inf of c ∈ Λ if and only if g fixes the image of c
in Q̄_p under `New.Lift.wittToQpBar`. -/
lemma smul_algebraMap_wittFq_eq_iff :
    g • algebraMap (WittFq 𝔣) Ainf c = algebraMap (WittFq 𝔣) Ainf c ↔
      g (wittToQpBar c) = wittToQpBar c := by
  -- `g` moves the coefficient `c` to a coefficient `b`, and `θ` is equivariant (`theta_smul`), so
  -- `wittToQpBar b = g (wittToQpBar c)`. By injectivity both sides then say `b = c`.
  obtain ⟨b, hb⟩ :
      ∃ b : WittFq 𝔣, g • algebraMap (WittFq 𝔣) Ainf c = algebraMap (WittFq 𝔣) Ainf b :=
    c.exists_smul_algebraMap_eq _
  have h_toΩ : wittToQpBar b = g (wittToQpBar c) := by
    rw [← UniformSpace.Completion.coe_inj, coe_wittToQpBar, ← hb, theta_smul]
    simp [← coe_wittToQpBar]
  have h_alg_inj : Function.Injective (algebraMap (WittFq 𝔣) Ainf) :=
    map_injective _ Subtype.val_injective
  rw [hb, ← h_toΩ, wittToQpBar_injective.eq_iff, h_alg_inj.eq_iff]

end WittEmbedding

/-! ## Frobenius and Galois actions, and Teichmüller roots of unity -/

section FrobeniusGroup

open Period WittVector MulSemiringAction HasEnoughRootsOfUnity OFlat

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p] {f : ℕ+}

/-! ### The action of ℤ × Γ -/

/-- The group ℤ × Γ (ℤ written multiplicatively); on rings with bijective Frobenius φ, such as
A_inf, the pair (n, g) acts as φ^n j(g). -/
def FrobGroup (Γ : GroupOverGp p) : Type := Multiplicative ℤ × Γ
  deriving Group

/-- The projection ℤ × Γ → Γ. -/
def FrobGroup.snd : FrobGroup Γ →* Γ := MonoidHom.snd (Multiplicative ℤ) Γ

/-- The element (1, identity) of ℤ × Γ, which acts on O^♭, A_inf and W(C^♭) as the Frobenius φ. -/
def FrobGroup.φ : FrobGroup Γ := (Multiplicative.ofAdd 1, 1)

/-- The inclusion Γ → ℤ × Γ, g ↦ (0, g). -/
def FrobGroup.inr : Γ →* FrobGroup Γ := MonoidHom.inr (Multiplicative ℤ) Γ

instance : MulSemiringAction (FrobGroup Γ) OFlat :=
  -- `(n, g)` acts by the `n`-th power of Frobenius composed with `toGp g`; these two commute.
  .compHom OFlat <|
    (zpowersHom _ (frobeniusEquiv OFlat p)).noncommCoprod ((toRingAut (Gp p) OFlat).comp toGp)
      fun n g ↦ Commute.zpow_left (RingEquiv.ext fun x ↦ by simp [frobenius_def]) _

/-- The element φ = (1, 1) of ℤ × Γ acts on O^♭ as the Frobenius x ↦ x^p. -/
lemma phi_smul_oFlat (x : OFlat) : FrobGroup.φ • x = frobEnd x := by
  -- by definition `FrobGroup.φ • x` is `(1 • x) ^ p`
  change ((1 : FrobGroup Γ) • x) ^ p = frobEnd x
  rw [one_smul, frobEnd_apply]

lemma phi_smul_ainf (x : Ainf) : FrobGroup.φ • x = frobEnd x :=
  ext fun (n : ℕ) ↦ phi_smul_oFlat (x.coeff n)

lemma phi_smul_wittCFlat (x : WittCFlat) : FrobGroup.φ • x = WittVector.frobenius x := by
  -- both sides act on coefficients, by two ring maps of the fraction field that agree on `OFlat`
  have h_coeff : toRingHom (FrobGroup Γ) CFlat FrobGroup.φ = _root_.frobenius CFlat p :=
    IsFractionRing.ringHom_ext (A := OFlat) (by simp [frobenius_def, phi_smul_oFlat, frobEnd_apply])
  rw [frobenius_eq_map_frobenius, ← h_coeff]
  rfl

lemma FrobGroup.phi_pow_smul (n : ℕ) (x : Ainf) : φ ^ n • x = frobEnd^[n] x := by
  simp [← funext phi_smul_ainf]

omit Γ

/-! ### Teichmüller roots of unity -/

/-- For distinct elements a ≠ b of the field with p^f elements in O^♭, the difference [a] − [b]
of their Teichmüller lifts is a unit of W(F_{p^f}). -/
lemma isUnit_teichmuller_sub {a b : flatFq f} (h_ne : a ≠ b) :
    IsUnit (teichmuller p a - teichmuller p b) := by
  simpa [Ainf.isUnit_iff_isUnit_constantCoeff, map_sub, sub_eq_zero]

instance : HasEnoughRootsOfUnity (flatFq f) (p ^ f.val - 1) :=
  of_card_le (by simp [← card_flatFq, ← Nat.card_units])

/-- Let k be the field of p^f elements in O^♭ and s: W(k) → K a ring homomorphism to a field.
Every x in K with x^{p^f} = x is s([a]) for the Teichmüller lift [a] of some a in k. -/
lemma exists_flatFq_teichmuller_eq {K : Type*} [Field K] (s : WittFq f →+* K) (x : K)
    (hx : x ≠ 0 → x ^ (p ^ f.val - 1) = 1) :
    ∃ a : flatFq f, s (teichmuller p a) = x := by
  -- `a ↦ s [a]` is injective and multiplicative, so it carries a primitive `(p ^ f - 1)`-th root
  -- of unity `g` to one in `K`, whose powers are all the nonzero solutions `x`.
  obtain ⟨g, hg⟩ : ∃ g : flatFq f, IsPrimitiveRoot g (p ^ f.val - 1) := prim
  have h_inj : Function.Injective ((s : WittFq f →* K).comp (teichmuller p)) := by
    intro a b h_eq
    by_contra h_ne
    exact ((isUnit_teichmuller_sub h_ne).map s).ne_zero (by simpa [sub_eq_zero] using h_eq)
  obtain rfl | hx₀ := eq_or_ne x 0
  · exact ⟨0, by simp⟩
  · obtain ⟨i, -, hi⟩ := (hg.map_of_injective h_inj).eq_pow_of_pow_eq_one (hx hx₀)
    exact ⟨g ^ i, by simpa using hi⟩

/-- An element of G_p fixes all (p^f - 1)-th roots of unity in Q̄_p if and only if it fixes the
image of W(F_{p^f}) in A_inf pointwise. -/
lemma fixes_roots_iff_fixesLambda (g : Gp p) :
    (∀ ζ : PadicAlgCl p, ζ ^ (p ^ f.val - 1) = 1 → g ζ = ζ) ↔ FixesLambda f g := by
  constructor
  · intro h_roots c
    -- `g` acts coefficientwise, and fixes each coefficient because it fixes its Teichmüller lift
    have h_teich (a : flatFq f) :
        g • algebraMap (WittFq f) Ainf (teichmuller p a) =
          algebraMap (WittFq f) Ainf (teichmuller p a) := by
      have h_pow : a ^ p ^ f.val = a := Subtype.ext a.prop
      -- `smul_algebraMap_wittFq_eq_iff` moves the question to the image of `[a]` under
      -- `wittToQpBar`, which is `0` or a `(p ^ f - 1)`-th root of unity
      apply smul_algebraMap_wittFq_eq_iff.mpr
      grind [NeZero.one_le, pow_sub₀]
    -- the `n`-th coefficient of `c` in `A_inf` is the `0`-th one of its Teichmüller lift
    ext n
    exact congrArg (fun w : Ainf ↦ w.coeff 0) (h_teich (c.coeff n))
  · intro h_fixes ζ hζ
    -- each such root of unity is the image of a Teichmüller lift
    obtain ⟨a, rfl⟩ := exists_flatFq_teichmuller_eq wittToQpBar.toRingHom ζ fun _ ↦ hζ
    exact smul_algebraMap_wittFq_eq_iff.mp (h_fixes (teichmuller p a))

end FrobeniusGroup

/-!
## Existence of Kummer charts

Here z = [u] is the Teichmüller lift of some u in O^♭, and `epsTilt` is ε = (1, ζ_p, ζ_{p²}, …).

* `New.Lift.exists_smul_teichmuller_eq`: the compactness step from roots of π to compatible towers
  of roots.
-/

section KummerChartExists

open Period OFlat Variety PadicComplex NeZero PowerSeries Ideal WittVector Selmer IsLocalRing
  PreTilt

attribute [local instance low] Fintype.ofFinite

variable {p : outParam ℕ} [ThePrime p] (Γ : outParam (GroupOverGp p))

/-- Let C be a closed subgroup of G_p that is transitive on the n-th roots of π ∈ Q̄_p for every
n > 0 (`h_transitive`). Let u, v ∈ O^♭ and e > 0 be such that the untilt u^♯ of u satisfies
(u^♯)^e = π and the untilt of v has the same e-th power. Then some g in C sends the Teichmüller
lift [u] to [v]. -/
lemma exists_smul_teichmuller_eq (C : Subgroup (Gp p)) [hC : IsClosed (C : Set (Gp p))]
    {π : PadicAlgCl p}
    (h_transitive :
      ∀ {x y : PadicAlgCl p} {n : ℕ}, 0 < n → x ^ n = π → y ^ n = x ^ n → ∃ g ∈ C, g • x = y)
    (u v : OFlat) (e : ℕ) [NeZero e] (hu : (u.untilt ^ e).val = π)
    (hv : v.untilt ^ e = u.untilt ^ e) :
    ∃ g ∈ C, g • teichmuller p u = teichmuller p v := by
  -- Compactness: the sets `X n` of `g ∈ C` that send the `n`-th component of `u` to that of `v` are
  -- closed, decreasing and nonempty; an element of their intersection sends `u` to `v`.
  -- The components are roots of `X ^ (p ^ n * e) - π`, so they are algebraic.
  have h_alg (y : OFlat) (hy : y.untilt ^ e = u.untilt ^ e) (n : ℕ) :
      ∃ x : PadicAlgCl p, x ^ (p ^ n * e) = π ∧ (x : ℂ_[p]) = (untiltRoot n y).val := by
    have h_root_eval : (Polynomial.X ^ (p ^ n * e) - Polynomial.C π).eval₂
        (algebraMap (PadicAlgCl p) ℂ_[p]) (untiltRoot n y).val = 0 := by
      simp [pow_mul, ← SubmonoidClass.coe_pow, untiltRoot, coe_eq, hy, hu]
    simpa [← coe_eq, sub_eq_zero] using IsAbsIntegrallyClosed.exists_root_map_eq
      (f := algebraMap ..)
      (Polynomial.monic_X_pow_sub_C π (ne (p ^ n * e))) h_root_eval
  -- `b y n` is the `n`-th component of `y`, as an element of `ℚ̄_p`.
  choose! b hb_pow hb using h_alg
  let X (n : ℕ) : Set (Gp p) := C.carrier ∩ {g | ↑(g • b u n) = (v.untiltRoot n).val}
  have hX_closed (n : ℕ) : IsClosed (X n) :=
    hC.inter (isClosed_setOf_smul (b u n) fun x ↦ ↑x = (v.untiltRoot n).val)
  -- the `n`-th component is the `p`-th power of the next one
  have hX_anti (n : ℕ) : X (n + 1) ⊆ X n := by
    refine Set.inter_subset_inter_right _ fun g h_next ↦ ?_
    have h_eq : ((g • b u (n + 1) : PadicAlgCl p) : ℂ_[p]) = (v.untiltRoot (n + 1)).val := h_next
    -- `↓`: with the plain lemma simp unfolds one Frobenius too many on each side
    simpa [← smul_coe_Cp, hb, untiltRoot, ↓Function.iterate_succ',
      ← untilt_iterate_frobeniusEquiv_symm_pow (_^[n] _) 1] using congrArg (· ^ p) h_eq
  have hX_ne (n : ℕ) : (X n).Nonempty := by
    have h_pow_eq : b v n ^ (p ^ n * e) = b u n ^ (p ^ n * e) := by simp [hb_pow, hv]
    obtain ⟨g, hg_C, hg_smul⟩ : ∃ g ∈ C, g • b u n = b v n :=
      h_transitive (pos _) (hb_pow u rfl n) h_pow_eq
    have hg_root : ((g • b u n : PadicAlgCl p) : ℂ_[p]) = (v.untiltRoot n).val := by
      rw [hg_smul, hb v hv n]
    exact ⟨g, hg_C, hg_root⟩
  have h_inter : (⋂ n, X n).Nonempty :=
    (hX_closed 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed X hX_anti hX_ne
      hX_closed
  obtain ⟨g, hg⟩ : ∃ g : Gp p, ∀ n : ℕ, g ∈ X n := Set.nonempty_iInter.mp h_inter
  have hg_C : g ∈ C := (hg 0).left
  refine ⟨g, hg_C, (map_teichmuller ..).trans (congrArg _ (Perfection.ext fun n ↦ ?_))⟩
  -- the `n`-th coefficient is the class of the `n`-th component modulo `p`
  -- `erw`: `OFlat` is the perfection of `O_C / p` only up to unfolding
  erw [map_pow, pow_one, ← coeff_tiltMap _ (mk_untiltRoot ..), ← mk_untiltRoot]
  have hg_n : ((g • b u n : PadicAlgCl p) : ℂ_[p]) = (v.untiltRoot n).val := (hg n).right
  have h_root_eq : g • untiltRoot n u = untiltRoot n v :=
    Subtype.ext (by simpa [← hb, smul_coe_Cp] using hg_n)
  exact congrArg _ h_root_eq

/-- A Kummer chart for j : Γ → G_p with open image: a chart S = Λ⟦z⟧ ⊂ A_inf, Λ = W(𝔽_{p^f}), and a
subgroup Γ' (the field `subgroup`) of Γ of index prime to p, with four properties. The image j(Γ')
fixes Λ and θ(z), and it contains every element of G_p that fixes Λ and θ(z). Γ' contains all g with
j(g) close enough to 1, that is, ∀ᶠ g in `New.Period.nearOne` Γ, g ∈ Γ'. For each l ≥ 0 some g in Γ'
has g z = [ε]^l z. -/
class KummerChart extends chart : Chart where
  /-- The subgroup `Γ'` of `Γ` whose fixed field the chart belongs to. -/
  subgroup : Subgroup Γ
  /-- The index of `Γ'` in `Γ` is prime to `p`. -/
  index_coprime : subgroup.index.Coprime p
  /-- Every element of `Γ'` fixes the constants `Λ` and `θ(z)`. -/
  fixes (g : subgroup) : chart.FixesThetaZ (toGp (g : Γ))
  /-- Every element of `G_p` that fixes `Λ` pointwise and fixes `θ(z)` lies in `j Γ'`. -/
  isChartOf : chart.IsChartOf (toGp.comp subgroup.subtype)
  /-- The elements of `Γ` whose image under `j` is close enough to `1` lie in `Γ'`. -/
  nearOne_le : nearOne Γ ≤ Filter.map subgroup.subtype ⊤
  /-- For every natural number `l`, some `g` in `Γ'` has `g z = [ε] ^ l z`. -/
  exists_smul_z (l : ℕ) :
    ∃ g : subgroup, toGp (g : Γ) • (chart.z : Ainf) = teichmuller p epsTilt ^ l * chart.z

/-- The map `thetaPhiInv a` = θ ∘ φ^{−a} sends φ^a • r to θ(r), for r in A_inf and φ = (1, 1). -/
@[simp]
lemma KummerChart.thetaPhiInv_phi_pow [GroupOverGp p] (a : ℕ) (r : Ainf) :
    thetaPhiInv a (FrobGroup.φ ^ a • r) = theta r := by
  induction a with
  | zero => simp [thetaPhiInv]
  | succ a ih => simp [pow_succ', mul_smul, phi_smul_ainf, ih]

variable {Γ} [k : KummerChart Γ]

/-- The number d = 0 if the ramification index e of the chart is 1, and d = v_p(e) + 1 otherwise. -/
def KummerChart.differentBound : ℕ := if k.e = 1 then 0 else padicValNat p k.e + 1

/-- The Kummer chart is unramified: E = z + p and the ramification index e is 1. The third
condition d = 0 follows from e = 1 by the definition of `New.Lift.KummerChart.differentBound`; it is
recorded for convenience. -/
def KummerChart.IsUnramified : Prop := k.E = k.z + p ∧ k.e = 1 ∧ k.differentBound = 0

/-- The chart of a Kummer chart belongs to the field fixed by j(Γ): every element of G_p that fixes
Λ pointwise and fixes θ(z) lies in j(Γ). -/
lemma KummerChart.chart_isChartOf : k.chart.IsChartOf Γ.overGp.toGp := by
  intro σ hσ
  obtain ⟨g, hg⟩ := k.isChartOf σ hσ
  exact ⟨g, hg⟩

/-- Let Γ act on Q̄_p through j : Γ → G_p, and let c be a chart whose element ϖ^♭ of O^♭ has untilt
π₀ ∈ Q̄_p. If j(Γ) is transitive on the n-th roots of π₀ for every n > 0, then for every l some
g ∈ Γ moves z = [ϖ^♭] to [ε]^l z. -/
lemma Chart.exists_smul_z_eq_of_transitive (c : Chart) (Γ : Type) [Group Γ] [𝒥 : OverGp Γ p]
    {π₀ : PadicAlgCl p}
    (h_transitive : ∀ {x y : PadicAlgCl p} {n : ℕ}, 0 < n → x ^ n = π₀ → y ^ n = x ^ n →
      ∃ g ∈ 𝒥.toGp.range, g • x = y)
    (h_untilt : (c.varpiFlat.untilt : ℂ_[p]) = π₀) (l : ℕ) :
    ∃ g : Γ, 𝒥.toGp g • (c.z : Ainf) = teichmuller p epsTilt ^ l * c.z := by
  -- `ε` has untilt `1`, so `ε ^ l ϖ^♭` and `ϖ^♭` have the same untilt
  have h_eps_untilt : (epsTilt ^ l * c.varpiFlat).untilt ^ 1 = c.varpiFlat.untilt ^ 1 := by simp
  simpa [c.z_eq_teichmuller] using exists_smul_teichmuller_eq 𝒥.toGp.range h_transitive c.varpiFlat
    (epsTilt ^ l * c.varpiFlat) 1 (by simpa using h_untilt) h_eps_untilt

/-- Let K be the subfield of Q̄_p fixed by an open subgroup V of G_p, local with group V (`L`),
whose normalised order is e times that of ℚ_p (`h_ord`). Then for an irreducible element π of the
integers of K, π^e is −p times a unit. -/
lemma associated_pow_neg_of_irreducible (V : OpenSubgroup (Gp p)) {e : ℕ}
    (L : IsLocalGalois (V : Subgroup (Gp p)) (fixedFieldOf (V : Subgroup (Gp p))) (intQpBar p))
    (h_ord : ordRat (fixedFieldOf (V : Subgroup (Gp p))) (intQpBar p) =
      e • ordRat ℚ_[p] (intQpBar p))
    {π : valRingBelow (fixedFieldOf (V : Subgroup (Gp p))) (intQpBar p)} (hπ : Irreducible π) :
    Associated (π ^ e) (-p) := by
  have h_dvr := L.isDiscreteValuationRing
  -- `π` has order `1` over `K`, so `1 / e` over `ℚ_[p]`: `π ^ e` and `p` have the same valuation
  have h_one :=
    (isUniformiser_iff_irreducible.mpr ⟨_, hπ⟩).ordRat_eq_one L (π := .mk0 π (mod_cast hπ.ne_zero))
  -- `using!`: `h_one` is about `DiscreteUnits.ofBase` of `π`, equal to `π` only up to unfolding
  simpa [← dvd_dvd_iff_associated, ← ge_antisymm_iff, dvd_iff_valuationVia_le,
    valuationVia] using!
    (isUniformiser_ell.valuation_pow_eq_zpow_iff_mul_ordRat_eq isLocalGalois_padic _ 1).mpr
      (by simpa [h_ord] using h_one)

/-- A Kummer chart `k` for `Γ`, seen in `G_p` through `j = 𝒥.toGp`, fits the field fixed by
`j(Γ)`: the four properties that `exists_kummerChart` provides. -/
structure KummerChart.IsChartFor (Γ : Type) [Group Γ] [𝒥 : OverGp Γ p] (k : KummerChart ⟨Γ⟩) :
    Prop where
  /-- All of `j(Γ)` fixes `Λ` pointwise and `θ(z)`. -/
  fixes_thetaZ : ∀ g : Γ, k.FixesThetaZ (𝒥.toGp g)
  /-- The ramification index times the residue degree is the index `[G_p : j(Γ)]`. -/
  e_mul_f_eq_index : k.e * k.f = 𝒥.toGp.range.index
  /-- If `j(Γ)` contains the inertia group of `G_p`, the chart is unramified. -/
  isUnramified_of_inertia_le : inertiaGroup (Gp p) (intQpBar p) ≤ 𝒥.toGp.range → k.IsUnramified
  /-- `j(Γ)` contains an element `φ` with `φ x ≡ x ^ (p ^ f)` on the integers of `ℚ̄_p`, modulo
  their maximal ideal. -/
  exists_isFrob : ∃ φ ∈ 𝒥.toGp.range, IsFrob (intQpBar p) (p ^ k.f.val) φ

/-- The Kummer chart of the field fixed by j(Γ), where `Γ` carries a homomorphism j to G_p with open
image. There is a Kummer chart for Γ over Λ = W(F_{p^f}), with coordinate z (a Teichmüller lift in
A_inf) and E = z^e A + p with A a unit, that fits that field (`KummerChart.IsChartFor`): j(Γ) fixes
Λ and θ(z), ef = [G_p : j(Γ)], the chart is unramified if j(Γ) contains inertia, and j(Γ) contains a
Frobenius. -/
lemma exists_kummerChart (Γ : Type) [Group Γ] [𝒥 : OverGp Γ p] :
    ∃ k : KummerChart ⟨Γ⟩, KummerChart.IsChartFor Γ k := by
  -- Let `K` be the fixed field, with ramification index `e`, residue degree `f` and a uniformiser
  -- `π`, so `π ^ e * v = -p`. Take the chart with `θ z = π`. As `θ` maps the power series onto the
  -- integers of `K`, the unit `v` lifts to a unit `A` and the fixer of the chart lies in
  -- `toGp.range`. `K` is local (`L`), with `e * f` the index, residue field of order `p ^ f`, order
  -- function `e` times that of `ℚ_[p]`, and `e = 1` if `toGp.range` contains inertia.
  -- These facts come from the fields of `IsLocalExtension`.
  obtain ⟨L, ⟨e, f, ⟨h_index, h_card, h_ord⟩, h_unram⟩, -⟩ :=
    IsLocalGalois.of_finite (k := ℚ_[p]) (A := intQpBar p) ⟨𝒥.toGp.range, 𝒥.isOpen_range.out⟩
  rw [residueCard_padic] at h_card
  -- a finite field has more than `p ^ 0 = 1` element
  have h_f_ne : f ≠ 0 := fun hf ↦ by simpa [hf, h_card] using L.finite_residue.one_lt_card
  lift f to ℕ+ using Nat.pos_of_ne_zero h_f_ne
  -- a Frobenius `φ` of `K`; the products of its powers with inertia are dense in `toGp.range`
  obtain ⟨⟨φ, hφ⟩, h_dense, -⟩ := L.frobenius_spec
  rw [h_card] at hφ h_dense
  have h_dvr := L.isDiscreteValuationRing
  obtain ⟨π, hπ⟩ : ∃ π : valRingBelow (localFieldOf Γ) (intQpBar p), Irreducible π :=
    h_dvr.exists_irreducible
  obtain ⟨v, hv⟩ : Associated (π ^ e) (-p) := associated_pow_neg_of_irreducible _ L h_ord hπ
  -- if `e = 1`, take `π = -p`
  wlog hv_one : e = 1 → v = 1 generalizing π v
  · have he : e = 1 := of_not_imp hv_one
    exact this _ ((irreducible_mul_units v).mpr hπ) 1 (by simp [he, ← hv]) fun _ ↦ rfl
  -- inertia and `φ` fix every `ζ` with `ζ ^ (p ^ f - 1) = 1`, hence so does all of `toGp.range`
  have h_fix (g : 𝒥.toGp.range) : FixesLambda f (g : Gp p) := by
    refine (fixes_roots_iff_fixesLambda _).mp fun ζ hζ ↦
      (h_dense hφ).induction_on g (isClosed_setOf_smul ζ fun x ↦ x = ζ) fun n ↦ ?_
    refine (apply_eq_pow_of_isFrob ((hφ.pow n.fst).mul_iff.mpr n.snd.prop)
      not_dvd_pow_sub_one hζ).trans ?_
    simp [pow_eq_pow_of_modEq ((Nat.modEq_sub one_le).pow _) hζ]
  -- `κ` is the inclusion of the integers of `K` in those of `ℂ_[p]`
  let κ : valRingBelow (localFieldOf Γ) (intQpBar p) →+* valRingCp p :=
    ((algebraMap ..).comp (localFieldOf Γ).val.toRingHom).restrict _ _ (by simp [← coe_nnnorm])
  -- `ev : Λ⟦X⟧ → A_inf` has `θ (ev X) = π`; each unit series `A` with `θ (ev A) = v` gives a chart
  obtain ⟨ev, h_evX, h_chart⟩ :=
    exists_chart_of_pow_mul_eq_neg f (v.map κ) (by simpa using congrArg κ hv)
  -- `O_C` is `π`-adically separated, since `p ∣ π ^ e`
  have h_sep : IsHausdorff (span {κ π}) OC := by
    refine ⟨fun x h ↦ eq_of_forall_pow_dvd_sub ↑p fun n ↦ ?_⟩
    grw [← map_natCast κ, neg_dvd.mp (Associated.dvd' ⟨v, hv⟩), map_pow, ← pow_mul,
      smodEq_span_pow_iff_dvd.mp (h _)]
  -- `θ` maps `Λ` into the integers of `K` (by `τ`), and every integer of `K` is a Teichmüller
  -- constant modulo `π` (`using!` below: the fact bounds `‖·‖`, the goal `‖·‖₊`)
  let τ : WittFq f →+* valRingBelow (localFieldOf Γ) (intQpBar p) :=
    (wittToQpBar.toRingHom.codRestrict (localFieldOf Γ) fun _ _ ↦
      smul_algebraMap_wittFq_eq_iff.mp (h_fix ..))
      |>.codRestrict _ fun a ↦ by simpa [← coe_wittToQpBar] using! (theta (algebraMap _ _ a)).prop
  have h_approx (x : valRingBelow (localFieldOf Γ) (intQpBar p)) :
      ∃ (n : (WittFq f)⟦X⟧) (y : valRingBelow (localFieldOf Γ) (intQpBar p)),
        κ x = theta (ev n) + κ π • κ y := by
    have h_fin := L.finite_residue
    have h_root : residue _ x ≠ 0 → residue _ x ^ (p ^ f.val - 1) = 1 := fun hx ↦ by
      simp [hx, ← h_card, FiniteField.pow_card_sub_one_eq_one]
    obtain ⟨a, ha⟩ := exists_flatFq_teichmuller_eq ((residue _).comp τ) (residue _ x) h_root
    obtain ⟨y, hy⟩ : π ∣ x - τ (teichmuller p a) := by
      rw [← mem_span_singleton, ← hπ.maximalIdeal_eq]
      exact Ideal.Quotient.eq.mp ha.symm
    use C (teichmuller p a), y
    simpa [eq_add_of_sub_eq' hy, C_eq_algebraMap] using Subtype.ext coe_wittToQpBar
  -- so all of them are values of `θ ∘ ev`, by successive approximation
  have h_lift (x : valRingBelow (localFieldOf Γ) (intQpBar p)) :
      ∃ n : (WittFq f)⟦X⟧, theta (ev n) = κ x :=
    mem_range_of_approx (π := (X : (WittFq f)⟦X⟧)) (π' := κ π)
      (theta.comp ev.toRingHom).toAddMonoidHom (by simp [h_evX]) κ h_approx x
  choose V hV using h_lift
  -- the lift `V v - V 1 + 1` of `v` is a unit, and it is `1` if `v = 1`
  have hA : IsUnit (V v - V 1 + 1) := by
    refine (IsUnit.mul_iff.mp (isUnit_of_mem_nonunits_one_sub_self (_ * V ↑v⁻¹) fun h ↦ ?_)).left
    simpa [hV, ← map_mul κ] using (h.map ev).map theta
  obtain ⟨c, rfl, rfl, hu, rfl, hc⟩ := h_chart hA.unit (by simp [hV])
  -- `toGp.range` fixes the constants, and it fixes `θ z = π`, which lies in `K`
  have h_chart_fix (g : Γ) : c.FixesThetaZ (𝒥.toGp g) := by
    refine ⟨h_fix ⟨𝒥.toGp g, g, rfl⟩, ?_⟩
    simp [hu, c.z_eq_teichmuller, κ, ← coe_eq, mem_localFieldOf.mp, Subtype.ext_iff]
  -- what fixes the chart fixes each `x` in `K`, as `x` or its inverse is an integer
  have h_sees (σ : Gp p) (hσ : c.FixesThetaZ σ) : σ ∈ 𝒥.toGp.range := by
    refine (fixingSubgroup_fixedFieldOf 𝒥.toGp.range).le fun x ↦ ?_
    -- the two cases are alike: `x` or `x⁻¹` is `θ` of an element of the chart ring
    obtain h | h := (valRingBelow (localFieldOf Γ) (intQpBar p)).mem_or_inv_mem x <;>
      simpa [hV, κ, ← coe_eq, Subtype.ext_iff] using
        c.smul_theta_of_fixesThetaZ hσ ⟨_, V ⟨_, h⟩, rfl⟩
  -- the inertia group of `K`, inside `toGp.range`, is transitive on the roots of `π`
  have h_roots {x y : PadicAlgCl p} {n : ℕ} (hn : 0 < n)
      (hx : x ^ n = ((π : localFieldOf Γ) : PadicAlgCl p)) (hy : y ^ n = x ^ n) :
      ∃ g ∈ 𝒥.toGp.range, g • x = y := by
    obtain ⟨g, -, hg_smul⟩ := L.exists_inertia_smul_eq_of_pow_eq
      (π := .mk0 π.val (mod_cast hπ.ne_zero)) (isUniformiser_iff_irreducible.mpr ⟨_, hπ⟩) hn hx hy
    exact ⟨g, g.prop, hg_smul⟩
  have h_kummer (l : ℕ) : ∃ g : Γ, 𝒥.toGp g • (c.z : Ainf) = teichmuller p epsTilt ^ l * c.z :=
    c.exists_smul_z_eq_of_transitive Γ h_roots (by simp [hu, κ, coe_eq]) l
  refine ⟨{ chart := c, subgroup := ⊤, index_coprime := by simp, fixes := fun g ↦ h_chart_fix g,
            isChartOf := by simpa [Chart.IsChartOf] using h_sees, nearOne_le := by simp,
            exists_smul_z := by simpa using h_kummer },
    h_chart_fix, h_index, fun h ↦ ?_, φ, φ.prop, hφ⟩
  -- if `toGp.range` contains inertia, then `e = 1`, so `v = 1` and its lift is `1`
  simp [KummerChart.IsUnramified, KummerChart.differentBound, Chart.E, hc.eq, h_unram h, hv_one]

end KummerChartExists

end New.Lift

end
