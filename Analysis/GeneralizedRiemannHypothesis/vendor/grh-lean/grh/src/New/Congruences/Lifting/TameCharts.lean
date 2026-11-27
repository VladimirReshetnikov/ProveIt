import New.Congruences.Lifting.CupProductBound

/-!
# Tame Kummer charts and the power of p that kills cokernels of Kisin modules

A tame chart `New.Lift.TameChart` is a Kummer chart `New.Lift.KummerChart`, with coordinate `z` and
exponent `e`, together with an element `s` of inertia. The power `s ^ k` multiplies `z` by `ξ ^ k`,
for some `ξ` in Λ = W(𝔽_{p^f}) that is a primitive e-th root of unity modulo `p`. The degree of a
polynomial that kills the operator induced by `s` bounds the power of `p` that kills the cokernel of
the map of Kisin modules attached to an extension of a trivial lattice `C` by a lattice `Y`. The
file also shows that, if Γ maps onto G_p, tame charts exist for each ramification index e dividing
p^f − 1, when p does not divide f.

## Main definitions and results

* `New.Lift.TameChart.exists_z_smul_eq_sum_tameGen`: if a polynomial `q` over `ℤ_p` kills the
  operator β induced by `s`, then `q(s)` maps the Kisin module into `z` times
  `New.Lift.KummerChart.JumpLattice.kisinAinf`.
* `New.Lift.TameChart.killsCokernel_of_isKilledBy`: if `Y` is potentially crystalline and a monic
  `q` kills β on `Y`, then `p ^ κ` kills the cokernel, that is, multiplies the constants of `C` into
  the image, as soon as `m (deg q + 1) ≤ κ`, `e ≤ p ^ m` and `p` is large against `κ` and the jumps.
* `New.Lift.exists_tameChart`: tame charts exist.

Notions from other files:
* `New.Lift.WittFq`: The ring Λ = W(𝔽_{p^f}) of constants, 𝔽_{p^f} taken inside the tilt O^♭.
* `New.Period.linearFrob`: For s in inertia, `linearFrob ρ s 0` is the B-linear operator β on B ⊗ T
  (B = `Bmax`) that acts as s on the vectors fixed by the elements of Γ near 1.
* `New.Lift.KummerChart.Letter`: A letter is a unit i of 𝔽_{p^f}. The coefficient ring O carries an
  element ζ with ζ^{p^f−1} = 1, and the letter-i part of W(C^♭) ⊗ L is where ζ acts as [i].

## Relation to the literature

See `New.Congruences.Lifting.CupOrthogonalityBounds` for related work.
-/

namespace New.Lift

/-!
## Tame charts and the power of p killing the cokernel of Kisin modules

Idea of the proof of `New.Lift.TameChart.killsCokernel_of_isKilledBy`: start from a power `z ^ ν`,
`ν < e`, in the ideal of multipliers and lower the exponent one step at a time.
-/

section TameKiller

open KummerChart JumpLattice Period WittVector Submodule FrobGroup Module Finset Polynomial
  LinearMap PairingSide algebraMap

/-- A tame Kummer chart for `Γ → G_p`. A Kummer chart gives constants `Λ = W(𝔽_{p^f})`, a
coordinate `z = chart.z ∈ A_inf`, an exponent `e` and a subgroup `Γ'` of `Γ` that fixes `Λ` and
`θ(z)`. A tame chart has `Γ'` normal and `p ∤ e`, an element `ϖ ∈ ℚ̄_p` fixed by `Γ'` with
`ϖ ^ e = p`, and an element `s ∈ Γ` with image in inertia (`IsWeilPair (toGp s) 0`) whose powers fix
`Λ` pointwise in `A_inf` (`FixesLambda`), such that `s ^ k` multiplies `z` by `ξ ^ k`. Here `ξ ∈ Λ`
is, modulo `p`, a primitive `e`-th root of unity. -/
class TameChart {p : outParam ℕ} [ThePrime p] (Γ : outParam (GroupOverGp p)) extends
    KummerChart Γ where
  /-- The element ξ of Λ = W(𝔽_{p^f}) by which the tame generator multiplies z. -/
  tameMultiplier : WittFq f
  /-- The tame generator s, an element of Γ. -/
  tameGen : Γ
  /-- Modulo p, ξ is a primitive e-th root of unity, e the exponent of the chart. -/
  isPrimitiveRoot_tameMultiplier : IsPrimitiveRoot (tameMultiplier.coeff 0) e
  /-- s^k z = ξ^k z. -/
  tameGen_pow_smul_z (k : ℕ) : toGp (tameGen ^ k) • chart.z.val = ↑(tameMultiplier ^ k) * chart.z
  /-- s lies in inertia. -/
  isWeilPair_tameGen : IsWeilPair (toGp tameGen) 0
  /-- Every power of s fixes Λ. -/
  fixesLambda_tameGen_pow (k : ℕ) : FixesLambda f (toGp (tameGen ^ k))
  /-- An element ϖ, an e-th root of p. -/
  ϖ : PadicAlgCl p
  /-- Every element of Γ' fixes ϖ. -/
  apply_varpi (g : subgroup) : toGp g.val ϖ = ϖ
  /-- ϖ^e = p. -/
  varpi_pow_eq : ϖ ^ e = p
  /-- p does not divide e. -/
  tame : ¬p ∣ e
  /-- Γ' is normal in Γ. -/
  [normal : subgroup.Normal]

namespace TameChart

open scoped TensorProduct

/-- Let `Γ` be a group with a map to `G_p = Gal(ℚ̄_p/ℚ_p)` of open image, and let `d` be a tame
chart for it. In particular, `d` gives a normal subgroup `Γ'` of `Γ` of index prime to `p`. Let `O`
be a finite free `ℤ_p`-algebra and `L` a finite free `O`-module with an action of `Γ` whose
restriction to `Γ'` is crystalline. Let `μ : W(C^♭) ⊗ L → B_dR` be a crystalline form: it is
`A_inf`-linear, `Γ'`-equivariant on `1 ⊗ L`, and its values on `1 ⊗ L` come from a `ℤ_p`-linear map
`L → Bmax`. Then its conjugate `x ↦ g⁻¹ μ(g x)` by `g ∈ Γ` is a crystalline form. -/
lemma conjForm_mem_crysForms {p : ℕ} [ThePrime p] [Γ : GroupOverGp p] {d : TameChart Γ}
    {O : d.Coeffs} {L : d.JumpLattice O}
    {μ : L.Functional} (hμ : μ ∈ L.crysForms) (g : Γ) : conjForm μ g ∈ L.crysForms := by
  obtain ⟨h_equiv, l, hl⟩ : μ ∈ L.forms ∧ ∃ l : L.Carrier →ₗ[ℤ_[p]] Bmax,
      ∀ t : L.Carrier, μ (DiagTensor.mk 1 t) = algebraMap Bmax BdR (l t) := hμ
  have h_normal : ∀ h ∈ d.subgroup, g * h * g⁻¹ ∈ d.subgroup := fun h hh ↦ d.normal.conj_mem h hh g
  -- The values of the conjugate form on `1 ⊗ L` come from the conjugate `t ↦ g⁻¹ l(g t)` of `l`.
  let l' : L.Carrier →ₗ[ℤ_[p]] Bmax :=
    DistribSMul.toLinearMap ℤ_[p] Bmax (toGp g)⁻¹ ∘ₗ l ∘ₗ overZp L.ρ g
  have hl' (t : L.Carrier) : conjForm μ g (DiagTensor.mk 1 t) = algebraMap Bmax BdR (l' t) := by
    simp [l', hl]
  exact ⟨conjForm_mem_forms h_normal h_equiv, l', hl'⟩

/-- Let `d` be a tame chart for a group `Γ → G_p`, with subgroup `Γ'` and inertia element
`s = d.tameGen`. Let `O` be a finite free `ℤ_p`-algebra and `L` a finite free `O`-module with an
action of `Γ` that is crystalline over `Γ'`.
* `β = linearFrob L.ρ s 0` is the `Bmax`-linear operator on `Bmax ⊗ L` that acts as `s` on the
  vectors fixed by the elements of `Γ` near `1`, and `q = ∑ q_k X ^ k` is a polynomial over `ℤ_p`
  with `q(β) = 0`.
* `μ : W(C^♭) ⊗ L → B_dR` is a crystalline form: it is `A_inf`-linear, `Γ'`-equivariant on `1 ⊗ L`,
  and its values on `1 ⊗ L` come from a `ℤ_p`-linear map `L → Bmax`.
* `x` lies in `L.kisinAinf`: it lies in `A_inf[1/τ] ⊗ L`, `τ = [ε^{1/p}] - 1`, and every
  `A_inf`-linear map to `B_dR` that is `Γ'`-equivariant on `1 ⊗ L` sends `φ ^ n x` into `B_dR⁺` for
  all `n ≥ 1`, with `φ` the Frobenius.

Then `∑ q_k • μ_k x = 0`, where `μ_k = conjForm μ (s ^ k)` is the conjugate `y ↦ s⁻ᵏ μ(sᵏ y)`. -/
lemma sum_coeff_smul_conjForm_apply_eq_zero {p : ℕ} [ThePrime p] [Γ : GroupOverGp p]
    {d : TameChart Γ} {O : d.Coeffs} {L : d.JumpLattice O}
    {q : ℤ_[p][X]} (hq_kills : aeval (linearFrob L.ρ d.tameGen 0) q = 0)
    {μ : L.Functional} (hμ_crys : μ ∈ L.crysForms)
    {x : L.Ambient} (hx_mem : x ∈ L.kisinAinf) :
    ∑ k ∈ range (q.natDegree + 1), q.coeff k • conjForm μ (d.tameGen ^ k) x = 0 := by
  -- The conjugates of `μ` define linear forms `ℓ g` on `Bmax ⊗ L` with `ℓ 1 ∘ β ^ k = ℓ (s ^ k)`,
  -- so `q(β) = 0` gives a relation among the `ℓ (s ^ k)`, which is carried back to the `μ_k`.
  obtain ⟨hμ_equiv, l, hl⟩ : μ ∈ L.forms ∧ ∃ l : L.Carrier →ₗ[ℤ_[p]] Bmax,
      ∀ t : L.Carrier, μ (DiagTensor.mk 1 t) = algebraMap Bmax BdR (l t) := hμ_crys
  have h_crys : IsPotentiallyCrystalline L.ρ := L.inClass.isPotentiallyCrystalline
  let ℓ (g : Γ) : Bmax ⊗[ℤ_[p]] L.Carrier →ₗ[Bmax] Bmax :=
    (DistribSMul.toLinearMap ℤ_[p] Bmax (toGp g)⁻¹ ∘ₗ l ∘ₗ overZp L.ρ g).liftBaseChange Bmax
  have hℓ_tmul (g : Γ) (t : L.Carrier) :
      algebraMap Bmax BdR (ℓ g (1 ⊗ₜ t)) = conjForm μ g (DiagTensor.mk 1 t) := by
    simp [ℓ, hl]
  have hℓ_act (g g' : Γ) (y : Bmax ⊗[ℤ_[p]] L.Carrier) :
      ℓ g' (tensorAction Bmax (toGp g) (L.ρ g) y) = toGp g • ℓ (g' * g) y := by
    induction y with
    | tmul b t => simp [ℓ, tensorAction, mul_smul]
    | add y y' hy hy' => simp only [map_add, smul_add, hy, hy']
  have hℓ_coset (u : Γ) (g : d.subgroup) : ℓ (u * g) = ℓ u := by
    ext t
    have h_equiv : conjForm μ u (DiagTensor.mk 1 (L.ρ g t)) =
        toGp g.val • conjForm μ u (DiagTensor.mk 1 t) :=
      conjForm_mem_forms (fun h hh ↦ d.normal.conj_mem h hh u) hμ_equiv t g
    simpa [ℓ, hl, mul_smul, inv_smul_eq_iff, -map_pow] using h_equiv
  -- The relation is tested on the vectors `y` fixed near `1`, which span.
  have hℓ_rel : ∑ k ∈ range (q.natDegree + 1), q.coeff k • ℓ (d.tameGen ^ k) = 0 := by
    refine ext_on h_crys fun y hy ↦ ?_
    have h_fixed (u : Γ) : ∀ᶠ g in nearOne Γ, toGp g • ℓ u y = ℓ u y := by
      -- It suffices to consider `g ∈ Γ'`, since `Γ'` contains the elements near `1`.
      refine Filter.Eventually.mp hy (d.nearOne_le fun g hg ↦ ?_)
      calc toGp g.val • ℓ u y
          = ℓ u (tensorAction Bmax (toGp g.val) (L.ρ g) y) := by rw [hℓ_act, hℓ_coset]
        _ = ℓ u y := congrArg (ℓ u) hg
    -- `ℓ (s ^ k) y` is fixed near `1`, hence by the inertia element `s ^ k`.
    have h_beta (k : ℕ) : ℓ 1 (linearFrob L.ρ (d.tameGen ^ k) 0 y) = ℓ (d.tameGen ^ k) y := by
      have hs : IsWeilPair (toGp (d.tameGen ^ k)) 0 := d.isWeilPair_tameGen.pow k
      have h_frob : linearFrob L.ρ (d.tameGen ^ k) 0 y =
          tensorAction Bmax (toGp (d.tameGen ^ k)) (L.ρ (d.tameGen ^ k)) y :=
        linearFrob_apply h_crys hs hy
      calc ℓ 1 (linearFrob L.ρ (d.tameGen ^ k) 0 y)
          = toGp (d.tameGen ^ k) • ℓ (d.tameGen ^ k) y := by rw [h_frob, hℓ_act, one_mul]
        _ = ℓ (d.tameGen ^ k) y := hs.smul_eq_of_fixed_nearOne (h_fixed (d.tameGen ^ k))
    have h_eval : ℓ 1 (aeval (linearFrob L.ρ d.tameGen 0) q y) = 0 := by simp [hq_kills]
    simpa [h_beta, ← linearFrob_pow h_crys d.isWeilPair_tameGen, aeval_eq_sum_range] using h_eval
  -- Forms that agree on `1 ⊗ L` agree on `kisinAinf`.
  have h_values :
      basisValues (∑ k ∈ range (q.natDegree + 1), q.coeff k • conjForm μ (d.tameGen ^ k)) =
        basisValues 0 := by
    ext i
    have h_rel (t : L.Carrier) : algebraMap Bmax BdR
        ((∑ k ∈ range (q.natDegree + 1), q.coeff k • ℓ (d.tameGen ^ k)) (1 ⊗ₜ t)) = 0 := by
      simp [hℓ_rel]
    simpa [basisValues, algebraMap.smul, hℓ_tmul] using h_rel _
  simpa using apply_eq_of_mem_fracSpan _ 0 h_values (kisinAinf_le_fracSpan hx_mem)

/-- Let `Γ` be a group over `G_p = Gal(ℚ̄_p/ℚ_p)` with a tame chart `d`: this gives an element
`z = d.z` of `A_inf`, a subgroup `Γ'` of `Γ`, and an element `s = d.tameGen` with image in inertia
that multiplies `z` by a constant. Let `L` be a finite free module over a finite free `ℤ_p`-algebra,
with an action of `Γ` that is crystalline over `Γ'`. Let `q` over `ℤ_p` kill the operator
`β = linearFrob L.ρ s 0` that `s` induces on `Bmax ⊗ L`.

The `A_inf`-module `L.kisinAinf` consists of the `y` in `A_inf[1/τ] ⊗ L`, `τ = [ε^{1/p}] - 1`, such
that every `Γ'`-equivariant form sends `φ ^ n y` into `B_dR⁺` for all `n ≥ 1`, with `φ` the
Frobenius. Such a `y` is in `L.kisinModule` if, moreover, these forms take at `y` values in the
subfield `valueField 0` of `B_dR`, which the chart generates over the field fixed by `Γ'`.

Then, for `x` in `L.kisinModule`, `∑ q_k • s ^ k • x` is `z` times an element of `L.kisinAinf`. -/
lemma exists_z_smul_eq_sum_tameGen {p : ℕ} [ThePrime p] [Γ : GroupOverGp p] {d : TameChart Γ}
    {O : d.Coeffs} {L : d.JumpLattice O}
    {q : ℤ_[p][X]} (hq_kills : aeval (linearFrob L.ρ d.tameGen 0) q = 0)
    {x : L.Ambient} (hx : x ∈ L.kisinModule) :
    ∃ y ∈ L.kisinAinf,
      d.z.val • y =
        ∑ k ∈ Finset.range (q.natDegree + 1), q.coeff k • FrobGroup.inr (d.tameGen ^ k) • x := by
  -- Write `μ_k` for the conjugate by `s ^ k` of a crystalline form `μ`. As `∑ q_k • μ_k x = 0`, the
  -- value of `μ` on the sum is `∑ q_k • (s ^ k - 1) (μ_k x)`, and `s ^ k - 1` produces a factor `z`
  -- once the denominators, powers of `E`, are cleared.
  have hx_ainf : x ∈ L.kisinAinf := hx.1
  obtain ⟨-, n, h_denominators⟩ := mem_kisinModule_iff_crysForms.mp hx
  set w : L.Ambient := ∑ k ∈ range (q.natDegree + 1), q.coeff k • inr (d.tameGen ^ k) • x with hw
  have hw_mem : w ∈ L.kisinAinf := sum_mem fun k _ ↦ smul_of_tower_mem _ (q.coeff k) <|
    smul_mem_kisinAinf (fun h hh ↦ d.normal.conj_mem h hh _) hx_ainf
  rw [← mem_smul_pointwise_iff_exists]
  refine mem_smul_kisinAinf_of_crysForms d.z_dvd_of_dvd_E_pow_mul hw_mem (n := 2 * n)
    fun μ hμ ↦ ?_
  have h_term (k : ℕ) :
      d.E.val ^ (2 * n) •
          (toGp (d.tameGen ^ k) • conjForm μ (d.tameGen ^ k) x - conjForm μ (d.tameGen ^ k) x) ∈
        BPlus ∙ algebraMap Ainf BdR d.z.val :=
    pow_smul_gal_sub_mem_span_of_dvd (d.z_dvd_sub (d.fixesLambda_tameGen_pow k))
      (h_denominators _ (conjForm_mem_crysForms hμ _))
  have h_value :
      μ w = ∑ k ∈ range (q.natDegree + 1), q.coeff k •
        (toGp (d.tameGen ^ k) • conjForm μ (d.tameGen ^ k) x - conjForm μ (d.tameGen ^ k) x) := by
    simp only [smul_sub, sum_sub_distrib,
      sum_coeff_smul_conjForm_apply_eq_zero hq_kills hμ hx_ainf]
    simp [hw]
  simpa only [h_value, smul_sum, smul_comm (d.E.val ^ (2 * n))] using
    sum_mem fun k _ ↦ smul_of_tower_mem _ (q.coeff k) (h_term k)

/-- Let `Γ` be a group over `G_p = Gal(ℚ̄_p/ℚ_p)`, `d` a tame chart for it, with tame generator `s`,
and `O` a finite free `ℤ_p`-algebra. A pairing side `S` consists of two lattices `Y` and `C` over
`O` with actions of `Γ` and an `O`-linear map from `C` to the crystalline cocycles of `Y`. It gives
the extension `Ỹ = S.extensionLattice` of `C`, with trivial action, by `Y`.

The hypothesis `IsKilledBy` says that `Y` is potentially crystalline and that `q`, a polynomial over
`ℤ_p` read over `O`, kills the operator `β` induced by `s` on `Bmax ⊗ Y`. Then `q * (X - 1)` kills
the operator `β` on `Bmax ⊗ Ỹ`. -/
lemma aeval_linearFrob_extensionLattice_eq_zero {p : ℕ} [ThePrime p] [Γ : GroupOverGp p]
    {d : TameChart Γ} {O : d.Coeffs} {q : ℤ_[p][X]} {S : d.PairingSide O}
    (hY_killed : IsKilledBy S.ρ d.tameGen 0 (q.map (algebraMap ℤ_[p] O))) :
    aeval (linearFrob S.extensionLattice.ρ d.tameGen 0) (q * (X - 1)) = 0 := by
  -- `β - 1` maps into `Bmax ⊗ Y`, as `β = 1` on the trivial quotient; and there `q(β) = 0`.
  obtain ⟨hY_crys, hq_zero⟩ := hY_killed
  have h_crys : IsPotentiallyCrystalline S.extensionLattice.ρ :=
    S.extensionLattice.inClass.isPotentiallyCrystalline
  set β : End Bmax (Bmax ⊗[ℤ_[p]] S.extensionLattice.Carrier) :=
    linearFrob S.extensionLattice.ρ d.tameGen 0
  let ι : S.Carrier →ₗ[ℤ_[p]] S.extensionLattice.Carrier :=
    LinearMap.inl ℤ_[p] S.Carrier S.paramLattice
  let π : S.extensionLattice.Carrier →ₗ[ℤ_[p]] S.trivialLattice.Carrier :=
    LinearMap.snd ℤ_[p] S.Carrier S.paramLattice
  refine LinearMap.ext fun y ↦ ?_
  have h_triv : linearFrob S.trivialLattice.ρ d.tameGen 0 = 1 := by
    simp [IsCrystalline.linearFrob_eq_one, isAdmissible_of_cyclotomicGp_zpow 0, isWeilPair_tameGen]
  have h_quot : π.baseChange Bmax (β y - y) = 0 := by
    simp [baseChange_linearFrob h_crys d.isWeilPair_tameGen
      S.trivialLattice.inClass.isPotentiallyCrystalline π (by simp [π, extensionRep]), h_triv, β]
  obtain ⟨x, hx⟩ : ∃ x : Bmax ⊗[ℤ_[p]] S.Carrier, ι.baseChange Bmax x = β y - y :=
    (lTensor_exact Bmax .inl_snd snd_surjective _).1 h_quot
  -- The inclusion of `Y` commutes with `β`, hence with its powers.
  have h_comm : Function.Semiconj (ι.baseChange Bmax) (linearFrob S.ρ d.tameGen 0) β :=
    baseChange_linearFrob hY_crys d.isWeilPair_tameGen h_crys ι (by simp [ι, extensionRep])
  have hqY : aeval (linearFrob S.ρ d.tameGen 0) q = 0 := by
    simpa [eval₂_map, coeffEnd, aeval_def] using hq_zero
  calc aeval β (q * (X - 1)) y
      = aeval β q (ι.baseChange Bmax x) := by simp [hx]
    _ = ι.baseChange Bmax (aeval (linearFrob S.ρ d.tameGen 0) q x) := by
      simp [aeval_eq_sum_range, End.pow_apply, h_comm.iterate_right _ x]
    _ = 0 := by simp [hqY]

/-- A tame chart `d` has an exponent `e`, prime to `p`, and an element `ξ = d.tameMultiplier` of
`Λ = W(𝔽_{p^f})` whose residue in `𝔽_{p^f}`, its `constantCoeff`, is a primitive `e`-th root of
unity. So, for a monic polynomial `Q` over `ℤ_p` and `ν ≤ e`, at most `deg Q` of the `k < ν` make
the residue of `Q(ξ ^ k) ∈ Λ` zero. -/
lemma count_constantCoeff_aeval_tameMultiplier_pow_le {p : ℕ} [ThePrime p] [Γ : GroupOverGp p]
    {d : TameChart Γ} {Q : ℤ_[p][X]}
    (hQ : Q.Monic) {ν : ℕ} (hν : ν ≤ d.e)
    [DecidablePred fun k : ℕ ↦ constantCoeff (aeval (d.tameMultiplier ^ k) Q) = 0] :
    ν.count (fun k : ℕ ↦ constantCoeff (aeval (d.tameMultiplier ^ k) Q) = 0) ≤ Q.natDegree := by
  classical
  let red : ℤ_[p] →+* flatFq d.f := constantCoeff.comp (algebraMap ℤ_[p] (WittFq d.f))
  let bad : Finset ℕ := {k ∈ range ν | constantCoeff (aeval (d.tameMultiplier ^ k) Q) = 0}
  have h_roots : ∀ k ∈ bad, d.tameMultiplier.coeff 0 ^ k ∈ (Q.map red).roots := by
    simp +contextual [bad, red, aeval_def, hom_eval₂, eval_map, map_monic_ne_zero hQ,
      ← WittVector.constantCoeff_apply]
  have h_inj : Set.InjOn (fun k : ℕ ↦ d.tameMultiplier.coeff 0 ^ k) bad :=
    d.isPrimitiveRoot_tameMultiplier.injOn_pow.mono
      (coe_subset.2 ((filter_subset _ _).trans (range_mono hν)))
  calc ν.count (fun k : ℕ ↦ constantCoeff (aeval (d.tameMultiplier ^ k) Q) = 0)
      = #(bad.image fun k : ℕ ↦ d.tameMultiplier.coeff 0 ^ k) := by
        rw [Nat.count_eq_card_filter_range, card_image_of_injOn h_inj]
    _ ≤ (Q.map red).natDegree := card_le_degree_of_subset_roots (forall_mem_image.2 h_roots)
    _ ≤ Q.natDegree := natDegree_map_le

/-- Let `d` be a tame chart. It gives a coordinate `z = d.z ∈ A_inf` and a tame generator `s`, an
element of inertia that multiplies `z` by the constant
`ξ = d.tameMultiplier ∈ W(𝔽_{p^f}) = WittFq d.f`. Let `Ỹ` be the extension of `C` by `Y` given by
the pairing side `S`, and let `Q` over `ℤ_p`, with `Q(1) = 0`, kill the operator induced by `s` on
`Bmax ⊗ Ỹ`.

The ideal `S.liftIdeal r 0 i` of `A_inf` is generated by the natural number `r` and by the elements
that multiply the letter-`i` part of `A_inf ⊗ C` into the image of the letter-`i` part of
`S.extensionLattice.kisinAinf`, the Kisin module of `Ỹ` over `A_inf`: this consists of the elements
of `A_inf[1/τ] ⊗ Ỹ`, `τ = [ε^{1/p}] - 1`, whose images by all positive powers of Frobenius are sent
into `B_dR⁺` by the equivariant forms.

If `p ^ t * z ^ (k + 1)` lies in this ideal, then so does `Q(ξ ^ (k + 1)) * p ^ t * z ^ k`. -/
lemma aeval_tameMultiplier_pow_mul_mem_liftIdeal {p : ℕ} [ThePrime p] [Γ : GroupOverGp p]
    {d : TameChart Γ} {O : d.Coeffs} {Q : ℤ_[p][X]} {S : d.PairingSide O}
    (hQ_kills : aeval (linearFrob S.extensionLattice.ρ d.tameGen 0) Q = 0) (hQ_one : Q.eval 1 = 0)
    {r t k : ℕ} {i : d.Letter} (h_mem : p ^ t * d.z.val ^ (k + 1) ∈ S.liftIdeal r 0 i) :
    algebraMap (WittFq d.f) Ainf (aeval (d.tameMultiplier ^ (k + 1)) Q) * (p ^ t * d.z.val ^ k) ∈
      S.liftIdeal r 0 i := by
  -- Lift `(p ^ t * z ^ (k + 1) - r * u) * c` to the extension, apply `Q(s)` and divide by `z`.
  obtain ⟨u, hu⟩ : ∃ u : d.S, ∀ y ∈ S.trivialLattice.stdOrdersPart 0 i,
      ∃ x ∈ S.extensionLattice.stdOrdersPart 0 i,
        S.projTrivial.wittMap x = (p ^ t * d.z ^ (k + 1) - r • u).val • y :=
    S.exists_lift_of_mem_liftIdeal h_mem
  -- Write `u = w + z * v` with `w ∈ Λ`; then `s ^ j` sends `u` to `w + ξ ^ j * z * s ^ j v`.
  obtain ⟨w, v, rfl⟩ := d.exists_eq_const_add_z_mul u
  let ξ : Ainf := algebraMap (WittFq d.f) Ainf d.tameMultiplier
  let w' : Ainf := algebraMap (WittFq d.f) Ainf w
  -- `a j` is the image of the multiplier under `s ^ j`, and `Q(s)` sends the multiplier to `z * b`.
  let v' (j : ℕ) : Ainf := toGp (d.tameGen ^ j) • v.val * ξ ^ j
  let a (j : ℕ) : Ainf := p ^ t * (ξ ^ j * d.z) ^ (k + 1) - r • (w' + d.z * v' j)
  let b : Ainf :=
    algebraMap (WittFq d.f) Ainf (aeval (d.tameMultiplier ^ (k + 1)) Q) * (p ^ t * d.z.val ^ k) -
      r • ∑ j ∈ range (Q.natDegree + 1), Q.coeff j • v' j
  -- The terms in `w` cancel because `Q(1) = 0`.
  have h_sum : ∑ j ∈ range (Q.natDegree + 1), Q.coeff j • a j = d.z * b := by
    have h_coeff : ∑ j ∈ range (Q.natDegree + 1), Q.coeff j = 0 := by
      simpa [eval_eq_sum_range] using hQ_one
    calc ∑ j ∈ range (Q.natDegree + 1), Q.coeff j • a j
        = ∑ j ∈ range (Q.natDegree + 1), (d.z * (Q.coeff j • (ξ ^ (k + 1)) ^ j * (p ^ t * d.z ^ k) -
            r • Q.coeff j • v' j) - Q.coeff j • r • w') := by
          refine sum_congr rfl fun j _ ↦ ?_
          simp only [a, Algebra.smul_def]
          ring
      _ = d.z * b := by
          simp [b, ξ, ← mul_sum, ← sum_smul, h_coeff, aeval_eq_sum_range, sum_mul, smul_sum,
            algebraMap.smul, -nsmul_eq_mul]
  refine mem_liftIdeal_iff.2 ⟨∑ j ∈ range (Q.natDegree + 1), Q.coeff j • v' j, fun c ↦ ?_⟩
  obtain ⟨x, ⟨hx_loc, hx_exp⟩, hx_proj⟩ := hu _ (constantAt_mem_stdOrdersPart c)
  have hx : x ∈ S.extensionLattice.kisinModule :=
    ⟨frobKisinAinf_zero.le (mem_withOrders_stdOrders_iff.1 hx_exp).1, hx_loc.2⟩
  -- `z • y` is the image of `x` under `Q(s)`.
  obtain ⟨y, hy, hzy⟩ := exists_z_smul_eq_sum_tameGen hQ_kills hx
  -- `s ^ j` fixes the constant `c` and `w`, and multiplies `z` by `ξ ^ j`.
  have h_act (j : ℕ) :
      S.trivialLattice.letterProj i (S.projTrivial.wittMap (FrobGroup.inr (d.tameGen ^ j) • x)) =
        a j • S.constantAt i c := by
    have h_fix : FrobGroup.inr (d.tameGen ^ j) • S.constantAt i c = S.constantAt i c := by
      simp [constantAt, smul_letterProj (m := inr _) (d.fixesLambda_tameGen_pow j _), -map_pow]
    have hz : toGp (d.tameGen ^ j) • d.z.val = ξ ^ j * d.z := by
      simpa [ξ, -map_pow, ← map_pow (algebraMap (WittFq d.f) Ainf)] using
        d.tameGen_pow_smul_z j
    have h_scalar : toGp (d.tameGen ^ j) •
        (p ^ t * d.z ^ (k + 1) - r • (algebraMap (WittFq d.f) d.S w + d.z * v)).val = a j := by
      simp [a, v', w', -map_pow, hz, fixesLambda_tameGen_pow, smul_sub, mul_assoc, mul_comm,
        mul_left_comm]
    have h_letter : S.trivialLattice.letterProj i (S.constantAt i c) = S.constantAt i c :=
      mem_letterPart_iff_letterProj.1 letterProj_mem_letterPart
    simp [hx_proj, frobGroup_smul_smul, h_fix, ← h_scalar, h_letter, -map_pow]
  refine ⟨S.extensionLattice.letterProj i y, letterProj_mem_withOrders (frobKisinAinf_zero.ge hy),
    ?_⟩
  -- Cancel `z`, which is a unit of `W(C^♭)`.
  suffices h : d.z.val • S.projTrivial.wittMap (S.extensionLattice.letterProj i y) =
      d.z.val • b • S.constantAt i c from
    (isUnit_algebraMap_wittCFlat_of_not_p_dvd d.not_p_dvd_z).smul_left_cancel.1
      (by simpa [b] using h)
  calc d.z.val • S.projTrivial.wittMap (S.extensionLattice.letterProj i y)
      = S.trivialLattice.letterProj i (S.projTrivial.wittMap (d.z.val • y)) := by simp
    _ = (∑ j ∈ range (Q.natDegree + 1), Q.coeff j • a j) • S.constantAt i c := by
      simp only [hzy, map_sum, LinearMap.map_smul_of_tower, h_act, sum_smul, smul_assoc]
    _ = d.z.val • b • S.constantAt i c := by simp [h_sum, mul_smul]

/-- Let `Γ` be a group over `G_p = Gal(ℚ̄_p/ℚ_p)`. Let `d` be a tame chart for it: a coordinate
`z ∈ A_inf` of exponent `e` prime to `p`, with an element `s` of inertia that multiplies `z` by a
constant `ξ`, a primitive `e`-th root of unity modulo `p`. Let `O` be a finite free `ℤ_p`-algebra
with its element `O.ζ`, `ζ ^ (p ^ f - 1) = 1`. Let `S` be a pairing side over `O`: lattices `Y`, `C`
with a map from `C` to the crystalline cocycles of `Y`, hence an extension `Ỹ` of the trivial
lattice `C` by `Y`. For a letter `i ∈ 𝔽_{p^f}ˣ`, the finite set `S.jumpSet i` holds the jumps of the
Hodge filtration of `Y` at the embeddings of `O` that send `O.ζ` to the Teichmüller lift of `i`.

Suppose that all these jumps are `≤ n`, that `Y` is potentially crystalline and that a monic `q`
over `ℤ_p` kills the operator induced by `s` on `Bmax ⊗ Y`; the last two conditions are
`IsKilledBy`, whose `0` is the power of Frobenius composed with `s`. If `e ≤ p ^ m`,
`m (deg q + 1) ≤ κ` and `n + κ + 2 < p`, then `S.KillsCokernel i κ 0`: multiplication by
`p ^ κ * E ^ 0 = p ^ κ`, `E` the generator of `ker θ`, kills the cokernel at `i`. -/
lemma killsCokernel_of_isKilledBy {p : ℕ} [ThePrime p] [Γ : GroupOverGp p]
    {d : TameChart Γ} {O : d.Coeffs} {n m : ℕ} {q : ℤ_[p][X]} {S : d.PairingSide O}
    (hY_killed : IsKilledBy S.ρ d.tameGen 0 (q.map (algebraMap ℤ_[p] O)))
    (h_jumps : ∀ i : d.Letter, ∀ u ∈ S.jumpSet i, u ≤ n) (hq_monic : q.Monic)
    (he_le : d.e ≤ p ^ m) {κ : ℕ} {i : d.Letter} (h_small : n + κ + 2 < p)
    (h_cost : m * (q.natDegree + 1) ≤ κ) :
    S.KillsCokernel i κ 0 := by
  classical
  -- Start from `z ^ ν`, `ν < e`, in the ideal of modulus `p ^ (κ + 1)` and lower the exponent
  -- one step at a time. With `Q = q * (X - 1)`, the step from `k` is free if
  -- `Q(tameMultiplier ^ k)` is a unit and costs a factor `p ^ m` if not; at most `deg Q` steps are
  -- costly.
  obtain ⟨ν, hzν, hν_le⟩ : ∃ ν : ℕ, (∀ i : Letter, d.z.val ^ ν ∈ S.liftIdeal (p ^ (κ + 1)) 0 i) ∧
      (p - 1) * ν ≤ d.e * (n + κ) :=
    exists_z_pow_mem_liftIdeal h_jumps κ
  have hν : ν < d.e := by nlinarith [NeZero.pos d.e, (by omega : n + κ < p - 1)]
  let Q : ℤ_[p][X] := q * (X - Polynomial.C 1)
  have hQ_kills : aeval (linearFrob S.extensionLattice.ρ d.tameGen 0) Q = 0 := by
    simpa only [Q, C_1] using aeval_linearFrob_extensionLattice_eq_zero hY_killed
  let bad (k : ℕ) : Prop := constantCoeff (aeval (d.tameMultiplier ^ k) Q) = 0
  have h_count : m * (ν + 1).count bad ≤ κ := by
    have h_deg : (ν + 1).count bad ≤ Q.natDegree :=
      count_constantCoeff_aeval_tameMultiplier_pow_le (hq_monic.mul (monic_X_sub_C 1)) hν
    grw [h_deg, natDegree_mul_le, natDegree_X_sub_C, h_cost]
  suffices descent : ∀ k < d.e, ∀ t : ℕ, m * (k + 1).count bad + t ≤ κ →
      p ^ t * d.z.val ^ k ∈ S.liftIdeal (p ^ (κ + 1)) 0 i → S.KillsCokernel i κ 0 from
    descent ν hν 0 h_count (by simpa using hzν i)
  intro k hk t ht h_ideal
  induction k generalizing t with
  | zero =>
    -- As `t ≤ κ`, `p ^ κ` lies in the ideal, and Nakayama's lemma removes the modulus.
    refine killsCokernel_of_p_pow_mem_liftIdeal (Ideal.mem_of_dvd _ ?_ h_ideal)
    simpa using pow_dvd_pow (p : Ainf) (le_of_add_le_right ht)
  | succ k ih =>
    rw [Nat.count_succ] at ht
    split_ifs at ht with h_bad
    · -- Costly step: going down from `z ^ (k + 1)` to `z ^ k` costs `v_p(k + 1) + 1` factors `p`,
      -- at most `m` since `k + 1 < p ^ m`.
      have h_val : padicValNat p (k + 1) < m :=
        (padicValNat_le_nat_log (k + 1)).trans_lt
          (Nat.log_lt_of_lt_pow (by simp) (hk.trans_le he_le))
      have h_down : p ^ (t + padicValNat p (k + 1) + 1) * d.z.val ^ k ∈
          S.liftIdeal (p ^ (κ + 1)) 0 i :=
        p_pow_mul_z_pow_pred_mem_liftIdeal k.succ_pos h_ideal
      have h_lower : p ^ (t + m) * d.z.val ^ k ∈ S.liftIdeal (p ^ (κ + 1)) 0 i :=
        Ideal.mem_of_dvd _ (mul_dvd_mul_right (pow_dvd_pow _ (by omega)) _) h_down
      exact ih hk.le (t + m) (by lia) h_lower
    · -- Free step: `Q(tameMultiplier ^ (k + 1))` is a unit.
      have h_unit : IsUnit (algebraMap (WittFq d.f) Ainf (aeval (d.tameMultiplier ^ (k + 1)) Q)) :=
        (isUnit_of_coeff_zero_ne_zero _ h_bad).map _
      have h_mul : algebraMap (WittFq d.f) Ainf (aeval (d.tameMultiplier ^ (k + 1)) Q) *
          (p ^ t * d.z.val ^ k) ∈ S.liftIdeal (p ^ (κ + 1)) 0 i :=
        aeval_tameMultiplier_pow_mul_mem_liftIdeal hQ_kills (eval_mul_X_sub_C 1) h_ideal
      have h_lower : p ^ t * d.z.val ^ k ∈ S.liftIdeal (p ^ (κ + 1)) 0 i :=
        (Ideal.unit_mul_mem_iff_mem _ h_unit).1 h_mul
      exact ih hk.le t ht h_lower

end TameChart

end TameKiller

/-!
## Existence of tame Kummer charts of given ramification index
-/

section TameChartExists

open Period WittVector Selmer NeZero Function PadicComplex QuotientGroup

/-- Let `f` be a positive integer prime to `p`, let `e` divide `p ^ f - 1`, and let `ϖ ^ e = p` in
`ℚ̄_p`. The elements of `Gp p = Gal(ℚ̄_p/ℚ_p)` that fix `ϖ` and the image of the Witt vectors
`W(𝔽_{p^f})` in `A_inf` (`FixesLambda f`) form an open normal subgroup of index prime to `p`. -/
lemma exists_normal_fixer_index_coprime {p e : ℕ} [hp : ThePrime p] {f : ℕ+} (hf : ¬p ∣ f)
    (he : e ∣ p ^ f.val - 1) {ϖ : PadicAlgCl p} (hϖ : ϖ ^ e = p) :
    ∃ U : OpenSubgroup (Gp p),
      (∀ g : Gp p, g ∈ U ↔ FixesLambda f g ∧ g ϖ = ϖ) ∧ U.Normal ∧ U.index.Coprime p := by
  -- `U` is the stabiliser of `ϖ` in the fixer `V` of the `N`-th roots of unity, `N = p ^ f - 1`.
  -- The exponent of `G_p / U` divides `f * N`, which is prime to `p`.
  have hN : ¬p ∣ p ^ f.val - 1 := not_dvd_pow_sub_one
  have ϖ_ne : ϖ ≠ 0 :=
    ne_zero_pow (ne_zero_of_dvd_ne_zero (NeZero.ne _) he) (hϖ.trans_ne (NeZero.ne _))
  set N : ℕ := p ^ f.val - 1
  have quot_pow (g : Gp p) : (g ϖ / ϖ) ^ N = 1 := by
    obtain ⟨m, hm⟩ := he
    simp [hm, hϖ, pow_mul, div_pow, ← map_pow, hp.out.ne_zero]
  let V : Subgroup (Gp p) := (cyclotomicCharMod (Γ := Gp p) (PadicAlgCl p) N).ker
  have mem_V {g : Gp p} : g ∈ V ↔ ∀ ζ : PadicAlgCl p, ζ ^ N = 1 → g ζ = ζ := by
    simpa [V, Units.val_eq_one] using
      cyclotomicCharMod_eq_iff (Ω := PadicAlgCl p) (N := N) (g := g) (a := 1)
  let U : OpenSubgroup (Gp p) := ⟨V, isOpen_ker_cyclotomicCharMod.out⟩ ⊓
    ⟨MulAction.stabilizer (Gp p) ϖ, isLocalGalois_padic.isOpen_stabilizer ϖ⟩
  have mem_U {g : Gp p} : g ∈ U ↔ g ∈ V ∧ g ϖ = ϖ := .rfl
  -- An element `n` of `U` fixes `ϖ` and the root of unity `g⁻¹ ϖ / ϖ`, so it fixes `g⁻¹ ϖ`.
  have U_normal : U.Normal := by
    refine ⟨fun n hn g ↦ ?_⟩
    obtain ⟨hn_V, hn_ϖ⟩ := mem_U.mp hn
    have h_fix : n (g.symm ϖ / ϖ) = g.symm ϖ / ϖ := mem_V.mp hn_V _ (quot_pow g.symm)
    refine mem_U.mpr ⟨(MonoidHom.normal_ker _).conj_mem n hn_V g, ?_⟩
    simpa [← g.eq_symm_apply, hn_ϖ, ϖ_ne] using h_fix
  -- An element of `V` multiplies `ϖ` by the root of unity `g ϖ / ϖ`, which it fixes.
  have pow_mem_U {g : Gp p} (hg : g ∈ V) : g ^ N ∈ U := by
    have pow_apply_varpi (n : ℕ) : (g ^ n) ϖ = (g ϖ / ϖ) ^ n * ϖ := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, mem_V.mp hg _ (quot_pow g),
          pow_succ, mul_assoc, div_mul_cancel₀ _ ϖ_ne]
    exact mem_U.mpr ⟨pow_mem hg N, by rw [pow_apply_varpi, quot_pow, one_mul]⟩
  -- Every `g` raises a root of unity `ζ` to some power `p ^ n`, and `p ^ f ≡ 1`, so `g ^ f ∈ V`.
  have pow_mem_V (g : Gp p) : g ^ f.val ∈ V := by
    refine mem_V.mpr fun ζ hζ ↦ ?_
    obtain ⟨n, hn⟩ : ∃ n : ℕ, g ζ = ζ ^ p ^ n := exists_apply_eq_pow hN hζ g
    have pow_apply (j : ℕ) : (g ^ j) ζ = ζ ^ (p ^ j) ^ n := by
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, AlgEquiv.mul_apply, hn, map_pow, ih, ← pow_mul, pow_succ, mul_pow]
    have h_mod : (p ^ f.val) ^ n ≡ 1 ^ n [MOD N] := (Nat.modEq_sub one_le).pow n
    rw [pow_apply, pow_eq_pow_of_modEq h_mod hζ, one_pow, pow_one]
  -- `f * N` kills the finite group `G_p / U`, whose order then divides a power of `f * N`.
  have h_exp (x : Gp p ⧸ U.toSubgroup) : x ^ (f.val * N) = 1 := by
    obtain ⟨g, rfl⟩ := mk_surjective x
    rw [← mk_pow, eq_one_iff, pow_mul]
    exact pow_mem_U (pow_mem_V g)
  have h_pgroup : IsPGroup (f * N) (Gp p ⧸ U.toSubgroup) := fun x ↦ ⟨1, by simpa using h_exp x⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, U.index ∣ (f * N) ^ m := by
    simpa [Subgroup.index_eq_card] using h_pgroup.exists_card_dvd_pow
  have h_coprime : p.Coprime (f * N) := hp.out.coprime_iff_not_dvd.2 (hp.out.not_dvd_mul hf hN)
  refine ⟨U, fun g ↦ ?_, U_normal, .of_dvd_left hm (h_coprime.symm.pow_left m)⟩
  rw [mem_U, mem_V, fixes_roots_iff_fixesLambda]

/-- A chart is given by constants `W(𝔽_{p^f})`, an exponent `e` and an element `ϖ^♭` of the tilt of
`O_{ℂ_p}`, with coordinate `z = [ϖ^♭]`. If `ϖ ^ e = p`, some chart with the given `f` and `e` has
a `ϖ^♭` that untilts to `ϖ`. -/
lemma exists_chart_untilt_varpiFlat_eq {p e : ℕ} [ThePrime p] (f : ℕ+) {ϖ : OC} (hϖ : ϖ ^ e = p) :
    ∃ c : Chart, c.f = f ∧ c.e = e ∧ c.varpiFlat.untilt = ϖ := by
  obtain ⟨_, -, charts⟩ := exists_chart_of_pow_mul_eq_neg f (x := ϖ) (e := e) (-1) (by simp [hϖ])
  obtain ⟨c, hc_f, -, hc_untilt, hc_e, -⟩ := charts (-1) (by simp)
  exact ⟨c, hc_f, hc_e, hc_untilt⟩

/-- Inertia is transitive on towers of roots of `p`: if `ϖ^♭` of a chart `c` (with coordinate
`z = [ϖ^♭]`) and `x` both untilt to `e`-th roots of `p`, an element of inertia maps `z` to `[x]`. -/
lemma exists_inertia_smul_z_eq_teichmuller {p : ℕ} [ThePrime p] (c : Chart)
    (hc_untilt_pow : c.varpiFlat.untilt ^ c.e = p) {x : OFlat}
    (hx_untilt_pow : x.untilt ^ c.e = p) :
    ∃ s ∈ inertiaGroup (Gp p) (intQpBar p), s • c.z.val = teichmuller p x := by
  have h_trans {a b : PadicAlgCl p} {n : ℕ} (hn : 0 < n) (ha : a ^ n = p) (hb : b ^ n = a ^ n) :
      ∃ g ∈ inertiaGroup (Gp p) (intQpBar p), g • a = b :=
    isLocalGalois_padic.exists_inertia_smul_eq_of_pow_eq isUniformiser_ell hn (by simpa) hb
  rw [c.z_eq_teichmuller]
  exact exists_smul_teichmuller_eq _ h_trans c.varpiFlat x c.e (by simp [hc_untilt_pow])
    (hx_untilt_pow.trans hc_untilt_pow.symm)

/-- An element of inertia fixes the constants `W(𝔽_{p^f})`. -/
lemma fixesLambda_of_mem_inertiaGroup {p : ℕ} [ThePrime p] (f : ℕ+) {g : Gp p}
    (hg : g ∈ inertiaGroup (Gp p) (intQpBar p)) : FixesLambda f g :=
  (fixes_roots_iff_fixesLambda g).1 (apply_eq_self_of_mem_inertiaGroup not_dvd_pow_sub_one hg)

/-- Let `ϖ^♭` of the chart `c` (with coordinate `z = [ϖ^♭]` and exponent `e`) untilt to an `e`-th
root of `p`, and let `a ∈ 𝔽_{p^f}` be an `e`-th root of unity. Then an element of inertia multiplies
`z` by the constant `[a]`. -/
lemma exists_inertia_smul_z_eq_teichmuller_mul {p : ℕ} [ThePrime p] (c : Chart)
    (hc_untilt_pow : c.varpiFlat.untilt ^ c.e = p) {a : flatFq c.f} (ha : a ^ c.e = 1) :
    ∃ s ∈ inertiaGroup (Gp p) (intQpBar p),
      s • c.z.val = algebraMap (WittFq c.f) Ainf (teichmuller p a) * c.z.val := by
  have h_root : (a * c.varpiFlat : OFlat).untilt ^ c.e = p := by
    simp [← hc_untilt_pow, ← map_pow, mul_pow, ← Subring.coe_pow, ha]
  have h_teich :
      algebraMap (WittFq c.f) Ainf (teichmuller p a) = teichmuller p (a : OFlat) := by
    change _ = teichmuller p (algebraMap (flatFq c.f) OFlat a)
    simp [RingHom.algebraMap_toAlgebra]
  simpa [h_teich, map_mul, c.z_eq_teichmuller] using
    exists_inertia_smul_z_eq_teichmuller c hc_untilt_pow h_root

/-- If `g` fixes the constants `W(𝔽_{p^f})` of the chart `c` and multiplies its coordinate `z` by a
constant `ξ`, then `g ^ n` multiplies `z` by `ξ ^ n`. -/
lemma pow_smul_z_eq_pow_mul {p : ℕ} [ThePrime p] {c : Chart} {g : Gp p} {ξ : WittFq c.f}
    (hg : FixesLambda c.f g) (hz : g • c.z.val = algebraMap (WittFq c.f) Ainf ξ * c.z.val)
    (n : ℕ) : g ^ n • c.z.val = algebraMap (WittFq c.f) Ainf (ξ ^ n) * c.z.val := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_smul, ih, smul_mul', hg, hz, pow_succ, map_mul, mul_assoc]

/-- An `e`-th root `ϖ` of `p` in `ℚ̄_p`, `e ≠ 0`, is an element of the ring of integers of `ℂ_p`. -/
lemma exists_coe_eq_of_pow_eq_p {p e : ℕ} [ThePrime p] (he : e ≠ 0) {ϖ : PadicAlgCl p}
    (hϖ : ϖ ^ e = p) : ∃ ϖ' : OC, ϖ'.val = ϖ ∧ ϖ' ^ e = p := by
  have h_norm : ‖ϖ‖ ≤ 1 := by
    simpa [← pow_le_one_iff_of_nonneg (norm_nonneg ϖ) he, ← norm_pow, hϖ] using norm_p_lt_one.le
  exact ⟨⟨ϖ, by simpa using h_norm⟩, rfl, Subtype.ext (by simp [coe_eq, ← map_pow, hϖ])⟩

/-- Let the structure map `Γ → G_p = Gal(ℚ̄_p/ℚ_p)` be surjective and `f` a positive integer prime
to `p`. Let `e` divide `p ^ f - 1`, so that `𝔽_{p^f}` contains a primitive `e`-th root of unity.
Then there is a tame chart for `Γ` of exponent (ramification index) `e`. -/
lemma exists_tameChart {p e : ℕ} [hp : ThePrime p] [Γ : GroupOverGp p]
    (hsurj : Surjective Γ.overGp.toGp) (f : ℕ+) (hf : ¬p ∣ f) (he : e ∣ p ^ f.val - 1) :
    ∃ d : TameChart Γ, d.e = e := by
  -- Idea: take the chart at a root `ϖ` of `X ^ e - p` and let `U` be the fixer of `ϖ` and of the
  -- constants. Inertia permutes the towers of roots of `p`; this gives the Kummer elements and the
  -- tame generator `s`.
  have : NeZero e := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne (p ^ f.val - 1)) he⟩
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : PadicAlgCl p, ϖ ^ e = p := IsSepClosed.exists_pow_nat_eq _ e
  obtain ⟨a, ha⟩ : ∃ a : flatFq f, IsPrimitiveRoot a e :=
    (HasEnoughRootsOfUnity.of_dvd (flatFq f) he).prim
  obtain ⟨U, hU, U_normal, index_coprime⟩ : ∃ U : OpenSubgroup (Gp p),
      (∀ g : Gp p, g ∈ U ↔ FixesLambda f g ∧ g ϖ = ϖ) ∧ U.Normal ∧ U.index.Coprime p :=
    exists_normal_fixer_index_coprime hf he hϖ
  obtain ⟨ϖ', h_coe, hϖ'⟩ : ∃ ϖ' : OC, ϖ'.val = ϖ ∧ ϖ' ^ e = p :=
    exists_coe_eq_of_pow_eq_p (NeZero.ne e) hϖ
  obtain ⟨c, rfl, rfl, h_untilt⟩ : ∃ c : Chart, c.f = f ∧ c.e = e ∧ c.varpiFlat.untilt = ϖ' :=
    exists_chart_untilt_varpiFlat_eq f hϖ'
  have hc_untilt_pow : c.varpiFlat.untilt ^ c.e = p := by rw [h_untilt, hϖ']
  have mem_U {g : Gp p} : g ∈ U ↔ c.FixesThetaZ g := by
    rw [hU g]
    exact and_congr_right' (by simp [c.z_eq_teichmuller, h_untilt, h_coe, Subtype.ext_iff])
  -- An inertial `t` with `t z = [ε] ^ l z` fixes the constants, and `θ z` since `θ [ε] = 1`.
  have exists_kummer (l : ℕ) :
      ∃ t : Γ, toGp t ∈ U ∧ toGp t • c.z.val = teichmuller p epsTilt ^ l * c.z := by
    obtain ⟨t, ht_inertia, ht⟩ := hsurj.exists.1
      (exists_inertia_smul_z_eq_teichmuller c hc_untilt_pow
        (x := epsTilt ^ l * c.varpiFlat) (by simp [hc_untilt_pow]))
    have hz : toGp t • c.z.val = teichmuller p epsTilt ^ l * c.z := by
      rw [ht, map_mul, map_pow, c.z_eq_teichmuller]
    exact ⟨t, mem_U.2 ⟨fixesLambda_of_mem_inertiaGroup c.f ht_inertia,
      by simp [← theta_smul, hz]⟩, hz⟩
  let kummer : KummerChart Γ :=
    { chart := c
      subgroup := .comap toGp U
      index_coprime := by rwa [U.index_comap_of_surjective hsurj]
      fixes g := mem_U.1 g.property
      isChartOf := hsurj.forall.2 fun g hg ↦ ⟨⟨g, mem_U.2 hg⟩, rfl⟩
      nearOne_le := by
        rw [Filter.map_top, Filter.le_principal_iff, Subgroup.coe_subtype, Subtype.range_coe]
        exact Filter.preimage_mem_comap U.mem_nhds_one
      exists_smul_z l := by simpa using exists_kummer l }
  -- The tame generator `s` multiplies `z` by the root of unity `[a]` of order `e`.
  obtain ⟨s, hs_inertia, hz⟩ : ∃ s : Γ, toGp s ∈ inertiaGroup (Gp p) (intQpBar p) ∧
      toGp s • c.z.val = algebraMap (WittFq c.f) Ainf (teichmuller p a) * c.z.val :=
    hsurj.exists.1 (exists_inertia_smul_z_eq_teichmuller_mul c hc_untilt_pow ha.pow_eq_one)
  have h_pow_z (n : ℕ) :
      toGp (s ^ n) • c.z.val = algebraMap (WittFq c.f) Ainf (teichmuller p a ^ n) * c.z.val := by
    simpa using pow_smul_z_eq_pow_mul (fixesLambda_of_mem_inertiaGroup c.f hs_inertia) hz n
  exact ⟨{ kummer with
    tameMultiplier := teichmuller p a
    tameGen := s
    isPrimitiveRoot_tameMultiplier := ha
    tameGen_pow_smul_z := h_pow_z
    isWeilPair_tameGen := isWeilPair_zero_iff.2 hs_inertia
    fixesLambda_tameGen_pow n := by
      rw [map_pow]
      exact fixesLambda_of_mem_inertiaGroup c.f (pow_mem hs_inertia n)
    ϖ := ϖ
    apply_varpi g := ((hU (toGp g.val)).1 g.property).2
    varpi_pow_eq := hϖ
    tame h := not_dvd_pow_sub_one (h.trans he)
    normal := U_normal.comap _ }, rfl⟩

end TameChartExists

end New.Lift
