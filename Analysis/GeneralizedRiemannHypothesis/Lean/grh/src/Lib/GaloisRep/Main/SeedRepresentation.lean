import Lib.ClassField.Avatar.HeckeBaseChange
import Lib.GaloisRep.KillingPolynomials
import Lib.GaloisRep.Main.CuspidalTypes
import Lib.Shimura.Eigenspace
import Lib.Shimura.IntegralModel.PELDataExistence
import Lib.Shimura.IntegralModel.TowerExistence
import Lib.Shimura.ThetaModuli.UniversalFamily
import Lib.Shimura.Transfer.WeightOccurs

/-!
# Seed representations: odd rank, a cuspidal type and free jumps

The Galois representation of a form `f` of odd rank on the definite unitary group, under two extra
local hypotheses: a cuspidal type at a split place and free jumps.

* `New.GaloisRep.exists_rep_of_cuspidal_type`: under these hypotheses, there is a continuous
  representation with the characteristic polynomials of Frobenius given by the Hecke polynomials of
  `f`, spherical at a further split place outside the ramification.

The proof transfers `f` to a form on the definite frames on which the centre acts by a character
(`New.GaloisRep.exists_central_eigenform`), realizes its Hecke eigenvalues in the cohomology of a
PEL model for each complex embedding of `E`, and joins the representations so obtained into one of
rank `a` (`New.GaloisRep.exists_galRep_charpoly_eq_of_forall_embedding`).

Notions from other files:
* `New.jumps κ N σ`: the multiset {j − 1 − λ_j} if σ is in the CM type, else {λ_j + N − j},
  1 ≤ j ≤ N, with λ the highest weight of κ at the place v of σ: λ_j = `κ.2 v` + Σ_{j ≤ h < N}
  `κ.1 v h`.
* `New.Variety.definiteForms 𝔑 ξ`: the functions `φ` on `GL n (𝔸f E)` with `φ (y x) = ξ y (φ x)` for
  rational `y`, zero off the definite frames, and right invariant under the level `levelGU n 𝔑`.
* `New.Variety.IsSafe 𝔑 w`: the place of `QuadField d` below `w` satisfies `IsSplitPrimeToDisc`, and
  `𝔑` lies neither in `w` nor in any place above the conjugate of that place.
* `New.GaloisRep.IsSphericalAbove r R J w P`: at every place above `w`, `r` is unramified or
  crystalline, its jumps are related to the multisets `J` by `R` (`OccursIn`: each member of `J` is
  among its jumps; `Eq`: they are exactly its jumps), and `P` kills its geometric Frobenius
  elements.
* `New.HasNoSmallRelations e`: two families of natural numbers with the same sum, at most
  `(n + 1) ^ 2`, and the same sum weighted by the `e i`, are equal.

## Relation to the literature

Known; see `Lib.GaloisRep.Main.OddRank` for sources.
-/

open NumberField Matrix New Variety Period IsLocalization RingHom Subgroup Gf

/-- `conjAtSplit w g` is the inverse transpose of the unitary element `ofSplitPlace w g`. -/
private lemma New.GaloisRep.invTransposeGL_ofSplitPlace_eq_conjAtSplit {E : Type} [Field E]
    [CMBase E] {n : Type} [Fintype n] [DecidableEq n] {w : SplitFinPlace E}
    (g : GL n (LocField (w : FinPlace E))) :
    invTransposeGL (ofSplitPlace w.prop g).val = conjAtSplit w g :=
  rfl

/-- Moving a coset representative at a split place. Let the cosets modulo the level `levelGU n 𝔑`
of `toFinGL y₀ * invTransposeGL u₀` and of `x` agree, and let `𝔑 ∉ star w` for the split place `w`.
Then for some `c` at `w` and all `y : GL n E` and `g` at `w`, the cosets of
`toFinGL (y * y₀) * invTransposeGL (u₀ * ofSplitPlace w (c * g))` and of
`toFinGL y * (x * conjAtSplit w g)` agree. -/
private lemma New.GaloisRep.exists_forall_mk_eq_mk_mul_conjAtSplit {E : Type} [Field E] [CMBase E]
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] {𝔑 : 𝓞 E} {y₀ : GL n E} {u₀ : Gf E n}
    {x : GL n (𝔸f E)}
    (h_coset : (⟦toFinGL y₀ * invTransposeGL u₀.val⟧ : GL n (𝔸f E) ⧸ levelGU n 𝔑) = ⟦x⟧)
    {w : SplitFinPlace E} (hw : 𝔑 ∉ (star w.val).asIdeal) :
    ∃ c : GL n (LocField (w : FinPlace E)),
      ∀ (y : GL n E) (g : GL n (LocField (w : FinPlace E))),
        (⟦toFinGL (y * y₀) * invTransposeGL (u₀ * ofSplitPlace w.prop (c * g)).val⟧ :
            GL n (𝔸f E) ⧸ levelGU n 𝔑) =
          ⟦toFinGL y * (x * conjAtSplit w g)⟧ := by
  set κ : GL n (𝔸f E) := (toFinGL y₀ * invTransposeGL u₀.val)⁻¹ * x
  have h_mem : κ ∈ levelGU n 𝔑 := QuotientGroup.eq.mp h_coset
  -- This level element is its component `conjAtSplit w c` at `w`, `star w`, itself in the level,
  -- times an element that commutes with every `conjAtSplit w g`.
  obtain ⟨h_loc, h_comm⟩ := conjAtSplit_dualComponent hw h_mem
  set c : GL n (LocField (w : FinPlace E)) := dualComponent w κ
  refine ⟨c, fun y g ↦ QuotientGroup.eq.mpr ?_⟩
  have h_elt : (toFinGL (y * y₀) * invTransposeGL (u₀ * ofSplitPlace w.prop (c * g)).val)⁻¹ *
      (toFinGL y * (x * conjAtSplit w g)) = (conjAtSplit w c)⁻¹ * κ := by
    simpa [mul_assoc, κ, invTransposeGL_ofSplitPlace_eq_conjAtSplit] using
      (h_comm g).symm.inv_mul_cancel
  rw [h_elt]
  exact mul_mem (inv_mem h_loc) h_mem

/-- Extension of a function `f` on `Gf E n`, on which rational unitary matrices act through `ξ`
(`h_rat`) and which is invariant at level `𝔑` (`h_level`), to a function `φ` on `GL n (𝔸f E)`. `φ`
agrees with `f` on `Gf E n` embedded by `invTransposeGL`, is right invariant under `levelGU n 𝔑`,
and vanishes off the definite frames (`IsSignedFrame x 1`: frames of totally positive definite
rational forms). At each split place `w` with `𝔑 ∉ star w` and each `x`,
`φ (y * x * conjAtSplit w g)` is `ξ y` of one linear map `L` applied to the translate of `f` by
`ofSplitPlace w g`. -/
lemma New.GaloisRep.exists_frame_extension {E : Type} [Field E] [CMBase E] {n W : Type} [Fintype n]
    [DecidableEq n] [Nonempty n] [AddCommGroup W] [Module ℂ W] (ξ : Representation ℂ (GL n E) W)
    {f : Gf E n → W} {𝔑 : 𝓞 E}
    (h_rat : ∀ y ∈ U (1 : Matrix n n E), ∃ c : Gf E n,
      (∀ u : Gf E n, f (c * u) = ξ y (f u)) ∧ invTransposeGL c.val = toFinGL y)
    (h_level : ∀ u : Gf E n, invTransposeGL u.val ∈ levelGU n 𝔑 → u ∈ rightStabilizer f) :
    ∃ φ : GL n (𝔸f E) → W,
      (∀ g : Gf E n, φ (invTransposeGL g.val) = f g) ∧
      (∀ x : GL n (𝔸f E), ∀ k ∈ levelGU n 𝔑, φ (x * k) = φ x) ∧
      (∀ x : GL n (𝔸f E), ¬IsSignedFrame x 1 → φ x = 0) ∧
      ∀ w : SplitFinPlace E, 𝔑 ∉ (star w.val).asIdeal → ∀ x : GL n (𝔸f E),
        ∃ L : (Gf E n → W) →ₗ[ℂ] W, ∀ (y : GL n E) (g : GL n (LocField (w : FinPlace E))),
        φ (toFinGL y * (x * conjAtSplit w g)) =
          ξ y (L (rightRegular ℂ (Gf E n) W (ofSplitPlace w.2 g) f)) := by
  have h_frame (u : Gf E n) : IsSignedFrameFor (invTransposeGL u.val) 1 1 :=
    isSignedFrameFor_one (entryConj u)
  let Q (p : GL n E × Gf E n) : GL n (𝔸f E) ⧸ levelGU n 𝔑 := ⟦toFinGL p.1 * invTransposeGL p.2.val⟧
  let φ (x : GL n (𝔸f E)) : W := Q.extend (fun p ↦ ξ p.1 (f p.2)) 0 ⟦x⟧
  -- Well defined: if `(z * y, u)` and `(z, t)` give the same coset, then `y` is unitary, since
  -- `u` and `t` both give definite frames for the form `1`.
  have h_factors : (fun p : GL n E × Gf E n ↦ ξ p.1 (f p.2)).FactorsThrough Q := by
    rintro ⟨z, t⟩ ⟨z', u⟩ h_eq
    obtain ⟨y, rfl⟩ : ∃ a : GL n E, z * a = z' := mul_left_surjective z z'
    have h_mem : (invTransposeGL t.val)⁻¹ * (toFinGL y * invTransposeGL u.val) ∈ levelGU n 𝔑 := by
      simpa [mul_assoc] using QuotientGroup.eq.mp h_eq
    have h_scalar :
        IsScalarFrame ((invTransposeGL t.val)⁻¹ * toFinGL y * invTransposeGL u.val)⁻¹ 1 := by
      simpa [mul_assoc] using levelGU.isScalarFrame_inv_one h_mem
    have hy : y ∈ U (1 : Matrix n n E) :=
      ((h_frame u).conjTranspose_mul_mul_eq_smul (h_frame t) h_scalar).trans (by simp)
    obtain ⟨c, hc_f, hc⟩ := h_rat y hy
    have h_stab : t⁻¹ * c * u ∈ rightStabilizer f :=
      h_level _ (by simpa [← hc, mul_assoc] using h_mem)
    have h_fix : f (t * (t⁻¹ * c * u)) = f t := h_stab t
    have h_ft : f t = ξ y (f u) := by simpa [← hc_f u, mul_assoc] using h_fix.symm
    simp [h_ft]
  have hφ {p : GL n E × Gf E n} {x : GL n (𝔸f E)} (h : Q p = ⟦x⟧) : φ x = ξ p.1 (f p.2) := by
    simp [φ, ← h, h_factors.extend_apply]
  have hφ_zero {x : GL n (𝔸f E)} (h : ¬∃ p : GL n E × Gf E n, Q p = ⟦x⟧) : φ x = 0 :=
    Q.extend_apply' (fun p : GL n E × Gf E n ↦ ξ p.1 (f p.2)) 0 ⟦x⟧ h
  have h_move {p : GL n E × Gf E n} {x : GL n (𝔸f E)} (h : Q p = ⟦x⟧) {w : SplitFinPlace E}
      (hw : 𝔑 ∉ (star w.val).asIdeal) :
      ∃ c : GL n (LocField (w : FinPlace E)),
        ∀ (y : GL n E) (g : GL n (LocField (w : FinPlace E))),
          Q (y * p.1, p.2 * ofSplitPlace w.prop (c * g)) = ⟦toFinGL y * (x * conjAtSplit w g)⟧ :=
    exists_forall_mk_eq_mk_mul_conjAtSplit h hw
  refine ⟨φ, fun g ↦ ?_, fun x k hk ↦ ?_, fun x hx ↦ ?_, fun w hw x ↦ ?_⟩
  · simpa using hφ (p := (1, g)) (by simp [Q])
  · simp [φ, hk]
  · -- A coset of `toFinGL y * invTransposeGL u` consists of definite frames.
    refine hφ_zero fun ⟨⟨y, u⟩, hp⟩ ↦ hx ?_
    simpa [ratConj, mul_assoc] using
      IsSignedFrame.mul ⟨1, h_frame u⟩ y (QuotientGroup.eq.mp hp).left
  · -- The linear map at `x`: evaluate a translate at `p.2` and apply `ξ p.1`, or `0` off the
    -- cosets.
    by_cases hx : ∃ p : GL n E × Gf E n, Q p = ⟦x⟧
    · obtain ⟨p, hp⟩ := hx
      obtain ⟨c, hc⟩ := h_move hp hw
      refine ⟨ξ p.1 ∘ₗ LinearMap.proj p.2 ∘ₗ rightRegular ℂ (Gf E n) W (ofSplitPlace w.prop c),
        fun y g ↦ ?_⟩
      simpa [mul_assoc] using hφ (hc y g)
    · refine ⟨0, fun y g ↦ ?_⟩
      have h_none : ¬∃ p : GL n E × Gf E n, Q p = ⟦toFinGL y * (x * conjAtSplit w g)⟧ := by
        -- Otherwise, moving back by `y⁻¹` and `g⁻¹` puts `x` on one of the cosets.
        rintro ⟨p, hp⟩
        obtain ⟨c, hc⟩ := h_move hp hw
        exact hx ⟨_, (hc y⁻¹ g⁻¹).trans (by simp [mul_assoc])⟩
      simp [hφ_zero h_none]

/-- Let `f ≠ 0` on `Gf E n` take values in a finite-dimensional `W`, let rational unitary matrices
act on `f` through `ξ`, let `f` be invariant at the neat level `𝔑`, and let some split place `w₀`
have `𝔑 ∉ star w₀`. Then some nonzero `ψ` in `definiteForms 𝔑 ξ` exists. This means `ψ` is left
`ξ`-equivariant under `GL n E`, zero off the definite frames, and right `levelGU n 𝔑`-invariant. It
has a central character `ω` (the finite ideles of `QuadField d` act through `centralScalar` by `ω`),
and at each split `w` with `𝔑 ∉ star w`, its translates are the images of those of `f` under one
linear map `L`. -/
lemma New.GaloisRep.exists_central_eigenform {E : Type} [Field E] [CMBase E] {d : ℕ}
    [HasQuadSubfield d E] {n W : Type} [Fintype n] [DecidableEq n] [Nonempty n] [AddCommGroup W]
    [Module ℂ W] [Module.Finite ℂ W] (ξ : Representation ℂ (GL n E) W) {f : Gf E n → W} (hf : f ≠ 0)
    {𝔑 : 𝓞 E} (h_neat : IsNeat n 𝔑) (w₀ : SplitFinPlace E) (hw₀ : 𝔑 ∉ (star w₀.val).asIdeal)
    (h_rat : ∀ y ∈ U (1 : Matrix n n E), ∃ c : Gf E n,
      (∀ u : Gf E n, f (c * u) = ξ y (f u)) ∧ invTransposeGL c.val = toFinGL y)
    (h_level : ∀ u : Gf E n, invTransposeGL u.val ∈ levelGU n 𝔑 → u ∈ rightStabilizer f) :
    ∃ ψ ∈ Variety.definiteForms 𝔑 ξ,
      ψ ≠ 0 ∧
      (∃ ω : (𝔸f (QuadField d))ˣ →* ℂ, ∀ x : (𝔸f (QuadField d))ˣ,
        rightRegular ℂ (GL n (𝔸f E)) W (centralScalar x) ψ = ω x • ψ) ∧
      ∀ w : SplitFinPlace E, 𝔑 ∉ (star w.val).asIdeal → ∃ L : (Gf E n → W) →ₗ[ℂ] GL n (𝔸f E) → W,
        ∀ g : GL n (LocField (w : FinPlace E)),
        rightRegular ℂ (GL n (𝔸f E)) W (conjAtSplit w g) ψ =
          L (rightRegular ℂ (Gf E n) W (ofSplitPlace w.2 g) f) := by
  obtain ⟨φ, hφ, hφ_level, hφ_zero, hφ_loc⟩ := exists_frame_extension ξ h_rat h_level
  choose L hL using hφ_loc
  let s : (𝔸f (QuadField d))ˣ →* GL n (𝔸f E) := centralScalar
  let ρ : (𝔸f (QuadField d))ˣ →* (GL n (𝔸f E) → W) →ₗ[ℂ] GL n (𝔸f E) → W :=
    (rightRegular ℂ (GL n (𝔸f E)) W).comp s
  have h_central (x : (𝔸f (QuadField d))ˣ) (g : GL n (𝔸f E)) : g * s x = s x * g :=
    commute_scalar_GL ..
  have hL_one (w : SplitFinPlace E) (hw : 𝔑 ∉ (star (w : FinPlace E)).asIdeal) (x : GL n (𝔸f E))
      (g : GL n (LocField (w : FinPlace E))) :
      φ (x * conjAtSplit w g) = L w hw x (rightRegular ℂ (Gf E n) W (ofSplitPlace w.prop g) f) := by
    simpa using hL w hw x 1 g
  have hφ_rat (x : GL n (𝔸f E)) (y : GL n E) : φ (toFinGL y * x) = ξ y (φ x) := by
    have h_x : φ x = L w₀ hw₀ x f := by simpa using hL_one w₀ hw₀ x 1
    simpa [h_x] using hL w₀ hw₀ x y 1
  -- The central translates of `φ` span a nonzero subspace of the finite-dimensional space of forms.
  have h_le : cyclicSpan ρ φ ≤ Variety.definiteForms 𝔑 ξ := by
    -- Each central translate `ρ x φ` is equivariant, vanishes off the definite frames and is
    -- invariant under the level.
    refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun x ↦ ⟨⟨?_, ?_⟩, ?_⟩)
    · intro y z
      simp [ρ, hφ_rat, mul_assoc]
    · refine fun z hz ↦ hφ_zero _ fun h_frame ↦ hz ?_
      simpa [s, ratConj] using h_frame.mul 1 (inv_mem (centralScalar_mem_GU x).left)
    · simp +contextual [ρ, funext_iff, h_central, ← mul_assoc, hφ_level]
  have : Module.Finite ℂ (Variety.definiteForms 𝔑 ξ) := finite_definiteForms ξ h_neat
  have : Module.Finite ℂ (cyclicSpan ρ φ) := .of_fg (.of_le .of_finite h_le)
  have hφ_ne : φ ≠ 0 := fun h_zero ↦ hf (funext fun g ↦ by simp [← hφ g, h_zero])
  have h_ne : ¬cyclicSpan ρ φ ≤ ⊥ := fun h_bot ↦ hφ_ne (h_bot self_mem_cyclicSpan)
  obtain ⟨ω, ψ, hψ_mem, hψ_ne, hω⟩ := exists_eigencharacter ρ apply_mem_cyclicSpan h_ne
  refine ⟨ψ, h_le hψ_mem, hψ_ne, ⟨ω, hω⟩, fun w hw ↦ ?_⟩
  -- `ψ` is a combination of central translates of `φ`; the same combination of the `L w hw` works.
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hψ_mem
  refine ⟨c.sum fun x r ↦ r • LinearMap.pi fun y ↦ L w hw (s x * y), fun g ↦ ?_⟩
  simp [ρ, funext_iff, Finsupp.sum, ← mul_assoc, h_central, hL_one w hw]

/-- A place `w` of `E` whose residue field has prime order and which does not contain `d` lies above
a place of `QuadField d` with `IsSplitPrimeToDisc`: that place contains `betaK d - b` for an integer
`b`, and this element is coprime to its conjugate. -/
lemma New.GaloisRep.isSplitPrimeToDisc_below_of_prime_norm {E : Type} [Field E] [NumberField E]
    {d : ℕ}
    [HasQuadSubfield d E] {w : FinPlace E} (hq_prime : w.q.Prime) (hd_notMem : ↑d ∉ w.asIdeal) :
    IsSplitPrimeToDisc (w.below (QuadField d)) := by
  -- The residue field at `w` has prime order and the class of `d` is nonzero, so it generates the
  -- additive group: `betaK d ≡ c * d` modulo `w` for an integer `c`.
  obtain ⟨c, hc⟩ :
      Ideal.Quotient.mk w.asIdeal (algebraMap (𝓞 (QuadField d)) (𝓞 E) (QuadField.betaK d)) ∈
        AddSubgroup.zmultiples (Ideal.Quotient.mk w.asIdeal (d : 𝓞 E)) :=
    mem_zmultiples_of_prime_card (hp := ⟨hq_prime⟩) rfl
      (mt Ideal.Quotient.eq_zero_iff_mem.mp hd_notMem)
  have hx_mem :
      QuadField.betaK d - ((c * d : ℤ) : 𝓞 (QuadField d)) ∈ (w.below (QuadField d)).asIdeal :=
    Ideal.mem_comap.mpr (by simpa using Ideal.Quotient.eq.mp hc.symm)
  refine ⟨c * d, hx_mem, 1 - 2 * c * QuadField.sqrtNegDInt d,
    2 * c * QuadField.sqrtNegDInt d + 1, ?_⟩
  -- A Bézout relation, from `star (betaK d) = 1 - betaK d` and `(2 * betaK d - 1) ^ 2 = -d`.
  have h_sq : (2 * QuadField.betaK d - 1) ^ 2 = -(d : 𝓞 (QuadField d)) := QuadField.sqrtNegDInt_sq d
  simp only [star_sub, QuadField.star_betaK, QuadField.sqrtNegDInt, Int.cast_mul, Int.cast_natCast,
    star_mul', star_intCast, star_natCast]
  linear_combination (-2 * (c : 𝓞 (QuadField d))) * h_sq

/-- Rank and characteristic polynomials from a Hodge–Tate frame: if the image of `r` spans the
diagonal matrices, `P w`, monic of degree `a`, kills `r` along `mostFrobenii E`, and `r` is
good at the place of `ε` with the free jumps `e i` of `κ` among its jumps, then `r` has rank `a` and
characteristic polynomials `P w` along `mostFrobenii E`: near `1` the cocharacter of the frame lies
in the Zariski closure of the image of `r`, and `card_eq_and_charpoly_eq` applies. -/
private lemma New.GaloisRep.card_eq_and_eventually_charpoly_eq_of_hasNoSmallRelations {ℓ : ℕ}
    {E : Type} {a b : ℕ} [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E]
    [NeZero a] (κ : Weight E) {P : FinPlace E → Polynomial (PadicAlgCl ℓ)} (r : GalRep ℓ E (Fin b))
    (hr : Continuous r)
    (h_diag : ∀ v : Fin b → PadicAlgCl ℓ,
      diagonal v ∈ Submodule.span (PadicAlgCl ℓ) (Set.range fun g : Gal(Ω/E) ↦ (r g).val))
    (h_kill : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E,
      (P y.place).aeval (r y.frob).val = 0 ∧ (P y.place).IsMonicOfDegree a)
    {ε : Ω →+* PadicAlgCl ℓ} {e : Fin a → ℤ} (he_free : HasNoSmallRelations e)
    (he_jumps : ∀ i : Fin a, e i ∈ jumps κ a (RingHom.comp ιℓ.symm (ε.comp (algebraMap E Ω))))
    (h_good : IsGoodAt r ((intQpBar ℓ).comap ε))
    (h_jump : JumpsRelAt r ((intQpBar ℓ).comap ε) OccursIn (jumps κ a)) :
    Fintype.card (Fin b) = a ∧
      ∀ᶠ y : FrobeniusDatum E in mostFrobenii E, (r y.frob).val.charpoly = P y.place := by
  -- A Hodge–Tate frame `T` at the place `A` of `ε`; its weights `k` include the `e i`.
  let A : ValuationSubring Ω := (intQpBar ℓ).comap ε
  obtain ⟨j, h_induces, hj_open, hj_range⟩ := exists_inducesPlace E Gal(Ω/E) (ι := ε) rfl
  -- The embedding `ε` and the open embedding `j` of the decomposition group, bundled.
  let chart : PadicPlaceEmbedding E A ℓ :=
    .mk (toOverGp := ⟨_, ⟨hj_open.isOpen_range⟩⟩) _ ⟨h_induces, hj_open, hj_range⟩
  obtain ⟨-, h_crys⟩ := h_good
  obtain ⟨T, k, hT, hk, -⟩ :=
    h_crys.isPotentiallyCrystalline.exists_isHodgeTateFrame (Pi.basisFun ..)
      (IsScalarTower.toAlgHom ..)
  -- Each `e i` is a jump of `κ` at `ε`, hence a jump of `r` at `A`: a weight `k`.
  have h_weights (i : Fin a) : e i ∈ Set.range k := by
    have h_jump_ne :
        jump (decompRep r A) (IsScalarTower.toAlgHom ℤ_[ℓ] (PadicAlgCl ℓ) ℂ_[ℓ]) (e i) ≠ 0 := by
      refine h_jump (L := chart) (g := 1) (fun _ ↦ rfl) (e i) ?_
      -- The embedding that `chart` induces through `g = 1` is the one of `ε`.
      convert Multiset.count_ne_zero.mpr (he_jumps i)
      ext x
      simp [chart]
      rfl -- `chart.e` is `ε` by definition
    rw [hk (e i), Multiset.count_ne_zero] at h_jump_ne
    simpa using h_jump_ne
  -- Near `1` the entries of `T⁻¹ * r g` are twisted translates of the entries of `T⁻¹`.
  have h_entries : ∀ᶠ g : decompGroup Gal(Ω/E) A in nearOne (decompGroup Gal(Ω/E) A),
      (T⁻¹.val * (r g).val.map (algebraMap ..)).uncurry = fun i : Fin b × Fin b ↦
        (cyclotomicGp (j g) ^ (-k i.1)).val • j g • T⁻¹.val.uncurry i := by
    refine hT.mono fun g hg ↦ funext fun i ↦ ?_
    -- `erw`: `Function.uncurry` here takes a matrix, read as a function of two indices
    erw [← inv_mul_apply_of_isHodgeTateFrame hg]
    simp [Matrix.mul_apply, Function.uncurry]
  -- So the cocharacter with weights `k` lies in the Zariski closure of the image of `r`, and
  -- `card_eq_and_charpoly_eq` gives the rank of `r` and its characteristic polynomials.
  refine card_eq_and_charpoly_eq r hr h_diag h_kill T⁻¹ k he_free h_weights fun G hG ↦ ?_
  -- `G` vanishes at `T⁻¹ * r g` near `1`, so at the translates, so at the cocharacter.
  have h_near : ∀ᶠ g : decompGroup Gal(Ω/E) A in nearOne (decompGroup Gal(Ω/E) A),
      G.aeval (T⁻¹.val * (r g).val.map (algebraMap (PadicAlgCl ℓ) ℂ_[ℓ])).uncurry = 0 := by
    rw [nearOne_eq_nhds_one hj_open]
    exact continuousAt_subtype_val (x := (1 : decompGroup Gal(Ω/E) A)) hG
  have h_twisted : ∀ᶠ g : decompGroup Gal(Ω/E) A in nearOne (decompGroup Gal(Ω/E) A),
      G.aeval (fun i : Fin b × Fin b ↦
        (cyclotomicGp (j g) ^ (-k i.1)).val • j g • T⁻¹.val.uncurry i) = 0 := by
    filter_upwards [h_entries, h_near] with g h_eq h_zero using by rwa [← h_eq]
  -- `convert`: the entries of the cocharacter matrix `diagonal (LaurentPolynomial.T ∘ k)` times
  -- `T⁻¹` appear only after the matrix product is expanded inside `aeval`.
  convert aeval_cocharacter_eq_zero (fun i : Fin b × Fin b ↦ k i.1) T⁻¹.val.uncurry G
    (nhds_one_le_map_nearOne _ h_twisted)
  simp [Function.uncurry]

/-- One representation from one for each embedding. Let `P w` be monic of degree `a` along the
filter `mostFrobenii E` (each nonempty open set of the Galois group has a nonempty open part whose
Frobenii have the property at almost all places).
Let the `a` jumps of `κ` at `ε` be free integers `e i` (`HasNoSmallRelations`), with
the place of `ε` in `F`. Suppose that for each embedding `τ₀` some continuous `ρ`, eventually along
those places and `F`, satisfies `IsSphericalAbove` with `OccursIn`: it is good above `w`, the jumps
of `κ` at `τ₀` occur in `ρ`, and `P w` kills its geometric Frobenii. Then one continuous `r` of rank
`a` has characteristic polynomial `P w` along `mostFrobenii E` and, eventually along `F`, exactly
the jumps of `κ`. -/
lemma New.GaloisRep.exists_galRep_charpoly_eq_of_forall_embedding {ℓ : ℕ} {E : Type} {a : ℕ}
    [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E] [NeZero a] (κ : Weight E)
    {P : FinPlace E → Polynomial (PadicAlgCl ℓ)}
    (h_monic : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E,
      ↑ℓ ∉ y.place.asIdeal ∧ (P y.place).IsMonicOfDegree a)
    {ε : Ω →+* PadicAlgCl ℓ} {e : Fin a → ℤ} (he_free : HasNoSmallRelations e)
    (he_jumps : ∀ i : Fin a, e i ∈ jumps κ a (RingHom.comp ιℓ.symm (ε.comp (algebraMap E Ω))))
    {F : Filter (FinPlace E)} (hF : pure (placeOfEmb (ε.comp (algebraMap E Ω))) ≤ F)
    (h_one : ∀ τ₀ : E →+* ℂ, ∃ ρ : PadicRep Gal(Ω/E) ℓ,
      Continuous ρ.rep ∧
      ∀ᶠ w : FinPlace E in (mostFrobenii E).map (fun y : FrobeniusDatum E ↦ y.place) ⊔ F,
        IsSphericalAbove ρ.rep OccursIn (Set.indicator {τ₀} (jumps κ a)) w (P w)) :
    ∃ r : GalRep ℓ E (Fin a),
      Continuous r ∧
      (∀ᶠ y : FrobeniusDatum E in mostFrobenii E, (r y.frob).val.charpoly = P y.place) ∧
      ∀ᶠ w : FinPlace E in F, IsSphericalAbove r Eq (jumps κ a) w (P w) := by
  obtain ⟨b, r, hr, h_diag, h_frob, h_F⟩ := exists_rep_span_diagonal _ (jumps κ a) P h_one
  -- At the place of `ε`, which `F` contains: `r` is good there and the jumps of `κ` occur.
  obtain ⟨h_good, h_jump, -⟩ := Filter.eventually_pure.mp (hF h_F) (isPlaceOver_placeOfEmb ε)
  have h_kill : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E,
      (P y.place).aeval (r y.frob).val = 0 ∧ (P y.place).IsMonicOfDegree a := by
    filter_upwards [h_frob, h_monic] with y h_sph ⟨hyℓ, hy⟩
    obtain ⟨-, -, h_kills⟩ := h_sph y.isPlaceOver
    exact ⟨(h_kills _ y.isFrob_inv).left (y.isPlaceOver.valuation_natCast_eq_one_iff.mpr hyℓ), hy⟩
  obtain ⟨h_card, h_charpoly⟩ := card_eq_and_eventually_charpoly_eq_of_hasNoSmallRelations κ r hr
    h_diag h_kill he_free he_jumps h_good h_jump
  obtain rfl : a = b := by simpa using h_card.symm
  refine ⟨r, hr, h_charpoly, Filter.Eventually.mono h_F fun w hw A hA ↦ ?_⟩
  obtain ⟨h_good', h_occ, h_poly⟩ := hw hA
  refine ⟨h_good', fun L γ g hγ u ↦ ?_, h_poly⟩
  -- The `a` distinct jumps of `κ` occur among the jumps of `r`, of which there are only `a`.
  obtain ⟨K, hK_card, hK⟩ := h_good'.right.isPotentiallyCrystalline.exists_hasJumps γ
  let σ : E →+* PadicAlgCl ℓ := .comp ↑g⁻¹ (L.e.comp (algebraMap E Ω))
  have h_le : jumps κ a (RingHom.comp ιℓ.symm σ) ≤ K :=
    (Multiset.le_iff_subset (κ.nodup_jumps ..)).mpr fun z ↦ by
      simpa [hK _, OccursIn] using h_occ hγ z
  have h_card_le : K.card ≤ (jumps κ a (RingHom.comp ιℓ.symm σ)).card := by simp [hK_card, jumps]
  rw [hK, Multiset.eq_of_le_of_card_le h_le h_card_le]

/-- The submonoid of the integers of `E` that lie in no place `u` with `G u` is disjoint from the
place `w` exactly when `G w` holds. -/
lemma New.GaloisRep.disjoint_iInf_primeCompl_iff {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : FinPlace E → Prop) (w : FinPlace E) :
    Disjoint (⨅ (u : FinPlace E) (_ : G u), u.asIdeal.primeCompl : Submonoid (𝓞 E)).carrier
        w.asIdeal ↔ G w := by
  -- An element `y` lying in `w` and in no other place is such an integer unless `G w` holds.
  -- It is a level with prescribed places `{w}`, for the whole group and the integer `N = 1`.
  obtain ⟨y, hy⟩ : ∃ y : 𝓞 E, ∀ u : FinPlace E, y ∈ u.asIdeal ↔ u = w := by
    obtain ⟨y, -, hy_mem, -⟩ :=
      exists_levelGU_invTransposeGL_le (n := Unit) isOpen_univ le_top (S := {w})
        (fun u hu ↦ Or.inl hu) 1
    exact ⟨y, by simpa [Ideal.one_notMem] using hy_mem⟩
  simp only [Set.disjoint_left, Submonoid.mem_carrier, SetLike.mem_coe, Submonoid.mem_iInf,
    Ideal.mem_primeCompl_iff]
  constructor
  · intro h_disj
    by_contra hG_w
    have hy_notMem (u : FinPlace E) (hG_u : G u) : y ∉ u.asIdeal := by
      rw [hy u]
      rintro rfl
      exact hG_w hG_u
    exact h_disj hy_notMem ((hy w).mpr rfl)
  · exact fun hG_w z hz ↦ hz w hG_w

/-- Let `ψ ≠ 0` lie in `definiteForms 𝔑 ξ`, with `𝔑 ≠ 0`, and let the ideles `x` of `QuadField d`
act on `ψ` through the central scalars by `ω x` (`hψ_cen`). Let the scalar matrix of `x̄`, for `x`
in `(QuadField d)ˣ`, act in `ξ` by `∏ s, s x ^ (-A s)` (`hξ_centre`). Then `(ω, A)` is an algebraic
Hecke character of `QuadField d` (a member of `algHeckeChars`), and its base change to `E` is
unramified at every place `w` with `IsSafe 𝔑 w`. -/
lemma New.GaloisRep.centralChar_mem_algHeckeChars_and_charUnramifiedAt {E : Type} [Field E]
    [CMBase E]
    [EmbeddedNumberField E] {d : ℕ} [HasQuadSubfield d E] {n W : Type} [Fintype n] [DecidableEq n]
    [Nonempty n] [AddCommGroup W] [Module ℂ W] {ξ : Representation ℂ (GL n E) W} {𝔑 : 𝓞 E}
    (h𝔑 : 𝔑 ≠ 0) {ψ : GL n (𝔸f E) → W} (hψ_mem : ψ ∈ Variety.definiteForms 𝔑 ξ) (hψ_ne : ψ ≠ 0)
    {ω : (𝔸f (QuadField d))ˣ →* ℂ}
    (hψ_cen : ∀ x : (𝔸f (QuadField d))ˣ,
      rightRegular ℂ (GL n (𝔸f E)) W (centralScalar x) ψ = ω x • ψ)
    {A : (QuadField d →+* ℂ) → ℤ}
    (hξ_centre : ∀ x : (QuadField d)ˣ,
      ξ (GeneralLinearGroup.scalar n (star (x.map (algebraMap (QuadField d) E)))) =
        (∏ s : QuadField d →+* ℂ, s x ^ (-A s)) • 1) :
    ∃ hω : (ω.toHomUnits, Multiplicative.ofAdd A) ∈ algHeckeChars (QuadField d), ∀ w : FinPlace E,
      IsSafe 𝔑 w →
      New.CharUnramifiedAt (AlgHeckeChar.baseChange (E := E)
        ⟨(ω.toHomUnits, Multiplicative.ofAdd A), hω⟩).val.1 w := by
  have hω_eq {x : (𝔸f (QuadField d))ˣ} {c : ℂ}
      (h : rightRegular ℂ (GL n (𝔸f E)) W (centralScalar x) ψ = c • ψ) : ω x = c :=
    smul_left_injective ℂ hψ_ne ((hψ_cen x).symm.trans h)
  obtain ⟨⟨hψ_rat, -⟩, hψ_level⟩ := hψ_mem
  have hω_level (x : (𝔸f (QuadField d))ˣ) (hx : centralScalar x ∈ levelGU n 𝔑) :
      ω.toHomUnits x = 1 := Units.ext (hω_eq (hψ_level ⟨centralScalar x, hx⟩))
  refine ⟨⟨?_, fun x ↦ hω_eq (funext fun y ↦ ?_)⟩, fun w hw x hx ↦ hω_level _ ?_⟩
  · -- The kernel contains the ideles whose central scalar has level `𝔑`, an open subgroup.
    refine isOpen_mono (fun x hx ↦ hω_level x ⟨(centralScalar_mem_GU x).left, mem_comap.mp hx⟩)
      ((Variety.isOpen_congruenceGL_span h𝔑).preimage (.of_coeHom_comp <| .matrix_diagonal ?_))
    simp [starRingEnd_apply]
    fun_prop
  · -- On `(QuadField d)ˣ` the central scalar is rational, so it acts through `ξ`.
    let z : GL n E := .scalar n (star (x.map (algebraMap (QuadField d) E)))
    have hz : centralScalar (principalIdele x) = toFinGL z := by
      simp [z, Units.ext_iff, starRingEnd_apply]
    calc ψ (y * centralScalar (principalIdele x))
        = ψ (centralScalar (principalIdele x) * y) := congrArg ψ (commute_scalar_GL ..)
      _ = ξ z (ψ y) := by rw [hz, hψ_rat z y]
      _ = _ := by simp [z, hξ_centre]
  · -- The norm of a local unit at `w` gives an integral scalar, trivial at the places of `𝔑`.
    obtain ⟨-, -, hw_conj⟩ := hw
    refine mem_levelGU_of_map_evalAt_eq (centralScalar_mem_GU _).left ?_ fun u hu ↦
      ⟨1, by simpa using evalAt_centralScalar_of_ne (hw_conj u · hu) x⟩
    have h_unit : locIdele w x ∈ (Ô E).units :=
      idelesUnitOff_empty.le (locIdele_mem_idelesUnitOff hx)
    simpa [mem_intGL, ← map_inv, ite_mem, diagonal, star_eq_adeleMap, starRingEnd_apply] using
      h_unit.imp adeleNorm_mem_Ô adeleNorm_mem_Ô

open Classical in
/-- The place `w₁` together with the places `u` of `S` or conjugate to a place of `S` such that
the conjugate of the place of `QuadField d` below `u` is neither the place below `w₀` nor the
place below `w'`. The seed construction takes a level that lies exactly in these places and in the
places that contain an integer `N`. -/
private noncomputable def New.GaloisRep.levelPlaces {E : Type} [Field E] [NumberField E]
    [IsCMField E] (d : ℕ) [HasQuadSubfield d E] (S : Finset (FinPlace E)) (w₀ w₁ w' : FinPlace E) :
    Finset (FinPlace E) :=
  insert w₁ {u ∈ S ∪ S.image star |
    star (u.below (QuadField d)) ∉ [w₀.below (QuadField d), w'.below (QuadField d)]}

open Classical in
/-- Each place in `insert w₁ S` or its conjugate lies in `levelPlaces d S w₀ w₁ w'`, written out:
`w₁` together with the places `u` of `S` or conjugate to a place of `S` such that the conjugate
of the place below `u` is neither the place below `w₀` nor the place below `w'`. The reason: the
places below `w₀` and `w'` are split and not conjugate to each other, since the place below `w₀`
contains `ℓ` (as `v`, the place of `ε`, does), hence so does its conjugate, and then `hw'`
applies. -/
private lemma New.GaloisRep.mem_or_star_mem_insert_filter_of_isSplitPrimeToDisc {ℓ : ℕ} {E : Type}
    {d : ℕ} [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E]
    [HasQuadSubfield d E] {S : Finset (FinPlace E)} {w₀ w₁ v w' : FinPlace E}
    (hw₀_split : IsSplitPrimeToDisc (w₀.below (QuadField d)))
    (hw' : IsSplitPrimeToDisc (w'.below (QuadField d)) ∧
      (↑ℓ ∈ w'.asIdeal → w'.below (QuadField d) = w₀.below (QuadField d)))
    (hv : v ∉ S ∧ star v ∉ S ∧ v.below (QuadField d) = w₀.below (QuadField d))
    {ε : Ω →+* PadicAlgCl ℓ} (hε : placeOfEmb (ε.comp (algebraMap E Ω)) = v) :
    ∀ w ∈ insert w₁ S,
      w ∈ insert w₁ {u ∈ S ∪ S.image star |
          star (u.below (QuadField d)) ∉ [w₀.below (QuadField d), w'.below (QuadField d)]} ∨
        star w ∈ insert w₁ {u ∈ S ∪ S.image star |
          star (u.below (QuadField d)) ∉ [w₀.below (QuadField d), w'.below (QuadField d)]} := by
  have mem_below {n : ℕ} (w : FinPlace E) : ↑n ∈ w.1 ↔ ↑n ∈ (w.below (QuadField d)).1 := by simp
  grind [IsSplitPrimeToDisc.isSplit_and_prime_q, natCast_mem_placeOfEmb, below_star,
    mem_star_place, star_natCast]

/-- Rational unitary matrices act on a form through its coefficient system. Let `f` be a form of
weight `κ` on the unitary group, and let `ξ y` be the action of `ȳ` in weight `κ` for unitary `y`
(`hξ`). Then every rational unitary `y` acts on `f` by left translation by
`embFin (entryConj y)`, whose inverse transpose is `toFinGL y`. -/
private lemma New.GaloisRep.exists_apply_mul_eq_of_mem_unitary {E : Type} [Field E] [CMType E]
    {a : ℕ} {κ : Weight E} {f : Gf E (Fin a) → WeylIndex (Fin a) κ.1 → ℂ}
    (hf : f ∈ (stdSpace E (Fin a)).forms κ)
    {ξ : Representation ℂ (GL (Fin a) E) (WeylIndex (Fin a) κ.1 → ℂ)}
    (hξ : ∀ y : U (1 : Matrix (Fin a) (Fin a) E),
      (stdSpace E (Fin a)).weightRep κ.1 κ.2 (entryConj y) = ξ y.val)
    (y : GL (Fin a) E) (hy : y ∈ U (1 : Matrix (Fin a) (Fin a) E)) :
    ∃ c : Gf E (Fin a),
      (∀ u : Gf E (Fin a), f (c * u) = ξ y (f u)) ∧ invTransposeGL c.val = toFinGL y := by
  refine ⟨(stdSpace E (Fin a)).embFin (entryConj ⟨y, hy⟩), fun u ↦ ?_, ?_⟩
  · simpa [hξ] using hf.right (entryConj ⟨y, hy⟩) u
  · -- `erw`: the form `(stdSpace E (Fin a)).J` of the standard space is `1` only by unfolding
    erw [stdSpace_embFin]
    rfl

/-- An embedding `s` of `E` that induces a safe place `w` (`IsSafe 𝔑 w`) restricts on `QuadField d`
to the embedding given by `ε`, if `𝔑 ∈ w₀` and `v`, the place of `ε`, lies over the same place of
`QuadField d` as `w₀`. Otherwise `s` restricts to its conjugate, and `w₀` would lie above the
conjugate of the place below `w`, which a safe place forbids. -/
private lemma New.GaloisRep.comp_algebraMap_eq_of_isSafe {ℓ : ℕ} {E : Type} {d : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E] [HasQuadSubfield d E]
    [HasPrimitiveRoot5040 E] {𝔑 : 𝓞 E} {w w₀ v : FinPlace E} (hw : IsSafe 𝔑 w)
    (h𝔑_w₀ : 𝔑 ∈ w₀.asIdeal)
    (hv_below : v.below (QuadField d) = w₀.below (QuadField d)) {ε : Ω →+* PadicAlgCl ℓ}
    (hε : placeOfEmb (ε.comp (algebraMap E Ω)) = v) {s : E →+* ℂ} (hs : inducedPrime s = w) :
    s.comp (algebraMap (QuadField d) E) =
      (ιℓ.symm.toRingHom.comp (ε.comp (algebraMap E Ω))).comp (algebraMap (QuadField d) E) := by
  -- `QuadField d` has one infinite place, so `s` restricts to the embedding of `ε` or to its
  -- conjugate.
  obtain ⟨-, -, hw_conj⟩ := hw
  refine (InfinitePlace.mk_eq_iff.mp (by subsingleton)).resolve_right fun h ↦ hw_conj w₀ ?_ h𝔑_w₀
  ext x
  -- `x` lies in a place exactly when its image has norm below `1`; compare the two embeddings.
  simpa [← hv_below, ← hs, ← hε, map_star_CM] using
    congrArg (fun z : ℂ ↦ ‖ιℓ z‖ < 1) (RingHom.congr_fun h x).symm

open Classical in
/-- Galois representations from the cohomology of a PEL model: for PEL data `D` with neat level,
`D.β = betaK d`, good at the safe places, a safe place `v`, and a multiset `J` of nonnegative
integers each occurring in weight `ν + 1` for `θ`, some continuous representation satisfies
`IsSphericalAbove` at every safe place `w`: the members of `J` occur among its jumps at the
embedding `algebraMap E ℂ`, with no condition at the other embeddings, and the Hecke polynomial of
`ιℓ ∘ θ w` kills its geometric Frobenius elements. The model lives over the localisation at the
integers that lie in no safe place. -/
private lemma New.GaloisRep.exists_padicRep_of_pel {ℓ : ℕ} {E : Type} {d : ℕ}
    [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMBase E] [EmbeddedNumberField E] [HasQuadSubfield d E]
    [HasPrimitiveRoot5040 E] {D : PEL E} [NeZero D.rank] (h_neat : IsNeat (Fin D.rank) D.level)
    (hD_β : D.β = algebraMap (𝓞 (QuadField d)) (𝓞 E) (QuadField.betaK d))
    (hD_good : ∀ w : FinPlace E, IsSafe D.level w → D.IsGoodAt w.asIdeal) {v : FinPlace E}
    (hv_safe : IsSafe D.level v) (ν : ℕ) (θ : SafePlace D.level → ℕ → ℂ) (J : Multiset ℤ)
    (hJ_nonneg : ∀ u ∈ J, 0 ≤ u)
    (hJ_occurs : ∀ h : ℕ, (h : ℤ) ∈ J → OccursInWeight D.rank ν.succ θ h) :
    ∃ ρ : PadicRep Gal(Ω/E) ℓ,
      Continuous ρ.rep ∧
      ∀ w : SafePlace D.level,
        IsSphericalAbove ρ.rep OccursIn
          (fun τ : E →+* ℂ ↦ if algebraMap E ℂ = τ then J else 0) w.val.val
          (heckePoly w.val.val.q D.rank fun j : ℕ ↦ ιℓ (θ w j)) := by
  -- The base ring `R` of the model: the safe places are exactly the places that survive in `R`.
  let M : Submonoid (𝓞 E) := ⨅ (w : FinPlace E) (_ : IsSafe D.level w), w.asIdeal.primeCompl
  have hM (w : FinPlace E) : Disjoint M.carrier w.asIdeal ↔ IsSafe D.level w :=
    disjoint_iInf_primeCompl_iff (IsSafe D.level) w
  have hM_le : M ≤ nonZeroDivisors (𝓞 E) :=
    iInf₂_le_of_le v hv_safe v.asIdeal.primeCompl_le_nonZeroDivisors
  let R := Localization.subalgebra E M hM_le
  -- `R` is not a field, as `v` extends to a nonzero proper ideal; so maximal ideals are nonzero
  -- and lie over safe places.
  have hR_field : ¬IsField R := Ring.not_isField_of_ne_of_ne (Ideal.map_ne_bot_of_ne_bot v.3)
    ((map_algebraMap_ne_top_iff_disjoint ..).mpr ((hM v).mpr hv_safe))
  have hR (𝔪 : Ideal R) (h𝔪 : 𝔪.IsMaximal) : D.IsGoodAt (𝔪.comap (algebraMap _ R)) :=
    hD_good _ ((hM ⟨_, .comap _, (bot_lt_under_prime M R hM_le 𝔪
      (𝔪.bot_lt_of_maximal hR_field).ne').ne'⟩).mp ((disjoint_under_iff ..).mpr h𝔪.ne_top))
  obtain ⟨X⟩ :=
    exists_model (ThetaNull.nonempty_universalFamily hM_le hR).some h_neat hD_β hD_good ν.succ
  exact X.exists_galois_rep h_neat M iInf₂_le θ J hJ_nonneg hJ_occurs

open Classical in
/-- The level `𝔑` is prime to the places the local conditions ask for: if `𝔑` lies exactly in the
places containing `N` and those of `levelPlaces d S w₀ w₁ w'`, `N` is prime to `w₀` and `w'`, and
`w₁` is split and far from `w'`, `S` and `N`, `w₀ ∈ S`, `w₀` and `w'` lie over places with
`IsSplitPrimeToDisc`, `v` and `star v` lie outside `S` with `v` over the place below `w₀`, and `w'`
lies over that place too if `ℓ ∈ w'`, then `v`, and `w'` if `w'` and `star w'` lie outside `S`, are
safe, `𝔑 ∉ star w₀`, and `𝔑` lies in `w₁` but not in `star w₁`. -/
private lemma New.GaloisRep.isSafe_and_mem_of_mem_iff {ℓ : ℕ} {E : Type} {d : ℕ}
    [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E] [HasQuadSubfield d E]
    [HasPrimitiveRoot5040 E] {S : Finset (FinPlace E)} {w₀ w₁ v w' : FinPlace E} {N : ℕ+} {𝔑 : 𝓞 E}
    (h𝔑_mem : ∀ w : FinPlace E,
      𝔑 ∈ w.asIdeal ↔ ((N : ℕ) : 𝓞 E) ∈ w.asIdeal ∨ w ∈ levelPlaces d S w₀ w₁ w')
    (hN : ∀ w ∈ ({w₀, w'} : Finset (FinPlace E)), ((N : ℕ) : 𝓞 E) ∉ w.asIdeal) (hS : w₀ ∈ S)
    (hw₀_split : IsSplitPrimeToDisc (w₀.below (QuadField d)))
    (hv : v ∉ S ∧ star v ∉ S ∧ v.below (QuadField d) = w₀.below (QuadField d))
    (hw' : IsSplitPrimeToDisc (w'.below (QuadField d)) ∧
      (↑ℓ ∈ w'.asIdeal → w'.below (QuadField d) = w₀.below (QuadField d)))
    (hw₁ : w₁.IsSplit)
    (hw₁_far : w₁.below (QuadField d) ∉ (insert w' S).image (FinPlace.below (QuadField d)) ∧
      star (w₁.below (QuadField d)) ∉ (insert w' S).image (FinPlace.below (QuadField d)) ∧
      ((N : ℕ) : 𝓞 (QuadField d)) ∉ (w₁.below (QuadField d)).asIdeal) :
    (∀ᶠ w : FinPlace E in
      pure v ⊔ Filter.principal {w : FinPlace E | w' = w ∧ w' ∉ S ∧ star w' ∉ S}, IsSafe 𝔑 w) ∧
    𝔑 ∉ (star w₀).asIdeal ∧ 𝔑 ∈ w₁.asIdeal ∧ 𝔑 ∉ (star w₁).asIdeal := by
  have mem_below {n : ℕ} (w : FinPlace E) : ↑n ∈ w.1 ↔ ↑n ∈ (w.below (QuadField d)).1 := by simp
  simp [IsSafe, h𝔑_mem, levelPlaces]
  grind -ring -linarith [star_star, below_star, mem_star_place, star_natCast]

open Classical in
/-- A place `u` of `E` is safe for `𝔑` (`IsSafe`) if the place below it satisfies
`IsSplitPrimeToDisc`, neither that place nor its conjugate lies below `w₁` or below a place of `S`,
and it is prime to `N`; here `𝔑` lies exactly in the places that contain `N` and in those of
`levelPlaces d S w₀ w₁ w'`. -/
private lemma New.GaloisRep.isSafe_of_notMem_image_below {ℓ : ℕ} {E : Type} {d : ℕ}
    [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E] [HasQuadSubfield d E]
    [HasPrimitiveRoot5040 E] {S : Finset (FinPlace E)} {w₀ w₁ w' u : FinPlace E} {N : ℕ+} {𝔑 : 𝓞 E}
    (h𝔑_mem : ∀ w : FinPlace E,
      𝔑 ∈ w.asIdeal ↔ ((N : ℕ) : 𝓞 E) ∈ w.asIdeal ∨ w ∈ levelPlaces d S w₀ w₁ w')
    (hu_split : IsSplitPrimeToDisc (u.below (QuadField d)))
    (hu_far : u.below (QuadField d) ∉ (insert w₁ S).image (FinPlace.below (QuadField d)) ∧
      star (u.below (QuadField d)) ∉ (insert w₁ S).image (FinPlace.below (QuadField d)) ∧
      ((N : ℕ) : 𝓞 (QuadField d)) ∉ (u.below (QuadField d)).asIdeal) :
    IsSafe 𝔑 u := by
  have mem_below {n : ℕ} (w : FinPlace E) : ↑n ∈ w.1 ↔ ↑n ∈ (w.below (QuadField d)).1 := by simp
  simp [IsSafe, h𝔑_mem, levelPlaces]
  grind -ring -linarith [star_star, below_star, mem_star_place, star_natCast]

open Classical in
/-- A place `w` that is safe for `𝔑` (`IsSafe`) lies outside `S`, and so does its conjugate, and
`𝔑` lies in `w₀`. Here `𝔑` lies exactly in the places that contain `N` and in those of
`levelPlaces d S w₀ w₁ w'`, each place of `insert w₁ S` or its conjugate lies in that set
(`h_cover`), `w₀ ∈ S`, and `𝔑` is prime to the conjugate of `w₀`. -/
private lemma New.GaloisRep.mem_and_notMem_of_isSafe {ℓ : ℕ} {E : Type} {d : ℕ}
    [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E] [HasQuadSubfield d E]
    [HasPrimitiveRoot5040 E] {S : Finset (FinPlace E)} {w₀ w₁ w' : FinPlace E} {N : ℕ+} {𝔑 : 𝓞 E}
    (h𝔑_mem : ∀ w : FinPlace E,
      𝔑 ∈ w.asIdeal ↔ ((N : ℕ) : 𝓞 E) ∈ w.asIdeal ∨ w ∈ levelPlaces d S w₀ w₁ w')
    (h_cover : ∀ w ∈ insert w₁ S, w ∈ levelPlaces d S w₀ w₁ w' ∨ star w ∈ levelPlaces d S w₀ w₁ w')
    (hS : w₀ ∈ S) (h𝔑 : 𝔑 ∉ (star w₀).asIdeal ∧ 𝔑 ∈ w₁.asIdeal ∧ 𝔑 ∉ (star w₁).asIdeal)
    (w : FinPlace E) : IsSafe 𝔑 w → 𝔑 ∈ w₀.asIdeal ∧ w ∉ S ∧ star w ∉ S := by
  grind [levelPlaces, IsSafe, star_star, below_star]

open Classical in
/-- A principal level inside the stabiliser of `f`: if `f` has an open stabiliser and is fixed by
the integral points trivial at `S ∋ w₀`, and each place of `insert w₁ S` or its conjugate lies in
`levelPlaces d S w₀ w₁ w'`, then some multiple `𝔑` of `N` lies exactly in the places containing `N`
and those of that set, and each `u` whose inverse transpose lies in `levelGU (Fin a) 𝔑` fixes `f`,
is `≡ 1` modulo `w₀` and lies in `proIwahori` at `w₁`. -/
private lemma New.GaloisRep.exists_levelGU_le_rightStabilizer {ℓ : ℕ} {E : Type} {d : ℕ}
    [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E] [HasQuadSubfield d E]
    [HasPrimitiveRoot5040 E] {a : ℕ} {W : Type} {f : Gf E (Fin a) → W → ℂ}
    (hf_open : IsOpen ((rightStabilizer f : Subgroup (Gf E (Fin a))) : Set (Gf E (Fin a))))
    {S : Finset (FinPlace E)} (hf_off : ∀ k ∈ stdLevel E (Fin a) ⊓ Gf.trivialOn (Fin a) S,
      rightRegular ℂ (Gf E (Fin a)) (W → ℂ) k f = f)
    {w₀ w₁ w' : FinPlace E} (hS : w₀ ∈ S)
    (h_cover : ∀ w ∈ insert w₁ S, w ∈ levelPlaces d S w₀ w₁ w' ∨ star w ∈ levelPlaces d S w₀ w₁ w')
    (N : ℕ+) :
    ∃ 𝔑 : 𝓞 E, ((N : ℕ) : 𝓞 E) ∣ 𝔑 ∧
      (∀ w : FinPlace E, 𝔑 ∈ w.asIdeal ↔ ((N : ℕ) : 𝓞 E) ∈ w.asIdeal ∨
        w ∈ levelPlaces d S w₀ w₁ w') ∧
      ∀ u : Gf E (Fin a), invTransposeGL u.val ∈ levelGU (Fin a) 𝔑 →
        u ∈ rightStabilizer f ∧ Gf.atPlace w₀ u ∈ localCongruence (Fin a) w₀ 0 ∧
          Gf.atPlace w₁ u ∈ proIwahori := by
  let H : OpenSubgroup (Gf E (Fin a)) := ⟨rightStabilizer f, hf_open⟩ ⊓
    (.comap _ (continuous_atPlace w₀) ⟨localCongruence _ _ 0, isOpen_localCongruence⟩ ⊓
      .comap _ (continuous_atPlace w₁) ⟨proIwahori, isOpen_proIwahori⟩)
  have hH : stdLevel E _ ⊓ Gf.trivialOn _ ↑(insert w₁ S) ≤ H.toSubgroup := fun k hk ↦
    ⟨congrFun (hf_off k (hk.imp_right (by simp))), by simp [mem_trivialOn.mp hk.2, hS]⟩
  exact exists_levelGU_invTransposeGL_le H.isOpen' hH h_cover N

/-- At a safe place `w`, the Hecke element `heckeSum` of index `j` acts on `ψ` by the eigenvalue
`t w j` of `f` (`ht_eig`) times `ω` of the inverse of `uniformizerNorm w ^ j`: the linear maps `L`,
with `L w hw f = ψ`, carry the local Hecke operator over from `f` (`hL`), and the central scalar
acts through `ω` (`hψ_cen`). -/
private lemma New.GaloisRep.asAlgebraHom_heckeSum_eq_smul {E : Type} {d : ℕ} [Field E] [CMBase E]
    [EmbeddedNumberField E] [HasQuadSubfield d E] {n W : Type} [Fintype n] [DecidableEq n]
    [AddCommGroup W] [Module ℂ W] {𝔑 : 𝓞 E} {f : Gf E n → W}
    {ξ : Representation ℂ (GL n E) W} {ψ : GL n (𝔸f E) → W}
    (hψ_mem : ψ ∈ Variety.definiteForms 𝔑 ξ) {ω : (𝔸f (QuadField d))ˣ →* ℂ}
    (hψ_cen : ∀ x : (𝔸f (QuadField d))ˣ,
      rightRegular ℂ (GL n (𝔸f E)) W (centralScalar x) ψ = ω x • ψ)
    (L : (w : SplitFinPlace E) → 𝔑 ∉ (star w.val).asIdeal → (Gf E n → W) →ₗ[ℂ] GL n (𝔸f E) → W)
    (hL : ∀ (w : SplitFinPlace E) (hw : 𝔑 ∉ (star w.val).asIdeal)
      (g : GL n (LocField (w : FinPlace E))),
      rightRegular ℂ (GL n (𝔸f E)) W (conjAtSplit w g) ψ =
        L w hw (rightRegular ℂ (Gf E n) W (ofSplitPlace w.prop g) f))
    {t : SafePlace 𝔑 → ℕ → ℂ}
    (ht_eig : ∀ (w : SafePlace 𝔑) (j : ℕ),
      heckeSplit (rightRegular ℂ (Gf E n) W) w.val.prop j f = t w j • f)
    (w : SafePlace 𝔑) (j : ℕ) :
    (rightRegular ℂ (GL n (𝔸f E)) W).asAlgebraHom (heckeSum n ℂ w.val j) ψ =
      (t w j * (ω (uniformizerNorm w.val))⁻¹ ^ j) • ψ := by
  obtain ⟨-, -, hw_conj⟩ := w.prop
  have hw : 𝔑 ∉ (star w.val.val).asIdeal := hw_conj _ (below_star ..)
  have hL_f : L _ hw f = ψ := by simpa using (hL _ hw 1).symm
  let π := (rightRegular ℂ (GL n (𝔸f E)) W).comp (conjAtSplit w.val)
  have h_equiv (g : GL n (LocField (w.val : FinPlace E))) :
      L _ hw (((rightRegular ℂ (Gf E n) W).comp (ofSplitPlace w.val.prop)) g f) =
        π g (L _ hw f) := by
    simpa [hL_f, π] using (hL _ hw g).symm
  -- `L` intertwines the local actions on `f` and `ψ`, hence the Hecke operators.
  have h_eig : heckeGL π j ψ = t w j • ψ :=
    calc heckeGL π j ψ = heckeGL π j (L _ hw f) := by rw [hL_f]
      _ = L _ hw (heckeSplit (rightRegular ℂ (Gf E n) W) w.val.prop j f) :=
        (map_heckeFun _ (isHeckeFunction_basicDoubleCoset j).1 h_equiv).symm
      _ = t w j • ψ := by rw [ht_eig, map_smul, hL_f]
  -- `heckeSum` at `(w, j)` is the `j`-th Hecke operator at `w`, then a central scalar.
  rw [asAlgebraHom_heckeSum (w, j) hψ_mem.right, h_eig, map_smul, hψ_cen]
  simp [smul_smul]

/-- The representation for one embedding. Under the hypotheses of
`New.GaloisRep.exists_rep_of_cuspidal_type` other than the free jumps, for each complex embedding
`τ₀` of `E` some continuous representation satisfies `IsSphericalAbove` at the places of the
Frobenius data along `mostFrobenii E`, at `v`, and at `w'` if `w'` and its conjugate are outside
`S`: the jumps of `κ` at `τ₀` occur among its jumps, with no condition at the other embeddings, and
`ιℓ (P w)` kills its Frobenius elements. -/
private lemma New.GaloisRep.exists_padicRep_of_cuspidal_type_at_embedding {ℓ : ℕ} {E : Type}
    {a d : ℕ} [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E]
    [HasQuadSubfield d E] [HasPrimitiveRoot5040 E]
    (ha : Odd a) {κ : Weight E} {f : Gf E (Fin a) → WeylIndex (Fin a) κ.1 → ℂ}
    (hf : f ∈ (stdSpace E (Fin a)).forms κ) {S : Finset (FinPlace E)}
    {P : FinPlace E → Polynomial ℂ} (hP : IsSphericalOff S f P) {w₀ v : FinPlace E} (hS : w₀ ∈ S)
    (hw₀_split : IsSplitPrimeToDisc (w₀.below (QuadField d)))
    {χ : localCongruence (Fin a) w₀ 0 →* ℂ}
    (hχ_type : IsCuspidalType (localCongruence (Fin a) w₀ 0) χ)
    (hχ : ∀ j : localCongruence (Fin a) w₀ 0,
      rightRegular ℂ (Gf E (Fin a)) (WeylIndex (Fin a) κ.1 → ℂ)
        (ofSplitPlace hw₀_split.isSplit_of_below j.val) f = χ j • f)
    (hv : v ∉ S ∧ star v ∉ S ∧ v.below (QuadField d) = w₀.below (QuadField d))
    {ε : Ω →+* PadicAlgCl ℓ} (hε : placeOfEmb (ε.comp (algebraMap E Ω)) = v) (w' : FinPlace E)
    (hw' : IsSplitPrimeToDisc (w'.below (QuadField d)) ∧
      (↑ℓ ∈ w'.asIdeal → w'.below (QuadField d) = w₀.below (QuadField d))) (τ₀ : E →+* ℂ) :
    ∃ ρ : PadicRep Gal(Ω/E) ℓ,
      Continuous ρ.rep ∧
      ∀ᶠ w : FinPlace E in (mostFrobenii E).map (fun y : FrobeniusDatum E ↦ y.place) ⊔
          (pure v ⊔ Filter.principal {w : FinPlace E | w' = w ∧ w' ∉ S ∧ star w' ∉ S}),
        IsSphericalAbove ρ.rep OccursIn (Set.indicator {τ₀} (jumps κ a)) w ((P w).map ιℓ) := by
  classical
  have : NeZero a := .of_pos ha.pos
  obtain ⟨hf_ne, hf_off, h_eig⟩ := hP
  let s₀ : QuadField d →+* ℂ :=
    (ιℓ.symm.toRingHom.comp (ε.comp (algebraMap E Ω))).comp (algebraMap (QuadField d) E)
  -- `ξ` extends the weight `κ` to `GL (Fin a) E`, with central exponents `A₀` and `A₀ s₀ = μ`; by
  -- `h_occurs`, the eigenvalues of a test eigenform occur in weight `z + μ` for each jump `z` at
  -- an embedding over `s₀`.
  obtain ⟨ξ, μ, m, A₀, hμ, hξ, hξ_centre, h_nonneg, h_occurs⟩ :=
    exists_isCoefficientSystem ha (algebraMap (QuadField d) E) s₀ κ
  -- A second CM type `Ψ`, whose embedding `Ψ.Φ Ψ.v₀` at its distinguished place is `τ₀` (`hv₀`) and
  -- whose other embeddings differ from `τ₀` on `QuadField d` (`hΨ`), and PEL data at every nonzero
  -- level divisible by `N`, which lies in neither `w₀` nor `w'`.
  obtain ⟨Ψ, ⟨hv₀, hΨ⟩, N, hN, h_model⟩ := exists_pel a τ₀ {w₀, w'}
  -- An auxiliary split place `w₁`, away from `S`, `w'` and `N`, makes the level neat.
  have h_far (w : FinPlace E) : ∀ᶠ x : FinPlace E in .cofinite, (x ∉ S ∧ star x ∉ S ∧ ↑d ∉ x.1) ∧
      x.below (QuadField d) ∉ (insert w S).image (.below _) ∧
      star (x.below (QuadField d)) ∉ (insert w S).image (.below _) ∧ ↑(N : ℕ) ∉ (x.below _).1 :=
    (eventually_notMem_star_notMem d S).and
      ((tendsto_place_comap_cofinite (algebraMap ..)).eventually (eventually_notMem_star_notMem ..))
  obtain ⟨w₁, hw₁, ⟨⟨hw₁S, hw₁S', -⟩, hw₁_far⟩, h_neat⟩ :=
    ((frequently_prime_q.mono fun _ ↦ isSplit_of_q_prime).and_eventually
      ((h_far w').and (eventually_isNeat (n := Fin a)))).exists
  -- A level `𝔑` that lies exactly in the places of `levelPlaces d S w₀ w₁ w'` and those containing
  -- `N`, whose elements fix `f`, are `≡ 1` modulo `w₀` and lie in `proIwahori` at `w₁`.
  have h_cover :
      ∀ w ∈ insert w₁ S, w ∈ levelPlaces d S w₀ w₁ w' ∨ star w ∈ levelPlaces d S w₀ w₁ w' :=
    mem_or_star_mem_insert_filter_of_isSplitPrimeToDisc hw₀_split hw' hv hε
  obtain ⟨𝔑, hN𝔑, h𝔑_mem, h_level⟩ := exists_levelGU_le_rightStabilizer hf.1 hf_off hS h_cover N
  -- Call `w` safe if `IsSafe 𝔑 w` holds. By `hF_good`, `v` is safe, and so is `w'` if `w'` and
  -- `star w'` lie outside `S`.
  obtain ⟨hF_good, h𝔑_star_w₀, h𝔑_w₁, h𝔑_star_w₁⟩ :=
    isSafe_and_mem_of_mem_iff h𝔑_mem hN hS hw₀_split hv hw' hw₁ hw₁_far
  have h_good (w : FinPlace E) : IsSafe 𝔑 w → 𝔑 ∈ w₀.1 ∧ w ∉ S ∧ star w ∉ S :=
    mem_and_notMem_of_isSafe h𝔑_mem h_cover hS ⟨h𝔑_star_w₀, h𝔑_w₁, h𝔑_star_w₁⟩ w
  -- `t w j` is the eigenvalue of the `j`-th Hecke operator at `w` on `f`.
  have h_eig_safe (w : SafePlace 𝔑) : HasHeckePolyAt f w.val.val w.val.prop (P w.val.val) := by
    obtain ⟨-, hw_S, hw_S'⟩ := h_good w.val.val w.prop
    exact h_eig w.val.val w.val.prop hw_S hw_S'
  choose t ht_poly ht_eig using fun w : SafePlace 𝔑 ↦ (h_eig_safe w).right
  specialize h_neat 𝔑 (fun h ↦ by simp [h] at h𝔑_star_w₀) h𝔑_w₁
  choose h_level_fix h_level_w₀ h_level_w₁ using h_level
  obtain ⟨D, rfl, rfl, hD_β, hD_good⟩ := h_model 𝔑 h_neat.1 hN𝔑
  -- The form `ψ` attached to `f`; rational unitary matrices act on `f` through `ξ`
  -- (`exists_apply_mul_eq_of_mem_unitary`).
  obtain ⟨ψ, hψ_mem, hψ_ne, ⟨ω, hψ_cen⟩, hψ_loc⟩ := exists_central_eigenform ξ hf_ne h_neat
    ⟨w₀, hw₀_split.isSplit_of_below⟩ h𝔑_star_w₀ (exists_apply_mul_eq_of_mem_unitary hf hξ)
      h_level_fix
  choose L hL using hψ_loc
  have hL_f (w : SplitFinPlace E) (hw : D.level ∉ (star w.val).asIdeal) : L w hw f = ψ := by
    simpa using (hL w hw 1).symm
  have h_test : IsTestVector D.level (rightRegular ..) ψ ⟨_, hw₀_split.isSplit_of_below⟩ ⟨_, hw₁⟩
    χ := by
    refine
      { place_ne := hS.ne_of_notMem hw₁S
        notMem_star_fst := h𝔑_star_w₀
        mem_snd := h𝔑_w₁
        notMem_star_snd := h𝔑_star_w₁
        level_le := fun g hg ↦ by simpa using h_level_w₀ _ hg
        le_localIntGL := fun _ hg ↦ hg.1
        isCuspidalType := hχ_type
        level_le_proIwahori := fun g hg ↦ by simpa using h_level_w₁ _ hg
        ne_zero := hψ_ne
        isEigenvector := fun j ↦ (hL _ h𝔑_star_w₀ _).trans (by rw [hχ, map_smul, hL_f])
        fixed := fun g ↦ ?_ }
    have h_fix : rightRegular ℂ _ _ (ofSplitPlace hw₁ g.val) f = f := by
      simpa using (mem_sphericalAt_iff hw₁).mp (h_eig _ hw₁ hw₁S hw₁S').left g
    exact (hL _ h𝔑_star_w₁ _).trans (by simp only [h_fix, hL_f, MonoidHom.one_apply, one_smul])
  -- `ω` is an algebraic Hecke character, and its base change is unramified at the safe places.
  obtain ⟨hω, h_unr⟩ := centralChar_mem_algHeckeChars_and_charUnramifiedAt h_neat.1 hψ_mem hψ_ne
    hψ_cen hξ_centre
  -- The eigenvalues `θ` of `ψ` are those of `f` twisted by `ω`.
  let θ (w : SafePlace D.level) (j : ℕ) : ℂ := t w j * (ω (uniformizerNorm w.val))⁻¹ ^ j
  have hθ (w : SafePlace D.level) (j : ℕ) :
      (rightRegular ..).asAlgebraHom (heckeSum _ ℂ w.val j) ψ = θ w j • ψ :=
    asAlgebraHom_heckeSum_eq_smul hψ_mem hψ_cen L hL ht_eig w j
  -- `J`: the jumps at `τ₀` shifted by `μ` if `τ₀` lies over `s₀`, and no condition otherwise.
  let J : Multiset ℤ :=
    ((jumps κ D.rank τ₀).map (· + (μ : ℤ))).filter fun _ ↦ τ₀.comp (algebraMap ..) = s₀
  have hJ (u : ℤ) (hu : u ∈ J) : 0 ≤ u ∧ OccursInWeight D.rank m.succ θ u.toNat := by
    obtain ⟨⟨z, hz, rfl⟩, hs₀⟩ : (∃ z ∈ jumps κ D.rank τ₀, z + (μ : ℤ) = u) ∧
        τ₀.comp (algebraMap (QuadField d) E) = s₀ := by simpa [J] using hu
    exact ⟨h_nonneg hs₀ hz, h_occurs hs₀ hz hv₀ (fun u hu h ↦ hΨ u hu (by rw [h, hv₀, hs₀])) h_neat
      ⟨hψ_mem, ⟨_, _, _, _, h_test⟩, hθ⟩⟩
  -- The cohomology of a PEL model for `D` gives a representation with the eigenvalues `θ`.
  have hv_safe : IsSafe D.level v := hF_good.left
  obtain ⟨ρ, hρ, hρ_sph⟩ := exists_padicRep_of_pel h_neat hD_β hD_good hv_safe m θ J
    (fun u hu ↦ (hJ u hu).1) fun h hh ↦ (hJ h hh).2
  -- Twisting by the base change of `ω` removes the shift `μ` and the factor `ω`.
  obtain ⟨ρ', hρ', h_twist⟩ := exists_twist_algHeckeChar (.baseChange ⟨_, hω⟩) μ hρ
  -- Almost all places of prime norm are safe; `hF_good` covers `v` and `w'`.
  have h_ev : ∀ᶠ w in (mostFrobenii E).map (·.place), IsSafe D.level w :=
    eventually_mostFrobenii (h_far w₁) fun y ⟨⟨_, _, hyd⟩, h_off⟩ ↦
      isSafe_of_notMem_image_below h𝔑_mem (isSplitPrimeToDisc_below_of_prime_norm y.prime_q hyd)
        h_off
  refine ⟨ρ', hρ', (Filter.eventually_sup.mpr ⟨h_ev, hF_good⟩).mono fun w hw A hA ↦ ?_⟩
  obtain ⟨-, -, hv_below⟩ := hv
  -- An embedding that induces the safe place `w` restricts to `s₀`.
  have h_s₀ (s : E →+* ℂ) (hs : inducedPrime s = w) : s.comp (algebraMap (QuadField d) E) = s₀ :=
    comp_algebraMap_eq_of_isSafe hw (h_good w hw).left hv_below hε hs
  obtain ⟨h_unr', h_jump, h_poly⟩ :=
    h_twist w (by simp +contextual [h_s₀, hμ, AlgHeckeChar.baseChange]) (h_unr w hw)
      (hρ_sph ⟨⟨w, hw.1.isSplit_of_below⟩, hw⟩) hA
  rw [ht_poly ⟨⟨w, hw.1.isSplit_of_below⟩, hw⟩, Fintype.card_fin, map_heckePoly]
  refine ⟨h_unr', h_jump.congr hA ?_, h_poly⟩
  -- At an embedding inducing `w` the type of the twist is `μ`, which cancels the shift in `J`.
  simp +contextual [J, h_s₀, hμ, hv₀, AlgHeckeChar.baseChange, apply_ite, algebraMap_toAlgebra,
    Pi.single_apply]
  grind

/-- A weak form of a case of the theorem on Galois representations attached to cohomological
cuspidal forms, in odd rank `a`. Let `f` be a form of weight `κ` on the definite unitary group,
spherical off `S` with Hecke polynomials `P` (`hP`), that transforms at a split place `w₀ ∈ S` by a
cuspidal type `χ` of the matrices `≡ 1` modulo `w₀` (`localCongruence (Fin a) w₀ 0`). Let `v`, the
place of `ε`, lie with its conjugate outside `S` and over the place of `QuadField d` below `w₀`, and
let `κ` have `a` free jumps `e i` at `ε` (`HasNoSmallRelations`). Then some continuous `r` of rank
`a` has characteristic polynomials `ιℓ (P w)` along the filter `mostFrobenii E` and satisfies
`IsSphericalAbove` with exactly the jumps of `κ` at a given place `w'` as in `hw'`, if `w'` and its
conjugate lie outside `S`. -/
lemma New.GaloisRep.exists_rep_of_cuspidal_type {ℓ : ℕ} {E : Type} {a d : ℕ} [ThePrime ℓ]
    [PadicIso ℓ] [Field E] [CMType E] [EmbeddedNumberField E] [HasQuadSubfield d E]
    [HasPrimitiveRoot5040 E]
    (ha : Odd a) {κ : Weight E} {f : Gf E (Fin a) → WeylIndex (Fin a) κ.1 → ℂ}
    (hf : f ∈ (stdSpace E (Fin a)).forms κ) {S : Finset (FinPlace E)}
    {P : FinPlace E → Polynomial ℂ} (hP : IsSphericalOff S f P) {w₀ v : FinPlace E} (hS : w₀ ∈ S)
    (hw₀_split : IsSplitPrimeToDisc (w₀.below (QuadField d)))
    {χ : localCongruence (Fin a) w₀ 0 →* ℂ}
    (hχ_type : IsCuspidalType (localCongruence (Fin a) w₀ 0) χ)
    (hχ : ∀ j : localCongruence (Fin a) w₀ 0,
      rightRegular ℂ (Gf E (Fin a)) (WeylIndex (Fin a) κ.1 → ℂ)
        (ofSplitPlace hw₀_split.isSplit_of_below j.val) f = χ j • f)
    (hv : v ∉ S ∧ star v ∉ S ∧ v.below (QuadField d) = w₀.below (QuadField d))
    {ε : Ω →+* PadicAlgCl ℓ} (hε : placeOfEmb (ε.comp (algebraMap E Ω)) = v) {e : Fin a → ℤ}
    (he_free : HasNoSmallRelations e)
    (he_jumps : ∀ i : Fin a, e i ∈ jumps κ a (RingHom.comp ιℓ.symm (ε.comp (algebraMap E Ω))))
    (w' : FinPlace E) (hw' : IsSplitPrimeToDisc (w'.below (QuadField d)) ∧
      (↑ℓ ∈ w'.asIdeal → w'.below (QuadField d) = w₀.below (QuadField d))) :
    ∃ r : GalRep ℓ E (Fin a),
      Continuous r ∧
      -- (a) characteristic polynomials along the filter `mostFrobenii E`
      (∀ᶠ y : FrobeniusDatum E in mostFrobenii E, (r y.frob).val.charpoly = (P y.place).map ιℓ) ∧
      -- (b) local behaviour at `w'`
      (w' ∉ S ∧ star w' ∉ S → IsSphericalAbove r Eq (jumps κ a) w' ((P w').map ιℓ)) := by
  -- For each embedding `τ₀`, transfer `f` to a form `ψ` on the definite frames, realize its
  -- eigenvalues in the cohomology of a PEL model and twist: this gives a representation with the
  -- jumps at `τ₀` (`exists_padicRep_of_cuspidal_type_at_embedding`).
  -- `exists_galRep_charpoly_eq_of_forall_embedding` joins these, using the free jumps at `v`.
  have : NeZero a := .of_pos ha.pos
  have h_one :=
    exists_padicRep_of_cuspidal_type_at_embedding ha hf hP hS hw₀_split hχ_type hχ hv hε w' hw'
  obtain ⟨hf_ne, -, h_eig⟩ := hP
  have h_monic : ∀ᶠ y : FrobeniusDatum E in mostFrobenii E,
      ↑ℓ ∉ y.place.asIdeal ∧ ((P y.place).map (ιℓ : ℂ →+* PadicAlgCl ℓ)).IsMonicOfDegree a := by
    refine eventually_mostFrobenii (eventually_notMem_star_notMem ℓ S) fun y ⟨hyS, hyS', hyℓ⟩ ↦ ?_
    obtain ⟨h_deg, h_lead⟩ :=
      (h_eig _ (isSplit_of_q_prime y.prime_q) hyS hyS').isMonicOfDegree hf_ne
    exact ⟨hyℓ, by simp [h_deg], h_lead.map _⟩
  obtain ⟨r, hr, h_frob, -, h_w'⟩ :=
    exists_galRep_charpoly_eq_of_forall_embedding κ h_monic he_free he_jumps (by simp [hε]) h_one
  exact ⟨r, hr, h_frob, fun hS' ↦ h_w' ⟨rfl, hS'⟩⟩
