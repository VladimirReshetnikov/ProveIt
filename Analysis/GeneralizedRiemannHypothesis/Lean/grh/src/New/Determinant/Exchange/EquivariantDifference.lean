import New.Determinant.Exchange.MatchingPartners

/-!
# The difference in the exchange identity as an equivariant lift

This file is a step towards the identity between theta integrals over `U(V)` and `U(V')`, where
`rk W = rk V + rk V'`. The identity is taken for matched functions `Φ`, `Ψ` at the ramified places
of the tame character `𝔠`. This file defines the small side `New.Exchange.thetaSmall`. It proves
how `thetaLarge` and `thetaSmall` change under translation at the ramified places, and that both
are invariant under the integral points of `U(W)` that are trivial there. From this it shows that
the difference of the two sides is an equivariant lift.

## Main definitions and results

* `New.Exchange.thetaSmall`: the theta integral for `V'` of the datum `Ψ`.
* `New.Exchange.exists_isEquivariantLift_eq_thetaLarge_sub_smul`: the difference
  `thetaLarge Φ - c • thetaSmall Ψ` is a linear map of `Ψ` alone, on a `GL_n`-stable space, and is
  equivariant (`New.Exchange.IsEquivariantLift`).

Notions from other files:
* `thetaIntegral S T α β f`: the integral over `[U(T)]` of the theta kernel of the datum `f`.
* `thetaLarge W V 𝔠 v Φ`: the theta integral over `[U(V)]` of the datum `v ⊗ Φ`.
* `localChar P ξ k`: the character `t ↦ ξ t * |t| ^ (k / 2)` of the completions at `P`.
* `sameSectionPairs χ σ`: pairs `(Φ, Ψ)` of Schwartz–Bruhat functions on `a × n` and `n × b`
  matrices, `σ : b ⊕ a ≃ n`, whose values of `localSection χ` at the blocks of `k` differ by
  `χ (det k)`.

## Relation to the literature

See `New.Determinant.Exchange.TheoremForPartners` for related work.
-/

namespace New.Exchange

open RingHom Matrix Pi WeilData SemilocalField Fintype SplitTameChar GeneralLinearGroup

variable {E : Type} [Field E] [CMType E] [WeilData E]
  {n a b : Type} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  {s : n → ℤˣ} {t : a → ℤˣ} {t' : b → ℤˣ} {μ : NumberField.InfinitePlace E → ℤ} (W : Space E n s)
  (V : Space E a t) (V' : Space E b t') (𝔠 : SplitTameChar E μ)

/-- The small side: the theta integral over `U(V)`, as a function on `U(W)`, of the datum with real
part `v` and component `y ↦ Ψ yᵀ`, read in the model at the conjugates of the ramified places of
`𝔠`. The two characters of `U(1)` are `ν υ ^ ⌊rk W / 2⌋` (`rankTwist`) and `υ ^ rk V`, where
`ν = 𝔠.character`. Here `υ` is the splitting character of the Weil data, restricted to the norm-one
ideles (`upsilonU1`). In the exchange identity it is applied to the space `V'`. -/
noncomputable abbrev thetaSmall
    (v : (Fock.isVacuum_realVac (ε := realSigns E (homSigns s t))).Model)
    (Ψ : Matrix n a (LocProd 𝔠.ramifiedPlaces) → ℂ) : G E s → ℂ :=
  thetaIntegral W V (rankTwist 𝔠.character n) (upsilonU1 ^ card a)
    (localDatum W V v (fun y : Matrix a n (LocProd 𝔠.ramifiedPlaces) ↦ Ψ yᵀ) 𝔠.readsAt.star)

/-- Polynomial growth of the theta kernel on `U(W)`, uniform on `U(V)` (`IsTargetBounded`), is kept
when the datum is moved by an element `k` of `U(V)`. -/
lemma IsTargetBounded.pairWeil_one_left {W : Space E n s} {V : Space E a t} {f : 𝒮 (W.hom V)}
    (hf : IsTargetBounded W V f) (α β : AutChar E) (k : G E t) :
    IsTargetBounded W V (pairWeil W V α β (1, k) f) := by
  obtain ⟨B, C, h_bound⟩ := hf
  refine ⟨B, C, fun α' β' g h ↦ ?_⟩
  -- the kernel at `(g, h)` becomes the kernel at `(g, h * k)`, times a scalar of modulus `1`
  have h_norm : ‖pairTheta W V α' β' (pairWeil W V α β (1, k) f) (g, h)‖ =
      ‖pairTheta W V α' β' f (g, h * k)‖ := by
    simp [pairTheta, pairWeil, rep_apply_apply, ← map_mul, Circle.norm_coe]
  exact h_norm.trans_le (h_bound α' β' g (h * k))

/-- The theta integral is homogeneous in the datum. -/
lemma thetaIntegral_smul (α β : AutChar E) (c : ℂ) (f : 𝒮 (W.hom V)) (x : G E s) :
    thetaIntegral W V α β (c • f) x = c * thetaIntegral W V α β f x := by
  simp [thetaIntegral, pairTheta, MeasureTheory.integral_const_mul]

/-- Let `π` be a ring map from the finite adeles of the CM field `E` to `F` that reads the
components at a set `A` of places (`ReadsAt`): `A` is disjoint from its conjugate, `π` has a
continuous additive section onto the `A`-part, and `π x` is integral exactly if `x` is so at `A`.
Let `φ` be Schwartz–Bruhat, vanishing outside some set `U`, and let `g ∈ U(W)`, `h ∈ U(V)` be finite
points supported on `A` and its conjugate. In the Weil representation (`pairWeil`), `(g, h)` moves
the datum of `φ` to that of `x ↦ φ (π h⁻¹ * x * π g)`. Here the datum (`localDatum`) is the vector
`v` of the Fock space `PairFock` at the infinite places, `φ` at `A` and the vacuum elsewhere. The
new datum is multiplied by `χ_W (det h) / χ_V (det g) * |det g| ^ (rk V / 2) / |det h| ^ (rk
W / 2)`. The determinants are taken on `A` (`detOn`) and `|·|` is `ideleAbs`.
`χ_W = α.spaceChar (rk W)` and `χ_V = β.spaceChar (rk V)`. -/
lemma ReadsAt.pairWeil_localDatum_of_mem_supportedOn {F : Type} [SemilocalField F]
    {A : Set (FinPlace E)} {π : 𝔸f E →+* F} (hπ : ReadsAt A π) (α β : AutChar E)
    (v : PairFock E s t) {U : Set (Matrix a n F)} {φ : Matrix a n F → ℂ}
    (hφ : φ ∈ schwartzBruhat U) {g : Gf E n} {h : Gf E a} (hg : g ∈ Gf.supportedOn n A)
    (hh : h ∈ Gf.supportedOn a A) :
    pairWeil W V α β ((1, g), 1, h) (localDatum W V v φ hπ) =
      ((α.spaceChar (card n)).val (detOn A h.val) / (β.spaceChar (card a)).val (detOn A g.val) *
          √(ideleAbs (detOn A g.val)) ^ card a / √(ideleAbs (detOn A h.val)) ^ card n : ℂ) •
        localDatum W V v
        (fun x : Matrix a n F ↦ φ (h⁻¹.val.val.map π * x * g.val.val.map π)) hπ := by
  rw [pairWeil_integrated_fin, pairWeil_schrodingerOp_of_mem_supportedOn hπ.disjoint_star
    (hΨ := hπ.isSchwartzBruhat hφ) hg hh]
  simp

/-- Let `𝔠` be a split tame character: a character `ν = 𝔠.character` of the norm-one ideles, tamely
ramified exactly at a finite set `S = 𝔠.ramifiedPlaces` of places disjoint from its conjugate. Let
`rk W` be even and let `k ∈ U(V)` be finite (`Gf`), supported at `S` and its conjugate, with
component `k_S` at `S`. Consider the datum `localDatum W V v Φ 𝔠.readsAt`: `v` at the infinite
places, the function `Φ` at `S` and the vacuum elsewhere. It lies in the Weil representation
`pairWeil` of `(W, V)` with both characters `ν⁻¹ υ ^ ⌊rk W / 2⌋` (`rankTwist`), `υ` being the
splitting character of the Weil data. Then `k⁻¹` moves it to the same datum with `x ↦ Φ (k_S * x)`
in place of `Φ`, times the value at `det k_S` of `t ↦ ν (t / t̄) |t| ^ (rk W / 2)` (`localChar`).
Here `Φ` is Schwartz–Bruhat on the matrices `x` of full row rank. -/
lemma pairWeil_inv_localDatum (hn : 2 ∣ card n) (v : PairFock E s t)
    {Φ : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ} (hΦ : Φ ∈ schwartzBruhat fun x ↦ HasLeftInv xᵀ)
    {k : Gf E a} (hk : k ∈ Gf.supportedOn a 𝔠.ramifiedPlaces) :
    pairWeil W V (rankTwist 𝔠.character⁻¹ n) (rankTwist 𝔠.character⁻¹ n) ((1, 1), 1, k⁻¹)
        (localDatum W V v Φ 𝔠.readsAt) =
      localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange (card n)
        (atPlaces 𝔠.ramifiedPlaces k).val.det •
        localDatum W V v (fun x ↦ Φ ((atPlaces 𝔠.ramifiedPlaces k).val * x)) 𝔠.readsAt := by
  rw [𝔠.readsAt.pairWeil_localDatum_of_mem_supportedOn W V _ _ v hΦ (one_mem _) (inv_mem hk)]
  simp [spaceChar_rankTwist hn, atPlaces_star]

/-- Let `𝔠` be a split tame character, with character `ν` of the norm-one ideles and finite set `S`
of ramified places. Let `rk W = card b + rk V` (`σ`) be even, and let `χ` be the character
`t ↦ ν (t / t̄) |t| ^ (rk W / 2)` at `S` (`localChar`). Let `(Φ, Ψ)` be a same-section pair for `χ`
and `σ`: both are Schwartz–Bruhat on matrices of full rank, and for each invertible `k` the coset
sum `localSection χ` of `y ↦ Φ yᵀ` at the transposed rows `a` of `k⁻¹` is `χ (det k)` times that of
`Ψ` at the columns `b` of `k`. By `thetaLarge W V 𝔠 v Φ` is meant the function on `U(W)` that
integrates over `[U(V)]` the theta kernel of the datum `v` at the infinite places, `Φ` at `S`, the
vacuum elsewhere, both characters being `ν⁻¹ υ ^ ⌊rk W / 2⌋` for the splitting character `υ` of the
Weil data. Let `g ∈ U(W)` be finite, supported at `S` and its conjugate, with component `g_S` at
`S`. Then `thetaLarge` of `y ↦ χ (det g_S⁻¹) Φ (y g_S⁻¹)` at `x g` is that of `Φ` at `x` divided by
`(υ |·| ^ (1 / 2)) (det g_S) ^ card b`. -/
lemma thetaLarge_translate_mul (σ : b ⊕ a ≃ n) (hn : 2 ∣ card n) (v : PairFock E s t)
    {Φ : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ} {Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ}
    (hp : (Φ, Ψ) ∈ sameSectionPairs (localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange (card n)) σ)
    {g : Gf E n} (hg : g ∈ Gf.supportedOn n 𝔠.ramifiedPlaces) (x : G E s) :
    thetaLarge W V 𝔠 v
        (localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange (card n)
          (atPlaces 𝔠.ramifiedPlaces g⁻¹).val.det •
          fun y : Matrix a n (LocProd 𝔠.ramifiedPlaces) ↦
            Φ (y * (atPlaces 𝔠.ramifiedPlaces g⁻¹).val)) (x * (1, g)) =
      thetaLarge W V 𝔠 v Φ x / localChar 𝔠.ramifiedPlaces υ 1 (atPlaces 𝔠.ramifiedPlaces g).val.det
        ^ card b := by
  obtain ⟨⟨h_sb, -⟩, -⟩ := sameSectionPairs.translate_mem _ σ hp (atPlaces 𝔠.ramifiedPlaces g⁻¹)
  have h_char : (rankTwist 𝔠.character⁻¹ n).spaceChar (card a) = 𝔠.character⁻¹.baseChange * υ ^ card
    b := by
    rw [← spaceChar_rankTwist (n := n) hn]
    simp [AutChar.spaceChar, ← card_congr σ, pow_add, mul_assoc, mul_comm (υ ^ card a)⁻¹]
  -- `pairWeil` undoes the translation; its scalar combines with the factor `χ (det g_S⁻¹)`
  let d : (𝔸 E)ˣ := detOn 𝔠.ramifiedPlaces g.val
  have h_scalar : (((𝔠.character⁻¹.baseChange * υ ^ card b).val d : ℂ)⁻¹ * √(ideleAbs d) ^ card a) *
      localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange (card n)
        (atPlaces 𝔠.ramifiedPlaces g⁻¹).val.det =
        (localChar 𝔠.ramifiedPlaces υ 1 (atPlaces 𝔠.ramifiedPlaces g).val.det ^ card b)⁻¹ := by
    rw [localChar_det, localChar_det, ← card_congr σ]
    simp [d, mul_pow, zpow_add₀, field]
  rw [thetaLarge, ← thetaIntegral_pairWeil ((1, g), 1, 1),
    𝔠.readsAt.pairWeil_localDatum_of_mem_supportedOn W V _ _ v h_sb hg (one_mem _), h_char,
    div_eq_inv_mul (thetaLarge W V 𝔠 v Φ x), ← h_scalar, ← thetaIntegral_smul, mul_smul]
  simp [d, localDatum, atPlaces_star, ← Pi.smul_def, -smul_eq_mul, -localChar_det]

/-- By `thetaSmall W V' 𝔠 v' Ψ` is meant the function on `U(W)` that integrates over `[U(V')]` the
theta kernel of the datum `v'` at the infinite places and `y ↦ Ψ yᵀ` at the conjugates of the
ramified places `S` of `𝔠`; the space `V'` has rank `card b`. Let `g ∈ U(W)` be finite, supported at
`S` and its conjugate, with component `g_S` at `S`. If `y ↦ Ψ (g_S y)` is Schwartz–Bruhat, its
`thetaSmall` at `x g` is `thetaSmall Ψ` at `x` divided by `(υ |·| ^ (1 / 2)) (det g_S) ^ card b`,
where `υ` is the splitting Hecke character of the Weil data. -/
lemma thetaSmall_translate_mul (v' : PairFock E s t')
    {Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ}
    {g : Gf E n} (hg : g ∈ Gf.supportedOn n 𝔠.ramifiedPlaces)
    (hΨ : (fun y : Matrix n b (LocProd 𝔠.ramifiedPlaces) ↦
      Ψ ((atPlaces 𝔠.ramifiedPlaces g).val * y)) ∈
      schwartzBruhat HasLeftInv) (x : G E s) :
    thetaSmall W V' 𝔠 v' (fun y ↦ Ψ ((atPlaces 𝔠.ramifiedPlaces g).val * y)) (x * (1, g)) =
      thetaSmall W V' 𝔠 v' Ψ x / localChar 𝔠.ramifiedPlaces υ 1
        (atPlaces 𝔠.ramifiedPlaces g).val.det ^ card b := by
  have hg_star : g ∈ Gf.supportedOn n (star ⁻¹' (𝔠.ramifiedPlaces : Set (FinPlace E))) := by
    simp +contextual [Gf.mem_supportedOn.1 hg]
  -- `pairWeil` undoes the translation, up to a scalar in the determinant `d̄⁻¹` on the conjugates
  let d : (𝔸 E)ˣ := detOn 𝔠.ramifiedPlaces g.val
  have h_scalar : (((upsilonU1 ^ card b : AutChar E).spaceChar (card b)).val (star d⁻¹) : ℂ)⁻¹ *
      √(ideleAbs (star d⁻¹)) ^ card b =
        (localChar 𝔠.ramifiedPlaces υ 1 (atPlaces 𝔠.ramifiedPlaces g).val.det ^ card b)⁻¹ := by
    simp [d, AutChar.spaceChar, υ_star, sq, mul_pow, field]
  rw [thetaSmall, ← thetaIntegral_pairWeil ((1, g), 1, 1),
    𝔠.readsAt.star.pairWeil_localDatum_of_mem_supportedOn W V' _ _ v'
      hΨ.transpose_mem_schwartzBruhat hg_star (one_mem _),
    thetaIntegral_smul, detOn_preimage_star g, div_eq_inv_mul (thetaSmall W V' 𝔠 v' Ψ x),
      ← h_scalar]
  simp [d, thetaSmall, atPlaces_star, -coe_comp]

/-- For Schwartz–Bruhat `Φ`, `thetaLarge Φ` is right invariant under the integral points `k` of
`U(W)` that are trivial at the ramified places of `𝔠`. -/
lemma thetaLarge_mul_of_mem_stdLevel (v : PairFock E s t)
    {Φ : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat fun x : Matrix a n (LocProd 𝔠.ramifiedPlaces) ↦ HasLeftInv xᵀ)
    {k : Gf E n}
    (hk_int : k ∈ stdLevel E n) (hk_triv : k ∈ Gf.trivialOn n 𝔠.ramifiedPlaces) (x : G E s) :
    thetaLarge W V 𝔠 v Φ (x * (1, k)) = thetaLarge W V 𝔠 v Φ x := by
  have h_one : k.val.val.map (evalPlaces 𝔠.ramifiedPlaces) = 1 :=
    congrArg Units.val (atPlaces_eq_one_of_mem_trivialOn hk_triv)
  rw [thetaLarge, ← thetaIntegral_pairWeil ((1, k), 1, 1),
    𝔠.readsAt.pairWeil_localDatum_of_mem_stdLevel hΦ hk_int (one_mem _)]
  simp [rankTwist, character_detFin_eq_of_mem_stdLevel, atPlaces_eq_one_of_mem_trivialOn, h_one,
    hk_int, hk_triv]

/-- For Schwartz–Bruhat `Ψ`, `thetaSmall Ψ` is right invariant under the integral points `k` of
`U(W)` that are trivial at the ramified places of `𝔠`. -/
lemma thetaSmall_mul_of_mem_stdLevel (v' : PairFock E s t')
    {Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhat HasLeftInv) {k : Gf E n}
    (hk_int : k ∈ stdLevel E n) (hk_triv : k ∈ Gf.trivialOn n 𝔠.ramifiedPlaces) (x : G E s) :
    thetaSmall W V' 𝔠 v' Ψ (x * (1, k)) = thetaSmall W V' 𝔠 v' Ψ x := by
  rw [thetaSmall, ← thetaIntegral_pairWeil ((1, k), 1, 1),
    𝔠.readsAt.star.pairWeil_localDatum_of_mem_stdLevel hΨ.transpose_mem_schwartzBruhat hk_int
      (one_mem _)]
  simp [-coe_comp, rankTwist, character_detFin_eq_of_mem_stdLevel,
    atPlaces_eq_one_of_mem_trivialOn,
    atPlaces_star, hk_int, hk_triv]

/-- For `v'` with all moments finite, `thetaSmall` is linear on Schwartz–Bruhat functions. -/
lemma exists_linear_thetaSmall {v' : PairFock E s t'} (hv' : IsSchwartzVector v') :
    ∃ T : (Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] G E s → ℂ,
      ∀ Ψ ∈ schwartzBruhat HasLeftInv, T Ψ = thetaSmall W V' 𝔠 v' Ψ := by
  -- `Λ` is linear and is the theta integral on data of polynomial growth
  obtain ⟨Λ, hΛ⟩ := exists_linear_thetaIntegral W V' (rankTwist 𝔠.character n) (upsilonU1 ^ card b)
  let D : (Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] 𝒮 (W.hom V') :=
    IsLinearMap.mk' (fun Ψ ↦ localDatum W V' v' (fun y ↦ Ψ yᵀ) 𝔠.readsAt.star)
      ⟨by simp [localDatum, ← add_def], by simp [localDatum, ← Pi.smul_def, -smul_eq_mul]⟩
  refine ⟨Λ ∘ₗ D, fun Ψ hΨ ↦ ?_⟩
  have h_bdd : IsTargetBounded W V' (localDatum W V' v' (fun y ↦ Ψ yᵀ) 𝔠.readsAt.star) :=
    𝔠.readsAt.star.isTargetBounded hv' hΨ.transpose_mem_schwartzBruhat
  rw [thetaSmall, ← hΛ h_bdd, LinearMap.comp_apply, IsLinearMap.mk'_apply]

/-- Let `rk W = rk V' + rk V` be even and `v` have all moments finite. Let `ν` be the character of
`𝔠`, `S` its ramified places, and let `thetaLarge W V 𝔠 v Φ` be the theta integral over `[U(V)]` of
the datum `v` at the infinite places and `Φ` at `S`, as a function on `U(W)`. A same-section pair
`(Φ, Ψ)` for `χ t = ν (t / t̄) |t| ^ (rk W / 2)` consists of Schwartz–Bruhat functions on `a × n`
and `n × b` matrices at `S` whose coset sums `localSection χ` at complementary blocks of each
invertible `k` differ by the factor `χ (det k)`. On these pairs `thetaLarge Φ` is a linear function
of `Ψ`. -/
lemma exists_linear_thetaLarge (σ : b ⊕ a ≃ n) (hn : 2 ∣ card n) {v : PairFock E s t}
    (hv : IsSchwartzVector v) :
    ∃ T : (Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] G E s → ℂ,
      ∀ (Φ : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ)
        (Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ),
        (Φ, Ψ) ∈ sameSectionPairs (localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange (card n)) σ →
          T Ψ = thetaLarge W V 𝔠 v Φ := by
  let ρ : AutChar E := rankTwist 𝔠.character⁻¹ n
  -- `Λ` is linear and is the theta integral on data of polynomial growth
  obtain ⟨Λ, hΛ⟩ := exists_linear_thetaIntegral W V ρ ρ
  let D : (Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] 𝒮 (W.hom V) :=
    IsLinearMap.mk' (localDatum W V v · 𝔠.readsAt)
      ⟨by simp [localDatum, ← add_def], by simp [localDatum, ← Pi.smul_def, -smul_eq_mul]⟩
  -- the theta integral does not see the action of `U(V)` on the datum
  have h_invariant (g : GL a (LocProd 𝔠.ramifiedPlaces))
      (Φ : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ)
      (hΦ : Φ ∈ schwartzBruhat fun x ↦ HasLeftInv xᵀ) :
      localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange (card n) g.val.det • Λ
        (D fun x ↦ Φ (g.val * x)) = Λ (D Φ) := by
    obtain ⟨k, hk, rfl⟩ := 𝔠.exists_atPlaces_eq g
    have h_bdd : IsTargetBounded W V (D Φ) := 𝔠.readsAt.isTargetBounded hv hΦ
    have h_move : pairWeil W V ρ ρ ((1, 1), 1, k⁻¹) (D Φ) =
        localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange (card n)
          (atPlaces 𝔠.ramifiedPlaces k).val.det •
          D fun x ↦ Φ ((atPlaces 𝔠.ramifiedPlaces k).val * x) :=
            pairWeil_inv_localDatum W V 𝔠 hn v hΦ hk
    ext x
    rw [← map_smul, ← h_move, hΛ h_bdd, Prod.mk_one_one,
      hΛ (h_bdd.pairWeil_one_left ρ ρ (1, k⁻¹)), thetaIntegral_pairWeil, mul_one]
  -- so `Λ (D Φ) = T Ψ` on same-section pairs, for a linear `T`
  obtain ⟨T, hT⟩ := sameSectionPairs.exists_linear_factor _ σ (Λ ∘ₗ D) h_invariant
  refine ⟨T, fun Φ Ψ hp ↦ (hT Φ Ψ hp).trans (hΛ ?_)⟩
  obtain ⟨⟨h_sb, -⟩, -⟩ := hp
  exact 𝔠.readsAt.isTargetBounded hv h_sb

/-- Let `𝔠` be a split tame character, with character `ν` of the norm-one ideles and finite set `S`
of ramified places, and let `υ` be the splitting Hecke character of the Weil data. Let
`rk W = rk V' + rk V` be even, `v`, `v'` real data with all moments finite, `c ∈ ℂ`. There are a
space `M` of functions on matrices at `S` and a linear map `𝒟` with (a) and (b). (a) `M` consists of
Schwartz–Bruhat functions and is stable under translation. `𝒟` maps `M` to automorphic functions on
`U(W)`. It is equivariant at `S` for the inverse of `υ ^ card b |·| ^ (card b / 2)` of the
determinant. It is invariant under the integral points elsewhere (`IsEquivariantLift`). (b) Let `Ψ`
be locally constant with a matched function `Φ`: both are supported on blocks of integral invertible
`k`, where their values differ by `𝔠.semilocalChar (det k)`, for the character
`𝔠.semilocalChar : t ↦ ν (t / t̄)` at `S`. Then `Ψ` lies in `M`, and
`𝒟 Ψ = thetaLarge Φ - c • thetaSmall Ψ`. -/
lemma exists_isEquivariantLift_eq_thetaLarge_sub_smul (σ : b ⊕ a ≃ n) (hn : 2 ∣ card n)
    {v : PairFock E s t}
    {v' : PairFock E s t'} (hv : IsSchwartzVector v) (hv' : IsSchwartzVector v') (c : ℂ) :
    ∃ (M : Submodule ℂ (Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ))
      (𝒟 : (Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] G E s → ℂ),
      -- (a) `𝒟` is an equivariant map from `M` to automorphic functions
      IsEquivariantLift 𝔠 W M 𝒟 ∧
      -- (b) on the second member of a pair of matched functions it is the difference of the two
      -- sides
      ∀ {Φ : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ}
        {Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ},
        IsLocallyConstant Ψ → AreMatched O σ 𝔠.semilocalChar Φ Ψ →
          Ψ ∈ M ∧ 𝒟 Ψ = thetaLarge W V 𝔠 v Φ - c • thetaSmall W V' 𝔠 v' Ψ := by
  -- Let `M` be the space of second members of same-section pairs `(Φ, Ψ)`. The theta integral of
  -- `Φ` for `V` depends only on `Ψ`, linearly; subtract `c` times the theta integral of `Ψ` for
  -- `V'`. The laws of `IsEquivariantLift` hold for each of the two integrals.
  let χ : MulChar (LocProd 𝔠.ramifiedPlaces) ℂ :=
    localChar 𝔠.ramifiedPlaces 𝔠.character.baseChange (card n)
  obtain ⟨T, hT⟩ := exists_linear_thetaLarge W V 𝔠 σ hn hv
  obtain ⟨T', hT'⟩ := exists_linear_thetaSmall W V' 𝔠 hv'
  have h_sb {Φ : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ}
    {Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ}
      (hp : (Φ, Ψ) ∈ sameSectionPairs χ σ) : (Φ ∈ schwartzBruhat fun x ↦ HasLeftInv xᵀ) ∧
        Ψ ∈ schwartzBruhat HasLeftInv := (Submodule.mem_inf.1 hp).1
  have h_diff {Φ : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ}
    {Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ}
      (hp : (Φ, Ψ) ∈ sameSectionPairs χ σ) :
      (T - c • T') Ψ = thetaLarge W V 𝔠 v Φ - c • thetaSmall W V' 𝔠 v' Ψ := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, hT Φ Ψ hp, hT' Ψ (h_sb hp).right]
  refine ⟨(sameSectionPairs χ σ).map (.snd ℂ _ _), T - c • T', ⟨?_, ?_, ?_, ?_⟩,
    fun {Φ Ψ} hΨ ⟨h_left, h_right, h_eq⟩ ↦ ?_⟩
  · rintro _ ⟨⟨Φ, Ψ⟩, hp, rfl⟩
    exact (h_sb hp).right
  · -- both theta integrals are automorphic
    rintro _ ⟨⟨Φ, Ψ⟩, hp, rfl⟩
    obtain ⟨h_cont, h_inv⟩ : IsAutFunction W (thetaLarge W V 𝔠 v Φ) :=
      (𝔠.readsAt.isTargetBounded hv (h_sb hp).left).isAutFunction_thetaIntegral
    obtain ⟨h_cont', h_inv'⟩ : IsAutFunction W (thetaSmall W V' 𝔠 v' Ψ) :=
      (𝔠.readsAt.star.isTargetBounded hv'
        (h_sb hp).right.transpose_mem_schwartzBruhat).isAutFunction_thetaIntegral
    rw [LinearMap.snd_apply, h_diff hp]
    exact ⟨by fun_prop, fun γ hγ x ↦ by simp [h_inv γ hγ x, h_inv' γ hγ x]⟩
  · -- the translate of a same-section pair by the inverse of the component of `g` at
    -- `𝔠.ramifiedPlaces` is again a same-section pair
    rintro _ ⟨⟨Φ, Ψ⟩, hp, rfl⟩ g hg
    have hq : (χ (atPlaces 𝔠.ramifiedPlaces g⁻¹).val.det • fun x ↦
      Φ (x * (atPlaces 𝔠.ramifiedPlaces g⁻¹).val),
        fun y ↦ Ψ ((atPlaces 𝔠.ramifiedPlaces g).val * y)) ∈ sameSectionPairs χ σ := by
      simpa only [map_inv (atPlaces 𝔠.ramifiedPlaces), inv_inv] using
        sameSectionPairs.translate_mem χ σ hp (atPlaces 𝔠.ramifiedPlaces g⁻¹)
    refine ⟨⟨_, hq, rfl⟩, fun x ↦ ?_⟩
    simp only [LinearMap.snd_apply, h_diff hp, h_diff hq, Pi.sub_apply, Pi.smul_apply]
    rw [thetaSmall_translate_mul W V' 𝔠 v' hg (h_sb hq).right,
      thetaLarge_translate_mul W V 𝔠 σ hn v hp hg, sub_div, smul_eq_mul, smul_eq_mul, mul_div_assoc]
  · rintro _ ⟨⟨Φ, Ψ⟩, hp, rfl⟩ k ⟨hk_int, hk_triv⟩ x
    simp only [LinearMap.snd_apply, h_diff hp, Pi.sub_apply, Pi.smul_apply]
    rw [thetaLarge_mul_of_mem_stdLevel W V 𝔠 v (h_sb hp).left hk_int hk_triv,
      thetaSmall_mul_of_mem_stdLevel W V' 𝔠 v' (h_sb hp).right hk_int hk_triv]
  · -- matched functions form a same-section pair: on integral units the factor `|·| ^ (n / 2)` of
    -- `χ` is `1`
    have h_char (k : GL n (LocProd 𝔠.ramifiedPlaces)) (hk : k ∈ intGL n O) :
      χ k.val.det = 𝔠.semilocalChar k.val.det := by
      obtain ⟨k, rfl⟩ := hk
      simp only [χ, ← val_det_apply, GeneralLinearGroup.map_det]
      simp [localChar_apply_of_isUnit]
    have h_match : (Φ, Ψ) ∈ sameSectionPairs χ σ :=
      AreMatched.mem_sameSectionPairs (𝔠.tameLocalChar _)
      ⟨h_left, h_right, fun k hk ↦ by rw [h_eq k hk, h_char k hk]⟩ hΨ
    exact ⟨⟨_, h_match, rfl⟩, h_diff h_match⟩

end New.Exchange
