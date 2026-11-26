import Lib.Weil.Construction.CanonicalTheta
import Lib.Weil.DualPair.WeilAction

/-!
# Weil representation of unitary pairs: finite action, sums, negation and change of point

This file studies the Weil representation `New.pairWeil` S T a b of a pair of unitary groups on
data on Hom(S,T). Here S and T are hermitian spaces of ranks n and n′, Hom(S,T) is the space of
n′ × n matrices, and θ denotes the theta functional. The file describes the action of finite points
on named data. It also describes the behaviour of the action and of θ when a space is split as a
sum, when the form of one space is negated, and when a point is moved.

## Main definitions and results

* `New.pairWeil_schrodingerOp_of_mem_supportedOn`: a pair supported on `A` and its conjugate
  (`New.Gf.supportedOn`) replaces `Ψ` by `Ψ (h⁻¹ · g)`, up to an explicit scalar.
* `New.pairWeil_schrodingerOp_of_mem`: an integral pair (`New.stdLevel`) moves `Ψ` and the vector
  together.
* `New.conj_weilMultiplier_of_eq_neg`, `New.exists_theta_negSource`: negation conjugates the
  multiplier and θ, up to a factor; `New.pairWeil_negSource`: it intertwines the actions of the pair
  once the characters are changed.

Notions from other files:
* `New.pairWeil`: The representation ω_{a,b}(g, h) = a(det h) b(det g)⁻¹ ω(`onHom` (g, h)); the
  scalar is `New.pairChar a b (g, h)`.
* `New.weilMultiplier`: Δ(g) = Δ_f(g_f) ∏_τ conj(det d_τ), with d_τ the block of g_τ on the negative
  coordinates.
* `New.Space.boxProd`: the product f₁ ⊠ f₂ of data on two blocks of coordinates.
* `New.Space.ϱ`, `New.Space.ω`, `New.Space.vacElem`: The Heisenberg operators, the Weil
  representation and the vacuum vector of the space of data `New.𝒮 V`.

## Relation to the literature

Known; see `Lib.Weil.DualPair.GaloisLaw` for sources.
-/

noncomputable section

namespace New

/-!
## Action of finite points of a pair on named data

The action `New.pairWeil S T a b` of a pair `(g, h)`, finite or integral at `A`, on named data. Let
`A` be a set of finite places disjoint from its conjugate. A Schwartz–Bruhat function `Ψ` above `A`
(`New.IsSchwartzBruhat`) names the operator `(S.hom T).schrodingerOp A Ψ` on the space of data of
Hom(S, T).

* `New.pairWeil_eq_smul_of_projOn_eq`, `New.SiegelWeil.projOn_pairWeil`: the action on vectors that
  are vacua above `A` (fixed by `New.Space.projOn`).
-/

section PairFinite

open NumberField Matrix GeneralLinearGroup Kronecker Unitary Fintype Gf G Space

section

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {s : n → ℤˣ} {s' : n' → ℤˣ} {A : Set (FinPlace E)}

/-! ### Supports, integrality and determinants -/

/-- For unitary `g`, the determinant on the conjugate of `A` is `x̄⁻¹`, with `x = detOn A g` the
idele equal to `det g` on `A` and to `1` elsewhere. -/
lemma Exchange.detOn_preimage_star (g : Gf E n) :
    detOn (star ⁻¹' A) g.val = star (detOn A g.val)⁻¹ := by
  ext <;> simp [detOn, cutGL, star_idem, ← det_conjTranspose, inv_eq_left_inv g.prop]

@[simp↓]
lemma onHom_snd_inv_mulVec {p : G E s × G E s'} (x : n' × n → 𝔸f E) :
    (G.onHom p).2⁻¹.val.val *ᵥ x = matrixToVec (p.2.2⁻¹.val.val * vecToMatrix x * p.1.2.val.val) :=
  kronecker_mulVec_eq_matrixToVec ..

@[simp]
lemma G.onHom_atPlace {p : G E s × G E s'} {w : FinPlace E} :
    ((onHom p).2.atPlace w).val = (p.2.2.atPlace w).val ⊗ₖ (p.1.2⁻¹.atPlace w).valᵀ := rfl

/-- If the finite parts of both members of a pair are supported on `A` and its conjugate, so is the
finite part of their image `x ↦ h x g⁻¹` under `G.onHom`. -/
@[simp↓]
lemma G.onHom_mem_supportedOn {A : Set (FinPlace E)} {p : G E s × G E s'}
    (hg : p.1.2 ∈ supportedOn n A) (hh : p.2.2 ∈ supportedOn n' A) :
    (onHom p).2 ∈ supportedOn (n' × n) A := by
  simp only [supportedOn, Subgroup.mem_iInf, MonoidHom.mem_ker] at hg hh ⊢
  exact fun w hw ↦ Units.ext (by simp [onHom_atPlace, hg w hw, hh w hw])

/-- If both members of a pair are integral at the place `w`, that is, lie in `localIntGL`, so is
their image under `G.onHom`. -/
@[simp]
lemma G.onHom_atPlace_mem {p : G E s × G E s'} {w : FinPlace E}
    (hg : p.1.2.atPlace w ∈ localIntGL n w) (hh : p.2.2.atPlace w ∈ localIntGL n' w) :
    (onHom p).2.atPlace w ∈ localIntGL (n' × n) w := by
  simp_all [mem_intGL, ← map_inv, ← Prod.snd_inv, mul_mem]

/-! ### Scalars and the finite multiplier -/

variable (n) in
/-- The scalar matrices, as a homomorphism from the finite adeles of norm one to `Gf E n`. -/
noncomputable def scalarFin : unitary (𝔸f E) →* Gf E n :=
  MonoidHom.codRestrict (MonoidHom.comp (GeneralLinearGroup.scalar n) Unitary.toUnits) (U 1)
    (by simp [star_mul_self_of_mem, U])

/-- Scalar finite points are central in the finite adelic unitary group. -/
lemma Seesaw.commute_scalarFin {ν : unitary (𝔸f E)} (g : Gf E n) : Commute (scalarFin n ν) g :=
  Subtype.ext (scalar_commute ..)

/-- Let `A` be disjoint from its conjugate. For `g` supported on `A` and its conjugate, the
determinant `detFin s g` of the adelic point `(1, g)` is `divStar x = x / x̄` with `x = detOn A g`,
the idele equal to `det g` on `A` and to `1` elsewhere. -/
lemma G.detFin_of_mem_supportedOn {A : Set (FinPlace E)} (hA : Set.IsConjDisjoint A) {g : Gf E n}
    (hg : g ∈ supportedOn n A) : detFin s g = divStar (detOn A g.val) := by
  -- `g` is `1` outside the disjoint sets `A` and `star ⁻¹' A`, so `det g` is a product of two parts
  have h_split :
      (det (s := s) (1, g)).val = (detOn A g.val).val * (detOn (star ⁻¹' A) g.val).val := by
    ext w
    · simp [↓det_fst]
    by_cases hw : w ∈ A
    · simp [↓det_atPlace, hw, show star w ∉ A from Set.disjoint_left.1 hA hw]
    by_cases hw_star : star w ∈ A
    · simp [↓det_atPlace, hw, hw_star]
    · simp [↓det_atPlace, hw, hw_star, mem_supportedOn.1 hg w hw hw_star]
  exact Subtype.ext (by rwa [Exchange.detOn_preimage_star] at h_split)

/-- The adelic point with trivial real part and scalar finite part `ν` has matrix `(1, ν)` times the
identity. -/
lemma G.adeleMatrix_scalarFin (ν : unitary (𝔸f E)) :
    adeleMatrix (s := s) (1, scalarFin n ν) = ((1, ν.val) : 𝔸 E) • 1 := by
  aesop (add simp [scalarFin, Matrix.one_apply])

/-- Take the pair of scalar finite points `ν` in `U(S)` and `ν'` in `U(T)`, with trivial archimedean
parts. `New.G.onHom` sends it to the scalar finite point `ν' / ν` on `Hom(S, T)`. -/
lemma G.onHom_scalarFin (ν ν' : unitary (𝔸f E)) :
    (onHom ((1, scalarFin n ν), 1, scalarFin n' ν') : G E (homSigns s s')) =
      (1, scalarFin (n' × n) (ν' / ν)) := by
  apply ext_adeleMatrix
  -- both sides are the scalar matrix `(1, ν' / ν) • 1`
  have h_inv : ((1, scalarFin n ν) : G E s)⁻¹ = (1, scalarFin n ν⁻¹) := by simp [← map_inv]
  rw [adeleMatrix_onHom, h_inv, adeleMatrix_scalarFin, adeleMatrix_scalarFin, adeleMatrix_scalarFin]
  simp [smul_kronecker, kronecker_smul, smul_smul, div_eq_mul_inv, mul_comm]

end

variable {E : Type*} [Field E] [CMType E] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {s : n → ℤˣ} {s' : n' → ℤˣ} {A : Set (FinPlace E)} [WeilData E] {S : Space E n s}
  {T : Space E n' s'} {a b : AutChar E}

/-- The finite multiplier `finMultiplier`, written Δ_f, of the image `G.onHom (g, 1)`, which acts on
Hom(S,T) by x ↦ x g⁻¹, is Δ_f(g_f⁻¹)^(n'), where n' is the rank of the second space. -/
lemma finMultiplier_onHom_left {g : G E s} :
    finMultiplier (G.onHom (s' := s') (g, 1)).2 = finMultiplier g.2⁻¹ ^ card n' := by
  -- `finMultiplier g` is `chiFin (det u)` for `u` saturating `g` or its transpose. If `u` saturates
  -- `g⁻¹`, then `1 ⊗ₖ u` saturates `1 ⊗ₖ g⁻¹`, the transpose of `onHom (g, 1)`, and
  -- `det (1 ⊗ₖ u) = det u ^ card n'`.
  let u : GL n (𝔸f E) := (saturatingElem g.2⁻¹.val).val
  let φ : Matrix n n (𝔸f E) →+* Matrix (n' × n) (n' × n) (𝔸f E) :=
    { toFun u := (1 : Matrix n' n' (𝔸f E)) ⊗ₖ u
      map_one' := one_kronecker_one
      map_mul' u v := by simp [← mul_kronecker_mul]
      map_zero' := kronecker_zero _
      map_add' := kronecker_add _ }
  let Φ : GL n (𝔸f E) →* GL (n' × n) (𝔸f E) := Units.map φ.toMonoidHom
  have h_sat : IsSaturating (Ô E).matrix (Φ g.2⁻¹.val) (Φ u) :=
    (saturatingElem g.2⁻¹.val).prop.map_of_le_comap φ fun x hx i ↦ by
      aesop (add simp Matrix.one_apply)
  have h_transpose : (G.onHom (s' := s') (g, 1)).2.val.val = (φ g.2⁻¹.val.val)ᵀ := by
    aesop (add simp [onHom_snd, Matrix.one_apply])
  have h_det : (Φ u).det = u.det ^ card n' := by simp [Φ, φ, Units.ext_iff, det_kronecker]
  rw [finMultiplier, h_sat.glMultiplier_transpose h_transpose, h_det, map_pow]
  rfl

/-- Let `f` be a vacuum above `A`, that is, fixed by the projection `projOn A`. An integral pair
`(g, h)` of finite points supported on `A` and its conjugate acts on `f` through `pairWeil` by the
scalar a(det h) · b(det g)⁻¹, where `detFin` is the determinant of a finite point. -/
lemma pairWeil_eq_smul_of_projOn_eq {g : Gf E n} {h : Gf E n'} {f : 𝒮 (S.hom T)}
    (A : Set (FinPlace E)) (hf : (S.hom T).projOn A f = f) (hg : g ∈ stdLevel E n ⊓ supportedOn n A)
    (hh : h ∈ stdLevel E n' ⊓ supportedOn n' A) :
    pairWeil S T a b (g, h) f = (a.val (detFin s' h) * (b.val (detFin s g))⁻¹).val • f := by
  -- `ω` of the image fixes `f`, as the image is integral and supported on `A` and `star A`
  rw [pairWeil_apply, onHom_fin,
    omega_eq_self_of_mem_stdLevel _ (onHom_mem_supportedOn hg.2 hh.2) hf
      (by simp_all [mem_stdLevel_iff])]
  simp

/-- If the finite part of the image `onHom p` is integral at the places of `A` (lies in
`localIntGL`), then `pairWeil S T a b p` maps a vector fixed by the projection `projOn A` onto vacua
above `A` to a vector that is again fixed by it. -/
lemma SiegelWeil.projOn_pairWeil {f : 𝒮 (S.hom T)} (hf : (S.hom T).projOn A f = f)
    (p : G E s × G E s') (hp : ∀ w ∈ A, (onHom p).2.atPlace w ∈ localIntGL (n' × n) w) :
    (S.hom T).projOn A (pairWeil S T a b p f) = pairWeil S T a b p f := by
  rw [pairWeil_apply, map_smul, ← omega_projOn _ hp, hf]

/-! ### The action on named data -/

/-- Let `A` be disjoint from its conjugate, `Ψ` a Schwartz–Bruhat function above `A`, and `g`, `h`
finite points supported on `A` and its conjugate. Let `pairWeil` be the representation
(g, h) ↦ a(det h) b(det g)⁻¹ ω(x ↦ hxg⁻¹) on 𝒮 of `S.hom T`, the space of n' × n matrices, and let
`schrodingerOp A Ψ` be the operator Ψ⊗ on that 𝒮. Then `pairWeil` at `(g, h)` applied to
`schrodingerOp A Ψ f` equals `schrodingerOp A Ψ' f`, with Ψ'(x) = Ψ(h⁻¹ x g), times the factor
`χ_S (det h) / χ_T (det g) * |det g| ^ (n' / 2) / |det h| ^ (n / 2)`. Here determinants are on `A`
(`detOn`), `ideleAbs` is the idele norm, `χ_S = a.spaceChar n` and `χ_T = b.spaceChar n'`, with
`a.spaceChar k` the base change of `a` times `υ⁻ᵏ`. -/
lemma pairWeil_schrodingerOp_of_mem_supportedOn (hA : A.IsConjDisjoint) {Ψ : (n' × n → 𝔸f E) → ℂ}
    [hΨ : IsSchwartzBruhat A Ψ] {g : Gf E n} {h : Gf E n'} (hg : g ∈ supportedOn n A)
    (hh : h ∈ supportedOn n' A) (f : 𝒮 (S.hom T)) :
    pairWeil S T a b (g, h) ((S.hom T).schrodingerOp A Ψ f) =
      ((a.spaceChar (card n)).val (detOn A h.val) / (b.spaceChar (card n')).val (detOn A g.val) *
          √(ideleAbs (detOn A g.val)) ^ card n' / √(ideleAbs (detOn A h.val)) ^ card n : ℂ) •
        (S.hom T).schrodingerOp A (fun x : n' × n → 𝔸f E ↦
          Ψ (matrixToVec (h⁻¹.val.val * vecToMatrix x * g.val.val))) f := by
  let u : Gf E (n' × n) := (onHom ((1, g), 1, h) : G E (homSigns s s')).2
  -- the matrix of `u` is the Kronecker product `h ⊗ₖ g⁻¹ᵀ`
  have h_det : detOn A u.val = detOn A h.val ^ card n / detOn A g.val ^ card n' :=
    eq_div_of_mul_eq' (by aesop (add simp [u, det_kronecker, det_ne_zero]))
  -- `a (det h)` and `b (det g)` are values of the base changes at `detOn A h` and `detOn A g`
  have h_scalar : pairChar (s := s) (s' := s') a b ((1, g), 1, h) *
        (starRingEnd ℂ) (chiAdelic (detOn A u.val)) =
      (a.spaceChar (card n)).val (detOn A h.val) / (b.spaceChar (card n')).val (detOn A g.val) *
        √(ideleAbs (detOn A g.val)) ^ card n' / √(ideleAbs (detOn A h.val)) ^ card n := by
    rw [h_det, map_div, map_pow, map_pow]
    simp [detFin_of_mem_supportedOn hA, AutChar.spaceChar, AutChar.baseChange_apply_coe_toFun, hg,
      hh,
      chiAdelic, mul_pow, field, ← Complex.inv_eq_conj, Circle.norm_coe]
  -- `ω u` moves `Ψ` to `Ψ (u⁻¹ ·)`, with the factor `conj (chiAdelic (detOn A u))`
  rw [pairWeil_apply, onHom_fin, omega_schrodingerOp_of_mem_supportedOn hA _
    (onHom_mem_supportedOn hg hh), smul_smul, h_scalar]
  simp only [onHom_snd_inv_mulVec]

/-- Let `A` be a set of finite places disjoint from its conjugate, `Φ` a Schwartz–Bruhat function of
finite adelic vectors above `A`, and Φ⊗ = `schrodingerOp A Φ` the operator on `𝒮 S` that is the
combination of Heisenberg operators whose coefficients have `schrodingerCombination` equal to Φ. If
`g` is an adelic unitary whose finite part `g_f` lies in GL_n(O_w) at every w ∈ A, then `ω g` sends
Φ⊗ f to (Φ ∘ g_f⁻¹)⊗ (ω g f) for every f. -/
lemma Space.omega_schrodingerOp_of_mem (hA : A.IsConjDisjoint) {Φ : (n → 𝔸f E) → ℂ}
    [IsSchwartzBruhat A Φ] {g : G E s} (hg : ∀ w ∈ A, g.2.atPlace w ∈ localIntGL n w) (f : 𝒮 S) :
    S.ω g (S.schrodingerOp A Φ f) = S.schrodingerOp A (fun x : n → 𝔸f E ↦ Φ (↑g.2⁻¹ *ᵥ x))
      (S.ω g f) := by
  classical
  -- By `omega_schrodingerOp` the datum moves by `g` and the vector becomes `ω g` of the name of the
  -- moved box function. As `g` is integral on `A`, it preserves the box and commutes with
  -- `projOn A`.
  have h_box : (fun x : n → 𝔸f E ↦ boxIndicator n A (g.2 *ᵥ x)) = boxIndicator n A :=
    funext fun x ↦ by simp [mulVec_mem_integralBox g.2 hg]
  rw [(omega_schrodingerOp hA S g f).2, h_box, schrodingerOp_boxIndicator hA, omega_projOn S hg,
    schrodingerOp_projOn]

/-- Let `A` be disjoint from its conjugate and `Ψ` Schwartz–Bruhat above `A`. For an integral pair
`(g, h)` (finite parts in `stdLevel`), `pairWeil` sends `schrodingerOp A Ψ f`, the vector named by
`Ψ` on `f`, to the vector named by `x ↦ Ψ (h⁻¹ x g)` on the image of `f` under `pairWeil`. -/
lemma pairWeil_schrodingerOp_of_mem (hA : A.IsConjDisjoint) {Ψ : (n' × n → 𝔸f E) → ℂ}
    [hΨ : IsSchwartzBruhat A Ψ] {g : G E s} {h : G E s'} (hg : g.2 ∈ stdLevel E n)
    (hh : h.2 ∈ stdLevel E n') (f : 𝒮 (S.hom T)) :
    pairWeil S T a b (g, h) ((S.hom T).schrodingerOp A Ψ f) =
      (S.hom T).schrodingerOp A (fun x : n' × n → 𝔸f E ↦
          Ψ (matrixToVec ((↑h.2⁻¹ : Matrix n' n' (𝔸f E)) * vecToMatrix x *
            (g.2 : Matrix n n (𝔸f E)))))
        (pairWeil S T a b (g, h) f) := by
  rw [pairWeil_apply, pairWeil_apply, map_smul,
    omega_schrodingerOp_of_mem hA fun w _ ↦ onHom_atPlace_mem (mem_stdLevel_iff.1 hg w)
      (mem_stdLevel_iff.1 hh w)]
  simp only [onHom_snd_inv_mulVec]

end PairFinite

/-!
## Pairs under sums of spaces, negation of a form and change of point

* `New.negSource`: the change of coordinates `x ↦ (1, u⁻¹) x` from Hom(S⁻,T) to Hom(S,T), with
  u ∈ Ô of norm −1 and S⁻ = `S.neg` the space with the negated form; `negSource.map` pulls data
  on Hom(S,T) back to data on Hom(S⁻,T).
* `New.theta_boxProd_target`, `New.theta_boxProd_source`: θ of a product f ⊠ f' of data is
  θ(f)θ(f').
-/

section PairSumNegation

open NumberField Matrix WeilData Space Equiv CoordChange Fintype G Fock ComplexConjugate Weil Int

variable {E : Type} [Field E] [CMType E] [WeilData E]
  {n n' n₁ n₂ : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n₁]
  [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] {s : n → ℤˣ} {s' : n' → ℤˣ} {s₁ : n₁ → ℤˣ}
  {s₂ : n₂ → ℤˣ} {e : n₁ ⊕ n₂ ≃ n} {S V : Space E n s} {V₁ : Space E n₁ s₁}
  {V₂ : Space E n₂ s₂} {T : Space E n' s'} (a b b' : AutChar E) {g : G E s} {g₁ : G E s₁}
  {g₂ : G E s₂}

omit [WeilData E] in
/-- A vector x on pairs of indices is a rational point of Hom(S,T) exactly when the matrix
x_T · x · x_S⁻¹ has rational entries, x_S = `S.x` and x_T = `T.x` being the points of S and T, their
matrices in GL(𝔸); the point of Hom(S,T) is x_T ⊗ (x_S⁻¹)ᵀ. -/
lemma Space.mem_ratVectors_hom {x : n' × n → 𝔸 E} :
    x ∈ (S.hom T).ratVectors ↔ T.x.val * vecToMatrix x * S.x⁻¹.val ∈ ratMatrices E n' n := by
  simp [mem_ratVectors_iff, hom, kronecker_mulVec_eq_matrixToVec, mem_ratVectors, mem_ratMatrices,
    matrixToVec]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n₁] [DecidableEq n₁]
  [Fintype n₂] [DecidableEq n₂] in
/-- Let the bijection `e : n₁ ⊕ n₂ ≃ n` split the signs `s` into `s₁` and `s₂`. Then the induced
bijection `n₁ × n' ⊕ n₂ × n' ≃ n × n'` splits the signs `homSigns s' s` into `homSigns s' s₁` and
`homSigns s' s₂`. -/
lemma homSigns_sum_target (hs : s ∘ e = s₁ ⊕ᵥ s₂) :
    homSigns s' s ∘ (sumProdDistrib n₁ n₂ n').symm.trans (e.prodCongr (Equiv.refl n')) =
      homSigns s' s₁ ⊕ᵥ homSigns s' s₂ := by
  ext (⟨i, j⟩ | ⟨i, j⟩) : 1
  · simpa [pairSign] using congrFun hs (Sum.inl i)
  · simpa [pairSign] using congrFun hs (Sum.inr i)

omit [Fintype n'] [DecidableEq n'] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] in
/-- The signs of Hom(V₁ ⊕ V₂, T), for signs `s₁`, `s₂` and `s'` of V₁, V₂ and T, split into those of
Hom(V₁, T) and Hom(V₂, T). -/
lemma homSigns_sum_source :
    homSigns (s₁ ⊕ᵥ s₂) s' ∘ (prodSumDistrib n' n₁ n₂).symm = homSigns s₁ s' ⊕ᵥ homSigns s₂ s' := by
  ext (⟨i, j⟩ | ⟨i, j⟩) <;> rfl

/-! ### Sums -/

section Sums

variable (T)

/-- Let e split the coordinates of V compatibly with the signs (s ∘ e = s₁ ⊕ s₂). Suppose the point
of V, meaning its matrix x in GL_n(𝔸) with xᴴJx = diag(s) at the infinite places and 1 at the finite
places, becomes block diagonal when reindexed along e, with blocks the points of V₁ and V₂. Then for
data f on Hom(T,V₁) and f' on Hom(T,V₂), θ on Hom(T,V) of the product f ⊠ f' is θ(f)θ(f'); the
product is taken along the splitting of the coordinates of Hom(T,V) induced by e, which keeps the
signs by `New.homSigns_sum_target`. -/
lemma theta_boxProd_target (hs : s ∘ e = s₁ ⊕ᵥ s₂) (T : Space E n' s')
    (h_block : V.x.val.submatrix e e = fromBlocks V₁.x 0 0 V₂.x)
    (f : 𝒮 (T.hom V₁)) (f' : 𝒮 (T.hom V₂)) :
    (T.hom V).θ (boxProd (homSigns_sum_target hs) f f') = (T.hom V₁).θ f * (T.hom V₂).θ f' :=
  -- The point of `Hom(T, V)` is block diagonal, as the point of `V` is.
  theta_boxProd _ (by simp_all [Space.hom, ← ext_iff]) f f'

/-- For data f on Hom(V₁,T) and f' on Hom(V₂,T), θ on Hom(V₁ ⊕ V₂, T) of the product f ⊠ f' is
θ(f)θ(f'). The product is taken along the splitting `New.homSigns_sum_source` of the coordinates. It
is induced by the identity of the index set n₁ ⊕ n₂ of V₁ ⊕ V₂. -/
lemma theta_boxProd_source (f : 𝒮 (V₁.hom T)) (f' : 𝒮 (V₂.hom T)) :
    ((V₁.sum V₂).hom T).θ (boxProd homSigns_sum_source f f') = (V₁.hom T).θ f * (V₂.hom T).θ f' :=
  theta_boxProd _ (by simp [Space.hom, Space.sum, blockGL, ← ext_iff]) f f'

/-- On Hom(V₁ ⊕ V₂, T), the block diagonal element with blocks g₁ and g₂ acts on a product f ⊠ f'
factor by factor: ω_{bb',a}(g,h)(f ⊠ f') = ω_{b,a}(g₁,h)f ⊠ ω_{b',a}(g₂,h)f' for data f, f' on
Hom(V₁,T), Hom(V₂,T). -/
lemma pairWeil_boxProd_source (h : G E s') (f : 𝒮 (V₁.hom T)) (f' : 𝒮 (V₂.hom T)) :
    pairWeil (V₁.sum V₂) T (b * b') a (G.sum (g₁, g₂), h) (boxProd homSigns_sum_source f f') =
      boxProd homSigns_sum_source (pairWeil V₁ T b a (g₁, h) f)
        (pairWeil V₂ T b' a (g₂, h) f') := by
  -- The determinant of a block matrix splits the scalar factor; `omega_boxProd` splits the action.
  have det_eq : (G.sum (g₁, g₂)).det = g₁.det * g₂.det := by simp [Subtype.ext_iff]
  have h_ω : ((V₁.sum V₂).hom T).ω (onHom (G.sum (g₁, g₂), h)) (boxProd homSigns_sum_source f f') =
      boxProd homSigns_sum_source ((V₁.hom T).ω (onHom (g₁, h)) f)
        ((V₂.hom T).ω (onHom (g₂, h)) f') :=
    omega_boxProd _ (by simp_all [adeleMatrix_inv, stdForm, ← ext_iff]) f f'
  simp [pairWeil_apply, det_eq, h_ω]
  module

/-- Let e split the coordinates of V compatibly with the signs, and let g be block diagonal along e
with blocks g₁, g₂. Then on Hom(T,V), ω_{a,bb'}(h,g)(f ⊠ f') = ω_{a,b}(h,g₁)f ⊠ ω_{a,b'}(h,g₂)f' for
data f, f' on Hom(T,V₁), Hom(T,V₂). -/
lemma pairWeil_boxProd_target (hs : s ∘ e = s₁ ⊕ᵥ s₂) (T : Space E n' s') (a b b' : AutChar E)
    (h_block : g.adeleMatrix.submatrix e e = fromBlocks g₁.adeleMatrix 0 0 g₂.adeleMatrix)
    (h : G E s') (f : 𝒮 (T.hom V₁)) (f' : 𝒮 (T.hom V₂)) :
    pairWeil T V a (b * b') (h, g) (boxProd (homSigns_sum_target hs) f f') =
      boxProd (homSigns_sum_target hs) (pairWeil T V₁ a b (h, g₁) f)
        (pairWeil T V₂ a b' (h, g₂) f') := by
  -- The determinant of a block matrix splits the scalar factor; `omega_boxProd` splits the action.
  have det_eq : g.det = g₁.det * g₂.det := by
    simpa [Subtype.ext_iff] using congrArg Matrix.det h_block
  have h_omega : (T.hom V).ω (G.onHom (h, g)) (boxProd (homSigns_sum_target hs) f f') =
      boxProd (homSigns_sum_target hs) ((T.hom V₁).ω (G.onHom (h, g₁)) f)
        ((T.hom V₂).ω (G.onHom (h, g₂)) f') :=
    omega_boxProd _ (by simp_all [← ext_iff]) f f'
  simp [pairWeil_apply, det_eq, h_omega]
  module

end Sums

/-! ### Negation of the source -/

lemma normNegOne_inv : normNegOne⁻¹.val.val = -star (normNegOne.val.val : 𝔸f E) := rfl

/-- The negation change of coordinates from Hom(S⁻,T) to Hom(S,T): x ↦ (1, u⁻¹)x, u the chosen
element of Ô of norm −1. It conjugates the bicharacter β of the Heisenberg group, so it induces an
antilinear map `negSource.map` from data on Hom(S,T) to data on Hom(S⁻,T). -/
noncomputable def negSource : CoordChange E conj (homSigns s s') (homSigns (-s) s') where
  φ := ContinuousAddEquiv.mk' (Homeomorph.smul (normNegOneIdele E)⁻¹) (by simp)
  realEquiv := ContinuousAddEquiv.refl (InfinitePlace E × n' × n → ℂ)
  finEquiv := ContinuousAddEquiv.mk' (Homeomorph.smul (normNegOne (E := E))⁻¹) (by simp)
  apply_adelicSum := by
    simp [adelicSum, Units.smul_def, Subring.smul_def, normNegOneIdele, mul_left_comm,
      ContinuousAddEquiv.mk', funext_iff]
  beta_realEquiv := by
    simp [↓Heisenberg.conj_beta, realHeisenberg, dotProduct, signMatrix, neg_add_eq_sub, pairSign,
      mulVec_diagonal]
  vac_realEquiv := by simp
  selfDualAddChar_finEquiv := by
    simp [dotProduct, Units.smul_def, Subring.smul_def, normNegOne_inv, mul_left_comm, mul_assoc,
      mul_comm normNegOne.val.val, ContinuousAddEquiv.mk', ← Complex.inv_eq_conj,
      ← AddChar.map_neg_eq_inv]
  dot_finEquiv := by
    simp [dotProduct, Units.smul_def, Subring.smul_def, normNegOne_inv, mul_left_comm, mul_assoc,
      mul_comm normNegOne.val.val, ContinuousAddEquiv.mk']
  finEquiv_mem := by
    simp [stdLattice, intVectors, mem_Ô, Units.smul_def, Subring.smul_def, isUnit_Ô.1,
      ContinuousAddEquiv.mk']

omit [WeilData E] in
lemma G.neg_snd : g.neg.2 = g.2 := by
  -- Comparing matrix entries, rather than `rfl`, keeps the kernel from unfolding the groups.
  refine Subtype.ext (Units.ext (Matrix.ext fun i j ↦ ?_))
  rw [← adeleMatrix_snd, adeleMatrix_neg, adeleMatrix_snd]

/-- If g and g₁ lie in the adelic unitary groups of opposite signs s = −t and have the same
matrix, then the complex conjugate of Δ(g₁) is υ(det g₁) Δ(g), where Δ = `weilMultiplier` and υ is
the splitting character restricted to norm one ideles (`upsilonU1`). -/
lemma conj_weilMultiplier_of_eq_neg {g : G E s} {t : n → ℤˣ} {g₁ : G E t} (hs : s = -t)
    (h_mat : g.adeleMatrix = g₁.adeleMatrix) :
    conj (weilMultiplier g₁) = upsilonU1.val g₁.det * weilMultiplier g := by
  subst hs
  obtain rfl : g = g₁.neg := ext_adeleMatrix (h_mat.trans g₁.adeleMatrix_neg.symm)
  -- Split `upsilonU1 (det g₁)` into the determinants at the infinite places, which have modulus
  -- one, and the value of `υ` at the finite part. In the three `simp` calls below,
  -- `-implicitDefEqProofs` keeps the kernel from unfolding the groups.
  have υ_split : (upsilonU1.val g₁.det : ℂ) =
      (∏ w : InfinitePlace E, (g₁.1 w).val.val.det) * υ.val (finIdeleIncl g₁.2.val.det) := by
    -- `det g₁` has the valuations of its finite part, and modulus one at the infinite places
    rw [upsilonU1_apply, upsilon_eq_prod_mul_of_v_eq g₁.2.val.det
      (by simp -implicitDefEqProofs [-coe_det])]
    simp -implicitDefEqProofs [-coe_det]
  -- Negation exchanges the positive and the negative block, and at an infinite place the negative
  -- minor is `det` times the conjugate of the positive one. It keeps the finite part.
  have h_real (w : InfinitePlace E) :
      conj (realMultiplier (g₁.1 w)) = (g₁.1 w).val.val.det * realMultiplier (g₁.neg.1 w) := by
    simp -implicitDefEqProofs [G.neg, MulEquiv.prodCongr, ← units_ne_iff_eq_neg, realMultiplier,
      U.principalMinor_compl]
  have h_fin :
      conj (finMultiplier g₁.2) = υ.val (finIdeleIncl g₁.2.val.det) * finMultiplier g₁.neg.2 := by
    rw [G.neg_snd, upsilon_mul_finMultiplier]
  rw [weilMultiplier, weilMultiplier, map_mul, map_prod, υ_split, h_fin,
    Finset.prod_congr rfl fun w _ ↦ h_real w, Finset.prod_mul_distrib]
  ring

omit [WeilData E] in
@[simp]
lemma G.det_neg : g.neg.det = g.det := by simp [Subtype.ext_iff]

/-- Let S⁻ = `S.neg` be the space with signs −s and matrix −J. Let `negSource.map` be the antilinear
map from data on Hom(S,T) to data on Hom(S⁻,T) induced by the change of coordinates x ↦ (1, u⁻¹)x,
with u in Ô of norm −1. This map carries ω_{a,b}(g,h) f to ω_{a⁻¹υ^n, b⁻¹υ^(n')}(g⁻,h) applied to
the image of f; these are the characters that belong to the inverse splitting characters. Here υ is
`New.WeilData.upsilonU1`, g⁻ = `New.G.neg` g is the element of signs −s with the same matrix as g,
and n, n' are the ranks of S and T. -/
lemma pairWeil_negSource (h : G E s') (f : 𝒮 (S.hom T)) :
    pairWeil S.neg T (a⁻¹ * upsilonU1 ^ card n) (b⁻¹ * upsilonU1 ^ card n') (g.neg, h)
        (negSource.map f) =
      negSource.map (pairWeil S T a b (g, h) f) := by
  -- `negSource` is a scalar map, so it intertwines the two actions on vectors, hence on data up to
  -- the ratio of the multipliers (`CoordChange.map_omega`), which `conj_weilMultiplier_of_eq_neg`
  -- computes.
  have h_signs : homSigns (-s) s' = -homSigns s s' := by simp [funext_iff, pairSign]
  have h_mat : (onHom (g.neg, h)).adeleMatrix = (onHom (g, h)).adeleMatrix := by simp [← map_inv]
  have ω_eq : negSource.map ((S.hom T).ω (onHom (g, h)) f) =
      (upsilonU1.val (onHom (g, h)).det : ℂ) •
        (S.neg.hom T).ω (onHom (g.neg, h)) (negSource.map f) :=
    negSource.map_omega (by simp [negSource, h_mat, ContinuousAddEquiv.mk', mulVec_smul])
      (conj_weilMultiplier_of_eq_neg h_signs h_mat) f
  -- `det (onHom (g, h)) = det h ^ n * (det g)⁻¹ ^ n'`, so the powers of `upsilonU1` in the new
  -- characters give the factor in `ω_eq`; conjugation inverts the values of `a` and `b`.
  have h_char : conj (pairChar a b (g, h)) * (upsilonU1.val (onHom (g, h)).det : ℂ) =
      pairChar (a⁻¹ * upsilonU1 ^ card n) (b⁻¹ * upsilonU1 ^ card n') (g.neg, h) := by
    simp [det_onHom, Circle.norm_coe, ← Complex.inv_eq_conj, field]
  rw [pairWeil_apply, pairWeil_apply, map_smulₛₗ, ω_eq, smul_smul, h_char]

variable (S T)

/-- There is a complex number `c` of modulus one such that, for every datum `f` on `Hom(S, T)`, the
theta functional `θ` of `Hom(S⁻, T)` (with `S⁻ = S.neg`) at `c • negSource.map f` is the complex
conjugate of `θ f` for `Hom(S, T)`. Here `negSource.map` is the antilinear map from data on
`Hom(S, T)` to data on `Hom(S⁻, T)` induced by the change of coordinates x ↦ (1, u⁻¹)x, where u is
the chosen element of Ô of norm −1. -/
lemma exists_theta_negSource :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ∀ f : 𝒮 (S.hom T), (S.neg.hom T).θ (c • negSource.map f) = conj ((S.hom T).θ f) := by
  -- `negSource` matches the rational points of the two spaces, so `θ f = c * conj (θ (map f))`
  -- with `‖c‖ = 1` (`CoordChange.exists_theta_omega_map` with `g = 1`).
  have h_rat (x : n' × n → 𝔸 E) (hx : (negSource (s := s) (s' := s')).φ x ∈ (S.hom T).ratVectors) :
      (1 : G E (homSigns (-s) s')) • x ∈ (S.neg.hom T).ratVectors := by
    simp [Space.neg, mem_ratVectors_hom] at hx ⊢
    rwa [← smul_mul, ← T.x.1.mul_smul]
  obtain ⟨c, hc, hθ⟩ := negSource.exists_theta_omega_map (S.hom T) (S.neg.hom T) 1 h_rat
  exact ⟨conj c, by simpa using hc, fun f ↦ by simp [hθ f]⟩

/-! ### Change of point -/

open Kronecker in
/-- Change of point for a pair. If the points of `S` and `T` are moved by `γ` and `γ'`, the theta
kernel for the characters `a` (of `det h`) and `b` (of `det g⁻¹`) at `(g, h)` becomes
`b (det γ) a (det γ')⁻¹` times the old kernel at `(γ g, γ' h)`. -/
lemma Space.pairTheta_move (S : Space E n s) (T : Space E n' s') (a b : AutChar E) (γ g : G E s)
    (γ' h : G E s') (f : 𝒮 (S.hom T)) :
    pairTheta (S.move γ) (T.move γ') a b f (g, h) =
      b.val γ.det * (a.val γ'.det : ℂ)⁻¹ * pairTheta S T a b f (γ * g, γ' * h) := by
  -- The point of the moved space is that of `Hom(S, T)` times `x ↦ γ' x γ⁻¹`. The two spaces have
  -- the same space of data, so `f` may be read on either.
  have h_point : (T.x.val * γ'.adeleMatrix) ⊗ₖ (γ⁻¹.adeleMatrix * S.x⁻¹.val)ᵀ =
      T.x.val ⊗ₖ S.x⁻¹.valᵀ * (G.onHom (γ, γ')).adeleMatrix := by
    rw [G.adeleMatrix_onHom, ← mul_kronecker_mul, transpose_mul]
  have h_hom : (S.move γ).hom (T.move γ') = (S.hom T).move (G.onHom (γ, γ')) := by
    simpa only [hom, move, Space.mk.injEq, true_and] using Units.ext h_point
  have h_theta (f' : 𝒮 (S.hom T)) : ((S.move γ).hom (T.move γ')).θ f' =
      (S.hom T).θ ((S.hom T).ω (G.onHom (γ, γ')) f') :=
    (congrArg (fun V : Space E (n' × n) (homSigns s s') ↦ V.θ f') h_hom).trans (theta_move ..)
  have h_char : pairChar a b (g, h) =
      b.val γ.det * (a.val γ'.det : ℂ)⁻¹ * pairChar a b (γ * g, γ' * h) := by simp [field]
  calc pairTheta (S.move γ) (T.move γ') a b f (g, h)
      = (S.hom T).θ ((S.hom T).ω (G.onHom (γ, γ')) (pairWeil S T a b (g, h) f)) := h_theta _
    _ = pairChar a b (g, h) * (S.hom T).θ ((S.hom T).ω (G.onHom (γ * g, γ' * h)) f) := by
        rw [pairWeil_apply, map_smul, map_smul, rep_apply_apply, ← map_mul, Prod.mk_mul_mk,
          smul_eq_mul]
    _ = b.val γ.det * (a.val γ'.det : ℂ)⁻¹ * pairTheta S T a b f (γ * g, γ' * h) := by
        rw [h_char, pairTheta, pairWeil_apply, map_smul, smul_eq_mul, mul_assoc]

end PairSumNegation

end New

end
