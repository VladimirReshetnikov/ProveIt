import Lib.Weil.MixedModel.NamedData

/-!
# Hom(S,T), the Weil representation and theta kernel of a pair, and data modulo an ideal

For hermitian spaces `S`, `T` (`New.Space`) of ranks `n`, `n'`, the `n' × n` matrices form a space
`Hom(S, T)`. The pair `(g, h)` acts on it by `x ↦ h x g⁻¹`. The Weil representation `New.Space.ω` of
that space restricts to the pair. Theta kernels are also built from a polynomial at the real places
and a function modulo an ideal at the finite places.

## Main definitions and results

* `New.Space.hom`, `New.G.onHom`: the space `Hom(S, T)` and the map `U(S) × U(T) → U(Hom(S, T))`.
* `New.pairWeil S T a b`: the representation of the pair, twisted by `a (det h) * b (det g)⁻¹`
  (`New.pairChar`), for characters `a, b` of `[U(1)]` (`New.AutChar`).
* `New.pairTheta`: the theta kernel, the theta functional `New.Space.θ` of
  `pairWeil S T a b (g, h) f`.
* `New.Modulus`: a non-zero ideal `𝔪` of `𝓞 E` such that no prime `w` divides it together with the
  complex conjugate of `w`; `New.Modulus.ResidueRing` is the finite ring `𝓞 E ⧸ 𝔪`,
  `New.Modulus.places` the set of primes dividing `𝔪` and `New.Modulus.reduction` a reduction map
  from `New.Ô E`.
* `New.modDatum`: the vector in the data space of `New.Space.hom S T` with real part `v`, with `Ψ`
  at the primes dividing `𝔪` (`New.Space.schrodingerOp`) and the vacuum elsewhere.
* `New.modKernel`: its theta kernel `New.pairTheta`, for `v` the Fock vector of a polynomial;
  `New.stdKernel`: this kernel for the standard characters `New.stdChar` of `S` and `T`.

Notions from other files:
* `New.Space`: a hermitian space over a CM field E with `CMType E` (a chosen embedding at each
  infinite place; it contains `NumberField E` and `IsCMField E`), with a point, given by a matrix J
  over E and x in GL_n(𝔸) with xᴴJx equal to diag(s), for a sign vector s, at the infinite places
  and 1 at the finite places; `𝒮 V` is the data space of such a space V, on which the Weil
  representation acts.
* `New.WeilData`: the fixed choices that the Weil representation needs, among them a splitting
  character `υ` of the ideles of E.
* `New.AutChar`: a continuous circle-valued character of U(1)(𝔸), the norm-one adeles of E, that is
  trivial on the elements coming from E.
* `New.Fock.polyVector`: the vector P(ζ(x)) exp(−|x|²/2) of the Fock space, for a polynomial P in
  the Fock coordinates ζ(x) of a real vector x.
* `New.Space.integrated`: the bilinear map (v, f) ↦ v ⊗ f = ∫ v(y) ϱ(y)f dy over real vectors y, for
  v in the Fock space and f in 𝒮(V), with ϱ the Heisenberg representation on 𝒮(V).

## Relation to the literature

Known; see `Lib.Weil.DualPair.ThetaLiftConvergence`, `Lib.Weil.MixedModel.ZeroTerm` and
`Lib.Adelic.Unitary.WeakApproximation` for sources.
-/

noncomputable section

namespace New

/-!
## The Weil representation and theta kernel of a pair of hermitian spaces

* `New.AutChar.spaceChar`: for a character `a` of `[U(1)]` and a rank `k`, the base change of `a`
  divided by the `k`-th power of the fixed splitting character `υ` of `New.WeilData`.
* `New.rankTwist`: the product of `a` with the `⌊n/2⌋`-th power of `υ` on norm-one ideles, for an
  index type of size `n`.
* `New.stdChar`: the standard character of a space, the power of `υ` on `[U(1)]` by the number
  of negative signs.
-/

section PairDefs

open Matrix Kronecker WeilData

variable {E : Type*} [Field E] [CMType E] [WeilData E]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {s : n → ℤˣ} {s' : n' → ℤˣ} (S : Space E n s) (T : Space E n' s') {m m' R : Type*}
  (a b : AutChar E)

/-! ### The space of homomorphisms -/

/-- For sign vectors s on n and s′ on n′, the sign vector on n′ × n given by the products
s′(i)s(j). -/
abbrev homSigns (s : n → ℤˣ) (s' : n' → ℤˣ) : n' × n → ℤˣ := pairSign 1 s' s

/-- A matrix x read as the function (i, j) ↦ x_{ij} on pairs (row, column). -/
def matrixToVec (x : Matrix m' m R) (p : m' × m) : R := x p.1 p.2

/-- A vector on pairs (row, column) as a matrix; inverse to `New.matrixToVec`. -/
def vecToMatrix (y : m' × m → R) : Matrix m' m R := of fun i j ↦ y (i, j)

section

variable {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]

omit [Fintype n] [Fintype n'] [NumberField.IsCMField E] in
/-- Over the adeles of the field E, let `stdForm E s` be the diagonal matrix that is diag(s) at the
infinite places and the identity at the finite ones. The standard form of the product signs on
n′ × n is the Kronecker product of that of s′ and the transpose of that of s. -/
@[simp]
lemma stdForm_homSigns : stdForm E (homSigns s s') = stdForm E s' ⊗ₖ (stdForm E s)ᵀ := by
  simp [stdForm, pairSign, diagonal_kronecker_diagonal, Pi.mul_def]

/-- The homomorphism from G(s) × G(s′) to the adelic unitary group of the product signs sending
(g, h) to x ↦ hxg⁻¹ on n′ × n matrices. -/
def G.onHom : G E s × G E s' →* G E (homSigns s s') :=
  toUnitary.symm.toMonoidHom.comp
    ((U.kroneckerHom stdForm_mul_self stdForm_homSigns).comp
      (toUnitary.toMonoidHom.prodMap toUnitary.toMonoidHom))

/-- The determinant, as a homomorphism from the adelic unitary group of signs s to the group of
adeles x of E with x x̄ = 1 (the determinant of the standard form is a unit). -/
def G.det : G E s →* unitary (𝔸 E) :=
  (U.det (isUnit_stdForm.map detMonoidHom)).comp (toUnitary : G E s ≃* U (stdForm E s)).toMonoidHom

/-- For g in the finite adelic unitary group, the determinant of the element (1, g) of G, as an
adele of norm one. -/
@[simp]
abbrev detFin (s : n → ℤˣ) (g : Gf E n) : unitary (𝔸 E) := G.det (s := s) (1, g)

end

/-- The space `Hom(S, T)` of `n' × n` matrices, indexed by pairs (row, column): its Gram matrix is
the Kronecker product `J_T ⊗ (J_S⁻¹)ᵀ`, its point is `x_T ⊗ (x_S⁻¹)ᵀ` (with inverse
`x_T⁻¹ ⊗ x_Sᵀ`), and the coordinate `(i, j)` has the sign `s' i * s j`. -/
@[simps -isSimp J]
def Space.hom : Space E (n' × n) (homSigns s s') where
  J := T.J ⊗ₖ S.J⁻¹ᵀ
  x :=
    { val := T.x ⊗ₖ S.x⁻¹.1ᵀ
      inv := ↑T.x⁻¹ ⊗ₖ S.xᵀ
      val_inv := by simp [← mul_kronecker_mul, ← transpose_mul]
      inv_val := by simp [← mul_kronecker_mul, ← transpose_mul] }
  -- The identity is the Kronecker product of `gram_point` for `T` with the inverse transpose of
  -- `gram_point` for `S`.
  gram_point := by
    simp [gram_point, map_J_inv, map_kronecker, conjTranspose_nonsing_inv, conjTranspose_kronecker,
      conjTranspose_transpose_eq_transpose_conjTranspose, transpose_map, ← mul_kronecker_mul,
      ← transpose_mul]

/-! ### Characters, the action of the pair and the theta kernel -/

/-- The restriction of υ to the norm-one ideles, as a character of U(1)(𝔸) trivial on the elements
coming from E. -/
def WeilData.upsilonU1 : AutChar E :=
  ⟨υ.1.comp ⟨Unitary.toUnits, Continuous.of_coeHom_comp (by fun_prop)⟩, fun _ hx ↦ υ.2 _ hx⟩

/-- For u in the norm-one adeles U(1)(𝔸) of the CM field E, the character `upsilonU1` takes the
value υ(u). Here υ is the splitting character contained in the Weil data on E, and u is viewed as an
idele. -/
lemma WeilData.upsilonU1_apply (u : unitary (𝔸 E)) :
    upsilonU1.val u = υ.val (Unitary.toUnits u) := rfl

/-- The Hecke character `x ↦ a (x / x̄) * υ x ^ (-k)` of `E`, for a character `a` of `[U(1)]` and a
natural number `k`: the base change `a.baseChange` divided by the `k`-th power of the splitting
character `υ`. It is the character attached to a space of rank `k` in a dual pair. -/
def AutChar.spaceChar (k : ℕ) : HeckeChar E := a.baseChange * υ⁻¹ ^ k

/-- For a character a of [U(1)] and a finite index set of size n, the character a·υ^⌊n/2⌋ of [U(1)],
where υ is restricted to the norm-one ideles (`upsilonU1`). -/
def rankTwist (n : Type*) [Fintype n] : AutChar E := a * upsilonU1 ^ (Fintype.card n / 2)

/-- The standard character of a space with signs s: the character υ^{n₋} of [U(1)], where υ is
restricted to the norm-one ideles (`upsilonU1`) and n₋ is the number of signs −1. Its Hecke
character `spaceChar` at the rank n₊ + n₋ of the space is υ^{−(n₊ − n₋)}, the power of υ by minus
the signature (`New.AutChar.spaceChar_stdChar`). -/
def stdChar {n : Type*} [Fintype n] (s : n → ℤˣ) : AutChar E := upsilonU1 ^ Exchange.negCount s

/-- The standard character of a sum of spaces is the product of their standard characters. -/
lemma stdChar_sum {n₁ n₂ : Type*} [Fintype n₁] [Fintype n₂] (s₁ : n₁ → ℤˣ) (s₂ : n₂ → ℤˣ) :
    (stdChar (s₁ ⊕ᵥ s₂) : AutChar E) = stdChar s₁ * stdChar s₂ := by
  simp [stdChar, Exchange.negCount_sumElim, pow_add]

/-- The standard character of the negated space is the inverse of the standard character times
υⁿ, where υ is restricted to the norm-one ideles (`upsilonU1`) and n is the rank: negation
exchanges the numbers of signs 1 and −1, which add up to n. -/
lemma stdChar_neg {n : Type*} [Fintype n] (s : n → ℤˣ) :
    (stdChar (-s) : AutChar E) = (stdChar s)⁻¹ * upsilonU1 ^ Fintype.card n := by
  rw [stdChar, stdChar, ← Exchange.negCount_neg_add s, add_comm, pow_add, inv_mul_cancel_left]

/-- For characters a, b of [U(1)], the complex character (g, h) ↦ a(det h) b(det g)⁻¹ of
G(s) × G(s′). -/
def pairChar : G E s × G E s' →* ℂ :=
  Circle.coeHom.comp ((b⁻¹.1.toMonoidHom.comp G.det).coprod (a.1.toMonoidHom.comp G.det))

/-- The representation (g, h) ↦ a(det h) b(det g)⁻¹ ω(x ↦ hxg⁻¹) of the product of the two adelic
unitary groups on the data space of Hom(S, T). -/
def pairWeil : G E s × G E s' →* 𝒮 (S.hom T) →L[ℂ] 𝒮 (S.hom T) where
  toFun p := pairChar a b p • (S.hom T).ω (G.onHom p)
  map_one' := by simp
  map_mul' := by simp [← smul_mul_smul]

/-- The theta kernel θ^{S,T}_{a,b}(f)(g, h) = θ(ω_{a,b}(g,h)f), for f in 𝒮(Hom(S,T)) and θ the
theta functional of Hom(S,T). -/
def pairTheta (f : 𝒮 (S.hom T)) (p : G E s × G E s') : ℂ := (S.hom T).θ (pairWeil S T a b p f)

end PairDefs

/-!
## Moduli prime to their conjugates and data modulo an ideal

* `New.Modulus.liftFn`: a function of vectors modulo `𝔪` read on finite adelic vectors.
-/

section ModulusKernel

open NumberField Ideal Space

section

variable (E : Type*) [Field E] [NumberField E] [IsCMField E]

/-- A modulus: a nonzero ideal of O_E prime to its complex conjugate, that is, no prime w divides
it together with its conjugate w̄. -/
structure Modulus where
  /-- The ideal `𝔪` of the ring of integers of `E`. -/
  ideal : Ideal (𝓞 E)
  /-- The ideal is not zero. -/
  ne_bot : ideal ≠ ⊥
  /-- No prime `w` divides the ideal together with its complex conjugate `star w`. -/
  not_le_star (w : FinPlace E) : ideal ≤ w → ¬ideal ≤ star w

variable {E} (𝔪 : Modulus E)

namespace Modulus

/-- The residue ring O_E/𝔪 of the modulus 𝔪. -/
abbrev ResidueRing : Type _ := 𝓞 E ⧸ 𝔪.ideal

/-- The residue ring of a modulus is finite, as the ideal is nonzero. -/
instance : Fintype 𝔪.ResidueRing :=
  haveI := finiteQuotientOfFreeOfNeBot 𝔪.ideal 𝔪.ne_bot
  Fintype.ofFinite _

instance : DecidableEq 𝔪.ResidueRing := Classical.decEq _

/-- The set of finite places of E that divide 𝔪. -/
def places : Set (FinPlace E) := {w : FinPlace E | 𝔪.ideal ≤ w}

/-- Only finitely many primes divide a modulus. -/
instance : Finite 𝔪.places := by
  simpa [places, dvd_iff_le] using (finite_factors 𝔪.ne_bot).to_subtype

/-- A chosen ring homomorphism Ô → O_E/𝔪, on the integral finite adeles Ô, extending reduction on
O_E, with kernel tÔ for an integral idele t equal to 1 off 𝔪. -/
def reduction : Ô E →+* 𝔪.ResidueRing := (exists_reduction_and_idele_generator 𝔪.ne_bot).choose

open scoped Classical in
/-- A function `Ψ` of vectors modulo `𝔪`, read on finite adelic vectors `x`. Multiplying by
`idem 𝔪.places` keeps the components at the primes dividing `𝔪` and sets the others to `0`. If the
result is integral, the value is `Ψ` of its reduction modulo `𝔪`; otherwise it is `0`. -/
@[simps -isSimp]
def liftFn {n : Type*} : ((n → 𝔪.ResidueRing) → ℂ) →ₗ[ℂ] (n → 𝔸f E) → ℂ where
  toFun Ψ x :=
    if h : ∀ i : n, idem 𝔪.places * x i ∈ Ô E then
      Ψ fun i ↦ 𝔪.reduction ⟨idem 𝔪.places * x i, h i⟩
    else 0
  map_add' Ψ Ψ' := by ext x; simp [dite_add_dite]
  map_smul' c Ψ := by ext x; simp [apply_dite (c * ·)]

end Modulus

end

variable {E : Type*} [Field E] [CMType E] [WeilData E] {n n' : Type} [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n'] {s : n → ℤˣ} {s' : n' → ℤˣ} (S : Space E n s) (T : Space E n' s')

/-- The datum v ⊗ Ψ ⊗ vac on Hom(S,T), for a vector v of the real Heisenberg model of Hom(S,T) and
a function Ψ on matrices modulo 𝔪: its real part is v, the lift of Ψ is put in at the places
dividing 𝔪 by `New.Space.schrodingerOp` (the operator attached to a function of finite adelic
vectors), and it is the vacuum elsewhere. -/
def modDatum (𝔪 : Modulus E) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (v : Heisenberg.IsVacuum.Model (Fock.realHeisenberg (realSigns E (homSigns s s')))) :
      𝒮 (S.hom T) :=
  (S.hom T).integrated v
    ((S.hom T).schrodingerOp (Modulus.places 𝔪) (𝔪.liftFn (Ψ ∘ vecToMatrix)) (S.hom T).vacElem)

/-- The theta kernel `(g, h) ↦ θ (ω_{a,b} (g, h) f)` on the product of the adelic unitary groups
of `S` and `T`, for the datum `f = modDatum S T 𝔪 Ψ v` given by a function `Ψ` on matrices modulo
`𝔪` and the Fock vector `v` of the polynomial `P`; `a` and `b` are the characters that twist
the action. -/
def modKernel (a b : AutChar E) (𝔪 : Modulus E) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) : G E s → G E s' → ℂ :=
  fun g h ↦
    pairTheta S T a b (modDatum S T 𝔪 Ψ (Fock.polyVector (realSigns E (homSigns s s')) P)) (g, h)

/-- The theta kernel θ^{S,T}[Ψ, P]: the kernel `New.modKernel` of a function Ψ on n′ × n matrices
modulo 𝔪 and a polynomial P, for the standard characters (`New.stdChar`) of S and T. -/
abbrev stdKernel (𝔪 : Modulus E) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) : G E s → G E s' → ℂ :=
  modKernel S T (stdChar s) (stdChar s') 𝔪 Ψ P

end ModulusKernel

end New

/-!
## Lifts of functions modulo an ideal and the primitive character

For a modulus `𝔪`, a function `Ψ` on `n → 𝔪.ResidueRing` has a lift `𝔪.liftFn Ψ` to finite adelic
vectors.

* `New.Modulus.isSchwartzBruhat_liftFn`: the lift is Schwartz–Bruhat above `𝔪.places`
  (`New.IsSchwartzBruhat`).
-/

namespace New.Modulus

open NumberField Finset RingHom MeasureTheory Ideal Quotient Function Space stdLattice

section

variable {E : Type _} [Field E] [NumberField E] [IsCMField E] {n : Type _} [Fintype n]
  [DecidableEq n] (𝔪 : Modulus E) (Ψ : (n → 𝔪.ResidueRing) → ℂ) (x : Ô E)

/-! ### Reduction modulo `𝔪` and the generator of its kernel -/

/-- The finite idele `t` generates the modulus `𝔪` in the integral finite adeles `Ô E`, and it is
`1` away from `𝔪`. -/
structure IsGenerator (𝔪 : Modulus E) (t : (𝔸f E)ˣ) : Prop where
  /-- The idele `t` is integral. -/
  mem : t.val ∈ Ô E
  /-- The component of `t` at a place not dividing `𝔪` is `1`. -/
  apply_of_notMem (w : FinPlace E) (hw : w ∉ 𝔪.places) : t.val w = 1
  /-- The kernel of `𝔪.reduction` consists of the multiples of `t` in `Ô E`. -/
  reduction_eq_zero_iff (x : Ô E) : 𝔪.reduction x = 0 ↔ t⁻¹.val * x ∈ Ô E
  /-- The order of `t` at every place `w` is the multiplicity of `w` in `𝔪`. -/
  valued_apply (w : FinPlace E) : Valued.v (t.val w) = .exp (-multiplicity w.asIdeal 𝔪.ideal)
  /-- For a finite adele `y`, `𝔪 y ⊆ Ô E` if and only if `t y ∈ Ô E`. -/
  forall_smul_mem_iff (y : 𝔸f E) : (∀ c ∈ 𝔪.ideal, c • y ∈ Ô E) ↔ t.val * y ∈ Ô E

/-- Every modulus `𝔪` is generated in `Ô E` by a finite idele that is `1` away from `𝔪`. -/
lemma exists_generator : ∃ t : (𝔸f E)ˣ, 𝔪.IsGenerator t := by
  obtain ⟨-, -, t, ⟨h_mem, h_one, h_ker⟩, h_order, h_smul⟩ :=
    (exists_reduction_and_idele_generator 𝔪.ne_bot).choose_spec
  exact ⟨t, h_mem, h_one, h_ker, h_order, h_smul⟩

/-- A finite idele `t` generating `𝔪` in `Ô E`, chosen from `exists_generator`. It is integral,
and equal to `1` at the places not dividing `𝔪`. The kernel of `𝔪.reduction` consists of the
multiples of `t` in `Ô E`. See `generator_mem`, `generator_apply_of_notMem`,
`reduction_eq_zero_iff_generator_inv_mul_mem` and `valued_generator`. -/
noncomputable def generator : (𝔸f E)ˣ := 𝔪.exists_generator.choose

lemma isGenerator_generator : 𝔪.IsGenerator 𝔪.generator := 𝔪.exists_generator.choose_spec

/-- The set of primes dividing a modulus is disjoint from its complex conjugate. -/
lemma isConjDisjoint_places : 𝔪.places.IsConjDisjoint :=
  Set.disjoint_left.2 𝔪.not_le_star

/-- On global integers, `𝔪.reduction` is the usual reduction `𝓞 E → 𝓞 E ⧸ 𝔪`. -/
@[simp]
lemma reduction_algebraMap (a : 𝓞 E) : 𝔪.reduction (algebraMap (𝓞 E) (Ô E) a) = a :=
  (exists_reduction_and_idele_generator 𝔪.ne_bot).choose_spec.left a

lemma reduction_surjective : Surjective 𝔪.reduction := by
  rintro ⟨a⟩
  exact ⟨algebraMap (𝓞 E) (Ô E) a, 𝔪.reduction_algebraMap a⟩

/-- For any a, b in O_E/𝔪 there is an idempotent e of O_E/𝔪 such that a and b both lie in the
principal ideal generated by (1 − e)a + eb; this is what `IsValuationPair` says for `⊤`. -/
lemma isValuationPair_residueRing : IsValuationPair (⊤ : Subring 𝔪.ResidueRing) := by
  refine 𝔪.reduction_surjective.forall₂.2 fun (a b : Ô E) ↦ ?_
  -- lift the pair to `Ô E` and reduce the idempotent `e` that patches it there; the spans in the
  -- conclusion become divisibility by `(1 - e) a + e b`
  obtain ⟨⟨e, he_mem⟩, he_idem, he_le⟩ := isValuationPair_Ô.top _ a b
  obtain ⟨ha, hb⟩ : a - e * (a - b) ∣ a ∧ a - e * (a - b) ∣ b := by simpa [dvd_def] using he_le
  refine ⟨⟨𝔪.reduction e, Subring.mem_top _⟩, by rw [← map_mul, he_idem], sup_le ?_ ?_⟩
  · simpa [dvd_def] using map_dvd 𝔪.reduction ha
  · simpa [dvd_def] using map_dvd 𝔪.reduction hb

lemma generator_mem : 𝔪.generator.val ∈ Ô E := 𝔪.isGenerator_generator.mem

lemma generator_apply_of_notMem {w : FinPlace E} (hw : w ∉ 𝔪.places) : 𝔪.generator.val w = 1 :=
  𝔪.isGenerator_generator.apply_of_notMem w hw

lemma reduction_eq_zero_iff_generator_inv_mul_mem (x : Ô E) :
    𝔪.reduction x = 0 ↔ 𝔪.generator⁻¹.val * x ∈ Ô E :=
  𝔪.isGenerator_generator.reduction_eq_zero_iff x

/-- The idele `t = 𝔪.generator` is integral, has component `1` at every place not dividing `𝔪`,
and an element `x` of `Ô E` reduces to `0` modulo `𝔪` exactly when `t⁻¹ x` is integral. -/
lemma generator_spec :
    𝔪.generator.val ∈ Ô E ∧ (∀ w : FinPlace E, w ∉ 𝔪.places → 𝔪.generator.val w = 1) ∧
    ∀ x : Ô E, 𝔪.reduction x = 0 ↔ 𝔪.generator⁻¹.val * x ∈ Ô E :=
  ⟨𝔪.generator_mem, fun _ ↦ 𝔪.generator_apply_of_notMem,
    𝔪.reduction_eq_zero_iff_generator_inv_mul_mem⟩

/-- The idele `t = 𝔪.generator` has order equal to the multiplicity of `w` in `𝔪` at every finite
place `w`. -/
lemma valued_generator (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) :
    Valued.v (𝔪.generator.val w) = .exp (-multiplicity w.asIdeal 𝔪.ideal) :=
  𝔪.isGenerator_generator.valued_apply w

/-- An element of `Ô E` reduces to `0` modulo `𝔪` exactly when it lies in the ideal of `Ô E`
generated by `𝔪`. -/
lemma reduction_eq_zero_iff {z : Ô E} :
    𝔪.reduction z = 0 ↔ z ∈ 𝔪.ideal.map (algebraMap (𝓞 E) (Ô E)) :=
  (exists_reduction_and_idele_generator 𝔪.ne_bot).choose_spec.right.left

/-- Two elements of `Ô E` with the same components at the primes dividing `𝔪` have the same
reduction modulo `𝔪`. -/
lemma reduction_congr {x y : Ô E} (hxy : ∀ w : FinPlace E, w ∈ 𝔪.places → x.val w = y.val w) :
    𝔪.reduction x = 𝔪.reduction y := by
  -- `x - y` vanishes on `𝔪.places` and `𝔪.generator` is `1` elsewhere, so `𝔪.generator` divides
  -- `x - y` in `Ô E`.
  have h_eq : (x - y : 𝔸f E) = 𝔪.generator * (idem 𝔪.placesᶜ * (x - y : 𝔸f E)) := by
    ext w
    by_cases hw : w ∈ 𝔪.places <;> simp [hw, hxy, generator_apply_of_notMem]
  rw [← sub_eq_zero, ← map_sub, reduction_eq_zero_iff_generator_inv_mul_mem,
    AddSubgroupClass.coe_sub, h_eq, Units.inv_mul_cancel_left]
  exact mul_mem (idem_mem_Ô _) (sub_mem x.2 y.2)

/-- Setting the components outside the primes dividing `𝔪` to `0` does not change the reduction
modulo `𝔪`. -/
lemma reduction_idem_mul :
    𝔪.reduction (⟨idem 𝔪.places, idem_mem_Ô 𝔪.places⟩ * x) = 𝔪.reduction x :=
  𝔪.reduction_congr fun w hw ↦ by simp [hw]

/-! ### Lifting functions modulo `𝔪` -/

section

omit [DecidableEq n]

/-- The lift of the constant function `1` is the indicator of the vectors that are integral at the
primes dividing `𝔪`. -/
lemma liftFn_one : 𝔪.liftFn 1 = boxIndicator n 𝔪.places := by
  ext x
  rw [liftFn_apply, boxIndicator_apply]
  split_ifs <;> simp_all [mem_integralBox]

/-- For an integral vector `x₀`, the lift `𝔪.liftFn` of the point mass at its class is the
indicator `cosetIndicator` of the vectors `x` such that `t⁻¹ (x - x₀)` is integral at the primes
dividing `𝔪`, where `t = 𝔪.generator`. -/
lemma liftFn_single (x₀ : n → Ô E) :
    𝔪.liftFn (Pi.single (𝔪.reduction ∘ x₀) 1) =
      cosetIndicator 𝔪.places 𝔪.generator fun i : n ↦ x₀ i := by
  classical
  ext x
  by_cases hx : ∀ i : n, idem 𝔪.places * x i ∈ Ô E
  · -- If `x` is integral on `𝔪.places`, the two sides agree since the kernel of `𝔪.reduction` is
    -- `𝔪.generator Ô`.
    have h_iff (i : n) :
        𝔪.reduction ⟨idem 𝔪.places * x i, hx i⟩ = 𝔪.reduction (x₀ i) ↔
          idem 𝔪.places * (𝔪.generator⁻¹.val * (x i - x₀ i)) ∈ Ô E := by
      rw [← 𝔪.reduction_idem_mul (x₀ i), ← sub_eq_zero, ← map_sub,
        reduction_eq_zero_iff_generator_inv_mul_mem, mul_left_comm, mul_sub]
      rfl
    simp [liftFn_apply, hx, Pi.single_apply, funext_iff, h_iff, mem_integralBox]
  · -- Otherwise both sides vanish: if `t⁻¹ (x - x₀)` were integral on `𝔪.places`, so would be
    -- `x = t (t⁻¹ (x - x₀)) + x₀`.
    have h_not_mem : 𝔪.generator⁻¹.val • (x - fun i : n ↦ (x₀ i : 𝔸f E)) ∉
        integralBox n 𝔪.places := by
      refine fun h_mem ↦ hx fun i ↦ ?_
      have h_eq : idem 𝔪.places * x i =
          𝔪.generator.val * (idem 𝔪.places * (𝔪.generator⁻¹.val * (x i - x₀ i))) +
            idem 𝔪.places * x₀ i := by
        linear_combination -idem 𝔪.places * 𝔪.generator.mul_inv_cancel_left (x i - x₀ i)
      rw [h_eq]
      exact add_mem (mul_mem 𝔪.generator_mem (mem_integralBox.1 h_mem i))
        (mul_mem (idem_mem_Ô _) (x₀ i).property)
    rw [liftFn_apply, dite_eq_right hx, cosetIndicator, boxIndicator_apply, ite_eq_right h_not_mem]

/-- Translating a function modulo `𝔪` by the class of an integral vector `z` translates its lift
by `z`. -/
lemma liftFn_reduction_add (F : (n → 𝔪.ResidueRing) → ℂ) (z : n → Ô E) (x : n → 𝔸f E) :
    𝔪.liftFn (fun v : n → 𝔪.ResidueRing ↦ F (𝔪.reduction ∘ z + v)) x =
      𝔪.liftFn F ((fun i : n ↦ (z i : 𝔸f E)) + x) := by
  have hz (i : n) : idem 𝔪.places * (z i : 𝔸f E) ∈ Ô E := mul_mem (idem_mem_Ô _) (z i).property
  by_cases hx : ∀ i : n, idem 𝔪.places * x i ∈ Ô E
  · have h_sum (i : n) : idem 𝔪.places * ((z i : 𝔸f E) + x i) ∈ Ô E := by
      simpa only [mul_add] using add_mem (hz i) (hx i)
    have h_red (i : n) : 𝔪.reduction ⟨idem 𝔪.places * ((z i : 𝔸f E) + x i), h_sum i⟩ =
        𝔪.reduction (z i) + 𝔪.reduction ⟨idem 𝔪.places * x i, hx i⟩ := by
      rw [← 𝔪.reduction_idem_mul (z i), ← map_add]
      exact congrArg 𝔪.reduction (Subtype.ext (mul_add ..))
    simp [liftFn_apply, hx, h_sum, h_red, Pi.add_def]
  · -- `z + x` is integral on `𝔪.places` exactly when `x` is, so both sides vanish.
    simp [liftFn_apply, hx, mul_add, add_mem_cancel_left, hz]

end

/-- Let `f` and `g` be ring homomorphisms to `S` from `𝓞 E ⧸ 𝔪` and from `Ô E`. If they agree on
every global integer, then `f (𝔪.reduction x) = g x` for every `x` in `Ô E`. -/
lemma apply_reduction_eq_of_algebraMap {S : Type*} [CommRing S] {f : 𝔪.ResidueRing →+* S}
    {g : Ô E →+* S} (h_agree : ∀ a : 𝓞 E, f a = g (algebraMap (𝓞 E) (Ô E) a)) :
    f (𝔪.reduction x) = g x := by
  -- `x` is congruent to a global integer modulo a nonzero `d` in `𝔪`, and both maps kill `d`
  obtain ⟨d, hd_mem, hd₀⟩ := 𝔪.ideal.ne_bot_iff.1 𝔪.ne_bot
  obtain ⟨a, c, hc⟩ : ∃ (a : 𝓞 E) (c : Ô E),
      algebraMap (𝓞 E) (Ô E) a - x = algebraMap (𝓞 E) (Ô E) d * c :=
    exists_dvd_algebraMap_sub hd₀ x
  have hfd : f (d : 𝔪.ResidueRing) = 0 := by simp [eq_zero_iff_mem.2 hd_mem]
  rw [← sub_eq_iff_comm.1 hc]
  simp [← h_agree, hfd]

/-- If `𝔪` divides `𝔫`, reduction modulo `𝔫` followed by `𝔫.ResidueRing → 𝔪.ResidueRing` is
reduction modulo `𝔪`. -/
@[simp]
lemma factor_reduction {𝔫 : Modulus E} (h_le : 𝔫.ideal ≤ 𝔪.ideal) :
    factor h_le (reduction 𝔫 x) = 𝔪.reduction x :=
  𝔫.apply_reduction_eq_of_algebraMap x fun a ↦ by rw [factor_mk, reduction_algebraMap]

end

variable {E : Type _} [Field E] [CMType E] {n : Type _} [Fintype n] [DecidableEq n] (𝔪 : Modulus E)
  (Ψ : (n → 𝔪.ResidueRing) → ℂ) (x : Ô E) [WeilData E]

open scoped Classical in
/-- The lift of any function Ψ on (O_E/𝔪)^n to finite adelic vectors is Schwartz–Bruhat on the
places dividing 𝔪: it depends only on the components at these places, it is locally constant, and
those components stay in a compact set on its support. -/
instance isSchwartzBruhat_liftFn : IsSchwartzBruhat 𝔪.places (𝔪.liftFn Ψ) where
  idem_smul := by simp [← mul_assoc, idem_mul_self, mem_Ô, liftFn_apply]
  locally_constant := by
    -- `Ψ` is a combination of point masses, and these lift to coset functions.
    rw [pi_eq_sum_univ' Ψ, map_sum]
    refine sum_induction _ _ IsLocallyConstant.add (.const 0) fun y _ ↦ ?_
    obtain ⟨x₀, rfl⟩ := 𝔪.reduction_surjective.comp_left y
    rw [map_smul, liftFn_single]
    exact (IsSchwartzBruhat.locally_constant 𝔪.places).comp (Ψ (𝔪.reduction ∘ x₀) * ·)
  compact_support := by
    -- The lift vanishes off the box, so the compact set of the box indicator serves.
    obtain ⟨C, hC_compact, hC_mem⟩ :=
      (isSchwartzBruhat_boxIndicator (n := n) (S := 𝔪.places)).compact_support
    refine ⟨C, hC_compact, fun x hx ↦ hC_mem x ?_⟩
    obtain ⟨hx_int, -⟩ := by simpa [liftFn_apply] using hx
    simp [mem_integralBox, hx_int]

/-- For a modulus `𝔪` (a nonzero ideal of O_E prime to its conjugate), `𝔪.liftFn Ψ` reads a function
`Ψ` of vectors modulo `𝔪` on finite adelic vectors `x`: it keeps the components of `x` at the primes
dividing `𝔪`, and takes `Ψ` of the reduction if the result is integral and `0` otherwise. The
theorem says that `localInner 𝔪.places` of two such lifts is the mean of `conj (Ψ y) * Ψ' y` over
all vectors `y` modulo `𝔪`. Here `localInner 𝔪.places` is `∫ conj(Φ) Φ'` over the finite adelic
vectors integral off `𝔪.places`, for the Haar measure giving `Ô^n` mass one. -/
lemma localInner_liftFn (Ψ' : (n → 𝔪.ResidueRing) → ℂ) :
    localInner 𝔪.places (𝔪.liftFn Ψ) (𝔪.liftFn Ψ') =
      star Ψ ⬝ᵥ Ψ' / Fintype.card (n → 𝔪.ResidueRing) := by
  classical
  -- With `F = star Ψ * Ψ'` the left side is the integral of the lift of `F`. Average this integral
  -- over the translates of `F`, whose sum is the constant `∑ y, F y`.
  let F : (n → 𝔪.ResidueRing) → ℂ := star Ψ * Ψ'
  let μ : Measure (n → 𝔸f E) := (latticeMeasure E n).restrict (integralBox n 𝔪.placesᶜ)
  have h_inner : localInner 𝔪.places (𝔪.liftFn Ψ) (𝔪.liftFn Ψ') = ∫ x, 𝔪.liftFn F x ∂μ := by
    simp +contextual [localInner, F, μ, liftFn_apply]
  -- every `y` comes from an integral vector, and the integral is invariant under those
  have h_transl (y : n → 𝔪.ResidueRing) :
      ∫ x, 𝔪.liftFn (fun z ↦ F (y + z)) x ∂μ = ∫ x, 𝔪.liftFn F x ∂μ := by
    obtain ⟨z, rfl⟩ := 𝔪.reduction_surjective.comp_left y
    have h_mem : (fun i : n ↦ (z i : 𝔸f E)) ∈ integralBox n 𝔪.placesᶜ := by
      simp [mem_integralBox, mul_mem]
    simp only [𝔪.liftFn_reduction_add F z]
    exact setIntegral_add_left_eq_self_of_mem (𝔪.liftFn F) h_mem
  have h_integrable (y : n → 𝔪.ResidueRing) : Integrable (𝔪.liftFn fun z ↦ F (y + z)) μ := by
    simpa [IntegrableOn, μ] using
      (isSchwartzBruhat_liftFn 𝔪 _).integrableOn_mul (continuous_const (y := 1))
  have h_avg : boxIndicator n 𝔪.places.conjClosure 0 * ∑ y : n → 𝔪.ResidueRing, F y =
      Fintype.card (n → 𝔪.ResidueRing) • ∫ x, 𝔪.liftFn F x ∂μ :=
    calc _
      -- Fourier transform at `0`: the integrand is `∑ y, F y` times the indicator of the box
      _ = ∫ x, ∑ y, 𝔪.liftFn (fun z ↦ F (y + z)) x ∂μ := by
        refine (fourier_boxIndicator 0 0 _ fun x ↦ ?_).symm
        simp [(AddGroup.addRight_bijective _).sum_comp, mem_integralBox, liftFn_apply]
      _ = ∑ y, ∫ x, 𝔪.liftFn (fun z ↦ F (y + z)) x ∂μ :=
        integral_finsetSum _ fun y _ ↦ h_integrable y
      _ = _ := sum_eq_card_nsmul fun y _ ↦ h_transl y
  rw [h_inner, eq_div_iff (by simp), mul_comm, ← nsmul_eq_mul, ← h_avg]
  simp [F, dotProduct, boxIndicator]

/-! ### The primitive character modulo `𝔪` -/

/-- Let 𝔪 be a modulus of the CM field E, where E carries Weil data. There is a primitive additive
character ψ′ of the residue ring `𝔪.ResidueRing` = O_E/𝔪 with ψ′(x mod 𝔪) = ψ₀(t⁻¹x) for all `x` in
`Ô E`. Here `t = 𝔪.generator` is the chosen finite idele generating 𝔪 in `Ô E`, and ψ₀ is the
character `selfDualAddChar E` of the finite adeles, z ↦ ψ_f(ȷαᾱz), built from the Weil data, for
which `Ô E` is self-dual. -/
lemma exists_isPrimitive_addChar :
    ∃ ψ' : AddChar 𝔪.ResidueRing ℂ, ψ'.IsPrimitive ∧
      ∀ x : Ô E, ψ' (𝔪.reduction x) = selfDualAddChar E (𝔪.generator⁻¹.val * x) :=
  exists_primitive_residue_addChar
    ⟨𝔪.reduction_surjective, 𝔪.reduction_eq_zero_iff_generator_inv_mul_mem⟩
    forall_selfDualAddChar_mul_eq_one_iff

/-- The character ψ′ of `𝔪.ResidueRing` with ψ′(x mod 𝔪) = ψ₀(t⁻¹x) for `x` in `Ô E`, where
`t = 𝔪.generator` (`New.Modulus.primAddChar_reduction`). It is primitive
(`New.Modulus.isPrimitive_primAddChar`) because `Ô E` is self-dual for ψ₀
(`forall_selfDualAddChar_mul_eq_one_iff`). -/
noncomputable def primAddChar : AddChar 𝔪.ResidueRing ℂ := 𝔪.exists_isPrimitive_addChar.choose

/-- For a modulus 𝔪 of the CM field E with Weil data, the character ψ′ = `𝔪.primAddChar` of O_E/𝔪
satisfies ψ′(x mod 𝔪) = ψ₀(t⁻¹x) for `x` in `Ô E`. Here `t = 𝔪.generator` is the chosen finite idele
generating 𝔪 in `Ô E`, and ψ₀ = `selfDualAddChar E` is the character z ↦ ψ_f(ȷαᾱz) of the finite
adeles given by the Weil data. -/
@[simp]
lemma primAddChar_reduction :
    𝔪.primAddChar (𝔪.reduction x) = selfDualAddChar E (𝔪.generator⁻¹ * x) :=
  𝔪.exists_isPrimitive_addChar.choose_spec.right x

/-- The additive character ψ′ = `New.Modulus.primAddChar` of O_E/𝔪 is primitive: for every nonzero a
in O_E/𝔪, the character x ↦ ψ′(ax) is nontrivial. -/
lemma isPrimitive_primAddChar : 𝔪.primAddChar.IsPrimitive :=
  𝔪.exists_isPrimitive_addChar.choose_spec.left

/-- Let `V` be a space, `f` a vector of `𝒮 V` and `y` a finite adelic vector. Translate the mean
`V.projOn 𝔪.places f` of `f` over integral translations by the part of `y` above the conjugates of
the primes dividing `𝔪`, using the Heisenberg operator `V.ϱ`. The result is `V.schrodingerOp`
applied to `f` with the function x ↦ ψ₀(y* x)·1(x). Here ψ₀ is `selfDualAddChar E` and 1
(`boxIndicator`) is the indicator of the vectors integral at every prime dividing `𝔪`. Only the part
`idem 𝔪.places • x` of `x` above those primes enters. -/
lemma rho_star_idem_smul_projOn {s : n → ℤˣ} (V : Space E n s) (f : 𝒮 V) (y : n → 𝔸f E) :
    V.ϱ (finVec (star (idem 𝔪.places) • y)) (V.projOn 𝔪.places f) =
      V.schrodingerOp 𝔪.places
        (fun x : n → 𝔸f E ↦ selfDualAddChar E (star y ⬝ᵥ idem 𝔪.places • x) *
          boxIndicator n 𝔪.places x) f := by
  -- the vector is supported on the conjugate places, which lie in `𝔪.places.conjClosure`
  have h_idem : star (idem 𝔪.places) = idem 𝔪.places.conjClosure * star (idem 𝔪.places) := by
    rw [idem_conjClosure_eq_add_star 𝔪.isConjDisjoint_places, add_mul,
      idem_mul_star 𝔪.isConjDisjoint_places, zero_add, ← star_mul', idem_mul_self]
  calc _ = V.ϱ (finVec (idem 𝔪.places.conjClosure • star (idem 𝔪.places) • y))
          (V.projOn 𝔪.places f) := by rw [← mul_smul, ← h_idem]
    _ = V.schrodingerOp 𝔪.places
          (schrodingerAct 𝔪.places (star (idem 𝔪.places) • y) (boxIndicator n 𝔪.places)) f :=
        (V.schrodingerOp_schrodingerAct_boxIndicator 𝔪.isConjDisjoint_places _ f).symm
    _ = _ := by rw [IsSchwartzBruhat.schrodingerAct_star_idem_smul 𝔪.isConjDisjoint_places]

/-- Let `u` be an integral vector, and let `Ψ x = ψ′(x ⬝ᵥ (u mod 𝔪))`, where ψ′(x mod 𝔪) = ψ₀(t⁻¹x)
is `𝔪.primAddChar` and `t = 𝔪.generator`. Then the operator `V.schrodingerOp` on 𝒮(V) attached to
the lift `𝔪.liftFn Ψ` sends `f` to `V.ϱ` applied to `V.projOn 𝔪.places f`. Here `V.ϱ` is taken at
the adelic vector with zero real part and finite part α times the conjugate of the part of `t⁻¹ u`
at the primes dividing `𝔪`. The map `𝔪.liftFn Ψ` is `Ψ` of the reduction of the part at those primes
when integral and `0` otherwise, and `projOn` is the mean of the finite Heisenberg operators over
integral vectors supported at the primes dividing `𝔪` and their conjugates. -/
lemma schrodingerOp_char_eq_translate_projOn {s : n → ℤˣ} (V : Space E n s) {f : 𝒮 V}
    (u : n → Ô E) :
    V.schrodingerOp 𝔪.places (𝔪.liftFn fun x : n → 𝔪.ResidueRing ↦
      𝔪.primAddChar (x ⬝ᵥ 𝔪.reduction ∘ u)) f =
      V.ϱ (finVec (star (idem 𝔪.places • 𝔪.generator⁻¹.val • (↑) ∘ u))) (V.projOn 𝔪.places f) := by
  -- the lift of the character is an adelic character times the box function
  have h_lift : (𝔪.liftFn fun x ↦ 𝔪.primAddChar (x ⬝ᵥ 𝔪.reduction ∘ u)) =
      fun x : n → 𝔸f E ↦ selfDualAddChar E ((𝔪.generator⁻¹.val • (↑) ∘ u) ⬝ᵥ idem 𝔪.places • x) *
        boxIndicator n 𝔪.places x := by
    ext x
    by_cases hx : ∀ i : n, idem 𝔪.places * x i ∈ Ô E
    · have h_dot : (fun i : n ↦ 𝔪.reduction ⟨idem 𝔪.places * x i, hx i⟩) ⬝ᵥ 𝔪.reduction ∘ u =
          𝔪.reduction (∑ i : n, ⟨idem 𝔪.places * x i, hx i⟩ * u i) := by
        simp [dotProduct]
      have h_arg : 𝔪.generator⁻¹.val * ↑(∑ i : n, (⟨idem 𝔪.places * x i, hx i⟩ * u i : Ô E)) =
          (𝔪.generator⁻¹.val • (↑) ∘ u : n → 𝔸f E) ⬝ᵥ idem 𝔪.places • x := by
        simp [dotProduct, mul_sum, mul_assoc, mul_comm, mul_left_comm]
      rw [liftFn_apply, dite_eq_left hx, h_dot, primAddChar_reduction, h_arg, boxIndicator_apply,
        ite_eq_left (mem_integralBox.2 hx), mul_one]
    · simp [liftFn_apply, hx, mem_integralBox]
  -- a translation above the conjugate places multiplies the box function by the character
  rw [h_lift, star_smul, 𝔪.rho_star_idem_smul_projOn V, star_star]

/-- The operator named by the indicator of a class `a` modulo `𝔪` is a weighted mean of translates.
Choose for every class `b` of vectors modulo `𝔪` an integral vector `u b` in it, and let `y b` be
the conjugate of the part of `t⁻¹ u b` at the places dividing `𝔪`, where `t = 𝔪.generator`. Then the
operator `V.schrodingerOp` attached to the lift of the point mass at `a` sends `f` to the mean over
`b` of `ψ′(-a ⬝ b)` times the translate of `V.projOn 𝔪.places f` by the finite Heisenberg operator
`V.finHeisenbergOp (y b)`, which equals `V.ϱ (finVec (y b))` because `y b` has norm zero. Here ψ′ is
`New.Modulus.primAddChar`, and `V.projOn 𝔪.places f` is the mean of `f` over integral translations
at those places and their conjugates. -/
lemma schrodingerOp_single_eq_mean_translate_projOn {s : n → ℤˣ} (V : Space E n s) (f : 𝒮 V)
    (a : n → 𝔪.ResidueRing) {u : (n → 𝔪.ResidueRing) → n → Ô E}
    (hu : ∀ b : n → 𝔪.ResidueRing, 𝔪.reduction ∘ u b = b) :
    V.schrodingerOp 𝔪.places (𝔪.liftFn (Pi.single a 1)) f =
      ∑ b : n → 𝔪.ResidueRing, (Fintype.card (n → 𝔪.ResidueRing) : ℂ)⁻¹ • 𝔪.primAddChar (-a ⬝ᵥ b) •
        V.finHeisenbergOp (star (idem 𝔪.places • 𝔪.generator⁻¹.val • (↑) ∘ u b))
          (V.projOn 𝔪.places f) := by
  -- Fourier inversion writes the point mass as a mean of characters, and each character names a
  -- translate (`schrodingerOp_char_eq_translate_projOn`).
  have h_inv : (Pi.single a 1 : (n → 𝔪.ResidueRing) → ℂ) =
      ∑ b : n → 𝔪.ResidueRing, (Fintype.card (n → 𝔪.ResidueRing) : ℂ)⁻¹ • 𝔪.primAddChar (-a ⬝ᵥ b) •
        fun y : n → 𝔪.ResidueRing ↦ 𝔪.primAddChar (y ⬝ᵥ b) := by
    ext y
    simp [← Finset.mul_sum, ← AddChar.map_add_eq_mul, neg_add_eq_sub, ← sub_dotProduct,
      sum_addChar_dotProduct 𝔪.isPrimitive_primAddChar, sub_eq_zero, Pi.single_apply]
  -- A vector supported at the places conjugate to those of `𝔪` has norm zero.
  have h_norm (w : n → 𝔸f E) :
      star (star (idem 𝔪.places • w)) ⬝ᵥ star (idem 𝔪.places • w) = 0 := by
    rw [star_star, star_smul, smul_dotProduct, dotProduct_smul, smul_smul,
      idem_mul_star 𝔪.isConjDisjoint_places, zero_smul]
  have h_term (b : n → 𝔪.ResidueRing) :
      V.schrodingerOp 𝔪.places (𝔪.liftFn fun y ↦ 𝔪.primAddChar (y ⬝ᵥ b)) f =
        V.finHeisenbergOp (star (idem 𝔪.places • 𝔪.generator⁻¹.val • (↑) ∘ u b))
          (V.projOn 𝔪.places f) := by
    rw [V.finHeisenbergOp_eq_rho_of_dotProduct_self_eq_zero (h_norm _),
      ← 𝔪.schrodingerOp_char_eq_translate_projOn V (u b), hu b]
  simp only [h_inv, map_smul, map_sum, _root_.smul_apply,
    _root_.sum_apply, h_term]

end New.Modulus

/-!
## Kronecker products of rational matrices in the coordinates of Hom(V,T)

`New.Space.hom_point_inv_mul_kronecker` reads a Kronecker product A ⊗ Bᵀ of rational matrices in the
adelic coordinates of Hom(V,T): it is (x_T⁻¹A) ⊗ (Bx_V)ᵀ, x_V and x_T being the points of V and T.
-/

section PairRationalMaps

open Matrix Kronecker

namespace New.Space

variable {E : Type*} [Field E] [CMType E]

/-- Let `E` be a CM number field with a chosen embedding at each infinite place (`CMType E` contains
`NumberField E` and `IsCMField E`), and `V`, `T` hermitian spaces over `E` with points x_V, x_T
(the adelic matrices `V.x`, `T.x`). For matrices A, B over E, read adelically by `toAdele`, the
inverse of the point of Hom(V,T) times A ⊗ Bᵀ is (x_T⁻¹A) ⊗ (Bx_V)ᵀ. -/
lemma hom_point_inv_mul_kronecker {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] {s : n → ℤˣ} {s' : n' → ℤˣ} {V : Space E n s} (T : Space E n' s')
    {m m' : Type*} (A : Matrix n' m' E) (B : Matrix m n E) :
    (V.hom T).x⁻¹.val * (A ⊗ₖ Bᵀ).map toAdele =
      (T.x⁻¹.val * A.map toAdele) ⊗ₖ (B.map toAdele * V.x.val)ᵀ := by
  simp [hom, map_kronecker, transpose_map, ← mul_kronecker_mul]

variable {n : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ} {V : Space E n s}

/-- The Gram matrix of a hermitian space is invertible. -/
noncomputable instance : Invertible V.J := V.isUnit_J.invertible

end New.Space

end PairRationalMaps

end
