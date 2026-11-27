import Lib.General.NumberTheory.ImaginaryQuadraticField
import Lib.Shimura.Uniformisation.AdelicFrames
import Lib.Weil.Unramified.HeckeGL

/-!
# Hecke elements in group rings, marked triples, local terms and neat levels

Hecke operators for a group `G` with a subgroup `K` are realised inside the group ring `k[G]`, so
they act on every representation of `G` without convolution. With this, the file sets up the data
for counting fixed points of Hecke correspondences for a CM field `E` over K₀ = ℚ(√-d₀). A rigidity
result for frames then shows that the objects counted have no automorphisms at deep level: levels
inside a large place are neat.

## Main definitions and results

* `New.Variety.fixedToEigen`: the elements that send `K`-fixed vectors to eigenvectors of a
  subgroup, in every representation.
* `New.Variety.MarkedTriple`, `New.Variety.countTerm`: triples (coset, rational matrix, mark) and
  the term that an orbit of triples contributes; `New.Variety.IsRegularHecke`: only separable
  matrices contribute.
* `New.Variety.IsSafe`, `New.Variety.invHeckeIsogeny`, `New.Variety.heckeSum`: the safe split places
  and the Hecke elements that appear in the congruence relation.
* `New.Variety.localTerm`: the local term of a fixed point, a polynomial whose coefficients are
  built from the roots of the characteristic polynomial.
* `New.Variety.IsSignedFrameFor.similitude_and_root_norm`: an automorphism scales the form, and its
  eigenvalues have equal moduli.
* `New.Variety.IsSignedFrameFor.eq_one_of_congr_large_norm`: if such an automorphism is congruent to
  `1` modulo an ideal of large norm, it is `1`.
* `New.Variety.eventually_isNeat`: hence levels inside a large place are neat.

Notions from other files:
* `New.levelSpace`: For a representation π of G, a subgroup K and a character χ of K, the submodule
  of vectors v with π(k)v = χ(k)v for all k in K; for χ = 1, the K-fixed vectors.
* `New.ofSplitPlace`: For a split place w, the homomorphism sending g in GL_n(E_w) to the unitary
  finite adelic matrix with component g at w and 1 off w, w̄.
* `New.Variety.GU`: The unitary similitudes: the frames of the scalar forms `c • 1`, `c > 0`
  rational. `New.Variety.GUPlus`: those whose inverse has integral entries.
* `New.Gf`: The finite adelic unitary group G_f: matrices g in GL_n(𝔸_f) with gᴴg = 1;
  `New.stdLevel` is its subgroup of integral points, `New.stdSpace E n` the definite space with form
  `1`.
* `New.basicCosetRep U`: for a subspace U of k_wⁿ of dimension r (k_w the residue field at w), a
  chosen g in GL_n(E_w) with g and ϖg⁻¹ integral, det g of valuation r, and U the kernel of the
  reduction of g.
* `New.levelOf w H`: the elements of `New.stdLevel` whose reductions modulo the places `w i` lie in
  `H`; `New.classAut Γ K g`: the stabiliser Γ ∩ gKg⁻¹ of the coset gK.

## Relation to the literature

Known; see `Lib.Shimura.HeckeTower.Model`, `Lib.Shimura.IntegralModel.TowerExistence` and
`Lib.Shimura.Uniformisation.AppellHumbert` for sources.
-/

noncomputable section

/-!
## The Hecke algebra inside the group ring, acting on fixed vectors

* `New.Variety.cosetFn`: the map `k[G] → k[G / K]`, `[g] ↦ [gK]`.
-/

section GroupRingOperators

open MonoidAlgebra Submodule QuotientGroup Representation

namespace New.Variety

variable {G : Type*} (k : Type*) [Group G] [CommRing k] (K : Subgroup G)

/-- The submodule of the group ring k[G] spanned by the basis elements [g] for g in D. -/
def spanOn (D : Set G) : Submodule k k[G] := span k (of k G '' D)

variable {k} {a b : k[G]} {W : Type*} [AddCommGroup W] [Module k W]

lemma asAlgebraHom_eq_sum_support (π : Representation k G W) :
    π.asAlgebraHom a = ∑ g ∈ a.coeff.support, a.coeff g • π g :=
  rfl

/-- The linear map `k[G] → k[G / K]` sending `∑ a_g [g]` to `∑ a_g [gK]`. It is written as the
action of the group ring element on the basis vector of the trivial coset. -/
@[local simp]
def cosetFn (a : k[G]) : G ⧸ K →₀ k :=
  ((ofMulAction k G (G ⧸ K)).asAlgebraHom a (MonoidAlgebra.single ⟦1⟧ 1)).coeff

/-- The submodule of elements `a` of k[G] with the following property: for every representation π of
G, `a` sends the K-fixed vectors to vectors on which the subgroup J of H acts through π∘ι by the
character χ. By default J = ι⁻¹(K) and χ is trivial. -/
def fixedToEigen {H : Type*} [Group H] (ι : H →* G) (J : Subgroup H := K.comap ι)
    (χ : J →* k := 1) :
    Submodule k k[G] where
  carrier :=
    {a : k[G] |
      ∀ ⦃W : Type⦄ [AddCommGroup.{0} W] [Module k W] ⦃π : Representation k G W⦄ ⦃v : W⦄,
        v ∈ levelSpace π K →
        π.asAlgebraHom a v ∈ levelSpace (π.comp ι) J χ}
  add_mem' := by simp_all
  zero_mem' := by simp_all
  smul_mem' := by simp_all [smul_smul, mul_comm]

variable {K} {D D' D'' : Set G}

/-- For ψ from G/K to a k-module W, the linear map sending a = ∑ a_g [g] in k[G] to ∑ a_g ψ(gK). -/
def Model.cosetSum (ψ : G ⧸ K → W) (a : k[G]) : W := (cosetFn K a).linearCombination k ψ

/-- The basis vector of the trivial coset in k[G / K] is fixed by K. -/
lemma single_one_mem_levelSpace :
    MonoidAlgebra.single (QuotientGroup.mk 1 : G ⧸ K) (1 : k) ∈
      levelSpace (ofMulAction k G (G ⧸ K)) K := by
  intro κ
  -- `κ • (1 K) = κ K = 1 K` as `κ ∈ K`
  simp [← mk_mul_of_mem 1 κ.property]

/-- If `a` is supported on `D`, its image in `k[G / K]` is supported on the cosets of elements of
`D`. -/
lemma spanOn.exists_mem_of_cosetFn_ne_zero (ha : a ∈ spanOn k D) {q : G ⧸ K} :
    cosetFn K a q ≠ 0 → ∃ d ∈ D, (d : G ⧸ K) = q := by
  -- The elements whose function vanishes at `q` form a submodule, which contains `of k G d`
  -- whenever the coset of `d` is not `q`.
  contrapose!
  intro hq
  induction ha using span_induction with
  | mem x hx =>
    obtain ⟨d, hd, rfl⟩ := hx
    simp [hq d hd]
  | zero => simp
  | add x y hx_mem hy_mem hx hy => simp_all
  | smul r x hx_mem hx => simp_all

/-- If `a` is supported on `D`, `b` on `D'`, and `D * D' ⊆ D''`, then `a * b` is supported on
`D''`. -/
lemma spanOn.mul (ha : a ∈ spanOn k D) (hb : b ∈ spanOn k D')
    (h_mul : ∀ g ∈ D, ∀ g' ∈ D', g * g' ∈ D'') :
    a * b ∈ spanOn k D'' := by
  have h_prod : a * b ∈ spanOn k D * spanOn k D' := mul_mem_mul ha hb
  rw [spanOn, spanOn, span_mul_span] at h_prod
  -- `[g] [g'] = [g g']`, and `g g' ∈ D''`
  refine span_mono (Set.mul_subset_iff.mpr ?_) h_prod
  rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
  exact ⟨g * g', h_mul g hg g' hg', map_mul (of k G) g g'⟩

end New.Variety

end GroupRingOperators

/-!
## Marked triples, safe places and Hecke elements in the fixed point count

`Φ v` is the embedding chosen by the CM type at the infinite place `v`, and `v₀` is the one place at
which the hermitian forms may be indefinite. `New.Variety.IsSignedFrame x J` says that the adelic
matrix `x` is a frame for a rational form β that is positive definite off `v₀`, with β J positive
definite at `v₀`. `New.Variety.toFinGL` embeds rational matrices in adelic ones.
-/

section HeckeData

open NumberField Cardinal Polynomial Module Matrix.GeneralLinearGroup Prod MulAction

variable (E : Type) [Field.{0} E] [NumberField E] [IsCMField E]
  {n : Type} [Fintype.{0} n] [DecidableEq n] {d d₀ : ℕ} [Fact (d % 4 = 3)]

/-- The prime u of ℚ(√−d) contains an element x = (1 + √−d)/2 − b, b ∈ ℤ, that is coprime to its
conjugate x̄; here `QuadField.betaK d` is (1 + √−d)/2. -/
def New.GaloisRep.IsSplitPrimeToDisc (u : FinPlace (QuadField d)) : Prop :=
  ∃ b : ℤ,
    let x : 𝓞 (QuadField d) := QuadField.betaK d - b
    x ∈ u.asIdeal ∧ IsCoprime x (star x)

/-- Let the place w of ℚ(√−d) satisfy `New.GaloisRep.IsSplitPrimeToDisc`. Then w̄ ≠ w, the order
`w.q` of the residue field of w is prime, and the places of ℚ(√−d) that contain `w.q` are exactly
w and w̄. -/
lemma New.GaloisRep.IsSplitPrimeToDisc.isSplit_and_prime_q {w : FinPlace (QuadField d)}
    (h_split : IsSplitPrimeToDisc w) :
    w.IsSplit ∧
    w.q.Prime ∧
    ∀ u : FinPlace (QuadField d), u = w ∨ u = star w ↔ ↑w.q ∈ u.asIdeal := by
  obtain ⟨b, hx, hx_coprime⟩ := h_split
  -- `w` lies over a prime number `p`
  obtain ⟨p, _, -, hp_mem, hp, -⟩ := w.asIdeal.exists_prime_and_absNorm_eq_pow
  -- The places over `p` are `w` and `J` (possibly equal), and `star w` is one of them. Either
  -- `w = J` with `w.q = p ^ 2`, or `w.q = J.q = p` and `(p) = w J`.
  obtain ⟨J, h_over, h_cases⟩ := QuadField.prime_inert_or_eq_mul (hp := ⟨hp⟩) w hp_mem
  -- `w` contains `QuadField.betaK d - b` but not its conjugate, which is coprime to it.
  have h_ne : star w ≠ w := by
    intro h_eq
    have h_mem_star : QuadField.betaK d - (b : 𝓞 (QuadField d)) ∈ (star w).asIdeal := by
      rwa [h_eq]
    have h_star_mem : star (QuadField.betaK d - (b : 𝓞 (QuadField d))) ∈ w.asIdeal :=
      mem_star_place.mp h_mem_star
    exact w.isPrime.notMem_of_isCoprime_of_mem hx_coprime hx h_star_mem
  have hp_star : (p : 𝓞 (QuadField d)) ∈ (star w).asIdeal := by simpa using hp_mem
  obtain rfl : star w = J := ((h_over (star w)).mp hp_star).resolve_left h_ne
  -- The inert case `w = J` is excluded, so `w.q = p`.
  obtain rfl : w.q = p := by
    rcases h_cases with ⟨h_inert, -⟩ | ⟨h_norm, -⟩
    · exact absurd h_inert.symm h_ne
    · exact h_norm
  exact ⟨h_ne, hp, fun u ↦ (h_over u).symm⟩

/-- A place satisfying `New.GaloisRep.IsSplitPrimeToDisc` differs from its conjugate. -/
lemma New.GaloisRep.IsSplitPrimeToDisc.isSplit {w : FinPlace (QuadField d)}
    (h_split : IsSplitPrimeToDisc w) : w.IsSplit :=
  h_split.isSplit_and_prime_q.1

/-- The order `w.q` of the residue field of a place satisfying
`New.GaloisRep.IsSplitPrimeToDisc` is prime. -/
lemma New.GaloisRep.IsSplitPrimeToDisc.prime_q {w : FinPlace (QuadField d)}
    (h_split : IsSplitPrimeToDisc w) : w.q.Prime := by
  obtain ⟨-, h_prime, -⟩ := h_split.isSplit_and_prime_q
  exact h_prime

/-- If `w` satisfies `New.GaloisRep.IsSplitPrimeToDisc`, the places that contain `w.q` are `w` and
its conjugate. -/
lemma New.GaloisRep.IsSplitPrimeToDisc.q_mem_asIdeal_iff {w : FinPlace (QuadField d)}
    (h_split : IsSplitPrimeToDisc w) (u : FinPlace (QuadField d)) :
    ↑w.q ∈ u.asIdeal ↔ u = w ∨ u = star w := by
  obtain ⟨-, -, h_places⟩ := h_split.isSplit_and_prime_q
  exact (h_places u).symm

/-- The number d is 3 mod 4, and the field E is an algebra over the imaginary quadratic field
ℚ(i√d). -/
class New.HasQuadSubfield (d : outParam ℕ) (E : semiOutParam Type)
    [semiOutParam (Field E)] extends Fact (d % 4 = 3), Algebra (QuadField d) E

namespace New.Variety

/-- The finite places w of E with w̄ ≠ w, that is, those split over the maximal real subfield. -/
abbrev SplitFinPlace : Type := {w : FinPlace E // w.IsSplit}

variable {E : Type} [Field.{0} E] [CMBase E] {n : Type} [Fintype.{0} n] [DecidableEq n]
  [HasQuadSubfield d₀ E] (t : E →+* ℂ) {ν : ℕ} (α : Fin ν → 𝓞 E) (P : E[X]) (μ : ℂ) (k : Type*)
  [CommRing k] (𝔑 : 𝓞 E)

omit [DecidableEq n] in
/-- A finite type embeds in ℂ. -/
lemma nonempty_embedding_complex : Nonempty (n ↪ ℂ) :=
  (Cardinal.le_def n ℂ).mp (mk_le_aleph0.trans (aleph0_le_mk ℂ))

/-- A chosen injection `n ↪ ℂ` that lists the roots of `t(P)` when these, counted with
multiplicity, are `|n|` distinct numbers (`roots_map_eq_map_numberedRoots`). Otherwise it is an
arbitrary injection. -/
def numberedRoots (t : E →+* ℂ) (P : E[X]) : n ↪ ℂ :=
  have : Nonempty (n ↪ ℂ) := nonempty_embedding_complex
  Classical.epsilon fun r : n ↪ ℂ ↦ (P.map t).roots = Finset.univ.val.map r

omit [CMBase E] [DecidableEq n] in
/-- If some injection `n ↪ ℂ` lists the roots of `t(P)`, then `numberedRoots t P` does. -/
lemma roots_map_eq_map_numberedRoots {t : E →+* ℂ} {P : E[X]}
    (h_exists : ∃ r : n ↪ ℂ, (P.map t).roots = Finset.univ.val.map r) :
    (P.map t).roots = Finset.univ.val.map (numberedRoots t P : n ↪ ℂ) :=
  Classical.epsilon_spec h_exists

open scoped Classical in
/-- The matrix that describes the signature at `v₀`, written as a polynomial in `Φ v₀ (y)`. The
proposition `ε` chooses the case. In the marked case (`ε` holds) it is `markedReflection y i`. In
the definite case (`ε` fails) it is the identity. See `eigenReflection_eq_ite`. -/
def eigenReflection (ε : Prop) (y : GL n E) (i : n) : Matrix n n ℂ :=
  aeval (y.val.map (Φ v₀))
    (if ε then
      Lagrange.interpolate Finset.univ (numberedRoots (Φ v₀) y.val.charpoly)
        fun j : n ↦ if j = i then 1 else -1
    else 1)

/-- The marked case of `eigenReflection`: the matrix `Q(Φ v₀ (y))`, where `Q` is the Lagrange
polynomial with value `1` at the `i`-th listed root of the characteristic polynomial of `y` and
`-1` at the others (`markedReflection_eq_aeval`). If the roots are distinct, it is `1` on the
`i`-th eigenline and `-1` on the other eigenlines. -/
abbrev markedReflection (y : GL n E) (i : n) : Matrix n n ℂ :=
  eigenReflection True y i

lemma markedReflection_eq_aeval (y : GL n E) (i : n) :
    markedReflection y i = aeval (y.val.map (Φ v₀))
      (Lagrange.interpolate Finset.univ (numberedRoots (Φ v₀) y.val.charpoly)
        fun j : n ↦ if j = i then 1 else -1) := by
  simp [markedReflection, eigenReflection]

open scoped Classical in
/-- The matrix `eigenReflection ε y i` is `markedReflection y i` if ε holds and `1` otherwise. -/
lemma eigenReflection_eq_ite (ε : Prop) (y : GL n E) (i : n) :
    eigenReflection ε y i = if ε then markedReflection y i else 1 := by
  by_cases hε : ε <;> simp [markedReflection, eigenReflection, hε]

section

variable {E : Type} [Field.{0} E] [NumberField E] (K : Subgroup (GL n (𝔸f E))) (y : GL n E)

/-- Triples (xK, y, z): a coset of `K` in GL_n of the finite adeles, an element `y` of GL_n(E), and
a mark `z : Z`. In `New.Variety.countTerm` the type of marks is `Z = n`, the index of an eigenvalue
of `y`; the default is `Z = ℂ`. GL_n(E) acts by left multiplication on the coset, by
conjugation on `y`, and trivially on the mark. -/
def MarkedTriple (Z : Type := ℂ) : Type := (GL n (𝔸f E) ⧸ K) × GL n E × Z

instance {Z : Type} : MulAction (GL n E) (MarkedTriple K Z) :=
  @mulAction _ _ _ _ (.compHom _ toFinGL)
    (@mulAction _ _ _ _ (.compHom _ MulAut.conj) (.ofEndHom 1))

/-- For y in GL_n(E) and x in GL_n of the finite adeles of E, the element x⁻¹y⁻¹x of that adelic
group, with y embedded diagonally. -/
abbrev invAutInFrame (x : GL n (𝔸f E)) : GL n (𝔸f E) := x⁻¹ * toFinGL y⁻¹ * x

end

/-! ### Split places and the Hecke elements of the congruence relation -/

section

variable {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] (v : SplitFinPlace E)

/-- For a split place v, the homomorphism sending g in GL_n(E_v) to the adelic matrix that is
g⁻ᵀ at v, the conjugate of g at v̄, and 1 elsewhere. -/
def conjAtSplit : GL n (LocField (v : FinPlace E)) →* GL n (𝔸f E) :=
  (invTransposeGL (n := n)).toMonoidHom.comp
    (MonoidHom.comp (N := Gf E n) (U 1).subtype (ofSplitPlace v.property))

/-- For a split place v, the homomorphism sending an adelic matrix to the inverse transpose of
its component at v, in GL_n(E_v); a left inverse of `New.Variety.conjAtSplit` at v. -/
def dualComponent : GL n (𝔸f E) →* GL n (LocField (v : FinPlace E)) :=
  (invTransposeGL (n := n)).symm.toMonoidHom.comp (Matrix.GeneralLinearGroup.map (evalAt v.val))

end

/-- Cuspidality of χ: for every idempotent matrix ε ≠ 0, 1, χ is non-trivial on the elements of
J lying in the unipotent group 1 + εM_n(1 − ε). -/
def IsCuspidalType {F : Type*} [Field F] (J : Subgroup (GL n F)) (χ : J →* ℂ) : Prop :=
  ∀ ε : Matrix n n F, IsIdempotentElem ε → ε ≠ 0 → ε ≠ 1 →
    ∃ (j : J) (Y : Matrix n n F), 1 + ε * Y * (1 - ε) = ((j : GL n F) : Matrix n n F) ∧ χ j ≠ 1

section

variable {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] [HasQuadSubfield d₀ E]
  (v : SplitFinPlace E)

/-- The norm from E to K₀ of the finite idele that is the chosen uniformiser at v and 1
elsewhere. -/
abbrev uniformizerNorm : (𝔸f (QuadField d₀))ˣ :=
  (locIdele v.val (uniformizer v.val)).map (adeleNorm (QuadField d₀) E)

/-- The homomorphism sending a finite idele x of K₀ to the scalar matrix x̄·1 in GL_n of the
finite adeles of E. -/
abbrev centralScalar : (𝔸f (QuadField d₀))ˣ →* GL n (𝔸f E) :=
  (scalar n).comp
    (Units.map ((starRingEnd (𝔸f E)).comp (finAdeleIncl (QuadField d₀) E)).toMonoidHom)

end

/-- Safe places w of E: the place u of ℚ(√−d₀) below w satisfies `New.GaloisRep.IsSplitPrimeToDisc`,
and 𝔑 lies neither in w nor in any place above ū. -/
def IsSafe (w : FinPlace E) : Prop :=
  GaloisRep.IsSplitPrimeToDisc (w.below (QuadField d₀)) ∧
  𝔑 ∉ w.asIdeal ∧
  ∀ v : FinPlace E, v.below (QuadField d₀) = star (w.below (QuadField d₀)) → 𝔑 ∉ v.asIdeal

/-- The split places of E that are safe for K₀ and the level 𝔑, in the sense of
`New.Variety.IsSafe`. -/
abbrev SafePlace {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] [HasQuadSubfield d₀ E]
    (𝔑 : 𝓞 E) : Type := {w : SplitFinPlace E // IsSafe 𝔑 w}

section

omit [CMBase E]

/-- A safe place lies over a place of K₀ that satisfies `New.GaloisRep.IsSplitPrimeToDisc`. -/
lemma IsSafe.isSplitPrimeToDisc_below {𝔑 : 𝓞 E} {w : FinPlace E} (h_safe : IsSafe 𝔑 w) :
    GaloisRep.IsSplitPrimeToDisc (w.below (QuadField d₀)) :=
  h_safe.1

/-- If `w` is safe for 𝔑, then 𝔑 is prime to `w`. -/
lemma IsSafe.level_notMem_asIdeal {𝔑 : 𝓞 E} {w : FinPlace E} (h_safe : IsSafe 𝔑 w) :
    𝔑 ∉ w.asIdeal := by
  obtain ⟨-, h_level, -⟩ := h_safe
  exact h_level

/-- If `w` is safe for 𝔑, then 𝔑 is prime to every place `v` above the conjugate of the place of
K₀ below `w`. -/
lemma IsSafe.level_notMem_asIdeal_of_below_eq_star {𝔑 : 𝓞 E} {w : FinPlace E} (h_safe : IsSafe 𝔑 w)
    {v : FinPlace E} (hv : v.below (QuadField d₀) = star (w.below (QuadField d₀))) :
    𝔑 ∉ v.asIdeal := by
  obtain ⟨-, -, h_conj⟩ := h_safe
  exact h_conj v hv

end

/-- For a subspace U of k_vⁿ (k_v the residue field) of dimension r, the scalar matrix of the
conjugate of the (-r)-th power of `New.Variety.uniformizerNorm` at v, times
`New.Variety.conjAtSplit` of the transpose of `New.basicCosetRep` U. -/
def invHeckeIsogeny {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] [HasQuadSubfield d₀ E]
    (v : SplitFinPlace E)
    (U : Submodule (ResField (v : FinPlace E)) (n → ResField (v : FinPlace E))) :
    GL n (𝔸f E) :=
  centralScalar (n := n) (uniformizerNorm v ^ finrank (ResField v.val) ↥U)⁻¹ *
    conjAtSplit v (transposeGL (basicCosetRep U))

variable (n)

section

variable {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] (n : Type) [Fintype.{0} n]
  [DecidableEq n] [HasQuadSubfield d₀ E] (k : Type*) [CommRing k] (v : SplitFinPlace E) (𝔑 : 𝓞 E)

/-- The principal level: the similitudes in `GL_n(Ô E)` that are congruent to `1` modulo `𝔑`. -/
def levelGU : Subgroup (GL n (𝔸f E)) :=
  GU E n ⊓ congruenceGL (Ô E ∙ algebraMap (𝓞 E) (𝔸f E) 𝔑) id

/-- The element τ_{v,j} of the group ring over k: the sum of the elements
`New.Variety.invHeckeIsogeny` over all j-dimensional subspaces U of k_vⁿ. -/
def heckeSum (j : ℕ) : MonoidAlgebra k (GL n (𝔸f E)) :=
  ∑ U ∈ {U : Submodule (ResField v.val) (n → ResField v.val) | finrank (ResField v.val) U = j},
    MonoidAlgebra.of k (GL n (𝔸f E)) (invHeckeIsogeny v U)

/-- The Hecke algebra of level K = `New.Variety.levelGU` for 𝔑. It is the subalgebra of elements
∑ a_g [g] of k[GL_n(𝔸_f)] that are supported on `GUPlus E n` and whose function ∑ a_g 1_{gK} is
left K-invariant. -/
def heckeAlgebra : Subalgebra k (MonoidAlgebra k (GL n (𝔸f E))) :=
  (spanOn k (GUPlus E n) ⊓
    fixedToEigen (levelGU n 𝔑) (MonoidHom.id (GL n (𝔸f E))) (levelGU n 𝔑)).toSubalgebra
    ⟨Submodule.subset_span ⟨1, by simp, rfl⟩, by simp [fixedToEigen]⟩ fun a b ha hb ↦
      -- `GUPlus E n` is closed under products, and `a * b` acts as `b` followed by `a`
      ⟨spanOn.mul ha.1 hb.1 fun _ hg _ ↦ mul_mem hg, by simp_all [fixedToEigen, -mem_levelSpace]⟩

end

variable {n 𝔑}

/-- The principal level consists of similitudes. -/
lemma levelGU_le_GU {𝔑 : 𝓞 E} : levelGU n 𝔑 ≤ GU E n :=
  inf_le_left

/-- An element of the Hecke algebra is supported on `GUPlus E n`. -/
lemma heckeAlgebra.val_mem_spanOn {𝔑 : 𝓞 E} {k : Type*} [CommRing k] (f : heckeAlgebra n k 𝔑) :
    f.val ∈ spanOn k (GUPlus E n) :=
  f.property.1

/-- An element of the Hecke algebra sends the vectors fixed by `levelGU n 𝔑` to vectors fixed by
it, in every representation. -/
lemma heckeAlgebra.val_mem_fixedToEigen {𝔑 : 𝓞 E} {k : Type*} [CommRing k]
    (f : heckeAlgebra n k 𝔑) :
    f.val ∈ fixedToEigen (levelGU n 𝔑) (MonoidHom.id (GL n (𝔸f E))) (levelGU n 𝔑) :=
  f.property.2

/-- For an element f = ∑ a_g [g] of the Hecke algebra of level 𝔑, the function ∑ a_g 1_{gK} on
cosets of the principal level subgroup K. -/
abbrev heckeCosetFn {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] {𝔑 : 𝓞 E}
    (f : heckeAlgebra n ℂ 𝔑) : GL n (𝔸f E) ⧸ levelGU n 𝔑 →₀ ℂ := cosetFn (levelGU n 𝔑) f.val

open scoped Classical in
/-- The term of a `GL n E`-orbit of triples, read at a chosen representative `(q, y, μ)` of the
orbit and a chosen representative `x` of the coset `q`. It is `f(x⁻¹ y⁻¹ x K) * ω(charpoly y, μ)`
if `x` is a signed frame for `eigenReflection ε y μ`, and `0` otherwise. So `ε = True` gives
the marked count and `ε = False` the definite count. The value does not depend on the two choices;
see `New.Variety.countTerm_mk` in `Lib.Shimura.Transfer.MarkedPairs`. -/
def countTerm (ε : Prop) {𝔑 : 𝓞 E} (f : heckeAlgebra n ℂ 𝔑) (ω : E[X] → n → ℂ)
    (c : orbitRel.Quotient (GL n E) (MarkedTriple (levelGU n 𝔑) n)) : ℂ :=
  let (q, y, μ) := c.out
  if IsSignedFrame q.out (eigenReflection ε y μ) then
    heckeCosetFn f (invAutInFrame y q.out) * ω y.val.charpoly μ
  else 0

/-- Regularity of f: whenever f(x⁻¹y⁻¹x) ≠ 0 with y in GL_n(E) and x adelic, the characteristic
polynomial of y is separable. -/
def IsRegularHecke {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] {𝔑 : 𝓞 E}
    (f : heckeAlgebra n ℂ 𝔑) : Prop :=
  ∀ ⦃y : GL n E⦄ ⦃x : GL n (𝔸f E)⦄,
    heckeCosetFn f (invAutInFrame y x) ≠ 0 → y.val.charpoly.Separable

open scoped Classical in
/-- For μ : ℂ, the eigenline of the root r at the embedding t : E →+* ℂ lies in the Lie algebra: if
t = Φ v₀, then r = μ; if t is the other embedding above v₀, then r ≠ μ̄; if t lies above a place
v ≠ v₀, then t = Φ v. -/
def IsLieRoot (r : ℂ) : Prop :=
  if InfinitePlace.mk t = v₀ then
    if t = Φ v₀ then r = μ else r ≠ star μ
  else
    t = Φ (InfinitePlace.mk t)

/-! ### The local term -/

open scoped Classical in
/-- For an embedding `σ : E →+* ℂ`, the roots `r` of σ(P), as polynomials: `r X` if the eigenline of
`r` lies in the Lie algebra, the constant `r` otherwise. It is `r X` exactly in these cases:
* σ = Φ v₀: only `r = μ`;
* σ the other embedding above `v₀`: all `r` other than the conjugate of `μ`;
* σ above a place `v ≠ v₀`: all `r` if σ = Φ v, none otherwise. -/
def lieRoots (σ : E →+* ℂ) : Multiset ℂ[X] :=
  (P.map σ).roots.map fun r : ℂ ↦ (if IsLieRoot σ μ r then X else 1) * C r

/-- For P : E[X] and α : Fin ν → 𝓞 E, with μ the `j`-th listed root of the image of P under Φ v₀:
the polynomial L(μX), with L the Lagrange basis polynomial that is 1 at μ and 0 at the other listed
roots, times ∏ (1 − σ(α i) η), over all i, all embeddings σ and all η in `New.Variety.lieRoots` at
σ. -/
def localTerm (j : n) : ℂ[X] :=
  let r : n ↪ ℂ := numberedRoots (Φ v₀) P
  (Lagrange.basis Finset.univ r j).comp (X * C (r j)) *
    ∏ i : Fin ν, ∏ σ : E →+* ℂ, ((lieRoots P (r j) σ).map fun x : ℂ[X] ↦ 1 - C (σ (α i)) * x).prod

end New.Variety

end HeckeData

/-!
## Rigidity of frames, neat levels and free action

Rigidity of frames, used to show that the objects counted have no automorphisms at deep level. A
matrix `x` over the finite adeles of the CM field `E` is a frame for the form `β`
(`New.Variety.IsFrameFor`) if `xᴴ β x` is the scalar matrix of a unit of `Ô ℚ`.
`New.Variety.IsSignedFrameFor x ℓ β` adds that `β` is positive definite at the infinite places other
than the base place `v₀`, and `β * ℓ` is so at `v₀`. `New.Variety.ratConj y ℓ` is `ℓ` conjugated by
the image of `y` under `Φ v₀`.
-/

section NeatLevel

open NumberField Fintype Matrix Multiset Ideal ComplexOrder AddMonoidHom Rat RingHom Module Algebra

namespace New.Variety

section

variable {E : Type} [Field.{0} E] [NumberField E] [IsCMField E]
  {n : Type} [Fintype.{0} n] [DecidableEq n] {x : GL n (𝔸f E)} {β : Matrix n n E} {𝔑 : 𝓞 E}

/-- A CM field that contains a primitive `5040`-th root of unity has degree at least `3` over `ℚ`,
hence at least two infinite places. -/
instance [h : HasPrimitiveRoot5040 E] : Nontrivial (InfinitePlace E) := by
  -- A primitive root of unity of order `5040` makes the degree of `E` at least `3`, and the
  -- degree is twice the number of infinite places.
  obtain ⟨ζ, hζ⟩ := h.exists_primitive_root
  have h_deg : 3 ≤ Module.finrank ℚ E :=
    (show 3 ≤ Nat.totient 5040 * Nat.totient 1 by decide +kernel).trans
      (totient_mul_totient_le_finrank _ 1 rfl .one hζ)
  have h_finrank : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) :=
    finrank_eq_two_mul_card_infinitePlace E
  exact one_lt_card_iff_nontrivial.1 (by omega)

/-- If `xᴴ x` is the scalar matrix of a finite idele `a` of `ℚ`, then the idele norm
`finIdeleAbs a` is a rational number `c`, and `x` is a frame for the positive scalar form `c • 1`.
-/
lemma exists_isScalarFrame_of_gram_eq (a : (𝔸f ℚ)ˣ)
    (h_gram : xᴴ * x.val = finAdeleIncl ℚ E a • 1) :
    ∃ c : ℚ, (c : ℝ) = finIdeleAbs a ∧ IsScalarFrame x c := by
  -- As `ℚ` has class number one, `a = s * u` with `s` rational and `u` a unit at every place; then
  -- `finIdeleAbs a = |s|⁻¹` by the product formula, and `|s|⁻¹ * a = ± u` is a unit of `Ô ℚ`.
  have h_split : a ∈ principalIdele.range ⊔ idelesUnitOff ∅ := by
    simpa [classNumber_eq] using pow_classNumber_mem_principal_sup a
  -- `a = principalIdele s * u` with `s ∈ ℚˣ` and `u` a unit at every place
  obtain ⟨_, ⟨s, rfl⟩, u, hu, rfl⟩ := Subgroup.mem_sup.1 h_split
  -- `u` as a unit of `Ô ℚ`
  let ν : (Ô ℚ)ˣ := (Ô ℚ).unitsEquivUnitsType ⟨u, idelesUnitOff_empty.le hu⟩
  have h_unit : finIdeleAbs u = 1 := by
    simp [finIdeleAbs, ideleAbs_eq_prod_of_v_eq_one, mem_idelesUnitOff.1 hu]
  have h_abs : finIdeleAbs (principalIdele s * u) = (|(s : ℚ)|⁻¹ : ℚ) := by
    rw [map_mul, h_unit, mul_one, finIdeleAbs_principalIdele]
    push_cast
    -- The goal's instance `Algebra ℚ ℚ` agrees with `Algebra.id ℚ` only after unfolding.
    exact congrArg (fun q : ℚ ↦ |(q : ℝ)|⁻¹)
      (show Algebra.norm ℚ (s : ℚ) = s by simp [Algebra.norm_self])
  refine ⟨|(s : ℚ)|⁻¹, h_abs.symm, inv_pos.2 (abs_pos.2 s.ne_zero), ?_⟩
  -- With `c = |s|⁻¹`, `xᴴ (c • 1) x = c • s • u`, which is `u` or `-u` by the sign of `s`.
  rcases abs_choice (s : ℚ) with hs | hs
  · exact ⟨ν, by simp [h_gram, hs, ν, principalIdele, mul_smul, map_smul']⟩
  · exact ⟨-ν, by simp [h_gram, hs, ν, principalIdele, Matrix.map_neg, mul_smul, map_smul']⟩

/-- A matrix `x` with `xᴴ x` the scalar matrix of a finite idele of `ℚ` is a similitude. -/
lemma mem_GU_of_gram_eq (a : (𝔸f ℚ)ˣ) (h_gram : xᴴ * x.val = finAdeleIncl ℚ E a • 1) :
    x ∈ GU E n :=
  let ⟨c, _, h_frame⟩ := exists_isScalarFrame_of_gram_eq a h_gram
  ⟨c, h_frame⟩

/-- If `xᴴ x` is the scalar matrix of a finite idele `a` of `ℚ` and the rational `c` is the idele
norm `finIdeleAbs a`, then `x` is a frame for the positive scalar form `c • 1`. -/
lemma isScalarFrame_of_gram_eq (a : (𝔸f ℚ)ˣ) (h_gram : xᴴ * x.val = finAdeleIncl ℚ E a • 1)
    {c : ℚ} (hc : (c : ℝ) = finIdeleAbs a) :
    IsScalarFrame x c := by
  obtain ⟨c', hc', h_frame⟩ := exists_isScalarFrame_of_gram_eq a h_gram
  rwa [show c = c' by exact_mod_cast hc.trans hc'.symm]

/-! ### Frames and their multipliers -/

/-- An element of the principal level is a similitude whose inverse has integral entries. -/
lemma mem_GUPlus_of_mem_levelGU (hx : x ∈ levelGU n 𝔑) : x ∈ GUPlus E n := by
  obtain ⟨h_sim, h_int, -⟩ := Subgroup.mem_inf.1 hx
  exact ⟨h_sim, h_int.isIntMatrix_inv⟩

/-- If `x` is a frame for the form `β`, the image of `β` under every complex embedding is
hermitian. -/
lemma IsFrameFor.isHermitian_map {f : E →+* ℂ} : IsFrameFor β x → (β.map f).IsHermitian := by
  rintro ⟨ε, hx⟩
  -- Over the adeles `β = ε • x⁻¹ᴴ * x⁻¹`, and conjugation fixes the rational adele `ε`.
  have hε_star : star (finAdeleIncl ℚ E ε) = finAdeleIncl ℚ E ε := by
    simp [star_eq_adeleMap, Subsingleton.elim ((starRingEnd E).comp _) (algebraMap ℚ E)]
  refine IsHermitian.map ?_ _ (map_star_complex f)
  apply Matrix.map_injective (algebraMap E (𝔸f E)).injective
  simp [conjTranspose_map _ fun a ↦ (star_algebraMap_finAdele a).symm, ← gram_inv_of_gram_eq hx,
    hε_star]

end

variable {E : Type} [Field.{0} E] [Ψ : CMBase E] {n : Type} [Fintype.{0} n] [DecidableEq n]
  {x : GL n (𝔸f E)} {ℓ : Matrix n n ℂ} {y : GL n E} {β : Matrix n n E} {x' : GL n (𝔸f E)}
  {ℓ' : Matrix n n ℂ} {β' : Matrix n n E} {𝔑 : 𝓞 E} [Nonempty n] {c : ℚ} {ι : Type*} [Fintype ι]

omit [Nonempty n] in
/-- A point `g` of the finite adelic unitary group `Gf E n` (so `gᴴ g = 1`) is a signed frame for
the identity form, with `ℓ = 1` at the base place. -/
lemma isSignedFrameFor_one (g : Gf E n) : IsSignedFrameFor g.val 1 1 :=
  ⟨⟨1, by simpa [U] using g.property⟩, by simp [PosDef.one]⟩

/-- If `x` is a similitude whose inverse has integral entries (`x ∈ GUPlus E n`) and `x` is a frame
for the scalar form `c • 1`, then the rational number `c` is an integer. -/
lemma IsFrameFor.exists_intCast_eq (hx : x ∈ GUPlus E n) (h : IsFrameFor ((c : E) • 1) x) :
    ∃ z : ℤ, z = c := by
  obtain ⟨ε, hframe⟩ := h
  obtain ⟨-, h_inv_int⟩ : x ∈ GU E n ∧ ∀ i j : n, x⁻¹ i j ∈ Ô E := hx
  -- `c • 1 = ε • x⁻¹ᴴ * x⁻¹` has integral diagonal entries, because `x⁻¹` and `ε` are integral.
  have h_diag_mem (i : n) : ((c : E) • (1 : Matrix n n E)).map (algebraMap E (𝔸f E)) i i ∈ Ô E := by
    rw [← gram_inv_of_gram_eq hframe]
    refine sum_mem ?_
    -- `coe_units_inv` is left out: it would turn `x⁻¹` into the matrix inverse, unlike `h_inv_int`.
    simp [mul_mem, adeleMap_mem_Ô, star_mem_Ô (h_inv_int _ _), h_inv_int, -coe_units_inv]
  -- A rational number that is integral at every place of `E` is an integer.
  simpa [isIntegral_ratCast_iff, IsIntegrallyClosed.isIntegral_iff] using h_diag_mem
    (Classical.arbitrary n)

/-- If `x` lies in the principal level `levelGU n 𝔑` and `x⁻¹` is a frame for the positive scalar
form `c • 1`, then `c = 1`. -/
lemma IsScalarFrame.eq_one_of_mem_levelGU (hx : x ∈ levelGU n 𝔑) (hframe : IsScalarFrame x⁻¹ c) :
    c = 1 := by
  -- Both `x` and `x⁻¹` lie in `GUPlus E n`, so `c` and `c⁻¹` are integers; and `c` is positive.
  obtain ⟨hc_pos, h_frame⟩ := hframe
  -- `x⁻¹ * x = 1` is a frame for `c⁻¹ • c • 1 = 1`, so `x` is one for `c⁻¹ • 1`.
  have h_inv_frame : IsFrameFor (((c⁻¹ : ℚ) : E) • 1) x :=
    h_frame.mul_iff.1 ⟨1, by simp [hc_pos.ne']⟩
  -- `c⁻¹ = k` and `c = z` for integers `k` and `z`
  obtain ⟨k, hk⟩ := h_inv_frame.exists_intCast_eq (mem_GUPlus_of_mem_levelGU hx)
  obtain ⟨z, rfl⟩ := h_frame.exists_intCast_eq (mem_GUPlus_of_mem_levelGU (inv_mem hx))
  have hzk : z * k = 1 := by
    qify
    rw [hk, mul_inv_cancel₀ hc_pos.ne']
  exact_mod_cast Int.eq_one_of_mul_eq_one_right (by exact_mod_cast hc_pos.le) hzk

/-- The inverse of an element of the principal level is a frame for the identity form. -/
lemma levelGU.isScalarFrame_inv_one (h : x ∈ levelGU n 𝔑) : IsScalarFrame x⁻¹ 1 := by
  obtain ⟨⟨c, hc⟩, -⟩ := Subgroup.mem_inf.1 (inv_mem h)
  rwa [hc.eq_one_of_mem_levelGU h] at hc

/-! ### Uniqueness of the form, and automorphisms -/

/-- A frame determines its form: let `x` in GL_n of the finite adeles of the CM field `E` be a frame
for both `β` and `β'` (`IsFrameFor`: xᴴβx = ε • 1 and xᴴβ'x = δ • 1 for units ε and δ of Ẑ). If
both forms are positive definite at the infinite place `w` (mapped to `ℂ` by the chosen embedding
`Φ w`), then `β' = β`. -/
lemma IsFrameFor.unique (w : InfinitePlace E) (h : IsFrameFor β x) (h' : IsFrameFor β' x)
    (hpos : (β.map (Φ w)).PosDef) (hpos' : (β'.map (Φ w)).PosDef) :
    β' = β := by
  -- The multipliers differ by a unit `u` of `Ô ℚ`, so `β' = u • β` over the adeles. Taking traces
  -- shows that `u` is a rational `s`; it is positive and a unit everywhere, hence `1`.
  obtain ⟨ε, hβ⟩ := h
  obtain ⟨δ, hβ'⟩ := h'
  obtain ⟨u, rfl⟩ : ∃ u : (Ô ℚ)ˣ, u * ε = δ := mul_right_surjective ε δ
  have h_adelic :
      finAdeleIncl ℚ E u • β.map (algebraMap E (𝔸f E)) = β'.map (algebraMap E (𝔸f E)) := by
    simp [← gram_inv_of_gram_eq hβ, ← gram_inv_of_gram_eq hβ', mul_smul]
  -- The trace of `β` is not zero, so one of its coordinates in a basis of `E / ℚ` is not zero;
  -- comparing that coordinate of the traces gives `u` as a quotient of two rationals.
  obtain ⟨s, hs⟩ : ∃ s : ℚ, ((u : Ô ℚ) : 𝔸f ℚ) = algebraMap ℚ (𝔸f ℚ) s := by
    let b : Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℚ E := integralBasis E
    obtain ⟨k, hk⟩ : ∃ k : Free.ChooseBasisIndex ℤ (𝓞 E), b.repr β.trace k ≠ 0 := by
      simpa [← map_trace, b.ext_elem_iff] using hpos.trace_pos.ne'
    have h_coord :
        (adeleBasis b).repr (trace (finAdeleIncl ℚ E u • β.map (algebraMap E (𝔸f E)))) k =
          (adeleBasis b).repr (trace (β'.map (algebraMap E (𝔸f E)))) k := by
      rw [h_adelic]
    -- In coordinates over `ℚ` this says `u * b.repr β.trace k = b.repr β'.trace k`.
    use (b.repr β.trace k)⁻¹ • b.repr β'.trace k
    simpa [← adeleCombination_repr b, adeleBasis, algebraMap_eq_smul_one, ← map_trace,
      ← smul_toAlgebra, ← eq_inv_smul_iff₀ hk, mul_smul] using h_coord
  -- So multiplying by `u` over the adeles is multiplying by `s` over `E`, and `β' = s • β`.
  have h_smul (A : Matrix n n E) :
      ((s : E) • A).map (algebraMap E (𝔸f E)) =
        finAdeleIncl ℚ E u • A.map (algebraMap E (𝔸f E)) := by
    simp [hs, map_smul']
  obtain rfl : (s : E) • β = β' :=
    map_injective (algebraMap E (𝔸f E)).injective ((h_smul β).trans h_adelic)
  -- The trace of `s • β` at `w` is `s` times the positive trace of `β`.
  have hs_pos : 0 < s := by
    simpa [← Complex.ofReal_ratCast, hpos.trace_pos, map_smul'] using hpos'.trace_pos
  -- The identity matrix, of level `0`, is a frame for `s • 1` with multiplier `u`.
  have h_one_frame : IsScalarFrame (1 : GL n (𝔸f E))⁻¹ s :=
    ⟨hs_pos, u, by simpa using h_smul 1⟩
  have hs_one : s = 1 :=
    IsScalarFrame.eq_one_of_mem_levelGU (levelGU n (0 : 𝓞 E)).one_mem h_one_frame
  rw [hs_one, Rat.cast_one, one_smul]

/-- Let `E` have a base place `v₀` (`CMBase`, so at least two infinite places), let `(x, ℓ, β)` and
`(x', ℓ', β')` be signed frames (`IsSignedFrameFor`), and let `y ∈ GL_n(E)`. If `(x'⁻¹ y x)⁻¹` is a
frame for the scalar form `c • 1` with `c > 0` rational, then `yᴴ β' y = c β`. -/
lemma IsSignedFrameFor.conjTranspose_mul_mul_eq_smul (h : IsSignedFrameFor x ℓ β)
    (h' : IsSignedFrameFor x' ℓ' β') (h_frame : IsScalarFrame (x'⁻¹ * toFinGL y * x)⁻¹ c) :
    yᴴ * β' * y.val = (c : E) • β := by
  -- Both forms have the frame `(toFinGL y)⁻¹ * x'` and are positive at a place `w ≠ v₀`, so they
  -- agree.
  obtain ⟨h_frame_x, h_pos_x⟩ := h
  obtain ⟨h_frame_x', h_pos_x'⟩ := h'
  obtain ⟨hc_pos, h_frame_c⟩ := h_frame
  obtain ⟨w, hw⟩ := exists_ne (v₀ : InfinitePlace E)
  have h_prod : toFinGL y * (x * (x'⁻¹ * toFinGL y * x)⁻¹) = x' := by group
  -- the common frame of the two forms
  set x₁ : GL n (𝔸f E) := x * (x'⁻¹ * toFinGL y * x)⁻¹
  have h_frame_conj : IsFrameFor (y.valᴴ * β' * y.val) x₁ := by
    rwa [IsFrameFor.conj_iff, h_prod]
  have hβ_pos : (β.map (Φ w)).PosDef := by simpa [hw] using h_pos_x w
  have hβ'_pos : (β'.map (Φ w)).PosDef := by simpa [hw] using h_pos_x' w
  have h_frame_smul : IsFrameFor ((c : E) • β) x₁ := h_frame_x.mul_iff.2 h_frame_c
  refine h_frame_smul.unique w h_frame_conj ?_ ?_
  · -- At `w` the form `c • β` is `c` times the positive definite `β`.
    have h_map_smul : ((c : E) • β).map (Φ w) = c • β.map (Φ w) := by
      simp [← Matrix.ext_iff, Rat.smul_def]
    simpa only [h_map_smul] using hβ_pos.smul hc_pos
  · -- At `w` the form `yᴴ β' y` is the positive definite `β'` transported by `y`.
    rw [map_conjTranspose_mul_mul (Φ w) (map_star_complex (Φ w))]
    simpa [star_eq_conjTranspose] using
      (y.map (Φ w)).isUnit.posDef_star_left_conjugate_iff.2 hβ'_pos

/-- Let `(x, ℓ, β)` be a signed frame (`IsSignedFrameFor`) and let `y ∈ GL_n(E)` fix `ℓ` under
`ratConj`, with `(x⁻¹ y x)⁻¹` a frame for the scalar form `c • 1`; so `y` is an automorphism of the
object given by `x`. Then `y` is a similitude of `β` with multiplier `c` (`yᴴ β y = c β`), and each
root `r` of the characteristic polynomial of `y` mapped by `Φ w`, at each infinite place `w`, has
`r * star r = c`. -/
lemma IsSignedFrameFor.similitude_and_root_norm (h : IsSignedFrameFor x ℓ β)
    (h_frame : IsScalarFrame (x⁻¹ * toFinGL y * x)⁻¹ c) (hℓ : ratConj y ℓ = ℓ) :
    yᴴ * β * y.val = (c : E) • β ∧
    ∀ w : InfinitePlace E, ∀ r ∈ (y.val.charpoly.map (Φ w)).roots, r * star r = c := by
  -- Uniqueness of the form of a frame gives `yᴴ β y = c β`. So `Φ w y` scales the positive
  -- form `Φ w β * J` by `c`, and evaluating this on an eigenvector gives `r * star r = c`.
  have h_form : y.valᴴ * β * y.val = (c : E) • β := h.conjTranspose_mul_mul_eq_smul h h_frame
  refine ⟨h_form, fun w r hr ↦ ?_⟩
  obtain ⟨-, h_pos_all⟩ := h
  let J : Matrix n n ℂ := if w = v₀ then ℓ else 1
  have h_pos : (β.map (Φ w) * J).PosDef := h_pos_all w
  -- `J` is `ℓ` at `v₀`, which `y` fixes by `hℓ`, and `1` at the other places.
  have hJ_fixed : ConjAct.toConjAct (y.map (Φ w)) • J = J := by
    rcases eq_or_ne w v₀ with rfl | hw
    · simpa [J, ratConj] using hℓ
    · simp [J, hw]
  have h_comm : y.val.map (Φ w) * J = J * y.val.map (Φ w) :=
    (y.map (Φ w)).mul_inv_eq_iff_eq_mul.1 hJ_fixed
  obtain ⟨u, hu_ne, hu⟩ : ∃ u : n → ℂ, u ≠ 0 ∧ r • u = y.val.map (Φ w) *ᵥ u := by
    simpa [← charpoly_map, eval_charpoly, ← exists_mulVec_eq_zero_iff, sub_mulVec,
      sub_eq_zero] using
      Polynomial.isRoot_of_mem_roots hr
  -- Pair `h_form` with `u` and `J u`: the left side is `r * star r` times the positive number
  -- `q = uᴴ (Φ w β * J) u` by `h_comm` and `hu`, and the right side is `c * q`.
  have hq_ne : star u ⬝ᵥ (β.map (Φ w) * J) *ᵥ u ≠ 0 := (h_pos.dotProduct_mulVec_pos hu_ne).ne'
  refine mul_right_cancel₀ hq_ne ?_
  calc r * star r * (star u ⬝ᵥ (β.map (Φ w) * J) *ᵥ u)
      = star u ᵥ* (y.valᴴ * β * y.val).map (Φ w) ⬝ᵥ J *ᵥ u := by
        rw [mul_assoc]
        symm
        simp [map_conjTranspose_mul_mul (Φ w) (map_star_complex (Φ w)), ← vecMul_vecMul,
          ← star_mulVec, ← dotProduct_mulVec, ← J.mulVec_mulVec, ← hu, h_comm, mulVec_smul]
    _ = star u ᵥ* ((c : E) • β).map (Φ w) ⬝ᵥ J *ᵥ u := by rw [h_form]
    _ = c * (star u ⬝ᵥ (β.map (Φ w) * J) *ᵥ u) := by
        simp [map_smul', ← dotProduct_mulVec, smul_mulVec]

variable {E : Type} [Field.{0} E] [NumberField E] {x : GL n (𝔸f E)} {y : GL n E} in
omit [Nonempty n] Ψ in
/-- If `x⁻¹ y x` is congruent to `1` modulo the ideal `J` of `Ô E`, and `J` meets `𝓞 E` inside the
ideal `I`, then the trace of `y - 1` is an algebraic integer `t` that lies in `I`. -/
private lemma exists_eq_trace_sub_one_mem_of_mem_congruenceGL {I : Ideal (𝓞 E)} {J : Ideal (Ô E)}
    (h_cong : x⁻¹ * toFinGL y * x ∈
      congruenceGL (Submodule.map (Algebra.linearMap (Ô E) (𝔸f E)) J) id)
    (hJI : under (𝓞 E) J ≤ I) :
    ∃ t : 𝓞 E, (t : E) = (y.val - 1).trace ∧ t ∈ I := by
  obtain ⟨-, h_row⟩ := h_cong
  -- The trace is invariant under conjugation by `x`, and the diagonal entries lie in `J`.
  have h_conj : ((x⁻¹ * toFinGL y * x).val - 1).trace ∈
      Submodule.map (Algebra.linearMap (Ô E) (𝔸f E)) J :=
    Submodule.sum_mem _ fun i _ ↦ h_row i i
  have h_mem : algebraMap E (𝔸f E) (y.val - 1).trace ∈
      Submodule.map (Algebra.linearMap (Ô E) (𝔸f E)) J := by
    simpa [map_trace, trace_mul_cycle] using h_conj
  obtain ⟨⟨a, ha_int⟩, ha_mem, ⟨⟩⟩ := h_mem
  exact ⟨⟨(y.val - 1).trace, algebraMap_mem_Ô.1 ha_int⟩, rfl, hJI ha_mem⟩

omit [Nonempty n] in
/-- If every complex eigenvalue `r` of `y` at the infinite place `v` has `r * star r = 1`, then the
image of the trace of `y - 1` under `Φ v` has modulus at most `2 * card n`. -/
private lemma norm_trace_sub_one_le_of_mul_star_eq_one (v : InfinitePlace E)
    (h_root : ∀ r ∈ (y.val.charpoly.map (Φ v)).roots, r * star r = 1) :
    ‖Φ v (y.val - 1).trace‖ ≤ 2 * card n := by
  have h_unit (r : ℂ) (hr : r ∈ (y.val.charpoly.map (Φ v)).roots) : ‖r‖ ≤ 1 := by
    simpa [← sq] using (congrArg norm (h_root r hr)).le
  have h_sum : Φ v (y.val - 1).trace = (y.val.charpoly.map (Φ v)).roots.sum - card n := by
    simp [map_trace, trace_eq_sum_roots_charpoly, charpoly_map]
  grw [h_sum, norm_sub_le, norm_multiset_sum_le, sum_map_le_sum_map _ 1 h_unit]
  simp [IsAlgClosed.card_roots_eq_natDegree, two_mul]

section

variable {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] {x : GL n (𝔸f E)} {y : GL n E}
  {β : Matrix n n E}

omit Ψ in
/-- An algebraic integer `t` of `E` whose images under all the embeddings `Φ v` have modulus at
most `B` has norm at most `B ^ [E : ℚ]` in absolute value. -/
private lemma abs_norm_le_pow_finrank_of_forall_norm_le {E : Type} [Field.{0} E] [CMType E]
    {t : 𝓞 E} {B : ℝ} (h_le : ∀ v : InfinitePlace E, ‖Φ v (t : E)‖ ≤ B) :
    |(Algebra.norm ℤ t : ℝ)| ≤ B ^ finrank ℚ E := by
  -- `|N t| = ∏ v, ‖Φ v t‖ ^ 2`, and `[E : ℚ]` is twice the number of places `v`.
  rw [← Rat.cast_intCast, Algebra.coe_norm_int, abs_norm_eq_prod_norm_sq]
  calc ∏ v : InfinitePlace E, ‖Φ v (t : E)‖ ^ 2
      ≤ ∏ _v : InfinitePlace E, B ^ 2 := by
        gcongr with v
        exact h_le v
    _ = B ^ finrank ℚ E := by
        simp [finrank_eq_two_mul_card_infinitePlace, pow_mul]

omit [Nonempty n] Ψ in
/-- Let `x⁻¹ y x` be congruent to `1` modulo the ideal `J` of `Ô E`, where `J` meets `𝓞 E` inside an
ideal `I` of norm above `(2 * card n) ^ [E : ℚ]`. If the images of the trace of `y - 1` under all
the embeddings `Φ v` have modulus at most `2 * card n`, then the trace of `y` is `card n`. -/
private lemma trace_eq_card_of_mem_congruenceGL {E : Type} [Field.{0} E] [CMType E]
    {x : GL n (𝔸f E)} {y : GL n E} {I : Ideal (𝓞 E)} {J : Ideal (Ô E)}
    (h_cong : x⁻¹ * toFinGL y * x ∈
      congruenceGL (Submodule.map (Algebra.linearMap (Ô E) (𝔸f E)) J) id)
    (hJI : under (𝓞 E) J ≤ I) (h_large : (2 * card n) ^ finrank ℚ E < absNorm I)
    (h_conj_le : ∀ v : InfinitePlace E, ‖Φ v (y.val - 1).trace‖ ≤ 2 * card n) :
    y.val.trace = card n := by
  obtain ⟨t, ht_eq, ht_mem⟩ : ∃ t : 𝓞 E, (t : E) = (y.val - 1).trace ∧ t ∈ I :=
    exists_eq_trace_sub_one_mem_of_mem_congruenceGL h_cong hJI
  have h_norm_lt : |Algebra.norm ℤ t| < absNorm I := by
    rify at h_large ⊢
    rw [← ht_eq] at h_conj_le
    exact (abs_norm_le_pow_finrank_of_forall_norm_le h_conj_le).trans_lt h_large
  -- The norm of `t` is a multiple of `absNorm I` and smaller in absolute value, hence `0`.
  have h_zero : t = 0 := Algebra.norm_eq_zero_iff.1
    (Int.eq_zero_of_abs_lt_dvd (absNorm_dvd_norm_of_mem ht_mem) h_norm_lt)
  simpa [h_zero, sub_eq_zero] using ht_eq.symm

omit [Nonempty n] Ψ in
/-- Let `β` be positive definite at the infinite place `w`. If `y` preserves `β` (`yᴴ β y = β`) and
the trace of `y` is `card n`, then `y = 1`: the positive definite form `A ↦ tr (β⁻¹ Aᴴ β A)` at
`w` takes the value `n - n - n + n = 0` at `A = y - 1`. -/
private lemma eq_one_of_conjTranspose_mul_mul_eq_of_trace_eq {E : Type} [Field.{0} E] [CMType E]
    {y : GL n E} {β : Matrix n n E} (w : InfinitePlace E)
    (h_pos : (β.map (Φ w)).PosDef) (h_form : y.valᴴ * β * y.val = β)
    (h_trace : y.val.trace = card n) :
    y = 1 := by
  refine Units.ext (map_injective (Φ w).injective ?_)
  -- `vec_sub` is left out: it would split `vec (y - 1)` before the form is evaluated.
  simpa [kronecker_mulVec_vec, star_vec_dotProduct_vec, sub_mul, ← mul_assoc,
    ← map_conjTranspose_mul_mul, -vec_sub, h_pos.det_pos.ne', ← map_trace, h_form, h_trace,
    sub_eq_zero, trace_mul_cycle] using
    (h_pos.inv.transpose.kronecker h_pos).dotProduct_mulVec_pos (x := vec (y.map (Φ w) - 1))

end

/-- Let `(x, ℓ, β)` be a signed frame, let `y ∈ GL_n(E)` fix `ℓ` under `ratConj`, and let
`(x⁻¹ y x)⁻¹` be a frame for the identity form (so `y` is an automorphism of the object given by
`x`). If `x⁻¹ y x` is congruent to `1` modulo an ideal `J` of `Ô E`, and `J` meets `𝓞 E`
inside an ideal `I` of norm above `(2 * card n) ^ [E : ℚ]`, then `y = 1`. -/
lemma IsSignedFrameFor.eq_one_of_congr_large_norm (h : IsSignedFrameFor x ℓ β) {I : Ideal (𝓞 E)}
    (J : Ideal (Ô E)) (h_frame : IsScalarFrame (x⁻¹ * toFinGL y * x)⁻¹ 1)
    (h_cong : x⁻¹ * toFinGL y * x ∈
      congruenceGL (Submodule.map (Algebra.linearMap (Ô E) (𝔸f E)) J) id)
    (hℓ : ratConj y ℓ = ℓ) (h_large : (2 * card n) ^ finrank ℚ E < absNorm I)
    (hJI : under (𝓞 E) J ≤ I) :
    y = 1 := by
  -- The eigenvalues of `y` have modulus `1`, so the conjugates of `tr y - n` have modulus at most
  -- `2 * n`. This number lies in `I`, so its norm is a multiple of `absNorm I` and smaller, hence
  -- `0`. An isometry of a positive form whose trace is `n` is the identity.
  obtain ⟨h_form, h_root⟩ := h.similitude_and_root_norm h_frame hℓ
  obtain ⟨-, h_pos_all⟩ := h
  have h_conj_le (v : InfinitePlace E) : ‖Φ v (y.val - 1).trace‖ ≤ 2 * card n :=
    norm_trace_sub_one_le_of_mul_star_eq_one v fun r hr ↦ by exact_mod_cast h_root v r hr
  have h_trace : y.val.trace = card n :=
    trace_eq_card_of_mem_congruenceGL h_cong hJI h_large h_conj_le
  have h_isom : y.valᴴ * β * y.val = β := by simpa using h_form
  obtain ⟨w, hw⟩ := exists_ne (v₀ : InfinitePlace E)
  have h_pos : (β.map (Φ w)).PosDef := by simpa [hw] using h_pos_all w
  exact eq_one_of_conjTranspose_mul_mul_eq_of_trace_eq w h_pos h_isom h_trace

/-! ### Neat levels and freeness -/

variable (n 𝔑) in
/-- The level 𝔑 is neat: 𝔑 ≠ 0 and, whenever `x` is a signed frame with `ℓ` for some form
(`New.Variety.IsSignedFrame`), every y in GL_n(E) with x⁻¹yx in `levelGU n 𝔑` that fixes ℓ under
`New.Variety.ratConj` equals 1. -/
def IsNeat : Prop :=
  𝔑 ≠ 0 ∧
  ∀ {x : GL n (𝔸f E)} {ℓ : Matrix n n ℂ} {y : GL n E}, IsSignedFrame x ℓ →
    x⁻¹ * toFinGL y * x ∈ levelGU n 𝔑 → ratConj y ℓ = ℓ → y = 1

omit [Nonempty n] in
lemma IsNeat.ne_zero (h_neat : IsNeat n 𝔑) : 𝔑 ≠ 0 :=
  h_neat.1

omit [Nonempty n] in
/-- On a neat level automorphisms are trivial: if `x` is a signed frame with `ℓ`, and `y ∈ GL_n(E)`
has `x⁻¹ y x` in `levelGU n 𝔑` and fixes `ℓ` under `ratConj`, then `y = 1`. -/
lemma IsNeat.eq_one_of_mem_levelGU (h_neat : IsNeat n 𝔑) {x : GL n (𝔸f E)}
    {ℓ : Matrix n n ℂ} {y : GL n E} (hx : IsSignedFrame x ℓ)
    (h_level : x⁻¹ * toFinGL y * x ∈ levelGU n 𝔑) (hℓ : ratConj y ℓ = ℓ) : y = 1 :=
  h_neat.2 hx h_level hℓ

/-- Let `E` have a base place (`CMBase`, so at least two infinite places) and let `n` be nonempty.
For all but finitely many finite places `w` of `E`, every nonzero `𝔑 : 𝓞 E` that lies in `w` is a
neat level (`IsNeat n 𝔑`). -/
lemma eventually_isNeat :
    ∀ᶠ w : FinPlace E in Filter.cofinite, ∀ 𝔑 ≠ (0 : 𝓞 E), 𝔑 ∈ w.asIdeal → IsNeat n 𝔑 := by
  -- All but finitely many places have norm above `(2 * n) ^ [E : ℚ]`; there
  -- `IsSignedFrameFor.eq_one_of_congr_large_norm` applies.
  filter_upwards [(Northcott.finite_le (h := FinPlace.q)
    ((2 * Fintype.card n) ^ Module.finrank ℚ E)).compl_mem_cofinite] with w hw 𝔑 h𝔑 h𝔑w
  have hw_large : (2 * card n) ^ finrank ℚ E < w.q := not_le.1 hw
  refine ⟨h𝔑, fun {x ℓ y} h_signed h_level hℓ ↦ ?_⟩
  obtain ⟨β, hx⟩ := h_signed
  -- The level `𝔑` as an ideal of `Ô E`.
  let J : Ideal (Ô E) := span {algebraMap (𝓞 E) (Ô E) 𝔑}
  obtain ⟨-, h_cong_𝔑⟩ := Subgroup.mem_inf.1 h_level
  have h_algebraMap :
      algebraMap (Ô E) (𝔸f E) (algebraMap (𝓞 E) (Ô E) 𝔑) = algebraMap (𝓞 E) (𝔸f E) 𝔑 := rfl
  have h_cong : x⁻¹ * toFinGL y * x ∈
      congruenceGL (Submodule.map (Algebra.linearMap (Ô E) (𝔸f E)) J) id := by
    simpa [J, Submodule.map_span, h_algebraMap] using h_cong_𝔑
  -- An integer divisible by `𝔑` in `Ô E` is divisible by `𝔑` in `𝓞 E`, so lies in `w`.
  have hJI : under (𝓞 E) J ≤ w.asIdeal := fun a ha ↦
    mem_of_dvd _ ((dvd_iff_Ô h𝔑).1 (mem_span_singleton.1 ha)) h𝔑w
  exact hx.eq_one_of_congr_large_norm J (levelGU.isScalarFrame_inv_one h_level) h_cong hℓ hw_large
    hJI

omit [Nonempty n] Ψ

/-- Freeness for the definite space `stdSpace E n`: let `E` be a CM field with at least two infinite
places, and let the `w i` be distinct finite places whose norms have product above
`(2 * card n) ^ [E : ℚ]`. Let `γ` be a rational unitary element and `g` lie in G_f. If the conjugate
`g⁻¹ γ g` (with γ embedded in G_f) lies in the integral level `stdLevel E n`, which is
G_f ∩ GL_n(Ô E) (hypothesis `hk`), and reduces to `1` modulo every `w i`, then `γ = 1`. -/
lemma eq_one_of_reduceAt_eq_one {E : Type} [Field.{0} E] [CMType E] {w : ι → FinPlace E}
    [Nontrivial (InfinitePlace E)] (hw : w.Injective)
    (h_large : (2 * card n) ^ finrank ℚ E < ∏ i : ι, (w i).q)
    {γ : U (stdSpace E n).J} {g : Gf E n}
    (hk : g⁻¹ * (stdSpace E n).embFin γ * g ∈ stdLevel E n)
    (h_red : ∀ i : ι, stdLevel.reduceAt (w i) ⟨g⁻¹ * (stdSpace E n).embFin γ * g, hk⟩ = 1) :
    γ = 1 := by
  -- The number `tr (γ - 1) = tr (g⁻¹ γ g - 1)` lies in the product of the `w i`, and its conjugates
  -- have modulus at most `2 * card n`. Comparing norms shows that it is `0`, and then
  -- `tr (γ - 1)ᴴ (γ - 1) = 0`.
  let y : GL n E := γ
  have h_isom : y.valᴴ * (1 : Matrix n n E) * y.val = 1 := mem_U.1 γ.property
  have h_conj_le (v : InfinitePlace E) : ‖Φ v (y.val - 1).trace‖ ≤ 2 * card n := by
    -- The image of `y` under `Φ v` is unitary, so its entries have modulus at most `1`.
    have h_unitary : y.val.map (Φ v) ∈ unitaryGroup n ℂ := by
      simpa [mem_unitaryGroup_iff', star_eq_conjTranspose,
        ← conjTranspose_map (Φ v) (map_star_complex (Φ v))] using
        congrArg (fun A : Matrix n n E ↦ A.map (Φ v)) h_isom
    have h_entry (i : n) : ‖Φ v (y.val i i) - 1‖ ≤ 1 + 1 :=
      norm_sub_le_of_le (entry_norm_bound_of_unitary h_unitary i i) norm_one.le
    calc ‖Φ v (y.val - 1).trace‖
      _ = ‖∑ i : n, (Φ v (y.val i i) - 1)‖ := by simp [Matrix.trace]
      _ ≤ ∑ _i : n, (1 + 1 : ℝ) := norm_sum_le_of_le _ fun i _ ↦ h_entry i
      _ = 2 * card n := by simp [two_mul]
  -- The kernel `J` of reduction at all the `w i` meets `𝓞 E` in the product of the `w i`.
  let J : Ideal (Ô E) := ⨅ i : ι, ker (reduceAt (w i))
  have h_cong : g.val⁻¹ * toFinGL y * g.val ∈
      congruenceGL (Submodule.map (Algebra.linearMap (Ô E) (𝔸f E)) J) id := by
    rw [← stdSpace_embFin γ]
    -- The entries of `g⁻¹ γ g - 1` reduce to `0` at every `w a`, so they lie in `J`.
    refine ⟨hk, fun i j ↦ ?_⟩
    let k : intGL n (Ô E) := ⟨(g⁻¹ * (stdSpace E n).embFin γ * g).val, hk⟩
    have h_entry_mem : intGL.toMatrix k i j - intGL.toMatrix (1 : intGL n (Ô E)) i j ∈ J :=
      mem_iInf.2 fun a ↦ intGL.map_eq_one.1 (h_red a) i j
    exact Submodule.mem_map_of_mem h_entry_mem
  have h_under : under (𝓞 E) J ≤ ∏ i : ι, (w i).asIdeal := by
    simp [J, IsConcreteLE.le_iff, mem_prod_finPlace_iff hw]
  have h_trace : y.val.trace = card n :=
    trace_eq_card_of_mem_congruenceGL h_cong h_under (by rwa [map_prod]) h_conj_le
  obtain ⟨v⟩ : Nonempty (InfinitePlace E) := inferInstance
  have h_pos : ((1 : Matrix n n E).map (Φ v)).PosDef := by simpa using PosDef.one
  exact Subtype.ext (eq_one_of_conjTranspose_mul_mul_eq_of_trace_eq v h_pos h_isom h_trace)

/-- Let `E` be a CM field with at least two infinite places. Let the `w i` be distinct finite places
whose norms have product above `(2 * card n) ^ [E : ℚ]`. Let `K` be a subgroup of the finite adelic
unitary group `Gf E n` whose elements are integral and reduce to `1` modulo every `w i`. Then for
`g` in `Gf E n`, the stabiliser of the coset `g K` is trivial. The stabiliser is taken in the
unitary group over `E` of the definite form `stdSpace E n` (identity matrix, sum of norms of
coordinates), embedded in `Gf E n`. A case of Minkowski's lemma on integral matrices of finite
order. -/
lemma classAut_eq_bot {E : Type} [Field.{0} E] [CMType E] {w : ι → FinPlace E}
    [Nontrivial (InfinitePlace E)] (hw : w.Injective)
    (h_large : (2 * card n) ^ finrank ℚ E < ∏ i : ι, (w i).q)
    {K : Subgroup (Gf E n)} (hK : K ≤ levelOf w ⊥) (g : Gf E n) :
    classAut (stdSpace E n).Γf K g = ⊥ := by
  refine bot_unique ?_
  rintro _ ⟨⟨γ, rfl⟩, hγ⟩
  obtain ⟨hk, h_red⟩ := mem_levelOf.1 (hK hγ)
  simp [eq_one_of_reduceAt_eq_one hw h_large hk fun a ↦ congrFun h_red a]

end New.Variety

end NeatLevel

end
