import Lib.General.NumberTheory.CoefficientInclusion
import New.Congruences.Selmer.Descent
import New.Congruences.Selmer.StickelbergerLine
import New.Congruences.Selmer.Untied

/-!
# Restriction to a line

For Selmer data and Stickelberger systems there is an integer `s₀` such that, for each radius `r`
with `0 < r` and `s₀ r < 1` and each large `N`, we find auxiliary primes `𝔮` and, for each datum and
each system, a polynomial `P` in variables `X_𝔮`. At a point `x = (ζ_𝔮 - 1)_𝔮` given by `ℓ ^ N`-th
roots of unity, `v(P(x))` bounds the length of the twisted Selmer group of a datum `T` if it is less
than `β_T + 1`, and `P(x)` is the twisted value of a system. At some point with coordinates of
valuation at least `r`, the valuation of `P` is at most `β + s₀ r`, where `β` is the number of the
datum or system. For a datum this point is taken on the line `X_{𝔮₀} = Y`, `X_𝔮 = s_𝔮 Y`, where `𝔮₀`
is the first prime and the `s_𝔮` are the slopes of the datum at the other primes.

For a datum, `v(P(x))` is bounded by `v(P⁰(y)) + v(P¹(y))` at the point `x` of the line with
`Y = y`. Here `P⁰` is the restriction to the line of a minor for the tied module that is sharp at
`0`, so that `v(P⁰(0)) ≤ β_T`, the polynomial `P¹` bounds the failure to be tied, and `y` is generic
for both.

* `New.Selmer.SelmerDatum.TwistedLengthLe`: a bound for the length of the twisted Selmer group.
* `New.Selmer.SelmerDatum.exists_boundsSelmer_and_eval_dvd`,
  `New.Selmer.SelmerDatum.exists_boundsSelmer_ellVal_eval_le`: the choice of `P⁰`, of `y` and of the
  polynomial `P` of a datum.
* `New.Selmer.IsTorsionLevel`: the power `ℓ ^ M` modulo which the Selmer modules are computed.
* `New.Selmer.TwistPolynomials`, `New.Selmer.exists_twistPolynomials`: the primes, polynomials and
  points.

Letters: for a set of tied primes (`New.Selmer.IsTiedPrimes`), `J` is the set `Q` of all auxiliary
primes, `P₀ ∈ J` is the first prime `𝔮₀`, and `d` attaches to `v ∈ J` a Frobenius element, a tame
generator, the homomorphism `λ_v = (d v).1.character` to `ℤ / ℓ ^ N` and the slopes `(d v).2 i`.

Notions from other files:
* `New.selmerModule ρ S L B`: the locally constant cocycles for `ρ` with values in `B ^ n` that are
  unramified outside `S` and obey the linear relations `L`. The coefficients `B` are
  `New.QuotSpan a = O / a` or `New.Selmer.DivisibleQuot O = Frac(O) / O`.
* `New.Selmer.SelmerDatum`: a lattice `T` with local conditions and the number `β_T`;
  `New.Selmer.SelmerDatum.tiedSelmer` is its tied Selmer group.
* `New.Selmer.StickelbergerSystem`: elements `Θ_Q` of the group rings of class groups `Cl_Q` with a
  norm relation, and the number `β`.
* `New.CoeffRing`: rings of integers of finite Galois extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`;
  `New.CoeffRing.normLength` scales lengths so that `O / ℓ` has length `1`.

## Relation to the literature

See `New.Congruences.Selmer.TwistingTheorem` for related work.
-/

noncomputable section

namespace New.Selmer

section Levels

open Module Submodule Ideal IsDiscreteValuationRing

variable {O : Type} [CommRing O] [DVR O]
  {E n : Type} [Field E] [EmbeddedNumberField E] [Fintype n] [DecidableEq n]

/-- The Selmer group of locally constant cocycles for `ρ` that are unramified outside `S` and obey
`L`, with coefficients in `DivisibleQuot O = Frac(O) / O`, is a torsion module: a member `z` takes
finitely many values, so a common denominator kills it. -/
lemma exists_smul_eq_zero_of_mem_selmerModule (ρ : Gal(Ω/E) → Matrix n n O) (S : Set (FinPlace E))
    (L : Set (Gal(Ω/E) →₀ Matrix n n O)) (z : selmerModule ρ S L (DivisibleQuot O)) :
    ∃ a : O, a ≠ 0 ∧ a • z = 0 := by
  obtain ⟨z, hz⟩ := z
  choose d hd_ne hd using exists_smul_eq_zero_divisibleQuot (O := O)
  obtain ⟨-, -, -, h_const⟩ := mem_selmerModule_iff.1 hz
  -- The product of the denominators `d y` of all coordinates `y` of all values of `z`.
  let a : O := ∏ u ∈ h_const.range_finite.toFinset, ∏ i : n, d (u i)
  have ha : a ≠ 0 := by simp [a, Finset.prod_ne_zero_iff, hd_ne]
  have h_smul (g : Gal(Ω/E)) (i : n) : a • z g i = 0 := by
    obtain ⟨c, hc⟩ : d (z g i) ∣ a :=
      calc d (z g i) ∣ ∏ j : n, d (z g j) := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
        _ ∣ a := Finset.dvd_prod_of_mem (fun u : n → DivisibleQuot O ↦ ∏ j : n, d (u j)) (by simp)
    rw [hc, mul_comm, mul_smul, hd, smul_zero]
  exact ⟨a, ha, Subtype.ext (funext₂ h_smul)⟩

/-- Let `O` be a discrete valuation ring with valuation `v = addVal O` and let `a ∈ O` be nonzero.
Consider the Selmer groups of locally constant cocycles for `ρ` that are unramified outside `S` and
obey the relations `L`. If the group with coefficients in `QuotSpan a = O / a` has length less than
`v(a)`, then the group with coefficients in `DivisibleQuot O = Frac(O) / O` is no longer than it,
because `a` kills the second group. -/
lemma length_selmerModule_divisibleQuot_le (ρ : Gal(Ω/E) → Matrix n n O) (S : Set (FinPlace E))
    (L : Set (Gal(Ω/E) →₀ Matrix n n O)) {a : O} (ha : a ≠ 0)
    (h_lt : length O (selmerModule ρ S L (QuotSpan a)) < addVal O a) :
    length O (selmerModule ρ S L (DivisibleQuot O)) ≤
      length O (selmerModule ρ S L (QuotSpan a)) := by
  rw [← length_torsionBy_selmerModule_divisibleQuot ρ S L ha] at h_lt ⊢
  have h_top : torsionBy O (selmerModule ρ S L (DivisibleQuot O)) a = ⊤ := by_contra fun h_ne ↦
    h_lt.not_ge (addVal_le_length_torsionBy (exists_smul_eq_zero_of_mem_selmerModule ρ S L) h_ne)
  rw [h_top, length_top]

end Levels

open Finset Filter Module MvPolynomial Subalgebra

open scoped NNReal ENNReal NNRat

section Choice

variable {ℓ : ℕ} [ThePrime ℓ] {E : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
  {S₀ : Finset (FinPlace E)} {g₀ : Gal(Ω/E)}

namespace SelmerDatum

/-- The Selmer group `Sel_Q(T ψ)` modulo `a` of a Selmer datum `T`, for a character `ψ` with values
in a ring `O'` over `O` (by the map `e`): the cocycles in `T ψ ⊗ O' / a` that vanish at the element
`γ_* = T.γ`, are unramified outside `S ∪ Q ∪ Q̄`, where `S = T.places`, and satisfy the
local conditions of `T`. If `ψ(γ_*) = 1`, each class has exactly one cocycle that vanishes at
`γ_*`. -/
def twistedSelmer {O O' n : Type} [CommRing O] [PadicIntegerRing O ℓ] [CommRing O'] [Fintype n]
    [DecidableEq n] (T : SelmerDatum ℓ S₀ g₀ O n) (Q : Finset (FinPlace E)) (e : O →+* O')
    (ψ : Gal(Ω/E) →* O') (a : O') : Submodule O' (Gal(Ω/E) → n → QuotSpan a) :=
  selmerModule (twistRep e ψ T.ρ) (unionWithConj T.places Q) (mapRel e '' T.classRelations)
    (QuotSpan a)

/-- The Selmer group `Sel_Q(T ψ)` of a Selmer datum `T` with divisible coefficients, for a character
`ψ` with values in a discrete valuation ring `O'` over `O` (by the map `e`): the cocycles in
`T ψ ⊗ Frac(O') / O'` that vanish at `γ_* = T.γ`, are unramified outside `S ∪ Q ∪ Q̄`,
where `S = T.places`, and satisfy the local conditions of `T`. -/
def divisibleSelmer {O O' n : Type} [CommRing O] [PadicIntegerRing O ℓ] [CommRing O'] [DVR O']
    [Fintype n] [DecidableEq n] (T : SelmerDatum ℓ S₀ g₀ O n) (Q : Finset (FinPlace E))
    (e : O →+* O') (ψ : Gal(Ω/E) →* O') : Submodule O' (Gal(Ω/E) → n → DivisibleQuot O') :=
  selmerModule (twistRep e ψ T.ρ) (unionWithConj T.places Q) (mapRel e '' T.classRelations)
    (DivisibleQuot O')

/-- The length over `O'` of the Selmer group `Sel_Q(T ψ)` with coefficients in `Frac(O') / O'`. -/
def divisibleLength {O O' n : Type} [CommRing O] [PadicIntegerRing O ℓ] [CommRing O'] [DVR O']
    [Fintype n] [DecidableEq n] (T : SelmerDatum ℓ S₀ g₀ O n) (Q : Finset (FinPlace E))
    (e : O →+* O') (ψ : Gal(Ω/E) →* O') : ℕ∞ :=
  length O' (T.divisibleSelmer Q e ψ)

/-- For all large coefficient rings `O' ⊇ O`, the character `ψ` has values in `O'` and the group
`Sel_Q(T ψ)` with coefficients in `Frac(O') / O'` has length at most `b`, normalised by
`len O' / ℓ = 1`. -/
def TwistedLengthLe {O : CoeffRing ℓ} {n : Type} [Fintype n] [DecidableEq n]
    (T : SelmerDatum ℓ S₀ g₀ O.val n) (Q : Finset (FinPlace E)) (ψ : Gal(Ω/E) →* PadicAlgCl ℓ)
    (b : ℝ≥0∞) : Prop :=
  ∀ᶠ O' : CoeffRing ℓ in atTop, ∃ hO : O ≤ O', ∃ ψ' : Gal(Ω/E) →* O'.val,
    (∀ g : Gal(Ω/E), (ψ' g : PadicAlgCl ℓ) = ψ g) ∧
    O'.normLength (T.divisibleLength Q (inclusion hO).toRingHom ψ') ≤ b

/-- A bound for the length of the twisted Selmer group may be weakened. -/
lemma TwistedLengthLe.mono {O : CoeffRing ℓ} {n : Type} [Fintype n] [DecidableEq n]
    {T : SelmerDatum ℓ S₀ g₀ O.val n} {Q : Finset (FinPlace E)} {ψ : Gal(Ω/E) →* PadicAlgCl ℓ}
    {b b' : ℝ≥0∞} (h : T.TwistedLengthLe Q ψ b) (hb : b ≤ b') : T.TwistedLengthLe Q ψ b' := by
  filter_upwards [h] with O' ⟨hO, ψ', hψ', h_le⟩ using ⟨hO, ψ', hψ', h_le.trans hb⟩

end SelmerDatum

open IsDiscreteValuationRing Polynomial

open scoped Classical in
/-- Let `d` attach to each prime `w` a tame generator `γ_w` and a Frobenius element `φ_w` (first
component) and slopes `s` indexed by `ι` (second component). The ties `z(γ_w) = s • z(φ_w)` with the
slopes of index `i`, as relations by `n × n` matrices, at the primes of `I ∪ I'` are the ties at
the primes of `I` together with those at the primes of `I'`. -/
lemma tieRelations_union {O n ι : Type} [CommRing O] [Fintype n] [DecidableEq n] {q : ℕ}
    (I I' : Finset (FinPlace E)) (d : FinPlace E → AuxPrimeData E q × (ι → O)) (i : ι) :
    tieRelations (n := n) (I ∪ I') d i = tieRelations I d i ∪ tieRelations I' d i := by
  ext f
  simp only [tieRelations, Set.mem_union, Set.mem_range, Prod.exists, Subtype.exists, mem_union,
    exists_prop, or_and_right, exists_or]

/-- The polynomial `P` bounds the length of `Sel(x)`, the Selmer module modulo `ℓ ^ M` of the twist
of `ρ` by `ψ_x(g) = ∏ (1 + x_j) ^ (h_j g)`: we have `len Sel(x) ≤ v(P(x))` at all points `x` over
all discrete valuation rings of characteristic zero over `O`, not only where `ψ_x` is a
character. -/
def BoundsSelmer (ℓ : ℕ) {E : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
    {O n σ : Type} [CommRing O] [Fintype n] [DecidableEq n] [Fintype σ] {q : ℕ} (M : ℕ)
    (h : σ → Gal(Ω/E) →* Multiplicative (ZMod q)) (ρ : Gal(Ω/E) →* Matrix n n O)
    (S : Set (FinPlace E)) (L : Set (Gal(Ω/E) →₀ Matrix n n O)) (P : MvPolynomial σ O) : Prop :=
  ∀ (O' : Type) [CommRing O'] [DVR O'] [CharZero O'] (e : O →+* O') (x : σ → O'),
    length O' (selmerAtPoint ℓ M h ρ S L e x) ≤ addVal O' (P.eval₂ e x)

/-- The restriction of a polynomial to the line `X_j = a_j Y`. -/
def restrictToLine {O σ : Type} [CommRing O] (a : σ → O) (P : MvPolynomial σ O) : O[X] :=
  MvPolynomial.aeval (fun j : σ ↦ Polynomial.C (a j) * Polynomial.X) P

/-- The value at `y` of the restriction of `P` to the line `X_j = a_j Y` is the value of `P` at the
point `(a_j y)_j`, with coefficients mapped by `e`. -/
lemma eval₂_restrictToLine {O O' σ : Type} [CommRing O] [CommRing O'] (a : σ → O)
    (P : MvPolynomial σ O) (e : O →+* O') (y : O') :
    (restrictToLine a P).eval₂ e y = P.eval₂ e fun j : σ ↦ e (a j) * y := by
  induction P using MvPolynomial.induction_on <;> simp_all [restrictToLine]

/-- Let `d` attach a Frobenius element `φ_v` to each prime `v`, and let `P¹ = tiePolynomial ρ I d`
be the product of the polynomials `det ((1 + Y) ρ(g) - 1)` over `g = φ_v` and its conjugate inverse
`g = φ_v^{-c}` for `v ∈ I`. If `2 n #I ≤ s₀`, where `n` is the rank of `ρ`, then the Gauss valuation
of radius `r` satisfies `v_r(P¹) ≤ s₀ r`, because each of the `2 #I` factors has a unit coefficient
in degree `n`. -/
lemma gaussVal_tiePolynomial_le {O n ι : Type} [CommRing O] [Fintype n] [DecidableEq n] {q : ℕ}
    (ρ : Gal(Ω/E) →* Matrix n n O) (I : Finset (FinPlace E))
    (d : FinPlace E → AuxPrimeData E q × (ι → O)) (f : O →+* intQpBar ℓ) (r : ℚ≥0) {s₀ : ℕ}
    (hs₀ : 2 * Fintype.card n * #I ≤ s₀) :
    gaussVal r ((tiePolynomial ρ I d).map f) ≤ s₀ * (r : ℝ≥0) := by
  have h_factor (g : Gal(Ω/E)) :
      gaussVal r ((shiftedDet (ρ g)).map f) ≤ (r : ℝ≥0) * (Fintype.card n : ℝ≥0∞) := by
    refine gaussVal_le_of_isUnit_coeff ?_
    rw [Polynomial.coeff_map, coeff_shiftedDet_card]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 ((Group.isUnit g).map ρ)).map f
  -- The Frobenius element at the prime `v` of `I`, or its conjugate inverse.
  let φ : I × Bool → Gal(Ω/E) := fun (v, b) ↦ idOrConjInv b (d v).1.frob
  have h_prod : tiePolynomial ρ I d = ∏ p : I × Bool, shiftedDet (ρ (φ p)) := rfl
  calc gaussVal r ((tiePolynomial ρ I d).map f)
    _ ≤ ∑ _p : I × Bool, (r : ℝ≥0) * (Fintype.card n : ℝ≥0∞) := by
      rw [h_prod, Polynomial.map_prod, gaussVal_prod]
      exact sum_le_sum fun p _ ↦ h_factor (φ p)
    _ = (2 * Fintype.card n * #I : ℕ) * (r : ℝ≥0) := by simp [mul_assoc, mul_comm, mul_left_comm]
    _ ≤ s₀ * (r : ℝ≥0) := by gcongr

omit [NumberField.IsCMField E] in
/-- Let `λ_j = lam j` be homomorphisms to `ℤ / q` and `ζ_j` be `q`-th roots of unity. The twist of
`ρ` by the character `g ↦ ∏ ζ_j ^ (λ_j g)` is the twist by the value of
`ψ_X(g) = ∏ (1 + X_j) ^ (λ_j g)` at the point `x = (ζ_j - 1)_j`. -/
lemma coe_twistRep_pointChar {O O' n σ : Type} [CommRing O] [CommRing O'] [Fintype n]
    [DecidableEq n] [Fintype σ] {q : ℕ} [NeZero q] (lam : σ → Gal(Ω/E) →* Multiplicative (ZMod q))
    {ζ : σ → O'} (hζ : ∀ j : σ, ζ j ^ q = 1) (e : O →+* O') (ρ : Gal(Ω/E) →* Matrix n n O) :
    ⇑(twistRep e (pointChar lam ζ hζ) ρ) = pointTwist lam (fun j : σ ↦ ζ j - 1) e ρ := by
  ext1 g
  simp [twistRep, pointTwist, eval_universalChar]

namespace SelmerDatum

variable {ι n : Type} [Fintype n] [DecidableEq n] {V : ι → Gal(Ω/E) → Prop} {W : Set Gal(Ω/E)}
  {J : Finset (FinPlace E)} {M N s₀ : ℕ} {P₀ : FinPlace E} {r : ℚ≥0}

/-- The action on the lattice of a Selmer datum `T`, reduced modulo `ℓ ^ M`, is trivial on the
inertia groups above the places outside `S₀`. -/
lemma reduceModPow_eq_one {O : Type} [CommRing O] [PadicIntegerRing O ℓ]
    (T : SelmerDatum ℓ S₀ g₀ O n) {g : Gal(Ω/E)} (hg : g ∈ inertiaAbove S₀ᶜ) :
    reduceModPow ℓ M T.ρ g = 1 := by
  obtain ⟨v, hv, hg_v⟩ := hg
  simp [reduceModPow, T.unramified g ⟨v, fun h_mem ↦ hv (T.subset h_mem), hg_v⟩]

open scoped Classical in
/-- Let `J` be a set of tied primes (`IsTiedPrimes`): auxiliary primes with a first prime `P₀ ∈ J`,
whose Frobenius element `(d P₀).1.frob` lies in `W`, and with Frobenius elements `φ_w`, tame
generators `γ_w` and slopes given by `d`. Let `M < N`. Suppose that the elements with the property
`V i` act trivially on `T` modulo `ℓ ^ M`, and that the Frobenius element of `P₀` and its conjugate
inverse act modulo `ℓ ^ M` as `g₀` and `g₀^{-c}` (`idOrConjInv`). If the Selmer group modulo `ℓ ^ M`
tied at all primes of `J` has length at most `globalTerm + placesTerm`, then the group tied only at
the primes other than `P₀` has length at most `β_T = globalTerm + placesTerm + firstPrimeTerm`. -/
lemma length_tiedSelmer_erase_le {O : Type} [CommRing O] [PadicIntegerRing O ℓ]
    (T : SelmerDatum ℓ S₀ g₀ O n) {d : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)}
    (h_primes : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hMN : M < N) (i : ι)
    (hV : ∀ g : Gal(Ω/E), V i g → reduceModPow ℓ M T.ρ g = 1)
    (h_first : ∀ b : Bool, reduceModPow ℓ M T.ρ (idOrConjInv b (d P₀).1.frob) =
      reduceModPow ℓ M T.ρ (idOrConjInv b g₀))
    (h_tied : length O (T.tiedSelmer J J d i (ℓ ^ M)) ≤ T.globalTerm + T.placesTerm) :
    length O (T.tiedSelmer J (J.erase P₀) d i (ℓ ^ M)) ≤ T.β := by
  let Z := T.tiedSelmer J J d i (ℓ ^ M)
  let Z₀ := T.tiedSelmer J (J.erase P₀) d i (ℓ ^ M)
  -- Dropping the ties at `P₀` and its conjugate costs at most `T.firstPrimeTerm`.
  have h_release : relLength Z₀ Z ≤ T.firstPrimeTerm := by
    have h_ties : tieRelations (n := n) J d i =
        tieRelations (J.erase P₀) d i ∪ tieRelations {P₀} d i := by
      rw [← tieRelations_union, union_comm, ← insert_eq, insert_erase h_primes.first_mem]
    simp only [Z₀, Z, tiedSelmer, h_ties, ← Set.union_assoc]
    exact h_primes.relLength_tieRelations_le_sum_addVal_det (Nat.ne_zero_of_lt hMN) i
      (fun _ hg ↦ T.reduceModPow_eq_one hg) hV hMN.le h_first (unionWithConj T.places J)
      (T.classRelations ∪ tieRelations (J.erase P₀) d i)
  calc length O Z₀
    _ = relLength Z₀ Z + length O ↥(Z₀ ⊓ Z) := (relLength_add_length_inf Z₀ Z).symm
    _ ≤ T.firstPrimeTerm + (T.globalTerm + T.placesTerm) :=
      add_le_add h_release ((length_mono inf_le_right).trans h_tied)
    _ = T.β := by rw [β, localTerms, add_comm, add_assoc]

open scoped Classical in
/-- Let `O` be the ring of integers of a finite extension of `ℚ_ℓ` and `T` a Selmer datum: a lattice
`O ^ n` with an action `ρ` of `Gal(Ω/E)`, unramified outside `T.places ⊆ S₀`, with the relations
`T.classRelations`. Its number `β_T = T.β` is the sum of a global term, local terms at `T.places`
and a term for the element `g₀`. Let `J` be a set of auxiliary primes with first prime `P₀`
(`IsTiedPrimes`), where `d` gives each `v ∈ J` a Frobenius element `φ_v`, a tame generator `γ_v`, a
character to `ℤ / ℓ ^ N` and the slope `s_v = (d v).2 i` for the index `i` of `T`. A cocycle `z` is
tied at `v` if `z(γ_v) = s_v • z(φ_v)`, and likewise at the conjugate prime. Let `T` modulo `ℓ ^ M`
be trivial at the elements with the property `V i`, and let `N ≠ 0`, `r ≤ 1` and `M ≤ N r`. Suppose
that the Selmer group of `T` modulo `ℓ ^ M` that is tied at the primes of `J` other than `P₀` has
length at most `β_T`. Then there is a polynomial `P⁰ = lineBound` with `v(P⁰(0)) ≤ β_T` and the
following property. Let `e : O → O'` be a discrete valuation ring of characteristic zero over `O`
with a map `f` to `ℤ̄_ℓ = intQpBar ℓ` that reflects divisibility, let `y ∈ O'` with
`ellVal (f y) ≥ r`, and let `x = (a_v y)_{v ∈ J}`, where `a = lineDirection P₀ J d i` has
`a_{P₀} = 1` and `a_v = s_v` otherwise. Then some polynomial `P` bounds the length of the Selmer
module of the characters `(d v).1.character` at all points (`BoundsSelmer`), and `P(x)` divides
`P⁰(y) P¹(y)` in `ℤ̄_ℓ`. Here `P¹ = tiePolynomial` is the product of the `det ((1 + Y) ρ(g) - 1)`
over the Frobenius elements `g = φ_v` of the primes `v` of `J` other than `P₀` and their conjugate
inverses. -/
lemma exists_boundsSelmer_and_eval_dvd {O : Type} [CommRing O] [PadicIntegerRing O ℓ]
    (T : SelmerDatum ℓ S₀ g₀ O n) {d : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O)}
    (h_primes : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN₀ : N ≠ 0) (i : ι)
    (hV : ∀ g : Gal(Ω/E), V i g → reduceModPow ℓ M T.ρ g = 1)
    (h_tied : length O (T.tiedSelmer J (J.erase P₀) d i (ℓ ^ M)) ≤ T.β) (hr : r ≤ 1)
    (hN : M ≤ N * r) :
    ∃ lineBound : O[X], addVal O (lineBound.coeff 0) ≤ T.β ∧
      ∀ (O' : Type) [CommRing O'] [DVR O'] [CharZero O'] (e : O →+* O') (f : O' →+* intQpBar ℓ)
        (y : O') (_hf_reflects : ∀ z z' : O', f z ∣ f z' → z ∣ z')
        (_hy_val : (r : ℝ≥0) ≤ ellVal (f y).val),
        ∃ P : MvPolynomial J O,
          BoundsSelmer ℓ M (fun v : J ↦ (d v).1.character) T.ρ (unionWithConj T.places J)
            T.classRelations P ∧
          MvPolynomial.eval (fun v : J ↦ f.comp e (lineDirection P₀ J d i v) * f y)
              (P.map (f.comp e)) ∣
            (lineBound.map (f.comp e)).eval (f y) *
              ((tiePolynomial T.ρ (J.erase P₀) d).map (f.comp e)).eval (f y) := by
  let lam (v : J) : Gal(Ω/E) →* Multiplicative (ZMod (ℓ ^ N)) := (d v).1.character
  let S : Set (FinPlace E) := unionWithConj T.places J
  let L₀ : Set (Gal(Ω/E) →₀ Matrix n n O) := T.classRelations ∪ tieRelations (J.erase P₀) d i
  let a : J → O := lineDirection P₀ J d i
  have h_lam (v : J) : IsLocallyConstant (lam v) :=
    (h_primes.isAuxPrimeDataAt v v.2).isLocallyConstant
  -- A polynomial `G` for the tied module that is sharp at `0`; `P⁰` is its restriction to the line.
  obtain ⟨G, hG_sharp, hG_bound⟩ : ∃ G : MvPolynomial J O,
      addVal O (G.eval₂ (.id O) fun _ ↦ 0) =
        length O (selmerAtPoint ℓ M lam T.ρ S L₀ (.id O) fun _ ↦ 0) ∧
      BoundsSelmer ℓ M lam T.ρ S L₀ G :=
    exists_sharp_polynomial h_lam (T.isLocallyConstant M) (finite_toSet _) L₀ (.id O) fun _ ↦ 0
  refine ⟨restrictToLine a G, ?_, fun O' _ _ _ e f y hf_reflects hy_val ↦ ?_⟩
  · have h_zero : (restrictToLine a G).coeff 0 = G.eval₂ (.id O) fun _ ↦ 0 := by
      simpa using eval₂_restrictToLine a G (.id O) 0
    rwa [h_zero, hG_sharp, selmerAtPoint_zero]
  -- A polynomial `P` for the module without ties that is sharp at the point `x` of the line.
  let x (v : J) : O' := e (a v) * y
  let Sel (L : Set (Gal(Ω/E) →₀ Matrix n n O)) :
      Submodule O' (Gal(Ω/E) → n → QuotSpan (ℓ ^ M : O')) := selmerAtPoint ℓ M lam T.ρ S L e x
  obtain ⟨P, hP_sharp, hP_bound⟩ : ∃ P : MvPolynomial J O,
      addVal O' (P.eval₂ e x) = length O' (Sel T.classRelations) ∧
      BoundsSelmer ℓ M lam T.ρ S T.classRelations P :=
    exists_sharp_polynomial h_lam (T.isLocallyConstant M) (finite_toSet _) T.classRelations e x
  have h_norm (α : O') (hα : y ∣ α - 1) : (ℓ ^ M : O') ∣ ∑ j ∈ range (ℓ ^ N), α ^ j :=
    pow_dvd_geom_sum f hf_reflects hr hN (hy_val.trans (dvd_iff_ellVal_le.1 (map_dvd f hα)))
  have h_untie : relLength (Sel T.classRelations) (Sel L₀) ≤
      addVal O' ((tiePolynomial T.ρ (J.erase P₀) d).eval₂ e y) :=
    h_primes.relLength_tied_le hN₀ i (fun _ ↦ T.reduceModPow_eq_one) hV e h_norm S T.classRelations
  have h_dvd : P.eval₂ e x ∣
      (restrictToLine a G).eval₂ e y * (tiePolynomial T.ρ (J.erase P₀) d).eval₂ e y := by
    rw [← addVal_le_iff_dvd, addVal_mul, eval₂_restrictToLine, hP_sharp,
      ← relLength_add_length_inf (Sel T.classRelations) (Sel L₀), add_comm]
    exact add_le_add ((length_mono inf_le_right).trans (hG_bound O' e x)) h_untie
  -- The claim is the image of `h_dvd` under `f`.
  refine ⟨P, hP_bound, ?_⟩
  simpa only [map_mul, Polynomial.hom_eval₂, MvPolynomial.eval₂_comp_left, Polynomial.eval_map,
    MvPolynomial.eval_map, Function.comp_def, RingHom.comp_apply, x, a] using map_dvd f h_dvd

/-- Let `P` bound, at all points `x`, the length of the Selmer module `Sel(x)` modulo `ℓ ^ M` of the
twist of `T` at `x`, unramified outside `S ∪ J ∪ J̄` and with the relations `T.classRelations`
(`BoundsSelmer`), for characters `λ_v = lam v` to `ℤ / q`. Let `e : O → O'` be a ring map to a
discrete valuation ring `O'` of characteristic zero, with valuation `v = addVal O'`, and let the
`ζ_v ∈ O'` be `q`-th roots of unity. At `x = (ζ_v - 1)_v` the module `Sel(x)` is the Selmer group
`Sel_J(T ψ)` modulo `ℓ ^ M` for `ψ = ∏ ζ_v ^ λ_v` (`pointChar`). So if `v(P(x)) < v(ℓ ^ M)`, where
`P(x)` is `P` evaluated through `e`, then `v(P(x))` bounds the length of `Sel_J(T ψ)` with
coefficients in `Frac(O') / O'` (`divisibleLength`). -/
lemma divisibleLength_pointChar_le {O : Type} [CommRing O] [PadicIntegerRing O ℓ]
    (T : SelmerDatum ℓ S₀ g₀ O n) {σ O' : Type} [Fintype σ] [CommRing O'] [DVR O'] [CharZero O']
    {q : ℕ} [NeZero q] {lam : σ → Gal(Ω/E) →* Multiplicative (ZMod q)} {P : MvPolynomial σ O}
    (hP : BoundsSelmer ℓ M lam T.ρ (unionWithConj T.places J) T.classRelations P) (e : O →+* O')
    {ζ : σ → O'} (hζ : ∀ v : σ, ζ v ^ q = 1)
    (h_lt : addVal O' (P.eval₂ e fun v : σ ↦ ζ v - 1) < addVal O' (ℓ ^ M)) :
    T.divisibleLength J e (pointChar lam ζ hζ) ≤
      addVal O' (P.eval₂ e fun v : σ ↦ ζ v - 1) := by
  have h_level : length O' (T.twistedSelmer J e (pointChar lam ζ hζ) (ℓ ^ M)) ≤
      addVal O' (P.eval₂ e fun v ↦ ζ v - 1) := by
    rw [twistedSelmer, coe_twistRep_pointChar]
    exact hP O' e _
  rw [twistedSelmer] at h_level
  exact (length_selmerModule_divisibleQuot_le _ _ _ (NeZero.ne _)
    (h_level.trans_lt h_lt)).trans h_level

open scoped Classical in
/-- The choice of the polynomial `P` of a Selmer datum `T` over a coefficient ring `O`, the ring of
integers of a finite Galois extension of `ℚ_ℓ`, included in `ℤ̄_ℓ` by `O.toIntQpBar`. The datum is
a lattice `O ^ n` with Galois action, unramified outside `T.places ⊆ S₀`, with the relations
`T.classRelations` (local conditions above `ℓ` and vanishing at `T.γ`); `β_T = T.β` is the sum of a
global term, local terms at `T.places` and a term for the element `g₀`. Let `J` be a set of
auxiliary primes with first prime `P₀` (`IsTiedPrimes`), where `d` gives each `w ∈ J` a Frobenius
element `φ_w`, a tame generator `γ_w`, a character to `ℤ / ℓ ^ N` and the slope `s_w = (d w).2 i`
for the index `i` of `T`; a cocycle `z` is tied at `w` if `z(γ_w) = s_w • z(φ_w)`, and likewise at
the conjugate prime. Let `T` modulo `ℓ ^ M` be trivial at the elements with the property `V i`, and
let `N ≠ 0`, `2 rank(T) #J ≤ s₀`, `r ≤ 1` and `M ≤ N r`. If the Selmer group modulo `ℓ ^ M` that is
tied at the primes of `J` other than `P₀` has length at most `β_T`, then some `P` bounds the length
of the Selmer module of these characters at all points (`BoundsSelmer`), and
`v(P(x₀)) ≤ β_T + s₀ r` at a point `x₀` over `ℤ̄_ℓ` whose coordinates have valuation at least `r`.
Here `v = ellVal` has `v(ℓ) = 1`, and `normLength` multiplies the length `β_T` by the valuation of a
uniformiser of `O`. -/
theorem exists_boundsSelmer_ellVal_eval_le {O : CoeffRing ℓ} (T : SelmerDatum ℓ S₀ g₀ O.val n)
    {d : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O.val)}
    (h_primes : IsTiedPrimes ℓ S₀ V W N P₀ J d) (hN₀ : N ≠ 0) (i : ι)
    (hV : ∀ g : Gal(Ω/E), V i g → reduceModPow ℓ M T.ρ g = 1)
    (h_tied : length O.val (T.tiedSelmer J (J.erase P₀) d i (ℓ ^ M)) ≤ T.β)
    (hs₀ : 2 * Fintype.card n * #J ≤ s₀) (hr : r ≤ 1) (hN : M ≤ N * r) :
    ∃ (P : MvPolynomial J O.val) (x₀ : J → intQpBar ℓ),
      (∀ v : J, (r : ℝ≥0) ≤ ellVal (x₀ v).val) ∧
      ellVal (MvPolynomial.eval x₀ (P.map O.toIntQpBar)).val ≤
        O.normLength T.β + s₀ * (r : ℝ≥0) ∧
      BoundsSelmer ℓ M (fun v : J ↦ (d v).1.character) T.ρ (unionWithConj T.places J)
        T.classRelations P := by
  -- Take `x₀` on the line at a parameter `y` that is generic for `p₀ = P⁰` and `p₁ = P¹`: they
  -- attain their Gauss valuations of radius `r` at `y`. Then `v(P(x₀)) ≤ v_r(P⁰) + v_r(P¹)`.
  obtain ⟨lineBound, h_coeff_zero, h_bound_dvd⟩ :=
    T.exists_boundsSelmer_and_eval_dvd h_primes hN₀ i hV h_tied hr hN
  set p₀ : (intQpBar ℓ)[X] := lineBound.map O.toIntQpBar with hp₀
  set p₁ : (intQpBar ℓ)[X] := (tiePolynomial T.ρ (J.erase P₀) d).map O.toIntQpBar with hp₁
  have h_zero : ellVal (p₀.eval 0).val ≤ O.normLength T.β := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, hp₀, Polynomial.coeff_map, CoeffRing.coe_toIntQpBar,
      ← CoeffRing.normLength_addVal]
    exact CoeffRing.normLength_mono h_coeff_zero
  have h_tie : gaussVal r p₁ ≤ s₀ * (r : ℝ≥0) :=
    gaussVal_tiePolynomial_le T.ρ _ d O.toIntQpBar r
      ((Nat.mul_le_mul_left _ card_erase_le).trans hs₀)
  obtain ⟨y, hy, h_generic⟩ := exists_forall_ellVal_eval_eq_gaussVal r ![p₀, p₁]
  have hy₀ : ellVal (p₀.eval y).val = gaussVal r p₀ := h_generic 0
  have hy₁ : ellVal (p₁.eval y).val = gaussVal r p₁ := h_generic 1
  obtain ⟨O', hO, hy_mem⟩ := ((eventually_ge_atTop O).and (CoeffRing.eventually_mem y.2)).exists
  let y' : O'.val := ⟨y, hy_mem⟩
  have hy' : O'.toIntQpBar y' = y := rfl
  let x₀ (v : J) : intQpBar ℓ := O.toIntQpBar (lineDirection P₀ J d i v) * y
  obtain ⟨P, hP, h_dvd⟩ : ∃ P : MvPolynomial J O.val,
      BoundsSelmer ℓ M (fun v : J ↦ (d v).1.character) T.ρ (unionWithConj T.places J)
        T.classRelations P ∧
      MvPolynomial.eval x₀ (P.map O.toIntQpBar) ∣ p₀.eval y * p₁.eval y := by
    simpa only [CoeffRing.toIntQpBar_comp_inclusion, hy', ← hp₀, ← hp₁] using h_bound_dvd O'.val
      (inclusion hO).toRingHom O'.toIntQpBar y' O'.dvd_of_toIntQpBar_dvd (by rwa [hy'])
  refine ⟨P, x₀, fun v ↦ hy.trans (dvd_iff_ellVal_le.1 (dvd_mul_left y _)), ?_, hP⟩
  calc
    _ ≤ ellVal (p₀.eval y).val + ellVal (p₁.eval y).val := by
      simpa only [ellVal_val_mul] using dvd_iff_ellVal_le.1 h_dvd
    _ = gaussVal r p₀ + gaussVal r p₁ := by rw [hy₀, hy₁]
    _ ≤ O.normLength T.β + s₀ * (r : ℝ≥0) :=
      add_le_add ((gaussVal_le_eval_zero p₀).trans h_zero) h_tie

/-- Let `T` be a Selmer datum over a coefficient ring `O`, for the set `S₀` of places and the
element `g₀`: a lattice with Galois action, unramified outside `S = T.places ⊆ S₀`. Let `P` bound,
at all points, the length of the Selmer module modulo `ℓ ^ M` of the twist of `T` by the characters
`λ_v = lam v` to `ℤ / q`, unramified outside `S ∪ J ∪ J̄` and with the relations `T.classRelations`,
the local conditions above `ℓ` and vanishing at `T.γ` (`BoundsSelmer`). Let the `ζ_v ∈ ℤ̄_ℓ` be
`q`-th roots of unity, `x = (ζ_v - 1)_v` and `ψ = ∏ ζ_v ^ λ_v` (`pointChar`). If `v(P(x)) < M`,
where `v = ellVal` has `v(ℓ) = 1`, then over all large coefficient rings the normalised length of
`Sel_J(T ψ)` with divisible coefficients is at most `v(P(x))` (`TwistedLengthLe`). -/
lemma twistedLengthLe_pointChar {O : CoeffRing ℓ} (T : SelmerDatum ℓ S₀ g₀ O.val n)
    {σ : Type} [Fintype σ] {q : ℕ} [NeZero q]
    {lam : σ → Gal(Ω/E) →* Multiplicative (ZMod q)} {P : MvPolynomial σ O.val}
    (hP : BoundsSelmer ℓ M lam T.ρ (unionWithConj T.places J) T.classRelations P)
    (ζ : σ → intQpBar ℓ) (hζ : ∀ v : σ, (ζ v : PadicAlgCl ℓ) ^ q = 1)
    (h_lt : ellVal (MvPolynomial.eval (fun v : σ ↦ ζ v - 1) (P.map O.toIntQpBar)).val < M) :
    T.TwistedLengthLe J (pointChar lam (fun v : σ ↦ (ζ v : PadicAlgCl ℓ)) hζ)
      (ellVal (MvPolynomial.eval (fun v : σ ↦ ζ v - 1) (P.map O.toIntQpBar)).val) := by
  filter_upwards [eventually_ge_atTop O, CoeffRing.eventually_exists_toIntQpBar_eq ζ]
    with O' hO ⟨ζ', hζ'⟩
  obtain rfl : (fun v ↦ O'.toIntQpBar (ζ' v)) = ζ := funext hζ'
  have hζ'_pow (v : σ) : ζ' v ^ q = 1 := Subtype.ext (by simpa using hζ v)
  let value : O'.val := P.eval₂ (inclusion hO).toRingHom fun v ↦ ζ' v - 1
  have h_val : O'.normLength (addVal O'.val value) =
      ellVal (MvPolynomial.eval (fun v ↦ O'.toIntQpBar (ζ' v) - 1) (P.map O.toIntQpBar)).val := by
    simp only [value, CoeffRing.normLength_addVal_eval₂ hO, map_sub, map_one]
  have h_level : O'.normLength (addVal O'.val (ℓ ^ M)) = M := by simp
  have h_lt' : addVal O'.val value < addVal O'.val (ℓ ^ M) :=
    (CoeffRing.normLength_mono (O := O')).reflect_lt (by rwa [h_val, h_level])
  have h_len : T.divisibleLength J (inclusion hO).toRingHom (pointChar lam ζ' hζ'_pow) ≤
      addVal O'.val value :=
    T.divisibleLength_pointChar_le hP _ hζ'_pow h_lt'
  -- The character with values in `O'` has the given values in `ℚ̄_ℓ`.
  exact ⟨hO, pointChar lam ζ' hζ'_pow, fun g ↦ by simp,
    (CoeffRing.normLength_mono h_len).trans_eq h_val⟩

end SelmerDatum

end Choice

variable {ℓ : ℕ} [ThePrime ℓ] {E : Type} [Field E] [EmbeddedNumberField E] [NumberField.IsCMField E]
  {S₀ : Finset (FinPlace E)} {g₀ : Gal(Ω/E)}

/-- For `g` near `g₀`, the element `g` (for `b = true`) or its conjugate inverse `g^{-c}` (for
`b = false`) acts on the lattice of a Selmer datum `T` modulo `ℓ ^ M` as `g₀` or `g₀^{-c}` does. -/
lemma SelmerDatum.eventually_reduceModPow_idOrConjInv_eq {O n : Type} [CommRing O]
    [PadicIntegerRing O ℓ] [Fintype n] [DecidableEq n] (T : SelmerDatum ℓ S₀ g₀ O n) (M : ℕ)
    (b : Bool) :
    ∀ᶠ g : Gal(Ω/E) in nhds g₀,
      reduceModPow ℓ M T.ρ (idOrConjInv b g) = reduceModPow ℓ M T.ρ (idOrConjInv b g₀) := by
  have h_cont : Continuous (idOrConjInv b : Gal(Ω/E) → Gal(Ω/E)) := by
    cases b
    exacts [continuous_conjGal.inv, continuous_id]
  exact ((T.isLocallyConstant M).comp_continuous h_cont).eventually_eq g₀

variable {ι κ : Type} {n : ι → Type} [∀ i : ι, Fintype (n i)] [∀ i : ι, DecidableEq (n i)]
  {O : CoeffRing ℓ}

/-- `ℓ ^ M` is a suitable level of torsion for the Selmer data `T i`: the exponent `M` exceeds the
normalised numbers `β_T` by more than `1`, and the residue field of `O` is large. -/
structure IsTorsionLevel (T : ∀ i : ι, SelmerDatum ℓ S₀ g₀ O.val (n i)) (M : ℕ) : Prop where
  /-- `M > β_T + 1` for each datum, with `β_T` scaled so that `O / ℓ` has length `1`. -/
  β_lt (i : ι) : O.normLength (T i).β + 1 < M
  /-- The residue field has more than `2 rank(T i) len(O / ℓ ^ M) + 1` elements, which leaves room
  for the choice of slopes. -/
  lt_card_residueField (i : ι) :
    2 * Fintype.card (n i) * IsDiscreteValuationRing.addVal O.val (ℓ ^ M) + 1 <
      Nat.card (IsLocalRing.ResidueField O.val)

/-- Auxiliary primes, homomorphisms to `ℤ / ℓ ^ N`, and polynomials with points for Selmer data
`T i` and Stickelberger systems `Y k`, for an integer `s₀` and a radius `r`. Valuations are those
of `ellVal`, with `v(ℓ) = 1`. -/
structure TwistPolynomials (T : ∀ i : ι, SelmerDatum ℓ S₀ g₀ O.val (n i))
    (Y : κ → StickelbergerSystem ℓ S₀ g₀) (s₀ : ℕ) (r : ℚ≥0) (N : ℕ) where
  /-- The set `Q` of primes. -/
  auxPrimes : Finset (FinPlace E)
  /-- `Q` is auxiliary for `S₀`. -/
  auxiliary : IsAuxiliary S₀ auxPrimes
  /-- `Q` has at most `s₀ / 2` primes. -/
  two_mul_card_le : 2 * #auxPrimes ≤ s₀
  /-- The homomorphisms `λ_𝔮` to `ℤ / ℓ ^ N`, one for each prime `𝔮` of `Q`. -/
  primeChar : auxPrimes → Gal(Ω/E) →* Multiplicative (ZMod (ℓ ^ N))
  /-- `λ_𝔮` is continuous and `λ_𝔮(Art y) = η(y / ȳ)` for an idele class character `η` of tame
  level `𝔮` that is trivial above `ℓ`. So it is anticyclotomic, unramified outside `𝔮` and `𝔮̄`, and
  zero on the decomposition groups above `ℓ`. -/
  isFromU1_primeChar (v : auxPrimes) : IsFromU1 (placesDividing E ℓ) {v.val} (primeChar v)
  /-- `λ_𝔮` is onto on inertia at `𝔮`. -/
  exists_eq_ofAdd_one (v : auxPrimes) : ∃ g ∈ inertiaAbove {v.val},
    primeChar v g = Multiplicative.ofAdd 1
  /-- The polynomials of the data. -/
  datumPoly : ι → MvPolynomial auxPrimes (intQpBar ℓ)
  /-- The polynomials of the systems. -/
  systemPoly : κ → MvPolynomial auxPrimes (intQpBar ℓ)
  /-- The points of the data. -/
  datumPoint : ι → auxPrimes → intQpBar ℓ
  /-- The points of the systems. -/
  systemPoint : κ → auxPrimes → intQpBar ℓ
  /-- The coordinates of the point of a datum have valuation at least `r`. -/
  le_ellVal_datumPoint (i : ι) (v : auxPrimes) : (r : ℝ≥0) ≤ ellVal (datumPoint i v).val
  /-- The coordinates of the point of a system have valuation at least `r`. -/
  le_ellVal_systemPoint (k : κ) (v : auxPrimes) : (r : ℝ≥0) ≤ ellVal (systemPoint k v).val
  /-- At the point of a datum, `v(P) ≤ β_T + s₀ r`. -/
  ellVal_datumPoly_le (i : ι) :
    ellVal (eval (datumPoint i) (datumPoly i)).val ≤ O.normLength (T i).β + s₀ * (r : ℝ≥0)
  /-- At the point of a system, `v(P) ≤ β + s₀ r`. -/
  ellVal_systemPoly_le (k : κ) :
    ellVal (eval (systemPoint k) (systemPoly k)).val ≤ (Y k).β + s₀ * (r : ℝ≥0)
  /-- For `ℓ ^ N`-th roots of unity `ζ_𝔮`, `ψ = ∏ ζ_𝔮 ^ λ_𝔮` and `x = (ζ_𝔮 - 1)_𝔮`, the value of `ψ`
  at the element `Θ_Q` of a system is `P(x)`. -/
  groupRingEval_eq_eval (ζ : auxPrimes → intQpBar ℓ)
    (hζ : ∀ v : auxPrimes, (ζ v : PadicAlgCl ℓ) ^ ℓ ^ N = 1) (k : κ) :
    groupRingEval (pointChar primeChar (fun v : auxPrimes ↦ (ζ v : PadicAlgCl ℓ)) hζ)
      ((Y k).element auxPrimes) =
      (eval (fun v : auxPrimes ↦ ζ v - 1) (systemPoly k) : intQpBar ℓ)
  /-- For the same `ψ` and `x`, the group `Sel_Q(T ψ)` has length at most `v(P(x))` if
  `v(P(x)) < β_T + 1`. -/
  length_le (ζ : auxPrimes → intQpBar ℓ) (hζ : ∀ v : auxPrimes, (ζ v : PadicAlgCl ℓ) ^ ℓ ^ N = 1)
    (i : ι)
    (h_lt : ellVal (eval (fun v : auxPrimes ↦ ζ v - 1) (datumPoly i)).val <
      O.normLength (T i).β + 1) :
    (T i).TwistedLengthLe auxPrimes
      (pointChar primeChar (fun v : auxPrimes ↦ (ζ v : PadicAlgCl ℓ)) hζ)
      (ellVal (eval (fun v : auxPrimes ↦ ζ v - 1) (datumPoly i)).val)

/-- Let `T i` be Selmer data over a coefficient ring `O` and `Y k` Stickelberger systems. Let `J` be
a set of tied auxiliary primes with elements and slopes given by `d` and with a first prime `P₀`
whose Frobenius element lies in the set `W`, otherwise unused (`IsTiedPrimes`); where the slope for
`T i` is nonzero, the Frobenius element and its conjugate inverse act trivially on `T i` modulo
`ℓ ^ M`. Let the Selmer group of each `T i` modulo `ℓ ^ M` tied at all primes of `J` (`tiedSelmer`)
have length at most `globalTerm + placesTerm`, the global term of `T i` plus its local terms at the
places of `(T i).places` prime to `ℓ`; adding the term for `g₀` gives the number `β` of `T i`. Let
the Frobenius element `φ = (d P₀).1.frob` of `P₀` and its conjugate inverse act on each `T i` modulo
`ℓ ^ M` as `g₀` and its conjugate inverse do, and let `ϑ(φ) ≡ ϑ(g₀)` modulo `ℓ ^ M'` for the
character `ϑ = twistChar` of each `Y k`. Let `M > O.normLength β + 1` for each `T i` and
`M' > β + 1` for each `Y k`, where `β = v(1(Θ_∅)) + 2 m v(ϑ(g₀) - 1)`, `1(Θ_∅)` is the value of the
trivial character at the element `(Y k).element ∅` and `m` is the length of the list
`(Y k).exponents`. Let `c ≥ 1` bound the ranks of the `T i` and the lengths `m`, and let `s₀ ≥ 1`,
`2 c #J ≤ s₀`, `s₀ r < 1`, `M < N` and `M, M' ≤ N r`. Then `TwistPolynomials` is inhabited: there
are auxiliary primes (the proof takes `J`), homomorphisms to `ℤ / ℓ ^ N`, and for each datum and
system a polynomial `P` that controls its twists at roots of unity, with a point of valuation at
least `r` where `v(P) ≤ β + s₀ r`, with `O.normLength β` in place of `β` for the `T i`. -/
lemma nonempty_twistPolynomials_of_isTiedPrimes (T : ∀ i : ι, SelmerDatum ℓ S₀ g₀ O.val (n i))
    (Y : κ → StickelbergerSystem ℓ S₀ g₀) {M M' N c s₀ : ℕ} {r : ℚ≥0} {W : Set Gal(Ω/E)}
    {P₀ : FinPlace E} {J : Finset (FinPlace E)}
    {d : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O.val)}
    (h_primes : IsTiedPrimes ℓ S₀
      (fun (i : ι) (g : Gal(Ω/E)) ↦ reduceModPow ℓ M (T i).ρ g = 1) W N P₀ J d)
    (h_tied : ∀ i : ι,
      length O.val ((T i).tiedSelmer J J d i (ℓ ^ M)) ≤ (T i).globalTerm + (T i).placesTerm)
    (h_frob_datum : ∀ (i : ι) (b : Bool), reduceModPow ℓ M (T i).ρ (idOrConjInv b (d P₀).1.frob) =
      reduceModPow ℓ M (T i).ρ (idOrConjInv b g₀))
    (h_frob_system : ∀ k : κ,
      (M' : ℝ≥0∞) ≤ ellVal ((Y k).twistChar (d P₀).1.frob - (Y k).twistChar g₀ : PadicAlgCl ℓ))
    (hM : ∀ i : ι, O.normLength (T i).β + 1 < M) (hM' : ∀ k : κ, (Y k).β + 1 < M')
    (hc : 1 ≤ c) (h_rank : ∀ i : ι, Fintype.card (n i) ≤ c)
    (h_exps : ∀ k : κ, (Y k).exponents.length ≤ c) (hs₀ : 1 ≤ s₀) (h_card_le : 2 * c * #J ≤ s₀)
    (hr : s₀ * r < 1) (hMN : M < N) (hN : M ≤ N * r) (hN' : M' ≤ N * r) :
    Nonempty (TwistPolynomials T Y s₀ r N) := by
  let lam (v : J) : Gal(Ω/E) →* Multiplicative (ZMod (ℓ ^ N)) := (d v).1.character
  have hr_one : r ≤ 1 := (le_mul_of_one_le_left zero_le (mod_cast hs₀)).trans hr.le
  have h_card {c' : ℕ} (hc' : c' ≤ c) : 2 * c' * #J ≤ s₀ := le_trans (by gcongr) h_card_le
  have h_datum (i : ι) : ∃ (P : MvPolynomial J O.val) (x : J → intQpBar ℓ),
      (∀ v : J, (r : ℝ≥0) ≤ ellVal (x v).val) ∧
      ellVal (eval x (P.map O.toIntQpBar)).val ≤ O.normLength (T i).β + s₀ * (r : ℝ≥0) ∧
      BoundsSelmer ℓ M lam (T i).ρ (unionWithConj (T i).places J) (T i).classRelations P :=
    (T i).exists_boundsSelmer_ellVal_eval_le h_primes (Nat.ne_zero_of_lt hMN) i (fun _ hg ↦ hg)
      ((T i).length_tiedSelmer_erase_le h_primes hMN i (fun _ hg ↦ hg) (h_frob_datum i) (h_tied i))
      (h_card (h_rank i)) hr_one hN
  have h_system (k : κ) : ∃ x : J → intQpBar ℓ, (∀ v : J, (r : ℝ≥0) ≤ ellVal (x v).val) ∧
      ellVal (eval x (groupRingEval (universalChar lam) ((Y k).element J))).val ≤
        (Y k).β + s₀ * (r : ℝ≥0) :=
    (Y k).exists_point_ellVal_universalChar_le h_primes (hM' k) (h_frob_system k) hs₀
      (h_card (h_exps k)) hr hN'
  have h_inertia (v : J) : ∃ g ∈ inertiaAbove {v.val}, lam v g = Multiplicative.ofAdd 1 := by
    obtain ⟨hγ_inertia, hγ_one, -⟩ := (h_primes.isAuxPrimeDataAt v v.2).tame_gen
    exact ⟨(d v).1.tameGenerator,
      ⟨v, rfl, _, (h_primes.isAuxPrimeDataAt v v.2).isPlaceOver, hγ_inertia⟩, hγ_one⟩
  choose P x hx hP_val hP_bound using h_datum
  choose x' hx' hx'_val using h_system
  exact ⟨{
    auxPrimes := J
    auxiliary := h_primes.auxiliary
    two_mul_card_le := by simpa using h_card hc
    primeChar := lam
    isFromU1_primeChar v := (h_primes.isAuxPrimeDataAt v v.2).toIsFromU1
    exists_eq_ofAdd_one := h_inertia
    datumPoly i := (P i).map O.toIntQpBar
    systemPoly k := groupRingEval (universalChar lam) ((Y k).element J)
    datumPoint := x
    systemPoint := x'
    le_ellVal_datumPoint := hx
    le_ellVal_systemPoint := hx'
    ellVal_datumPoly_le := hP_val
    ellVal_systemPoly_le := hx'_val
    groupRingEval_eq_eval ζ hζ k := (coe_eval_groupRingEval_universalChar lam hζ _).symm
    length_le ζ hζ i h_lt :=
      (T i).twistedLengthLe_pointChar (hP_bound i) ζ hζ (h_lt.trans (hM i)) }⟩

/-- Let finitely many Selmer data `T i` and Stickelberger systems `Y k` be given, and let `g₀` lie
in an inertia group above a place of `S₀` prime to `ℓ`. Let `M > β_T + 1` for all data and let the
residue field of `O` have more than `2 rank(T i) len(O / ℓ ^ M) + 1` elements (`IsTorsionLevel`).
There is an integer `s₀ ≥ 1` such that for every rational `r > 0` with `s₀ r < 1` and every large
`N` the following exist (`TwistPolynomials`), where `v(ℓ) = 1` and `β_T` and the lengths of Selmer
groups are scaled so that `O / ℓ` has length `1`.
* A set `Q` of at most `s₀ / 2` primes of prime norm that lie outside `S₀`, with conjugates outside
  `S₀` and `Q` (`IsAuxiliary`).
* For each `𝔮 ∈ Q` a homomorphism `λ_𝔮` to `ℤ / ℓ ^ N` that is onto on inertia at `𝔮` and comes by
  `y ↦ y / ȳ` from an idele class character of modulus `𝔮` trivial above `ℓ` (`IsFromU1`).
* For each datum and each system a polynomial `P` over `ℤ̄_ℓ` in variables `X_𝔮`, and a point with
  coordinates of valuation at least `r` at which `v(P) ≤ β + s₀ r`, for the number `β` of that datum
  or system.

For `ℓ ^ N`-th roots of unity `ζ_𝔮` put `ψ = ∏ ζ_𝔮 ^ λ_𝔮` and `x = (ζ_𝔮 - 1)_𝔮`. For a system,
`P(x)` is the value of `ψ` at its element `Θ_Q`. For a datum `T` with `v(P(x)) < β_T + 1`, the
Selmer group `Sel_Q(T ψ)` with divisible coefficients has length at most `v(P(x))`. -/
theorem exists_twistPolynomials (T : ∀ i : ι, SelmerDatum ℓ S₀ g₀ O.val (n i))
    (Y : κ → StickelbergerSystem ℓ S₀ g₀) [Finite ι] [Finite κ]
    (hg₀ : g₀ ∈ inertiaAbove (S₀ \ placesDividing E ℓ)) {M : ℕ} (hM : IsTorsionLevel T M) :
    ∃ s₀ : ℕ, 1 ≤ s₀ ∧ ∀ r : ℚ≥0, 0 < r → s₀ * r < 1 →
      ∀ᶠ N : ℕ in atTop, Nonempty (TwistPolynomials T Y s₀ r N) := by
  -- Descend all data at once, with the Frobenius element of the first prime near `g₀`, and take the
  -- polynomials and points of the resulting set of tied primes.
  obtain ⟨c, hc, h_rank, h_exps⟩ : ∃ c : ℕ,
      1 ≤ c ∧ (∀ i : ι, Fintype.card (n i) ≤ c) ∧ ∀ k : κ, (Y k).exponents.length ≤ c :=
    ((eventually_ge_atTop 1).and <| (eventually_all.2 fun _ ↦ eventually_ge_atTop _).and <|
      eventually_all.2 fun _ ↦ eventually_ge_atTop _).exists
  obtain ⟨M', hM'⟩ : ∃ M' : ℕ, ∀ k : κ, (Y k).β + 1 < M' :=
    (eventually_all.2 fun k ↦ ENNReal.tendsto_nat_nhds_top.eventually
      (lt_mem_nhds (by simp [(Y k).β_ne_top.lt_top]))).exists
  have h_near : ∀ᶠ g : Gal(Ω/E) in nhds g₀,
      (∀ (i : ι) (b : Bool), reduceModPow ℓ M (T i).ρ (idOrConjInv b g) =
        reduceModPow ℓ M (T i).ρ (idOrConjInv b g₀)) ∧
      ∀ k : κ, (M' : ℝ≥0∞) ≤ ellVal ((Y k).twistChar g - (Y k).twistChar g₀ : PadicAlgCl ℓ) :=
    (eventually_all.2 fun i ↦ eventually_all.2 ((T i).eventually_reduceModPow_idOrConjInv_eq M)).and
      (eventually_all.2 fun k ↦ (Y k).eventually_le_ellVal_sub M')
  obtain ⟨W, hW, h_frob⟩ := h_near.exists_mem
  obtain ⟨s, h_descent⟩ : ∃ s : ℕ, ∀ N > M, ∃ (P₀ : FinPlace E) (J : Finset (FinPlace E))
      (d : FinPlace E → AuxPrimeData E (ℓ ^ N) × (ι → O.val)),
      IsTiedPrimes ℓ S₀ (fun i g ↦ reduceModPow ℓ M (T i).ρ g = 1) W N P₀ J d ∧ #J ≤ s ∧
      ∀ i : ι, length O.val ((T i).tiedSelmer J J d i (ℓ ^ M)) ≤ (T i).globalTerm +
        (T i).placesTerm :=
    exists_isTiedPrimes_card_le_and_length_le T hg₀ M hM.lt_card_residueField hW
  -- The bound `s` includes the first prime; the summand `1` only makes `s₀` positive.
  have hs₀ : 1 ≤ 2 * c * (1 + s) := Nat.succ_le_of_lt (by positivity)
  refine ⟨2 * c * (1 + s), hs₀, fun r hr₀ hr ↦ ?_⟩
  have h_large (K : ℕ) : ∀ᶠ N : ℕ in atTop, K ≤ N * r :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const hr₀).eventually_ge_atTop _
  filter_upwards [eventually_gt_atTop M, h_large M, h_large M'] with N hMN hN hN'
  obtain ⟨P₀, J, d, h_primes, h_card, h_tied⟩ := h_descent N hMN
  obtain ⟨h_frob_datum, h_frob_system⟩ := h_frob _ h_primes.first_frob_mem
  exact nonempty_twistPolynomials_of_isTiedPrimes T Y h_primes h_tied h_frob_datum h_frob_system
    hM.β_lt hM' hc h_rank h_exps hs₀ (Nat.mul_le_mul_left _ (by omega)) hr hMN hN hN'

end New.Selmer

end
