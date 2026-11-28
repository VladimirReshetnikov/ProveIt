import Lib.ClassField.Global.Chebotarev
import Lib.Weil.Unramified.SplitHecke

/-!
# Weights, Hecke polynomials, eigenforms and the filter of most Frobenii

The automorphic side concerns functions `f` on the finite adelic points `New.Gf E n` of the definite
unitary group, with values in a complex vector space, under right translation `New.rightRegular`. At
a split place `w` (one with `star w ≠ w`), `GL n (E_w)` acts through `New.ofSplitPlace`, and
`q = New.FinPlace.q w` is the order of the residue field. We define weights and their jumps, Hecke
polynomials built from the eigenvalues of the Hecke operators `New.heckeSplit`, and eigenforms.

## Main definitions and results

* `New.Weight`, `New.jumps`: weights, and the multiset of integers attached to an embedding.
* `New.heckePoly`, `New.HasHeckePolyAt`: the polynomial made from the eigenvalues of the Hecke
  operators `New.heckeSplit`, and the statement that `f` is spherical at `w` with this polynomial.
* `New.IsEigenform`, `New.IsSphericalOff`: eigenforms at almost all places of prime norm, and at all
  split places outside a finite set and its conjugate.
* `New.HasHeckePolyAt.isMonicOfDegree`: the Hecke polynomial of a nonzero spherical eigenvector
  (`New.HasHeckePolyAt`) of rank `n` is monic of degree `n`.
* `New.mostFrobenii`: the filter. `New.mostFrobeniiAt` adds that the Frobenius element `frob` tends
  to `g`.
* `New.dense_of_mostFrobenii`: a property of most Frobenius elements holds on a dense set; hence the
  filters `New.mostFrobeniiAt` are not trivial.

Notions from other files:
* `New.IsFrob`: `σ` stabilises the valuation subring `A` and `σ • x ≡ x ^ q` modulo the maximal
  ideal for all `x ∈ A`.
* `New.IsPlaceOver`: The valuation subring A of Ω lies over the prime w of E: an integer of E is in
  the maximal ideal of A exactly when it lies in w.
* `New.stdLevel`: The subgroup K_0 = G_f ∩ GL_n(Ô) of the finite adelic unitary group, the
  stabiliser of the standard lattice Ô^n.

## Relation to the literature

Known; see `Lib.GaloisRep.Main.OddRank`, `Lib.GaloisRep.LocalGlobal.LabelCompatibility` and
`Lib.ClassField.Global.Chebotarev` for sources.
-/

noncomputable section

/-!
## Weights, Hecke polynomials and eigenforms on the definite unitary group

Besides the notions of the file head, this section defines `New.HasLabel`, a condition on the action
of `GL n` of the residue field at `w`.
-/

section FormDefs

open NumberField Polynomial Function

namespace New

variable {E n M : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] [DecidableEq n]
  (f : Gf E n → M → ℂ) {w : FinPlace E} (hw : star w ≠ w)

variable (E) in
/-- Weights. For `κ : Weight E` and an infinite place `v` of `E`, `κ.1 v h` is the number of columns
of height `h` of a Young diagram, and `κ.2 v` is an integer exponent of the determinant. -/
abbrev Weight : Type := (InfinitePlace E → ℕ → ℕ) × (InfinitePlace E → ℤ)

/-- For natural numbers q, N and a sequence t in a commutative ring, the polynomial Σ_{j=0}^{N}
(−1)^j q^{j(j−1)/2} t_j X^{N−j}. -/
def heckePoly {R : Type} [CommRing R] (q N : ℕ) (t : ℕ → R) : R[X] :=
  ∑ j ∈ Finset.range (N + 1), C ((-1) ^ j * q ^ j.choose 2 * t j) * X ^ (N - j)

/-- `f` is spherical at the split place `w` with Hecke polynomial `P`: the maximal compact subgroup
`maxCompactAt n w` at `w` and `star w` fixes `f`, the `j`-th Hecke operator at `w` (`heckeSplit`)
acts on `f` by a scalar `t j`, and `P = heckePoly q (Fintype.card n) t`, that is
`P = Σ_j (−1)^j q^{j(j−1)/2} t_j X^{n−j}`, with `q` the order of the residue field at `w`. -/
def HasHeckePolyAt (w : FinPlace E) (hw : star w ≠ w) (P : ℂ[X]) : Prop :=
  f ∈ levelSpace (rightRegular ℂ (Gf E n) (M → ℂ)) (maxCompactAt n w) ∧
  ∃ t : ℕ → ℂ,
    P = heckePoly w.q (Fintype.card n) t ∧
      ∀ j : ℕ, heckeSplit (rightRegular ℂ (Gf E n) (M → ℂ)) hw j f = t j • f

/-- `f` is an eigenform for the system `P` of polynomials: `f ≠ 0`, and for all but finitely many
places `w`, if the norm of `w` is prime then `w` is split (`star w ≠ w`) and `f` is spherical
at `w` with Hecke polynomial `P w` (`New.HasHeckePolyAt`). Splitting is part of the assertion. -/
def IsEigenform (P : FinPlace E → ℂ[X]) : Prop :=
  f ≠ 0 ∧
  ∀ᶠ w : FinPlace E in Filter.cofinite, w.q.Prime → ∃ hw : star w ≠ w, HasHeckePolyAt f w hw (P w)

/-- `f` is spherical off the finite set `S` of places with Hecke polynomials `P`: `f ≠ 0`, `f` is
fixed by the integral points `stdLevel E n` that are trivial at the places of `S`
(`Gf.trivialOn n S`), and `f` has Hecke polynomial `P w` (`New.HasHeckePolyAt`) at every split
place `w` with `w ∉ S` and `star w ∉ S`. -/
def IsSphericalOff (S : Finset (FinPlace E)) (f : Gf E n → M → ℂ) (P : FinPlace E → ℂ[X]) : Prop :=
  f ≠ 0 ∧
  (∀ k ∈ stdLevel E n ⊓ Gf.trivialOn n S, rightRegular ℂ (Gf E n) (M → ℂ) k f = f) ∧
  ∀ (w : FinPlace E) (hw : star w ≠ w), w ∉ S → star w ∉ S → HasHeckePolyAt f w hw (P w)

/-- `f` has the label `Ξ`, a function on `GL n (ResField w)` with `ResField w` the residue field at
the split place `w`: the kernel of the reduction `reduceGL` from the integral matrices
`intGL n Valued.v.integer` at `w` to `GL n (ResField w)` fixes `f`, and the sum over `x` of
`star (Ξ x)` times the translate of `f` by a lift of `x` is nonzero. -/
def HasLabel (Ξ : GL n (ResField w) → ℂ) : Prop :=
  (∀ k : intGL n Valued.v.integer, reduceGL k = 1 →
    rightRegular ℂ (Gf E n) (M → ℂ) (ofSplitPlace hw k.val) f = f) ∧
  ∑ᶠ x : GL n (ResField w),
    star (Ξ x) •
      rightRegular ℂ (Gf E n) (M → ℂ) (ofSplitPlace hw (surjInv reduceGL_surjective x).val) f ≠ 0

open scoped Classical in
/-- The multiset {j − 1 − λ_j} if σ is in the CM type `Φ`, that is if σ equals `Φ v`, the embedding
that `Φ` picks at the place v of σ, else {λ_j + N − j}, 1 ≤ j ≤ N, with λ the highest weight of κ at
the place v of σ: λ_j = `κ.2 v` + Σ_{j ≤ h < N} `κ.1 v h`. The index in the code is j − 1, and `u`
is λ_j + N − j. -/
def jumps {E : Type} [Field E] [CMType E] (κ : Weight E) (N : ℕ) (σ : E →+* ℂ) : Multiset ℤ :=
  (Multiset.range N).map fun j ↦
    let u : ℤ :=
      κ.2 (InfinitePlace.mk σ) + ∑ h ∈ Finset.Ioo j N, κ.1 (InfinitePlace.mk σ) h + (N - 1 - j)
    (if σ = Φ (InfinitePlace.mk σ) then N - 1 - u else u)

end New

end FormDefs

/-!
## Coefficients and monicity of Hecke polynomials; distinct jumps

* `New.coeff_heckePoly`: the coefficients of
  `New.heckePoly q N t = ∑ j, (-1) ^ j q ^ (j choose 2) t j X ^ (N - j)`.
-/

section HeckePolyMonic

open Polynomial Finset

variable {E n : Type} {M : Type} [Field E] [New.CMType E] [Fintype n]

/-- The coefficient of `X ^ j` in `heckePoly q N t` is
`(-1) ^ (N - j) q ^ (N - j choose 2) t (N - j)` for `j ≤ N`, and `0` otherwise. -/
@[simp]
lemma New.coeff_heckePoly {R : Type} [CommRing R] (q N : ℕ) (t : ℕ → R) (j : ℕ) :
    (heckePoly q N t).coeff j =
      (if j ≤ N then (-1) ^ (N - j) * q ^ (N - j).choose 2 else 0 : ℤ) * t (N - j) := by
  rw [heckePoly, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  push_cast
  -- Only the term of index `N - j` can have degree `j`.
  grind [sum_eq_single (N - j)]

/-- Let `f ≠ 0` be a function on the finite adelic unitary group `Gf E n`, and let `P` be its Hecke
polynomial at the split place `w` (`New.HasHeckePolyAt`). Then `P` is monic of degree
`Fintype.card n`. -/
lemma New.HasHeckePolyAt.isMonicOfDegree [DecidableEq n] {f : Gf E n → M → ℂ} (hf : f ≠ 0)
    {w : FinPlace E} {hw : star w ≠ w} {P : ℂ[X]} (hP : HasHeckePolyAt f w hw P) :
    P.IsMonicOfDegree (Fintype.card n) := by
  obtain ⟨hf_fix, t, rfl, ht⟩ := hP
  -- The zeroth Hecke operator is the identity on spherical vectors, so `t 0 = 1`.
  have ht_zero : t 0 = 1 := by
    rw [← smul_left_inj hf, ← ht 0, heckeSplit, heckeGL_zero ((mem_sphericalAt_iff hw).mp hf_fix),
      one_smul]
  simp +contextual [isMonicOfDegree_iff, natDegree_le_iff_coeff_eq_zero, not_le.mpr, ht_zero]

/-- The jumps of a weight at an embedding are distinct: the multiset `jumps κ N σ` has no
repetition. -/
lemma New.Weight.nodup_jumps {E : Type} [Field E] [CMType E] (κ : Weight E) (N : ℕ) (σ : E →+* ℂ) :
    (jumps κ N σ).Nodup := by
  -- `jumps κ N σ` is the image of `range N`; the map is injective since, for `i < j`, the jumps of
  -- index `i` and `j` differ.
  rw [jumps]
  refine (Multiset.nodup_range N).map (Function.Injective.of_lt_imp_ne fun i j hij ↦ ?_)
  -- For `i < j` the sum over `Ioo j N` is at most the sum over `Ioo i N`, while `N - 1 - j` is
  -- smaller than `N - 1 - i` in `ℤ`.
  have h_sum : ∑ h ∈ Ioo j N, κ.1 (.mk σ) h ≤ ∑ h ∈ Ioo i N, κ.1 (.mk σ) h :=
    sum_le_sum_of_subset (Ioo_subset_Ioo hij.le le_rfl)
  grind

end HeckePolyMonic

/-!
## The filter of most Frobenii and density by Chebotarev

A filter that expresses that a property holds for most Frobenius elements.
-/

section FrobeniusFilter

open Filter Topology

namespace New

variable (E : Type) [Field E] [EmbeddedNumberField E]

/-- A finite place w = `place` of E of prime norm, a valuation subring A = `valuationSubring` of Ω
(a term of `ClosurePlace`) above w in the sense of `IsPlaceOver`, and a geometric Frobenius
s = `frob` in Gal(Ω/E) at A. -/
structure FrobeniusDatum where
  /-- The finite place of `E`. -/
  place : FinPlace E
  /-- The valuation subring of `Ω`. -/
  valuationSubring : ClosurePlace
  /-- The element of the Galois group of `Ω` over `E`. -/
  frob : Gal(Ω/E)
  /-- The norm of the place is a prime number. -/
  prime_q : place.q.Prime
  /-- The valuation subring lies over the place. -/
  isPlaceOver : IsPlaceOver valuationSubring place
  /-- The inverse of the element is an arithmetic Frobenius at the valuation subring. -/
  isFrob_inv : IsFrob valuationSubring place.q frob⁻¹

/-- The filter 'most Frobenii' on `New.FrobeniusDatum E`. A set `X` of data `(w, A, s)` belongs to
it if each nonempty open `V ⊆ Gal(Ω/E)` has a nonempty open part `O` such that, for almost all `w`,
`X` contains every datum `(w, A, s)` with `s ∈ O`. -/
def mostFrobenii : Filter (FrobeniusDatum E) where
  sets :=
    {X : Set (FrobeniusDatum E) |
      ∀ V : Set Gal(Ω/E), IsOpen V → V.Nonempty → ∃ O ⊆ V,
        IsOpen O ∧ O.Nonempty ∧
        ∀ᶠ w : FinPlace E in cofinite,
          ∀ (A : ClosurePlace) (s : Gal(Ω/E)) (hp : w.q.Prime) (hA : IsPlaceOver A w)
            (hs : IsFrob A w.q s⁻¹),
          s ∈ O →
          ⟨w, A, s, hp, hA, hs⟩ ∈ X}
  univ_sets V hV hV_ne := ⟨V, subset_rfl, hV, hV_ne, by simp⟩
  sets_of_superset hX hXY V hV hV_ne := by
    obtain ⟨O, hOV, hO, hO_ne, h_ev⟩ := hX V hV hV_ne
    exact ⟨O, hOV, hO, hO_ne, h_ev.mono fun w hw A s hp hA hs hsO ↦ hXY (hw A s hp hA hs hsO)⟩
  inter_sets hX hY V hV hV_ne := by
    -- shrink `V` twice: to `O` for the first set, then to `O'` inside `O` for the second
    obtain ⟨O, hOV, hO, hO_ne, hX_ev⟩ := hX V hV hV_ne
    obtain ⟨O', hO'O, hO', hO'_ne, hY_ev⟩ := hY O hO hO_ne
    refine ⟨O', hO'O.trans hOV, hO', hO'_ne, ?_⟩
    filter_upwards [hX_ev, hY_ev] with w hwX hwY A s hp hA hs hsO'
    exact ⟨hwX A s hp hA hs (hO'O hsO'), hwY A s hp hA hs hsO'⟩

/-- The filter of most Frobenii tending to `g`: `New.mostFrobenii` on data `(w, A, s)`, refined by
the condition that `s` lies near `g`. -/
noncomputable abbrev mostFrobeniiAt (g : Gal(Ω/E)) : Filter (FrobeniusDatum E) :=
  mostFrobenii E ⊓ comap (fun x : FrobeniusDatum E ↦ x.frob) (𝓝 g)

variable {E}

/-- For a continuous `f` on `Gal(Ω/E)`, the values of `f` at the Frobenius elements tend to `f g`
along the filter `mostFrobeniiAt E g` of most Frobenii tending to `g`. -/
lemma tendsto_mostFrobeniiAt {X : Type*} {g : Gal(Ω/E)} [TopologicalSpace X] (f : Gal(Ω/E) → X)
    (hf : Continuous f := by fun_prop) :
    Tendsto (fun x : FrobeniusDatum E ↦ f x.frob) (mostFrobeniiAt E g) (𝓝 (f g)) :=
  (hf.tendsto g).comp (tendsto_comap.mono_left inf_le_right)

/-- Along most Frobenius data the place leaves every finite set: a property of all but finitely
many places holds at the place of most Frobenius data. -/
lemma tendsto_place_mostFrobenii :
    Tendsto (fun x : FrobeniusDatum E ↦ x.place) (mostFrobenii E) cofinite := by
  -- any nonempty open set serves as its own small open set
  intro S hS V hV hV_ne
  refine ⟨V, subset_rfl, hV, hV_ne, ?_⟩
  filter_upwards [hS] with w hw A s hp hA hs _ using hw

/-- If `p` holds at all but finitely many places, and `p` at the place of a Frobenius datum
implies `q` of the datum, then `q` holds for most Frobenius data. When `q x` is `p x.place`, pass
`fun _ ↦ id` as `h_imp`. -/
lemma eventually_mostFrobenii {p : FinPlace E → Prop} {q : FrobeniusDatum E → Prop}
    (hp : ∀ᶠ w : FinPlace E in cofinite, p w) (h_imp : ∀ x : FrobeniusDatum E, p x.place → q x) :
    ∀ᶠ x : FrobeniusDatum E in mostFrobenii E, q x :=
  (tendsto_place_mostFrobenii.eventually hp).mono h_imp

/-- Let `φ` be an open embedding of `Gal(Ω/E)` in `Gal(Ω/F)`, `π` a map from the finite places of
`E` to those of `F`, and `X` a set that contains most Frobenius data over `E`. Then for most data
`y` over `F`, the set `X` contains every datum over `E` whose place and Frobenius element are sent
by `π` and `φ` to those of `y`. -/
lemma eventually_mostFrobenii_of_isOpenEmbedding {F : Type} [Field F] [EmbeddedNumberField F]
    {φ : Gal(Ω/E) → Gal(Ω/F)}
    (hφ : IsOpenEmbedding φ) (π : FinPlace E → FinPlace F) {X : Set (FrobeniusDatum E)}
    (hX : X ∈ mostFrobenii E) :
    ∀ᶠ y : FrobeniusDatum F in mostFrobenii F,
      ∀ x : FrobeniusDatum E, π x.place = y.place → φ x.frob = y.frob → x ∈ X := by
  intro V hV hV_ne
  by_cases h_meet : (φ ⁻¹' V).Nonempty
  · -- Push forward the open set `O` that `hX` gives in `φ ⁻¹' V`; the exceptional places of `F`
    -- lie in the image under `π` of the finitely many exceptional places of `E`.
    obtain ⟨O, hO_sub, hO_open, hO_ne, h_cofinite⟩ :
        ∃ O ⊆ φ ⁻¹' V, IsOpen O ∧ O.Nonempty ∧
          ∀ᶠ w : FinPlace E in cofinite,
            ∀ (A : ClosurePlace) (s : Gal(Ω/E)) (hp : w.q.Prime) (hA : IsPlaceOver A w)
              (hs : IsFrob A w.q s⁻¹), s ∈ O → (⟨w, A, s, hp, hA, hs⟩ : FrobeniusDatum E) ∈ X :=
      hX (φ ⁻¹' V) (hV.preimage hφ.continuous) h_meet
    refine ⟨φ '' O, Set.image_subset_iff.2 hO_sub, hφ.isOpenMap O hO_open, hO_ne.image φ, ?_⟩
    filter_upwards [(h_cofinite.image π).compl_mem_cofinite] with v hv A s hp hA hs hs_mem x hw hφx
    have h_frob_mem : x.frob ∈ O := hφ.injective.mem_set_image.1 (by rwa [hφx])
    -- were `x` outside `X`, its place would be exceptional and `v = π x.place` in the image
    by_contra hx_not_mem
    refine hv ⟨x.place, fun h_good ↦ hx_not_mem ?_, hw⟩
    exact h_good x.valuationSubring x.frob x.prime_q x.isPlaceOver x.isFrob_inv h_frob_mem
  · -- If `V` misses the range of `φ`, the condition is vacuous on `V` itself.
    refine ⟨V, subset_rfl, hV, hV_ne, .of_forall fun v A s hp hA hs hs_mem x hw hφx ↦ ?_⟩
    exact absurd ⟨x.frob, show φ x.frob ∈ V by rwa [hφx]⟩ h_meet

/-- If most Frobenius data `(w, A, s)` satisfy `p s`, then `p` holds on a dense subset of
`Gal(Ω/E)`. -/
lemma dense_of_mostFrobenii {p : Gal(Ω/E) → Prop}
    (h : ∀ᶠ x : FrobeniusDatum E in mostFrobenii E, p x.frob) :
    Dense {s : Gal(Ω/E) | p s} := by
  -- A nonempty open `V` contains an open set `O` as in the definition of `mostFrobenii`. By
  -- Chebotarev `O⁻¹` contains an arithmetic Frobenius `σ` at a place of prime norm that is not
  -- exceptional, so `p σ⁻¹` holds.
  refine dense_iff_inter_open.2 fun V hV hV_ne ↦ ?_
  obtain ⟨O, hOV, hO, hO_ne, h_cofinite⟩ :
      ∃ O ⊆ V, IsOpen O ∧ O.Nonempty ∧
        ∀ᶠ w : FinPlace E in cofinite,
          ∀ (A : ClosurePlace) (s : Gal(Ω/E)) (hp : w.q.Prime) (hA : IsPlaceOver A w)
            (hs : IsFrob A w.q s⁻¹), s ∈ O → p s :=
    h V hV hV_ne
  -- Chebotarev: a place `w` of prime norm outside the exceptional set of `h_cofinite`, a place
  -- `A` of `Ω` above it, and an arithmetic Frobenius `σ ∈ O⁻¹` at `A`.
  obtain ⟨w, hw_good, h_prime, A, hA, σ, hσ_inv, h_frob, -⟩ :=
    chebotarev hO.inv hO_ne.inv h_cofinite
  have h_frob_inv : IsFrob A w.q σ⁻¹⁻¹ := by rwa [inv_inv]
  exact ⟨σ⁻¹, hOV hσ_inv, not_not.mp hw_good A σ⁻¹ h_prime hA h_frob_inv hσ_inv⟩

instance {g : Gal(Ω/E)} : NeBot (mostFrobeniiAt E g) :=
  -- a set that holds most Frobenius elements is dense, so it meets every neighbourhood of `g`
  neBot_inf_comap_iff_map.mpr
    (inf_neBot_iff.mpr fun _ h_most _ ↦ (dense_of_mostFrobenii h_most).inter_nhds_nonempty)

end New

end FrobeniusFilter

end
