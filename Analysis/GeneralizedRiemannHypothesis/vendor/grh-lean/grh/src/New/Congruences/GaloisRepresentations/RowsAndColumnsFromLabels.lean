import New.Congruences.GaloisRepresentations.AttachedRepresentations
import New.Congruences.Selmer.AuxiliaryPrimes

/-!
# Main summands and conjugate self-dual representations from type polynomials

Let `O` be a descent pair (`New.DescentPair`) with type polynomials `c` in a lift setting
(`New.Selmer.IsLiftSetting`). This file describes inertia on representations of a type for `O` and
on representations attached to its eigenforms.

* `New.Selmer.exists_inertiaGroup_isInertiaSpectrum`: inertia elements above the primes
  `D.levelPrime 0` and `D.levelPrime 1` are killed by polynomials whose roots are roots of unity of
  controlled order (`New.Selmer.IsInertiaSpectrum`).
* `New.Selmer.IsRepOfType.isMainSummandLike`: a representation of a type of rank `card r` and empty
  level, with jumps as in `New.Selmer.IsMainSummandWeights`, is a main summand
  (`New.Selmer.IsMainSummandLike`).
* `New.Selmer.isFiniteTypeAt_and_polyKillsAt_of_mem_conjClosure`: a representation attached to an
  eigenform of parahoric type at the auxiliary places (`New.Selmer.HasTwistParahoricType`) has no
  monodromy above `ϑ.Q` and its conjugates, and a quadratic polynomial kills inertia there.
* `New.Selmer.normalisedRep_quadratic_on_inertia`: its normalised representation satisfies the same
  quadratic relation on inertia above `ϑ.Q` and its conjugates.

Notions from other files:
* `New.Selmer.IsLiftSetting O c ϑ`: the places of `O` are the chosen places above `D.levelPrime 0`,
  `D.levelPrime 1` and those of `ϑ.Q`, its character is a power of `D.chiMLocal` times `ϑ.tamePart`,
  and `c` are type polynomials of degree `card r`.
* `New.Selmer.IsRepOfType O k J c S R`: `R` is a conjugate self-dual representation of given level
  (`New.Selmer.IsConjSelfDualOfLevel`: on traces `R^c ≅ R^∨(1 - k)`, with Hodge–Tate jumps `J` and
  local conditions off the level `S` and above `ℓ M`), and inertia at the chosen places acts through
  the roots of the type polynomials `c` over the residue fields.
* `New.ClosurePlace`: a place of the algebraic closure `Ω` of `ℚ`, that is, a valuation subring;
  `conjPlace A` is the complex conjugate place, and `AbsGal D` is `Gal(Ω/D.E)`.
* `New.Data.IsChosen`: a place of `D.E` is chosen if it divides `D.piM`, an integer whose product
  with its conjugate is `M = D.levelPrime 0 * D.levelPrime 1`.
* `New.GaloisRep.PolyKillsAt R A s P`: `P` kills `s` at the place `A`, that is, `P (R s) = 0` off
  `ℓ`, and an analogue for Weil pairs (`New.Period.IsKilledBy`) above `ℓ`.
* `New.Selmer.scaledTypePoly`: the scaled type polynomial, `c i` with its roots multiplied by the
  element of the residue field that names the character `(O.tamePart w)⁻¹`, `w = O.chosenPlace i`.
* `New.ellVal`: the `ℓ`-adic valuation with values in `[0, ∞]`.
* `New.Data.Twist`: a tame character (`New.Data.TameChar`) whose tame part is non-trivial at every
  place of its set `Q`.

## Relation to the literature

See `New.Congruences.GaloisRepresentations.RowsFromEigensystems` for related work.
-/

namespace New.Selmer

open Matrix Polynomial Fintype GaloisRep Fact IsAlgClosed

attribute [local instance low] Fintype.ofFinite
open Multiset hiding card
open scoped NumberField

variable {ℓ : ℕ} [hp : ThePrime ℓ] {P : Parameters} {D : Data P}
  {r n : Type} [Fintype r] [DecidableEq r] [Fintype n]

/-- Let `x` be a root of unity in `ℚ̄_ℓ`. If `(x ^ a) ^ ℓ ^ u ≠ (x ^ b) ^ ℓ ^ u` for all `u`, then
`x ^ a - x ^ b` has norm `1`. -/
lemma norm_pow_sub_pow_eq_one {x : PadicAlgCl ℓ} (hx : IsOfFinOrder x) (a b : ℕ)
    (h_ne : ∀ u : ℕ, (x ^ a) ^ ℓ ^ u ≠ (x ^ b) ^ ℓ ^ u) : ‖x ^ a - x ^ b‖ = 1 := by
  -- Write the order of `x` as `ℓ ^ u * k` with `¬ℓ ∣ k`. The `ℓ ^ u`-th powers of `x ^ a` and
  -- `x ^ b` are distinct `k`-th roots of unity, so their difference has norm at least `‖k‖ ≥ 1`;
  -- and it is an integral multiple of `x ^ a - x ^ b`.
  obtain ⟨u, k, hk, h_ord⟩ := WfDvdMonoid.max_power_factor hx.orderOf_pos.ne' (out : ℓ.Prime)
  have h_root (c : ℕ) : ((x ^ c) ^ ℓ ^ u) ^ k = 1 := by
    rw [← pow_mul, ← h_ord, pow_right_comm, pow_orderOf_eq_one, one_pow]
  let z : NormedField.valuation.integer := ⟨x, hx.norm_eq_one.le⟩
  refine le_antisymm (z ^ a - z ^ b).prop ?_
  calc 1 ≤ ‖(k : PadicAlgCl ℓ)‖ := by
        simpa [← Padic.norm_natCast_lt_one_iff, ← PadicAlgCl.norm_extends] using hk
    _ ≤ ‖(x ^ a) ^ ℓ ^ u - (x ^ b) ^ ℓ ^ u‖ :=
      norm_natCast_le_norm_sub_of_pow_eq_one (h_root a) (h_root b) (h_ne u)
    _ ≤ ‖x ^ a - x ^ b‖ :=
      (Valuation.integer.integers _).le_of_dvd (sub_dvd_pow_sub_pow (z ^ a) (z ^ b) _)

/-- Let the matrix `Z` be killed by the polynomial with roots `μ`, where each member `y` of `μ` is
different from `1` and satisfies `y ^ (D.levelPrime i ^ d - 1) = 1` for some `1 ≤ d ≤ D.r`. Then the
`ℓ`-adic valuation of `det (Z - 1)` is at most `card r` times that of `D.chosenGroupOrder`. -/
lemma ellVal_det_sub_one_le_card_mul {i : Fin 2} {μ : Multiset (PadicAlgCl ℓ)}
    (hμ : ∀ y ∈ μ, y ≠ 1 ∧ ∃ d ∈ Set.Icc 1 D.r, y ^ (D.levelPrime i ^ d - 1) = 1)
    {Z : Matrix r r (PadicAlgCl ℓ)} (h_kill : aeval Z (μ.map (X - C ·)).prod = 0) :
    ellVal (Z - 1).det ≤ card r * padicValNat ℓ D.chosenGroupOrder := by
  -- Each eigenvalue `x` is a root of unity `≠ 1` of order dividing some `D.levelPrime i ^ d - 1`,
  -- so the valuation of `x - 1` is at most that of `D.levelPrime i ^ d - 1`.
  have h_root : ∀ x ∈ Z.charpoly.roots, ellVal (x - 1) ≤ padicValNat ℓ D.chosenGroupOrder := by
    intro x hx
    have hxμ : x ∈ μ := by simpa [eval_multiset_prod, sub_eq_zero] using
      isRoot_of_isRoot_charpoly h_kill (isRoot_of_mem_roots hx)
    obtain ⟨h_ne, d, ⟨hd_pos, hd_le⟩, hxd⟩ := hμ x hxμ
    have h_norm : ‖(D.levelPrime i ^ d - 1 : PadicAlgCl ℓ)‖ ≤ ‖x - 1‖ := by
      simpa [NeZero.pos] using norm_natCast_le_norm_sub_of_pow_eq_one hxd (one_pow _) h_ne
    exact (ellVal_le_ellVal h_norm).trans
      (ellVal_levelPrime_pow_sub_one_le D ℓ i ⟨hd_pos, hd_le.trans D.nat_le_of_hasLogBound⟩)
  have h_det : (Z - 1).det = (Z.charpoly.roots.map (· - 1)).prod := by
    simpa using (det_aeval_neg_eq_prod_roots Z (-X - 1) :)
  rw [h_det]
  calc _ ≤ ((Z.charpoly.roots.map (· - 1)).map ellVal).sum :=
        apply_prod_le_sum_map _ ellVal (by simp [ellVal]) fun _ _ ↦ ellVal_mul_le
    _ ≤ _ := sum_le_card_nsmul _ _ (by simpa only [forall_mem_map_iff] using h_root)
    _ = card r * padicValNat ℓ D.chosenGroupOrder := by simp [card_roots_eq_natDegree]

/-- Let `D` be the data of the construction with parameters `P`, so that `D.m` is the number of
lifts and `D.r` the rank of the target, and let `1 ≤ j ≤ D.m`, `1 ≤ t ≤ 4 * D.r + 2`. Let
`s = D.towerExp`
be the exponent with `2 ^ s = D.m ^ 22`. The number `P.q₂ s` is a multiple of `P.q₀ ^ s` and is the
order of the fixed residue field characters `D.chiMLocal` at the chosen places of `D.E` above the
level. It does not divide `j * t` times a power of `ℓ`. -/
lemma not_q₂_dvd_mul_pow_mul {j t : ℕ} (hj : j ∈ Set.Icc 1 D.m)
    (ht : t ∈ Set.Icc 1 (4 * D.r + 2)) (b : ℕ) : ¬P.q₂ D.towerExp ∣ j * (ℓ ^ b * t) := by
  -- For a prime `p ≠ ℓ` dividing `q₀` we would get `p ^ D.towerExp ∣ j * t`, but
  -- `0 < j * t < p ^ D.towerExp`.
  intro h_dvd
  -- one of the primes `2` and `5`, which divide `18480` and hence `q₀`
  obtain ⟨p, hpℓ, hp_prime, hp_dvd⟩ : ∃ p : ℕ, p ≠ ℓ ∧ p.Prime ∧ p ∣ P.q₀ := by
    by_cases h_two : 2 = ℓ
    · exact ⟨5, by omega, Nat.prime_five, Nat.dvd_trans (by norm_num) P.dvd_q₀⟩
    · exact ⟨2, h_two, Nat.prime_two, Nat.dvd_trans (by norm_num) P.dvd_q₀⟩
  have h_lt : j * t < p ^ D.towerExp :=
    calc j * t ≤ D.m * (4 * D.r + 2) := Nat.mul_le_mul hj.2 ht.2
      _ < 2 ^ D.towerExp := D.nat_lt_of_hasLogBound
      _ ≤ p ^ D.towerExp := Nat.pow_le_pow_left hp_prime.two_le _
  have h_pow_dvd : p ^ D.towerExp ∣ ℓ ^ b * (j * t) :=
    calc p ^ D.towerExp ∣ P.q₂ D.towerExp := by
          grw [hp_dvd.mul_right P.d, Parameters.q₂, ← le_self_add]
      _ ∣ j * (ℓ ^ b * t) := h_dvd
      _ = ℓ ^ b * (j * t) := mul_left_comm _ _ _
  exact Nat.not_dvd_of_pos_of_lt (mul_pos hj.1 ht.1) h_lt
    ((Nat.coprime_pow_primes D.towerExp b hp_prime out hpℓ).dvd_mul_left.1 h_pow_dvd)

variable [PadicIso ℓ]
  {O : DescentPair D.E r n} {ϑ : D.Twist}
  {c : (i : O.ChosenIndex) → (ResField (O.chosenPlace i))[X]}

variable (O c) in
/-- A multiset `μ` of possible eigenvalues of `s` at the place `A` of `Ω = ℚ̄`, common to all
representations `R` of a type of rank `card m` whose type polynomials are the scaled type
polynomials `scaledTypePoly O c i` times `(X - 1) ^ t`; the duality twist `k`, the jumps `J` and the
level `S` of `R` are arbitrary. It consists of `card r + t` roots of unity whose orders are bounded
through `p = D.levelPrime l`. On every such representation the polynomial with roots `μ` kills `s`
at `A`, and kills `conjGal s⁻¹` at the complex conjugate place `conjPlace A`. Here `conjGal` is
conjugation by complex conjugation, and off `ℓ` "`Q` kills `s`" (`PolyKillsAt`) means
`Q (R s) = 0`. -/
structure IsInertiaSpectrum (m : Type) [Fintype m] [DecidableEq m] (l : Fin 2) (A : ClosurePlace)
    (t : ℕ) (s : Gal(Ω/D.E)) (μ : Multiset (PadicAlgCl ℓ)) : Prop where
  /-- `μ` has `card r + t` members. -/
  card_eq : Multiset.card μ = card r + t
  /-- Each member of `μ` has order dividing `p ^ (card r)! - 1`, `p = D.levelPrime l`. -/
  pow_factorial_eq_one : ∀ y ∈ μ, y ^ (D.levelPrime l ^ (card r).factorial - 1) = 1
  /-- Each member of `μ` has order dividing `p ^ d - 1` for some `1 ≤ d ≤ D.r`. -/
  exists_pow_eq_one : ∀ y ∈ μ, ∃ d ∈ Set.Icc 1 D.r, y ^ (D.levelPrime l ^ d - 1) = 1
  /-- On every such representation, the polynomial with roots `μ` kills `s` at `A`. -/
  polyKillsAt {R : GalRep ℓ D.E m} {k : ℕ} {J : (D.E →+* ℂ) → Multiset ℤ} {S : Set (FinPlace D.E)}
    (hR : IsRepOfType (m := m) O k J
      (fun i : O.ChosenIndex ↦ scaledTypePoly O c i * (X - 1) ^ t) S R) :
    PolyKillsAt R A s (μ.map fun y : PadicAlgCl ℓ ↦ X - C y).prod
  /-- On every such representation, the polynomial with roots `μ` kills `conjGal s⁻¹` at the
  conjugate place. -/
  polyKillsAt_conjPlace {R : GalRep ℓ D.E m} {k : ℕ} {J : (D.E →+* ℂ) → Multiset ℤ}
    {S : Set (FinPlace D.E)} (hR : IsRepOfType (m := m) O k J
      (fun i : O.ChosenIndex ↦ scaledTypePoly O c i * (X - 1) ^ t) S R) :
    PolyKillsAt R (conjPlace A) (conjGal s⁻¹) (μ.map fun y : PadicAlgCl ℓ ↦ X - C y).prod

/-- If `μ` is an inertia spectrum (`IsInertiaSpectrum`: a multiset of possible eigenvalues) of
`conjGal s⁻¹` at the conjugate place `conjPlace A`, then `μ` is also an inertia spectrum of `s` at
`A`. -/
lemma IsInertiaSpectrum.of_conjPlace {m : Type} [Fintype m] [DecidableEq m] {l : Fin 2}
    {A : ClosurePlace} {t : ℕ} {s : Gal(Ω/D.E)} {μ : Multiset (PadicAlgCl ℓ)}
    (hμ : IsInertiaSpectrum O c m l (conjPlace A) t (conjGal s⁻¹) μ) :
    IsInertiaSpectrum O c m l A t s μ :=
  { hμ with
    polyKillsAt hR := by simpa using hμ.polyKillsAt_conjPlace hR
    polyKillsAt_conjPlace hR := hμ.polyKillsAt hR }

/-- The eigenvalues of inertia at a chosen place. Let `O.chosenPlace i` divide `p = D.levelPrime l`,
and let `A` be a place of `Ω = ℚ̄` over it. Each `s` in inertia at `A` has a multiset `μ` of
`card r + t` roots of unity (`IsInertiaSpectrum`), each of order dividing `p ^ (card r)! - 1` and
some `p ^ d - 1`, `1 ≤ d ≤ D.r`, such that the polynomial with roots `μ` kills `s` at `A` and
`conjGal s⁻¹` at the conjugate place in every rank `card m` representation with type polynomials
`scaledTypePoly O c i * (X - 1) ^ t`. Moreover `1 ∉ μ` if `t = 0` and `s` is `hA.tameGenerator`, the
fixed generator of tame inertia at `A`. -/
lemma exists_isInertiaSpectrum_chosenPlace (m : Type) [Fintype m] [DecidableEq m]
    (hc : IsLiftSetting O c ϑ) {l : Fin 2} {i : O.ChosenIndex}
    (hv : (D.levelPrime l : 𝓞 D.E) ∈ (O.chosenPlace i).asIdeal) {A : ClosurePlace}
    (hA : IsPlaceOver A (O.chosenPlace i)) (t : ℕ) {s : Gal(Ω/D.E)}
    (hs : s ∈ inertiaGroup Gal(Ω/D.E) A) :
    ∃ μ : Multiset (PadicAlgCl ℓ),
      IsInertiaSpectrum O c m l A t s μ ∧ (t = 0 → s = hA.tameGenerator.val → 1 ∉ μ) := by
  -- `s` acts through the roots of the type polynomial raised to its tame exponent.
  have h_label : IsLabel (card r) (scaledTypePoly O c i) := (hc.isLabel i).scaleRoots _
  have hq : (O.chosenPlace i).q = D.levelPrime l := D.q_eq_levelPrime hv
  let K : Type := AlgebraicClosure (ResField (O.chosenPlace i))
  let T : MulChar K ℂ := faithfulChar _
  -- `a` is the tame exponent of `s`, prime to `q ^ (card r)! - 1` for the tame generator
  obtain ⟨a, h_tame, h_coprime⟩ := (GaloisRep.exists_isTameExponent T hA (card r)).2 s hs
  -- `μ` consists of the images under `ιℓ ∘ T ^ a` of the roots of the scaled type polynomial times
  -- `(X - 1) ^ t`
  let roots : Multiset K := (scaledTypePoly O c i * (X - 1) ^ t).aroots K
  let μ : Multiset (PadicAlgCl ℓ) := roots.map fun x ↦ ιℓ ((T ^ a) x)
  have h_roots (x : K) (hx : x ∈ roots) : aeval x (scaledTypePoly O c i) = 0 ∨ x = 1 ∧ t ≠ 0 := by
    simpa [sub_eq_zero] using (mem_aroots.1 hx).2
  -- every root is killed by `D.levelPrime l ^ (card r)! - 1` and by some `D.levelPrime l ^ d - 1`
  have h_order (x : K) (hx : x ∈ roots) : x ^ (D.levelPrime l ^ (card r).factorial - 1) = 1 ∧
      ∃ d ∈ Set.Icc 1 D.r, x ^ (D.levelPrime l ^ d - 1) = 1 := by
    obtain h_root | ⟨rfl, -⟩ := h_roots x hx
    · grw [← hq, ← hc.rank_le.1]
      exact h_label.root_pow_eq_one h_root
    · exact ⟨one_pow _, 1, ⟨le_rfl, D.nat_le_of_hasLogBound⟩, one_pow _⟩
  have h_image (x : K) (e : ℕ) (hx : x ^ e = 1) : ιℓ ((T ^ a) x) ^ e = 1 := by simp [← map_pow, hx]
  -- the polynomial of the type polynomials kills `s`
  have h_kill {R : GalRep ℓ D.E m} {k : ℕ} {J : (D.E →+* ℂ) → Multiset ℤ} {S : Set (FinPlace D.E)}
      (hR : IsRepOfType (m := m) O k J (fun i ↦ scaledTypePoly O c i * (X - 1) ^ t) S R) :
      PolyKillsAt R A s (μ.map (X - C ·)).prod := by
    simpa [μ, Multiset.map_map, Function.comp_def] using hR.labelled h_tame
  refine ⟨μ,
    { card_eq := ?_
      pow_factorial_eq_one := forall_mem_map_iff.2 fun x hx ↦ h_image x _ (h_order x hx).1
      exists_pow_eq_one := forall_mem_map_iff.2 fun x hx ↦ ?_
      polyKillsAt := h_kill
      polyKillsAt_conjPlace := fun hR ↦ ?_ }, fun ht hs_gen h_one ↦ ?_⟩
  · obtain ⟨h_monic, -, h_deg, -⟩ := h_label
    simp [μ, roots, card_aroots_eq_natDegree, ← C_1,
      h_monic.natDegree_mul ((monic_X_sub_C 1).pow t), h_deg, -map_one]
  · obtain ⟨-, d, hd, h_pow_d⟩ := h_order x hx
    exact ⟨d, hd, h_image x _ h_pow_d⟩
  · -- duality carries the relation to the conjugate place
    have h_above : O.chosenPlace i ∈ placesAboveM D := ⟨l, hv⟩
    obtain ⟨h_fin, -⟩ := hR.local_conditions _ (by simp [h_above]) hA
    obtain ⟨-, -, h_dual⟩ := isFiniteTypeAt_and_hasJumpsAt_of_conjPlace hR.toIsConjSelfDual
      (A := conjPlace A) (by simpa using h_fin)
    exact h_dual s (by simpa) _ (by simpa using h_kill hR)
  · -- For the tame generator `a` is prime to the order of a root `x`, so `T x ^ a = 1` forces
    -- `x = 1`, which is not a root of the scaled type polynomial.
    obtain ⟨x, hx, hx_image⟩ : ∃ x ∈ roots, ιℓ ((T ^ a) x) = 1 := mem_map.1 h_one
    have hxa : x ^ a = 1 := by
      obtain rfl | ha := eq_or_ne a 0
      · exact pow_zero x
      · apply IsFaithfulMulChar.injective (T := T)
        simpa [← T.pow_apply' ha] using ιℓ.map_eq_one_iff.1 hx_image
    obtain rfl : x = 1 :=
      (pow_eq_one_iff_of_coprime (h_coprime hs_gen)).1 ⟨hxa, by simpa [hq] using (h_order x hx).1⟩
    exact hc.not_isRoot_scaledTypePoly i (by simpa [aeval_def, ht] using h_roots 1 hx)

/-- The eigenvalues of inertia above the two primes `D.levelPrime l` of the level. Let `v` be a
place of `D.E` dividing `p = D.levelPrime l` and `A` a place of `Ω = ℚ̄` over `v`. There is `γ` in
inertia at `A`, the fixed generator `hA.tameGenerator` of tame inertia if `v` is chosen, such that
each `s` in inertia has a multiset `μ` of `card r + t` possible eigenvalues (`IsInertiaSpectrum`),
with `1 ∉ μ` if `t = 0` and `s = γ`. These are roots of unity of order dividing `p ^ (card r)! - 1`
and some `p ^ d - 1`, `1 ≤ d ≤ D.r`, and the polynomial with roots `μ` kills `s` at `A`, and
`conjGal s⁻¹` at the conjugate place, in every rank `card m` representation whose type polynomials
are the `scaledTypePoly O c i` times `(X - 1) ^ t`. -/
lemma exists_inertiaGroup_isInertiaSpectrum (m : Type) [Fintype m] [DecidableEq m]
    (hc : IsLiftSetting O c ϑ)
    {l : Fin 2} {v : FinPlace D.E} (hv : (D.levelPrime l : 𝓞 D.E) ∈ v.asIdeal)
    {A : ClosurePlace} (hA : IsPlaceOver A v) (t : ℕ) :
    ∃ γ : inertiaGroup Gal(Ω/D.E) A,
      (D.IsChosen v → γ = hA.tameGenerator) ∧
      ∀ s ∈ inertiaGroup Gal(Ω/D.E) A, ∃ μ : Multiset (PadicAlgCl ℓ),
        IsInertiaSpectrum O c m l A t s μ ∧ (t = 0 → s = γ.val → 1 ∉ μ) := by
  -- The places above `D.levelPrime l` that are not chosen are the conjugates of chosen ones.
  wlog h_chosen : D.IsChosen v generalizing v A with at_chosen
  · obtain ⟨γ, -, hγ⟩ :=
      at_chosen (by simpa) hA.conjPlace_star ((D.isChosen_star_iff hv).2 h_chosen)
    use ⟨conjGal γ.val⁻¹, conjGal_mem_inertiaGroup_iff.1 (by simp)⟩, h_chosen.elim
    intro s hs
    obtain ⟨μ, hμ, h_one⟩ := hγ (conjGal s⁻¹) (inv_mem hs).conjPlace_conjGal
    exact ⟨μ, hμ.of_conjPlace, fun ht hs_eq ↦ h_one ht (by simp [hs_eq])⟩
  obtain ⟨i, rfl⟩ : ∃ i : O.ChosenIndex, O.chosenPlace i = v := by
    rw [hc.toLevelPlaces_eq]
    exact D.range_chosenPlace.ge h_chosen
  exact ⟨hA.tameGenerator, fun _ ↦ rfl, fun _ ↦ exists_isInertiaSpectrum_chosenPlace m hc hv hA t⟩

/-- Ramification of a representation of a type above `M = D.levelPrime 0 * D.levelPrime 1`. Let `R`
be a rank `card r` representation of a type (`IsRepOfType`) and empty level: conjugate self-dual of
weight `k` with Hodge–Tate jumps `J`, unramified off `ℓ M`, inertia at each `O.chosenPlace i` acting
through the roots of `scaledTypePoly O c i`. Let `A` lie over a place `v` that divides `M`
(`placesAboveM`) but not `ℓ`. Then `R` is trivial on the `N`-th powers of the inertia group of `A`
in `AbsGal D = Gal(Ω/D.E)` for some `N` that is a unit at `A`. For some `γ` in inertia, the fixed
tame generator if `v` is chosen, the `ℓ`-adic valuations of the determinants of `R γ - 1` and
`R (conjGal γ)⁻¹ - 1` are at most `card r` times that of `D.chosenGroupOrder`, the product of the
orders of `GL (D.r * D.t)` over the residue fields at the chosen places. Here `conjGal γ` is the
conjugate of `γ` by the chosen complex conjugation `cmConj` of `Ω`. -/
lemma IsRepOfType.exists_map_pow_eq_one_and_ellVal_det_le (hc : IsLiftSetting O c ϑ)
    {R : GalRep ℓ D.E r} {k : ℕ} {J : (D.E →+* ℂ) → Multiset ℤ}
    (hR : IsRepOfType (m := r) O k J (Selmer.scaledTypePoly O c) ∅ R) {v : FinPlace D.E}
    (hvM : v ∈ placesAboveM D) (hℓ : v ∉ placesDividing D.E ℓ) {A : ClosurePlace}
    (hA : IsPlaceOver A v) :
    ∃ (γ : inertiaGroup (AbsGal D) A) (N : ℕ),
      (D.IsChosen v → γ = hA.tameGenerator) ∧
      A.valuation (N : Ω) = 1 ∧
      (∀ s ∈ inertiaGroup (AbsGal D) A, R (s ^ N) = 1) ∧
      ellVal ((R γ).val - 1).det ≤ card r * padicValNat ℓ D.chosenGroupOrder ∧
      ellVal ((R (conjGal γ.val)⁻¹).val - 1).det ≤ card r * padicValNat ℓ D.chosenGroupOrder := by
  obtain ⟨l, hl⟩ : ∃ l : Fin 2, (D.levelPrime l : 𝓞 D.E) ∈ v.asIdeal := hvM
  have h_val : A.valuation ℓ = 1 := hA.valuation_natCast_eq_one_iff.mpr hℓ
  let N : ℕ := D.levelPrime l ^ (card r).factorial - 1
  have hR_zero : IsRepOfType (m := r) O k J
      (fun j ↦ Selmer.scaledTypePoly O c j * (X - 1) ^ 0) ∅ R := by simpa using hR
  -- `h_eigen s` gives a multiset `μ` containing the eigenvalues of `s` and of `(conjGal s)⁻¹`
  obtain ⟨γ, hγ, h_eigen⟩ := exists_inertiaGroup_isInertiaSpectrum (ℓ := ℓ) r hc hl hA 0
  refine ⟨γ, N, hγ, ?_, fun s hs ↦ ?_, ?_⟩
  · -- `D.levelPrime l` vanishes in the residue field, so `N` is `-1` there
    rw [hA.valuation_natCast_eq_one_iff]
    simp [N, ← algebraMap_ResField_eq_zero, ← D.q_eq_levelPrime hl, ← card_ResField, NeZero.pos,
      Nat.factorial_ne_zero]
  · -- the members of `μ` are roots of `X ^ N - 1`
    obtain ⟨μ, hμ, -⟩ := h_eigen s hs
    have h_pow : aeval (R s).val (X ^ N - 1 : (PadicAlgCl ℓ)[X]) = 0 :=
      (hR.local_conditions v (by simp) hA).1.aeval_eq_zero_of_roots h_val hs
        (hμ.polyKillsAt hR_zero) _
        (by simpa [eval_multiset_prod, sub_eq_zero] using hμ.pow_factorial_eq_one)
    simpa [Units.ext_iff, sub_eq_zero] using h_pow
  · -- both matrices are killed by the polynomial with roots `μ`
    obtain ⟨μ, hμ, h_one⟩ := h_eigen γ γ.prop
    have h_roots : ∀ y ∈ μ, y ≠ 1 ∧ ∃ d ∈ Set.Icc 1 D.r, y ^ (D.levelPrime l ^ d - 1) = 1 :=
      fun y hy ↦ ⟨ne_of_mem_of_not_mem hy (h_one rfl rfl), hμ.exists_pow_eq_one y hy⟩
    have h_val_conj : (conjPlace A).valuation ℓ = 1 := by
      simpa [hA.conjPlace_star.valuation_natCast_eq_one_iff]
    constructor
    · exact ellVal_det_sub_one_le_card_mul h_roots ((hμ.polyKillsAt hR_zero).1 h_val)
    · apply ellVal_det_sub_one_le_card_mul h_roots
      simpa using (hμ.polyKillsAt_conjPlace hR_zero).1 h_val_conj

variable (ℓ O c) in
/-- The roots of the scaled type polynomial `scaledTypePoly O c i`, taken in an algebraic closure of
the residue field of `O.chosenPlace i`, have the common `e`-th power `y`, of large order relative to
`j`. With `q` the order of the residue field, each root is fixed by the `q ^ card r`-th power, and
its Frobenius conjugates stay distinct after raising to powers of `ℓ`. -/
structure IsCommonRootPower (i : O.ChosenIndex) (j e : ℕ)
    (y : AlgebraicClosure (ResField (O.chosenPlace i))) : Prop where
  /-- Each root `ξ` has `ξ ^ e = y`. -/
  pow_eq : ∀ ξ ∈ (scaledTypePoly O c i).aroots (AlgebraicClosure (ResField (O.chosenPlace i))),
    ξ ^ e = y
  /-- Each root is fixed by the `q ^ card r`-th power. -/
  pow_q_pow_card_eq : ∀ ξ ∈ (scaledTypePoly O c i).aroots
    (AlgebraicClosure (ResField (O.chosenPlace i))), ξ ^ (O.chosenPlace i).q ^ card r = ξ
  /-- For each root `ξ` and each `u`, the powers `(ξ ^ q ^ a) ^ ℓ ^ u`, `a < card r`, are
  distinct. -/
  injOn_pow : ∀ ξ ∈ (scaledTypePoly O c i).aroots (AlgebraicClosure (ResField (O.chosenPlace i))),
    ∀ u : ℕ, (Set.Iio (card r)).InjOn fun a : ℕ ↦ (ξ ^ (O.chosenPlace i).q ^ a) ^ ℓ ^ u
  /-- If `y ^ x = 1` then `P.q₂ D.towerExp`, the order of `D.chiMLocal` at the chosen places,
  divides `j * x`. -/
  dvd_of_pow_eq_one (x : ℕ) (hx : y ^ x = 1) : P.q₂ D.towerExp ∣ j * x

omit [PadicIso ℓ] in
/-- Let `c` be a lift setting for the descent pair `O` and the twist `ϑ`, so that `c i` is a type
polynomial over the residue field, of order `q`, of the place `O.chosenPlace i` above the level, and
let `O.tamePart = D.chiMLocal ^ j * ϑ.tamePart`, where `D.chiMLocal` has order `N = P.q₂ D.towerExp`
at the chosen places (`P`: the parameters of the data `D`). Let `card r = D.r` and let `c i` be a
primitive polynomial: monic irreducible of degree `card r` with a root of order `q ^ card r - 1`.
Then the roots `ξ` of the scaled type polynomial `scaledTypePoly O c i` have a common `e`-th power
`y` such that, for every `x : ℕ`, `y ^ x = 1` forces `N ∣ j * x`; moreover (`IsCommonRootPower`)
`ξ ^ q ^ card r = ξ`, and for each `u` the powers `(ξ ^ q ^ a) ^ ℓ ^ u`, `a < card r`, are
distinct. -/
lemma IsLiftSetting.exists_isCommonRootPower_of_isPrimitivePolynomial (hc : IsLiftSetting O c ϑ)
    {i : O.ChosenIndex} (h_card : card r = D.r)
    (h_primitive : IsPrimitivePolynomial (card r) (c i)) {j : ℕ}
    (h_tamePart : O.tamePart = D.chiMLocal ^ (j : ℤ) * ϑ.tamePart) :
    ∃ (e : ℕ) (y : AlgebraicClosure (ResField (O.chosenPlace i))),
      IsCommonRootPower ℓ O c i j e y := by
  -- A primitive polynomial stays primitive after normalisation; `y` is the product of its roots.
  have h_chosen : D.IsChosen (O.chosenPlace i) := hc.isChosen_chosenPlace i
  obtain ⟨l, hl⟩ : O.chosenPlace i ∈ placesAboveM D := h_chosen.mem_placesAboveM
  obtain ⟨r_exp, hr_exp⟩ := D.exists_r_eq_three_pow
  -- `q = D.levelPrime l`, so `q₂ ^ 2` divides `q - 1`; and so does `9`, as `3 ∣ 18480 ∣ q₀ ∣ q₂`
  have h_Mω_sq : P.q₂ D.towerExp ^ 2 ∣ Nat.card (ResField (O.chosenPlace i)) - 1 := by
    simpa only [card_ResField, D.q_eq_levelPrime hl] using D.dvd_levelPrime_sub_one l
  have h_nine : 3 ^ 2 ∣ Nat.card (ResField (O.chosenPlace i)) - 1 := by
    refine (pow_dvd_pow_of_dvd ?_ 2).trans h_Mω_sq
    exact dvd_pow ((Nat.dvd_trans (by norm_num) P.dvd_q₀).mul_right P.d) (by omega)
  have h_tamePart_pow : O.tamePart (O.chosenPlace i) ^ P.q₂ D.towerExp = 1 := by
    rw [h_tamePart, D.chiMLocal_zpow_mul_pow_eq_one j (ϑ.tamePart_eq_one_of_isChosen h_chosen)]
  have h_twisted : IsPrimitivePolynomial (card r) (Selmer.scaledTypePoly O c i) :=
    h_primitive.scaleRoots _ (charName_pow_eq_one (by simp [h_tamePart_pow])) h_Mω_sq
  let K : Type := AlgebraicClosure (ResField (O.chosenPlace i))
  let roots : Multiset K := (Selmer.scaledTypePoly O c i).aroots K
  obtain ⟨h_prod, e, h_pow⟩ :
      IsPrimitiveRoot roots.prod (Nat.card (ResField (O.chosenPlace i)) - 1) ∧
      ∃ e : ℕ, ∀ ξ ∈ roots, ξ ^ e = roots.prod :=
    h_twisted.isPrimitiveRoot_prod_aroots_and_exists_pow_eq
  obtain ⟨⟨-, -, h_deg, -⟩, h_irred, η, hη, hη_order⟩ := h_twisted
  refine ⟨e, roots.prod,
    { pow_eq := h_pow
      pow_q_pow_card_eq := fun ξ hξ ↦ ?_
      injOn_pow := fun ξ hξ u a ha b hb hab ↦ ?_
      dvd_of_pow_eq_one := fun x hx ↦ ?_ }⟩
  · -- the type polynomial is irreducible of degree `card r`
    rw [← card_ResField, root_pow_card_pow_eq_self_iff h_irred (mem_aroots.mp hξ).2, h_deg]
  · -- `ξ` is a Frobenius conjugate of the primitive root `η`; as `9 ∣ q - 1` and `card r` is a
    -- power of `3`, the conjugates of `η ^ ℓ ^ u` are distinct
    obtain ⟨d, -, rfl⟩ := exists_pow_card_pow_eq_of_root h_irred (mem_aroots.mp hξ).2 hη
    rw [h_card, hr_exp] at hη_order ha hb
    apply injOn_Iio_pow_card_pow_of_isPrimitiveRoot u h_nine hη_order hp.out ha hb
    have h_comm (q a : ℕ) : ((ξ ^ q ^ d) ^ ℓ ^ u) ^ q ^ a = ((ξ ^ q ^ a) ^ ℓ ^ u) ^ q ^ d := by ring
    simp only [h_comm, card_ResField, hab]
  · -- `y` has order `q - 1`, a multiple of `q₂ ^ 2`
    grw [dvd_pow_self (P.q₂ D.towerExp) two_ne_zero, h_Mω_sq, h_prod.dvd_of_pow_eq_one x hx]
    exact dvd_mul_left x j

omit hp [PadicIso ℓ] in
/-- Let `c` be a lift setting for the descent pair `O` and the twist `ϑ`, so that `c i` is a type
polynomial over the residue field, of order `q`, of the place `O.chosenPlace i` above the level, and
let `O.tamePart = D.chiMLocal ^ j * ϑ.tamePart`, where `D.chiMLocal` has order
`N = P.q₂ D.towerExp` at the chosen places (`P`: the parameters of the data `D`). Let `card r = 1`
and `c i = X - 1`, so that `scaledTypePoly O c i` has as only root `ξ` the element naming
`O.tamePart⁻¹`. Then some power `y = ξ ^ e` has the property that, for every `x : ℕ`, `y ^ x = 1`
forces `N ∣ j * x`; moreover (`IsCommonRootPower`) `ξ ^ q = ξ`, the remaining condition being
empty in rank `1`. -/
lemma IsLiftSetting.exists_isCommonRootPower_of_eq_X_sub_one (hc : IsLiftSetting O c ϑ)
    {i : O.ChosenIndex} (h_card : card r = 1) (h_eq : c i = X - 1) {j : ℕ}
    (h_tamePart : O.tamePart = D.chiMLocal ^ (j : ℤ) * ϑ.tamePart) :
    ∃ (e : ℕ) (y : AlgebraicClosure (ResField (O.chosenPlace i))),
      IsCommonRootPower ℓ O c i j e y := by
  -- The only root is the name `z` of `ω⁻ʲ`, where the character
  -- `ω = D.chiMLocal (O.chosenPlace i)` has order `q₂`.
  have h_chosen : D.IsChosen (O.chosenPlace i) := hc.isChosen_chosenPlace i
  let K : Type := AlgebraicClosure (ResField (O.chosenPlace i))
  let z : (ResField (O.chosenPlace i))ˣ :=
    charName (faithfulChar (ResField (O.chosenPlace i))) (O.tamePart (O.chosenPlace i))⁻¹
  let y : K := algebraMap _ K z.val
  have h_scaled_eq : Selmer.scaledTypePoly O c i = X - C z.val := by
    rw [Selmer.scaledTypePoly, h_eq, ← C_1, X_sub_C_scaleRoots, one_mul]
  have h_root (ξ : K) (hξ : ξ ∈ (Selmer.scaledTypePoly O c i).aroots K) : ξ = y := by
    simpa [h_scaled_eq] using hξ
  refine ⟨1, y,
    { pow_eq := fun ξ hξ ↦ by rw [pow_one, h_root ξ hξ]
      pow_q_pow_card_eq := fun ξ hξ ↦ ?_
      injOn_pow := fun ξ hξ u a ha b hb _ ↦ ?_
      dvd_of_pow_eq_one := fun x hx ↦ ?_ }⟩
  · simp [h_root ξ hξ, h_card, y, ← card_ResField, ← map_pow, FiniteField.pow_card]
  · -- the only index below `card r = 1` is `0`
    rw [h_card, Set.mem_Iio] at ha hb
    omega
  · have hz : z ^ x = 1 := by simpa [y, K, ← map_pow, ← Units.val_pow_eq_pow_val] using hx
    have hω : O.tamePart (O.chosenPlace i) = D.chiMLocal (O.chosenPlace i) ^ j := by
      simp [h_tamePart, ϑ.toTameChar.tamePart_eq_one_of_isChosen h_chosen]
    rw [← D.orderOf_chiMLocal h_chosen, orderOf_dvd_iff_pow_eq_one, pow_mul, ← hω]
    simpa [z, ← map_pow, MulEquiv.map_eq_one_iff] using hz

omit [PadicIso ℓ] in
/-- Let `c` be a lift setting for the descent pair `O` and the twist `ϑ`, so that `c i` is a type
polynomial over the residue field, of order `q`, of the place `O.chosenPlace i` above the level, and
let `O.tamePart = D.chiMLocal ^ j * ϑ.tamePart`, where `D.chiMLocal` has order `N = P.q₂ D.towerExp`
at the chosen places (`P`: the parameters of the data `D`). Let `c i` be primitive with
`card r = D.r`, or `X - 1` with `card r = 1`. Then the roots `ξ` of `scaledTypePoly O c i` have a
common `e`-th power `y` such that, for every `x : ℕ`, `y ^ x = 1` forces `N ∣ j * x`; moreover
`ξ ^ q ^ card r = ξ`, and for each `u` the powers `(ξ ^ q ^ a) ^ ℓ ^ u`, `a < card r`, are
distinct. -/
lemma IsLiftSetting.exists_isCommonRootPower (hc : IsLiftSetting O c ϑ) {i : O.ChosenIndex}
    (h_primitive_or_one :
      (card r = D.r ∧ IsPrimitivePolynomial (card r) (c i)) ∨ (card r = 1 ∧ c i = X - 1))
    {j : ℕ} (h_tamePart : O.tamePart = D.chiMLocal ^ (j : ℤ) * ϑ.tamePart) :
    ∃ (e : ℕ) (y : AlgebraicClosure (ResField (O.chosenPlace i))),
      IsCommonRootPower ℓ O c i j e y := by
  obtain ⟨h_card, h_primitive⟩ | ⟨h_card, h_eq⟩ := h_primitive_or_one
  · exact hc.exists_isCommonRootPower_of_isPrimitivePolynomial h_card h_primitive h_tamePart
  · exact hc.exists_isCommonRootPower_of_eq_X_sub_one h_card h_eq h_tamePart

/-- Let `c` be a lift setting for the descent pair `O` and the twist `ϑ`. Let `R` be a rank `card r`
representation of `AbsGal D = Gal(Ω/D.E)` over `ℚ̄_ℓ` of empty level whose inertia at each chosen
place acts through the roots of `scaledTypePoly O c i` (`IsRepOfType`), these being the roots of
`c i` times the element naming `O.tamePart⁻¹`. Let the place `A` of `Ω = ℚ̄` lie over
`O.chosenPlace i` and not over `ℓ`. There are `s` in inertia at `A` and an injective multiplicative
map `τ` from the algebraic closure of the residue field to `ℚ̄_ℓ` such that `R s` is killed by every
polynomial that vanishes on the images of the roots of the scaled type polynomial, and one image
`τ ξ`, a root of unity, is an eigenvalue of `R s`. -/
lemma IsRepOfType.exists_inertia_isRoot_charpoly (hc : IsLiftSetting O c ϑ) {R : GalRep ℓ D.E r}
    {k : ℕ} {J : (D.E →+* ℂ) → Multiset ℤ}
    (hR : IsRepOfType (m := r) O k J (Selmer.scaledTypePoly O c) ∅ R) {i : O.ChosenIndex}
    {A : ClosurePlace} (hA : IsPlaceOver A (O.chosenPlace i)) (h_val : A.valuation ℓ = 1) :
    ∃ (s : inertiaGroup (AbsGal D) A)
      (τ : AlgebraicClosure (ResField (O.chosenPlace i)) →* PadicAlgCl ℓ),
      Function.Injective τ ∧
      (∀ p : (PadicAlgCl ℓ)[X],
        (∀ η ∈ (Selmer.scaledTypePoly O c i).aroots (AlgebraicClosure (ResField (O.chosenPlace i))),
          p.IsRoot (τ η)) → aeval (R s).val p = 0) ∧
      ∃ ξ ∈ (Selmer.scaledTypePoly O c i).aroots (AlgebraicClosure (ResField (O.chosenPlace i))),
        (R s).val.charpoly.IsRoot (τ ξ) ∧ IsOfFinOrder (τ ξ) := by
  -- `s` has tame exponent `1`, and `τ` is the faithful character followed by `ιℓ`
  let K : Type := AlgebraicClosure (ResField (O.chosenPlace i))
  let T : MulChar K ℂ := faithfulChar _
  let τ : K →* PadicAlgCl ℓ := ιℓ.toMonoidHom.comp T
  let Z : Multiset K := (Selmer.scaledTypePoly O c i).aroots K
  obtain ⟨⟨s, hs⟩, -⟩ := GaloisRep.exists_isTameExponent T hA (card r)
  have h_poly : PolyKillsAt R A s (Z.map fun ξ ↦ X - C (τ ξ)).prod := by
    simpa [τ] using hR.labelled hs
  have h_root (x : PadicAlgCl ℓ) (hx : (Z.map fun ξ ↦ X - C (τ ξ)).prod.IsRoot x) :
      ∃ ξ ∈ Z, x = τ ξ := by
    simpa [eval_multiset_prod, sub_eq_zero] using hx
  refine ⟨s, τ, ιℓ.injective.comp IsFaithfulMulChar.injective, fun p hp_root ↦ ?_, ?_⟩
  · have h_fin : IsFiniteTypeAt R A := (hR.local_conditions _ (by simp) hA).1
    refine h_fin.aeval_eq_zero_of_roots h_val s.prop h_poly p fun x hx ↦ ?_
    obtain ⟨ξ, hξ, rfl⟩ := h_root x hx
    exact hp_root ξ hξ
  · obtain ⟨ζ, hζ⟩ := exists_root (R s).val.charpoly (by simp [hc.odd.1.pos.ne'])
    obtain ⟨ξ, hξ, rfl⟩ := h_root ζ (isRoot_of_isRoot_charpoly (h_poly.1 h_val) hζ)
    obtain ⟨h_pow, -⟩ := ((hc.isLabel i).scaleRoots _).root_pow_eq_one (mem_aroots'.1 hξ).2
    exact ⟨ξ, hξ, hζ, τ.isOfFinOrder
      (isOfFinOrder_iff_pow_eq_one.2 ⟨_, by simp [FinPlace.one_lt_q, NeZero.ne], h_pow⟩)⟩

omit [PadicIso ℓ] in
/-- Let `A` be a place of `Ω = ℚ̄`, not over `ℓ`, over the place `w` dividing `D.levelPrime l`, with
residue field of order `q`. Let the representation `R` of rank `card r` have finite type at `A` and
be trivial on the `N`-th powers of inertia, `N` a unit at `A`. Let `s` in inertia have
`R (s ^ q ^ card r) = R s` and an eigenvalue `ζ`, a root of unity, whose conjugates `ζ ^ q ^ a`,
`a < card r`, are pairwise incongruent. Then over all large coefficient rings the image of a lattice
in `R` spans all matrices and has a scalar matrix at an element of cyclotomic character
`D.levelPrime m ^ card r` for some `m`. -/
lemma eventually_span_eq_top_and_exists_scalar_of_tame_pair {R : GalRep ℓ D.E r} {l : Fin 2}
    {w : FinPlace D.E} (hlw : ↑(D.levelPrime l) ∈ w.asIdeal) {A : ClosurePlace}
    (hA : IsPlaceOver A w) (h_val : A.valuation ℓ = 1) (h_fin : IsFiniteTypeAt R A) {N : ℕ}
    (hN : A.valuation (N : Ω) = 1) (hRN : ∀ s ∈ inertiaGroup (AbsGal D) A, R (s ^ N) = 1)
    {s : inertiaGroup (AbsGal D) A} {ζ : PadicAlgCl ℓ} (h_ord : IsOfFinOrder ζ)
    (h_eigen : (R s).val.charpoly.IsRoot ζ) (h_fix : R (s ^ w.q ^ card r) = R s)
    (h_dist : ∀ a < card r, ∀ b < card r, a ≠ b → ‖ζ ^ w.q ^ a - ζ ^ w.q ^ b‖ = 1) :
    ∀ᶠ 𝒪 : CoeffRing ℓ in Filter.atTop, ∀ u : AbsGal D →* Matrix r r 𝒪,
      IsLatticeIn R u →
      Submodule.span 𝒪 (Set.range u) = ⊤ ∧
      ∃ (g : AbsGal D) (m : Fin 2) (α : ↑𝒪),
        (cyclotomicChar Ω ℓ g).val = D.levelPrime m ^ card r ∧ u g = α • 1 := by
  -- conjugation by a Frobenius `φ` raises `R s` to the `q`-th power
  obtain ⟨φ, hφ⟩ := hA.exists_isFrob (AbsGal D)
  have h_frob : R s ^ w.q = R (φ * s * φ⁻¹) :=
    ((hA.tame_inertia R (h_fin.1 h_val) hN (by simpa using hRN) s).2 w.q φ hφ).symm
  filter_upwards [CoeffRing.eventually_mem h_ord.norm_eq_one.le] with 𝒪 h_mem u hu
  -- the image of the lattice `u` spans all matrices over `𝒪`, and `φ ^ card r` acts by a scalar
  obtain ⟨h_span, α, hα⟩ :=
    hu.span_range_eq_top_of_map_pow_eq_map_conj (ζ := ⟨ζ, h_mem⟩) (φ := φ⁻¹) h_frob h_dist
      h_eigen h_fix
  refine ⟨h_span, φ ^ card r, l, α, ?_, by rwa [inv_inv] at hα⟩
  simp [hφ.cyclotomicChar_eq ℓ h_val, D.q_eq_levelPrime hlw]

/-- Let `c` be a lift setting for the descent pair `O` and the twist `ϑ`, and let
`M = D.levelPrime 0 * D.levelPrime 1`. Let `R` be a representation of a type of rank `card r` and
empty level: in particular `R^c ≅ R^∨(1 - k)` on traces, `R` has Hodge–Tate jumps `J` and is
unramified off `ℓ M`, and inertia at `O.chosenPlace i` acts through the roots of
`scaledTypePoly O c i`. Let `k` and `J` satisfy `IsMainSummandWeights`: `k ≤ D.t`; for one
`j ≤ D.m` each jump `u` has `D.gap / 4 ≤ |u| ≤ 2 D.m D.gap` or is within `D.t` of `-D.liftWeight j`
(of `D.liftWeight j` at embeddings outside the CM type); at most `card r * D.m / D.k` jumps at an
embedding have `|u| ≤ 2 D.halfGap ^ 2`, and at most `card r` at a conjugate pair are negative. Then
`R` is like a main summand (`IsMainSummandLike`): above `M` and off `ℓ`, inertia is killed by a
power prime to the place and, for some inertia element `γ`, `det (R γ - 1)` and
`det (R (conjGal γ)⁻¹ - 1)` have valuation at most `card r` times that of `D.chosenGroupOrder`; over
all large coefficient rings the image of a lattice spans all matrices and has a scalar at an element
of cyclotomic character `D.levelPrime m ^ card r`; and an inertia element above `M` acts by a scalar
`y` with `y ^ (ℓ ^ a * t) - 1` a unit for all `a` and `1 ≤ t ≤ 4 * card r + 2`. -/
lemma IsRepOfType.isMainSummandLike (hc : IsLiftSetting O c ϑ) {R : GalRep ℓ D.E r} {k : ℕ}
    {J : (D.E →+* ℂ) → Multiset ℤ} (hR : IsRepOfType (m := r) O k J (Selmer.scaledTypePoly O c) ∅ R)
    (hJ : IsMainSummandWeights D (card r) k J) : IsMainSummandLike D k J R := by
  -- Take a chosen place `w` not above `ℓ` whose type polynomial is primitive or `X - 1`, and `s` in
  -- inertia at `w` of tame exponent `1`; the eigenvalues of `R s` come from the roots of the scaled
  -- type polynomial, `R s` and a Frobenius generate all matrices, and a power of `s` acts by a
  -- scalar of large order.
  obtain ⟨l, hl⟩ : ∃ l : Fin 2, D.levelPrime l ≠ ℓ := D.levelPrime_injective.exists_ne ℓ
  obtain ⟨i, hli, h_primitive_or_one⟩ := hc.exists_primitive_or_one l
  obtain ⟨j, hj, h_tamePart⟩ :
      ∃ j ∈ Set.Icc 1 D.m, O.tamePart = D.chiMLocal ^ (j : ℤ) * ϑ.tamePart :=
    hc.exists_tamePart_eq_chiMLocal_zpow_mul
  -- the roots of the scaled type polynomial have the common `e`-th power `y`, of large order
  obtain ⟨e, y, hy⟩ := hc.exists_isCommonRootPower (ℓ := ℓ) h_primitive_or_one h_tamePart
  let w : FinPlace D.E := O.chosenPlace i
  obtain ⟨A, hA⟩ : ∃ A : ClosurePlace, IsPlaceOver A w := ⟨_, w.isPlaceOver_placeOver⟩
  have hwℓ : w ∉ placesDividing D.E ℓ :=
    fun hw ↦ hl ((FinPlace.charP_quotient w hli).eq _ (FinPlace.charP_quotient w hw))
  have hwM : w ∈ placesAboveM D := ⟨l, hli⟩
  have h_val : A.valuation ℓ = 1 := hA.valuation_natCast_eq_one_iff.2 hwℓ
  -- `τ ξ` is an eigenvalue of `R s`
  obtain ⟨s, τ, hτ, h_kill, ξ, hξ, h_eigen, h_ord⟩ := hR.exists_inertia_isRoot_charpoly hc hA h_val
  have h_fin : IsFiniteTypeAt R A := (hR.local_conditions w (by simp) hA).1
  have h_fix : R (s ^ w.q ^ card r) = R s := by
    have h_aeval : aeval (R s).val (X ^ w.q ^ card r - X : (PadicAlgCl ℓ)[X]) = 0 := by
      refine h_kill _ fun η hη ↦ ?_
      rw [IsRoot, eval_sub, eval_X_pow, ← map_pow, hy.pow_q_pow_card_eq η hη, eval_X, sub_self]
    simpa [Units.ext_iff, sub_eq_zero] using h_aeval
  have h_dist (a : ℕ) (ha : a < card r) (b : ℕ) (hb : b < card r) (hab : a ≠ b) :
      ‖τ ξ ^ w.q ^ a - τ ξ ^ w.q ^ b‖ = 1 :=
    norm_pow_sub_pow_eq_one h_ord _ _ fun u hu ↦
      hab (hy.injOn_pow ξ hξ u ha hb (hτ (by simpa using hu)))
  obtain ⟨-, N, -, hN, hRN, -⟩ := hR.exists_map_pow_eq_one_and_ellVal_det_le hc hwM hwℓ hA
  have h_large := eventually_span_eq_top_and_exists_scalar_of_tame_pair hli hA h_val h_fin hN hRN
    h_ord h_eigen h_fix h_dist
  -- the scalar is `R (s ^ e) = τ y`, as `X ^ e - τ y` kills `R s`
  have h_scalar : (R ↑(s ^ e)).val = τ y • 1 := by
    have h_aeval : aeval (R s).val (X ^ e - C (τ y) : (PadicAlgCl ℓ)[X]) = 0 :=
      h_kill _ fun η hη ↦ by simp [← map_pow, hy.pow_eq η hη]
    simpa [Algebra.smul_def, sub_eq_zero] using h_aeval
  -- `y ^ (ℓ ^ a * t)` does not have `ℓ`-power order, as `q₂` does not divide `j * ℓ ^ b * t`
  have h_unit (a t : ℕ) (ht : t ∈ Set.Icc 1 (4 * card r + 2)) :
      ‖τ y ^ (ℓ ^ a * t) - 1‖ = 1 := by
    have ht_le : t ∈ Set.Icc 1 (4 * D.r + 2) := ⟨ht.1, by grw [ht.2, hc.rank_le.1]⟩
    have h_ne (u : ℕ) : y ^ (ℓ ^ (a + u) * t) ≠ 1 :=
      fun hu ↦ not_q₂_dvd_mul_pow_mul hj ht_le (a + u) (hy.dvd_of_pow_eq_one _ hu)
    have hτy : τ y = τ ξ ^ e := by rw [← map_pow, hy.pow_eq ξ hξ]
    have h_norm : ‖τ ξ ^ (e * ℓ ^ a * t) - τ ξ ^ 0‖ = 1 := by
      refine norm_pow_sub_pow_eq_one h_ord _ _ fun u hu ↦ h_ne u (hτ ?_)
      simpa [hτy, pow_mul, pow_add, pow_right_comm] using hu
    simpa [hτy, pow_mul] using h_norm
  have h_inertia : (↑(s ^ e) : AbsGal D) ∈
      inertiaAbove (placesAboveM D \ placesDividing D.E ℓ) :=
    ⟨w, ⟨hwM, hwℓ⟩, A, hA, (s ^ e).prop⟩
  exact
    { hR.toIsConjSelfDualOfLevel, hJ with
      inertia_above_M := fun v ⟨hvM, hvℓ⟩ B ↦
        hR.exists_map_pow_eq_one_and_ellVal_det_le hc hvM hvℓ
      span_eq_top := h_large.mono fun 𝒪 h𝒪 u hu ↦ (h𝒪 u hu).1
      exists_scalar_cyclotomicChar := h_large.mono fun 𝒪 h𝒪 u hu ↦ (h𝒪 u hu).2
      exists_scalar_inertia := ⟨↑(s ^ e), h_inertia, τ y, h_scalar, h_unit⟩ }

/-- Let `ϑ` be a twist, that is, a tame Hecke character with tame part `ϑ.tamePart` non-trivial on
its set of places `ϑ.Q`, and let `ϑ.invAvatar` be the `ℓ`-adic avatar of `ϑ⁻¹`, the Galois character
with values in `ℚ̄_ℓ` obtained through the fixed isomorphism `ιℓ : ℂ ≅ ℚ̄_ℓ`. Let `A` be a place of
`Ω = ℚ̄` not over `ℓ`, let `w` be a place in `ϑ.Q` different from its conjugate `star w`, with
residue field `k` of order `q`, and let `T = faithfulChar k` be the fixed injective character of the
algebraic closure of `k`. Let `s` have tame exponent `a` of level `f` at `A` over `w`: `s` is in
inertia, and `T` sends the residue of `s z / z` to `exp (2πi / (q ^ f - 1)) ^ a` for a
`(q ^ f - 1)`-th root `z` of a uniformiser. Then `ϑ.invAvatar` sends `s` to `ιℓ ((T ^ a) x⁻¹)`,
where `x` is the unit of `k` that corresponds to the character `ϑ.tamePart w` under the isomorphism
`charName T`. -/
lemma invAvatar_eq_of_isTameExponent {w : FinPlace D.E} (hw : w ∈ ϑ.Q) (h_split : star w ≠ w)
    {A : ClosurePlace} (h_val : A.valuation ℓ = 1) {s : AbsGal D} {f a : ℕ}
    (ha : IsTameExponent w A (faithfulChar (ResField w)) f s a) :
    ϑ.invAvatar (ℓ := ℓ) s = ιℓ ((faithfulChar (ResField w) ^ a)
      (algebraMap (ResField w) (AlgebraicClosure (ResField w))
        (charName (faithfulChar (ResField w)) (ϑ.tamePart w)).val)⁻¹) := by
  have h_star : ϑ.tamePart⁻¹ (star w) = 1 := by simp [ϑ.tamePart_eq_one _ (ϑ.star_notMem w hw)]
  -- the avatar, as a one-dimensional representation, is labelled by `X - x⁻¹` at `w`
  have h_kill : aeval
      ((GeneralLinearGroup.scalar (Fin 1)).comp
        (ϑ.hasWeight.inv.toAlgebraic 0 0).avatar s).val
      ((((X - C (charName (faithfulChar (ResField w)) (ϑ.tamePart⁻¹ w)).val).aroots
        (AlgebraicClosure (ResField w))).map fun x ↦
          X - C (ιℓ ((faithfulChar (ResField w) ^ a) x))).prod : (PadicAlgCl ℓ)[X]) = 0 :=
    (isLabelledAt_avatar (ℓ := ℓ) ϑ.hasWeight.inv 0 0 h_star h_split ha).1 h_val
  -- on `1 × 1` scalar matrices this says that the avatar takes the value `ιℓ ((T ^ a) x⁻¹)`
  simpa [algebraMap_eq_diagonal, funext_iff, Data.TameChar.invAvatar, sub_eq_zero] using h_kill

/-- Each place `O.twistPlace i` of the twist of the pair `O` differs from its conjugate. -/
lemma isSplit_twistPlace (O : DescentPair D.E r n) (i : O.TwistIndex) : (O.twistPlace i).IsSplit :=
  O.apart.star_ne (.inr i) (.inr i)

variable (O) in
/-- The function `f` on the finite adelic unitary group `Gf D.E n`, with values in the coordinates
`WeylIndex n O.columnCount → ℂ` of the Weyl module of weight `O.columnCount`, has the parahoric type
(`New.HasParahoricType`) of the pair `O` at `w = O.twistPlace i`, a place of the twist of `O`.
Block `0` is empty; block `1` is the complement of the range of the embedding `O.incl : r ↪ n`, with
the trivial character; block `2` is that range, with the character `(O.tamePart w)⁻¹`. So an
integral matrix at `w` whose reduction is block triangular multiplies `f` by `(O.tamePart w)⁻¹` of
the determinant of block `2` of the reduction. -/
def HasTwistParahoricType [DecidableEq n] (f : Gf D.E n → WeylIndex n O.columnCount → ℂ)
    (i : O.TwistIndex) : Prop :=
  HasParahoricType f (isSplit_twistPlace O i) (ρ := Empty) Function.Embedding.ofIsEmpty
    (fun a : n ↦ if a ∈ Set.range O.incl then 2 else 1) 1 ![1, (O.tamePart (O.twistPlace i))⁻¹]
    fun _ : GL Empty (ResField (O.twistPlace i)) ↦ f

omit [PadicIso ℓ] in
/-- If `ϑ.Q` is auxiliary (`IsAuxiliary`) for the places dividing `ℓ p₀ p₁ N` (`badPlaces D ℓ`),
then no place `w` of `ϑ.Q` or of its conjugate divides `ℓ`, that is, `ℓ ∉ w.asIdeal`. -/
lemma natCast_notMem_of_mem_conjClosure (hQ : IsAuxiliary (badPlaces D ℓ) ϑ.Q) {w : FinPlace D.E}
    (hwQ : w ∈ Set.conjClosure ϑ.Q) : (ℓ : 𝓞 D.E) ∉ w.asIdeal := by
  have h_bad {v : FinPlace D.E} (hv : v ∈ placesDividing D.E ℓ) : v ∉ ϑ.Q :=
    fun hvQ ↦ (hQ v hvQ).1 (placesDividing_union_subset_badPlaces D ℓ (.inl hv))
  exact fun hw ↦ hwQ.elim (h_bad hw) (h_bad (star_mem_placesDividing.2 hw))

/-- Let `c` be a lift setting (`IsLiftSetting`) for the descent pair `O` and `ϑ`: the places
`O.twistPlace i` are those of `ϑ.Q`, and `O.tamePart` agrees with `ϑ.tamePart` there. Let `ϑ.Q` be
auxiliary for the places dividing `ℓ * D.levelPrime 0 * D.levelPrime 1 * D.N` (`badPlaces D ℓ`): its
places have prime norm, and neither they nor their conjugates are bad. Let `R` be attached
(`Attached`) to the Hecke polynomials `H` of an eigenform `f`. Suppose that at each `O.twistPlace i`
the form `f` has the parahoric type of `O`: block triangular integral matrices act through
`O.tamePart⁻¹` of the determinant of the block indexed by `r`. Let `A` lie over a place `w` in
`Set.conjClosure ϑ.Q`. Then `R` has finite type at `A`. Also `(X - a s) (X - 1)` kills each `s` in
the inertia group of `A`, where `a = ϑ.invAvatar` is the `ℓ`-adic avatar of `ϑ⁻¹`. -/
lemma isFiniteTypeAt_and_polyKillsAt_of_mem_conjClosure [DecidableEq n] [Nonempty n]
    (hc : IsLiftSetting O c ϑ) (hQ : IsAuxiliary (badPlaces D ℓ) ϑ.Q)
    {f : (stdSpace D.E n).forms (O.columnCount, O.detExp)} {H : FinPlace D.E → ℂ[X]}
    {R : Gal(Ω/D.E) →* GL n (PadicAlgCl ℓ)} (he : IsEigenform f.val H) (hR : Attached H R)
    (h_type : ∀ i : O.TwistIndex, HasTwistParahoricType O f.val i) {w : FinPlace D.E}
    (hwQ : w ∈ Set.conjClosure ϑ.Q) {A : ClosurePlace} (hA : IsPlaceOver A w) :
    IsFiniteTypeAt R A ∧
      ∀ s ∈ inertiaGroup (AbsGal D) A, PolyKillsAt R A s ((X - C (ϑ.invAvatar s)) * (X - 1)) := by
  -- At a place of `Q` inertia acts through `1` and the tame character of `ϑ.tamePart⁻¹`; duality
  -- carries both clauses to the conjugate places.
  wlog hw : w ∈ ϑ.Q generalizing w A with at_Q
  · have hw_star : star w ∈ ϑ.Q := hwQ.resolve_left hw
    obtain ⟨h_fin_conj, h_poly⟩ := at_Q (.inl hw_star) hA.conjPlace_star hw_star
    obtain ⟨h_fin, -, h_dual⟩ :=
      isFiniteTypeAt_and_hasJumpsAt_of_conjPlace (isConjSelfDual_of_attached he hR) h_fin_conj
    refine ⟨h_fin, fun s hs ↦ ?_⟩
    have hs_conj : conjGal s⁻¹ ∈ inertiaGroup (AbsGal D) (conjPlace A) := by simpa using hs
    have h_av : ϑ.invAvatar (ℓ := ℓ) (conjGal s⁻¹) = ϑ.invAvatar s := by
      simp [eq_inv_of_mul_eq_one_left (avatar_conjGal_mul_avatar _ 0 0 s), Data.TameChar.invAvatar]
    have h_kill : PolyKillsAt R (conjPlace A) (conjGal s⁻¹)
        ((X - C (ϑ.invAvatar s)) * (X - 1)) := by
      rw [← h_av]
      exact h_poly _ hs_conj
    simpa using h_dual _ hs_conj _ h_kill
  obtain ⟨i, rfl⟩ : ∃ i : O.TwistIndex, O.twistPlace i = w := by
    rw [hc.toLevelPlaces_eq]
    exact ⟨⟨w, hw⟩, rfl⟩
  let K : Type := AlgebraicClosure (ResField (O.twistPlace i))
  let T : MulChar K ℂ := faithfulChar _
  have h_val : A.valuation ℓ = 1 :=
    hA.valuation_natCast_eq_one_iff.2 (natCast_notMem_of_mem_conjClosure hQ hwQ)
  -- `D.chiMLocal` is trivial at `Q`, so there `O.tamePart = D.chiMLocal ^ j * ϑ.tamePart` is
  -- `ϑ.tamePart`
  have h_tamePart : O.tamePart (O.twistPlace i) = ϑ.tamePart (O.twistPlace i) := by
    obtain ⟨j, -, hj⟩ := hc.exists_tamePart_eq_chiMLocal_zpow_mul
    obtain ⟨-, h_not_chosen, -⟩ := D.normQ_mem_and_notMem_of_mem_Q _ hwQ
    simp [hj, D.chiMLocal_eq_one_of_not_isChosen h_not_chosen]
  have h_split : star (O.twistPlace i) ≠ O.twistPlace i := isSplit_twistPlace O i
  -- block `0` is empty, so its label is `1`, whose idempotent does not kill `f`
  obtain ⟨t, h_lab⟩ : ∃ t : Fin 2 → ℕ,
      HasProductLabel f.val h_split T (card Empty) 1 ![1, (ϑ.tamePart (O.twistPlace i))⁻¹] t := by
    have h_idem : (1 : Representation ℂ _ _).asAlgebraHom
        (labelIdem (k := ResField (O.twistPlace i)) Empty 1) f.val ≠ 0 := by
      simp [he.1, labelIdem, IsLabel, asAlgebraHom_eq_sum, Hall.evalGL]
    have h_lab := (h_type i).hasProductLabel 1 Function.injective_id h_idem
      (by simp [h_tamePart, ϑ.tamePart_ne_one, hw]) (by simp)
    exact ⟨_, by simpa only [scaleRoots_one, map_one, Units.val_one, h_tamePart] using h_lab⟩
  obtain ⟨h_fin, -, h_labelled⟩ := hR.isLabelledAt f.prop he h_lab hA
  refine ⟨h_fin, fun s hs ↦ ?_⟩
  -- with `a` the tame exponent of `s`, the roots of the label give the eigenvalues of `s`
  obtain ⟨a, ha, -⟩ := (GaloisRep.exists_isTameExponent T hA (card Empty)).2 s hs
  refine ⟨fun _ ↦ h_fin.aeval_eq_zero_of_roots h_val hs (h_labelled ha) _ ?_, fun {L} ↦ ?_⟩
  · -- the roots of the label are `1` and the name of `(ϑ.tamePart)⁻¹`, whose images are the roots
    -- of the quadratic
    rw [invAvatar_eq_of_isTameExponent hw h_split h_val ha]
    simp +contextual [or_imp, T, K, eval_multiset_prod, sub_eq_zero]
  · -- `A` is not above `ℓ`, so no embedding in `ℚ̄_ℓ` induces it
    obtain ⟨⟨h_comap, -⟩, -⟩ := L.inducesPlace
    rw [← h_comap] at h_val
    exact absurd h_val (valuation_comap_intQpBar_lt_one L.e).ne

/-- Let `c` be a lift setting (`IsLiftSetting`) for the descent pair `O` and the twist `ϑ`: the
places `O.twistPlace i` are those of `ϑ.Q`. Let `ϑ.Q` be auxiliary for the set `badPlaces D ℓ` of
places dividing `ℓ * D.M * D.N`: its places have prime norm, and they and their conjugates are not
bad. Let `f ≠ 0` have Hecke polynomial `H w` at almost all places `w` of prime norm (`IsEigenform`),
and the parahoric type of `O` at each `O.twistPlace i`: block triangular integral matrices act
through `O.tamePart⁻¹` of the determinant of the block indexed by `r`. Let `R` be attached to `H`:
for each `η > 0` and most Frobenius elements, the coefficients of the characteristic polynomial are
within `η` of those of `ιℓ (H w)`. Let `u = normalisedRep O R` be the twist of `R` by
`normalizingAvatar O`, the avatar of a Hecke character made from the inverse of the character
`O.charW` of the hermitian space of `O`. Then `(u g - a g) (u g - 1) = 0` for `g` in inertia above
`ϑ.Q` and its conjugates, where `a = ϑ.invAvatar` is the `ℓ`-adic avatar of `ϑ⁻¹`. -/
lemma normalisedRep_quadratic_on_inertia [DecidableEq n] [Nonempty n] (hc : IsLiftSetting O c ϑ)
    (hQ : IsAuxiliary (badPlaces D ℓ) ϑ.Q) {f : (stdSpace D.E n).forms (O.columnCount, O.detExp)}
    {H : FinPlace D.E → ℂ[X]} {R : Gal(Ω/D.E) →* GL n (PadicAlgCl ℓ)} (he : IsEigenform f.val H)
    (hR : Attached H R) (h_type : ∀ i : O.TwistIndex, HasTwistParahoricType O f.val i) :
    ∀ g ∈ inertiaAbove (Set.conjClosure ϑ.Q),
      ((normalisedRep O R g).val - ϑ.invAvatar g • 1) * ((normalisedRep O R g).val - 1) = 0 := by
  -- On inertia away from `ℓ` the normalising character is trivial, so it is enough that
  -- `(X - ϑ.invAvatar s) * (X - 1)` kills `s` on `R`.
  rintro s ⟨w, hwQ, A, hA, hs⟩
  have hℓ : (ℓ : 𝓞 D.E) ∉ w.asIdeal := natCast_notMem_of_mem_conjClosure hQ hwQ
  obtain ⟨-, h_kill⟩ := isFiniteTypeAt_and_polyKillsAt_of_mem_conjClosure hc hQ he hR h_type hwQ hA
  have h_aeval : aeval (R s).val ((X - C (ϑ.invAvatar s)) * (X - 1) : (PadicAlgCl ℓ)[X]) = 0 :=
    (h_kill s hs).1 (hA.valuation_natCast_eq_one_iff.2 hℓ)
  simpa [Units.smul_def, normalizingAvatar_eq_of_isFrob_inv hA hℓ 0 (inv_mem hs), Algebra.smul_def]
    using h_aeval

end New.Selmer
