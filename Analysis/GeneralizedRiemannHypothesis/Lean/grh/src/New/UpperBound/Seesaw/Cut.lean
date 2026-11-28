import Lib.Weil.Periods.LatticeBounds
import New.UpperBound.Seesaw.IntegralAsCosetSum
import New.UpperBound.Seesaw.UnfoldingStages

/-!
# The outer variables: finitely many classes, with weights

Let `G_j = Gf D.E (D.Y j)` be the finite adelic unitary group of the hermitian space `Y_j` over the
CM field `D.E`. For each `j ≤ 2ϱ + 1` and each tame character `ϑ` we choose a finite set `Ω_j` of
classes of `G_j` modulo the level `levelY ϑ j`, with multiplicities that divide a power of
`q = ϑ.normQ`. The file defines the weighted sum of a function over `Ω_0 × ⋯ × Ω_{k-1}` and proves
that it is invariant under the levels `D.levelX j` and has coefficients integral away from `q`.

Notions from other files:
* A tame character `ϑ` is an automorphic character of `U(1)` of weight `0` with a finite set `ϑ.Q`
  of places as modulus, and `ϑ.normQ` is the product of the norms of these places.
* The chosen places are the prime divisors of `D.piM`; they lie above the primes `p₀` and `p₁` of
  the data `D`.
* `stdLevel D.E (D.Y j)` is the stabiliser in `G_j` of the standard lattice, and `levelY ϑ j` its
  subgroup of elements that reduce to `1` at the chosen places and at the places of `ϑ.Q`.
* `localLevel n S` is the group of points that are integral at every place in `S`.

## Relation to the literature

See `New.UpperBound.Seesaw.SeesawIdentity` for related work.
-/

open Function Finset MulAction
noncomputable section
namespace New.Data
open Gf Seesaw IsTopologicalGroup
variable {P : Parameters} {D : Data P} (ϑ : D.TameChar)

/-- Since the number `D.m` of lifts equals `2 ϱ + 2`, an index `j ≤ 2 ϱ + 1` satisfies `j < D.m`. -/
lemma lt_m_of_le {j : ℕ} (hj : j ≤ 2 * D.ϱ + 1) : j < D.m := by
  grind [D.m_eq_two_mul_varrho_add_two]

/-! ### The cuts -/

/-- Let `x` be a finite adelic point of the unitary group of the space `Y_j` whose component
`x.atPlace w` is in `localIntGL = GL(O_w)` at every place `w` outside `ϑ.Q` and its conjugate. Then
there is an `n` such that, for all `u` in `levelY ϑ j`, the `q ^ n`-th power of `x u x⁻¹` lies in
the stabiliser `stdLevel` of the standard lattice. -/
lemma exists_conj_pow_mem_stdLevel {j : ℕ} {x : Gf D.E (D.Y j)}
    (hx : ∀ w : FinPlace D.E, ¬(w ∈ ϑ.Q ∨ star w ∈ ϑ.Q) → x.atPlace w ∈ localIntGL (D.Y j) w) :
    ∃ n : ℕ, ∀ u ∈ levelY ϑ j, (x * u * x⁻¹) ^ ϑ.normQ ^ n ∈ stdLevel D.E (D.Y j) := by
  -- At `w ∈ ϑ.Q`, conjugation by `x` keeps elements close to `1` integral, and high powers of
  -- `u ≡ 1` are close to `1` by lifting the exponent.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ w ∈ ϑ.Q, ∀ g ∈ localCongruence (D.Y j) w n,
      x.atPlace w * g * (x.atPlace w)⁻¹ ∈ localIntGL (D.Y j) w :=
    (ϑ.Q.eventually_all.2 fun w _ ↦ eventually_localCongruence_subset
      (((isOpen_localIntGL w).preimage (continuous_conj (x.atPlace w))).mem_nhds (by simp))).exists
  refine ⟨n, fun u hu ↦ mem_stdLevel_iff.2 fun w ↦ ?_⟩
  have hu_int := mem_stdLevel_iff.1 (levelOf_le_stdLevel hu)
  have h_onQ (w : FinPlace D.E) (hw : w ∈ ϑ.Q) :
      ((x * u * x⁻¹) ^ ϑ.normQ ^ n).atPlace w ∈ localIntGL (D.Y j) w := by
    -- `u` reduces to `1` at every place of `D.levelPlaces ϑ`, and `w` is the place `.inr ⟨w, hw⟩`.
    have hu_near : u.atPlace w ∈ localCongruence (D.Y j) w 0 :=
      mem_localCongruence_zero.2 ⟨hu_int w, congrFun (mem_levelOf.1 hu).2 (.inr ⟨w, hw⟩)⟩
    have hu_pow : u.atPlace w ^ ϑ.normQ ^ n ∈ localCongruence (D.Y j) w n := by
      simpa using pow_pow_mem_localCongruence
        (D.normQ_mem_and_notMem_of_mem_Q ϑ (.inl hw)).1 hu_near n
    simpa using hn w hw _ hu_pow
  by_cases hw : w ∈ ϑ.Q ∨ star w ∈ ϑ.Q
  · exact hw.elim (h_onQ w) fun hw ↦ atPlace_star_mem_iff.1 (h_onQ (star w) hw)
  · simp [hx w hw, mul_mem, pow_mem (hu_int w)]

/-- A cut for the `j`-th outer variable: a finite set `T` of classes of `G_j = Gf D.E (D.Y j)`
modulo the level `levelY ϑ j`, used to write integrals over `R_j \ G_j` as finite sums. Here `R_j`
is the finite Bessel subgroup `(D.gradingY j hj).besselFin`. The multiplicity of a class is the
number of translates of `T` under `R_j / (R_j ∩ stdLevel)` that contain it, `stdLevel` the lattice
stabiliser. -/
structure IsStageCut (j : ℕ) (hj : j ≤ 2 * D.ϱ + 1) (T : Finset (Gf D.E (D.Y j) ⧸ levelY ϑ j)) :
    Prop where
  /-- The group `R_j ∩ stdLevel` permutes `T`. -/
  mem_iff_smul_mem : ∀ p : (D.gradingY j hj).besselFin,
    ↑p ∈ stdLevel D.E (D.Y j) → ∀ c : Gf D.E (D.Y j) ⧸ levelY ϑ j, c ∈ T ↔ p • c ∈ T
  /-- The points over `T` are integral at the places that do not divide `ϑ.normQ`. -/
  integral : ∀ x : Gf D.E (D.Y j), ↑x ∈ T →
    x ∈ localLevel (D.Y j) {w : FinPlace D.E | ↑ϑ.normQ ∉ w.asIdeal}
  /-- On `T` the multiplicity divides a power of `ϑ.normQ`. -/
  multiplicity_dvd_pow : ∀ x : Gf D.E (D.Y j), ↑x ∈ T →
    ∃ n : ℕ,
      coverMultiplicity (D.gradingY j hj).besselFin (stdLevel D.E (D.Y j)) T x ∣ ϑ.normQ ^ n
  /-- The multiplicity is nonzero at the points whose `R_j`-orbit meets the lattice bounds. -/
  ne_zero_of_hasBoundedOrbit : ∀ x : Gf D.E (D.Y j),
    (D.gradingY j hj).HasBoundedOrbit (twistIdele ϑ).val j x →
    coverMultiplicity (D.gradingY j hj).besselFin (stdLevel D.E (D.Y j)) T x ≠ 0

open scoped Pointwise in
/-- For every `j ≤ 2 D.ϱ + 1` there is a finite set `T` of classes of `Gf D.E (D.Y j)` modulo
`levelY ϑ j` with `IsStageCut ϑ j hj T`. Let `R_j` be the finite Bessel subgroup
`(D.gradingY j hj).besselFin`, and let `stdLevel` be the lattice stabiliser. The multiplicity of a
class is the number of translates of `T` under `R_j / (R_j ∩ stdLevel)` that contain it. Being a cut
means four things. First, `T` is stable under `R_j ∩ stdLevel`. Second, its points are integral at
the places prime to `q = ϑ.normQ`. Third, on `T` the multiplicity divides a power of `q`. Fourth,
the multiplicity is nonzero at each `x` such that some point of the orbit `R_j x` has a graded
lattice satisfying `HasLatticeBounds` for `twistIdele ϑ`, a generator of the ideal `ϑ.Q`
(`HasBoundedOrbit`). -/
lemma exists_isStageCut (j : ℕ) (hj : j ≤ 2 * D.ϱ + 1) :
    ∃ T : Finset (Gf D.E (D.Y j) ⧸ levelY ϑ j), IsStageCut ϑ j hj T := by
  -- Finitely many cosets `c stdLevel`, with `c` supported on `Q ∪ Q̄`, meet all orbits with the
  -- bounds.
  obtain ⟨C, hC_finite, hC_supp, hC_meets⟩ :=
    (D.gradingY j hj).exists_finite_representatives (Q := (ϑ.Q : Set (FinPlace D.E)))
      (twistIdele ϑ) j fun w hw ↦ (valued_twistIdele ϑ w).trans (ite_eq_right hw)
  have h_off : ∀ x ∈ C * (stdLevel D.E (D.Y j) : Set (Gf D.E (D.Y j))), ∀ w : FinPlace D.E,
      ¬(w ∈ ϑ.Q ∨ star w ∈ ϑ.Q) → x.atPlace w ∈ localIntGL (D.Y j) w := by
    rintro _ ⟨c, hc, z, hz, rfl⟩ w hw
    obtain ⟨hw, hw_star⟩ := not_or.1 hw
    simp [mem_supportedOn.1 (hC_supp hc) w hw hw_star, mem_stdLevel_iff.1 hz]
  have h_int : ∀ x ∈ C * (stdLevel D.E (D.Y j) : Set (Gf D.E (D.Y j))),
      x ∈ localLevel (D.Y j) {w : FinPlace D.E | ↑ϑ.normQ ∉ w.asIdeal} := fun x hx w hw ↦
    h_off x hx w fun hwQ ↦ hw (D.normQ_mem_and_notMem_of_mem_Q ϑ hwQ).1
  -- A cut on these points: its multiplicity divides a power of `q` also where the bounds are met.
  obtain ⟨T, h_stable, h_integral, h_dvd⟩ :=
    exists_finset_coverMultiplicity_dvd_pow (J := levelY ϑ j) levelOf_le_stdLevel
      (hC_finite.isCompact.mul isCompact_stdLevel) stdLevel_le_localLevel
      (fun x hx ↦ ⟨h_int x hx, exists_conj_pow_mem_stdLevel ϑ (h_off x hx)⟩) hC_meets
  refine ⟨T, h_stable, h_integral, fun x hx ↦ h_dvd x (.inl hx), fun x hx ↦ ?_⟩
  obtain ⟨n, hn⟩ := h_dvd x (.inr hx)
  exact ne_zero_of_dvd_ne_zero (pow_ne_zero n (by simp [prod_eq_zero_iff])) hn

/-- The classes `Ω_j` modulo `levelY ϑ j` over which the `j`-th outer variable is summed: the
classes of the elements of `D.chosenLevel` (integral points that reduce to `1` at the chosen places)
for `j = 0`, and a chosen cut (`IsStageCut`) for `j > 0`. -/
def cutPoints : ∀ j : ℕ, j ≤ 2 * D.ϱ + 1 → Finset (Gf D.E (D.Y j) ⧸ levelY ϑ j)
  | 0, _ => (finite_quotient_image_of_isCompact (IsLevel.isOpen (K := levelY ϑ 0))
      (IsLevel.isCompact (K := D.chosenLevel))).toFinset
  | k + 1, hk => (exists_isStageCut ϑ (k + 1) hk).choose

/-- For `k + 1 ≤ 2 ϱ + 1` the set `cutPoints ϑ (k + 1)` is a cut (`IsStageCut`). -/
lemma isStageCut_cutPoints (k : ℕ) (hk : k + 1 ≤ 2 * D.ϱ + 1) :
    IsStageCut ϑ (k + 1) hk (cutPoints ϑ (k + 1) hk) :=
  (exists_isStageCut ϑ (k + 1) hk).choose_spec

/-- The multiplicity of a class modulo `levelY ϑ j`: it is `1` for `j = 0`, and for `j > 0` the
number of translates of `cutPoints ϑ j` under `R_j / (R_j ∩ stdLevel)` that contain the class, with
`R_j` the finite Bessel subgroup and `stdLevel` the lattice stabiliser. -/
def cutMultiplicity : ∀ j : ℕ, j ≤ 2 * D.ϱ + 1 → Gf D.E (D.Y j) ⧸ levelY ϑ j → ℕ
  | 0, _ => fun _ ↦ 1
  | k + 1, hk => coverMultiplicity (D.gradingY (k + 1) hk).besselFin (stdLevel D.E (D.Y (k + 1)))
      (cutPoints ϑ (k + 1) hk)

/-- The set `cutPoints ϑ 0` consists of the classes modulo `levelY ϑ 0` of the elements of
`D.chosenLevel`, the integral points that reduce to `1` at every prime divisor of `D.piM`: the class
of a finite adelic point `x` of the unitary group of `Y_0` lies in it if and only if
`x ∈ D.chosenLevel`. -/
lemma mk_mem_cutPoints_zero {hj : 0 ≤ 2 * D.ϱ + 1} {x : Gf D.E (D.Y 0)} :
    ↑x ∈ cutPoints ϑ 0 hj ↔ x ∈ D.chosenLevel := by
  rw [cutPoints, Set.Finite.mem_toFinset]
  exact ⟨fun ⟨x', hx', h_eq⟩ ↦ (mul_mem_cancel_left (inv_mem hx')).1
    (levelY_le_chosenLevel ϑ 0 (QuotientGroup.eq.1 h_eq)), fun hx ↦ ⟨x, hx, rfl⟩⟩

/-- A point whose class lies in `cutPoints ϑ j` is integral at every place that does not divide
`ϑ.normQ`. -/
lemma mem_localLevel_of_mem_cutPoints {j : ℕ} {hj : j ≤ 2 * D.ϱ + 1} {x : Gf D.E (D.Y j)}
    (hx : ↑x ∈ cutPoints ϑ j hj) :
    x ∈ localLevel (D.Y j) {w : FinPlace D.E | ↑ϑ.normQ ∉ w.asIdeal} := by
  cases j with
  | zero => exact stdLevel_le_localLevel (levelOf_le_stdLevel ((mk_mem_cutPoints_zero ϑ).1 hx))
  | succ k => exact (isStageCut_cutPoints ϑ k hj).integral x hx

/-- If the class of a point `x` lies in `cutPoints ϑ j`, then its multiplicity
`cutMultiplicity ϑ j hj x` divides some power `ϑ.normQ ^ n` of `ϑ.normQ`. -/
lemma exists_cutMultiplicity_dvd {j : ℕ} {hj : j ≤ 2 * D.ϱ + 1} {x : Gf D.E (D.Y j)}
    (hx : ↑x ∈ cutPoints ϑ j hj) : ∃ n : ℕ, cutMultiplicity ϑ j hj x ∣ ϑ.normQ ^ n := by
  cases j with
  | zero => exact ⟨0, one_dvd _⟩
  | succ k => exact (isStageCut_cutPoints ϑ k hj).multiplicity_dvd_pow x hx

/-- The image in `U(Y_j)` of a finite point of `U(X_j)` lies in the finite Bessel subgroup. -/
lemma inclXFin_gradingY_mem_besselFin {j : ℕ} (hj : j ≤ 2 * D.ϱ + 1) (b : Gf D.E (D.X j)) :
    (D.gradingY j hj).inclXFin b ∈ (D.gradingY j hj).besselFin :=
  (D.gradingY j hj).snd_mem_besselFin ((D.gradingY j hj).inclX_mem_besselGroup (1, b))

/-- Let `X_j` be the space that `D.gradingY j` embeds in the hermitian space `Y_j`, and let
`cutPoints ϑ j` be the finite set of classes of the finite adelic unitary group of `Y_j` modulo
`levelY ϑ j` over which the `j`-th variable is summed. If `b` lies in the level `D.levelX j` of
`U(X_j)`, then a class `c` lies in `cutPoints ϑ j` if and only if its translate by the image of `b`
in `U(Y_j)` does. -/
lemma smul_mem_cutPoints_iff {j : ℕ} {hj : j ≤ 2 * D.ϱ + 1} {b : Gf D.E (D.X j)}
    (hb : b ∈ D.levelX j) (c : Gf D.E (D.Y j) ⧸ levelY ϑ j) :
    c ∈ cutPoints ϑ j hj ↔ (D.gradingY j hj).inclXFin b • c ∈ cutPoints ϑ j hj := by
  cases j with
  | zero =>
    induction c using QuotientGroup.induction_on with | H x =>
    rw [Quotient.smul_mk, mk_mem_cutPoints_zero, mk_mem_cutPoints_zero]
    exact (mul_mem_cancel_left (inclXFin_mem_chosenLevel hb)).symm
  | succ k =>
    have hb_stdLevel : (D.gradingY (k + 1) hj).inclXFin b ∈ stdLevel D.E (D.Y (k + 1)) :=
      (D.gradingY (k + 1) hj).inclXFin_mem_stdLevel (D.spansLattice_gradingY (k + 1) hj)
        D.isSplitSquarefree_piNIdele (Subgroup.mem_inf.1 hb).2
    exact (isStageCut_cutPoints ϑ k hj).mem_iff_smul_mem ⟨_, inclXFin_gradingY_mem_besselFin hj b⟩
      hb_stdLevel c

/-- For a finite point `b` of `U(X_j)` and a class `c` modulo `levelY ϑ j`, moving `c` by the image
`(D.gradingY j hj).inclXFin b` of `b` in `U(Y_j)` does not change `cutMultiplicity ϑ j hj c`. -/
lemma cutMultiplicity_smul {j : ℕ} {hj : j ≤ 2 * D.ϱ + 1} (b : Gf D.E (D.X j))
    (c : Gf D.E (D.Y j) ⧸ levelY ϑ j) :
    cutMultiplicity ϑ j hj ((D.gradingY j hj).inclXFin b • c) = cutMultiplicity ϑ j hj c := by
  cases j with
  | zero => rfl
  | succ k => exact coverMultiplicity_smul _ ⟨_, inclXFin_gradingY_mem_besselFin hj b⟩ c

variable {ϑ} in
/-- Suppose that the modulus `ϑ.Q` of `ϑ` is empty (`hQ`) and that `k < D.m`. Let `T` be a finite
set of classes of `Gf D.E (D.Y k)` modulo `levelY ϑ k`, and suppose (`hT`) that every point over `T`
lies in `localLevel` at the places not dividing `ϑ.normQ = 1`. Then `T` has at most
`D.residueMatrixCount = M ^ (f n²)` elements, where `M = D.M = p₀ p₁` (the primes of `D`), `f = D.f`
is the number of infinite places of `E`, and `n = D.n D.m`. -/
lemma card_le_residueMatrixCount (hQ : ϑ.Q = ∅) {k : ℕ} (hk : k < D.m)
    {T : Finset (Gf D.E (D.Y k) ⧸ levelY ϑ k)}
    (hT : ∀ x : Gf D.E (D.Y k),
      ↑x ∈ T → x ∈ localLevel (D.Y k) {w : FinPlace D.E | ↑ϑ.normQ ∉ w.asIdeal}) :
    T.card ≤ D.residueMatrixCount := by
  -- As `Q = ∅`, the points over `T` lie in `stdLevel` and the principal level of `D.piM` lies in
  -- `levelY ϑ k`. So `T` injects into `stdLevel` modulo that principal level.
  have h_out (t : T) : t.val.out ∈ stdLevel D.E (D.Y k) := by
    simpa [hQ, mem_stdLevel_iff, localLevel, Ideal.one_notMem] using hT t.val.out (by simp)
  have h_level : principalLevel (D.Y k) D.piM ≤ levelY ϑ k := fun g hg ↦
    D.chosenLevel_inf_trivialOn_le ϑ ⟨D.principalLevel_le_chosenLevel dvd_rfl hg, by simp [hQ]⟩
  have h_inj (t t' : T) (h_quot : t.val.out⁻¹ * t'.val.out ∈ principalLevel (D.Y k) D.piM) :
      t = t' := by
    simpa using QuotientGroup.eq.2 (h_level h_quot)
  have : Fact (D.piM ≠ 0) := ⟨D.piM_ne_zero⟩
  calc T.card = Nat.card T := by simp
    _ ≤ (principalLevel (D.Y k) D.piM).relIndex (stdLevel D.E (D.Y k)) :=
      Finite.card_le_of_injective' (f := fun t : T ↦ QuotientGroup.mk ⟨t.val.out, h_out t⟩)
        (fun t t' h_eq ↦ h_inj t t' (Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h_eq)))
        fun h_zero ↦ absurd h_zero (relIndex_ne_zero_of_isLevel _)
    _ ≤ Ideal.absNorm (Ideal.span {D.piM}) ^ Fintype.card (D.Y k) ^ 2 :=
      relIndex_principalLevel_le D.piM_ne_zero
    _ = D.M ^ (D.f * Fintype.card (D.Y k) ^ 2) := by rw [absNorm_piM, ← pow_mul]
    _ ≤ D.M ^ (D.f * D.n D.m ^ 2) :=
      Nat.pow_le_pow_right NeZero.one_le (by grw [D.card_Y_le hk.le])
    _ = D.residueMatrixCount := rfl

/-! ### Sums over the cuts -/

section CutSum
variable {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']

/-- The sum of `S` over the tuples obtained from `c` by letting the `j`-th coordinate run over
`cutPoints ϑ j`, each term divided by the multiplicity of that coordinate. -/
def cutSumAt (j : ℕ) (hj : j ≤ 2 * D.ϱ + 1) (S : (∀ i : ℕ, Gf D.E (D.Y i) ⧸ levelY ϑ i) → M)
    (c : ∀ i : ℕ, Gf D.E (D.Y i) ⧸ levelY ϑ i) : M :=
  ∑ x ∈ cutPoints ϑ j hj, (cutMultiplicity ϑ j hj x : ℂ)⁻¹ • S (update c j x)

/-- The sum of `S` over `Ω_0 × ⋯ × Ω_{k-1}`, `Ω_j = cutPoints ϑ j`, each term divided by the
multiplicities of its coordinates; the coordinates from `k` on are the class of `1`. -/
def cutSum : ∀ k : ℕ, k ≤ 2 * D.ϱ + 2 → ((∀ i : ℕ, Gf D.E (D.Y i) ⧸ levelY ϑ i) → M) → M
  | 0, _, S => S fun i ↦ (1 : Gf D.E (D.Y i))
  | k + 1, hk, S => cutSum k (by omega) (cutSumAt ϑ k (by omega) S)

/-- A ℂ-linear map `L : M → M'` commutes with `cutSum ϑ k`: the sum of `S` over `Ω_0 × ⋯ × Ω_{k-1}`,
`Ω_i = cutPoints ϑ i`, with each term divided by the multiplicities of its coordinates. -/
lemma map_cutSum (L : M →ₗ[ℂ] M') (k : ℕ) (hk : k ≤ 2 * D.ϱ + 2)
    (S : (∀ i : ℕ, Gf D.E (D.Y i) ⧸ levelY ϑ i) → M) :
    L (cutSum ϑ k hk S) =
      cutSum ϑ k hk fun c : ∀ i : ℕ, Gf D.E (D.Y i) ⧸ levelY ϑ i ↦ L (S c) := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    simp only [cutSum, ih, cutSumAt, map_sum, _root_.map_smul]
    rfl

/-- Let `S` be a function on tuples of classes modulo the levels `levelY ϑ i` with values in a
complex vector space `M`, and `h` a tuple of group elements whose `k`-th entry is the image of an
element `b` of the level `D.levelX k` of `U(X_k)`. Then `h k` drops out of `cutSumAt ϑ k`, the sum
over the `k`-th coordinate in `cutPoints ϑ k` weighted by the inverses of the multiplicities: this
sum of `S` translated by `h` at `c` is the same sum of `S` at the translate of `c` by `h` with
`k`-th entry replaced by `1`. -/
lemma cutSumAt_smul {k : ℕ} (hk : k ≤ 2 * D.ϱ + 1)
    (S : (∀ i : ℕ, Gf D.E (D.Y i) ⧸ levelY ϑ i) → M) {h : ∀ i : ℕ, Gf D.E (D.Y i)}
    {b : Gf D.E (D.X k)} (hb : b ∈ D.levelX k) (h_eq : h k = (D.gradingY k hk).inclXFin b)
    (c : ∀ i : ℕ, Gf D.E (D.Y i) ⧸ levelY ϑ i) :
    cutSumAt ϑ k hk (fun c' : ∀ i : ℕ, Gf D.E (D.Y i) ⧸ levelY ϑ i ↦ S fun i : ℕ ↦ h i • c' i) c =
      cutSumAt ϑ k hk S fun i : ℕ ↦ update h k 1 i • c i := by
  -- `h k` permutes `cutPoints ϑ k` and keeps the multiplicities.
  refine sum_equiv (toPerm (h k)) (fun x ↦ ?_) fun x _ ↦ ?_
  · simpa [h_eq] using smul_mem_cutPoints_iff ϑ hb x
  · have h_update : (fun i : ℕ ↦ h i • update c k x i) =
        update (fun i : ℕ ↦ update h k 1 i • c i) k (h k • x) := by
      ext i
      obtain rfl | hi := eq_or_ne i k <;> simp [*]
    simp only [toPerm_apply, h_update, h_eq, cutMultiplicity_smul]

/-- Let `S` be a function on tuples of classes modulo the levels `levelY ϑ i` with values in a
complex vector space `M`. The sum `cutSum` of `S` over `Ω_0 × ⋯ × Ω_{k-1}`, `Ω_i = cutPoints ϑ i`,
weighted by the inverses of the multiplicities of the coordinates, is invariant under translation
of `S` by a tuple `h` of group elements such that `h i` is the image of an element of the level
`D.levelX i` of `U(X_i)` for `i < k` and `h i = 1` for `i ≥ k`. -/
lemma cutSum_comp_smul (k : ℕ) (hk : k ≤ 2 * D.ϱ + 2)
    (S : (∀ i : ℕ, Gf D.E (D.Y i) ⧸ levelY ϑ i) → M) {h : ∀ i : ℕ, Gf D.E (D.Y i)}
    (h_low : ∀ (i : ℕ) (hi : i < k),
      ∃ b ∈ D.levelX i, h i = (D.gradingY i (by omega)).inclXFin b)
    (h_high : ∀ i : ℕ, k ≤ i → h i = 1) :
    (cutSum ϑ k hk fun c : ∀ i : ℕ, Gf D.E (D.Y i) ⧸ levelY ϑ i ↦ S fun i : ℕ ↦ h i • c i) =
      cutSum ϑ k hk S := by
  induction k generalizing S h with
  | zero => simp [h_high]
  | succ k ih =>
    obtain ⟨b, hb, h_eq⟩ := h_low k k.lt_succ_self
    -- `h k` drops out of the last sum; the induction hypothesis applies to `update h k 1`.
    rw [cutSum, cutSum, funext (cutSumAt_smul ϑ (by omega) S hb h_eq)]
    have h_high' (i : ℕ) (hi : k ≤ i) : update h k 1 i = 1 := by
      obtain rfl | hi' := hi.eq_or_lt
      · simp
      · simpa [hi'.ne'] using h_high i hi'
    exact ih _ _ (fun i hi ↦ by simpa [hi.ne] using h_low i (by omega)) h_high'

/-- Let `k ≤ 2 ϱ + 1`, let `S` be a function from tuples of classes modulo the levels `levelY ϑ i`
to a complex vector space `M`, and let `y` be a tuple of points integral at the places that do not
divide `q = ϑ.normQ`. Let `cutSumAt` be the sum of `S` over the tuples got from `y` by letting the
`k`-th coordinate run over the finite set `cutPoints ϑ k`, each term divided by the multiplicity of
that coordinate. It is an admissible combination of the values of `S` at all such tuples `y'`: a
finite linear combination with coefficients integral away from `q` (denominator `1`) that, if the
modulus `ϑ.Q` is empty, have absolute sum at most `D.residueMatrixCount` under every automorphism of
`ℂ`. -/
lemma isAdmissibleCombination_cutSumAt {k : ℕ} (hk : k ≤ 2 * D.ϱ + 1)
    (S : (∀ i : ℕ, Gf D.E (D.Y i) ⧸ levelY ϑ i) → M)
    (y : ∀ i : ℕ, localLevel (D.Y i) {w : FinPlace D.E | ↑ϑ.normQ ∉ w.asIdeal}) :
    IsAdmissibleCombination
      (fun y' : ∀ i : ℕ, localLevel (D.Y i) {w : FinPlace D.E | ↑ϑ.normQ ∉ w.asIdeal} ↦
        S fun i : ℕ ↦ ⟦(y' i).val⟧)
      Set.univ ϑ.normQ 1 (ϑ.Q = ∅) D.residueMatrixCount
      (cutSumAt ϑ k hk S fun i : ℕ ↦ ⟦(y i).val⟧) := by
  have h_integral : ∀ c ∈ cutPoints ϑ k hk,
      ((1 : ℕ) : ℂ) * (cutMultiplicity ϑ k hk c : ℂ)⁻¹ ∈ integralAway ϑ.normQ := by
    intro c hc
    induction c using QuotientGroup.induction_on with | H x =>
    obtain ⟨n, hn⟩ : ∃ n : ℕ, cutMultiplicity ϑ k hk x ∣ ϑ.normQ ^ n :=
      exists_cutMultiplicity_dvd ϑ hc
    simpa [div_eq_mul_inv] using div_mem_integralAway (hn.mul_left 1)
  have h_size (hQ : ϑ.Q = ∅) (σ : ℂ ≃+* ℂ) :
      ∑ c ∈ cutPoints ϑ k hk, ‖σ (cutMultiplicity ϑ k hk c : ℂ)⁻¹‖ ≤ D.residueMatrixCount := by
    have h_card : (cutPoints ϑ k hk).card ≤ D.residueMatrixCount :=
      card_le_residueMatrixCount hQ (lt_m_of_le hk) fun x ↦ mem_localLevel_of_mem_cutPoints ϑ
    grw [sum_le_card_nsmul _ _ (1 : ℝ) (by simp [Nat.cast_inv_le_one]), nsmul_one, h_card]
  refine .of_eq_isOfFinOrder_smul (.of_sum h_integral h_size) fun c hc ↦ ?_
  -- Each term is `1` times the value of `S` at `y` updated by a point `x` integral away from `q`.
  induction c using QuotientGroup.induction_on with | H x =>
  refine ⟨1, .one, update y k ⟨x, mem_localLevel_of_mem_cutPoints ϑ hc⟩, Set.mem_univ _, ?_⟩
  rw [one_smul]
  congr! with i
  obtain rfl | hi := eq_or_ne i k <;> simp [*, QuotientGroup.mk]

/-- Let `k ≤ 2 ϱ + 2` and let `S` be a function from tuples of classes modulo the levels
`levelY ϑ i` to a complex vector space `M`. Let `cutSum` be the sum of `S` over `Ω_0 × ⋯ × Ω_{k-1}`,
`Ω_i = cutPoints ϑ i`, each term divided by the multiplicities of its coordinates, the other
coordinates being the class of `1`. It is an admissible combination of the values of `S` at all
tuples of points integral at the places that do not divide `q = ϑ.normQ`: a finite linear
combination with coefficients integral away from `q` (denominator `1`) that, if the modulus `ϑ.Q` is
empty, have absolute sum at most `D.residueMatrixCount ^ k` under every automorphism of `ℂ`. -/
lemma isAdmissibleCombination_cutSum (k : ℕ) (hk : k ≤ 2 * D.ϱ + 2)
    (S : (∀ i : ℕ, Gf D.E (D.Y i) ⧸ levelY ϑ i) → M) :
    IsAdmissibleCombination
      (fun y : ∀ i : ℕ, localLevel (D.Y i) {w : FinPlace D.E | ↑ϑ.normQ ∉ w.asIdeal} ↦
        S fun i : ℕ ↦ ⟦(y i).val⟧)
      Set.univ ϑ.normQ 1 (ϑ.Q = ∅) (D.residueMatrixCount ^ k) (cutSum ϑ k hk S) := by
  induction k generalizing S with
  | zero => simpa only [pow_zero, cutSum] using .single 1 (Set.mem_univ 1)
  | succ k ih =>
    exact (ih (by omega) (cutSumAt ϑ k (by omega) S)).bind 1 D.residueMatrixCount
      (fun y _ ↦ isAdmissibleCombination_cutSumAt ϑ (by omega) S y) (one_mul 1).dvd
      fun _ ↦ by rw [Nat.abs_cast, pow_succ]

end CutSum

end New.Data

end
