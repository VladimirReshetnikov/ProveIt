import Lib.PadicHodge.Kisin.Charts

/-!
# The ring S_B of a chart and extension of S-linear maps of A_inf to B^+

This file works in B^+ = `BPlus` = A_max[1/p], where A_max = `Amax` has image `amaxImage` in B^+.
It defines the ring S_B of a chart, the elements of B^+ whose multiplication commutes with all
`S`-linear maps of B^+ that keep `amaxImage`. It shows that S_B is the closure of `S[E/p]` with `p`
inverted, and that every `S`-linear map of A_inf extends to an S_B-linear map of B^+ that keeps
`amaxImage`. Most identities for the extensions are checked on A_inf by a density principle: an
additive map of B^+ that keeps `amaxImage` and kills A_inf is zero
(`New.Lift.Chart.eq_zero_of_map_ainfToBPlus_eq_zero`). The file ends with results on divisibility
by `z` in B^+.

## Main definitions and results

* `New.Lift.Chart.bicommutant`: the ring S_B of the elements of B^+ whose multiplication commutes
  with all S-linear maps B^+ → B^+ that keep the image of A_max.
* `New.Lift.Chart.extendToBPlus`: an S-linear map of A_inf extends to an S_B-linear map of B^+
  keeping the image of A_max.

Notions from other files:
* `New.Period.Amax`: Colmez's period ring A_max, the p-adic completion of A_inf[X]/(pX − ξ).
* `New.Period.FrobGal`: The monoid ℕ × G_p; the pair (n, g) acts on A_inf as φ^n g.
* `New.Lift.Chart.S`: the ring `S`, the image in A_inf of the chart's map Λ[[X]] → A_inf.
* `New.Lift.Chart.E`: the image `E` in `S` of the series X^e A + p; it equals ξ times a unit.
* `New.Lift.Chart.adicBasis`: a chosen (p, z)-adic topological basis of A_inf over `S`, whose
  coordinate at `New.Lift.Chart.oneIndex` is the identity on `S`.

## Relation to the literature

Known; see `Lib.PadicHodge.Kisin.PeriodMatrixFrame` for sources.
-/

noncomputable section

namespace New.Lift

section ChartScalars

open Period BPlus Amax Ideal IsScalarTower Algebra Witt Variety Filter NeZero

variable {p : ℕ} [ThePrime p] (c : Chart)

/-! ### Preliminaries on B^+ -/

/-- An element `y` of B^+ that is `p ^ n` times an element of `amaxImage` (the image of A_max)
for every `n` is zero. -/
lemma eq_zero_of_p_pow_amaxImage {y : BPlus} (h : ∀ n : ℕ, ∃ w ∈ amaxImage, y = p ^ n * w) :
    y = 0 := by
  -- By the case `n = 0`, `y` comes from some `b` in `Amax`, which is `p`-adically separated.
  obtain ⟨_, ⟨b, rfl⟩, hy⟩ := h 0
  rw [pow_zero, one_mul] at hy
  have h_dvd (n : ℕ) : (p : Amax) ^ n ∣ b - 0 := by
    obtain ⟨_, ⟨b', rfl⟩, hy'⟩ := h n
    have h_eq : b = (p : Amax) ^ n * b' := injective_Amax_BPlus (by simpa [hy] using hy')
    simp [h_eq]
  rw [hy, eq_of_forall_pow_dvd_sub (p : Amax) h_dvd, map_zero]

/-- An additive map `G` of B^+ commutes with multiplication by `p ^ n`. -/
lemma map_p_pow_mul {F : Type*} [FunLike F BPlus BPlus] [AddMonoidHomClass F BPlus BPlus] (G : F)
    (n : ℕ) (y : BPlus) :
    G (p ^ n * y) = p ^ n * G y := by
  simpa [nsmul_eq_mul] using map_nsmul G (p ^ n) y

/-- Each `m` in `FrobGal` (acting as `φ ^ n g`) keeps `amaxImage`, the image of A_max. -/
lemma smul_mem_amaxImage {m : FrobGal} : ∀ y ∈ amaxImage, m • y ∈ amaxImage := by
  rintro _ ⟨b, rfl⟩
  exact ⟨m • b, (smul_algebraMap_eq_algebraMap_smul m b).symm⟩

namespace Chart

/-- The structure ring homomorphism from A_inf to B^+. -/
abbrev ainfToBPlus : Ainf →+* BPlus := algebraMap Ainf BPlus

/-- θ(z) divides p in O_C. -/
lemma theta_z_dvd_p : theta c.z ∣ p := by
  -- `z` divides `E - p`, and `θ E = 0`.
  grw [c.dvd_iff_coe_dvd.mp c.z_dvd_E_sub_p]
  simp [theta_E]

/-- θ(z) is not zero, as it divides `p`. -/
lemma theta_z_ne_zero : theta c.z ≠ 0 :=
  ne_zero_of_dvd_ne_zero (out : (p : OC) ≠ 0) c.theta_z_dvd_p

/-- The ring S_B of the chart: the elements of `BPlus` whose multiplication commutes with every
`c.S`-linear map of `BPlus` that keeps `amaxImage`, the image of A_max. By
`adjoinEDivPClosure_eq_bicommutant` this is the closure of `S[E/p]` in `BPlus` with `p` inverted. -/
def bicommutant : Subalgebra c.S BPlus :=
  Subalgebra.comap (lmul c.S BPlus)
    (Subalgebra.centralizer c.S {G : Module.End c.S BPlus | ∀ y ∈ amaxImage, G y ∈ amaxImage})

/-- An element `y` of B^+ lies in S_B = `c.bicommutant` if and only if multiplication by `y`
commutes with every `c.S`-linear map `G` of B^+ that keeps `amaxImage`. -/
lemma mem_bicommutant_iff {y : BPlus} :
    y ∈ c.bicommutant ↔ ∀ G : BPlus →ₗ[c.S] BPlus, (∀ w ∈ amaxImage, G w ∈ amaxImage) →
      ∀ x : BPlus, G (y * x) = y * G x :=
  forall₂_congr fun _ _ ↦ LinearMap.ext_iff

@[simp]
lemma ainfToBPlus_mem_bicommutant {c : Chart} (s : c.S) : ainfToBPlus s ∈ c.bicommutant :=
  c.bicommutant.algebraMap_mem' s

/-- Every `c.S`-linear map `f` from A_inf to itself extends along `ainfToBPlus` to a `c.S`-linear
map from B^+ to itself that keeps `amaxImage`, the image of A_max in B^+. Here `c.S` is the subring
of A_inf that is the image of the chart's map Λ⟦X⟧ → A_inf, and `BPlus` is B^+ = A_max[1/p], with
A_max the period ring `Amax`. -/
lemma exists_extendToBPlus (f : Ainf →ₗ[c.S] Ainf) :
    ∃ G : BPlus →ₗ[c.S] BPlus,
      (∀ a : Ainf, G (ainfToBPlus a) = ainfToBPlus (f a)) ∧ ∀ y ∈ amaxImage, G y ∈ amaxImage := by
  -- Extend `f` first to the `x` in `Amax` with `p ^ d * x` in `Ainf`, then to `Amax` by
  -- `p`-adic continuity, then to `BPlus` by inverting `p`.
  let i : Ainf →ₗ[c.S] Amax := (toAlgHom c.S Ainf Amax).toLinearMap
  -- `f` keeps `(p, E) ^ n = (p, ξ) ^ n`, hence divisibility by `p ^ n` in `Amax`.
  have h_dvd_f_of_dvd {n : ℕ} {a : Ainf} (ha : (p : Amax) ^ n ∣ algebraMap Ainf Amax a) :
      (p : Amax) ^ n ∣ algebraMap Ainf Amax (f a) := by
    have h_mem_pow : a ∈ span {↑p, xi} ^ n → f a ∈ span {↑p, xi} ^ n := by
      simpa [span_singleton_eq_span_singleton.mpr c.associated_E_xi, span_insert, Ideal.map_pow,
        Ideal.map_sup, map_span] using (span {↑p, c.E} ^ n).smul_top_le_comap_smul_top f (x := a)
    exact p_pow_dvd_of_mem_pow (h_mem_pow (mem_span_pow_of_p_pow_dvd ha))
  -- The pairs `(x, z)` with `p ^ d * (x, z) = (a, f a)`: the `x` fill `Amax` modulo `p`, and
  -- `x ↦ z` is `p`-adically continuous.
  have h_dense (y : Amax) : ∃ x : Amax,
      (∃ (z : Amax) (d : ℕ) (a : Ainf), algebraMap Ainf Amax a = p ^ d * x ∧
        algebraMap Ainf Amax (f a) = p ^ d * z) ∧ (p : Amax) ∣ x - y := by
    obtain ⟨d, a, w, hw⟩ : ∃ (d : ℕ) (a : Ainf) (w : Amax),
        algebraMap Ainf Amax a = p ^ d * (y - p ^ 1 * w) :=
      y.exists_algebraMap_eq_p_pow_mul_sub 1
    obtain ⟨z, hz⟩ : (p : Amax) ^ d ∣ algebraMap Ainf Amax (f a) :=
      h_dvd_f_of_dvd ⟨y - p ^ 1 * w, hw⟩
    exact ⟨y - p ^ 1 * w, ⟨z, d, a, hw, hz⟩, ⟨-w, by ring⟩⟩
  have h_cont (n : ℕ) (x z : Amax) (d : ℕ) (a : Ainf) (hx : algebraMap Ainf Amax a = p ^ d * x)
      (hz : algebraMap Ainf Amax (f a) = p ^ d * z) :
      (p : Amax) ^ (n + n) ∣ x → (p : Amax) ^ n ∣ z := by
    -- Already `p ^ n ∣ x` is enough: then `p ^ (d + n)` divides `a`, hence also `f a = p ^ d * z`,
    -- so `p ^ n` divides `z`.
    intro h_dvd_x
    have h_dvd_a : (p : Amax) ^ (d + n) ∣ algebraMap Ainf Amax a := by
      rw [hx, pow_add]
      exact mul_dvd_mul_left _ ((pow_dvd_pow _ (Nat.le_add_right n n)).trans h_dvd_x)
    have h_dvd_fa : (p : Amax) ^ d * p ^ n ∣ p ^ d * z := by
      rw [← pow_add, ← hz]
      exact h_dvd_f_of_dvd h_dvd_a
    exact (mul_dvd_mul_iff_left (pow_ne_zero d (NeZero.ne (p : Amax)))).mp h_dvd_fa
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : Amax →ₗ[c.S] Amax, ∀ (x z : Amax) (d : ℕ) (a : Ainf),
      algebraMap Ainf Amax a = p ^ d * x → algebraMap Ainf Amax (f a) = p ^ d * z → G₀ x = z := by
    -- These pairs form the `p`-saturation of the graph of `f`. By `exists_adic_extension` the
    -- second projection factors through the first, by `h_dense` and `h_cont`.
    let saturation : Submodule c.S (Amax × Amax) :=
      (primaryComponent _ (span {↑p})).comap (i.prod (i ∘ₗ f)).range.mkQ
    have h_mem (x z : Amax) : (x, z) ∈ saturation ↔ ∃ (d : ℕ) (a : Ainf),
        algebraMap Ainf Amax a = p ^ d * x ∧ algebraMap Ainf Amax (f a) = p ^ d * z := by
      simp [saturation, i, primaryComponent_mem, ← Submodule.Quotient.mk_smul,
        smul_def (A := Amax), span_singleton_pow]
    have h_smul_top (n : ℕ) (y : Amax) :
        y ∈ (span {(p : c.S)} ^ n • ⊤ : Submodule c.S Amax) ↔ (p : Amax) ^ n ∣ y := by
      simp [span_singleton_pow, map_span, mem_span_singleton]
    obtain ⟨G₀, hG₀⟩ : ∃ G₀ : Amax →ₗ[c.S] Amax, ∀ q : saturation, G₀ q.val.1 = q.val.2 := by
      refine exists_adic_extension (span {↑p}) (LinearMap.fst c.S Amax Amax ∘ₗ saturation.subtype)
        (LinearMap.snd c.S Amax Amax ∘ₗ saturation.subtype) ?_ fun n q hq ↦ ?_
      · rintro ⟨y⟩
        obtain ⟨x, ⟨z, d, a, ha, hz⟩, hxy⟩ := h_dense y
        refine ⟨⟨(x, z), (h_mem x z).mpr ⟨d, a, ha, hz⟩⟩, (Submodule.Quotient.eq _).mpr ?_⟩
        simpa using (h_smul_top 1 (x - y)).mpr (by simpa using hxy)
      · obtain ⟨d, a, ha, hz⟩ := (h_mem q.val.1 q.val.2).mp q.prop
        exact (h_smul_top n _).mpr (h_cont n _ _ d a ha hz ((h_smul_top (n + n) _).mp hq))
    exact ⟨G₀, fun x z d a ha hz ↦ hG₀ ⟨(x, z), (h_mem x z).mpr ⟨d, a, ha, hz⟩⟩⟩
  let j : Amax →ₗ[c.S] BPlus := (toAlgHom c.S Amax BPlus).toLinearMap
  have h_away : IsLocalization.Away (algebraMap c.S Amax p) BPlus := by
    simpa using (inferInstance : IsLocalization.Away (p : Amax) BPlus)
  -- `hG x`: the extension sends `j x` to `j (G₀ x)`.
  have hG := IsLocalizedModule.map_apply (.powers ↑p) j j G₀
  have hG₀_ainf (a : Ainf) : G₀ (algebraMap Ainf Amax a) = algebraMap Ainf Amax (f a) :=
    hG₀ _ _ 0 a (by simp) (by simp)
  refine ⟨IsLocalizedModule.map (.powers ↑p) j j G₀, fun a ↦ ?_, ?_⟩
  · -- On `Ainf` the extension is `G₀`, which is `f` there.
    exact (hG _).trans (congrArg j (hG₀_ainf a))
  · -- It sends the image of `x` in `Amax` to the image of `G₀ x` (`hG x`), so it keeps
    -- `amaxImage`.
    rintro _ ⟨x, rfl⟩
    exact ⟨G₀ x, (hG x).symm⟩

/-- For a `c.S`-linear map `f` of A_inf, a chosen `c.S`-linear extension of `f` to B^+ that
keeps `amaxImage`; it is even linear over S_B = `c.bicommutant`
(`New.Lift.Chart.extendToBPlus_mul`). -/
def extendToBPlus (f : Ainf →ₗ[c.S] Ainf) : BPlus →ₗ[c.S] BPlus := (c.exists_extendToBPlus f).choose

/-- On the image of A_inf the extension of `f` is `f`. -/
lemma extendToBPlus_ainfToBPlus (f : Ainf →ₗ[c.S] Ainf) (a : Ainf) :
    c.extendToBPlus f (ainfToBPlus a) = ainfToBPlus (f a) :=
  (c.exists_extendToBPlus f).choose_spec.left a

lemma extendToBPlus_mem_amaxImage (f : Ainf →ₗ[c.S] Ainf) :
    ∀ y ∈ amaxImage, c.extendToBPlus f y ∈ amaxImage :=
  (c.exists_extendToBPlus f).choose_spec.right

/-- Let `f` be a `c.S`-linear endomorphism of A_inf, and let `c.extendToBPlus f` be its chosen
`c.S`-linear extension to B^+ = A_max[1/p] that preserves the image of A_max. This extension is
linear over S_B = `c.bicommutant` (the elements of B^+ whose multiplication commutes with all such
maps): it commutes with multiplication by every `y` in S_B. -/
lemma extendToBPlus_mul {y : BPlus} (f : Ainf →ₗ[c.S] Ainf) (hy : y ∈ c.bicommutant) (x : BPlus) :
    c.extendToBPlus f (y * x) = y * c.extendToBPlus f x :=
  -- Multiplication by `y` commutes with every map that keeps `amaxImage`, such as the extension.
  c.mem_bicommutant_iff.mp hy (c.extendToBPlus f) (c.extendToBPlus_mem_amaxImage f) x

/-- For a chart and an index `i`, the extension to B^+ of the coordinate
`c.adicBasis.coord i : Ainf → c.S` followed by the inclusion into A_inf, as a `c.S`-linear map
B^+ → B^+. -/
abbrev extendedCoord (i : c.adicBasis.Index) : BPlus →ₗ[c.S] BPlus :=
  c.extendToBPlus (Algebra.linearMap c.S Ainf ∘ₗ c.adicBasis.coord i)

/-! ### The density principle and membership in S_B -/

/-- Density: an additive map `G` from B^+ to itself that keeps `amaxImage` (the image of A_max)
and vanishes on the image of A_inf is zero at every `y`. -/
lemma eq_zero_of_map_ainfToBPlus_eq_zero {y : BPlus} (G : BPlus →+ BPlus)
    (hG_amax : ∀ y ∈ amaxImage, G y ∈ amaxImage) (hG_ainf : ∀ a : Ainf, G (ainfToBPlus a) = 0) :
    G y = 0 := by
  -- From `p ^ m * y = ainfToBPlus a + p ^ (m + n) * w` we get `G y = p ^ n * G w` for every `n`.
  refine eq_zero_of_p_pow_amaxImage fun n ↦ ?_
  obtain ⟨m, a, w, hw, hy⟩ : ∃ (m : ℕ) (a : Ainf), ∃ w ∈ amaxImage,
      (p : BPlus) ^ m * y = ainfToBPlus a + (p : BPlus) ^ (m + n) * ainfToBPlus mu ^ 0 * w :=
    y.exists_Ainf_approx n 0
  refine ⟨G w, hG_amax w hw, ?_⟩
  -- Apply `G` to `hy`: it kills `a` and commutes with powers of `p`; then cancel `p ^ m`.
  have hG_eq : p ^ m * G y = p ^ m * (p ^ n * G w) := by
    rw [← map_p_pow_mul, hy, map_add, hG_ainf, zero_add, pow_zero, mul_one, map_p_pow_mul, pow_add,
      mul_assoc]
  exact mul_left_cancel₀ (pow_ne_zero m isUnit_p.ne_zero) hG_eq

/-- Let `m = (n, g)` in `FrobGal` act as `φ ^ n g`. If `m • f a` lies in `c.S` for every `a` in
A_inf, then `m • c.extendToBPlus f y` lies in S_B = `c.bicommutant` for every `y` in B^+. -/
lemma smul_extendToBPlus_mem_bicommutant {m : FrobGal} {y : BPlus} {f : Ainf →ₗ[c.S] Ainf}
    (hf : ∀ a : Ainf, m • f a ∈ c.S) :
    m • c.extendToBPlus f y ∈ c.bicommutant := by
  -- To show: multiplication by `t = m • c.extendToBPlus f y` commutes with every `c.S`-linear `G`
  -- keeping `amaxImage`.
  rw [mem_bicommutant_iff]
  intro G hG x
  -- On `w` in `amaxImage`: by density in `y`, since for `y` in `Ainf` the scalar lies in `c.S`.
  have h_on_amaxImage (w : BPlus) (hw : w ∈ amaxImage) :
      G (m • c.extendToBPlus f y * w) - m • c.extendToBPlus f y * G w = 0 := by
    let H : BPlus →+ BPlus :=
      (G * .mulRight c.S w - .mulRight c.S (G w)).toAddMonoidHom.comp (m • c.extendToBPlus f)
    have hH_amax : ∀ y ∈ amaxImage, H y ∈ amaxImage := by
      aesop (add simp [extendToBPlus_mem_amaxImage, smul_mem_amaxImage])
    have hH_ainf (a : Ainf) : H (ainfToBPlus a) = 0 := by
      simpa [H, extendToBPlus_ainfToBPlus, sub_eq_zero, smul_def] using
        G.map_smul (⟨m • f a, hf a⟩ : c.S) w
    exact eq_zero_of_map_ainfToBPlus_eq_zero H hH_amax hH_ainf
  -- Every `x` has a multiple `p ^ n * x` in `amaxImage`; cancel `p ^ n`.
  obtain ⟨n, b, hb⟩ : ∃ (n : ℕ) (b : Amax), (p : BPlus) ^ n * x = algebraMap Amax BPlus b :=
    x.exists_p_pow_mul_eq_amax
  have h_pow : G (m • c.extendToBPlus f y * (p ^ n * x)) -
      m • c.extendToBPlus f y * G (p ^ n * x) = 0 :=
    h_on_amaxImage (p ^ n * x) ⟨b, hb.symm⟩
  rw [sub_eq_zero, mul_left_comm, map_p_pow_mul, map_p_pow_mul, mul_left_comm] at h_pow
  exact mul_left_cancel₀ (pow_ne_zero n isUnit_p.ne_zero) h_pow

/-- For each index `i`, take the coordinate `c.adicBasis.coord i : A_inf → c.S` of the chosen
topological basis of A_inf over `c.S`, and extend it `c.S`-linearly to
`c.extendedCoord i : B^+ → B^+`, where B^+ = A_max[1/p]. This extension takes all its values in
S_B = `c.bicommutant`, the set of elements of B^+ whose multiplication commutes with every
`c.S`-linear endomorphism of B^+ that preserves the image of A_max. -/
lemma extendedCoord_mem_bicommutant (i : c.adicBasis.Index) (y : BPlus) :
    c.extendedCoord i y ∈ c.bicommutant := by
  rw [← one_smul FrobGal (c.extendedCoord i y)]
  -- The coordinate takes its values in `c.S`.
  exact c.smul_extendToBPlus_mem_bicommutant fun a ↦ by simp

/-- If `v ≠ 0` and `v * u` lie in S_B = `c.bicommutant`, so does `u`. -/
lemma mem_bicommutant_of_mul {u v : BPlus} (hv : v ∈ c.bicommutant) (hv_ne : v ≠ 0)
    (hvu : v * u ∈ c.bicommutant) : u ∈ c.bicommutant := by
  rw [mem_bicommutant_iff] at hv hvu ⊢
  intro G hG x
  -- `v * G (u * x) = G (v * u * x) = v * u * G x`, and `v ≠ 0` cancels.
  have h_v : G (v * (u * x)) = v * G (u * x) := hv G hG (u * x)
  have h_vu : G (v * u * x) = v * u * G x := hvu G hG x
  apply mul_left_cancel₀ hv_ne
  rw [← h_v, ← mul_assoc, h_vu, mul_assoc]

/-- The inverse of `p` in B^+ lies in S_B = `c.bicommutant`. -/
lemma exists_bicommutant_mul_p_eq_one : ∃ u ∈ c.bicommutant, u * p = 1 := by
  -- `p` and the product `p * p⁻¹ = 1` lie in `c.bicommutant`.
  refine ⟨↑isUnit_p.unit⁻¹, c.mem_bicommutant_of_mul (natCast_mem c.bicommutant p)
    isUnit_p.ne_zero ?_, isUnit_p.val_inv_mul⟩
  simp [one_mem]

/-! ### Coordinates, Frobenius and decompositions on S_B -/

/-- Let B^+ = A_max[1/p], and let S_B = `c.bicommutant` be the set of elements of B^+ whose
multiplication commutes with every `c.S`-linear endomorphism of B^+ that preserves the image of
A_max. The coordinate at `c.oneIndex` of the chosen topological basis of A_inf over `c.S` is the
identity on `c.S`. Its `c.S`-linear extension `c.extendedCoord c.oneIndex` to B^+ fixes every `y` in
S_B. -/
lemma extendedCoord_oneIndex_eq_self {y : BPlus} (hy : y ∈ c.bicommutant) :
    c.extendedCoord c.oneIndex y = y := by
  -- The extension is linear over S_B, and the coordinate of `1` is `1`.
  have h_one : c.adicBasis.coord c.oneIndex 1 = 1 := c.coord₀_coe 1
  have h_ext_one : c.extendedCoord c.oneIndex 1 = 1 := by
    rw [← map_one ainfToBPlus, extendToBPlus_ainfToBPlus]
    simp [h_one]
  calc c.extendedCoord c.oneIndex y = y * c.extendedCoord c.oneIndex 1 := by
        simpa using c.extendToBPlus_mul (Algebra.linearMap c.S Ainf ∘ₗ
          c.adicBasis.coord c.oneIndex) hy 1
    _ = y := by rw [h_ext_one, mul_one]

/-- The subring `S[E/p]` of `BPlus`: the `c.S`-algebra generated by `E / p`. It lies in
S_B = `c.bicommutant` (`adjoinEDivP_le_bicommutant`). -/
def adjoinEDivP : Subalgebra c.S BPlus :=
  Algebra.adjoin c.S {x : BPlus | (p : BPlus) * x = ainfToBPlus c.E}

theorem adjoinEDivP_le_bicommutant : c.adjoinEDivP ≤ c.bicommutant := by
  refine Algebra.adjoin_le fun x (hx : (p : BPlus) * x = ainfToBPlus c.E) ↦ ?_
  refine c.mem_bicommutant_of_mul (natCast_mem c.bicommutant p) BPlus.isUnit_p.ne_zero ?_
  rw [hx]
  exact ainfToBPlus_mem_bicommutant c.E

/-- The closure of `S[E/p]` in `BPlus` for the topology whose neighbourhoods of `0` are the
`p ^ n * amaxImage`, with `p` inverted: `y` lies in it when, for some `m` and every `n`,
`p ^ m * y` is an element of `S[E/p]` plus `p ^ n` times an element of `amaxImage`. It equals
S_B = `c.bicommutant` (`adjoinEDivPClosure_eq_bicommutant`). -/
def adjoinEDivPClosure : Set BPlus :=
  {y : BPlus | ∃ m : ℕ, ∀ n : ℕ, ∃ s ∈ c.adjoinEDivP, ∃ w ∈ amaxImage,
    (p : BPlus) ^ m * y = s + (p : BPlus) ^ n * w}

/-- For a chart `c` with ring `c.S` and element `E` (ξ times a unit in A_inf),
`c.extendedCoord c.oneIndex : B^+ → B^+` is the extension to B^+ of the coordinate of A_inf over
`c.S` that is the identity on `c.S`. It sends the image in B^+ of any polynomial over `Ainf`
evaluated at `Amax.xiDivP = ξ / p` into `S[E/p]` (`c.adjoinEDivP`), the subring of B^+ generated
over `c.S` by `E / p`. -/
theorem extendedCoord_oneIndex_aeval_mem_adjoinEDivP (P : Polynomial Ainf) :
    c.extendedCoord c.oneIndex (algebraMap Amax BPlus (Polynomial.aeval Amax.xiDivP P)) ∈
      c.adjoinEDivP := by
  -- As `E * u = ξ` for a unit `u`, the element `Amax.xiDivP` is `x * u` with `x = E / p` in
  -- `S[E/p]`; so a monomial `a * Amax.xiDivP ^ n` is `x ^ n` times an element of `Ainf`, and the
  -- coordinate is `S[E/p]`-linear.
  obtain ⟨u, hu⟩ : ∃ u : Ainfˣ, c.E.val * u = xi := c.associated_E_xi
  have h_E : (c.E : Ainf) = xi * ↑u⁻¹ := by simp [← hu]
  have h_pX : (p : BPlus) * algebraMap Amax BPlus Amax.xiDivP = ainfToBPlus xi := by
    rw [← map_natCast (algebraMap Amax BPlus) p, ← map_mul, Period.p_mul_X]
    exact (IsScalarTower.algebraMap_apply Ainf Amax BPlus xi).symm
  obtain ⟨x, hx_mem, hX⟩ : ∃ x ∈ c.adjoinEDivP,
      algebraMap Amax BPlus Amax.xiDivP = x * ainfToBPlus ↑u := by
    refine ⟨algebraMap Amax BPlus Amax.xiDivP * ainfToBPlus ↑u⁻¹, Algebra.subset_adjoin ?_, ?_⟩
    · show (p : BPlus) * (algebraMap Amax BPlus Amax.xiDivP * ainfToBPlus ↑u⁻¹) = ainfToBPlus c.E
      rw [← mul_assoc, h_pX, ← map_mul, ← h_E]
    · simp [mul_assoc, ← map_mul]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa using add_mem hP hQ
  | monomial n a =>
    have h_monomial : algebraMap Amax BPlus (Polynomial.aeval Amax.xiDivP (Polynomial.monomial n a))
      =
        x ^ n * ainfToBPlus (↑u ^ n * a) := by
      rw [Polynomial.aeval_monomial, map_mul (algebraMap Amax BPlus), map_pow, hX,
        ← IsScalarTower.algebraMap_apply Ainf Amax BPlus a, map_mul ainfToBPlus, map_pow]
      ring
    have hx_pow : x ^ n ∈ c.bicommutant := pow_mem (c.adjoinEDivP_le_bicommutant hx_mem) n
    rw [h_monomial, c.extendToBPlus_mul _ hx_pow, c.extendToBPlus_ainfToBPlus, LinearMap.comp_apply]
    -- The value of the coordinate lies in `S`.
    generalize c.adicBasis.coord c.oneIndex (↑u ^ n * a) = s
    exact mul_mem (pow_mem hx_mem n) (c.adjoinEDivP.algebraMap_mem s)

/-- The closure of `S[E/p]` in `BPlus` = A_max[1/p], for the topology with neighbourhoods of `0` the
`p ^ n * amaxImage`, with `p` inverted, equals `bicommutant`. Here `c.S` is the image in A_inf of
the chart's map Λ⟦X⟧ → A_inf, E ∈ S is the image of X^e A + p (e = `c.e`, A = `c.unitSeries`), and
`bicommutant` is the set of elements of `BPlus` whose multiplication commutes with every
`c.S`-linear self-map of `BPlus` that keeps `amaxImage`, the image of A_max. -/
theorem adjoinEDivPClosure_eq_bicommutant : c.adjoinEDivPClosure = c.bicommutant := by
  -- The coordinate of `1` fixes `S[E/p]` and `bicommutant` and keeps `amaxImage`. One way, it
  -- moves `p ^ m * y` by elements of `p ^ n * amaxImage` for every `n`, so not at all; the
  -- other way, it sends polynomial approximations in `Amax` into `S[E/p]`.
  have hp_pow (m : ℕ) : (p : BPlus) ^ m ∈ c.bicommutant := pow_mem (natCast_mem c.bicommutant p) m
  ext y
  simp only [adjoinEDivPClosure, Set.mem_ofPred_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨m, h_approx⟩
    have h_zero : c.extendedCoord c.oneIndex (p ^ m * y) - p ^ m * y = 0 := by
      refine eq_zero_of_p_pow_amaxImage fun n ↦ ?_
      obtain ⟨s, hs, w, hw, h_eq⟩ := h_approx n
      refine ⟨c.extendedCoord c.oneIndex w - w,
        sub_mem (c.extendToBPlus_mem_amaxImage _ w hw) hw, ?_⟩
      rw [h_eq, map_add, c.extendedCoord_oneIndex_eq_self (c.adjoinEDivP_le_bicommutant hs),
        c.extendToBPlus_mul _ (hp_pow n)]
      ring
    refine c.mem_bicommutant_of_mul (hp_pow m) (BPlus.isUnit_p.pow m).ne_zero ?_
    rw [← sub_eq_zero.mp h_zero]
    exact c.extendedCoord_mem_bicommutant c.oneIndex (p ^ m * y)
  · intro hy
    obtain ⟨m, b, hb⟩ : ∃ (m : ℕ) (b : Amax), (p : BPlus) ^ m * y = algebraMap Amax BPlus b :=
      y.exists_p_pow_mul_eq_amax
    refine ⟨m, fun n ↦ ?_⟩
    obtain ⟨P, w, hw⟩ : ∃ P : Polynomial Ainf,
      (p : Amax) ^ n ∣ b - Polynomial.aeval Amax.xiDivP P :=
      b.exists_p_pow_dvd_sub_aeval n
    have h_split : (p : BPlus) ^ m * y =
        algebraMap Amax BPlus (Polynomial.aeval Amax.xiDivP P) + p ^ n * algebraMap Amax BPlus
          w := by
      rw [hb, eq_add_of_sub_eq' hw, map_add, map_mul, map_pow, map_natCast]
    refine ⟨c.extendedCoord c.oneIndex (algebraMap Amax BPlus (Polynomial.aeval Amax.xiDivP P)),
      c.extendedCoord_oneIndex_aeval_mem_adjoinEDivP P,
      c.extendedCoord c.oneIndex (algebraMap Amax BPlus w),
      c.extendToBPlus_mem_amaxImage _ (algebraMap Amax BPlus w) ⟨w, rfl⟩, ?_⟩
    rw [← c.extendedCoord_oneIndex_eq_self (mul_mem (hp_pow m) hy), h_split, map_add,
      c.extendToBPlus_mul _ (hp_pow n)]

/-- For `y` in B^+ and `m : ℕ`, for all large enough finite sets `F` of indices,
`y - ∑ i ∈ F, b i • c.extendedCoord i y` is `p ^ m` times an element of `amaxImage`, the image of
the period ring A_max in B^+. Here `b i = c.adicBasis.b i` is the topological basis of A_inf
over `c.S`, and `c.extendedCoord i` extends its `i`-th coordinate to B^+. -/
lemma eventually_approx_sum_extendedCoord (y : BPlus) (m : ℕ) :
    ∀ᶠ F : Finset c.adicBasis.Index in Filter.atTop, ∃ w ∈ amaxImage,
      y - ∑ i ∈ F, c.adicBasis.b i • c.extendedCoord i y = p ^ m * w := by
  -- Write `p ^ k * y = a + p ^ (k + m) * w` with `a` in `Ainf`, and expand `a` in the basis.
  obtain ⟨k, a, w, hw, hy⟩ : ∃ (k : ℕ) (a : Ainf), ∃ w ∈ amaxImage,
      (p : BPlus) ^ k * y = ainfToBPlus a + (p : BPlus) ^ (k + m) * ainfToBPlus mu ^ 0 * w :=
    y.exists_Ainf_approx m 0
  -- The remainder lies in `(p, z) ^ N ⊆ (p, ξ) ^ (k + m)`, so `p ^ (k + m)` divides it in `Amax`.
  obtain ⟨N, hN⟩ : ∃ N : ℕ,
      c.maxIdeal ^ N • (⊤ : Submodule c.S Ainf) ≤
        (span {(p : Ainf), xi} ^ (k + m)).restrictScalars c.S :=
    c.exists_maxIdeal_pow_le (k + m)
  filter_upwards [c.adicBasis.eventually_sub_sum_mem a N] with F hF
  obtain ⟨b, hb⟩ : (p : Amax) ^ (k + m) ∣
      algebraMap Ainf Amax (a - ∑ i ∈ F, c.adicBasis.coord i a • c.adicBasis.b i) :=
    p_pow_dvd_of_mem_pow (hN hF)
  have h_sum_mem : ∑ i ∈ F, ainfToBPlus (c.adicBasis.b i) * c.extendedCoord i w ∈ amaxImage :=
    sum_mem fun i _ ↦ mul_mem (amaxImage.algebraMap_mem (c.adicBasis.b i))
      (c.extendToBPlus_mem_amaxImage _ w hw)
  refine ⟨w - ∑ i ∈ F, ainfToBPlus (c.adicBasis.b i) * c.extendedCoord i w +
      algebraMap Amax BPlus b, add_mem (sub_mem hw h_sum_mem) ⟨b, rfl⟩, ?_⟩
  -- Apply `T = 1 - ∑ b i • extendedCoord i` to `hy`, insert `hb` for the part of `a`, cancel
  -- `p ^ k`.
  let T : BPlus →ₗ[c.S] BPlus := 1 - ∑ i ∈ F, c.adicBasis.b i • c.extendedCoord i
  have h_applied : T ((p : BPlus) ^ k * y) - algebraMap Amax BPlus ((p : Amax) ^ (k + m) * b) =
      T (ainfToBPlus a + (p : BPlus) ^ (k + m) * ainfToBPlus mu ^ 0 * w) -
        algebraMap Amax BPlus
          (algebraMap Ainf Amax (a - ∑ i ∈ F, c.adicBasis.coord i a • c.adicBasis.b i)) := by
    rw [hy, hb]
  -- `↓commutes`: without it the products `b i * coord i a` are left in two orders.
  simpa [T, ← mul_add, map_add, ← algebraMap_apply, ↓commutes (R := c.S), sub_eq_iff_eq_add,
    smul_def, map_p_pow_mul, pow_add, mul_assoc, extendToBPlus_ainfToBPlus, IsUnit.ne_zero] using
    h_applied

/-- The Frobenius of B^+ maps S_B = `c.bicommutant` into itself. -/
lemma frobEnd_mem_bicommutant {y : BPlus} (hy : y ∈ c.bicommutant) :
    frobEnd y ∈ c.bicommutant := by
  -- `y = extendedCoord oneIndex y`, and `φ` maps the values of the coordinate, which lie in `S`,
  -- into `S`.
  rw [← c.extendedCoord_oneIndex_eq_self hy]
  exact c.smul_extendToBPlus_mem_bicommutant fun a ↦
    (c.φ (c.adicBasis.coord c.oneIndex a)).property

/-- The image of `φ E` in B^+ has an inverse in S_B = `c.bicommutant`. -/
lemma exists_bicommutant_mul_phi_E_eq_one : ∃ u ∈ c.bicommutant, u * ainfToBPlus (c.φ c.E) = 1 := by
  -- `φ E` is associated to `φ ξ`, hence to `p` in `Amax`, and `p` is a unit of `BPlus`.
  have h_assoc : Associated (p : Amax) (algebraMap Ainf Amax (frobEnd c.E.val)) :=
    associated_p_frobEnd_xi.trans ((c.associated_E_xi.map frobEnd).map (algebraMap Ainf Amax)).symm
  have h_unit : IsUnit (ainfToBPlus (c.φ c.E)) := by
    -- `ainfToBPlus` is the composite of the maps `Ainf → Amax → BPlus`.
    show IsUnit (algebraMap Amax BPlus (algebraMap Ainf Amax (frobEnd c.E.val)))
    exact (h_assoc.map (algebraMap Amax BPlus)).isUnit (by rw [map_natCast]; exact isUnit_p)
  -- The inverse lies in `c.bicommutant`, as `φ E` and the product `1` do.
  refine ⟨↑h_unit.unit⁻¹, c.mem_bicommutant_of_mul (ainfToBPlus_mem_bicommutant (c.φ c.E))
    h_unit.ne_zero ?_, h_unit.val_inv_mul⟩
  simp [one_mem]

/-- Let `ν` in `c.S` have `ξ ∈ (p, ν)` in A_inf, and let `b` be in A_max. For every `M`, the
extended coordinate at `c.oneIndex` (the one that is the identity on `c.S`) satisfies
`p ^ M * c.extendedCoord c.oneIndex b = s + ν ^ M * w` with `s` in `c.S` and `w` in
S_B = `c.bicommutant`. -/
lemma exists_pow_mul_extendedCoord_eq_add (ν : c.S) (hν : ∃ b : Ainf, ν.val ∣ xi - p * b) (b : Amax)
    (M : ℕ) :
    ∃ s : c.S, ∃ w ∈ c.bicommutant,
      p ^ M * c.extendedCoord c.oneIndex (algebraMap Amax BPlus b) =
        ainfToBPlus s + ainfToBPlus ν ^ M * w := by
  -- Apply `extendedCoord oneIndex` to `p ^ M * b = a + ν ^ M * x`; it is `S`-linear and `ν ∈ S`.
  obtain ⟨a, x, hb⟩ : ∃ (a : Ainf) (x : Amax),
      (p : Amax) ^ M * b = algebraMap Ainf Amax a + algebraMap Ainf Amax ν ^ M * x :=
    exists_p_pow_mul_eq_add hν M b
  refine ⟨c.adicBasis.coord c.oneIndex a, c.extendedCoord c.oneIndex (algebraMap Amax BPlus x),
    c.extendedCoord_mem_bicommutant c.oneIndex (algebraMap Amax BPlus x), ?_⟩
  -- The image of `hb` in `BPlus`; the coordinate is linear over `c.S` and fixes `ν ^ M`.
  have h_image : (p : BPlus) ^ M * algebraMap Amax BPlus b =
      ainfToBPlus a + ainfToBPlus ν ^ M * algebraMap Amax BPlus x := by
    simpa [← algebraMap_apply] using congrArg (algebraMap Amax BPlus) hb
  rw [← map_p_pow_mul, h_image, map_add, extendToBPlus_ainfToBPlus,
    c.extendToBPlus_mul _ (pow_mem (ainfToBPlus_mem_bicommutant ν) M)]
  -- `algebraMap c.S Ainf s` is the inclusion `↑s`.
  rfl

/-- For every `y` in S_B = `c.bicommutant` and all large enough `m`, there are `w` in the ring
`WittFq c.f` of constants of the chart and `x` in S_B with `p ^ m * y = w + z * x`. -/
lemma eventually_exists_pow_mul_eq_add_z_mul {y : BPlus} (hy : y ∈ c.bicommutant) :
    ∀ᶠ m : ℕ in Filter.atTop, ∃ w : WittFq c.f, ∃ x ∈ c.bicommutant,
      p ^ m * y = ainfToBPlus (algebraMap (WittFq c.f) Ainf w) + ainfToBPlus c.z * x := by
  -- Let `p ^ k * y = b` lie in `Amax` and `m = k + 1 + n`. Apply
  -- `exists_pow_mul_extendedCoord_eq_add` to `p ^ n * b`, which `extendedCoord oneIndex` fixes, and
  -- split the constant off `s`.
  obtain ⟨k, b, hb⟩ : ∃ (k : ℕ) (b : Amax), (p : BPlus) ^ k * y = algebraMap Amax BPlus b :=
    y.exists_p_pow_mul_eq_amax
  filter_upwards [Ioi_mem_atTop k] with m hm
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k + 1 + n = m := Nat.le.dest hm
  obtain ⟨s, x, hx, h_dec⟩ : ∃ s : c.S, ∃ x ∈ c.bicommutant,
      p ^ 1 * c.extendedCoord c.oneIndex (algebraMap Amax BPlus (p ^ n * b)) =
        ainfToBPlus s + ainfToBPlus c.z ^ 1 * x :=
    c.exists_pow_mul_extendedCoord_eq_add c.z c.exists_z_dvd_xi_sub_p_mul (p ^ n * b) 1
  obtain ⟨w, r, hr⟩ : ∃ (w : WittFq c.f) (r : c.S), s = algebraMap (WittFq c.f) c.S w + c.z * r :=
    c.exists_eq_const_add_z_mul s
  refine ⟨w, ainfToBPlus r + x, add_mem (ainfToBPlus_mem_bicommutant r) hx, ?_⟩
  -- The coordinate fixes `p ^ n * b = p ^ (n + k) * y`, as `y` lies in S_B.
  have h_fix : c.extendedCoord c.oneIndex (algebraMap Amax BPlus (p ^ n * b)) =
      p ^ n * (p ^ k * y) := by
    rw [map_mul, map_pow, map_natCast, ← hb, map_p_pow_mul, map_p_pow_mul,
      c.extendedCoord_oneIndex_eq_self hy]
  calc (p : BPlus) ^ (k + 1 + n) * y = p ^ 1 * (p ^ n * (p ^ k * y)) := by ring
    _ = ainfToBPlus s + ainfToBPlus c.z ^ 1 * x := by rw [← h_fix, h_dec]
    _ = _ := by simp [hr, mul_add, add_assoc]

/-! ### Divisibility by z -/

/-- If `g` in G_p fixes the constants `WittFq c.f` pointwise and `y` is in S_B = `c.bicommutant`,
then `z` divides `g • y - y` in B^+. -/
lemma z_dvd_sub {y : BPlus} {g : Gp p} (hg : FixesLambda c.f g) (hy : y ∈ c.bicommutant) :
    ainfToBPlus c.z ∣ g • y - y := by
  -- In `p ^ k * y = w + z * x` the constant `w` is fixed by `g`, and `z` divides `g • z`;
  -- the unit `p ^ k` cancels.
  obtain ⟨k, w, x, -, hk⟩ : ∃ (k : ℕ) (w : WittFq c.f), ∃ x ∈ c.bicommutant,
      (p : BPlus) ^ k * y = ainfToBPlus (algebraMap (WittFq c.f) Ainf w) + ainfToBPlus c.z * x :=
    (c.eventually_exists_pow_mul_eq_add_z_mul hy).exists
  obtain ⟨u, hu⟩ : c.z.val ∣ g • c.z.val := by
    -- `erw`: `g` acts on `Ainf` as its image in `FrobGal`, the action of `smul_teichmuller`.
    erw [z_eq_teichmuller, smul_teichmuller]
    simp [map_dvd, untilt_dvd_iff.mp, valRingCp.dvd_iff_norm_le, untilt_frobGal_smul]
  have h_dvd : ainfToBPlus c.z ∣ g • ((p : BPlus) ^ k * y) - (p : BPlus) ^ k * y := by
    rw [hk]
    simp [hg, hu, mul_assoc, ← mul_sub, -isUnit_map_iff]
  simpa [← mul_sub, IsUnit.pow, -isUnit_map_iff] using h_dvd

/-- An element of B^+ that is divisible by every power of z is zero. -/
lemma eq_zero_of_z_pow_dvd {y : BPlus} (h_dvd : ∀ n : ℕ, ainfToBPlus c.z ^ n ∣ y) : y = 0 := by
  -- With `E * u = ξ` and `E = z ^ e * A + p`, `A` a unit, the element `ξ - p * u` is `z ^ e` times
  -- a unit; so all its powers divide `y`.
  obtain ⟨u, hu⟩ :
      ∃ u : Ainfˣ, c.seriesMap (PowerSeries.X ^ c.e * c.unitSeries.val + p.cast) * u = xi :=
    c.associated_xi
  refine eq_zero_of_forall_pow_dvd u ?_
  simp_all (maxDischargeDepth := 4) [← hu, add_mul, ← pow_mul, mul_pow, IsUnit.map, z, IsUnit.pow,
    -isUnit_map_iff]

/-- A_inf ∩ y B^+[1/E] = y A_inf, where `E = c.E` is ξ times a unit. Let `y` in A_inf not be
divisible by `p`, let ξ lie in the ideal `(p, y)`, and let `θ y ≠ 0`. If `a` is in A_inf and `y`
divides `E ^ k * a` in B^+, then `y` divides `a` in A_inf. -/
lemma dvd_of_dvd_E_pow_mul {y a : Ainf} {k : ℕ} (hy_p : ¬(p : Ainf) ∣ y)
    (hy_xi : ∃ b : Ainf, y ∣ xi - p * b) (hy_theta : theta y ≠ 0)
    (h_dvd : ainfToBPlus y ∣ ainfToBPlus (c.E ^ k * a)) : y ∣ a := by
  have h_bplus : ainfToBPlus y ∣ ainfToBPlus (xi ^ k * a) := by
    grw [c.associated_E_xi.dvd] at h_dvd
    exact h_dvd
  have h_ainf : y ∣ xi ^ k * a := dvd_of_algebraMap_BPlus_dvd hy_p hy_xi h_bplus
  -- The prime ξ does not divide `y`, since `θ y ≠ 0`.
  have hxi_y : ¬xi ∣ y := mt theta_eq_zero_iff_xi_dvd.mpr hy_theta
  exact dvd_of_dvd_prime_pow_mul Ainf.prime_xi hxi_y h_ainf

/-- Let `c` be a chart, `z = c.z` the image of `X` in A_inf and `E = c.E` the image of
`X ^ e * A + p`, which is ξ times a unit, and let `a` be in A_inf. If the image of `z` divides the
image of `E ^ k * a` in B^+, then `z` divides `a` in A_inf. -/
lemma z_dvd_of_dvd_E_pow_mul {k : ℕ} {a : Ainf}
    (h : ainfToBPlus c.z ∣ ainfToBPlus (c.E ^ k * a)) :
    c.z.val ∣ a :=
  c.dvd_of_dvd_E_pow_mul c.not_p_dvd_z c.exists_z_dvd_xi_sub_p_mul c.theta_z_ne_zero h

end Chart

end ChartScalars

end New.Lift

end
